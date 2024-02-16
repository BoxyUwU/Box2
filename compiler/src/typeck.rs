use std::{
    collections::HashMap,
    iter::FromIterator,
    ops::{Deref, DerefMut},
};

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::{
    ast::{self, NodeId, Nodes},
    resolve::{DefKind, Res},
    solve::{Goal, GoalKind, NoSolution},
    tir::{
        building::{build_args_for_path, TirBuilder},
        *,
    },
    tokenize::{Literal, Span},
};

use self::visit::{FallibleTypeFolder, TypeFoldable, TypeSuperFoldable};

pub struct TypeckResults<'t> {
    pub tys: HashMap<NodeId, Ty<'t>>,
    pub errs: Vec<TypeckError<'t>>,
}

pub struct FnChecker<'ast, 'm, 't> {
    pub ast: &'ast ast::Nodes<'ast>,
    pub resolutions: &'m HashMap<NodeId, Res<NodeId>>,
    pub body_sources: &'m HashMap<BodyId, BodySource<'t>>,
    pub lowered_ids: HashMap<NodeId, TirId>,

    pub typeck_results: HashMap<TirId, TypeckResults<'t>>,

    pub tir_ctx: &'t TirCtx<'t>,
}

impl<'ast, 'm, 't> visit::Visitor<'t> for FnChecker<'ast, 'm, 't> {
    fn visit_fn(&mut self, f: &Fn<'t>) {
        visit::super_visit_fn(self, f);

        let mut typeck_ctx = TypeckCtxt::new(
            self.tir_ctx,
            f.bounds.instantiate_root_placeholders(self.tir_ctx),
            f.generics,
            self.ast,
            std::mem::take(&mut self.lowered_ids),
            self.resolutions,
        );

        let r = typeck_fn(f, &self.body_sources, &mut typeck_ctx);
        self.typeck_results.insert(f.id, r);
        drop(std::mem::replace(
            &mut self.lowered_ids,
            typeck_ctx.lowered_ids,
        ));
    }
}

pub enum TypeckError<'t> {
    ExpectedFound(ExpectedFound<'t>),
    UnconstrainedInfer(NodeId, InferId, Span),
}
pub fn typeck_fn<'ast, 't>(
    Fn { body, .. }: &'_ Fn<'t>,
    body_sources: &HashMap<BodyId, BodySource<'t>>,
    tcx: &mut TypeckCtxt<'ast, '_, 't>,
) -> TypeckResults<'t> {
    // FIXME: param tys wf
    // FIXME: ret tys wf

    let body_src = match body {
        Some(body) => body_sources[body],
        None => {
            return TypeckResults {
                tys: HashMap::new(),
                errs: vec![],
            }
        }
    };

    let body = tcx.ast.get(body_src.expr).unwrap_expr();

    let mut node_tys = HashMap::from_iter(body_src.params.iter().map(|(node_id, ty)| {
        let var = tcx.new_var(Span::new(0..1));
        let r_tcx = tcx.tcx();
        _ = tcx.eq(
            Ty::Infer(var),
            *ty.instantiate_root_placeholders(r_tcx),
            Span::new(0..1),
        );
        (*node_id, var)
    }));

    let ret_ty_span = Span::new(0..1);
    let var = tcx.new_var(ret_ty_span);
    node_tys.insert(body_src.expr, var);
    _ = tcx.eq(
        Ty::Infer(var),
        *body_src.ret.instantiate_root_placeholders(tcx.tcx()),
        ret_ty_span,
    );

    typeck_expr(body, tcx, &mut node_tys);
    let infcx_errs = std::mem::take(&mut tcx.infcx.errors);
    let mut node_tys = node_tys.into_iter().collect::<Vec<_>>();
    node_tys.sort_by(|(_, a), (_, b)| InferId::cmp(a, b));

    node_tys
        .into_iter()
        .map(|(id, ty)| (id, tcx.infcx.resolve_ty(Ty::Infer(ty))))
        .fold(
            TypeckResults {
                tys: HashMap::default(),
                errs: infcx_errs
                    .into_iter()
                    .map(TypeckError::ExpectedFound)
                    .collect(),
            },
            |TypeckResults { mut tys, mut errs }, (id, ty)| {
                match ty {
                    Ty::Infer(infer_id) => errs.push(TypeckError::UnconstrainedInfer(
                        id,
                        infer_id,
                        tcx.infcx.infer_spans[&infer_id],
                    )),
                    _ => {
                        tys.insert(id, ty);
                    }
                };
                TypeckResults { tys, errs }
            },
        )
}

impl<'t> Ty<'t> {
    pub fn pretty(self, tcx: &'t TirCtx<'t>) -> String {
        match self {
            Ty::Unit => "()".into(),
            Ty::Infer(inf) => format!("?{}", inf.0),
            Ty::FnDef(id, args) => {
                let mut pretty_args = String::new();
                for arg in args.0 {
                    if !pretty_args.is_empty() {
                        pretty_args.push_str(", ");
                    }

                    match arg {
                        GenArg::Ty(ty) => pretty_args.push_str(&ty.pretty(tcx)),
                    }
                }
                let func = tcx.get_item(id).unwrap_fn();
                format!("{}[{}]", func.name, pretty_args)
            }
            Ty::Adt(id, args) => {
                let mut pretty_args = String::new();
                for arg in args.0 {
                    if !pretty_args.is_empty() {
                        pretty_args.push_str(", ");
                    }

                    match arg {
                        GenArg::Ty(ty) => pretty_args.push_str(&ty.pretty(tcx)),
                    }
                }
                let adt = tcx.get_item(id).unwrap_adt();
                format!("{}[{}]", adt.name, pretty_args)
            }
            Ty::Alias(id, args) => {
                let mut pretty_args = String::new();
                for arg in args.0 {
                    if !pretty_args.is_empty() {
                        pretty_args.push_str(", ");
                    }

                    match arg {
                        GenArg::Ty(ty) => pretty_args.push_str(&ty.pretty(tcx)),
                    }
                }
                let alias = tcx.get_item(id).unwrap_alias();
                format!("{}[{}]", alias.name, pretty_args)
            }
            Ty::Bound(db, bv) => format!("^{}_{}", db.0, bv.0),
            Ty::Placeholder(u, bv) => format!("!{}_{}", u.0, bv.0),
            Ty::Int => "int".into(),
            Ty::Float => "float".into(),
            Ty::Error => "{ type error }".into(),
        }
    }
}

#[derive(Debug)]
pub struct ExpectedFound<'t>(pub Ty<'t>, pub Ty<'t>, pub Span);

pub struct InferCtxt<'t> {
    pub tcx: &'t TirCtx<'t>,
    next_infer_id: InferId,
    constraints: HashMap<InferId, Ty<'t>>,
    infer_spans: HashMap<InferId, Span>,
    errors: Vec<ExpectedFound<'t>>,
}
impl<'t> Deref for InferCtxt<'t> {
    type Target = TirCtx<'t>;
    fn deref(&self) -> &TirCtx<'t> {
        &self.tcx
    }
}

impl<'t> InferCtxt<'t> {
    fn new(tcx: &'t TirCtx<'t>) -> Self {
        Self {
            tcx,
            next_infer_id: InferId(0),
            constraints: HashMap::new(),
            infer_spans: HashMap::new(),
            errors: Vec::new(),
        }
    }

    fn tcx(&self) -> &'t TirCtx<'t> {
        self.tcx
    }

    pub fn new_var(&mut self, span: Span) -> InferId {
        let id = self.next_infer_id;
        self.infer_spans.insert(id, span);
        self.next_infer_id.0 += 1;
        id
    }

    fn resolve_ty(&self, mut ty: Ty<'t>) -> Ty<'t> {
        loop {
            let infer = match ty {
                Ty::Infer(inf) => inf,
                _ => return ty,
            };

            match self.constraints.get(&infer) {
                None => return ty,
                Some(&resolved_ty) => ty = resolved_ty,
            };
        }
    }

    fn eq(
        &mut self,
        a: Ty<'t>,
        b: Ty<'t>,
        bounds: Bounds<'t>,
        span: Span,
    ) -> Result<Vec<Goal<'t>>, NoSolution> {
        let mut eq = Equate {
            infcx: self,
            bounds,
            goals: vec![],
        };
        match eq.eq(a, b) {
            Err(NoSolution) => {
                self.errors.push(ExpectedFound(a, b, span));
                Err(NoSolution)
            }
            Ok(_) => Ok(eq.goals),
        }
    }
}

struct Generalizer<'a, 't> {
    infcx: &'a mut InferCtxt<'t>,
    var: InferId,

    in_alias: bool,
}
impl<'a, 't> Generalizer<'a, 't> {
    fn new(infcx: &'a mut InferCtxt<'t>, var: InferId) -> Self {
        assert_eq!(infcx.resolve_ty(Ty::Infer(var)), Ty::Infer(var));

        Self {
            infcx,
            var,
            in_alias: false,
        }
    }
}
impl<'t> FallibleTypeFolder<'t> for Generalizer<'_, 't> {
    type Error = ();

    fn tcx(&self) -> &'t TirCtx<'t> {
        self.infcx.tcx()
    }

    fn try_fold_ty(&mut self, ty: &'t Ty<'t>) -> Result<&'t Ty<'t>, ()> {
        let ty = self.infcx.resolve_ty(*ty);

        match ty {
            // FIXME(universes)
            Ty::Infer(var) => {
                if self.var == var {
                    return Err(());
                } else {
                    Ok(self
                        .infcx
                        .tcx()
                        .arena
                        .alloc(Ty::Infer(self.infcx.new_var(Span::new(0..0)))))
                }
            }

            Ty::Alias(id, args) => {
                let old_in_alias = self.in_alias;
                self.in_alias = true;
                let r = match args.try_fold_with(self) {
                    Ok(args) => Ok(&*self.infcx.tcx().arena.alloc(Ty::Alias(id, args))),
                    Err(_) if self.in_alias == false => Ok(&*self
                        .infcx
                        .tcx()
                        .arena
                        .alloc(Ty::Infer(self.infcx.new_var(Span::new(0..0))))),
                    Err(_) => Err(()),
                };
                self.in_alias = old_in_alias;
                r
            }
            // FIXME(universes)
            Ty::Placeholder(_, _)
            | Ty::Bound(_, _)
            | Ty::FnDef(_, _)
            | Ty::Adt(_, _)
            | Ty::Unit
            | Ty::Int
            | Ty::Float
            | Ty::Error => (self.infcx.tcx().arena.alloc(ty)).try_super_fold_with(self),
        }
    }
}

struct Equate<'a, 't> {
    infcx: &'a mut InferCtxt<'t>,
    bounds: Bounds<'t>,
    goals: Vec<Goal<'t>>,
}
impl<'a, 't> Equate<'a, 't> {
    fn eq(&mut self, a: Ty<'t>, b: Ty<'t>) -> Result<(), NoSolution> {
        let a = self.infcx.resolve_ty(a);
        let b = self.infcx.resolve_ty(b);

        let instantiate = |equate: &mut Equate<'a, 't>, var: InferId, with: Ty<'t>| {
            let tcx: &TirCtx<'_> = equate.infcx.tcx();
            match Generalizer::new(equate.infcx, var).try_fold_ty(tcx.arena.alloc(with)) {
                Ok(new_a) => {
                    equate.infcx.constraints.try_insert(var, *new_a).unwrap();
                    equate.eq(*new_a, with)
                }
                Err(()) => Err(NoSolution),
            }
        };

        match (a, b) {
            (Ty::Error, _) | (_, Ty::Error) => Ok(()),

            (Ty::Infer(a), Ty::Infer(b)) => match a == b {
                true => Ok(()),
                false => {
                    self.infcx.constraints.try_insert(a, Ty::Infer(b)).unwrap();
                    Ok(())
                }
            },
            (alias @ Ty::Alias(_, _), ty) | (ty, alias @ Ty::Alias(_, _)) => {
                self.goals.push(Goal {
                    bounds: self.bounds,
                    kind: GoalKind::Equate(alias, ty),
                });
                Ok(())
            }

            // FIXME: universe errors
            (Ty::Infer(var), ty) | (ty, Ty::Infer(var)) => instantiate(self, var, ty),

            (
                Ty::Placeholder(_, _) | Ty::Int | Ty::Float | Ty::Unit,
                Ty::Placeholder(_, _) | Ty::Int | Ty::Float | Ty::Unit,
            ) => match a == b {
                true => Ok(()),
                false => Err(NoSolution),
            },
            (
                Ty::FnDef(a_id, a_args) | Ty::Adt(a_id, a_args),
                Ty::FnDef(b_id, b_args) | Ty::Adt(b_id, b_args),
            ) if a_id == b_id => {
                for (a_arg, b_arg) in a_args.0.iter().zip(b_args.0.iter()) {
                    let GenArg::Ty(a_arg) = a_arg;
                    let GenArg::Ty(b_arg) = b_arg;
                    self.eq(**a_arg, **b_arg)?;
                }
                Ok(())
            }
            (Ty::FnDef(_, _) | Ty::Adt(_, _), _) | (_, Ty::FnDef(_, _) | Ty::Adt(_, _)) => {
                Err(NoSolution)
            }
            (Ty::Bound(_, _), _) | (_, Ty::Bound(_, _)) => unreachable!(),
        }
    }
}

pub struct TypeckCtxt<'ast, 'r, 't> {
    pub infcx: InferCtxt<'t>,
    bounds: Bounds<'t>,
    generics: &'t Generics<'t>,
    goals: Vec<Goal<'t>>,

    ast: &'ast Nodes<'ast>,
    pub lowered_ids: HashMap<NodeId, TirId>,
    resolutions: &'r HashMap<NodeId, Res<NodeId>>,
}
impl<'ast, 'r, 't> TypeckCtxt<'ast, 'r, 't> {
    fn new(
        tcx: &'t TirCtx<'t>,
        bounds: Bounds<'t>,
        generics: &'t Generics<'t>,
        ast: &'ast Nodes<'ast>,
        lowered_ids: HashMap<NodeId, TirId>,
        resolutions: &'r HashMap<NodeId, Res<NodeId>>,
    ) -> Self {
        let infcx = InferCtxt::new(tcx);

        TypeckCtxt {
            infcx,
            bounds,
            generics,
            goals: Vec::new(),
            ast,
            lowered_ids,
            resolutions,
        }
    }

    fn eq(&mut self, a: Ty<'t>, b: Ty<'t>, span: Span) -> Result<(), NoSolution> {
        let goals = self.infcx.eq(a, b, self.bounds, span)?;
        self.goals.extend(goals);
        Ok(())
    }
}

impl<'t> Deref for TypeckCtxt<'_, '_, 't> {
    type Target = InferCtxt<'t>;
    fn deref(&self) -> &Self::Target {
        &self.infcx
    }
}
impl<'t> DerefMut for TypeckCtxt<'_, '_, 't> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.infcx
    }
}

pub fn typeck_expr<'ast, 't>(
    this_expr: &ast::Expr<'_>,
    tcx: &mut TypeckCtxt<'ast, '_, 't>,
    node_tys: &mut HashMap<NodeId, InferId>,
) {
    match this_expr.kind {
        ast::ExprKind::Let(binding, rhs, span) => {
            _ = tcx.eq(Ty::Infer(node_tys[&this_expr.id]), Ty::Unit, span);

            let pat_var = tcx.infcx.new_var(binding.span);
            node_tys.insert(binding.id, pat_var);
            let rhs_var = tcx.infcx.new_var(rhs.span());
            node_tys.insert(rhs.id, rhs_var);
            _ = tcx.eq(Ty::Infer(pat_var), Ty::Infer(rhs_var), span);
            typeck_expr(rhs, tcx, node_tys);
        }
        ast::ExprKind::Block(stmts, block_span) => {
            // fixme  block layout is fucky
            for (expr, _) in stmts {
                let var = tcx.infcx.new_var(expr.span());
                node_tys.insert(expr.id, var);
                typeck_expr(expr, tcx, node_tys);
            }

            match stmts.last() {
                Some((expr, false)) => {
                    let var = node_tys[&expr.id];
                    _ = tcx.eq(
                        Ty::Infer(var),
                        Ty::Infer(node_tys[&this_expr.id]),
                        block_span,
                    );
                    // FIXME add `Stmt`/`StmtKind`
                }
                _ => _ = tcx.eq(Ty::Infer(node_tys[&this_expr.id]), Ty::Unit, block_span),
            }
        }
        ast::ExprKind::TypeInit(ast::TypeInit {
            path,
            field_inits,
            span,
        }) => {
            let id = match tcx.resolutions.get(&this_expr.id) {
                Some(Res::Def(DefKind::Adt, id)) => *id,
                Some(Res::Def(DefKind::Variant, id)) => tcx.ast.get_variants_adt(*id).id,
                // >!?!?!:<
                None => return,
                _ => unreachable!(),
            };
            let id = tcx.get_id(id).unwrap();
            let (_, args) = build_args_for_path(&path, tcx, tcx.resolutions, tcx.generics);
            let args = args.instantiate_root_placeholders(tcx.tcx());
            _ = tcx.eq(Ty::Adt(id, args), Ty::Infer(node_tys[&this_expr.id]), span);

            for field_init in field_inits {
                let var = tcx.infcx.new_var(field_init.span);
                node_tys.insert(field_init.expr.id, var);
                let field_id = match tcx.resolutions.get(&field_init.id) {
                    Some(Res::Def(DefKind::Field, id)) => *id,
                    // haha,,,, :,(
                    None => return,
                    _ => unreachable!(),
                };
                let field_def = tcx.get_item(tcx.get_id(field_id).unwrap()).unwrap_field();
                let field_ty = field_def.ty.instantiate(args, tcx.tcx());
                _ = tcx.eq(*field_ty, Ty::Infer(var), field_init.span);
                typeck_expr(field_init.expr, tcx, node_tys);
            }
        }
        ast::ExprKind::Path(path @ ast::Path { span, .. }) => {
            let res_ty = match tcx.resolutions[&this_expr.id] {
                Res::Local(id) => Ty::Infer(node_tys[&id]),
                Res::Def(DefKind::Func, _) => {
                    let (id, args) =
                        building::build_args_for_path(&path, tcx, tcx.resolutions, tcx.generics);
                    let args = args.instantiate_root_placeholders(tcx.tcx());
                    Ty::FnDef(id, args)
                }
                _ => todo!(),
            };
            _ = tcx.eq(res_ty, Ty::Infer(node_tys[&this_expr.id]), span);
        }
        ast::ExprKind::Lit(Literal::Int(_), span) => {
            _ = tcx.eq(Ty::Int, Ty::Infer(node_tys[&this_expr.id]), span)
        }
        ast::ExprKind::Lit(Literal::Float(_), span) => {
            _ = tcx.eq(Ty::Float, Ty::Infer(node_tys[&this_expr.id]), span)
        }

        ast::ExprKind::BinOp(_, _, _, _) => todo!(),
        ast::ExprKind::UnOp(_, _, _) => todo!(),
        ast::ExprKind::FnCall(ast::FnCall { func, args, span }) => {
            let rcvr_id = tcx.infcx.new_var(func.span());
            node_tys.insert(func.id, rcvr_id);
            typeck_expr(func, tcx, node_tys);

            let rcvr = tcx.infcx.resolve_ty(Ty::Infer(rcvr_id));
            if let Ty::FnDef(id, fndef_args) = rcvr {
                let func = tcx.get_item(id).unwrap_fn();
                _ = tcx.eq(
                    *func.ret_ty.instantiate(fndef_args, tcx.tcx()),
                    Ty::Infer(node_tys[&this_expr.id]),
                    span,
                );

                if func.params.len() != args.len() {
                    let err = diag_wrong_number_fn_args(func.params, args, span);
                    tcx.err(err);
                }

                for (param, arg) in func.params.iter().zip(args.iter()) {
                    let id = tcx.infcx.new_var(arg.span());
                    node_tys.insert(arg.id, id);
                    _ = tcx.eq(
                        Ty::Infer(id),
                        *param.ty.instantiate(fndef_args, tcx.tcx()),
                        arg.span(),
                    );
                    typeck_expr(arg, tcx, node_tys);
                }
            } else {
                let err = diag_fn_call_on_non_fn(tcx.tcx(), rcvr, func.span());
                tcx.err(err);
                _ = tcx.eq(Ty::Error, Ty::Infer(node_tys[&this_expr.id]), span);
            }
        }

        ast::ExprKind::FieldInit(_) => unreachable!(),
    }
}

fn diag_wrong_number_fn_args(
    params: &[Param<'_>],
    args: &[&ast::Expr<'_>],
    span: Span,
) -> Diagnostic<usize> {
    assert!(params.len() != args.len());

    Diagnostic::error()
        .with_message(format!(
            "wrong number of fn args provided, expected {} args, found {} args",
            params.len(),
            args.len()
        ))
        .with_labels(vec![Label::primary(0, span)])
}

fn diag_fn_call_on_non_fn<'t>(
    tcx: &'t TirCtx<'t>,
    actual_ty: Ty<'t>,
    span: Span,
) -> Diagnostic<usize> {
    Diagnostic::error()
        .with_message(format!(
            "cannot call non-function type: {}",
            actual_ty.pretty(tcx)
        ))
        .with_labels(vec![Label::primary(0, span)])
}
