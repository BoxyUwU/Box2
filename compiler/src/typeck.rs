use std::{collections::HashMap, iter::FromIterator};

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::{
    ast::{self, NodeId, Nodes},
    resolve::{DefKind, Res},
    tir::{
        building::{build_args_for_path, TirBuilder},
        *,
    },
    tokenize::{Literal, Span},
};

pub struct TypeckResults<'t> {
    pub tys: HashMap<NodeId, Ty<'t>>,
    pub errs: Vec<TypeckError<'t>>,
}

pub struct FnChecker<'ast, 'm, 't> {
    pub ast: &'ast ast::Nodes<'ast>,
    pub resolutions: &'m HashMap<NodeId, Res<NodeId>>,
    pub body_sources: &'m HashMap<BodyId, BodySource<'t>>,

    pub tcx: &'m TirBuilder<'t>,
    pub typeck_results: HashMap<TirId, TypeckResults<'t>>,
}

impl<'ast, 'm, 't> visit::Visitor<'t> for FnChecker<'ast, 'm, 't> {
    fn visit_fn(&mut self, f: &Fn<'t>) {
        visit::super_visit_fn(self, f);

        let r = typeck_fn(f, self.tcx, &self.body_sources, self.ast, self.resolutions);
        self.typeck_results.insert(f.id, r);
    }
}

pub enum TypeckError<'t> {
    ExpectedFound(ExpectedFound<'t>),
    UnconstrainedInfer(NodeId, InferId, Span),
}
pub fn typeck_fn<'ast, 't>(
    Fn { body, generics, .. }: &'_ Fn<'t>,
    tcx: &TirBuilder<'t>,
    body_sources: &HashMap<BodyId, BodySource<'t>>,
    ast: &'ast Nodes<'ast>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
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

    let body = ast.get(body_src.expr).unwrap_expr();

    let mut infer_ctx = InferCtxt::new();
    let mut node_tys = HashMap::from_iter(body_src.params.iter().map(|(node_id, ty)| {
        let var = infer_ctx.new_var(Span::new(0..1));
        infer_ctx.eq(
            Ty::Infer(var),
            *ty.instantiate_root_placeholders(tcx.tcx()),
            Span::new(0..1),
        );
        (*node_id, var)
    }));

    let ret_ty_span = Span::new(0..1);
    let var = infer_ctx.new_var(ret_ty_span);
    node_tys.insert(body_src.expr, var);
    infer_ctx.eq(
        Ty::Infer(var),
        *body_src.ret.instantiate_root_placeholders(tcx.tcx()),
        ret_ty_span,
    );

    typeck_expr(
        body,
        ast,
        tcx,
        resolutions,
        &mut infer_ctx,
        &mut node_tys,
        generics,
    );
    let infcx_errs = std::mem::take(&mut infer_ctx.errors);
    node_tys
        .iter()
        .map(|(&id, ty)| (id, infer_ctx.resolve_ty(Ty::Infer(*ty))))
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
                        infer_ctx.infer_spans[&infer_id],
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

#[derive(Debug)]
pub struct InferCtxt<'t> {
    next_infer_id: InferId,
    constraints: HashMap<InferId, Ty<'t>>,
    infer_spans: HashMap<InferId, Span>,
    errors: Vec<ExpectedFound<'t>>,
}

impl<'t> InferCtxt<'t> {
    fn new() -> Self {
        Self {
            next_infer_id: InferId(0),
            constraints: HashMap::new(),
            infer_spans: HashMap::new(),
            errors: Vec::new(),
        }
    }

    fn new_var(&mut self, span: Span) -> InferId {
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

    fn eq(&mut self, a: Ty<'t>, b: Ty<'t>, span: Span) {
        // FIXME occurs check
        let a = self.resolve_ty(a);
        let b = self.resolve_ty(b);

        match (a, b) {
            (Ty::Error, _) | (_, Ty::Error) => return,
            (Ty::Infer(a), Ty::Infer(b)) => match a == b {
                true => (),
                false => {
                    self.constraints.try_insert(a, Ty::Infer(b)).unwrap();
                }
            },
            // FIXME: universe errors
            (Ty::Infer(a), _) => {
                self.constraints.try_insert(a, b).unwrap();
            }
            (_, Ty::Infer(b)) => {
                self.constraints.try_insert(b, a).unwrap();
            }
            (
                Ty::Placeholder(_, _) | Ty::Int | Ty::Float | Ty::Unit,
                Ty::Placeholder(_, _) | Ty::Int | Ty::Float | Ty::Unit,
            ) => match a == b {
                true => (),
                false => self.errors.push(ExpectedFound(a, b, span)),
            },
            (
                Ty::FnDef(a_id, a_args) | Ty::Adt(a_id, a_args),
                Ty::FnDef(b_id, b_args) | Ty::Adt(b_id, b_args),
            ) if a_id == b_id => {
                for (a_arg, b_arg) in a_args.0.iter().zip(b_args.0.iter()) {
                    let GenArg::Ty(a_arg) = a_arg;
                    let GenArg::Ty(b_arg) = b_arg;
                    self.eq(**a_arg, **b_arg, span);
                }
            }
            (Ty::FnDef(_, _) | Ty::Adt(_, _), _) | (_, Ty::FnDef(_, _) | Ty::Adt(_, _)) => {
                self.errors.push(ExpectedFound(a, b, span))
            }
            (Ty::Bound(_, _), _) | (_, Ty::Bound(_, _)) => unreachable!(),
        }
    }
}

pub fn typeck_expr<'ast, 't>(
    this_expr: &ast::Expr<'_>,
    ast: &'ast Nodes<'ast>,
    tcx: &TirBuilder<'t>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    infer_ctx: &mut InferCtxt<'t>,
    node_tys: &mut HashMap<NodeId, InferId>,
    generics: &Generics<'t>,
) {
    match this_expr.kind {
        ast::ExprKind::Let(binding, rhs, span) => {
            infer_ctx.eq(Ty::Infer(node_tys[&this_expr.id]), Ty::Unit, span);

            let pat_var = infer_ctx.new_var(binding.span);
            node_tys.insert(binding.id, pat_var);
            let rhs_var = infer_ctx.new_var(rhs.span());
            node_tys.insert(rhs.id, rhs_var);
            infer_ctx.eq(Ty::Infer(pat_var), Ty::Infer(rhs_var), span);
            typeck_expr(rhs, ast, tcx, resolutions, infer_ctx, node_tys, generics);
        }
        ast::ExprKind::Block(stmts, block_span) => {
            // fixme  block layout is fucky
            for (expr, _) in stmts {
                let var = infer_ctx.new_var(expr.span());
                node_tys.insert(expr.id, var);
                typeck_expr(expr, ast, tcx, resolutions, infer_ctx, node_tys, generics);
            }

            match stmts.last() {
                Some((expr, false)) => {
                    let var = node_tys[&expr.id];
                    infer_ctx.eq(
                        Ty::Infer(var),
                        Ty::Infer(node_tys[&this_expr.id]),
                        block_span,
                    );
                    // FIXME add `Stmt`/`StmtKind`
                }
                _ => infer_ctx.eq(Ty::Infer(node_tys[&this_expr.id]), Ty::Unit, block_span),
            }
        }
        ast::ExprKind::TypeInit(ast::TypeInit {
            path,
            field_inits,
            span,
        }) => {
            let id = match resolutions.get(&this_expr.id) {
                Some(Res::Def(DefKind::Adt, id)) => *id,
                Some(Res::Def(DefKind::Variant, id)) => ast.get_variants_adt(*id).id,
                // >!?!?!:<
                None => return,
                _ => unreachable!(),
            };
            let id = tcx.get_id(id).unwrap();
            let (_, args) = build_args_for_path(&path, tcx, resolutions, generics);
            let args = args.instantiate_root_placeholders(tcx.tcx());
            infer_ctx.eq(Ty::Adt(id, args), Ty::Infer(node_tys[&this_expr.id]), span);

            for field_init in field_inits {
                let var = infer_ctx.new_var(field_init.span);
                node_tys.insert(field_init.expr.id, var);
                let field_id = match resolutions.get(&field_init.id) {
                    Some(Res::Def(DefKind::Field, id)) => *id,
                    // haha,,,, :,(
                    None => return,
                    _ => unreachable!(),
                };
                let field_def = tcx.get_item(tcx.get_id(field_id).unwrap()).unwrap_field();
                let field_ty = field_def.ty.instantiate(args, tcx.tcx());
                infer_ctx.eq(*field_ty, Ty::Infer(var), field_init.span);
                typeck_expr(
                    field_init.expr,
                    ast,
                    tcx,
                    resolutions,
                    infer_ctx,
                    node_tys,
                    generics,
                );
            }
        }
        ast::ExprKind::Path(path @ ast::Path { span, .. }) => {
            let res_ty = match resolutions[&this_expr.id] {
                Res::Local(id) => Ty::Infer(node_tys[&id]),
                Res::Def(DefKind::Func, _) => {
                    let (id, args) =
                        building::build_args_for_path(&path, tcx, resolutions, generics);
                    let args = args.instantiate_root_placeholders(tcx.tcx());
                    Ty::FnDef(id, args)
                }
                _ => todo!(),
            };
            infer_ctx.eq(res_ty, Ty::Infer(node_tys[&this_expr.id]), span);
        }
        ast::ExprKind::Lit(Literal::Int(_), span) => {
            infer_ctx.eq(Ty::Int, Ty::Infer(node_tys[&this_expr.id]), span)
        }
        ast::ExprKind::Lit(Literal::Float(_), span) => {
            infer_ctx.eq(Ty::Float, Ty::Infer(node_tys[&this_expr.id]), span)
        }

        ast::ExprKind::BinOp(_, _, _, _) => todo!(),
        ast::ExprKind::UnOp(_, _, _) => todo!(),
        ast::ExprKind::FnCall(ast::FnCall { func, args, span }) => {
            let rcvr_id = infer_ctx.new_var(func.span());
            node_tys.insert(func.id, rcvr_id);
            typeck_expr(func, ast, tcx, resolutions, infer_ctx, node_tys, generics);

            let rcvr = infer_ctx.resolve_ty(Ty::Infer(rcvr_id));
            if let Ty::FnDef(id, fndef_args) = rcvr {
                let func = tcx.get_item(id).unwrap_fn();
                infer_ctx.eq(
                    *func.ret_ty.instantiate(fndef_args, tcx.tcx()),
                    Ty::Infer(node_tys[&this_expr.id]),
                    span,
                );

                if func.params.len() != args.len() {
                    let err = diag_wrong_number_fn_args(func.params, args, span);
                    tcx.tcx().err(err);
                }

                for (param, arg) in func.params.iter().zip(args.iter()) {
                    let id = infer_ctx.new_var(arg.span());
                    node_tys.insert(arg.id, id);
                    infer_ctx.eq(
                        Ty::Infer(id),
                        *param.ty.instantiate(fndef_args, tcx.tcx()),
                        arg.span(),
                    );
                    typeck_expr(arg, ast, tcx, resolutions, infer_ctx, node_tys, generics);
                }
            } else {
                let err = diag_fn_call_on_non_fn(tcx.tcx(), rcvr, func.span());
                tcx.tcx().err(err);
                infer_ctx.eq(Ty::Error, Ty::Infer(node_tys[&this_expr.id]), span);
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
