use std::{collections::HashMap, iter::FromIterator};

use crate::{
    ast::{self, NodeId, Nodes},
    resolve::{DefKind, Res},
    tir::*,
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

    pub tcx: &'t TirCtx<'t>,
    pub typeck_results: HashMap<TirId, TypeckResults<'t>>,
}

impl<'ast, 'm, 't> visit::Visitor for FnChecker<'ast, 'm, 't> {
    fn visit_fn(&mut self, f: &Fn<'_>) {
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
    Fn { body, generics, .. }: &'_ Fn<'_>,
    tcx: &'t TirCtx<'t>,
    body_sources: &HashMap<BodyId, BodySource<'t>>,
    ast: &'ast Nodes<'ast>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
) -> TypeckResults<'t> {
    // FIXME: param tys wf
    // FIXME: ret tys wf

    let (body_id, body_src) = match body {
        Some(body) => (*body, body_sources[body]),
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
        infer_ctx.eq(Ty::Infer(var), **ty, Span::new(0..1));
        (*node_id, var)
    }));

    let ret_ty_span = Span::new(0..1);
    let var = infer_ctx.new_var(ret_ty_span);
    node_tys.insert(body_src.expr, var);
    infer_ctx.eq(Ty::Infer(var), *body_src.ret, ret_ty_span);

    typeck_expr(body, ast, resolutions, &mut infer_ctx, &mut node_tys);
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

    fn resolve_ty(&self, mut ty: Ty) -> Ty {
        loop {
            let infer = match ty {
                Ty::Float | Ty::Int | Ty::Adt(_, _) | Ty::Unit => return ty,
                Ty::Infer(inf) => inf,
            };

            match self.constraints.get(&infer) {
                None => return ty,
                Some(&resolved_ty) => ty = resolved_ty,
            };
        }
    }

    fn eq(&mut self, a: Ty, b: Ty, span: Span) {
        // FIXME occurs check
        let a = self.resolve_ty(a);
        let b = self.resolve_ty(b);

        match (a, b) {
            (Ty::Infer(a), Ty::Infer(b)) => match a == b {
                true => (),
                false => {
                    self.constraints.try_insert(a, Ty::Infer(b)).unwrap();
                }
            },
            (Ty::Infer(a), Ty::Float | Ty::Int | Ty::Adt(_, _) | Ty::Unit) => {
                self.constraints.try_insert(a, b).unwrap();
            }
            (Ty::Float | Ty::Adt(_, _) | Ty::Int | Ty::Unit, Ty::Infer(b)) => {
                self.constraints.try_insert(b, a).unwrap();
            }
            (
                Ty::Adt(_, _) | Ty::Float | Ty::Unit | Ty::Int,
                Ty::Int | Ty::Adt(_, _) | Ty::Float | Ty::Unit,
            ) => match a == b {
                true => (),
                false => self.errors.push(ExpectedFound(a, b, span)),
            },
        }
    }
}

pub fn typeck_expr<'ast>(
    this_expr: &ast::Expr<'_>,
    ast: &'ast Nodes<'ast>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    infer_ctx: &mut InferCtxt,
    node_tys: &mut HashMap<NodeId, InferId>,
) {
    match this_expr.kind {
        ast::ExprKind::Let(binding, rhs, span) => {
            infer_ctx.eq(Ty::Infer(node_tys[&this_expr.id]), Ty::Unit, span);

            let pat_var = infer_ctx.new_var(binding.span);
            node_tys.insert(binding.id, pat_var);
            let rhs_var = infer_ctx.new_var(rhs.span());
            node_tys.insert(rhs.id, rhs_var);
            infer_ctx.eq(Ty::Infer(pat_var), Ty::Infer(rhs_var), span);
            typeck_expr(rhs, ast, resolutions, infer_ctx, node_tys);
        }
        ast::ExprKind::Block(stmts, block_span) => {
            // fixme  block layout is fucky
            for (expr, _) in stmts {
                let var = infer_ctx.new_var(expr.span());
                node_tys.insert(expr.id, var);
                typeck_expr(expr, ast, resolutions, infer_ctx, node_tys);
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
            let id = match resolutions[&path.id] {
                Res::Def(DefKind::Adt, id) => id,
                Res::Def(DefKind::Variant, id) => ast.get_variants_adt(id).id,
                _ => unreachable!(),
            };
            infer_ctx.eq(Ty::Adt(id), Ty::Infer(node_tys[&this_expr.id]), span);

            for field_init in field_inits {
                let var = infer_ctx.new_var(field_init.span);
                node_tys.insert(field_init.expr.id, var);
                let field_id = match resolutions[&field_init.id] {
                    Res::Def(DefKind::Field, id) => id,
                    _ => unreachable!(),
                };
                let field_def = ast.get(field_id).unwrap_field_def();
                let field_ty = match resolutions[&field_def.ty.id] {
                    Res::Def(DefKind::Adt, id) => Ty::Adt(id),
                    _ => unreachable!(),
                };
                infer_ctx.eq(field_ty, Ty::Infer(var), field_init.span);
                typeck_expr(field_init.expr, ast, resolutions, infer_ctx, node_tys);
            }
        }
        ast::ExprKind::Path(ast::Path { span, .. }) => {
            let res_ty = match resolutions[&this_expr.id] {
                Res::Local(id) => Ty::Infer(node_tys[&id]),
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
        ast::ExprKind::FnCall(_) => todo!(),

        ast::ExprKind::FieldInit(_) => unreachable!(),
    }
}
