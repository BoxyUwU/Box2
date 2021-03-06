use std::{collections::HashMap, iter::FromIterator};

use crate::{
    ast::*,
    resolve::{DefKind, Res},
    tokenize::{Literal, Span},
};

fn ast_ty_to_ty(ty: &crate::ast::Ty, resolutions: &HashMap<NodeId, Res<NodeId>>) -> Ty {
    let id = match resolutions[&ty.id] {
        Res::Def(DefKind::Adt, id) => id,
        Res::Def(_, _) | Res::Local(_) => unreachable!(),
    };
    Ty::Adt(id)
}

pub fn visit_items<'ast>(
    item: &Item<'ast>,
    ast: &'ast Nodes<'ast>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    f: &mut dyn FnMut(&'_ Item<'ast>),
) {
    f(item);
    match item {
        Item::Fn(_) => return, /* FIXME `fn foo() { fn bar() { ... }} */
        Item::Mod(Module { items, .. }) => {
            for item in *items {
                visit_items(item, ast, resolutions, f);
            }
        }
        Item::TypeDef(_) | Item::VariantDef(_) | Item::FieldDef(_) => return, /* FIXME: field tys are exprs */
        Item::Use(_) => return,
    }
}
pub enum TypeckError {
    ExpectedFound(ExpectedFound),
    UnconstrainedInfer(NodeId, InferId, Span),
}
pub fn typeck_fn<'ast>(
    Fn {
        params,
        ret_ty,
        body,
        ..
    }: &'_ Fn<'ast>,
    ast: &'ast Nodes<'ast>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
) -> (HashMap<NodeId, Ty>, Vec<TypeckError>) {
    // FIXME: param tys wf
    // FIXME: ret tys wf
    let mut infer_ctx = InferCtxt::new();
    let mut node_tys = HashMap::from_iter(params.iter().map(|param| {
        let var = infer_ctx.new_var(param.span);
        let ty = ast_ty_to_ty(param.ty.unwrap(), resolutions);
        infer_ctx.eq(Ty::Infer(var), ty, param.span);
        (param.id, var)
    }));

    let ret_ty_span = ret_ty.map(|ty| ty.span).unwrap_or(Span::new(0..1));
    let var = infer_ctx.new_var(ret_ty_span);
    node_tys.insert(body.id, var);
    let ret_ty = match ret_ty {
        Some(ret_ty) => ast_ty_to_ty(ret_ty, resolutions),
        None => Ty::Unit,
    };
    infer_ctx.eq(Ty::Infer(var), ret_ty, ret_ty_span);

    typeck_expr(body, ast, resolutions, &mut infer_ctx, &mut node_tys);
    let infcx_errs = std::mem::take(&mut infer_ctx.errors);
    node_tys
        .iter()
        .map(|(&id, ty)| (id, infer_ctx.resolve_ty(Ty::Infer(*ty))))
        .fold(
            (
                HashMap::default(),
                infcx_errs
                    .into_iter()
                    .map(TypeckError::ExpectedFound)
                    .collect(),
            ),
            |(mut node_tys, mut unconstrained), (id, ty)| {
                match ty {
                    Ty::Infer(infer_id) => unconstrained.push(TypeckError::UnconstrainedInfer(
                        id,
                        infer_id,
                        infer_ctx.infer_spans[&infer_id],
                    )),
                    _ => {
                        node_tys.insert(id, ty);
                    }
                };
                (node_tys, unconstrained)
            },
        )
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Ty {
    Unit,
    Infer(InferId),
    Adt(NodeId),
    Int,
    Float,
}

impl Ty {
    pub fn pretty<'ast>(self, nodes: &'ast Nodes<'ast>) -> String {
        match self {
            Ty::Unit => "()".into(),
            Ty::Infer(_) => "_".into(),
            Ty::Adt(id) => nodes.get(id).unwrap_type_def().name.into(),
            Ty::Int => "int".into(),
            Ty::Float => "float".into(),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct InferId(usize);

#[derive(Debug)]
pub struct ExpectedFound(pub Ty, pub Ty, pub Span);

#[derive(Debug)]
pub struct InferCtxt {
    next_infer_id: InferId,
    constraints: HashMap<InferId, Ty>,
    infer_spans: HashMap<InferId, Span>,
    errors: Vec<ExpectedFound>,
}

impl InferCtxt {
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
                Ty::Float | Ty::Int | Ty::Adt(_) | Ty::Unit => return ty,
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
            (Ty::Infer(a), Ty::Float | Ty::Int | Ty::Adt(_) | Ty::Unit) => {
                self.constraints.try_insert(a, b).unwrap();
            }
            (Ty::Float | Ty::Adt(_) | Ty::Int | Ty::Unit, Ty::Infer(b)) => {
                self.constraints.try_insert(b, a).unwrap();
            }
            (
                Ty::Adt(_) | Ty::Float | Ty::Unit | Ty::Int,
                Ty::Int | Ty::Adt(_) | Ty::Float | Ty::Unit,
            ) => match a == b {
                true => (),
                false => self.errors.push(ExpectedFound(a, b, span)),
            },
        }
    }
}

pub fn typeck_expr<'ast>(
    this_expr: &Expr<'ast>,
    ast: &'ast Nodes<'ast>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    infer_ctx: &mut InferCtxt,
    node_tys: &mut HashMap<NodeId, InferId>,
) {
    match this_expr.kind {
        ExprKind::Let(binding, rhs, span) => {
            infer_ctx.eq(Ty::Infer(node_tys[&this_expr.id]), Ty::Unit, span);

            let pat_var = infer_ctx.new_var(binding.span);
            node_tys.insert(binding.id, pat_var);
            let rhs_var = infer_ctx.new_var(rhs.span());
            node_tys.insert(rhs.id, rhs_var);
            infer_ctx.eq(Ty::Infer(pat_var), Ty::Infer(rhs_var), span);
            typeck_expr(rhs, ast, resolutions, infer_ctx, node_tys);
        }
        ExprKind::Block(stmts, block_span) => {
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
        ExprKind::TypeInit(TypeInit {
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
        ExprKind::Path(Path { span, .. }) => {
            let res_ty = match resolutions[&this_expr.id] {
                Res::Local(id) => Ty::Infer(node_tys[&id]),
                _ => todo!(),
            };
            infer_ctx.eq(res_ty, Ty::Infer(node_tys[&this_expr.id]), span);
        }
        ExprKind::Lit(Literal::Int(_), span) => {
            infer_ctx.eq(Ty::Int, Ty::Infer(node_tys[&this_expr.id]), span)
        }
        ExprKind::Lit(Literal::Float(_), span) => {
            infer_ctx.eq(Ty::Float, Ty::Infer(node_tys[&this_expr.id]), span)
        }

        ExprKind::BinOp(_, _, _, _) => todo!(),
        ExprKind::UnOp(_, _, _) => todo!(),
        ExprKind::FnCall(_) => todo!(),

        ExprKind::FieldInit(_) => unreachable!(),
    }
}
