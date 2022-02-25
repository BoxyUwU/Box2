use std::{collections::HashMap, iter::FromIterator};

use crate::{
    ast::*,
    resolve::{DefKind, Res},
};

fn ast_ty_to_ty(ty: &crate::ast::Ty, resolutions: &HashMap<NodeId, Res<NodeId>>) -> Ty {
    let id = match resolutions[&ty.id] {
        Res::Def(DefKind::Adt, id) => id,
        Res::Def(_, _) | Res::Local(_) => unreachable!(),
    };
    Ty::Adt(id)
}

pub fn typeck_item_recursive<'ast>(
    item: &Item<'ast>,
    ast: &'ast Nodes<'ast>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
) {
    match item {
        Item::Fn(Fn {
            params,
            ret_ty,
            body,
            ..
        }) => {
            // FIXME: param tys wf
            // FIXME: ret tys wf
            let mut infer_ctx = InferCtxt::new();
            let mut node_tys = HashMap::from_iter(params.iter().map(|param| {
                let var = infer_ctx.new_var();
                let ty = ast_ty_to_ty(param.ty.unwrap(), resolutions);
                infer_ctx.eq(Ty::Infer(var), ty);
                (param.id, var)
            }));

            let var = infer_ctx.new_var();
            node_tys.insert(body.id, var);
            if let Some(ret_ty) = ret_ty {
                // FIXME add a `()` for none
                let ret_ty = ast_ty_to_ty(ret_ty, resolutions);
                infer_ctx.eq(Ty::Infer(var), ret_ty);
            }

            typeck_expr(body, ast, resolutions, &mut infer_ctx, &mut node_tys);

            dbg!(&body);
            dbg!(node_tys
                .iter()
                .map(|(id, ty)| (id, infer_ctx.resolve_ty(Ty::Infer(*ty))))
                .collect::<Vec<_>>());
            dbg!(&infer_ctx.errors);
            dbg!(resolutions);
        }
        Item::Mod(Module { items, .. }) => {
            for item in *items {
                typeck_item_recursive(item, ast, resolutions);
            }
        }
        Item::TypeDef(_) | Item::VariantDef(_) | Item::FieldDef(_) => return, /* FIXME: field tys are exprs */
        Item::Use(_) => return,
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Ty {
    Infer(InferId),
    Adt(NodeId),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct InferId(usize);

#[derive(Debug)]
pub struct ExpectedFound(Ty, Ty);

#[derive(Debug)]
pub struct InferCtxt {
    next_infer_id: InferId,
    constraints: HashMap<InferId, Ty>,
    errors: Vec<ExpectedFound>,
}

impl InferCtxt {
    fn new() -> Self {
        Self {
            next_infer_id: InferId(0),
            constraints: HashMap::new(),
            errors: Vec::new(),
        }
    }

    fn new_var(&mut self) -> InferId {
        let id = self.next_infer_id;
        self.next_infer_id.0 += 1;
        id
    }

    fn resolve_ty(&self, mut ty: Ty) -> Ty {
        loop {
            let infer = match ty {
                Ty::Adt(_) => return ty,
                Ty::Infer(inf) => inf,
            };

            match self.constraints.get(&infer) {
                None => return ty,
                Some(&resolved_ty) => ty = resolved_ty,
            };
        }
    }

    fn eq(&mut self, a: Ty, b: Ty) {
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
            (Ty::Infer(a), Ty::Adt(_)) => {
                self.constraints.try_insert(a, b).unwrap();
            }
            (Ty::Adt(_), Ty::Infer(b)) => {
                self.constraints.try_insert(b, a).unwrap();
            }
            (Ty::Adt(_), Ty::Adt(_)) => match a == b {
                true => (),
                false => self.errors.push(ExpectedFound(a, b)),
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
        ExprKind::Let(binding, rhs) => {
            let pat_var = infer_ctx.new_var();
            node_tys.insert(binding.id, pat_var);
            let rhs_var = infer_ctx.new_var();
            node_tys.insert(rhs.id, rhs_var);
            infer_ctx.eq(Ty::Infer(pat_var), Ty::Infer(rhs_var));
            typeck_expr(rhs, ast, resolutions, infer_ctx, node_tys);
            // eq self with `()`
        }
        ExprKind::Block(stmts) => {
            // fixme  block layout is fucky
            for (expr, semi) in stmts {
                let var = infer_ctx.new_var();
                node_tys.insert(expr.id, var);
                if *semi == false {
                    infer_ctx.eq(Ty::Infer(var), Ty::Infer(node_tys[&this_expr.id]));
                } else {
                    // eq self with `()`
                }
                typeck_expr(expr, ast, resolutions, infer_ctx, node_tys);
            }
        }
        ExprKind::TypeInit(TypeInit { path, field_inits }) => {
            // validate res?
            let id = match resolutions[&path.id] {
                Res::Def(DefKind::Adt, id) => id,
                _ => unreachable!(),
            };
            infer_ctx.eq(Ty::Adt(id), Ty::Infer(node_tys[&this_expr.id]));

            for field_init in field_inits {
                let var = infer_ctx.new_var();
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
                infer_ctx.eq(field_ty, Ty::Infer(var));
                typeck_expr(field_init.expr, ast, resolutions, infer_ctx, node_tys);
            }
        }
        ExprKind::Path(Path { .. }) => {
            let res_ty = match resolutions[&this_expr.id] {
                Res::Local(id) => Ty::Infer(node_tys[&id]),
                _ => todo!(),
            };
            infer_ctx.eq(res_ty, Ty::Infer(node_tys[&this_expr.id]));
        }
        ExprKind::BinOp(_, _, _) => todo!(),
        ExprKind::UnOp(_, _) => todo!(),
        ExprKind::Lit(_) => todo!(),
        ExprKind::FnCall(_) => todo!(),

        ExprKind::FieldInit(_) => unreachable!(),
    }
}
