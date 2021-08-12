use crate::ast::*;
use std::collections::HashMap;

#[derive(Debug)]
struct Resolver<'ast> {
    nodes: &'ast Nodes,
    resolutions: HashMap<NodeId, NodeId>,
    ribs: Vec<Rib>,
}

#[derive(Debug)]
struct Rib {
    bindings: HashMap<String, NodeId>,
}

impl<'ast> Resolver<'ast> {
    fn new(nodes: &'ast Nodes) -> Self {
        Self {
            nodes,
            resolutions: HashMap::new(),
            ribs: Vec::new(),
        }
    }

    fn with_rib<T>(&mut self, rib: Rib, f: impl FnOnce(&mut Resolver<'ast>) -> T) -> T {
        self.ribs.push(rib);
        let ret = f(self);
        self.ribs.pop();
        ret
    }

    fn resolve_type_def(&mut self, node: &Node) {
        let ty_def = unwrap_matches!(&node.kind, NodeKind::TypeDef(ty) => ty);

        self.with_rib(
            Rib {
                bindings: HashMap::new(),
            },
            |this| {
                ty_def.variants.iter().for_each(|id| {
                    let variant = this.nodes.variant_def(*id);
                    this.resolve_variant_def(variant);
                })
            },
        );
    }

    fn resolve_variant_def(&mut self, node: &VariantDef) {
        use std::iter::FromIterator;
        let bindings = HashMap::from_iter(
            node.type_defs
                .iter()
                .map(|id| (self.nodes.type_def(*id).name.clone(), *id)),
        );

        self.with_rib(Rib { bindings }, |this| {
            for &field_id in node.field_defs.iter() {
                let field = this.nodes.field_def(field_id);
                let node = &this.nodes.0[field.ty.0];
                match &node.kind {
                    NodeKind::Expr(Expr {
                        kind: ExprKind::Ident(i),
                        ..
                    }) => this.resolve_ident(field.ty, i),
                    NodeKind::TypeDef(_) => this.resolve_type_def(node),
                    _ => unreachable!(),
                }
            }
        })
    }

    fn resolve_fn(&mut self, node: &Node) {
        let func = unwrap_matches!(&node.kind, NodeKind::Fn(f) => f);

        self.with_rib(
            Rib {
                bindings: HashMap::from([(func.name.clone(), node.id)]),
            },
            |this| this.resolve_expr(this.nodes.expr(func.body)),
        );
    }

    fn resolve_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Block(stmts) => self.with_rib(
                Rib {
                    bindings: HashMap::new(),
                },
                |this| {
                    for &(expr, _) in stmts {
                        this.resolve_expr(this.nodes.expr(expr));
                    }
                },
            ),
            ExprKind::UnOp(_, rhs) => self.resolve_expr(self.nodes.expr(*rhs)),
            ExprKind::BinOp(_, lhs, rhs) => {
                self.resolve_expr(self.nodes.expr(*lhs));
                self.resolve_expr(self.nodes.expr(*rhs));
            }
            ExprKind::Lit(_) => (),
            ExprKind::Ident(ident) => self.resolve_ident(expr.id, ident),
            ExprKind::Let(name, rhs) => {
                self.ribs
                    .last_mut()
                    .unwrap()
                    .bindings
                    .insert(name.to_owned(), expr.id);
                self.resolve_expr(self.nodes.expr(*rhs));
            }
        }
    }

    fn resolve_ident(&mut self, id: NodeId, ident: &String) {
        for rib in self.ribs.iter().rev() {
            if let Some(&node) = rib.bindings.get(ident) {
                self.resolutions.insert(id, node);
                return;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{ast::*, resolve::Resolver, tokenize::Tokenizer};

    #[test]
    fn resolve_type_def() {
        let mut nodes = Nodes(vec![]);
        let root = crate::parser::parse_type_def(
            &mut Tokenizer::new(
                "type Foo { 
                    field: type {}, 
                    other_field: Field, 
                }",
            ),
            &mut nodes,
            None,
        )
        .unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_type_def(&nodes.0[root.0]);

        let ty_def = nodes.type_def(root);
        let variant_def = nodes.variant_def(ty_def.variants[0]);

        let anon_ty_id = variant_def.type_defs[0];
        let other_field_def = nodes.field_def(variant_def.field_defs[1]);

        assert_eq!(resolver.resolutions[&other_field_def.ty], anon_ty_id);
    }

    #[test]
    fn let_stmt() {
        let mut nodes = Nodes(vec![]);
        let root = crate::parser::parse_block_expr(
            &mut Tokenizer::new("{ let foo = 10; foo + 1; }"),
            &mut nodes,
        )
        .unwrap();
        let stmts = unwrap_matches!(&nodes.expr(root).kind, ExprKind::Block(stmts) => stmts);

        let let_id = stmts[0].0;
        let foo_ident =
            unwrap_matches!(&nodes.expr(stmts[1].0).kind, ExprKind::BinOp(_, lhs, _) => lhs);

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_expr(nodes.expr(root));

        assert_eq!(resolver.resolutions[foo_ident], let_id);
    }

    #[test]
    fn nested_block() {
        let mut nodes = Nodes(vec![]);
        let root = crate::parser::parse_block_expr(
            &mut Tokenizer::new("{ { let foo = 1; } foo + 1; }"),
            &mut nodes,
        )
        .unwrap();
        let stmts = unwrap_matches!(&nodes.expr(root).kind, ExprKind::Block(stmts) => stmts);

        let foo_ident =
            unwrap_matches!(&nodes.expr(stmts[1].0).kind, ExprKind::BinOp(_, lhs, _) => lhs);

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_expr(nodes.expr(root));

        assert!(resolver.resolutions.get(foo_ident).is_none());
    }
}
