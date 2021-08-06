use crate::ast::*;
use std::collections::HashMap;

struct Resolver<'ast> {
    nodes: &'ast Nodes,
    resolutions: HashMap<NodeId, NodeId>,
    ribs: Vec<Rib>,
}

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
