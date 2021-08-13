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

    fn resolve_mod(&mut self, module: &Module) {
        use std::iter::FromIterator;
        let bindings = HashMap::from_iter(module.items.iter().flat_map(|&id| {
            let node = &self.nodes.0[id.0];
            Some(match &node.kind {
                NodeKind::Fn(func) => (func.name.clone(), id),
                NodeKind::TypeDef(ty_def) => (ty_def.name.clone(), id),
                NodeKind::Mod(module) => (module.name.clone(), id),
                _ => return None,
            })
        }));

        self.with_rib(Rib { bindings }, |this| {
            for item_id in module.items.iter() {
                let node = &this.nodes.0[item_id.0];
                match &node.kind {
                    NodeKind::Fn(_) => this.resolve_fn(node),
                    NodeKind::Mod(module) => this.resolve_mod(module),
                    NodeKind::TypeDef(_) => this.resolve_type_def(node),
                    _ => unreachable!(),
                }
            }
        })
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
                    NodeKind::Expr(
                        expr
                        @
                        Expr {
                            kind: ExprKind::Path(_),
                            ..
                        },
                    ) => this.resolve_expr(expr),
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
            ExprKind::Path(path) => {
                let initial = &path.segments[0];
                let mut initial_res = None;
                for rib in self.ribs.iter().rev() {
                    if let Some(&node) = rib.bindings.get(&initial.0) {
                        initial_res = Some(node);
                        break;
                    }
                }

                let mut final_res = initial_res.unwrap();
                if let [_, rest @ ..] = path.segments.as_slice() {
                    let item_name: fn(&NodeKind) -> &String = |item| match item {
                        NodeKind::Mod(module) => &module.name,
                        NodeKind::Fn(func) => &func.name,
                        NodeKind::TypeDef(ty_def) => &ty_def.name,
                        NodeKind::VariantDef(variant_def) => variant_def.name.as_ref().unwrap(),
                        _ => panic!(""),
                    };

                    // FIXME emit errors in name res
                    let mut current_scope = initial_res.unwrap();
                    for (segment, _) in rest {
                        let node = &self.nodes.0[current_scope.0];
                        match &node.kind {
                            NodeKind::Mod(module) => {
                                for item in &module.items {
                                    let item_node = &self.nodes.0[item.0];
                                    if &segment == &item_name(&item_node.kind) {
                                        current_scope = item_node.id;
                                        break;
                                    }
                                }
                            }
                            NodeKind::TypeDef(ty_def) => {
                                'arm: loop {
                                    // single anon variant
                                    if let [variant] = ty_def.variants.as_slice() {
                                        let node = &self.nodes.0[variant.0];
                                        if let NodeKind::VariantDef(
                                            def @ VariantDef { name: None, .. },
                                        ) = &node.kind
                                        {
                                            // FIXME dedupe with `NodeKind::VariantDef` branch
                                            for ty_def_id in &def.type_defs {
                                                let ty_node = &self.nodes.0[ty_def_id.0];
                                                if &segment == &item_name(&ty_node.kind) {
                                                    current_scope = *ty_def_id;
                                                    break 'arm;
                                                }
                                            }
                                        }
                                    }

                                    // variants
                                    for variant in &ty_def.variants {
                                        if &segment == &item_name(&self.nodes.0[variant.0].kind) {
                                            current_scope = *variant;
                                            break 'arm;
                                        }
                                    }
                                }
                            }
                            NodeKind::VariantDef(def) => {
                                for ty_def_id in &def.type_defs {
                                    let ty_node = &self.nodes.0[ty_def_id.0];
                                    if &segment == &item_name(&ty_node.kind) {
                                        current_scope = *ty_def_id;
                                        break;
                                    }
                                }
                            }
                            _ => panic!(""),
                        }
                    }

                    final_res = current_scope;
                }

                self.resolutions.insert(expr.id, final_res);
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
    fn resolve_paths() {
        let mut nodes = Nodes(vec![]);
        let root = crate::parser::parse_crate(
            &mut Tokenizer::new(
                "type Foo {
                    field: type {},
                }

                type Other {
                    fffiiield: Foo::Field,
                }

                type EnumIguess {
                    | Blah { f: type {} }
                }

                mod my_module {
                    type MyTYyyyy {
                        inner: EnumIguess::Blah::F,
                    }

                    mod barrrr {
                        type TyTyTy {
                            ffield: type {}
                        }
                    }
                }

                fn foo() {
                    Foo::Field + 10;
                    my_module::barrrr::TyTyTy::Ffield + 10;
                }",
            ),
            &mut nodes,
        )
        .unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(nodes.mod_def(root));

        dbg!(resolver);
    }

    #[test]
    fn resolve_type_def() {
        let mut nodes = Nodes(vec![]);
        let root = crate::parser::parse_crate(
            &mut Tokenizer::new(
                "type Foo { 
                    field: type {}, 
                    other_field: Field, 
                }",
            ),
            &mut nodes,
        )
        .unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(nodes.mod_def(root));

        let root_mod = nodes.mod_def(root);

        let ty_def = nodes.type_def(root_mod.items[0]);
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
