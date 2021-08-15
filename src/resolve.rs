use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::ast::*;
use std::collections::HashMap;

struct Resolver<'ast> {
    nodes: &'ast Nodes<'ast>,
    resolutions: HashMap<NodeId, NodeId>,
    ribs: Vec<Rib>,
    errors: Vec<Diagnostic<usize>>,
}

#[derive(Debug)]
struct Rib {
    bindings: HashMap<String, NodeId>,
}

impl<'ast> Resolver<'ast> {
    fn new(nodes: &'ast Nodes<'ast>) -> Self {
        Self {
            nodes,
            resolutions: HashMap::new(),
            ribs: Vec::new(),
            errors: Vec::new(),
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
        let bindings = HashMap::from_iter(module.items.iter().flat_map(|&item| {
            Some(match item {
                Item::Fn(func) => (func.name.clone(), func.id),
                Item::TypeDef(ty_def) => (ty_def.name.clone(), ty_def.id),
                Item::Mod(module) => (module.name.clone(), module.id),
                Item::VariantDef(..) | Item::FieldDef(..) => unreachable!(),
            })
        }));

        self.with_rib(Rib { bindings }, |this| {
            for &item in module.items.iter() {
                match item {
                    Item::Fn(func) => this.resolve_fn(func),
                    Item::Mod(module) => this.resolve_mod(module),
                    Item::TypeDef(ty_def) => this.resolve_type_def(ty_def),
                    Item::VariantDef(..) | Item::FieldDef(..) => unreachable!(),
                }
            }
        })
    }

    fn resolve_type_def(&mut self, ty_def: &TypeDef) {
        self.with_rib(
            Rib {
                bindings: HashMap::new(),
            },
            |this| {
                ty_def
                    .variants
                    .iter()
                    .for_each(|variant| this.resolve_variant_def(variant))
            },
        );
    }

    fn resolve_variant_def(&mut self, node: &VariantDef) {
        use std::iter::FromIterator;
        let bindings = HashMap::from_iter(
            node.type_defs
                .iter()
                .map(|ty_def_node| (ty_def_node.name.clone(), ty_def_node.id)),
        );

        self.with_rib(Rib { bindings }, |this| {
            for &field in node.field_defs.iter() {
                match &field.ty.kind {
                    NodeKind::Item(Item::TypeDef(ty_def)) => this.resolve_type_def(ty_def),
                    NodeKind::Ty(Ty { path })
                    | NodeKind::Expr(Expr {
                        kind: ExprKind::Path(path),
                        ..
                    }) => this.resolve_path(field.ty.id, path),
                    _ => unreachable!(),
                }
            }
        })
    }

    fn resolve_fn(&mut self, func: &Fn) {
        self.with_rib(
            Rib {
                bindings: HashMap::from([(func.name.clone(), func.id)]),
            },
            |this| this.resolve_expr(func.body.kind.unwrap_expr()),
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
                        this.resolve_expr(expr.kind.unwrap_expr());
                    }
                },
            ),
            ExprKind::UnOp(_, rhs) => self.resolve_expr(rhs.kind.unwrap_expr()),
            ExprKind::BinOp(BinOp::Dot, lhs, _) => {
                self.resolve_expr(lhs.kind.unwrap_expr());
            }
            ExprKind::BinOp(_, lhs, rhs) => {
                self.resolve_expr(lhs.kind.unwrap_expr());
                self.resolve_expr(rhs.kind.unwrap_expr());
            }
            ExprKind::Lit(_) => (),
            ExprKind::Let(name, rhs) => {
                self.ribs
                    .last_mut()
                    .unwrap()
                    .bindings
                    .insert(name.to_owned(), expr.id);
                self.resolve_expr(rhs.kind.unwrap_expr());
            }
            ExprKind::Path(path) => self.resolve_path(expr.id, path),
            ExprKind::TypeInit(ty_init) => {
                let path = ty_init.path.kind.unwrap_expr();
                self.resolve_expr(path);

                for field_init in &ty_init.field_inits {
                    self.resolve_expr(field_init.expr.kind.unwrap_expr());

                    if let Some(&res) = self.resolutions.get(&path.id) {
                        match &self.nodes.get(res).kind {
                            NodeKind::Item(Item::VariantDef(variant_def))
                            | &NodeKind::Item(Item::TypeDef(TypeDef {
                                variants: box [variant_def @ VariantDef { name: None, .. }],
                                ..
                            })) => {
                                let mut resolved = false;
                                for field in variant_def.field_defs.iter() {
                                    if &field_init.ident == &field.name {
                                        self.resolutions.insert(field_init.id, field.id);
                                        resolved = true;
                                        break;
                                    }
                                }

                                if resolved == false {
                                    self.errors.push(diag_unresolved(
                                        &field_init.ident,
                                        field_init.span.clone(),
                                    ));
                                }
                            }
                            res => {
                                let message = match res {
                                    NodeKind::Item(Item::TypeDef(..)) => {
                                        "type init expr on type with variants"
                                    }
                                    _ => "type init expr not on a type",
                                };

                                let path =
                                    unwrap_matches!(&path.kind, ExprKind::Path(path) => path);
                                let path_span = path.segments.last().unwrap().1.clone();
                                self.errors.push(
                                    Diagnostic::error()
                                        .with_message(message)
                                        .with_labels(vec![Label::primary(0, path_span)]),
                                )
                            }
                        }
                    }
                }
            }
            ExprKind::FieldInit(..) => panic!(""),
            ExprKind::FnCall(fn_call) => {
                self.resolve_expr(fn_call.func.kind.unwrap_expr());
                for expr in fn_call.args.iter().map(|arg| arg.kind.unwrap_expr()) {
                    self.resolve_expr(expr);
                }
            }
            ExprKind::MethodCall(method_call) => {
                self.resolve_expr(method_call.receiver.kind.unwrap_expr());
                for expr in method_call.args.iter().map(|arg| arg.kind.unwrap_expr()) {
                    self.resolve_expr(expr);
                }
            }
        }
    }

    fn resolve_path(&mut self, id: NodeId, path: &Path) {
        let initial = &path.segments[0];
        let mut initial_res = None;
        for rib in self.ribs.iter().rev() {
            if let Some(&node) = rib.bindings.get(&initial.0) {
                initial_res = Some(node);
                break;
            }
        }

        if let None = initial_res {
            self.errors.push(
                Diagnostic::error()
                    .with_message(format!("unable to resolve `{}`", initial.0))
                    .with_labels(vec![Label::primary(0, initial.1.clone())]),
            );
            return;
        }
        let mut final_res = initial_res.unwrap();

        if let [_, rest @ ..] = path.segments.as_slice() {
            let mut current_scope = initial_res.unwrap();
            for (segment, span) in rest {
                match self.nodes.get(current_scope).kind.unwrap_item() {
                    Item::Mod(module) => {
                        let mut resolved = false;
                        for item in &module.items {
                            let item_name = match item {
                                Item::Mod(module) => &module.name,
                                Item::Fn(func) => &func.name,
                                Item::TypeDef(ty_def) => &ty_def.name,
                                Item::VariantDef(variant_def) => variant_def.name.as_ref().unwrap(),
                                Item::FieldDef(..) => unreachable!(),
                            };

                            if segment == item_name {
                                current_scope = item.id();
                                resolved = true;
                                break;
                            }
                        }

                        if resolved == false {
                            self.errors.push(
                                Diagnostic::error()
                                    .with_message(format!("unable to resolve `{}`", segment))
                                    .with_labels(vec![Label::primary(0, span.clone())]),
                            );
                            return;
                        }
                    }
                    Item::VariantDef(def)
                    | &Item::TypeDef(TypeDef {
                        variants: box [def @ VariantDef { name: None, .. }],
                        ..
                    }) => {
                        let mut resolved = false;
                        for ty_def in def.type_defs.iter() {
                            if segment == &ty_def.name {
                                current_scope = ty_def.id;
                                resolved = true;
                                break;
                            }
                        }

                        if resolved == false {
                            self.errors.push(diag_unresolved(segment, span.clone()));
                            return;
                        }
                    }
                    Item::TypeDef(ty_def) => {
                        // variants
                        let mut resolved = false;
                        for variant in ty_def.variants.iter() {
                            if segment == variant.name.as_ref().unwrap() {
                                current_scope = variant.id;
                                resolved = true;
                                break;
                            }
                        }

                        if resolved == false {
                            self.errors.push(diag_unresolved(segment, span.clone()));
                            return;
                        }
                    }
                    Item::FieldDef(..) | Item::Fn(..) => unreachable!(),
                }
            }

            final_res = current_scope;
        }

        self.resolutions.insert(id, final_res);
    }
}

fn diag_unresolved(unresolved: &str, span: logos::Span) -> Diagnostic<usize> {
    Diagnostic::error()
        .with_message(format!("failed to resolve {}", unresolved))
        .with_labels(vec![Label::primary(0, span)])
}

#[cfg(test)]
mod test {
    use crate::{ast::*, resolve::Resolver, tokenize::Tokenizer};

    #[test]
    fn resolve_method_call() {
        let code = "
        type Foo {}
        
        fn bar() {
            Foo.bar(10 + 2);
            Foo.bar.baz.blah.aaaaa();
        }";

        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(&mut Tokenizer::new(code), &nodes).unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(root.kind.unwrap_mod());

        // for diag in resolver.errors.iter() {
        //     let mut files = codespan_reporting::files::SimpleFiles::new();
        //     files.add("main.box", code);
        //     let writer = codespan_reporting::term::termcolor::StandardStream::stderr(
        //         codespan_reporting::term::termcolor::ColorChoice::Always,
        //     );
        //     let config = codespan_reporting::term::Config::default();
        //     codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
        // }

        assert_eq!(resolver.errors.len(), 0);
    }

    #[test]
    fn resolve_method_call_fail() {
        let code = "
        fn bar() {
            foo.bar(10 + 2);
        }";

        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(&mut Tokenizer::new(code), &nodes).unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(root.kind.unwrap_mod());

        // for diag in resolver.errors.iter() {
        //     let mut files = codespan_reporting::files::SimpleFiles::new();
        //     files.add("main.box", code);
        //     let writer = codespan_reporting::term::termcolor::StandardStream::stderr(
        //         codespan_reporting::term::termcolor::ColorChoice::Always,
        //     );
        //     let config = codespan_reporting::term::Config::default();
        //     codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
        // }

        assert_eq!(resolver.errors.len(), 1);
    }

    #[test]
    fn resolve_fn_call() {
        let code = "
        fn foo() {
            foo();
            foo(1 + 2);
            foo(1 + 2,);
            foo(1 + 2, foo());
        }
        
        fn bar() {
            foo(bar(foo()));
        }";

        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(&mut Tokenizer::new(code), &nodes).unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(root.kind.unwrap_mod());

        // for diag in resolver.errors.iter() {
        //     let mut files = codespan_reporting::files::SimpleFiles::new();
        //     files.add("main.box", code);
        //     let writer = codespan_reporting::term::termcolor::StandardStream::stderr(
        //         codespan_reporting::term::termcolor::ColorChoice::Always,
        //     );
        //     let config = codespan_reporting::term::Config::default();
        //     codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
        // }

        assert_eq!(resolver.errors.len(), 0);
    }

    #[test]
    fn resolve_type_init_fail() {
        let code = "
            type FieldTy {}

            type Foo {
                field: FieldTy,
            }

            type Bar {
                | Baz { field: FieldTy }
            }

            fn foo() {
                Foo {
                    field_awd: FieldTy,
                };

                Bar {
                    field: 10,
                };

                Bar::Bazz {}

                Blah {}
            }
        ";

        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(&mut Tokenizer::new(code), &nodes).unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(root.kind.unwrap_mod());

        // for diag in resolver.errors.iter() {
        //     let mut files = codespan_reporting::files::SimpleFiles::new();
        //     files.add("main.box", code);
        //     let writer = codespan_reporting::term::termcolor::StandardStream::stderr(
        //         codespan_reporting::term::termcolor::ColorChoice::Always,
        //     );
        //     let config = codespan_reporting::term::Config::default();
        //     codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
        // }

        assert_eq!(resolver.errors.len(), 4);
    }

    #[test]
    fn resolve_type_init() {
        let code = "
            type FieldTy {}

            type Foo {
                field: FieldTy,
                fielddd: FieldTy,
            }

            type FooTwo {
                | Bar {
                    field: FieldTy,
                }
            }

            type Nested {
                | Foo {
                    field: type {
                        | Baz {
                            inner: FieldTy
                        }
                    }
                }
            }

            fn foo() {
                FieldTy {};

                Foo {
                    field: 10 + 2,
                    fielddd: 12 + 13
                };

                FooTwo::Bar {
                    field: 122222,
                };

                Nested::Foo::Field::Baz {
                    inner: 12,
                };

                Nested::Foo {
                    field: Nested::Foo::Field::Baz {
                        inner: 10000,
                    },
                };
            }
        ";

        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(&mut Tokenizer::new(code), &nodes).unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(root.kind.unwrap_mod());

        assert_eq!(resolver.errors.len(), 0);
    }

    #[test]
    fn resolve_paths() {
        let code = "
            type Foo {
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
            }";
        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(&mut Tokenizer::new(code), &nodes).unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(root.kind.unwrap_mod());

        assert_eq!(resolver.errors.len(), 0);
    }

    #[test]
    fn resolve_type_def() {
        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(
            &mut Tokenizer::new(
                "type Foo { 
                    field: type {}, 
                    other_field: Field, 
                }",
            ),
            &nodes,
        )
        .unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(root.kind.unwrap_mod());

        let root_mod = root.kind.unwrap_mod();

        let ty_def = unwrap_matches!(root_mod.items[0], Item::TypeDef(ty_def) => ty_def);
        let variant_def = ty_def.variants[0];

        let anon_ty_id = variant_def.type_defs[0].id;
        let other_field_def = variant_def.field_defs[1];

        assert_eq!(resolver.resolutions[&other_field_def.ty.id], anon_ty_id);
        assert_eq!(resolver.errors.len(), 0);
    }

    #[test]
    fn let_stmt() {
        let nodes = Nodes::new();
        let root = crate::parser::parse_block_expr(
            &mut Tokenizer::new("{ let foo = 10; foo + 1; }"),
            &nodes,
        )
        .unwrap();
        let stmts = unwrap_matches!(&root.kind.unwrap_expr().kind, ExprKind::Block(stmts) => stmts);

        let let_id = stmts[0].0.id;
        let foo_ident = unwrap_matches!(
            &stmts[1].0.kind.unwrap_expr().kind,
            ExprKind::BinOp(_, lhs, _) => lhs.id
        );

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_expr(root.kind.unwrap_expr());

        assert_eq!(resolver.resolutions[&foo_ident], let_id);
        assert_eq!(resolver.errors.len(), 0);
    }

    #[test]
    fn nested_block() {
        let nodes = Nodes::new();
        let root = crate::parser::parse_block_expr(
            &mut Tokenizer::new("{ { let foo = 1; } foo + 1; }"),
            &nodes,
        )
        .unwrap();
        let stmts = unwrap_matches!(&root.kind.unwrap_expr().kind, ExprKind::Block(stmts) => stmts);

        let foo_ident = unwrap_matches!(
            &stmts[1].0.kind.unwrap_expr().kind,
            ExprKind::BinOp(_, lhs, _) => lhs.id
        );

        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_expr(root.kind.unwrap_expr());

        assert!(resolver.resolutions.get(&foo_ident).is_none());
        assert_eq!(resolver.errors.len(), 1);
    }
}
