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
        let bindings = HashMap::from_iter(module.items.iter().flat_map(|&node| {
            Some(match &node.kind {
                NodeKind::Fn(func) => (func.name.clone(), node.id),
                NodeKind::TypeDef(ty_def) => (ty_def.name.clone(), node.id),
                NodeKind::Mod(module) => (module.name.clone(), node.id),
                _ => return None,
            })
        }));

        self.with_rib(Rib { bindings }, |this| {
            for item in module.items.iter() {
                match &item.kind {
                    NodeKind::Fn(_) => this.resolve_fn(item),
                    NodeKind::Mod(module) => this.resolve_mod(module),
                    NodeKind::TypeDef(_) => this.resolve_type_def(item),
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
                ty_def.variants.iter().for_each(|variant| {
                    this.resolve_variant_def(variant.kind.unwrap_variant_def());
                })
            },
        );
    }

    fn resolve_variant_def(&mut self, node: &VariantDef) {
        use std::iter::FromIterator;
        let bindings = HashMap::from_iter(node.type_defs.iter().map(|ty_def_node| {
            (
                ty_def_node.kind.unwrap_type_def().name.clone(),
                ty_def_node.id,
            )
        }));

        self.with_rib(Rib { bindings }, |this| {
            for &field_node in node.field_defs.iter() {
                let field = field_node.kind.unwrap_field_def();
                match &field.ty.kind {
                    NodeKind::TypeDef(_) => this.resolve_type_def(field.ty),
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

    fn resolve_fn(&mut self, node: &Node) {
        let func = unwrap_matches!(&node.kind, NodeKind::Fn(f) => f);

        self.with_rib(
            Rib {
                bindings: HashMap::from([(func.name.clone(), node.id)]),
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

                for field_init_node in &ty_init.field_inits {
                    let field_init_id = field_init_node.id;
                    let field_init = unwrap_matches!(
                        field_init_node.kind.unwrap_expr(),
                        Expr {
                            kind: ExprKind::FieldInit(f),
                            ..
                        } => f
                    );

                    self.resolve_expr(field_init.expr.kind.unwrap_expr());

                    if let Some(&res) = self.resolutions.get(&path.id) {
                        match &self.nodes.get(res).kind {
                            NodeKind::TypeDef(ty_def) => {
                                if ty_def.variants.len() > 1
                                    || ty_def.variants[0].kind.unwrap_variant_def().name.is_some()
                                {
                                    let path =
                                        unwrap_matches!(&path.kind, ExprKind::Path(path) => path);
                                    let ty_span = path.segments.last().unwrap().1.clone();
                                    self.errors.push(
                                        Diagnostic::error()
                                            .with_message("type init expr on type with variants")
                                            .with_labels(vec![Label::primary(0, ty_span)]),
                                    );
                                } else {
                                    let variant_def = ty_def.variants[0].kind.unwrap_variant_def();
                                    let mut resolved = false;
                                    for field in variant_def.field_defs.iter() {
                                        if &field_init.ident == &field.kind.unwrap_field_def().name
                                        {
                                            self.resolutions.insert(field_init_id, field.id);
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
                            }
                            NodeKind::VariantDef(variant_def) => {
                                let mut resolved = false;
                                for field in variant_def.field_defs.iter() {
                                    if &field_init.ident == &field.kind.unwrap_field_def().name {
                                        self.resolutions.insert(field_init_id, field.id);
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
                            _ => {
                                let path =
                                    unwrap_matches!(&path.kind, ExprKind::Path(path) => path);
                                let path_span = path.segments.last().unwrap().1.clone();
                                self.errors.push(
                                    Diagnostic::error()
                                        .with_message("type init expr not on a type")
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
            let item_name: for<'a> fn(&'a NodeKind<'a>) -> &'a String = |item| match item {
                NodeKind::Mod(module) => &module.name,
                NodeKind::Fn(func) => &func.name,
                NodeKind::TypeDef(ty_def) => &ty_def.name,
                NodeKind::VariantDef(variant_def) => variant_def.name.as_ref().unwrap(),
                _ => panic!(""),
            };

            let mut current_scope = initial_res.unwrap();
            for (segment, span) in rest {
                let node = self.nodes.get(current_scope);
                match &node.kind {
                    NodeKind::Mod(module) => {
                        let mut resolved = false;
                        for item_node in &module.items {
                            if &segment == &item_name(&item_node.kind) {
                                current_scope = item_node.id;
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
                    NodeKind::VariantDef(def)
                    | NodeKind::TypeDef(TypeDef {
                        variants:
                            box [Node {
                                kind: NodeKind::VariantDef(def @ VariantDef { name: None, .. }),
                                ..
                            }],
                        ..
                    }) => {
                        let mut resolved = false;
                        for ty_node in def.type_defs.iter() {
                            if &segment == &item_name(&ty_node.kind) {
                                current_scope = ty_node.id;
                                resolved = true;
                                break;
                            }
                        }

                        if resolved == false {
                            self.errors.push(diag_unresolved(segment, span.clone()));
                            return;
                        }
                    }
                    NodeKind::TypeDef(ty_def) => {
                        // variants
                        let mut resolved = false;
                        for variant in ty_def.variants.iter() {
                            if &segment == &item_name(&variant.kind) {
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
                    _ => panic!(""),
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

        let ty_def = root_mod.items[0].kind.unwrap_type_def();
        let variant_def = ty_def.variants[0].kind.unwrap_variant_def();

        let anon_ty_id = variant_def.type_defs[0].id;
        let other_field_def = variant_def.field_defs[1].kind.unwrap_field_def();

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
