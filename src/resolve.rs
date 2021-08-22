use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::ast::*;
use crate::tokenize::Span;
use std::collections::HashMap;
use std::thread::current;

struct Resolver<'ast> {
    nodes: &'ast Nodes<'ast>,
    resolutions: HashMap<NodeId, NodeId>,
    ribs: Vec<Rib>,
    errors: Vec<Diagnostic<usize>>,
    // used to prevent cycles when resolving use statements
    use_item_stack: Vec<NodeId>,
}

#[derive(Debug)]
struct Rib {
    bindings: HashMap<String, NodeId>,
}

impl<'ast> Resolver<'ast> {
    fn debug_out_errors(&mut self, code: &str) {
        for diag in self.errors.iter() {
            let mut files = codespan_reporting::files::SimpleFiles::new();
            files.add("main.box", code);
            let writer = codespan_reporting::term::termcolor::StandardStream::stderr(
                codespan_reporting::term::termcolor::ColorChoice::Always,
            );
            let config = codespan_reporting::term::Config::default();
            codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
        }
    }

    fn new(nodes: &'ast Nodes<'ast>) -> Self {
        let mut this = Self {
            nodes,
            resolutions: HashMap::new(),
            ribs: Vec::new(),
            errors: Vec::new(),
            use_item_stack: Vec::new(),
        };

        let num_nodes = this.nodes.arena.len();
        if num_nodes > 0 {
            this.early_resolve_mod(this.nodes.get(NodeId(num_nodes - 1)).unwrap_mod());
        }

        this
    }

    fn with_rib<T>(&mut self, rib: Rib, f: impl FnOnce(&mut Resolver<'ast>) -> T) -> T {
        self.ribs.push(rib);
        let ret = f(self);
        self.ribs.pop();
        ret
    }

    fn resolve_mod(&mut self, module: &Module) {
        use std::iter::FromIterator;
        let bindings = HashMap::from_iter(module.items.iter().map(|&item| match item {
            Item::Use(u) => (
                // we resolve use stmts before nameres
                u.path.segments.last().unwrap().0.to_owned(),
                self.resolutions[&u.id],
            ),
            Item::Fn(func) => (func.name.to_owned(), func.id),
            Item::TypeDef(ty_def) => (ty_def.name.to_owned(), ty_def.id),
            Item::Mod(module) => (module.name.to_owned(), module.id),
            Item::VariantDef(..) | Item::FieldDef(..) => unreachable!(),
        }));

        self.with_rib(Rib { bindings }, |this| {
            for &item in module.items.iter() {
                match item {
                    Item::Fn(func) => this.resolve_fn(func),
                    Item::Mod(module) => this.resolve_mod(module),
                    Item::TypeDef(ty_def) => this.resolve_type_def(ty_def),
                    Item::Use(..) => (), // we resolve use items before nameres
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
                .map(|type_def| (type_def.name.to_owned(), type_def.id)),
        );

        self.with_rib(Rib { bindings }, |this| {
            for &type_def in node.type_defs.iter() {
                this.resolve_type_def(type_def);
            }
            for &field in node.field_defs.iter() {
                this.resolve_ty(field.ty);
            }
        })
    }

    fn resolve_ty(&mut self, ty: &Ty) {
        self.resolve_path(ty.id, &ty.path);
    }

    fn resolve_fn(&mut self, func: &Fn) {
        self.with_rib(
            Rib {
                bindings: HashMap::from([(func.name.to_owned(), func.id)]),
            },
            |this| this.resolve_expr(func.body),
        );
    }

    fn resolve_expr(&mut self, expr: &Expr) {
        match expr.kind {
            ExprKind::Block(stmts) => self.with_rib(
                Rib {
                    bindings: HashMap::new(),
                },
                |this| {
                    for &(expr, _) in stmts {
                        this.resolve_expr(expr);
                    }
                },
            ),
            ExprKind::UnOp(_, rhs) => self.resolve_expr(rhs),
            ExprKind::BinOp(BinOp::Dot, lhs, _) => {
                self.resolve_expr(lhs);
            }
            ExprKind::BinOp(_, lhs, rhs) => {
                self.resolve_expr(lhs);
                self.resolve_expr(rhs);
            }
            ExprKind::Lit(_) => (),
            ExprKind::Let(name, rhs) => {
                self.ribs
                    .last_mut()
                    .unwrap()
                    .bindings
                    .insert(name.to_owned(), expr.id);
                self.resolve_expr(rhs);
            }
            ExprKind::Path(path) => self.resolve_path(expr.id, &path),
            ExprKind::TypeInit(ty_init) => {
                let path = ty_init.path;
                self.resolve_expr(path);

                for field_init in ty_init.field_inits {
                    self.resolve_expr(field_init.expr);

                    if let Some(&res) = self.resolutions.get(&path.id) {
                        match self.nodes.get(res) {
                            Node::Item(Item::VariantDef(variant_def))
                            | &Node::Item(Item::TypeDef(TypeDef {
                                variants: &[variant_def @ VariantDef { name: None, .. }],
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
                                    self.errors
                                        .push(diag_unresolved(&field_init.ident, field_init.span));
                                }
                            }
                            res => {
                                let message = match res {
                                    Node::Item(Item::TypeDef(..)) => {
                                        "type init expr on type with variants"
                                    }
                                    _ => "type init expr not on a type",
                                };

                                let path =
                                    unwrap_matches!(&path.kind, ExprKind::Path(path) => path);
                                let path_span = path.segments.last().unwrap().1;
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
                self.resolve_expr(fn_call.func);
                for expr in fn_call.args {
                    self.resolve_expr(expr);
                }
            }
            ExprKind::MethodCall(method_call) => {
                self.resolve_expr(method_call.receiver);
                for expr in method_call.args {
                    self.resolve_expr(expr);
                }
            }
        }
    }

    fn resolve_path(&mut self, id: NodeId, path: &Path) {
        let initial = &path.segments[0];
        let mut initial_res = None;
        for rib in self.ribs.iter().rev() {
            if let Some(&node) = rib.bindings.get(&initial.0.to_owned()) {
                initial_res = Some(node);
                break;
            }
        }

        if let None = initial_res {
            self.errors.push(
                Diagnostic::error()
                    .with_message(format!("unable to resolve `{}`", initial.0))
                    .with_labels(vec![Label::primary(0, initial.1)]),
            );
            return;
        }
        let mut final_res = initial_res.unwrap();

        if let Node::Item(Item::Use(u)) = self.nodes.get(final_res) {
            final_res = self.resolutions[&u.id];
        }

        if let [_, rest @ ..] = path.segments {
            let mut current_scope = initial_res.unwrap();
            for (segment, span) in rest {
                match self.nodes.get(current_scope).unwrap_item() {
                    Item::Mod(module) => {
                        let mut resolved = false;
                        for item in module.items {
                            let item_name = match item {
                                Item::Use(u) => {
                                    let use_as = &u.path.segments.last().unwrap().0;
                                    if segment == use_as {
                                        // we resolve use stmts before nameres
                                        current_scope = self.resolutions[&u.id];
                                        resolved = true;
                                    }
                                    break;
                                }
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
                                    .with_labels(vec![Label::primary(0, *span)]),
                            );
                            return;
                        }
                    }
                    Item::VariantDef(def)
                    | &Item::TypeDef(TypeDef {
                        variants: &[def @ VariantDef { name: None, .. }],
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
                            self.errors.push(diag_unresolved(segment, *span));
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
                            self.errors.push(diag_unresolved(segment, *span));
                            return;
                        }
                    }
                    // we replace ids of use stmts with the ids of what they point to
                    // before entering this body, and when we resolve idents of mod children
                    Item::Use(..) => unreachable!(),
                    Item::FieldDef(..) | Item::Fn(..) => unreachable!(),
                }
            }

            final_res = current_scope;
        }

        self.resolutions.insert(id, final_res);
    }
}

impl<'a> Resolver<'a> {
    fn early_resolve_mod(&mut self, module: &Module) {
        for item in module.items {
            match item {
                Item::Use(u) => drop(self.early_resolve_use(module, u)),
                Item::Mod(module) => self.early_resolve_mod(module),
                _ => (),
            }
        }
    }

    fn early_resolve_use(&mut self, module: &Module, u: &Use) -> Result<NodeId, ()> {
        if let Some(n) = self.use_item_stack.iter().position(|&id| id == u.id) {
            let start = self.nodes.get(self.use_item_stack[0]).unwrap_use();
            let &(start, span) = start.path.segments.last().unwrap();
            let cycle_diagnostic = Diagnostic::error()
                .with_message(format!("cyclic use item found: {}", start))
                .with_labels(
                    IntoIterator::into_iter([
                        Label::primary(0, span).with_message("cyclic use item")
                    ])
                    .chain(self.use_item_stack[0..n].iter().map(|node| {
                        let node = self.nodes.get(*node).unwrap_use();
                        let &(_, span) = node.path.segments.last().unwrap();
                        Label::primary(0, span).with_message("requires resolving this use item")
                    }))
                    .chain([Label::primary(0, span).with_message("cycle completed here")])
                    .collect::<Vec<_>>(),
                );
            self.errors.push(cycle_diagnostic);
            return Err(());
        }
        self.use_item_stack.push(u.id);

        let mut prev_seg = module.id;
        for seg in u.path.segments {
            let (_, resolved_to) = match self.nodes.get(prev_seg).unwrap_item() {
                Item::VariantDef(def)
                | Item::TypeDef(TypeDef {
                    variants: &[def @ VariantDef { name: None, .. }],
                    ..
                }) => def
                    .type_defs
                    .iter()
                    .map(|ty_def| (ty_def.name, ty_def.id))
                    .find(|&(name, _)| name == seg.0),
                Item::TypeDef(def) => def
                    .variants
                    .iter()
                    .map(|var_def| (var_def.name.unwrap(), var_def.id))
                    .find(|&(name, _)| name == seg.0),
                Item::Mod(module) => module
                    .items
                    .iter()
                    .map(|item| (item.name().unwrap(), item.id()))
                    .find(|&(name, _)| name == seg.0),
                Item::Fn(..) => None,
                Item::FieldDef(..) | Item::Use(..) => unreachable!(),
            }
            .ok_or_else(|| self.errors.push(diag_unresolved(seg.0, seg.1)))?;

            match self.nodes.get(resolved_to).unwrap_item() {
                Item::Use(u) => {
                    let module = self.nodes.get(prev_seg).unwrap_mod();
                    prev_seg = self.early_resolve_use(module, u)?;
                }
                _ => prev_seg = resolved_to,
            }
        }

        self.use_item_stack.pop();
        self.resolutions.insert(u.id, prev_seg);
        Ok(prev_seg)
    }
}

fn diag_unresolved(unresolved: &str, span: Span) -> Diagnostic<usize> {
    Diagnostic::error()
        .with_message(format!("failed to resolve {}", unresolved))
        .with_labels(vec![Label::primary(0, span)])
}

#[cfg(test)]
mod test {
    use crate::{ast::*, resolve::Resolver, tokenize::Tokenizer};

    #[test]
    fn resolve_use_items() {
        let code = "
            mod foo {
                type Foo {}
            }
            use foo::Foo;
            fn bar(arg: Foo) {}
        ";

        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(&mut Tokenizer::new(code), &nodes).unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.debug_out_errors(code);
        assert_eq!(resolver.errors.len(), 0);
        resolver.resolve_mod(root);
        resolver.debug_out_errors(code);
        assert_eq!(resolver.errors.len(), 0);
    }

    #[test]
    fn resolve_use_items_2() {
        let code = "
            mod foo_one {
                mod foo_two {
                    type Other {}
                }
                use foo_two::Other;
            }
            use foo_one::Other;
            fn uses_other(arg: Other) {}
        ";

        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(&mut Tokenizer::new(code), &nodes).unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.debug_out_errors(code);
        assert_eq!(resolver.errors.len(), 0);
        resolver.resolve_mod(root);
        resolver.debug_out_errors(code);
        assert_eq!(resolver.errors.len(), 0);
    }

    #[test]
    fn resolve_use_items_cycles() {
        let code = "
            use Foo;
            use Foo;
        ";

        let nodes = Nodes::new();
        crate::parser::parse_crate(&mut Tokenizer::new(code), &nodes).unwrap();

        let resolver = Resolver::new(&nodes);
        assert_eq!(resolver.errors.len(), 2);
    }

    #[test]
    fn resolve_use_items_3() {
        let code = "
            type Foo {
                field: Bar,
                other_field: type {},
            }

            type WithVariant {
                | Blah { field: type Bar {} },
                | Idk { field: OtherField },
            }

            use Foo::OtherField;
            use WithVariant::Blah::Bar;
        ";

        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(&mut Tokenizer::new(code), &nodes).unwrap();

        let mut resolver = Resolver::new(&nodes);
        resolver.debug_out_errors(code);
        assert_eq!(resolver.errors.len(), 0);
        resolver.resolve_mod(root);
        resolver.debug_out_errors(code);
        assert_eq!(resolver.errors.len(), 0);
    }

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
        resolver.resolve_mod(root);

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
        resolver.resolve_mod(root);

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
        resolver.resolve_mod(root);

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
        resolver.resolve_mod(root);

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
        resolver.resolve_mod(root);

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
        resolver.resolve_mod(root);

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
        resolver.resolve_mod(root);

        let ty_def = unwrap_matches!(root.items[0], Item::TypeDef(ty_def) => ty_def);
        let variant_def = ty_def.variants[0];

        let anon_ty_id = variant_def.type_defs[0].id;
        let other_field_def = variant_def.field_defs[1];

        assert_eq!(resolver.resolutions[&other_field_def.ty.id], anon_ty_id);
        assert_eq!(resolver.errors.len(), 0);
    }

    #[test]
    fn let_stmt() {
        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(
            &mut Tokenizer::new("fn foo() { let bar = 10; bar + 1; }"),
            &nodes,
        )
        .unwrap();
        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(root);
        assert_eq!(resolver.errors.len(), 0);
    }

    #[test]
    fn nested_block() {
        let nodes = Nodes::new();
        let root = crate::parser::parse_crate(
            &mut Tokenizer::new("fn foo() { { let bar = 1; } bar + 1; }"),
            &nodes,
        )
        .unwrap();
        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(root);
        assert_eq!(resolver.errors.len(), 1);
    }
}
