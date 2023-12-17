use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::ast::*;
use crate::tokenize::Span;
use std::collections::HashMap;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum DefKind {
    Adt,
    Variant,
    Func,
    Mod,
    Field,
    Trait,
    TypeAlias,
    GenericParam,
}
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Res<Id> {
    Def(DefKind, Id),
    Local(Id),
}

impl Res<NodeId> {
    pub fn from_id<'a>(id: NodeId, nodes: &'a Nodes<'a>) -> Res<NodeId> {
        match nodes.get(id) {
            Node::Item(i) => Res::Def(
                match i {
                    Item::Mod(_) => DefKind::Mod,
                    Item::TypeDef(_) => DefKind::Adt,
                    Item::VariantDef(_) => DefKind::Variant,
                    Item::Fn(_) => DefKind::Func,
                    Item::Use(_) | Item::FieldDef(_) => unreachable!(),
                    Item::Impl(_) => unreachable!(),
                    Item::TypeAlias(_) => DefKind::TypeAlias,
                    Item::Trait(_) => DefKind::Trait,
                },
                id,
            ),
            Node::Param(_) => Res::Local(id),
            Node::Expr(Expr {
                id: _,
                kind: ExprKind::Let(_, _, _),
            }) => Res::Local(id),
            Node::GenericParam(param) => Res::Def(DefKind::GenericParam, param.id),
            Node::PathSeg(_) | Node::Expr(_) | Node::Ty(_) => unreachable!(),
        }
    }
}
impl<Id> Res<Id> {
    pub fn map_id<NewId>(self, f: impl FnOnce(Id) -> NewId) -> Res<NewId> {
        match self {
            Res::Def(d, id) => Res::Def(d, f(id)),
            Res::Local(id) => Res::Local(f(id)),
        }
    }
}

pub struct Resolver<'ast> {
    nodes: &'ast Nodes<'ast>,
    pub resolutions: HashMap<NodeId, Res<NodeId>>,
    ribs: Vec<Rib>,
    pub errors: Vec<Diagnostic<usize>>,
    // used to prevent cycles when resolving use statements
    use_item_stack: Vec<NodeId>,
}

#[derive(Debug)]
struct Rib {
    bindings: HashMap<String, NodeId>,
}
impl Rib {
    fn from_generics(generics: &Generics<'_>) -> Rib {
        Rib {
            bindings: generics
                .params
                .iter()
                .map(|param| (param.name.to_owned(), param.id))
                .collect(),
        }
    }
}

impl<'ast> Resolver<'ast> {
    #[allow(unused)]
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

    pub fn new(nodes: &'ast Nodes<'ast>) -> Self {
        Self {
            nodes,
            resolutions: HashMap::new(),
            ribs: Vec::new(),
            errors: Vec::new(),
            use_item_stack: Vec::new(),
        }
    }

    fn with_rib<T>(&mut self, rib: Rib, f: impl FnOnce(&mut Resolver<'ast>) -> T) -> T {
        self.ribs.push(rib);
        let ret = f(self);
        self.ribs.pop();
        ret
    }

    pub fn resolve_mod(&mut self, module: &Module) {
        use std::iter::FromIterator;
        let bindings = HashMap::from_iter(module.items.iter().flat_map(|&item| {
            Some(match item {
                Item::Use(u) => {
                    // FIXME
                    // remove the flat_map and allow to resolve to an error or something idfk
                    return self
                        .resolve_path(Some(module.id), u.id, &u.path)
                        .ok()
                        .map(|id| (u.name.to_owned(), id));
                }
                Item::Fn(func) => (func.name.to_owned(), func.id),
                Item::TypeDef(ty_def) => (ty_def.name.to_owned(), ty_def.id),
                Item::Mod(module) => (module.name.to_owned(), module.id),
                Item::Trait(t) => (t.ident.to_owned(), t.id),
                Item::TypeAlias(t) => (t.name.to_owned(), t.id),
                Item::Impl(..) => return None,
                Item::VariantDef(..) | Item::FieldDef(..) => unreachable!(),
            })
        }));

        self.with_rib(Rib { bindings }, |this| {
            for &item in module.items.iter() {
                match item {
                    Item::Fn(func) => this.resolve_fn(func),
                    Item::Mod(module) => this.resolve_mod(module),
                    Item::TypeDef(ty_def) => this.resolve_type_def(ty_def),
                    Item::Impl(impl_) => this.resolve_impl(impl_),
                    Item::Trait(trait_) => this.resolve_trait(trait_),
                    Item::TypeAlias(alias) => match alias.ty {
                        Some(ty) => this.resolve_ty(ty),
                        None => (),
                    },
                    Item::Use(..) => (), // handled above when building bindings
                    Item::VariantDef(..) | Item::FieldDef(..) => unreachable!(),
                }
            }
        })
    }

    fn resolve_impl(&mut self, impl_: &Impl<'_>) {
        let Impl {
            id,
            span: _,
            of_trait,
            generics,
            assoc_items,
        } = impl_;

        self.with_rib(Rib::from_generics(&generics), |this| {
            let _ = this.resolve_path(None, *id, of_trait);
            for assoc_item in *assoc_items {
                this.resolve_associated_item(assoc_item);
            }
        });
    }

    fn resolve_trait(&mut self, trait_: &Trait<'_>) {
        let Trait {
            id: _,
            span: _,
            visibility: _,
            ident: _,
            generics,
            assoc_items,
        } = trait_;
        self.with_rib(Rib::from_generics(generics), |this| {
            for assoc_item in *assoc_items {
                this.resolve_associated_item(assoc_item);
            }
        });
    }

    fn resolve_associated_item(&mut self, assoc_item: &AssocItem<'_>) {
        match assoc_item {
            AssocItem::Fn(f) => self.resolve_fn(f),
            AssocItem::Type(t) => match t.ty {
                Some(ty) => self.resolve_ty(ty),
                None => (),
            },
        }
    }

    fn resolve_type_def(&mut self, ty_def: &TypeDef) {
        self.with_rib(Rib::from_generics(&ty_def.generics), |this| {
            ty_def
                .variants
                .iter()
                .for_each(|variant| this.resolve_variant_def(variant))
        });
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
        match ty.kind {
            TyKind::Path(path) => {
                let _ = self.resolve_path(None, ty.id, &path);
            }
            TyKind::Infer => (),
        }
    }

    fn resolve_fn(&mut self, func: &Fn) {
        self.with_rib(Rib::from_generics(&func.generics), |this| {
            for param in func.params {
                this.resolve_ty(param.ty.unwrap());
            }
            if let Some(ret) = func.ret_ty {
                this.resolve_ty(ret);
            }

            use std::iter::FromIterator;
            if let Some(body) = func.body {
                this.with_rib(
                    Rib {
                        bindings: HashMap::from_iter(
                            func.params
                                .iter()
                                .map(|param| (param.ident.to_string(), param.id)),
                        ),
                    },
                    |this| this.resolve_expr(body),
                );
            }
        })
    }

    fn resolve_expr(&mut self, expr: &Expr) {
        match expr.kind {
            ExprKind::Block(stmts, _) => self.with_rib(
                Rib {
                    bindings: HashMap::new(),
                },
                |this| {
                    for &(expr, _) in stmts {
                        this.resolve_expr(expr);
                    }
                },
            ),
            ExprKind::UnOp(_, rhs, _) => self.resolve_expr(rhs),
            ExprKind::BinOp(BinOp::Dot, lhs, _, _) => {
                self.resolve_expr(lhs);
            }
            ExprKind::BinOp(_, lhs, rhs, _) => {
                self.resolve_expr(lhs);
                self.resolve_expr(rhs);
            }
            ExprKind::Lit(_, _) => (),
            ExprKind::Let(binding, rhs, _) => {
                self.resolve_expr(rhs);
                self.ribs
                    .last_mut()
                    .unwrap()
                    .bindings
                    .insert(binding.ident.to_owned(), binding.id);
            }
            ExprKind::Path(path) => drop(self.resolve_path(None, expr.id, &path)),
            ExprKind::TypeInit(ty_init) => {
                let path = ty_init.path;
                let _ = self.resolve_path(None, expr.id, &path);

                for field_init in ty_init.field_inits {
                    self.resolve_expr(field_init.expr);

                    if let Some(&res) = self.resolutions.get(&expr.id) {
                        let id = match res {
                            Res::Def(DefKind::Variant, id) => id,
                            Res::Def(DefKind::Adt, id) => id,
                            // FIXME: probably ICE
                            Res::Def(
                                DefKind::Trait
                                | DefKind::TypeAlias
                                | DefKind::Field
                                | DefKind::Func
                                | DefKind::Mod
                                | DefKind::GenericParam,
                                _,
                            )
                            | Res::Local(_) => unreachable!(),
                        };

                        match self.nodes.get(id) {
                            Node::Item(Item::VariantDef(variant_def))
                            | &Node::Item(Item::TypeDef(TypeDef {
                                variants: &[variant_def @ VariantDef { name: None, .. }],
                                ..
                            })) => {
                                let mut resolved = false;
                                for field in variant_def.field_defs.iter() {
                                    if &field_init.ident == &field.name {
                                        self.resolutions.insert(
                                            field_init.id,
                                            Res::Def(DefKind::Field, field.id),
                                        );
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

                                let path_span = path.segments.last().unwrap().span;
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
        }
    }

    fn resolve_path(
        &mut self,
        resolve_in_item: Option<NodeId>,
        path_id: NodeId,
        path: &Path,
    ) -> Result<NodeId, ()> {
        // error when attempting to resolve a path that we are already in the process
        // of trying to resolve
        if let Some(n_id) = self.use_item_stack.iter().find(|&&id| id == path_id) {
            let start_use_item = self.nodes.get(self.use_item_stack[0]).unwrap_use();
            let cyclic_use_item = self.nodes.get(*n_id).unwrap_use();
            let cycle_diagnostic = Diagnostic::error()
                .with_message(format!(
                    "Cycle when resolving use item {}",
                    start_use_item.name
                ))
                .with_labels(vec![
                    Label::primary(0, start_use_item.path.segments.last().unwrap().span)
                        .with_message("use item"),
                    Label::secondary(0, cyclic_use_item.path.segments.last().unwrap().span)
                        .with_message("which requires resolving this cyclic use item"),
                ]);
            self.errors.push(cycle_diagnostic);
            return Err(());
        }

        for args in path.segments.iter().map(|segment| segment.args) {
            // FIXME: not super correct wrt `resolve_in_item` maybe just remove that
            self.resolve_gen_args(args)?;
        }

        let first_seg = &path.segments[0];
        let first_seg = match resolve_in_item {
            Some(id) => id,
            None => match self
                .ribs
                .iter()
                .rev()
                .find_map(|rib| rib.bindings.get(first_seg.ident).copied())
            {
                Some(id) => {
                    self.resolutions
                        .insert(first_seg.id, Res::from_id(id, self.nodes));
                    id
                }
                None => {
                    return Err(self
                        .errors
                        .push(diag_unresolved(first_seg.ident, first_seg.span)))
                }
            },
        };

        let res = path
            .segments
            .iter()
            .skip(resolve_in_item.is_none() as usize)
            .try_fold(
                first_seg,
                |prev_segment,
                 PathSeg {
                     ident: segment,
                     span,
                     id: seg_id,
                     ..
                 }| {
                    let opt_res = match self.nodes.get(prev_segment).unwrap_item() {
                        Item::Mod(module) => module
                            .items
                            .iter()
                            .map(|item| (item.name().unwrap(), item.id()))
                            .find(|(name, _)| segment == name),
                        Item::VariantDef(def)
                        | &Item::TypeDef(TypeDef {
                            variants: &[def @ VariantDef { name: None, .. }],
                            ..
                        }) => def
                            .type_defs
                            .iter()
                            .map(|ty_def| (ty_def.name, ty_def.id))
                            .find(|(name, _)| segment == name),
                        Item::TypeDef(ty_def) => ty_def
                            .variants
                            .iter()
                            .map(|variant| (variant.name.unwrap(), variant.id))
                            .find(|(name, _)| segment == name),
                        Item::Fn(..) => None,
                        // we replace prev_segment == Item::Use before continuing to next iterations
                        // and we dont insert resolutions to use items in ribs.
                        // we cannot resolve to field defs
                        Item::Use(..) | Item::FieldDef(..) => unreachable!(),
                        Item::Impl(_) => unreachable!(),
                        Item::TypeAlias(_) => None,
                        Item::Trait(trait_) => trait_
                            .assoc_items
                            .iter()
                            .map(|assoc_item| match assoc_item {
                                AssocItem::Fn(f) => (f.name, f.id),
                                AssocItem::Type(t) => (t.name, t.id),
                            })
                            .find(|(name, _)| segment == name),
                    };

                    let opt_res = opt_res
                        .map(|(_, id)| id)
                        .ok_or_else(|| self.errors.push(diag_unresolved(segment, *span)))
                        .and_then(|id| match self.nodes.get(id) {
                            Node::Item(Item::Use(u)) => {
                                self.use_item_stack.push(path_id);
                                let resolved = self.resolve_path(Some(prev_segment), u.id, &u.path);
                                assert_eq!(self.use_item_stack.pop().unwrap(), path_id);
                                resolved
                            }
                            _ => Ok(id),
                        });

                    if let Ok(id) = opt_res {
                        self.resolutions
                            .insert(*seg_id, Res::from_id(id, self.nodes));
                    }

                    opt_res
                },
            );

        if let Ok(id) = res {
            self.resolutions
                .insert(path_id, Res::from_id(id, self.nodes));
        }
        res
    }

    fn resolve_gen_args(&mut self, args: GenArgs<'_>) -> Result<(), ()> {
        for arg in args.0 {
            match arg {
                GenArg::Ty(ty) => self.resolve_ty(ty),
            };
        }

        Ok(())
    }
}

fn diag_unresolved(unresolved: &str, span: Span) -> Diagnostic<usize> {
    Diagnostic::error()
        .with_message(format!("failed to resolve {}", unresolved))
        .with_labels(vec![Label::primary(0, span)])
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::tokenize::Tokenizer;

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
            &mut Tokenizer::new("fn foo() { { let bar = 1; }; bar + 1; }"),
            &nodes,
        )
        .unwrap();
        let mut resolver = Resolver::new(&nodes);
        resolver.resolve_mod(root);
        assert_eq!(resolver.errors.len(), 1);
    }
}
