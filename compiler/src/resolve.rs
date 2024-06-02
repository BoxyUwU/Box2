use std::{cell::RefCell, collections::HashMap, iter, vec};

use crate::{
    ast::{
        self, visit::Visitor, Expr, ExprKind, Impl, Item, Module, Node, NodeId, Nodes, Trait, Ty,
        TypeAlias, TypeDef,
    },
    scopegraph::*,
};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum DefKind {
    Impl,
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
    Err,
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
            Node::Clause(_) | Node::PathSeg(_) | Node::Expr(_) | Node::Ty(_) => unreachable!(),
        }
    }
}
impl<Id> Res<Id> {
    pub fn map_id<NewId>(self, f: impl FnOnce(Id) -> NewId) -> Res<NewId> {
        match self {
            Res::Def(d, id) => Res::Def(d, f(id)),
            Res::Local(id) => Res::Local(f(id)),
            Res::Err => Res::Err,
        }
    }
}

pub enum ResolutionError {
    UnresolvedLexicalIdentifier {
        ident: String,
        in_scope: (NodeId, SGNodeId),
        cause_expr: NodeId,
    },
    UnresolvedAssociatedIdentifier {
        ident: String,
        in_scope: NodeId,
        cause_expr: NodeId,
    },
    UnresolvedField {
        ident: String,
        on_res: NodeId,
        cause_expr: NodeId,
    },
}

#[derive(Copy, Clone)]
pub struct DeferredRes<'ast> {
    start: NodeId,
    path: &'ast ast::Path<'ast>,
}

pub struct Resolver<'ast, 'sg> {
    errors: RefCell<Vec<ResolutionError>>,
    resolutions: HashMap<NodeId, Res<NodeId>>,
    scopegraphs: &'sg HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>>,
}

impl<'ast, 'sg> Resolver<'ast, 'sg> {
    pub fn new(scopegraphs: &'sg HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>>) -> Self {
        Self {
            errors: RefCell::default(),
            resolutions: HashMap::new(),
            scopegraphs,
        }
    }

    pub fn into_outputs(self) -> (Vec<ResolutionError>, HashMap<NodeId, Res<NodeId>>) {
        (self.errors.into_inner(), self.resolutions)
    }

    pub fn resolve_item(&mut self, item: &Item<'_>) {
        match item {
            Item::Mod(m) => self.resolve_mod(m),
            Item::TypeDef(t) => self.resolve_ty_def(t),
            Item::VariantDef(_) | Item::FieldDef(_) => unreachable!(),
            Item::TypeAlias(t) => self.resolve_ty_alias(t),
            Item::Fn(f) => self.resolve_fn(f),
            Item::Use(u) => self.resolve_use(u),
            Item::Trait(trait_) => self.resolve_trait(trait_),
            Item::Impl(impl_) => self.resolve_impl(impl_),
        };
    }

    pub fn resolve_mod(&mut self, module: &Module<'_>) {
        let ast::Module {
            id: _,
            visibility: _,
            name: _,
            items,
        } = module;

        for item in *items {
            self.resolve_item(item);
        }
    }

    pub fn resolve_use(&mut self, u: &ast::Use<'_>) {
        let ast::Use {
            id: _,
            visibility: _,
            path,
            name: _,
        } = u;

        let res = resolve_path(self, path, (u.id, SGNodeId::ROOT));
        let _ = self.record_res(u.id, res);
    }

    pub fn resolve_impl(&mut self, impl_def: &ast::Impl<'_>) {
        let ast::Impl {
            id: _,
            span: _,
            of_trait,
            generics: _,
            bounds: _,
            assoc_items,
        } = impl_def;

        let res = resolve_path(self, of_trait, (impl_def.id, SGNodeId::ROOT));
        let _ = self.record_res(impl_def.id, res);

        for assoc in *assoc_items {
            match assoc {
                ast::AssocItem::Fn(func) => self.resolve_fn(func),
                ast::AssocItem::Type(ty) => self.resolve_ty_alias(ty),
            };
        }
    }

    pub fn resolve_trait(&mut self, trait_def: &ast::Trait<'_>) {
        let ast::Trait {
            id: _,
            span: _,
            visibility: _,
            ident: _,
            generics: _,
            bounds,
            assoc_items,
        } = trait_def;

        self.resolve_bounds(bounds, trait_def.id);
        for assoc in *assoc_items {
            match assoc {
                ast::AssocItem::Fn(func) => self.resolve_fn(func),
                ast::AssocItem::Type(ty) => self.resolve_ty_alias(ty),
            };
        }
    }

    pub fn resolve_ty_alias(&mut self, alias: &ast::TypeAlias<'_>) {
        let ast::TypeAlias {
            id: _,
            visibility: _,
            name: _,
            name_span: _,
            generics: _,
            bounds,
            ty,
        } = alias;

        self.resolve_bounds(bounds, alias.id);
        if let Some(ty) = ty {
            let _ = resolve_ty(self, ty, (alias.id, SGNodeId::ROOT));
        }
    }

    pub fn resolve_fn(&mut self, func: &ast::Fn<'_>) {
        let ast::Fn {
            id: _,
            visibility: _,
            name: _,
            params,
            ret_ty,
            generics: _,
            bounds,
            body,
        } = func;

        self.resolve_bounds(bounds, func.id);
        for ty in params
            .iter()
            .map(|param| param.ty)
            .chain([*ret_ty])
            .flatten()
        {
            // fine to continue on
            let _ = resolve_ty(self, ty, (func.id, SGNodeId::ROOT));
        }

        struct ExprResolver<'a, 'ast, 'sg> {
            resolver: &'a mut Resolver<'ast, 'sg>,
            scope_swap: iter::Peekable<vec::IntoIter<(NodeId, SGNodeId)>>,
            start_from: (NodeId, SGNodeId),
        }

        impl<'a, 'ast, 'sg> ExprResolver<'a, 'ast, 'sg> {
            pub fn new(resolver: &'a mut Resolver<'ast, 'sg>, scopegraph_id: NodeId) -> Self {
                let mut source_to_sg_nodes = resolver.scopegraphs[&scopegraph_id]
                    .source_to_sg_node()
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .into_iter()
                    .peekable();

                Self {
                    resolver,
                    start_from: source_to_sg_nodes.next().unwrap(),
                    scope_swap: source_to_sg_nodes,
                }
            }
        }

        impl<'a, 'ast, 'sg> Visitor for ExprResolver<'a, 'ast, 'sg> {
            fn visit_expr(&mut self, expr: &Expr<'_>) {
                match expr.kind {
                    ExprKind::Let(_, rhs, _) => self.visit_expr(rhs),
                    ExprKind::Block(exprs, _) => {
                        for expr in exprs {
                            self.visit_expr(expr.0);
                        }
                    }
                    ExprKind::BinOp(binop, lhs, rhs, _) => {
                        self.visit_expr(lhs);
                        match binop {
                            ast::BinOp::Add
                            | ast::BinOp::Sub
                            | ast::BinOp::Mul
                            | ast::BinOp::Div
                            | ast::BinOp::Mutate => self.visit_expr(rhs),
                            ast::BinOp::Dot => (),
                        };
                    }
                    ExprKind::UnOp(_, expr, _) => self.visit_expr(expr),
                    ExprKind::Path(path) => {
                        // Dont care
                        let res = resolve_path(self.resolver, &path, self.start_from);
                        let _ = self.resolver.record_res(expr.id, res);
                    }
                    ExprKind::FnCall(ast::FnCall {
                        func,
                        args,
                        span: _,
                    }) => {
                        self.visit_expr(func);
                        for expr in args {
                            self.visit_expr(expr);
                        }
                    }
                    ExprKind::TypeInit(ast::TypeInit {
                        path,
                        field_inits,
                        span: _,
                    }) => {
                        let resolved_ty = resolve_path(self.resolver, &path, self.start_from);
                        let _ = self.resolver.record_res(expr.id, resolved_ty);
                        for ast::FieldInit {
                            id: field_id,
                            ident,
                            span: _,
                            expr,
                        } in field_inits
                        {
                            if let Ok(Res::Def(_, ty_id) | Res::Local(ty_id)) = resolved_ty {
                                let field_res = self
                                    .resolver
                                    .resolve_ident_as_field(ident, ty_id, *field_id);
                                let _ = self.resolver.record_res(*field_id, field_res);
                            }

                            self.visit_expr(expr);
                        }
                    }
                    ExprKind::FieldInit(_) => unreachable!("should have been handled above "),

                    // Nothing to resolve
                    ExprKind::Lit(_, _) => (),
                }

                match self.scope_swap.peek() {
                    Some((id, _)) if *id == expr.id => {
                        self.start_from.1 = self.scope_swap.next().unwrap().1;
                    }
                    _ => (),
                }
            }

            fn visit_mod(&mut self, _module: &Module<'_>) {}
            fn visit_type_def(&mut self, _def: &TypeDef<'_>) {}
            fn visit_variant_def(&mut self, _def: &ast::VariantDef<'_>) {}
            fn visit_field_def(&mut self, _def: &ast::FieldDef<'_>) {}
            fn visit_type_alias(&mut self, _alias: &TypeAlias<'_>) {}
            fn visit_fn(&mut self, _func: &ast::Fn<'_>) {}
            fn visit_use(&mut self, _u: &ast::Use<'_>) {}
            fn visit_trait(&mut self, _trait_: &Trait<'_>) {}
            fn visit_impl(&mut self, _impl_: &Impl<'_>) {}
            fn visit_bounds(&mut self, _bounds: &ast::Bounds<'_>) {}
        }

        if let Some(expr) = body {
            ExprResolver::new(self, func.id).visit_expr(expr);
        }
    }

    pub fn resolve_ty_def(&mut self, adt: &TypeDef<'_>) {
        let TypeDef {
            id: _,
            visibility: _,
            name: _,
            name_span: _,
            generics: _,
            bounds,
            variants,
        } = adt;

        self.resolve_bounds(bounds, adt.id);
        for variant in *variants {
            let ast::VariantDef {
                id: _,
                visibility: _,
                name: _,
                field_defs,
                type_defs,
            } = variant;

            for ty_def in *type_defs {
                self.resolve_ty_def(ty_def);
            }

            for field in *field_defs {
                let ast::FieldDef {
                    id: _,
                    visibility: _,
                    name: _,
                    ty,
                } = field;

                let id = if adt.is_struct() { adt.id } else { variant.id };

                // Resolving fields is not dependent on other fields having resolved. No harm
                // in continueing
                let _ = resolve_ty(self, ty, (id, SGNodeId::ROOT));
            }
        }
    }

    fn sg_node_id_for_bound_clause(&self, bound_clause: NodeId, on_item: NodeId) -> SGNodeId {
        self.scopegraphs[&on_item].bound_clause_to_sg_node(bound_clause)
    }

    fn resolve_bounds(&mut self, bounds: &ast::Bounds<'_>, on_item: NodeId) {
        for clause in bounds.clauses {
            self.resolve_clause(clause, (on_item, SGNodeId::ROOT));
        }
    }

    fn resolve_clause(&mut self, clause: &ast::Clause<'_>, start_from: (NodeId, SGNodeId)) {
        match &clause.kind {
            ast::ClauseKind::Bound(binder) => {
                let sg_node_id = self.sg_node_id_for_bound_clause(clause.id, start_from.0);
                self.resolve_clause(binder.value, (start_from.0, sg_node_id));
            }
            ast::ClauseKind::AliasEq(lhs, rhs) => {
                let _ = resolve_ty(self, lhs, start_from);
                let _ = resolve_ty(self, rhs, start_from);
            }
            ast::ClauseKind::Trait(trait_path) => {
                let res = resolve_path(self, trait_path, start_from);
                let _ = self.record_res(clause.id, res);
            }
        }
    }

    fn resolve_ident_as_field(
        &mut self,
        ident: &str,
        start_from: NodeId,
        cause_expr: NodeId,
    ) -> Result<Res<NodeId>, ()> {
        let query_result = self.query(NameResQuery {
            name: ident.to_owned(),
            start: (start_from, SGNodeId::ROOT),
            edge_filter: vec![EdgeKind::Field],
        });

        match query_result {
            Ok(candidates) => {
                let mut cand_iter = candidates
                    .values()
                    .flat_map(|resolutions| resolutions.into_iter());
                let cand = cand_iter.next().unwrap();
                match cand_iter.next() {
                    None => Ok(*cand),
                    Some(_) => {
                        return self.error(ResolutionError::UnresolvedField {
                            ident: ident.to_owned(),
                            on_res: start_from,
                            cause_expr,
                        })
                    }
                }
            }
            Err(()) => {
                return self.error(ResolutionError::UnresolvedField {
                    ident: ident.to_owned(),
                    on_res: start_from,
                    cause_expr,
                })
            }
        }
    }

    fn error(&self, e: ResolutionError) -> Result<Res<NodeId>, ()> {
        self.errors.borrow_mut().push(e);

        Err(())
    }
}

fn resolve_ty<'ast, R: SomeResolver>(
    resolver: &mut R,
    ty: &Ty<'_>,
    start_from: (NodeId, SGNodeId),
) -> Result<(), ()> {
    match &ty.kind {
        ast::TyKind::Path(path) => {
            let res = resolve_path(resolver, path, start_from);
            resolver.record_res(ty.id, res)?;
        }
        ast::TyKind::Infer => (),
    };

    Ok(())
}

fn resolve_deferred_res<'sg, 'ast>(
    resolver: &mut NameResQueryEvaluator<'sg, DeferredRes<'ast>>,
    deferred: DeferredRes<'ast>,
) -> Res<NodeId> {
    resolve_path(resolver, deferred.path, (deferred.start, SGNodeId::ROOT)).unwrap_or(Res::Err)
}

fn resolve_path<'ast, R: SomeResolver>(
    resolver: &mut R,
    path: &ast::Path<'_>,
    start_from: (NodeId, SGNodeId),
) -> Result<Res<NodeId>, ()> {
    let mut seg_iter = path.segments.iter();

    let result = (|| -> Result<Res<NodeId>, ()> {
        let first_seg = seg_iter.next().unwrap();
        let prev_seg_res =
            resolve_ident_lexically(resolver, first_seg.ident, start_from, first_seg.id);
        let mut prev_seg_res = resolver.record_res(first_seg.id, prev_seg_res)?;
        resolve_gen_args(resolver, &first_seg.args, start_from);

        for cur_seg in &mut seg_iter {
            let inner_start_from = match prev_seg_res {
                Res::Def(_, id) => id,
                Res::Local(id) => id,
                Res::Err => unreachable!(),
            };

            let cur_seg_res =
                resolve_ident_in_item(resolver, cur_seg.ident, inner_start_from, cur_seg.id);
            prev_seg_res = resolver.record_res(cur_seg.id, cur_seg_res)?;
            resolve_gen_args(resolver, &cur_seg.args, start_from);
        }

        Ok(prev_seg_res)
    })();

    match result {
        Ok(res) => Ok(res),
        Err(()) => {
            for seg in seg_iter {
                let _ = resolver.record_res(seg.id, Err(()));
            }
            Err(())
        }
    }
}

fn resolve_gen_args<'ast, R: SomeResolver>(
    resolver: &mut R,
    args: &ast::GenArgs<'_>,
    start_from: (NodeId, SGNodeId),
) {
    for arg in args.0 {
        match arg {
            ast::GenArg::Ty(ty) => {
                let _ = resolve_ty(resolver, ty, start_from);
            }
        }
    }
}

fn resolve_ident_in_item<'ast, R: SomeResolver>(
    resolver: &mut R,
    ident: &str,
    start_from: NodeId,
    cause_expr: NodeId,
) -> Result<Res<NodeId>, ()> {
    let query_result = resolver.query(NameResQuery {
        name: ident.to_owned(),
        start: (start_from, SGNodeId::ROOT),
        edge_filter: vec![EdgeKind::Defines],
    });
    match query_result {
        Ok(candidates) => {
            let mut cand_iter = candidates
                .values()
                .flat_map(|resolutions| resolutions.into_iter());
            let cand = cand_iter.next().unwrap();
            match cand_iter.next() {
                None => Ok(*cand),
                Some(_) => {
                    return resolver.error(ResolutionError::UnresolvedAssociatedIdentifier {
                        ident: ident.to_owned(),
                        in_scope: start_from,
                        cause_expr,
                    })
                }
            }
        }
        Err(()) => {
            return resolver.error(ResolutionError::UnresolvedAssociatedIdentifier {
                ident: ident.to_owned(),
                in_scope: start_from,
                cause_expr,
            })
        }
    }
}

fn resolve_ident_lexically<'ast, R: SomeResolver>(
    resolver: &mut R,
    ident: &str,
    start_from: (NodeId, SGNodeId),
    cause_expr: NodeId,
) -> Result<Res<NodeId>, ()> {
    let query_result = resolver.query(NameResQuery {
        name: ident.to_owned(),
        start: start_from,
        edge_filter: vec![EdgeKind::Defines, EdgeKind::Lexical],
    });

    match query_result {
        Ok(candidates) => {
            let closest = candidates.keys().min().unwrap();
            match candidates[closest].as_slice() {
                [cand] => Ok(*cand),
                [] => unreachable!(),
                [..] => {
                    return resolver.error(ResolutionError::UnresolvedLexicalIdentifier {
                        ident: ident.to_owned(),
                        in_scope: start_from,
                        cause_expr,
                    })
                }
            }
        }
        Err(()) => {
            return resolver.error(ResolutionError::UnresolvedLexicalIdentifier {
                ident: ident.to_owned(),
                in_scope: start_from,
                cause_expr,
            })
        }
    }
}

pub trait SomeResolver {
    type Deferred;
    fn record_res(&mut self, id: NodeId, res: Result<Res<NodeId>, ()>) -> Result<Res<NodeId>, ()>;
    fn error(&self, e: ResolutionError) -> Result<Res<NodeId>, ()>;
    fn query(&mut self, query: NameResQuery) -> Result<HashMap<usize, Vec<Res<NodeId>>>, ()>;
}

impl<'ast, 'sg> SomeResolver for Resolver<'ast, 'sg> {
    type Deferred = DeferredRes<'ast>;

    fn record_res(&mut self, id: NodeId, res: Result<Res<NodeId>, ()>) -> Result<Res<NodeId>, ()> {
        let new_res = match res {
            Err(()) => Res::Err,
            Ok(res) => res,
        };

        if let Some(_) = self.resolutions.insert(id, new_res) {
            panic!("resolution recorded twice for `{id:?}`");
        }

        res
    }

    fn error(&self, e: ResolutionError) -> Result<Res<NodeId>, ()> {
        self.errors.borrow_mut().push(e);

        Err(())
    }

    fn query(&mut self, query: NameResQuery) -> Result<HashMap<usize, Vec<Res<NodeId>>>, ()> {
        ScopeGraph::query(&self.scopegraphs, query, resolve_deferred_res)
    }
}

pub fn build_graph_for_crate<'ast>(
    root_mod: &Module<'ast>,
) -> HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>> {
    let mut graphs = HashMap::new();
    let sg = build_graph_for_mod(root_mod, &mut graphs);
    graphs.insert(root_mod.id, sg);

    // println!("{}", graphviz_export(&graphs));

    graphs
}

fn build_graph_for_item<'ast>(
    item: &Item<'ast>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>>,
) {
    let graph = match item {
        Item::Mod(m) => build_graph_for_mod(m, graphs),
        Item::Use(u) => build_graph_for_use(u, parent, graphs),
        Item::TypeDef(ty) => build_graph_for_type_def(ty, parent, graphs),
        Item::TypeAlias(ty) => build_graph_for_type_alias(ty, parent, graphs),
        Item::Fn(f) => build_graph_for_fn(f, parent, graphs),
        Item::Trait(tr) => build_graph_for_trait(tr, parent, graphs),
        Item::Impl(i) => build_graph_for_impl(i, parent, graphs),

        Item::FieldDef(_) => {
            panic!("`build_graph` called on a `Item::FieldDef` instead of a `item::TypeDef`")
        }
        Item::VariantDef(_) => {
            panic!("`build_graph` called on a `Item::VariantDef` instead of `item::TypeDef`")
        }
    };

    graphs.insert(item.id(), graph);
}

fn build_graph_for_mod<'ast>(
    module: &Module<'ast>,
    graphs: &mut HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>>,
) -> ScopeGraph<DeferredRes<'ast>> {
    let mut graph = ScopeGraphBuilder::new(
        module.id,
        match module.name {
            "" => "crate root",
            name => name,
        }
        .to_owned(),
    );

    let mod_id = graph.add_node(
        module
            .items
            .iter()
            .flat_map(|item| {
                item.name().map(|name| {
                    (
                        EdgeKind::Defines,
                        name.to_owned(),
                        if let Item::Use(u) = item {
                            SGDefinition::Deferred(DeferredRes {
                                start: u.id,
                                path: &u.path,
                            })
                        } else {
                            SGDefinition::PreResolved(Res::Def(
                                match item {
                                    Item::Mod(_) => DefKind::Mod,
                                    Item::TypeDef(_) => DefKind::Adt,
                                    Item::TypeAlias(_) => DefKind::TypeAlias,
                                    Item::Fn(_) => DefKind::Func,
                                    Item::Trait(_) => DefKind::Trait,
                                    Item::Impl(_) => DefKind::Impl,
                                    Item::Use(_) => unreachable!(),
                                    Item::VariantDef(_) | Item::FieldDef(_) => unreachable!(),
                                },
                                item.id(),
                            ))
                        },
                    )
                })
            })
            .collect(),
        vec![],
    );

    // root module doesn't have a name
    if module.name != "" {
        make_lexical_only_scope(
            &mut graph,
            mod_id,
            vec![(
                EdgeKind::Defines,
                module.name.to_owned(),
                SGDefinition::PreResolved(Res::Def(DefKind::Mod, module.id)),
            )],
            vec![],
        );
    }

    for item in module.items {
        build_graph_for_item(item, module.id, graphs);
    }

    graph.build(vec![], HashMap::new())
}

fn build_graph_for_use<'ast>(
    use_def: &ast::Use<'ast>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>>,
) -> ScopeGraph<DeferredRes<'ast>> {
    let mut graph = ScopeGraphBuilder::new(use_def.id, "use_".to_owned() + use_def.name);

    graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );

    graph.build(vec![], HashMap::new())
}

fn build_graph_for_type_def<'ast>(
    type_def: &TypeDef<'ast>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>>,
) -> ScopeGraph<DeferredRes<'ast>> {
    let mut graph = ScopeGraphBuilder::new(type_def.id, type_def.name.to_owned());

    let adt_node = graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );

    introduce_generic_parameters(&mut graph, adt_node, type_def.generics);
    let bounds_subgraph = introduce_bounds(&mut graph, adt_node, &type_def.bounds);

    fn build_graph_for_variant<'ast>(
        graph: &mut ScopeGraphBuilder<DeferredRes<'ast>>,
        graph_id: NodeId,
        variant: &ast::VariantDef<'ast>,
        graphs: &mut HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>>,
    ) {
        for field in variant.field_defs {
            graph.get_node_mut(SGNodeId::ROOT).defines.push((
                EdgeKind::Field,
                field.name.to_owned(),
                SGDefinition::PreResolved(Res::Def(DefKind::Field, field.id)),
            ))
        }

        for type_def in variant.type_defs {
            let nested_graph = build_graph_for_type_def(type_def, graph_id, graphs);
            graphs.insert(type_def.id, nested_graph);

            graph.get_node_mut(SGNodeId::ROOT).defines.push((
                EdgeKind::Defines,
                type_def.name.to_owned(),
                SGDefinition::PreResolved(Res::Def(DefKind::Adt, type_def.id)),
            ))
        }
    }

    match type_def.is_struct() {
        true => build_graph_for_variant(&mut graph, type_def.id, type_def.variants[0], graphs),
        false => {
            for variant in type_def.variants.iter() {
                graph.get_node_mut(SGNodeId::ROOT).defines.push((
                    EdgeKind::Defines,
                    variant.name.unwrap().to_owned(),
                    SGDefinition::PreResolved(Res::Def(DefKind::Variant, variant.id)),
                ));
                let mut variant_graph =
                    ScopeGraphBuilder::new(variant.id, variant.name.unwrap().to_owned());
                variant_graph.add_node(
                    vec![],
                    vec![(EdgeKind::Lexical, EdgeTarget::Global(type_def.id))],
                );
                build_graph_for_variant(&mut variant_graph, variant.id, variant, graphs);
                graphs.insert(variant.id, variant_graph.build(vec![], HashMap::new()));
            }
        }
    };

    graph.build(vec![], bounds_subgraph)
}

fn build_graph_for_type_alias<'ast>(
    type_alias: &TypeAlias<'ast>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>>,
) -> ScopeGraph<DeferredRes<'ast>> {
    let mut graph = ScopeGraphBuilder::new(type_alias.id, type_alias.name.to_owned());

    let ty_node_id = graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );

    introduce_generic_parameters(&mut graph, ty_node_id, type_alias.generics);
    let bounds_subgraph = introduce_bounds(&mut graph, ty_node_id, &type_alias.bounds);

    graph.build(vec![], bounds_subgraph)
}

fn build_graph_for_fn<'ast>(
    func: &ast::Fn<'ast>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>>,
) -> ScopeGraph<DeferredRes<'ast>> {
    let mut graph = ScopeGraphBuilder::new(func.id, func.name.to_owned());

    let fn_id = graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );

    let generics_and_params = func
        .generics
        .params
        .iter()
        .map(|param| {
            (
                EdgeKind::Defines,
                param.name.to_owned(),
                SGDefinition::PreResolved(Res::Def(DefKind::GenericParam, param.id)),
            )
        })
        .chain(func.params.iter().map(|param| {
            (
                EdgeKind::Defines,
                param.ident.to_owned(),
                SGDefinition::PreResolved(Res::Local(param.id)),
            )
        }))
        .collect::<Vec<_>>();

    if generics_and_params.len() > 0 {
        make_lexical_only_scope(&mut graph, fn_id, generics_and_params, vec![]);
    }
    let bounds_subgraph = introduce_bounds(&mut graph, fn_id, &func.bounds);

    let source_to_sg_node = func
        .body
        .map(|expr| scope_for_expr(&mut graph, expr, func.id, fn_id))
        .unwrap_or(vec![]);

    graph.build(source_to_sg_node, bounds_subgraph)
}

fn build_graph_for_trait<'ast>(
    trait_def: &Trait<'ast>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>>,
) -> ScopeGraph<DeferredRes<'ast>> {
    let mut graph = ScopeGraphBuilder::new(trait_def.id, trait_def.ident.to_owned());

    let trait_node = graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );

    introduce_generic_parameters(&mut graph, trait_node, trait_def.generics);
    let bounds_subgraph = introduce_bounds(&mut graph, trait_node, &trait_def.bounds);

    for assoc_item in trait_def.assoc_items {
        match assoc_item {
            ast::AssocItem::Fn(func) => {
                let func_graph = build_graph_for_fn(func, trait_def.id, graphs);
                graphs.insert(func.id, func_graph);

                graph.get_node_mut(trait_node).defines.push((
                    EdgeKind::Defines,
                    func.name.to_owned(),
                    SGDefinition::PreResolved(Res::Def(DefKind::Func, func.id)),
                ));
            }
            ast::AssocItem::Type(alias) => {
                let alias_graph = build_graph_for_type_alias(alias, trait_def.id, graphs);
                graphs.insert(alias.id, alias_graph);

                graph.get_node_mut(trait_node).defines.push((
                    EdgeKind::Defines,
                    alias.name.to_owned(),
                    SGDefinition::PreResolved(Res::Def(DefKind::TypeAlias, alias.id)),
                ));
            }
        }
    }

    graph.build(vec![], bounds_subgraph)
}

fn build_graph_for_impl<'ast>(
    impl_def: &Impl<'ast>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<DeferredRes<'ast>>>,
) -> ScopeGraph<DeferredRes<'ast>> {
    let mut graph = ScopeGraphBuilder::new(impl_def.id, "impl".to_owned());

    let impl_node = graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );

    introduce_generic_parameters(&mut graph, impl_node, impl_def.generics);
    let bounds_subgraph = introduce_bounds(&mut graph, impl_node, &impl_def.bounds);

    for assoc_item in impl_def.assoc_items {
        match assoc_item {
            ast::AssocItem::Fn(func) => {
                let func_graph = build_graph_for_fn(func, impl_def.id, graphs);
                graphs.insert(func.id, func_graph);

                graph.get_node_mut(impl_node).defines.push((
                    EdgeKind::Defines,
                    func.name.to_owned(),
                    SGDefinition::PreResolved(Res::Def(DefKind::Func, func.id)),
                ));
            }
            ast::AssocItem::Type(alias) => {
                let alias_graph = build_graph_for_type_alias(alias, impl_def.id, graphs);
                graphs.insert(alias.id, alias_graph);

                graph.get_node_mut(impl_node).defines.push((
                    EdgeKind::Defines,
                    alias.name.to_owned(),
                    SGDefinition::PreResolved(Res::Def(DefKind::TypeAlias, alias.id)),
                ));
            }
        }
    }

    graph.build(vec![], bounds_subgraph)
}

fn make_lexical_only_scope<'ast>(
    builder: &mut ScopeGraphBuilder<DeferredRes<'ast>>,
    for_node: SGNodeId,
    defines: Vec<(EdgeKind, String, SGDefinition<DeferredRes<'ast>>)>,
    edges: Vec<(EdgeKind, EdgeTarget)>,
) -> SGNodeId {
    let lexical_self_id = builder.add_node(defines, edges);
    builder
        .get_node_mut(for_node)
        .edges
        .push((EdgeKind::Lexical, EdgeTarget::Intragraph(lexical_self_id)));
    lexical_self_id
}

/// Introduces a lexial only scope defining all the generics in `generics`.
/// Returns the `SGNodeId` that the parameters are defined on.
///
/// Does not create a scope if there are no generics introduced.
fn introduce_generic_parameters<'ast>(
    builder: &mut ScopeGraphBuilder<DeferredRes<'ast>>,
    for_node: SGNodeId,
    generics: ast::Generics,
) -> Option<SGNodeId> {
    if generics.params.len() == 0 {
        return None;
    }

    Some(make_lexical_only_scope(
        builder,
        for_node,
        generics
            .params
            .iter()
            .map(|param| {
                (
                    EdgeKind::Defines,
                    param.name.to_owned(),
                    SGDefinition::PreResolved(Res::Def(DefKind::GenericParam, param.id)),
                )
            })
            .collect(),
        vec![],
    ))
}

fn introduce_bounds<'ast>(
    builder: &mut ScopeGraphBuilder<DeferredRes<'ast>>,
    on_node: SGNodeId,
    bounds: &ast::Bounds<'ast>,
) -> HashMap<NodeId, SGNodeId> {
    let mut map = HashMap::new();

    for clause in bounds.clauses {
        if let ast::ClauseKind::Bound(binder) = clause.kind {
            let sg_node = builder.add_node(
                binder
                    .vars
                    .iter()
                    .map(|param| {
                        (
                            EdgeKind::Defines,
                            param.name.to_owned(),
                            SGDefinition::PreResolved(Res::Def(DefKind::GenericParam, param.id)),
                        )
                    })
                    .collect(),
                vec![(EdgeKind::Lexical, EdgeTarget::Intragraph(on_node))],
            );
            map.insert(clause.id, sg_node);
        };
    }

    map
}

fn scope_for_expr<'ast>(
    graph: &mut ScopeGraphBuilder<DeferredRes<'ast>>,
    expr: &ast::Expr<'ast>,
    root_sg_id: NodeId,
    root_sg_node: SGNodeId,
) -> Vec<(NodeId, SGNodeId)> {
    let mut scope_swaps = vec![(root_sg_id, root_sg_node)];
    scope_for_expr_recur(graph, expr, &mut scope_swaps);
    scope_swaps
}

/// Optionally returns whether any following expressions should be parented
/// under a new scope. Used for `let` statements which require all following
/// expressions to be able to name their bindings.
fn scope_for_expr_recur<'ast>(
    graph: &mut ScopeGraphBuilder<DeferredRes<'ast>>,
    expr: &ast::Expr<'ast>,
    scope_swaps: &mut Vec<(NodeId, SGNodeId)>,
) -> Option<SGNodeId> {
    fn reset_scope_to(
        scope_swaps: &mut Vec<(NodeId, SGNodeId)>,
        scope: SGNodeId,
        for_expr: NodeId,
    ) {
        if scope_swaps.last().unwrap().1 != scope {
            scope_swaps.push((for_expr, scope));
        }
    }

    let parent_scope = scope_swaps.last().unwrap().1;

    match expr.kind {
        ast::ExprKind::Let(binding, rhs, _) => {
            // ignore returned scope, rhs of let statement ends after evaluating it
            scope_for_expr_recur(graph, rhs, scope_swaps);
            reset_scope_to(scope_swaps, parent_scope, rhs.id);

            let new_scope = graph.add_node(
                vec![(
                    EdgeKind::Defines,
                    binding.ident.to_owned(),
                    SGDefinition::PreResolved(Res::Local(binding.id)),
                )],
                vec![(EdgeKind::Lexical, EdgeTarget::Intragraph(parent_scope))],
            );
            reset_scope_to(scope_swaps, new_scope, expr.id);

            Some(new_scope)
        }
        ast::ExprKind::Block(exprs, _) => {
            let mut scope = parent_scope;
            for expr in exprs {
                // we dont reset the scope of statements as any bindings should still be accessible
                // until the end of the block
                let new_scope = scope_for_expr_recur(graph, expr.0, scope_swaps);
                if let Some(new_scope) = new_scope {
                    scope = new_scope;
                }

                reset_scope_to(scope_swaps, scope, expr.0.id);
            }

            // At the end of a block any introduced bindings are unnameable
            reset_scope_to(scope_swaps, parent_scope, expr.id);
            None
        }
        ast::ExprKind::BinOp(_, lhs, rhs, _) => {
            scope_for_expr_recur(graph, lhs, scope_swaps);
            reset_scope_to(scope_swaps, parent_scope, lhs.id);
            scope_for_expr_recur(graph, rhs, scope_swaps);
            reset_scope_to(scope_swaps, parent_scope, rhs.id);
            None
        }
        ast::ExprKind::UnOp(_, expr, _) => {
            scope_for_expr_recur(graph, expr, scope_swaps);
            reset_scope_to(scope_swaps, parent_scope, expr.id);
            None
        }
        ast::ExprKind::FnCall(call) => {
            scope_for_expr_recur(graph, call.func, scope_swaps);
            reset_scope_to(scope_swaps, parent_scope, call.func.id);

            for arg in call.args {
                scope_for_expr_recur(graph, arg, scope_swaps);
                reset_scope_to(scope_swaps, parent_scope, arg.id);
            }
            None
        }
        ast::ExprKind::TypeInit(ty_init) => {
            for field_init in ty_init.field_inits {
                scope_for_expr_recur(graph, field_init.expr, scope_swaps);
                reset_scope_to(scope_swaps, parent_scope, field_init.expr.id);
            }
            None
        }
        ast::ExprKind::FieldInit(_) => {
            unreachable!("`FieldInit` is handled in the `TypeInit` arm")
        }

        // path and lit exprs do not introduce bindings
        ast::ExprKind::Path(_) | ast::ExprKind::Lit(_, _) => None,
    }
}
