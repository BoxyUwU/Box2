use std::{cell::RefCell, collections::HashMap, vec};

use crate::{
    ast::{
        self, Impl, Item, Module, Node, NodeId, Nodes, Term, TermKind, Trait, TypeAlias, TypeDef,
    },
    scopegraph::*,
};

#[derive(Copy, Clone, Hash, Debug, Eq, PartialEq)]
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
#[derive(Copy, Clone, Hash, Debug, Eq, PartialEq)]
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
            Node::Term(Term {
                id: _,
                kind: TermKind::Let { .. },
            }) => Res::Local(id),
            Node::GenericParam(param) => Res::Def(DefKind::GenericParam, param.id),
            Node::Clause(_) | Node::PathSeg(_) | Node::Term(_) => unreachable!(),
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
        in_scope: GlobalSGodeId,
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
pub enum NameResQuery<'ast> {
    Path(PathResQuery<'ast>),
    Field(FieldInitResQuery<'ast>),
}

#[derive(Copy, Clone)]
pub struct PathResQuery<'ast> {
    path_id: NodeId,
    path: ast::Path<'ast>,
    in_sg: GlobalSGodeId,
}

#[derive(Copy, Clone)]
pub struct FieldInitResQuery<'ast> {
    path_id: NodeId,
    path: ast::Path<'ast>,

    field_ident_id: NodeId,
    field_ident: &'ast str,

    in_sig: GlobalSGodeId,
}

pub trait SomeResolver<D> {
    type Deferred;
    fn record_res(&mut self, id: NodeId, res: Result<Res<NodeId>, ()>) -> Result<Res<NodeId>, ()>;
    fn error(&self, e: ResolutionError) -> Result<Res<NodeId>, ()>;
    fn query(&mut self, query: SGQuery) -> Result<HashMap<usize, Vec<Res<NodeId>>>, ()>;
}

impl<'ast, 'sg> SomeResolver<PathResQuery<'ast>> for Resolver<'ast, 'sg> {
    type Deferred = PathResQuery<'ast>;

    fn record_res(&mut self, id: NodeId, res: Result<Res<NodeId>, ()>) -> Result<Res<NodeId>, ()> {
        let new_res = match res {
            Err(()) => Res::Err,
            Ok(res) => res,
        };

        if let Some(old_res) = self.resolutions.insert(id, new_res) {
            assert_eq!(
                old_res, new_res,
                "differing resolutions recorded for `{id:?}`: {old_res:?} and {new_res:?}"
            );
        }

        res
    }

    fn error(&self, e: ResolutionError) -> Result<Res<NodeId>, ()> {
        self.errors.borrow_mut().push(e);

        Err(())
    }

    fn query(&mut self, query: SGQuery) -> Result<HashMap<usize, Vec<Res<NodeId>>>, ()> {
        ScopeGraph::query(&self.scopegraphs, query, |resolver, d| {
            resolve_path_res(resolver, d).unwrap_or(Res::Err)
        })
    }
}

pub struct Resolver<'ast, 'sg> {
    errors: RefCell<Vec<ResolutionError>>,
    resolutions: HashMap<NodeId, Res<NodeId>>,
    scopegraphs: &'sg HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>,
}

impl<'ast, 'sg> Resolver<'ast, 'sg> {
    pub fn new(scopegraphs: &'sg HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>) -> Self {
        Self {
            errors: RefCell::default(),
            resolutions: HashMap::new(),
            scopegraphs,
        }
    }

    pub fn into_outputs(self) -> (Vec<ResolutionError>, HashMap<NodeId, Res<NodeId>>) {
        (self.errors.into_inner(), self.resolutions)
    }

    fn error(&self, e: ResolutionError) -> Result<Res<NodeId>, ()> {
        self.errors.borrow_mut().push(e);

        Err(())
    }

    pub fn resolve_name_res_query(&mut self, q: NameResQuery<'ast>) -> Result<(), ()> {
        match q {
            NameResQuery::Path(path_res_query) => resolve_path_res(self, path_res_query).map(drop),
            NameResQuery::Field(field_init_res_query) => {
                resolve_field_res(self, field_init_res_query).map(drop)
            }
        }
    }
}

fn resolve_field_res<'ast, R: SomeResolver<PathResQuery<'ast>>>(
    resolver: &mut R,
    field_res_query: FieldInitResQuery<'ast>,
) -> Result<Res<NodeId>, ()> {
    let res = resolve_path_res(
        resolver,
        PathResQuery {
            path_id: field_res_query.path_id,
            path: field_res_query.path,
            in_sg: field_res_query.in_sig,
        },
    )?;

    let id = match res {
        Res::Def(DefKind::Adt | DefKind::Variant, id) => id,
        Res::Def(_, _) | Res::Local(_) | Res::Err => return Err(()),
    };

    let ident_res = resolve_ident_as_field(
        resolver,
        field_res_query.field_ident,
        GlobalSGodeId(id, SGNodeId::ROOT),
        field_res_query.field_ident_id,
    );
    resolver.record_res(field_res_query.field_ident_id, ident_res)
}

fn resolve_path_res<'ast, R: SomeResolver<PathResQuery<'ast>>>(
    resolver: &mut R,
    path_res_query: PathResQuery<'ast>,
) -> Result<Res<NodeId>, ()> {
    let PathResQuery {
        path_id,
        path,
        in_sg,
    } = path_res_query;

    let mut seg_iter = path.segments.iter();

    let result = (|| -> Result<Res<NodeId>, ()> {
        let first_seg = seg_iter.next().unwrap();
        let prev_seg_res = resolve_ident_lexically(resolver, first_seg.ident, in_sg, first_seg.id);
        let mut prev_seg_res = resolver.record_res(first_seg.id, prev_seg_res)?;

        for cur_seg in &mut seg_iter {
            let inner_start_from = match prev_seg_res {
                Res::Def(_, id) => id,
                Res::Local(id) => id,
                Res::Err => unreachable!(),
            };

            let cur_seg_res = resolve_ident_in_item(
                resolver,
                cur_seg.ident,
                GlobalSGodeId(inner_start_from, SGNodeId::ROOT),
                cur_seg.id,
            );
            prev_seg_res = resolver.record_res(cur_seg.id, cur_seg_res)?;
        }

        Ok(prev_seg_res)
    })();

    match result {
        Ok(_) => resolver.record_res(path_id, result),
        Err(()) => {
            for seg in seg_iter {
                let _ = resolver.record_res(seg.id, Err(()));
            }
            Err(())
        }
    }
}

fn resolve_ident_in_item<'ast, R: SomeResolver<PathResQuery<'ast>>>(
    resolver: &mut R,
    ident: &str,
    start_from: GlobalSGodeId,
    cause_expr: NodeId,
) -> Result<Res<NodeId>, ()> {
    let query_result = resolver.query(SGQuery {
        name: ident.to_owned(),
        start: start_from,
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
                        in_scope: start_from.0,
                        cause_expr,
                    })
                }
            }
        }
        Err(()) => {
            return resolver.error(ResolutionError::UnresolvedAssociatedIdentifier {
                ident: ident.to_owned(),
                in_scope: start_from.0,
                cause_expr,
            })
        }
    }
}

fn resolve_ident_lexically<'ast, R: SomeResolver<PathResQuery<'ast>>>(
    resolver: &mut R,
    ident: &str,
    start_from: GlobalSGodeId,
    cause_expr: NodeId,
) -> Result<Res<NodeId>, ()> {
    let query_result = resolver.query(SGQuery {
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

fn resolve_ident_as_field<'ast, R: SomeResolver<PathResQuery<'ast>>>(
    resolver: &mut R,
    ident: &str,
    start_from: GlobalSGodeId,
    cause_expr: NodeId,
) -> Result<Res<NodeId>, ()> {
    let query_result = resolver.query(SGQuery {
        name: ident.to_owned(),
        start: start_from,
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
                    return resolver.error(ResolutionError::UnresolvedField {
                        ident: ident.to_owned(),
                        on_res: start_from.0,
                        cause_expr,
                    })
                }
            }
        }
        Err(()) => {
            return resolver.error(ResolutionError::UnresolvedField {
                ident: ident.to_owned(),
                on_res: start_from.0,
                cause_expr,
            })
        }
    }
}

pub fn build_graph_for_crate<'ast>(
    root_mod: &'ast Module<'ast>,
) -> (
    HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>,
    Vec<NameResQuery<'ast>>,
) {
    let mut graphs = HashMap::new();
    let mut name_res_queries = vec![];
    build_graph_for_mod(root_mod, &mut name_res_queries, &mut graphs);
    // println!("{}", graphviz_export(&graphs));

    (graphs, name_res_queries)
}

fn build_graph_for_item<'ast>(
    item: &'ast Item<'ast>,
    name_res_queries: &mut Vec<NameResQuery<'ast>>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>,
) {
    match item {
        Item::Mod(m) => build_graph_for_mod(m, name_res_queries, graphs),
        Item::Use(u) => build_graph_for_use(u, name_res_queries, parent, graphs),
        Item::TypeDef(ty) => build_graph_for_type_def(ty, name_res_queries, parent, graphs),
        Item::TypeAlias(ty) => build_graph_for_type_alias(ty, name_res_queries, parent, graphs),
        Item::Fn(f) => build_graph_for_fn(f, name_res_queries, parent, graphs),
        Item::Trait(tr) => build_graph_for_trait(tr, name_res_queries, parent, graphs),
        Item::Impl(i) => build_graph_for_impl(i, name_res_queries, parent, graphs),

        Item::FieldDef(_) => {
            panic!("`build_graph` called on a `Item::FieldDef` instead of a `item::TypeDef`")
        }
        Item::VariantDef(_) => {
            panic!("`build_graph` called on a `Item::VariantDef` instead of `item::TypeDef`")
        }
    }
}

fn build_graph_for_mod<'ast>(
    module: &'ast Module<'ast>,
    name_res_queries: &mut Vec<NameResQuery<'ast>>,
    graphs: &mut HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>,
) {
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
                            SGDefinition::Deferred(PathResQuery {
                                in_sg: GlobalSGodeId(u.id, SGNodeId::ROOT),
                                path: u.path,
                                path_id: u.id,
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
            GlobalSGodeId(module.id, mod_id),
            vec![(
                EdgeKind::Defines,
                module.name.to_owned(),
                SGDefinition::PreResolved(Res::Def(DefKind::Mod, module.id)),
            )],
            vec![],
        );
    }

    for item in module.items {
        build_graph_for_item(item, name_res_queries, module.id, graphs);
    }

    let sg = graph.build();
    graphs.insert(module.id, sg);
}

fn build_graph_for_use<'ast>(
    use_def: &'ast ast::Use<'ast>,
    _name_res_queries: &mut Vec<NameResQuery<'ast>>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>,
) {
    let mut graph = ScopeGraphBuilder::new(use_def.id, "use_".to_owned() + use_def.name);

    graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );

    let sg = graph.build();
    graphs.insert(use_def.id, sg);
}

fn build_graph_for_type_def<'ast>(
    type_def: &'ast TypeDef<'ast>,
    name_res_queries: &mut Vec<NameResQuery<'ast>>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>,
) {
    let mut graph = ScopeGraphBuilder::new(type_def.id, type_def.name.to_owned());

    let adt_node = graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );
    let adt_global_node = GlobalSGodeId(type_def.id, adt_node);

    scope_for_generics(
        &mut graph,
        &type_def.generics,
        adt_global_node,
        name_res_queries,
    );
    scope_for_bounds(
        &mut graph,
        &type_def.bounds,
        adt_global_node,
        name_res_queries,
    );

    fn build_graph_for_variant<'ast>(
        graph: &mut ScopeGraphBuilder<PathResQuery<'ast>>,
        name_res_queries: &mut Vec<NameResQuery<'ast>>,
        graph_id: NodeId,
        variant: &ast::VariantDef<'ast>,
        graphs: &mut HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>,
    ) {
        for field in variant.field_defs {
            graph.get_node_mut(SGNodeId::ROOT).defines.push((
                EdgeKind::Field,
                field.name.to_owned(),
                SGDefinition::PreResolved(Res::Def(DefKind::Field, field.id)),
            ))
        }

        for type_def in variant.type_defs {
            build_graph_for_type_def(type_def, name_res_queries, graph_id, graphs);
            graph.get_node_mut(SGNodeId::ROOT).defines.push((
                EdgeKind::Defines,
                type_def.name.to_owned(),
                SGDefinition::PreResolved(Res::Def(DefKind::Adt, type_def.id)),
            ))
        }
    }

    match type_def.is_struct() {
        true => build_graph_for_variant(
            &mut graph,
            name_res_queries,
            type_def.id,
            type_def.variants[0],
            graphs,
        ),
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
                build_graph_for_variant(
                    &mut variant_graph,
                    name_res_queries,
                    variant.id,
                    variant,
                    graphs,
                );
                graphs.insert(variant.id, variant_graph.build());
            }
        }
    };

    let sg = graph.build();
    graphs.insert(type_def.id, sg);
}

fn build_graph_for_type_alias<'ast>(
    type_alias: &'ast TypeAlias<'ast>,
    name_res_queries: &mut Vec<NameResQuery<'ast>>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>,
) {
    let mut graph = ScopeGraphBuilder::new(type_alias.id, type_alias.name.to_owned());

    let ty_node_id = graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );
    let ty_node_global_id = GlobalSGodeId(type_alias.id, ty_node_id);

    scope_for_generics(
        &mut graph,
        &type_alias.generics,
        ty_node_global_id,
        name_res_queries,
    );
    scope_for_bounds(
        &mut graph,
        &type_alias.bounds,
        ty_node_global_id,
        name_res_queries,
    );

    let sg = graph.build();
    graphs.insert(type_alias.id, sg);
}

fn build_graph_for_fn<'ast>(
    func: &'ast ast::Fn<'ast>,
    name_res_queries: &mut Vec<NameResQuery<'ast>>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>,
) {
    let mut graph = ScopeGraphBuilder::new(func.id, func.name.to_owned());

    let fn_id = graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );
    let fn_global_id = GlobalSGodeId(func.id, fn_id);

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

    make_lexical_only_scope(&mut graph, fn_global_id, generics_and_params, vec![]);
    scope_for_bounds(&mut graph, &func.bounds, fn_global_id, name_res_queries);

    if let Some(term) = func.body {
        scope_for_term(&mut graph, term, name_res_queries, fn_global_id);
    }

    let sg = graph.build();
    graphs.insert(func.id, sg);
}

fn build_graph_for_trait<'ast>(
    trait_def: &'ast Trait<'ast>,
    name_res_queries: &mut Vec<NameResQuery<'ast>>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>,
) {
    let mut graph = ScopeGraphBuilder::new(trait_def.id, trait_def.ident.to_owned());

    let trait_node = graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );
    let trait_global_node = GlobalSGodeId(trait_def.id, trait_node);

    scope_for_generics(
        &mut graph,
        &trait_def.generics,
        trait_global_node,
        name_res_queries,
    );
    scope_for_bounds(
        &mut graph,
        &trait_def.bounds,
        trait_global_node,
        name_res_queries,
    );

    for assoc_item in trait_def.assoc_items {
        match assoc_item {
            ast::AssocItem::Fn(func) => {
                build_graph_for_fn(func, name_res_queries, trait_def.id, graphs);
                graph.get_node_mut(trait_node).defines.push((
                    EdgeKind::Defines,
                    func.name.to_owned(),
                    SGDefinition::PreResolved(Res::Def(DefKind::Func, func.id)),
                ));
            }
            ast::AssocItem::Type(alias) => {
                build_graph_for_type_alias(alias, name_res_queries, trait_def.id, graphs);
                graph.get_node_mut(trait_node).defines.push((
                    EdgeKind::Defines,
                    alias.name.to_owned(),
                    SGDefinition::PreResolved(Res::Def(DefKind::TypeAlias, alias.id)),
                ));
            }
        }
    }

    let sg = graph.build();
    graphs.insert(trait_def.id, sg);
}

fn build_graph_for_impl<'ast>(
    impl_def: &'ast Impl<'ast>,
    name_res_queries: &mut Vec<NameResQuery<'ast>>,
    parent: NodeId,
    graphs: &mut HashMap<NodeId, ScopeGraph<PathResQuery<'ast>>>,
) {
    let mut graph = ScopeGraphBuilder::new(impl_def.id, "impl".to_owned());

    let impl_node = graph.add_node(
        vec![],
        vec![(EdgeKind::Lexical, EdgeTarget::Global(parent))],
    );
    let impl_global_node = GlobalSGodeId(impl_def.id, impl_node);

    scope_for_generics(
        &mut graph,
        &impl_def.generics,
        impl_global_node,
        name_res_queries,
    );
    scope_for_bounds(
        &mut graph,
        &impl_def.bounds,
        impl_global_node,
        name_res_queries,
    );

    for assoc_item in impl_def.assoc_items {
        match assoc_item {
            ast::AssocItem::Fn(func) => {
                build_graph_for_fn(func, name_res_queries, impl_def.id, graphs);
                graph.get_node_mut(impl_node).defines.push((
                    EdgeKind::Defines,
                    func.name.to_owned(),
                    SGDefinition::PreResolved(Res::Def(DefKind::Func, func.id)),
                ));
            }
            ast::AssocItem::Type(alias) => {
                build_graph_for_type_alias(alias, name_res_queries, impl_def.id, graphs);
                graph.get_node_mut(impl_node).defines.push((
                    EdgeKind::Defines,
                    alias.name.to_owned(),
                    SGDefinition::PreResolved(Res::Def(DefKind::TypeAlias, alias.id)),
                ));
            }
        }
    }

    let sg = graph.build();
    graphs.insert(impl_def.id, sg);
}

fn make_lexical_only_scope<'ast>(
    builder: &mut ScopeGraphBuilder<PathResQuery<'ast>>,
    current_scope: GlobalSGodeId,
    defines: Vec<(EdgeKind, String, SGDefinition<PathResQuery<'ast>>)>,
    edges: Vec<(EdgeKind, EdgeTarget)>,
) -> SGNodeId {
    let lexical_self_id = builder.add_node(defines, edges);
    builder
        .get_node_mut(current_scope.1)
        .edges
        .push((EdgeKind::Lexical, EdgeTarget::Intragraph(lexical_self_id)));
    lexical_self_id
}

/// Introduces a lexial only scope defining all the generics in `generics`.
/// Returns the `SGNodeId` that the parameters are defined on.
///
/// Does not create a scope if there are no generics introduced.
fn scope_for_generics<'ast>(
    graph: &mut ScopeGraphBuilder<PathResQuery<'ast>>,
    generics: &'ast ast::Generics<'ast>,
    current_scope: GlobalSGodeId,
    _name_res_queries: &mut Vec<NameResQuery<'ast>>,
) {
    make_lexical_only_scope(
        graph,
        current_scope,
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
    );
}

fn scope_for_bounds<'ast>(
    graph: &mut ScopeGraphBuilder<PathResQuery<'ast>>,
    bounds: &ast::Bounds<'ast>,
    current_scope: GlobalSGodeId,
    name_res_queries: &mut Vec<NameResQuery<'ast>>,
) {
    for clause in bounds.clauses {
        scope_for_clause(graph, clause, name_res_queries, current_scope);
    }
}

fn scope_for_clause<'ast>(
    graph: &mut ScopeGraphBuilder<PathResQuery<'ast>>,
    clause: &'ast ast::Clause<'ast>,
    name_res_queries: &mut Vec<NameResQuery<'ast>>,
    current_scope: GlobalSGodeId,
) {
    match &clause.kind {
        ast::ClauseKind::Bound(binder) => {
            let new_scope = graph.add_node(
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
                vec![(EdgeKind::Lexical, EdgeTarget::Intragraph(current_scope.1))],
            );
            scope_for_clause(
                graph,
                binder.value,
                name_res_queries,
                current_scope.map_sg_id(new_scope),
            );
        }
        ast::ClauseKind::AliasEq(lhs, rhs) => {
            scope_for_term(graph, lhs, name_res_queries, current_scope);
            scope_for_term(graph, rhs, name_res_queries, current_scope);
        }
        ast::ClauseKind::Trait(path) => {
            scope_for_path(graph, *path, clause.id, name_res_queries, current_scope);
        }
    }
}

fn scope_for_term<'ast>(
    graph: &mut ScopeGraphBuilder<PathResQuery<'ast>>,
    term: &'ast ast::Term<'ast>,
    name_res_queries: &mut Vec<NameResQuery<'ast>>,
    current_scope: GlobalSGodeId,
) {
    match term.kind {
        ast::TermKind::Let {
            param: binding,
            init,
            cont,
            sp: _,
        } => {
            // ignore returned scope, rhs of let statement ends after evaluating it
            scope_for_term(graph, init, name_res_queries, current_scope);
            let new_scope = graph.add_node(
                vec![(
                    EdgeKind::Defines,
                    binding.ident.to_owned(),
                    SGDefinition::PreResolved(Res::Local(binding.id)),
                )],
                vec![(EdgeKind::Lexical, EdgeTarget::Intragraph(current_scope.1))],
            );
            scope_for_term(
                graph,
                cont,
                name_res_queries,
                current_scope.map_sg_id(new_scope),
            );
        }
        ast::TermKind::BinOp(_, lhs, rhs, _) => {
            scope_for_term(graph, lhs, name_res_queries, current_scope);
            scope_for_term(graph, rhs, name_res_queries, current_scope);
        }
        ast::TermKind::UnOp(_, expr, _) => {
            scope_for_term(graph, expr, name_res_queries, current_scope);
        }
        ast::TermKind::FnCall(call) => {
            scope_for_term(graph, call.func, name_res_queries, current_scope);
            for arg in call.args {
                scope_for_term(graph, arg, name_res_queries, current_scope);
            }
        }
        ast::TermKind::TypeInit(ty_init) => {
            scope_for_path(
                graph,
                ty_init.path,
                term.id,
                name_res_queries,
                current_scope,
            );

            for field_init in ty_init.field_inits {
                scope_for_term(graph, field_init.expr, name_res_queries, current_scope);
            }
        }
        ast::TermKind::FieldInit(_) => {
            unreachable!("`FieldInit` is handled in the `TypeInit` arm")
        }

        ast::TermKind::Path(path) => {
            scope_for_path(graph, path, term.id, name_res_queries, current_scope);
        }

        // infer and lit exprs do not introduce bindings or contain paths
        ast::TermKind::Infer(_) | ast::TermKind::Lit(_, _) => (),
    }
}

fn scope_for_path<'ast>(
    graph: &mut ScopeGraphBuilder<PathResQuery<'ast>>,
    path: ast::Path<'ast>,
    path_id: NodeId,
    name_res_queries: &mut Vec<NameResQuery<'ast>>,
    current_scope: GlobalSGodeId,
) {
    name_res_queries.push(NameResQuery::Path(PathResQuery {
        path_id,
        path,
        in_sg: current_scope,
    }));

    for seg in path.segments {
        seg.args
            .0
            .iter()
            .map(|term| scope_for_term(graph, term, name_res_queries, current_scope));
    }
}
