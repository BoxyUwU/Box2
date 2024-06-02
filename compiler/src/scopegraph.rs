use std::collections::{hash_map::Entry, HashMap, HashSet};

use crate::{ast::NodeId, resolve::Res};

pub struct ScopeGraph<D> {
    id: NodeId,
    name: String,
    nodes: Vec<SGNode<D>>,

    // When walking the ast, upon reaching `NodeId`, after evaluating it,
    // `SGNodeId` should be used for all name res queries.
    source_to_sg_node: Vec<(NodeId, SGNodeId)>,
    // A map of `NodeId` -> `SGNodeId` where `NodeId` is a `ClauseKind::Bound`'s id.
    bound_clause_to_sg_node: HashMap<NodeId, SGNodeId>,
}
impl<D> ScopeGraph<D> {
    pub fn source_to_sg_node(&self) -> &[(NodeId, SGNodeId)] {
        &self.source_to_sg_node
    }

    pub fn bound_clause_to_sg_node(&self, clause: NodeId) -> SGNodeId {
        self.bound_clause_to_sg_node[&clause]
    }
}
impl<D: Clone> ScopeGraph<D> {
    pub fn query<'sg>(
        forest: &'sg HashMap<NodeId, ScopeGraph<D>>,
        query: NameResQuery,
        resolve_deferred: fn(&mut NameResQueryEvaluator<'sg, D>, D) -> Res<NodeId>,
    ) -> Result<HashMap<usize, Vec<Res<NodeId>>>, ()> {
        let mut evaluator = NameResQueryEvaluator {
            query_stack: vec![],
            scopegraphs: forest,
            resolve_deferred,
        };

        evaluator.nested_query(query)
    }
}

#[derive(Debug, Hash, Copy, Clone, Eq, PartialEq)]
pub struct SGNodeId(usize);
impl SGNodeId {
    pub const ROOT: SGNodeId = SGNodeId(0);
}

pub struct SGNode<D> {
    defines: Vec<(EdgeKind, String, SGDefinition<D>)>,
    edges: Vec<(EdgeKind, EdgeTarget)>,
}

pub enum SGDefinition<D> {
    Deferred(D),
    PreResolved(Res<NodeId>),
}

pub enum EdgeTarget {
    Intragraph(SGNodeId),
    Global(NodeId),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum EdgeKind {
    Defines,
    Lexical,
    Field,
}

#[derive(Clone, Eq, PartialEq)]
pub struct NameResQuery {
    pub name: String,
    pub start: (NodeId, SGNodeId),
    pub edge_filter: Vec<EdgeKind>,
}

pub struct NameResQueryEvaluator<'sg, D> {
    query_stack: Vec<NameResQuery>,
    scopegraphs: &'sg HashMap<NodeId, ScopeGraph<D>>,
    resolve_deferred: fn(&mut NameResQueryEvaluator<'sg, D>, D) -> Res<NodeId>,
}

impl<'sg, D: Clone> crate::resolve::SomeResolver for NameResQueryEvaluator<'sg, D> {
    type Deferred = D;

    fn record_res(&mut self, _id: NodeId, res: Result<Res<NodeId>, ()>) -> Result<Res<NodeId>, ()> {
        res
    }

    fn error(&self, _e: crate::resolve::ResolutionError) -> Result<Res<NodeId>, ()> {
        Err(())
    }

    fn query(&mut self, query: NameResQuery) -> Result<HashMap<usize, Vec<Res<NodeId>>>, ()> {
        self.nested_query(query)
    }
}
impl<D: Clone> NameResQueryEvaluator<'_, D> {
    pub fn nested_query(
        &mut self,
        query: NameResQuery,
    ) -> Result<HashMap<usize, Vec<Res<NodeId>>>, ()> {
        if let Some(_) = self
            .query_stack
            .iter()
            .rev()
            .find(|&parent_query| parent_query == &query)
        {
            // the current query is already being evaluated, do not infinitely recurse
            return Err(());
        }
        self.query_stack.push(query.clone());
        let r = self.compute_query(query.name, query.start, query.edge_filter);
        self.query_stack.pop().unwrap();
        r
    }

    fn compute_query(
        &mut self,
        for_name: String,
        start: (NodeId, SGNodeId),
        edge_filter: Vec<EdgeKind>,
    ) -> Result<HashMap<usize, Vec<Res<NodeId>>>, ()> {
        let mut visited_nodes = HashSet::new();
        let mut work_list = vec![(start, 0_usize)];
        let mut candidates = HashMap::<usize, Vec<Res<NodeId>>>::new();

        while let Some(((graph_id, node_id), cur_depth)) = work_list.pop() {
            if visited_nodes.contains(&(graph_id, node_id)) {
                continue;
            }

            let node = &self.scopegraphs[&graph_id].nodes[node_id.0];
            visited_nodes.insert((graph_id, node_id));
            work_list.extend(node.edges.iter().flat_map(|(test_edge, target)| {
                edge_filter
                    .iter()
                    .any(|edge| test_edge == edge)
                    .then(|| match target {
                        EdgeTarget::Intragraph(node_id) => ((graph_id, *node_id), cur_depth + 1),
                        EdgeTarget::Global(graph_id) => {
                            ((*graph_id, SGNodeId::ROOT), cur_depth + 1)
                        }
                    })
            }));

            let node_candidates = node
                .defines
                .iter()
                .flat_map(|(test_edge, test_name, res)| {
                    (edge_filter.iter().any(|edge| test_edge == edge) && *test_name == for_name)
                        .then_some(res)
                })
                .map(|cand| match cand {
                    SGDefinition::Deferred(d) => (self.resolve_deferred)(self, d.clone()),
                    SGDefinition::PreResolved(res) => *res,
                })
                .filter(|res| *res != Res::Err);

            match candidates.entry(cur_depth) {
                Entry::Occupied(mut candidates) => candidates.get_mut().extend(node_candidates),
                Entry::Vacant(candidates) => {
                    let node_candidates = node_candidates.collect::<Vec<_>>();
                    if node_candidates.len() > 0 {
                        candidates.insert(node_candidates);
                    }
                }
            }
        }

        if candidates.is_empty() {
            return Err(());
        } else {
            Ok(candidates)
        }
    }
}

pub struct ScopeGraphBuilder<D> {
    name: String,
    id: NodeId,
    wip_nodes: Vec<WIPSGNode<D>>,
}

pub struct WIPSGNode<D> {
    pub defines: Vec<(EdgeKind, String, SGDefinition<D>)>,
    pub edges: Vec<(EdgeKind, EdgeTarget)>,
}

impl<D> ScopeGraphBuilder<D> {
    pub fn new(id: NodeId, name: String) -> Self {
        Self {
            name,
            id,
            wip_nodes: vec![],
        }
    }

    pub fn add_node(
        &mut self,
        defines: Vec<(EdgeKind, String, SGDefinition<D>)>,
        edges: Vec<(EdgeKind, EdgeTarget)>,
    ) -> SGNodeId {
        let nodes_len = self.wip_nodes.len();
        self.wip_nodes.push(WIPSGNode { defines, edges });
        SGNodeId(nodes_len)
    }

    pub fn get_node_mut(&mut self, id: SGNodeId) -> &mut WIPSGNode<D> {
        self.wip_nodes.get_mut(id.0).unwrap()
    }

    pub fn build(
        self,
        source_to_sg_node: Vec<(NodeId, SGNodeId)>,
        bound_clause_to_sg_node: HashMap<NodeId, SGNodeId>,
    ) -> ScopeGraph<D> {
        ScopeGraph {
            name: self.name,
            id: self.id,
            nodes: self
                .wip_nodes
                .into_iter()
                .map(|wip_sgnode| SGNode {
                    defines: wip_sgnode.defines,
                    edges: wip_sgnode.edges,
                })
                .collect(),
            source_to_sg_node,
            bound_clause_to_sg_node,
        }
    }
}

pub fn graphviz_export<D>(sg: &HashMap<NodeId, ScopeGraph<D>>) -> String {
    let mut graph = "digraph G {\n".to_owned();

    let mut edges = String::new();

    for (id, sg) in sg.into_iter() {
        let mut subgraph = format!("    subgraph cluster{} {{\n", id.0);
        subgraph.push_str("        node [style=\"filled\"];\n");
        subgraph.push_str(&format!("        label=\"{}\";\n", sg.name));

        for (node_id, node) in sg.nodes.iter().enumerate() {
            subgraph.push_str(&format!(
                "        _{}_{} [shape=circle,label=\"\"]\n",
                id.0, node_id
            ));

            for (kind, name, _) in node.defines.iter() {
                let edge_label = match kind {
                    EdgeKind::Defines => "def",
                    EdgeKind::Lexical => "lexical",
                    EdgeKind::Field => "field",
                };

                subgraph.push_str(&format!(
                    "        _{}_{}_{name} [shape=box,label=\"{name}\"]\n",
                    id.0, node_id
                ));
                edges.push_str(&format!(
                    "    _{}_{node_id} -> _{}_{node_id}_{name} [label=\" {edge_label}\"];\n",
                    id.0, id.0
                ))
            }

            for (kind, target) in node.edges.iter() {
                let edge_label = match kind {
                    EdgeKind::Defines => "def",
                    EdgeKind::Lexical => "lexical",
                    EdgeKind::Field => "field",
                };

                match target {
                    EdgeTarget::Intragraph(other_node_id) => edges.push_str(&format!(
                        "    _{}_{node_id} -> _{}_{} [label=\" {edge_label}\"];\n",
                        id.0, id.0, other_node_id.0,
                    )),
                    EdgeTarget::Global(other_sg_id) => edges.push_str(&format!(
                        "    _{}_{node_id} -> _{}_0 [label=\" {edge_label}\"];\n",
                        id.0, other_sg_id.0,
                    )),
                }
            }
        }

        subgraph.push_str("    }\n");
        graph.push_str(&subgraph);
    }

    graph.push_str(&edges);

    graph.push_str("}");
    graph
}
