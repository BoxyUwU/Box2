#[derive(Debug)]
pub struct Nodes(pub Vec<Node>);

impl Nodes {
    pub fn push_expr(&mut self, kind: ExprKind) -> NodeId {
        let id = NodeId(self.0.len());
        self.0.push(Node {
            id,
            kind: NodeKind::Expr(Expr { id, kind }),
        });
        id
    }

    pub fn push_fn(&mut self, func: Fn) -> NodeId {
        let id = NodeId(self.0.len());
        self.0.push(Node {
            id,
            kind: NodeKind::Fn(func),
        });
        id
    }
}

impl std::fmt::Display for Nodes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0.last() {
            Some(_) => {
                fn print_node(
                    f: &mut std::fmt::Formatter<'_>,
                    nodes: &Nodes,
                    node: NodeId,
                ) -> std::fmt::Result {
                    let node = &(&nodes.0[node.0]).kind;
                    if let NodeKind::Expr(Expr { kind, .. }) = node {
                        let kind = kind.clone();
                        let op_str = &kind.op_string();

                        match kind {
                            ExprKind::Bottom(_) => {
                                f.write_str(op_str)?;
                            }
                            ExprKind::BinOp(_, lhs, rhs) => {
                                f.write_str("(")?;
                                f.write_str(op_str)?;
                                f.write_str(" ")?;
                                print_node(f, nodes, lhs)?;
                                f.write_str(" ")?;
                                print_node(f, nodes, rhs)?;
                                f.write_str(")")?;
                            }
                            ExprKind::UnOp(_, lhs) => {
                                f.write_str("(")?;
                                f.write_str(op_str)?;
                                f.write_str(" ")?;
                                print_node(f, nodes, lhs)?;
                                f.write_str(")")?;
                            }
                        }
                    }

                    if let NodeKind::Fn(func) = node {
                        if let Some(visibility) = &func.visibility {
                            match visibility {
                                Visibility::Pub => {
                                    f.write_str("pub ")?;
                                }
                            }
                        };
                        f.write_str("fn ")?;
                        f.write_str(&func.name)?;
                        f.write_str("(")?;
                        for (param, ty) in &func.params {
                            f.write_str(&param)?;
                            f.write_str(": ")?;
                            f.write_str(&ty)?;
                            f.write_str(",")?;
                        }
                        f.write_str(")")?;

                        if let Some(ret_ty) = &func.ret_ty {
                            f.write_str(" -> ")?;
                            f.write_str(&ret_ty)?;
                        }

                        f.write_str(" {\n    ")?;
                        print_node(f, nodes, func.body)?;
                        f.write_str("\n}")?;
                    }

                    Ok(())
                }
                print_node(f, self, NodeId(self.0.len() - 1))
            }
            None => Ok(()),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct NodeId(pub usize);

#[derive(Debug)]
pub struct Node {
    id: NodeId,
    kind: NodeKind,
}

#[derive(Debug)]
pub enum NodeKind {
    Expr(Expr),
    Fn(Fn),
}

#[derive(Debug)]
pub enum Visibility {
    Pub,
}

#[derive(Debug)]
pub struct Fn {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub params: Vec<(String, String)>,
    pub ret_ty: Option<String>,
    pub body: NodeId,
}

#[derive(Debug)]
pub struct Expr {
    pub id: NodeId,
    pub kind: ExprKind,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    BinOp(BinOp, NodeId, NodeId),
    UnOp(UnOp, NodeId),
    Bottom(Bottom),
}

impl ExprKind {
    pub fn op_string(&self) -> String {
        match self {
            ExprKind::BinOp(op, _, _) => match op {
                BinOp::Add => "+".into(),
                BinOp::Sub => "-".into(),
                BinOp::Div => "/".into(),
                BinOp::Mul => "*".into(),
            },
            ExprKind::UnOp(op, _) => match op {
                UnOp::Neg => "-".into(),
            },
            ExprKind::Bottom(bottom) => match bottom {
                Bottom::Float(f) => f.to_string(),
                Bottom::Int(i) => i.to_string(),
                Bottom::Ident(ident) => ident.to_string(),
            },
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum UnOp {
    Neg,
}

#[derive(Clone, PartialEq, Debug)]
pub enum Bottom {
    Int(u64),
    Float(f64),
    Ident(String),
}
