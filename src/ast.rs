use logos::Span;

use crate::tokenize::Literal;

#[derive(Debug)]
pub struct Nodes(pub Vec<Node>);

impl Nodes {
    pub fn expr(&self, id: NodeId) -> &Expr {
        unwrap_matches!(&self.0[id.0].kind, NodeKind::Expr(e) => e)
    }

    pub fn type_def(&self, id: NodeId) -> &TypeDef {
        unwrap_matches!(&self.0[id.0].kind, NodeKind::TypeDef(def) => def)
    }

    pub fn variant_def(&self, id: NodeId) -> &VariantDef {
        unwrap_matches!(&self.0[id.0].kind, NodeKind::VariantDef(def) => def)
    }

    pub fn field_def(&self, id: NodeId) -> &FieldDef {
        unwrap_matches!(&self.0[id.0].kind, NodeKind::FieldDef(def) => def)
    }

    pub fn mod_def(&self, id: NodeId) -> &Module {
        unwrap_matches!(&self.0[id.0].kind, NodeKind::Mod(def) => def)
    }

    pub fn path(&self, id: NodeId) -> &Path {
        unwrap_matches!(&self.0[id.0].kind, NodeKind::Path(path) => path)
    }

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

    pub fn push_variant_def(&mut self, def: VariantDef) -> NodeId {
        let id = NodeId(self.0.len());
        self.0.push(Node {
            id,
            kind: NodeKind::VariantDef(def),
        });
        id
    }

    pub fn push_field_def(&mut self, def: FieldDef) -> NodeId {
        let id = NodeId(self.0.len());
        self.0.push(Node {
            id,
            kind: NodeKind::FieldDef(def),
        });
        id
    }

    pub fn push_type_def(&mut self, def: TypeDef) -> NodeId {
        let id = NodeId(self.0.len());
        self.0.push(Node {
            id,
            kind: NodeKind::TypeDef(def),
        });
        id
    }

    pub fn push_mod_def(&mut self, def: Module) -> NodeId {
        let id = NodeId(self.0.len());
        self.0.push(Node {
            id,
            kind: NodeKind::Mod(def),
        });
        id
    }

    pub fn push_path(&mut self, def: Path) -> NodeId {
        let id = NodeId(self.0.len());
        self.0.push(Node {
            id,
            kind: NodeKind::Path(def),
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
                            ExprKind::Lit(_) => {
                                f.write_str(op_str)?;
                            }
                            ExprKind::Ident(_) => {
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
                            ExprKind::Block(stmts) => {
                                f.write_str("{")?;
                                for &(node, terminator) in &stmts {
                                    f.write_str("\n    ")?;
                                    print_node(f, nodes, node)?;
                                    if terminator {
                                        f.write_str(";")?;
                                    }
                                }
                                f.write_str("\n}")?;
                            }
                            ExprKind::Let(name, expr) => {
                                f.write_str("let ")?;
                                f.write_str(&name)?;
                                f.write_str(" = ")?;
                                print_node(f, nodes, expr)?;
                            }
                            ExprKind::Path(..) => (),
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
                        f.write_str(") ")?;

                        if let Some(ret_ty) = &func.ret_ty {
                            f.write_str("-> ")?;
                            f.write_str(&ret_ty)?;
                            f.write_str(" ")?;
                        }

                        print_node(f, nodes, func.body)?;
                    }

                    Ok(())
                }
                print_node(f, self, NodeId(self.0.len() - 1))
            }
            None => Ok(()),
        }
    }
}

#[derive(Copy, Clone, Hash, PartialEq, Eq, Debug)]
pub struct NodeId(pub usize);

#[derive(Debug)]
pub struct Node {
    pub id: NodeId,
    pub kind: NodeKind,
}

#[derive(Debug)]
pub enum NodeKind {
    Expr(Expr),
    Fn(Fn),
    TypeDef(TypeDef),
    VariantDef(VariantDef),
    FieldDef(FieldDef),
    Mod(Module),
    Path(Path),
}

#[derive(Debug, Copy, Clone)]
pub enum Visibility {
    Pub,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Path {
    pub segments: Vec<(String, Span)>,
}

#[derive(Debug)]
pub struct Module {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub items: Vec<NodeId>,
}

#[derive(Debug)]
pub struct TypeDef {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub variants: Vec<NodeId>,
}

#[derive(Debug)]
pub struct VariantDef {
    pub visibility: Option<Visibility>,
    pub name: Option<String>,
    pub field_defs: Vec<NodeId>,
    pub type_defs: Vec<NodeId>,
}

#[derive(Debug)]
pub struct FieldDef {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub ty: NodeId,
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
    Let(String, NodeId),
    Block(Vec<(NodeId, bool)>),
    BinOp(BinOp, NodeId, NodeId),
    UnOp(UnOp, NodeId),
    Lit(Literal),
    Ident(String),
    Path(Path),
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
            ExprKind::Lit(l) => match l {
                Literal::Float(f) => f.to_string(),
                Literal::Int(i) => i.to_string(),
            },
            ExprKind::Ident(ident) => ident.to_string(),
            ExprKind::Block(_) => "".to_string(),
            ExprKind::Let(..) => "".to_string(),
            ExprKind::Path(..) => "".to_string(),
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
