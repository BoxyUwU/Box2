use std::cell::RefCell;

use logos::Span;
use typed_arena::Arena;

use crate::tokenize::Literal;

pub struct Nodes<'a>(Arena<Node<'a>>, RefCell<Vec<&'a Node<'a>>>);

impl<'a> Nodes<'a> {
    pub fn new() -> Self {
        Self(Arena::new(), RefCell::default())
    }

    pub fn get(&'a self, id: NodeId) -> &Node {
        self.1.borrow()[id.0]
    }

    pub fn push_ty(&'a self, ty: Ty) -> &Node {
        let id = NodeId(self.0.len());
        let node = &*self.0.alloc(Node {
            id,
            kind: NodeKind::Ty(ty),
        });
        self.1.borrow_mut().push(node);
        node
    }

    pub fn push_expr(&'a self, kind: ExprKind<'a>) -> &Node {
        let id = NodeId(self.0.len());
        let node = &*self.0.alloc(Node {
            id,
            kind: NodeKind::Expr(Expr { id, kind }),
        });
        self.1.borrow_mut().push(node);
        node
    }

    pub fn push_fn(&'a self, func: Fn<'a>) -> &Node {
        let id = NodeId(self.0.len());
        let node = &*self.0.alloc(Node {
            id,
            kind: NodeKind::Fn(func),
        });
        self.1.borrow_mut().push(node);
        node
    }

    pub fn push_variant_def(&'a self, def: VariantDef<'a>) -> &Node {
        let id = NodeId(self.0.len());
        let node = &*self.0.alloc(Node {
            id,
            kind: NodeKind::VariantDef(def),
        });
        self.1.borrow_mut().push(node);
        node
    }

    pub fn push_field_def(&'a self, def: FieldDef<'a>) -> &Node {
        let id = NodeId(self.0.len());
        let node = &*self.0.alloc(Node {
            id,
            kind: NodeKind::FieldDef(def),
        });
        self.1.borrow_mut().push(node);
        node
    }

    pub fn push_type_def(&'a self, def: TypeDef<'a>) -> &Node {
        let id = NodeId(self.0.len());
        let node = &*self.0.alloc(Node {
            id,
            kind: NodeKind::TypeDef(def),
        });
        self.1.borrow_mut().push(node);
        node
    }

    pub fn push_mod_def(&'a self, def: Module<'a>) -> &Node {
        let id = NodeId(self.0.len());
        let node = &*self.0.alloc(Node {
            id,
            kind: NodeKind::Mod(def),
        });
        self.1.borrow_mut().push(node);
        node
    }
}

#[derive(Copy, Clone, Hash, PartialEq, Eq, Debug)]
pub struct NodeId(pub usize);

#[derive(Debug)]
pub struct Node<'a> {
    pub id: NodeId,
    pub kind: NodeKind<'a>,
}

#[derive(Debug)]
pub enum NodeKind<'a> {
    Expr(Expr<'a>),
    Fn(Fn<'a>),
    TypeDef(TypeDef<'a>),
    VariantDef(VariantDef<'a>),
    FieldDef(FieldDef<'a>),
    Mod(Module<'a>),
    Ty(Ty),
}

impl<'a> NodeKind<'a> {
    pub fn unwrap_expr(&self) -> &Expr<'a> {
        unwrap_matches!(self, NodeKind::Expr(expr) => expr)
    }

    pub fn unwrap_fn(&self) -> &Fn<'a> {
        unwrap_matches!(self, NodeKind::Fn(expr) => expr)
    }

    pub fn unwrap_type_def(&self) -> &TypeDef<'a> {
        unwrap_matches!(self, NodeKind::TypeDef(expr) => expr)
    }

    pub fn unwrap_variant_def(&self) -> &VariantDef<'a> {
        unwrap_matches!(self, NodeKind::VariantDef(expr) => expr)
    }

    pub fn unwrap_field_def(&self) -> &FieldDef<'a> {
        unwrap_matches!(self, NodeKind::FieldDef(expr) => expr)
    }

    pub fn unwrap_mod(&self) -> &Module<'a> {
        unwrap_matches!(self, NodeKind::Mod(expr) => expr)
    }

    pub fn unwrap_ty(&self) -> &Ty {
        unwrap_matches!(self, NodeKind::Ty(expr) => expr)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Visibility {
    Pub,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ty {
    pub path: Path,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Path {
    pub segments: Vec<(String, Span)>,
}

#[derive(Debug)]
pub struct Module<'a> {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub items: Vec<&'a Node<'a>>,
}

#[derive(Debug)]
pub struct TypeDef<'a> {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub variants: Box<[&'a Node<'a>]>,
}

#[derive(Debug)]
pub struct VariantDef<'a> {
    pub visibility: Option<Visibility>,
    pub name: Option<String>,
    pub field_defs: Box<[&'a Node<'a>]>,
    pub type_defs: Box<[&'a Node<'a>]>,
}

#[derive(Debug)]
pub struct FieldDef<'a> {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub ty: &'a Node<'a>,
}

#[derive(Debug)]
pub struct Fn<'a> {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub params: Vec<(String, &'a Node<'a>)>,
    pub ret_ty: Option<String>,
    pub body: &'a Node<'a>,
}

#[derive(Debug)]
pub struct Expr<'a> {
    pub id: NodeId,
    pub kind: ExprKind<'a>,
}

#[derive(Clone, Debug)]
pub enum ExprKind<'a> {
    Let(String, &'a Node<'a>),
    Block(Vec<(&'a Node<'a>, bool)>),
    BinOp(BinOp, &'a Node<'a>, &'a Node<'a>),
    UnOp(UnOp, &'a Node<'a>),
    Lit(Literal),
    Path(Path),
    FnCall(FnCall<'a>),
    MethodCall(MethodCall<'a>),
    TypeInit(TypeInit<'a>),
    FieldInit(FieldInit<'a>),
}

#[derive(Debug, Clone)]
pub struct FnCall<'a> {
    pub func: &'a Node<'a>,
    pub args: Vec<&'a Node<'a>>,
}

#[derive(Debug, Clone)]
pub struct MethodCall<'a> {
    pub receiver: &'a Node<'a>,
    pub func: &'a Node<'a>,
    pub args: Vec<&'a Node<'a>>,
}

#[derive(Debug, Clone)]
pub struct FieldInit<'a> {
    pub ident: String,
    pub span: Span,
    pub expr: &'a Node<'a>,
}

#[derive(Debug, Clone)]
pub struct TypeInit<'a> {
    pub path: &'a Node<'a>,
    pub field_inits: Vec<&'a Node<'a>>,
}

impl<'a> ExprKind<'a> {
    pub fn op_string(&self) -> String {
        match self {
            ExprKind::BinOp(op, _, _) => match op {
                BinOp::Dot => ".".into(),
                BinOp::Add => "+".into(),
                BinOp::Sub => "-".into(),
                BinOp::Div => "/".into(),
                BinOp::Mul => "*".into(),
            },
            ExprKind::UnOp(op, _) => match op {
                UnOp::Neg => "-".into(),
                UnOp::Call => "Call".into(),
            },
            ExprKind::Lit(l) => match l {
                Literal::Float(f) => f.to_string(),
                Literal::Int(i) => i.to_string(),
            },
            ExprKind::Block(_) => "".to_string(),
            ExprKind::Let(..) => "".to_string(),
            ExprKind::Path(path) => {
                let mut path_string = String::new();
                for (segment, _) in &path.segments[..path.segments.len() - 1] {
                    path_string.push_str(&segment);
                    path_string.push_str("::");
                }
                path_string.push_str(&path.segments.last().unwrap().0);
                path_string
            }
            ExprKind::TypeInit(..) => "".to_string(),
            ExprKind::FieldInit(..) => "".to_string(),
            ExprKind::FnCall(..) => "".to_string(),
            ExprKind::MethodCall(..) => "".to_string(),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Dot,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum UnOp {
    Neg,
    Call,
}
