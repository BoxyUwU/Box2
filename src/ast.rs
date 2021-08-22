use std::cell::RefCell;

use typed_arena::Arena;

use crate::tokenize::{Literal, Span};

#[derive(Default)]
pub struct Nodes<'a> {
    pub arena: Arena<Node<'a>>,
    pub ids: RefCell<Vec<&'a Node<'a>>>,

    pub string_arena: Arena<String>,
    pub item_def_slices: Arena<Vec<&'a Item<'a>>>,
    pub type_def_slices: Arena<Vec<&'a TypeDef<'a>>>,
    pub variant_def_slices: Arena<Vec<&'a VariantDef<'a>>>,
    pub field_def_slices: Arena<Vec<&'a FieldDef<'a>>>,
    pub expr_slices: Arena<Vec<&'a Expr<'a>>>,
    pub expr_bool_slices: Arena<Vec<(&'a Expr<'a>, bool)>>,
    pub field_init_slices: Arena<Vec<&'a FieldInit<'a>>>,
    pub str_span_slices: Arena<Vec<(&'a str, Span)>>,
    pub str_ty_slices: Arena<Vec<(&'a str, &'a Ty<'a>)>>,
}

impl<'a> Nodes<'a> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn get(&'a self, id: NodeId) -> &'a Node {
        self.ids.borrow()[id.0]
    }

    pub fn push_ty(&'a self, f: impl FnOnce(NodeId) -> Ty<'a>) -> &Ty {
        let id = NodeId(self.arena.len());
        let node = &*self.arena.alloc(Node::Ty(f(id)));
        self.ids.borrow_mut().push(node);
        node.unwrap_ty()
    }

    pub fn push_expr_with(&'a self, f: impl FnOnce(NodeId) -> ExprKind<'a>) -> &Expr {
        let id = NodeId(self.arena.len());
        let node = &*self.arena.alloc(Node::Expr(Expr { id, kind: f(id) }));
        self.ids.borrow_mut().push(node);
        node.unwrap_expr()
    }

    pub fn push_expr(&'a self, kind: ExprKind<'a>) -> &Expr {
        let id = NodeId(self.arena.len());
        let node = &*self.arena.alloc(Node::Expr(Expr { id, kind }));
        self.ids.borrow_mut().push(node);
        node.unwrap_expr()
    }

    pub fn push_fn(&'a self, f: impl FnOnce(NodeId) -> Fn<'a>) -> &Item {
        let id = NodeId(self.arena.len());
        let node = &*self.arena.alloc(Node::Item(Item::Fn(f(id))));
        self.ids.borrow_mut().push(node);
        node.unwrap_item()
    }

    pub fn push_variant_def(&'a self, f: impl FnOnce(NodeId) -> VariantDef<'a>) -> &VariantDef {
        let id = NodeId(self.arena.len());
        let node = &*self.arena.alloc(Node::Item(Item::VariantDef(f(id))));
        self.ids.borrow_mut().push(node);
        node.unwrap_variant_def()
    }

    pub fn push_field_def(&'a self, f: impl FnOnce(NodeId) -> FieldDef<'a>) -> &FieldDef {
        let id = NodeId(self.arena.len());
        let node = &*self.arena.alloc(Node::Item(Item::FieldDef(f(id))));
        self.ids.borrow_mut().push(node);
        node.unwrap_field_def()
    }

    pub fn push_type_def(&'a self, f: impl FnOnce(NodeId) -> TypeDef<'a>) -> &Item {
        let id = NodeId(self.arena.len());
        let node = &*self.arena.alloc(Node::Item(Item::TypeDef(f(id))));
        self.ids.borrow_mut().push(node);
        node.unwrap_item()
    }

    pub fn push_mod_def(&'a self, f: impl FnOnce(NodeId) -> Module<'a>) -> &Item {
        let id = NodeId(self.arena.len());
        let node = &*self.arena.alloc(Node::Item(Item::Mod(f(id))));
        self.ids.borrow_mut().push(node);
        node.unwrap_item()
    }

    pub fn push_use(&'a self, f: impl FnOnce(NodeId) -> Use<'a>) -> &Item {
        let id = NodeId(self.arena.len());
        let node = &*self.arena.alloc(Node::Item(Item::Use(f(id))));
        self.ids.borrow_mut().push(node);
        node.unwrap_item()
    }
}

#[derive(Copy, Clone, Hash, PartialEq, Eq, Debug)]
pub struct NodeId(pub usize);

#[derive(Copy, Clone, Debug)]
pub enum Node<'a> {
    Expr(Expr<'a>),
    Item(Item<'a>),
    Ty(Ty<'a>),
}

impl<'a> Node<'a> {
    pub fn unwrap_item(&self) -> &Item<'a> {
        unwrap_matches!(self, Node::Item(item) => item)
    }

    pub fn unwrap_expr(&self) -> &Expr<'a> {
        unwrap_matches!(self, Node::Expr(expr) => expr)
    }

    pub fn unwrap_fn(&self) -> &Fn<'a> {
        unwrap_matches!(self, Node::Item(Item::Fn(expr)) => expr)
    }

    pub fn unwrap_type_def(&self) -> &TypeDef<'a> {
        unwrap_matches!(self, Node::Item(Item::TypeDef(expr)) => expr)
    }

    pub fn unwrap_variant_def(&self) -> &VariantDef<'a> {
        unwrap_matches!(self, Node::Item(Item::VariantDef(expr)) => expr)
    }

    pub fn unwrap_field_def(&self) -> &FieldDef<'a> {
        unwrap_matches!(self, Node::Item(Item::FieldDef(expr)) => expr)
    }

    pub fn unwrap_mod(&self) -> &Module<'a> {
        unwrap_matches!(self, Node::Item(Item::Mod(expr)) => expr)
    }

    pub fn unwrap_ty(&self) -> &Ty {
        unwrap_matches!(self, Node::Ty(expr) => expr)
    }

    pub fn unwrap_use(&self) -> &Use {
        unwrap_matches!(self, Node::Item(Item::Use(u)) => u)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Visibility {
    Priv,
    Pub,
}
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Ty<'a> {
    pub id: NodeId,
    pub path: Path<'a>,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Path<'a> {
    pub segments: &'a [(&'a str, Span)],
}

#[derive(Copy, Clone, Debug)]
pub enum Item<'a> {
    Mod(Module<'a>),
    TypeDef(TypeDef<'a>),
    VariantDef(VariantDef<'a>),
    FieldDef(FieldDef<'a>),
    Fn(Fn<'a>),
    Use(Use<'a>),
}

impl<'a> Item<'a> {
    pub fn unwrap_fn(&self) -> &Fn<'a> {
        unwrap_matches!(self, Item::Fn(expr) => expr)
    }

    pub fn unwrap_type_def(&self) -> &TypeDef<'a> {
        unwrap_matches!(self, Item::TypeDef(expr) => expr)
    }

    pub fn unwrap_variant_def(&self) -> &VariantDef<'a> {
        unwrap_matches!(self, Item::VariantDef(expr) => expr)
    }

    pub fn unwrap_field_def(&self) -> &FieldDef<'a> {
        unwrap_matches!(self, Item::FieldDef(expr) => expr)
    }

    pub fn unwrap_mod(&self) -> &Module<'a> {
        unwrap_matches!(self, Item::Mod(expr) => expr)
    }

    pub fn unwrap_use(&self) -> &Use<'a> {
        unwrap_matches!(self, Item::Use(u) => u)
    }

    pub fn id(&self) -> NodeId {
        match self {
            Item::Mod(module) => module.id,
            Item::VariantDef(def) => def.id,
            Item::TypeDef(def) => def.id,
            Item::Fn(func) => func.id,
            Item::FieldDef(def) => def.id,
            Item::Use(u) => u.id,
        }
    }

    pub fn name(&self) -> Option<&str> {
        Some(match self {
            Item::Mod(m) => m.name,
            Item::TypeDef(def) => def.name,
            Item::VariantDef(def) => return def.name,
            Item::FieldDef(def) => def.name,
            Item::Fn(f) => f.name,
            Item::Use(u) => u.path.segments.last().unwrap().0,
        })
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Module<'a> {
    pub id: NodeId,
    pub visibility: Visibility,
    pub name: &'a str,
    pub items: &'a [&'a Item<'a>],
}

#[derive(Copy, Clone, Debug)]
pub struct TypeDef<'a> {
    pub id: NodeId,
    pub visibility: Visibility,
    pub name: &'a str,
    pub name_span: Span,
    pub variants: &'a [&'a VariantDef<'a>],
}

#[derive(Copy, Clone, Debug)]
pub struct VariantDef<'a> {
    pub id: NodeId,
    pub visibility: Visibility,
    pub name: Option<&'a str>,
    pub field_defs: &'a [&'a FieldDef<'a>],
    pub type_defs: &'a [&'a TypeDef<'a>],
}

#[derive(Copy, Clone, Debug)]
pub struct FieldDef<'a> {
    pub id: NodeId,
    pub visibility: Visibility,
    pub name: &'a str,
    pub ty: &'a Ty<'a>,
}

#[derive(Copy, Clone, Debug)]
pub struct Fn<'a> {
    pub id: NodeId,
    pub visibility: Visibility,
    pub name: &'a str,
    pub params: &'a [(&'a str, &'a Ty<'a>)],
    pub ret_ty: Option<&'a Ty<'a>>,
    pub body: &'a Expr<'a>,
}

#[derive(Copy, Clone, Debug)]
pub struct Use<'a> {
    pub id: NodeId,
    pub visibility: Visibility,
    pub path: Path<'a>,
}

#[derive(Copy, Clone, Debug)]
pub struct Expr<'a> {
    pub id: NodeId,
    pub kind: ExprKind<'a>,
}

#[derive(Copy, Clone, Debug)]
pub enum ExprKind<'a> {
    Let(&'a str, &'a Expr<'a>),
    Block(&'a [(&'a Expr<'a>, bool)]),
    BinOp(BinOp, &'a Expr<'a>, &'a Expr<'a>),
    UnOp(UnOp, &'a Expr<'a>),
    Lit(Literal),
    Path(Path<'a>),
    FnCall(FnCall<'a>),
    MethodCall(MethodCall<'a>),
    TypeInit(TypeInit<'a>),
    FieldInit(FieldInit<'a>),
}

#[derive(Copy, Clone, Debug)]
pub struct FnCall<'a> {
    pub func: &'a Expr<'a>,
    pub args: &'a [&'a Expr<'a>],
}

#[derive(Debug, Copy, Clone)]
pub struct MethodCall<'a> {
    pub receiver: &'a Expr<'a>,
    pub func: &'a Expr<'a>,
    pub args: &'a [&'a Expr<'a>],
}

#[derive(Debug, Copy, Clone)]
pub struct FieldInit<'a> {
    pub id: NodeId,
    pub ident: &'a str,
    pub span: Span,
    pub expr: &'a Expr<'a>,
}

#[derive(Debug, Copy, Clone)]
pub struct TypeInit<'a> {
    pub path: &'a Expr<'a>,
    pub field_inits: &'a [&'a FieldInit<'a>],
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
