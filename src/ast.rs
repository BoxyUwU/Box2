use crate::tokenize::{Literal, Span};
use bumpalo::Bump;
use std::{cell::RefCell, collections::HashMap};

#[derive(Default)]
pub struct Nodes<'a> {
    pub arena: Bump,
    pub ids: RefCell<Vec<&'a Node<'a>>>,
    variant_parent: RefCell<HashMap<NodeId, NodeId>>,
}

impl<'a> Nodes<'a> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn get(&'a self, id: NodeId) -> &'a Node {
        self.ids.borrow()[id.0]
    }

    pub fn push_node(&'a self, f: impl FnOnce(NodeId) -> Node<'a>) -> &'a Node<'a> {
        let mut ids = self.ids.borrow_mut();
        let id = NodeId(ids.len());
        let node = f(id);
        if let Node::Item(Item::TypeDef(TypeDef { id, variants, .. })) = node {
            let mut variant_parents = self.variant_parent.borrow_mut();
            for variant in variants {
                variant_parents.insert(variant.id, id);
            }
        }
        let node = self.arena.alloc(node);
        ids.push(&*node);
        node
    }

    pub fn push_ty(&'a self, f: impl FnOnce(NodeId) -> Ty<'a>) -> &Ty {
        self.push_node(|id| Node::Ty(f(id))).unwrap_ty()
    }

    pub fn push_expr_with(&'a self, f: impl FnOnce(NodeId) -> ExprKind<'a>) -> &Expr {
        self.push_node(|id| Node::Expr(Expr { id, kind: f(id) }))
            .unwrap_expr()
    }

    pub fn push_expr(&'a self, kind: ExprKind<'a>) -> &Expr {
        self.push_node(|id| Node::Expr(Expr { id, kind }))
            .unwrap_expr()
    }

    pub fn push_fn(&'a self, f: impl FnOnce(NodeId) -> Fn<'a>) -> &Item {
        self.push_node(|id| Node::Item(Item::Fn(f(id))))
            .unwrap_item()
    }

    pub fn push_variant_def(&'a self, f: impl FnOnce(NodeId) -> VariantDef<'a>) -> &VariantDef {
        self.push_node(|id| Node::Item(Item::VariantDef(f(id))))
            .unwrap_variant_def()
    }

    pub fn push_field_def(&'a self, f: impl FnOnce(NodeId) -> FieldDef<'a>) -> &FieldDef {
        self.push_node(|id| Node::Item(Item::FieldDef(f(id))))
            .unwrap_field_def()
    }

    pub fn push_type_def(&'a self, f: impl FnOnce(NodeId) -> TypeDef<'a>) -> &Item {
        self.push_node(|id| Node::Item(Item::TypeDef(f(id))))
            .unwrap_item()
    }

    pub fn push_mod_def(&'a self, f: impl FnOnce(NodeId) -> Module<'a>) -> &Item {
        self.push_node(|id| Node::Item(Item::Mod(f(id))))
            .unwrap_item()
    }

    pub fn push_use(&'a self, f: impl FnOnce(NodeId) -> Use<'a>) -> &Item {
        self.push_node(|id| Node::Item(Item::Use(f(id))))
            .unwrap_item()
    }

    pub fn push_param(&'a self, f: impl FnOnce(NodeId) -> Param<'a>) -> &Param {
        self.push_node(|id| Node::Param(f(id))).unwrap_param()
    }

    pub fn push_ty_alias(&'a self, f: impl FnOnce(NodeId) -> TypeAlias<'a>) -> &Item {
        self.push_node(|id| Node::Item(Item::TypeAlias(f(id))))
            .unwrap_item()
    }

    pub fn push_trait(&'a self, f: impl FnOnce(NodeId) -> Trait<'a>) -> &Item {
        self.push_node(|id| Node::Item(Item::Trait(f(id))))
            .unwrap_item()
    }

    pub fn push_impl(&'a self, f: impl FnOnce(NodeId) -> Impl<'a>) -> &Item {
        self.push_node(|id| Node::Item(Item::Impl(f(id))))
            .unwrap_item()
    }

    pub fn get_variants_adt(&'a self, variant: NodeId) -> &'a TypeDef {
        let parent = self.variant_parent.borrow()[&variant];
        self.get(parent).unwrap_type_def()
    }
}

#[derive(Copy, Clone, Hash, PartialEq, Eq, Debug)]
pub struct NodeId(pub usize);

#[derive(Copy, Clone, Debug)]
pub enum Node<'a> {
    Expr(Expr<'a>),
    Item(Item<'a>),
    Ty(Ty<'a>),
    Param(Param<'a>),
}

impl<'a> Node<'a> {
    pub fn unwrap_item(&self) -> &Item<'a> {
        unwrap_matches!(self, Node::Item(item) => item)
    }

    pub fn unwrap_expr(&self) -> &Expr<'a> {
        unwrap_matches!(self, Node::Expr(expr) => expr)
    }

    #[allow(unused)]
    pub fn unwrap_fn(&self) -> &Fn<'a> {
        unwrap_matches!(self, Node::Item(Item::Fn(expr)) => expr)
    }

    #[allow(unused)]
    pub fn unwrap_type_def(&self) -> &TypeDef<'a> {
        unwrap_matches!(self, Node::Item(Item::TypeDef(expr)) => expr)
    }

    pub fn unwrap_variant_def(&self) -> &VariantDef<'a> {
        unwrap_matches!(self, Node::Item(Item::VariantDef(expr)) => expr)
    }

    pub fn unwrap_field_def(&self) -> &FieldDef<'a> {
        unwrap_matches!(self, Node::Item(Item::FieldDef(expr)) => expr)
    }

    #[allow(unused)]
    pub fn unwrap_mod(&self) -> &Module<'a> {
        unwrap_matches!(self, Node::Item(Item::Mod(expr)) => expr)
    }

    #[allow(unused)]
    pub fn unwrap_trait(&self) -> &Trait<'a> {
        unwrap_matches!(self, Node::Item(Item::Trait(trait_)) => trait_)
    }

    #[allow(unused)]
    pub fn unwrap_impl(&self) -> &Impl<'a> {
        unwrap_matches!(self, Node::Item(Item::Impl(impl_)) => impl_)
    }

    #[allow(unused)]
    pub fn unwrap_type_alias(&self) -> &TypeAlias<'a> {
        unwrap_matches!(self, Node::Item(Item::TypeAlias(alias)) => alias)
    }

    pub fn unwrap_ty(&self) -> &Ty {
        unwrap_matches!(self, Node::Ty(expr) => expr)
    }

    pub fn unwrap_use(&self) -> &Use {
        unwrap_matches!(self, Node::Item(Item::Use(u)) => u)
    }

    pub fn unwrap_param(&self) -> &Param {
        unwrap_matches!(self, Node::Param(p) => p)
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
    pub span: Span,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Path<'a> {
    pub segments: &'a [(&'a str, Span)],
    pub span: Span,
}

#[derive(Copy, Clone, Debug)]
pub enum Item<'a> {
    Mod(Module<'a>),
    TypeDef(TypeDef<'a>),
    VariantDef(VariantDef<'a>),
    FieldDef(FieldDef<'a>),
    TypeAlias(TypeAlias<'a>),
    Fn(Fn<'a>),
    Use(Use<'a>),
    Trait(Trait<'a>),
    Impl(Impl<'a>),
}

impl<'a> Item<'a> {
    #[allow(unused)]
    pub fn unwrap_fn(&self) -> &Fn<'a> {
        unwrap_matches!(self, Item::Fn(expr) => expr)
    }

    pub fn unwrap_type_def(&self) -> &TypeDef<'a> {
        unwrap_matches!(self, Item::TypeDef(expr) => expr)
    }

    #[allow(unused)]
    pub fn unwrap_variant_def(&self) -> &VariantDef<'a> {
        unwrap_matches!(self, Item::VariantDef(expr) => expr)
    }

    #[allow(unused)]
    pub fn unwrap_field_def(&self) -> &FieldDef<'a> {
        unwrap_matches!(self, Item::FieldDef(expr) => expr)
    }

    pub fn unwrap_mod(&self) -> &Module<'a> {
        unwrap_matches!(self, Item::Mod(expr) => expr)
    }

    #[allow(unused)]
    pub fn unwrap_use(&self) -> &Use<'a> {
        unwrap_matches!(self, Item::Use(u) => u)
    }

    #[allow(unused)]
    pub fn unwrap_trait(&self) -> &Trait<'a> {
        unwrap_matches!(self, Item::Trait(t) => t)
    }

    #[allow(unused)]
    pub fn unwrap_impl(&self) -> &Impl<'a> {
        unwrap_matches!(self, Item::Impl(i) => i)
    }

    #[allow(unused)]
    pub fn unwrap_ty_alias(&self) -> &TypeAlias<'a> {
        unwrap_matches!(self, Item::TypeAlias(t) => t)
    }

    pub fn id(&self) -> NodeId {
        match self {
            Item::Mod(module) => module.id,
            Item::VariantDef(def) => def.id,
            Item::TypeDef(def) => def.id,
            Item::Fn(func) => func.id,
            Item::FieldDef(def) => def.id,
            Item::Use(u) => u.id,
            Item::TypeAlias(t) => t.id,
            Item::Trait(t) => t.id,
            Item::Impl(i) => i.id,
        }
    }

    pub fn name(&self) -> Option<&str> {
        Some(match self {
            Item::Mod(m) => m.name,
            Item::TypeDef(def) => def.name,
            Item::VariantDef(def) => return def.name,
            Item::FieldDef(def) => def.name,
            Item::Fn(f) => f.name,
            Item::Use(u) => u.name,
            Item::TypeAlias(t) => t.name,
            Item::Trait(t) => t.ident,
            Item::Impl(_) => return None,
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
pub struct TypeAlias<'a> {
    pub id: NodeId,
    pub visibility: Visibility,
    pub name: &'a str,
    pub name_span: Span,
    pub ty: Option<&'a Ty<'a>>,
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
pub struct Param<'a> {
    pub id: NodeId,
    pub ident: &'a str,
    pub ty: Option<&'a Ty<'a>>,
    pub span: Span,
}

#[derive(Copy, Clone, Debug)]
pub struct Fn<'a> {
    pub id: NodeId,
    pub visibility: Visibility,
    pub name: &'a str,
    pub params: &'a [&'a Param<'a>],
    pub ret_ty: Option<&'a Ty<'a>>,
    pub body: Option<&'a Expr<'a>>,
}

#[derive(Copy, Clone, Debug)]
pub struct Use<'a> {
    pub id: NodeId,
    pub visibility: Visibility,
    pub path: Path<'a>,
    pub name: &'a str,
}

#[derive(Copy, Clone, Debug)]
pub struct Trait<'a> {
    pub id: NodeId,
    pub span: Span,

    pub visibility: Visibility,
    pub ident: &'a str,
    pub assoc_items: &'a [AssocItem<'a>],
}

#[derive(Copy, Clone, Debug)]
pub enum AssocItem<'a> {
    Fn(&'a Fn<'a>),
    Type(&'a TypeAlias<'a>),
}

#[derive(Copy, Clone, Debug)]
pub struct Impl<'a> {
    pub id: NodeId,
    pub span: Span,

    pub of_trait: Path<'a>,
    pub self_ty: &'a Ty<'a>,

    pub assoc_items: &'a [AssocItem<'a>],
}

#[derive(Copy, Clone, Debug)]
pub struct Expr<'a> {
    pub id: NodeId,
    pub kind: ExprKind<'a>,
}

impl<'a> Expr<'a> {
    pub fn span(&self) -> Span {
        match &self.kind {
            ExprKind::Let(_, _, span)
            | ExprKind::Block(_, span)
            | ExprKind::BinOp(_, _, _, span)
            | ExprKind::UnOp(_, _, span)
            | ExprKind::Lit(_, span) => *span,
            ExprKind::Path(path) => path.span,
            ExprKind::FnCall(call) => call.span,
            ExprKind::TypeInit(ty_init) => ty_init.span,
            ExprKind::FieldInit(field_init) => field_init.span,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum ExprKind<'a> {
    Let(&'a Param<'a>, &'a Expr<'a>, Span),
    Block(&'a [(&'a Expr<'a>, bool)], Span),
    BinOp(BinOp, &'a Expr<'a>, &'a Expr<'a>, Span),
    UnOp(UnOp, &'a Expr<'a>, Span),
    Lit(Literal, Span),
    Path(Path<'a>),
    FnCall(FnCall<'a>),
    TypeInit(TypeInit<'a>),
    FieldInit(FieldInit<'a>),
}

#[derive(Copy, Clone, Debug)]
pub struct FnCall<'a> {
    pub func: &'a Expr<'a>,
    pub args: &'a [&'a Expr<'a>],
    pub span: Span,
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
    pub span: Span,
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
