use core::fmt;
use std::{cell::RefCell, collections::HashMap};

use bumpalo::Bump;
use codespan_reporting::diagnostic::Diagnostic;

use crate::{
    ast,
    resolve::Res,
    tir::visit::{
        TypeFolder, TypeSuperFoldable, TypeSuperVisitable, TypeVisitable, TypeVisitableExt,
        TypeVisitor,
    },
    tokenize::{Literal, Span},
    typeck::InferCtxt,
};

use self::visit::TypeFoldable;

pub mod building;
pub mod visit;

pub struct TirCtx<'t> {
    pub arena: Bump,
    items: RefCell<HashMap<TirId, &'t Item<'t>>>,

    errors: RefCell<Vec<Diagnostic<usize>>>,
}
impl<'t> TirCtx<'t> {
    pub fn new() -> Self {
        Self {
            arena: Bump::new(),
            items: RefCell::new(HashMap::new()),
            errors: RefCell::new(vec![]),
        }
    }

    pub fn err(&self, err: Diagnostic<usize>) {
        self.errors.borrow_mut().push(err);
    }

    pub fn get_item(&self, id: TirId) -> &'t Item<'t> {
        self.items.borrow().get(&id).unwrap()
    }

    pub fn take_errs(&self) -> Vec<Diagnostic<usize>> {
        std::mem::take(&mut *self.errors.borrow_mut())
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct BodyId(usize);
#[derive(Copy, Clone, Debug)]
pub struct BodySource<'t> {
    pub params: &'t [(ast::NodeId, EarlyBinder<&'t Ty<'t>>)],
    pub ret: EarlyBinder<&'t Ty<'t>>,
    pub expr: ast::NodeId,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct TirId(usize);

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct GenArgs<'t>(pub &'t [GenArg<'t>]);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum GenArg<'t> {
    Ty(&'t Ty<'t>),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct BoundVar(pub u32);

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Universe {
    idx: u32,
    gen: UniverseGen,
}
impl fmt::Debug for Universe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "U({}_{})", self.idx, self.gen.0)
    }
}
impl fmt::Display for Universe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "U{}", self.idx)
    }
}
impl Universe {
    pub const ROOT: Universe = Universe {
        idx: 0,
        gen: UniverseGen(0),
    };

    /// Prefer to use `UniverseStorage`/`Infcx`
    pub fn new_raw(idx: u32, gen: u32) -> Self {
        Self {
            idx,
            gen: UniverseGen(gen),
        }
    }

    pub fn can_name(self, b: Universe, infcx: &InferCtxt<'_>) -> bool {
        assert!(infcx.is_universe_alive(self));
        assert!(infcx.is_universe_alive(b));

        self.idx >= b.idx
    }

    pub fn idx(self) -> u32 {
        self.idx
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct UniverseGen(u32);

pub struct UniverseStorage {
    alive_universes: Vec<UniverseGen>,
    /// Indexed by the `Universe` types `idx` field to find what the previous generation at that index was
    dead_universes: Vec<UniverseGen>,
}
impl UniverseStorage {
    pub fn new() -> Self {
        Self {
            alive_universes: vec![UniverseGen(0)],
            dead_universes: vec![UniverseGen(0)],
        }
    }

    pub fn current_universe(&self) -> Universe {
        let idx = self.alive_universes.len() - 1;
        let gen = self.alive_universes[idx];
        Universe {
            idx: idx as u32,
            gen,
        }
    }

    pub fn enter_new_universe(&mut self) -> Universe {
        let new_idx = self.alive_universes.len();
        let gen = match self.dead_universes.get_mut(new_idx) {
            Some(gen) => {
                gen.0 += 1;
                *gen
            }
            None => {
                self.dead_universes.push(UniverseGen(0));
                UniverseGen(0)
            }
        };
        self.alive_universes.push(gen);
        Universe {
            idx: new_idx as u32,
            gen,
        }
    }

    pub fn exit_current_universe(&mut self) {
        assert!(self.alive_universes.len() >= 2);
        self.alive_universes.pop();
    }

    pub fn is_universe_alive(&self, universe: Universe) -> bool {
        match self.alive_universes.get(universe.idx as usize) {
            Some(gen) if gen.0 == universe.gen.0 => true,
            _ => false,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct DebruijnIndex(pub u32);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Ord, PartialOrd)]
pub struct InferId(pub u32);

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct EarlyBinder<T>(T);

impl<T> EarlyBinder<T> {
    pub fn instantiate<'t>(self, args: GenArgs<'t>, tcx: &'t TirCtx<'t>) -> T
    where
        T: TypeFoldable<'t>,
    {
        assert!(!args.has_escaping_bound_vars());

        struct Folder<'t> {
            args: GenArgs<'t>,
            tcx: &'t TirCtx<'t>,
            outtermost_debruijn: DebruijnIndex,
        }
        impl<'t> Folder<'t> {
            fn new(tcx: &'t TirCtx<'t>, args: GenArgs<'t>) -> Self {
                Self {
                    args,
                    tcx,
                    outtermost_debruijn: DebruijnIndex(0),
                }
            }
        }

        impl<'t> TypeFolder<'t> for Folder<'t> {
            fn tcx(&self) -> &'t TirCtx<'t> {
                self.tcx
            }

            fn fold_ty(&mut self, ty: &'t Ty<'t>) -> &'t Ty<'t> {
                match ty {
                    Ty::Bound(debruijn, var) if *debruijn == self.outtermost_debruijn => {
                        match self.args.0[var.0 as usize] {
                            GenArg::Ty(ty) => ty,
                        }
                    }
                    _ => ty.super_fold_with(self),
                }
            }

            fn fold_binder<T: TypeFoldable<'t>>(&mut self, binder: Binder<'t, T>) -> Binder<'t, T> {
                self.outtermost_debruijn.0 += 1;
                let r = binder.value.fold_with(self);
                self.outtermost_debruijn.0 -= 1;
                Binder {
                    value: r,
                    vars: binder.vars,
                }
            }
        }

        self.0.fold_with(&mut Folder::new(tcx, args))
    }

    pub fn instantiate_root_placeholders<'t>(self, tcx: &'t TirCtx<'t>) -> T
    where
        T: TypeFoldable<'t>,
    {
        struct Folder<'t> {
            tcx: &'t TirCtx<'t>,
            outtermost_debruijn: DebruijnIndex,
        }
        impl<'t> Folder<'t> {
            fn new(tcx: &'t TirCtx<'t>) -> Self {
                Self {
                    tcx,
                    outtermost_debruijn: DebruijnIndex(0),
                }
            }
        }
        impl<'t> TypeFolder<'t> for Folder<'t> {
            fn tcx(&self) -> &'t TirCtx<'t> {
                self.tcx
            }

            fn fold_ty(&mut self, ty: &'t Ty<'t>) -> &'t Ty<'t> {
                match ty {
                    Ty::Bound(debruijn, var) if *debruijn == self.outtermost_debruijn => {
                        self.tcx.arena.alloc(Ty::Placeholder(Universe::ROOT, *var))
                    }
                    _ => ty.super_fold_with(self),
                }
            }

            fn fold_binder<T: TypeFoldable<'t>>(&mut self, binder: Binder<'t, T>) -> Binder<'t, T> {
                self.outtermost_debruijn.0 += 1;
                let r = binder.value.fold_with(self);
                self.outtermost_debruijn.0 -= 1;
                Binder {
                    value: r,
                    vars: binder.vars,
                }
            }
        }

        self.0.fold_with(&mut Folder::new(tcx))
    }

    /// be careful
    pub fn skip_binder(self) -> T {
        self.0
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Binder<'t, T> {
    value: T,
    vars: &'t [BoundVarKind],
}
impl<'t, T> Binder<'t, T> {
    pub fn bind_with_vars(value: T, vars: &'t [BoundVarKind]) -> Self {
        // FIXME: validate vars
        Self { value, vars }
    }

    pub fn vars(&self) -> &'t [BoundVarKind] {
        self.vars
    }

    /// Dangerous
    pub fn skip_binder(self) -> T {
        self.value
    }

    pub fn no_bound_vars(self) -> Option<T> {
        match self.vars.len() {
            0 => Some(self.value),
            _ => None,
        }
    }

    pub fn dummy(tcx: &'t TirCtx<'t>, value: T) -> Binder<'t, T>
    where
        T: TypeVisitable<'t>,
    {
        struct Folder {
            outtermost_debruijn: DebruijnIndex,
        }
        impl Folder {
            fn new() -> Self {
                Self {
                    outtermost_debruijn: DebruijnIndex(0),
                }
            }
        }
        impl<'t> TypeVisitor<'t> for Folder {
            fn visit_ty(&mut self, ty: &'t Ty<'t>) {
                match ty {
                    Ty::Bound(debruijn, _) if debruijn.0 >= self.outtermost_debruijn.0 => {
                        panic!("ty: {:?} with escaping bound vars", ty)
                    }
                    _ => ty.super_visit_with(self),
                }
            }

            fn visit_binder<T: TypeVisitable<'t>>(&mut self, binder: Binder<'t, T>) {
                self.outtermost_debruijn.0 += 1;
                binder.value.visit_with(self);
                self.outtermost_debruijn.0 -= 1;
            }
        }

        value.visit_with(&mut Folder::new());
        Binder { value, vars: &[] }
    }

    pub fn instantiate_with_infer(self, infcx: &mut InferCtxt<'t>, span: Span) -> T
    where
        T: TypeFoldable<'t>,
    {
        struct Folder<'a, 't> {
            infcx: &'a mut InferCtxt<'t>,
            outtermost_debruijn: DebruijnIndex,
            span: Span,
        }
        impl<'a, 't> Folder<'a, 't> {
            fn new(infcx: &'a mut InferCtxt<'t>, span: Span) -> Self {
                Self {
                    infcx,
                    span,
                    outtermost_debruijn: DebruijnIndex(0),
                }
            }
        }
        impl<'a, 't> TypeFolder<'t> for Folder<'a, 't> {
            fn tcx(&self) -> &'t TirCtx<'t> {
                self.infcx.tcx
            }

            fn fold_ty(&mut self, ty: &'t Ty<'t>) -> &'t Ty<'t> {
                match ty {
                    Ty::Bound(debruijn, _) if *debruijn == self.outtermost_debruijn => self
                        .infcx
                        .tcx
                        .arena
                        .alloc(Ty::Infer(self.infcx.new_var(self.span))),
                    _ => ty.super_fold_with(self),
                }
            }

            fn fold_binder<T: TypeFoldable<'t>>(&mut self, binder: Binder<'t, T>) -> Binder<'t, T> {
                self.outtermost_debruijn.0 += 1;
                let r = binder.value.fold_with(self);
                self.outtermost_debruijn.0 -= 1;
                Binder {
                    value: r,
                    vars: binder.vars,
                }
            }
        }

        Folder::new(infcx, span).fold_binder(self).skip_binder()
    }

    pub fn enter_forall<U>(self, infcx: &mut InferCtxt<'t>, f: impl FnOnce(T) -> U) -> U
    where
        T: TypeFoldable<'t>,
    {
        struct Folder<'a, 't> {
            infcx: &'a InferCtxt<'t>,
            outtermost_debruijn: DebruijnIndex,
        }
        impl<'a, 't> Folder<'a, 't> {
            fn new(infcx: &'a InferCtxt<'t>) -> Self {
                Self {
                    infcx,
                    outtermost_debruijn: DebruijnIndex(0),
                }
            }
        }
        impl<'a, 't> TypeFolder<'t> for Folder<'a, 't> {
            fn tcx(&self) -> &'t TirCtx<'t> {
                self.infcx.tcx
            }

            fn fold_ty(&mut self, ty: &'t Ty<'t>) -> &'t Ty<'t> {
                match ty {
                    Ty::Bound(debruijn, var) if *debruijn == self.outtermost_debruijn => self
                        .infcx
                        .tcx
                        .arena
                        .alloc(Ty::Placeholder(self.infcx.current_universe(), *var)),
                    _ => ty.super_fold_with(self),
                }
            }

            fn fold_binder<T: TypeFoldable<'t>>(&mut self, binder: Binder<'t, T>) -> Binder<'t, T> {
                self.outtermost_debruijn.0 += 1;
                let r = binder.value.fold_with(self);
                self.outtermost_debruijn.0 -= 1;
                Binder {
                    value: r,
                    vars: binder.vars,
                }
            }
        }

        infcx.enter_new_universe();
        let inner = Folder::new(infcx).fold_binder(self).skip_binder();
        let r = f(inner);
        infcx.exit_current_universe();
        r
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum BoundVarKind {
    Ty,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Ty<'t> {
    Unit,
    Infer(InferId),
    FnDef(TirId, GenArgs<'t>),
    Adt(TirId, GenArgs<'t>),
    Alias(TirId, GenArgs<'t>),
    Bound(DebruijnIndex, BoundVar),
    Placeholder(Universe, BoundVar),
    Int,
    Float,
    Error,
}

#[derive(Copy, Clone, Debug)]
pub struct Generics<'t> {
    pub item: TirId,
    /// Number of parameters present in our parents' generics
    pub parent_count: u32,
    pub parent: Option<TirId>,
    pub params: &'t [GenParam<'t>],
    pub param_id_to_var: &'t HashMap<TirId, u32>,
}

#[derive(Copy, Clone, Debug)]
pub struct GenParam<'t> {
    pub name: &'t str,
    pub id: TirId,
    pub index: u32,
    pub kind: GenParamKind,
}

#[derive(Copy, Clone, Debug)]
pub enum GenParamKind {
    Ty,
}

#[derive(Copy, Clone, Debug)]
pub struct Path<'t> {
    pub span: Span,
    pub res: Res<TirId>,
    pub segs: &'t [PathSeg<'t>],
}

#[derive(Copy, Clone, Debug)]
pub struct PathSeg<'t> {
    pub args: GenArgs<'t>,
    pub res: Res<TirId>,
}

#[derive(Copy, Clone, Debug)]
pub struct Expr<'a> {
    pub kind: ExprKind<'a>,
}

#[derive(Copy, Clone, Debug)]
pub struct Param<'t> {
    pub ty: EarlyBinder<&'t Ty<'t>>,
    pub span: Span,
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
    pub field: TirId,
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

#[derive(Debug, Copy, Clone)]
pub enum Item<'t> {
    Mod(Mod<'t>),
    Fn(Fn<'t>),
    Adt(Adt<'t>),
    Variant(Variant<'t>),
    Field(Field<'t>),
    TyAlias(TyAlias<'t>),
    Trait(Trait<'t>),
    Impl(Impl<'t>),
}
impl<'t> Item<'t> {
    pub fn unwrap_adt(&self) -> &Adt<'t> {
        match self {
            Item::Adt(adt) => adt,
            _ => panic!("item was not an adt: {:?}", self),
        }
    }

    pub fn unwrap_variant(&self) -> &Variant<'t> {
        match self {
            Item::Variant(v) => v,
            _ => panic!("Item was not a variant: {:?}", self),
        }
    }

    pub fn unwrap_field(&self) -> &Field<'t> {
        match self {
            Item::Field(f) => f,
            _ => panic!("Item was not a field: {:?}", self),
        }
    }

    pub fn unwrap_fn(&self) -> &Fn<'t> {
        match self {
            Item::Fn(func) => func,
            _ => panic!("item was not a func: {:?}", self),
        }
    }

    pub fn unwrap_alias(&self) -> &TyAlias<'t> {
        match self {
            Item::TyAlias(alias) => alias,
            _ => panic!("item was not an alias: {:?}", self),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Fn<'t> {
    pub id: TirId,
    pub name: &'t str,
    pub params: &'t [Param<'t>],
    pub ret_ty: EarlyBinder<&'t Ty<'t>>,
    pub generics: &'t Generics<'t>,
    pub bounds: EarlyBinder<Bounds<'t>>,
    pub body: Option<BodyId>,
}

#[derive(Debug, Copy, Clone)]
pub struct Adt<'t> {
    pub id: TirId,
    pub name: &'t str,
    pub generics: &'t Generics<'t>,
    pub bounds: EarlyBinder<Bounds<'t>>,
    pub variants: &'t [&'t Variant<'t>],
}

#[derive(Debug, Copy, Clone)]
pub struct Variant<'t> {
    pub id: TirId,
    pub name: Option<&'t str>,
    pub adts: &'t [&'t Adt<'t>],
    pub fields: &'t [&'t Field<'t>],
}

#[derive(Debug, Copy, Clone)]
pub struct Field<'t> {
    pub id: TirId,
    pub name: &'t str,
    pub ty: EarlyBinder<&'t Ty<'t>>,
}

#[derive(Debug, Copy, Clone)]
pub struct TyAlias<'t> {
    pub id: TirId,
    pub name: &'t str,
    pub generics: &'t Generics<'t>,
    pub bounds: EarlyBinder<Bounds<'t>>,
    pub ty: Option<EarlyBinder<&'t Ty<'t>>>,
}

#[derive(Debug, Copy, Clone)]
pub struct Trait<'t> {
    pub id: TirId,
    pub name: &'t str,
    pub generics: &'t Generics<'t>,
    pub bounds: EarlyBinder<Bounds<'t>>,
    pub assoc_items: &'t [AssocItem<'t>],
}

#[derive(Debug, Copy, Clone)]
pub struct Impl<'t> {
    pub id: TirId,
    pub of_trait: (TirId, EarlyBinder<GenArgs<'t>>),
    pub generics: &'t Generics<'t>,
    pub bounds: EarlyBinder<Bounds<'t>>,
    pub assoc_items: &'t [AssocItem<'t>],
}

#[derive(Debug, Copy, Clone)]
pub enum AssocItem<'t> {
    TyAlias(TyAlias<'t>),
    Fn(Fn<'t>),
}

#[derive(Debug, Copy, Clone)]
pub struct Mod<'t> {
    pub id: TirId,
    pub name: &'t str,
    pub items: &'t [Item<'t>],
}

#[derive(Debug, Copy, Clone)]
pub struct Bounds<'t> {
    clauses: &'t [Clause<'t>],
}

#[derive(Debug, Copy, Clone)]
pub enum Clause<'t> {
    Bound(Binder<'t, &'t Clause<'t>>),
    AliasEq(TirId, GenArgs<'t>, &'t Ty<'t>),
    Trait(TirId, GenArgs<'t>),
    WellFormed(&'t Ty<'t>),
}
