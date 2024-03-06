use super::*;

pub trait Visitor<'t>: Sized {
    #![allow(unused_variables)]

    fn visit_expr(&mut self, expr: &Expr<'t>) {}

    fn visit_mod(&mut self, module: &Mod<'t>) {
        super_visit_mod(self, module)
    }
    fn visit_type_def(&mut self, def: &Adt<'t>) {
        super_visit_type_def(self, def)
    }
    fn visit_variant_def(&mut self, def: &Variant<'t>) {
        super_visit_variant_def(self, def)
    }
    fn visit_field_def(&mut self, def: &Field<'t>) {
        super_visit_field_def(self, def)
    }
    fn visit_type_alias(&mut self, alias: &TyAlias<'t>) {
        super_visit_type_alias(self, alias)
    }
    fn visit_fn(&mut self, func: &Fn<'t>) {
        super_visit_fn(self, func)
    }
    fn visit_trait(&mut self, trait_: &Trait<'t>) {
        super_visit_trait(self, trait_)
    }
    fn visit_impl(&mut self, impl_: &Impl<'t>) {
        super_visit_impl(self, impl_)
    }
}

pub fn super_visit_item<'t, V: Visitor<'t>>(v: &mut V, item: &Item<'t>) {
    match item {
        Item::Mod(m) => v.visit_mod(m),
        Item::Adt(t) => v.visit_type_def(t),
        Item::Variant(vrnt) => v.visit_variant_def(vrnt),
        Item::Field(f) => v.visit_field_def(f),
        Item::TyAlias(t) => v.visit_type_alias(t),
        Item::Fn(f) => v.visit_fn(f),
        Item::Trait(t) => v.visit_trait(t),
        Item::Impl(i) => v.visit_impl(i),
    }
}

pub fn super_visit_mod<'t, V: Visitor<'t>>(v: &mut V, module: &Mod<'t>) {
    for i in module.items {
        super_visit_item(v, i);
    }
}

pub fn super_visit_type_def<'t, V: Visitor<'t>>(v: &mut V, def: &Adt<'t>) {
    for variant in def.variants {
        v.visit_variant_def(variant);
    }
}

pub fn super_visit_variant_def<'t, V: Visitor<'t>>(v: &mut V, def: &Variant<'t>) {
    for field in def.fields {
        v.visit_field_def(field);
    }

    for ty in def.adts {
        v.visit_type_def(ty);
    }
}

pub fn super_visit_field_def<'t, V: Visitor<'t>>(_v: &mut V, _def: &Field<'t>) {}

pub fn super_visit_type_alias<'t, V: Visitor<'t>>(_v: &mut V, _alias: &TyAlias<'t>) {}

pub fn super_visit_fn<'t, V: Visitor<'t>>(_v: &mut V, _func: &Fn<'t>) {}

pub fn super_visit_assoc_item<'t, V: Visitor<'t>>(v: &mut V, assoc_item: &AssocItem<'t>) {
    match assoc_item {
        AssocItem::Fn(f) => v.visit_fn(f),
        AssocItem::TyAlias(t) => v.visit_type_alias(t),
    }
}

pub fn super_visit_trait<'t, V: Visitor<'t>>(v: &mut V, trait_: &Trait<'t>) {
    for assoc_item in trait_.assoc_items {
        super_visit_assoc_item(v, assoc_item)
    }
}

pub fn super_visit_impl<'t, V: Visitor<'t>>(v: &mut V, impl_: &Impl<'t>) {
    for assoc_item in impl_.assoc_items {
        super_visit_assoc_item(v, assoc_item)
    }
}

//
//

pub trait TypeVisitor<'t> {
    fn visit_ty(&mut self, ty: &'t Ty<'t>);
    fn visit_binder<T: TypeVisitable<'t>>(&mut self, binder: Binder<'t, T>);
}
pub trait TypeFolder<'t>: FallibleTypeFolder<'t, Error = core::convert::Infallible> {
    fn tcx(&self) -> &'t TirCtx<'t>;
    fn fold_ty(&mut self, ty: &'t Ty<'t>) -> &'t Ty<'t>;
    fn fold_binder<T: TypeFoldable<'t>>(&mut self, binder: Binder<'t, T>) -> Binder<'t, T>;
}
pub trait FallibleTypeFolder<'t> {
    type Error;
    fn tcx(&self) -> &'t TirCtx<'t>;
    fn try_fold_ty(&mut self, ty: &'t Ty<'t>) -> Result<&'t Ty<'t>, Self::Error>;
    fn try_fold_binder<T: TypeFoldable<'t>>(
        &mut self,
        binder: Binder<'t, T>,
    ) -> Result<Binder<'t, T>, Self::Error>;
}

impl<'t, F: TypeFolder<'t>> FallibleTypeFolder<'t> for F {
    type Error = core::convert::Infallible;

    fn tcx(&self) -> &'t TirCtx<'t> {
        TypeFolder::tcx(self)
    }

    fn try_fold_ty(&mut self, ty: &'t Ty<'t>) -> Result<&'t Ty<'t>, Self::Error> {
        Ok(TypeFolder::fold_ty(self, ty))
    }

    fn try_fold_binder<T: TypeFoldable<'t>>(
        &mut self,
        binder: Binder<'t, T>,
    ) -> Result<Binder<'t, T>, Self::Error> {
        Ok(TypeFolder::fold_binder(self, binder))
    }
}

pub trait TypeVisitable<'t>: Sized {
    fn visit_with<V: TypeVisitor<'t>>(&self, v: &mut V);
}
pub trait TypeSuperVisitable<'t>: TypeVisitable<'t> {
    fn super_visit_with<V: TypeVisitor<'t>>(&self, v: &mut V);
}
pub trait TypeFoldable<'t>: Sized {
    fn try_fold_with<V: FallibleTypeFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error>;
    fn fold_with<V: TypeFolder<'t>>(self, v: &mut V) -> Self {
        self.try_fold_with(v).unwrap()
    }
}
pub trait TypeSuperFoldable<'t>: TypeFoldable<'t> {
    fn try_super_fold_with<V: FallibleTypeFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error>;
    fn super_fold_with<V: TypeFolder<'t>>(self, v: &mut V) -> Self {
        self.try_super_fold_with(v).unwrap()
    }
}

impl<'t> TypeVisitable<'t> for &'t Ty<'t> {
    fn visit_with<V: TypeVisitor<'t>>(&self, v: &mut V) {
        v.visit_ty(self);
    }
}
impl<'t> TypeSuperVisitable<'t> for &'t Ty<'t> {
    fn super_visit_with<V: TypeVisitor<'t>>(&self, v: &mut V) {
        match self {
            Ty::Unit
            | Ty::Infer(_)
            | Ty::Bound(_, _)
            | Ty::Placeholder(_, _)
            | Ty::Int
            | Ty::Float
            | Ty::Error => (),
            Ty::Alias(_, args) | Ty::FnDef(_, args) | Ty::Adt(_, args) => args.visit_with(v),
        }
    }
}
impl<'t> TypeFoldable<'t> for &'t Ty<'t> {
    fn try_fold_with<V: FallibleTypeFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
        v.try_fold_ty(self)
    }
}
impl<'t> TypeSuperFoldable<'t> for &'t Ty<'t> {
    fn try_super_fold_with<V: FallibleTypeFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
        Ok(match self {
            Ty::Unit
            | Ty::Infer(_)
            | Ty::Bound(_, _)
            | Ty::Placeholder(_, _)
            | Ty::Int
            | Ty::Float
            | Ty::Error => self,

            Ty::Alias(id, args) => v.tcx().arena.alloc(Ty::Alias(*id, args.try_fold_with(v)?)),
            Ty::FnDef(id, args) => v.tcx().arena.alloc(Ty::FnDef(*id, args.try_fold_with(v)?)),
            Ty::Adt(id, args) => v.tcx().arena.alloc(Ty::Adt(*id, args.try_fold_with(v)?)),
        })
    }
}

impl<'t> TypeVisitable<'t> for GenArgs<'t> {
    fn visit_with<V: TypeVisitor<'t>>(&self, v: &mut V) {
        for arg in self.0 {
            arg.visit_with(v);
        }
    }
}
impl<'t> TypeFoldable<'t> for GenArgs<'t> {
    fn try_fold_with<V: FallibleTypeFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
        Ok(GenArgs(
            v.tcx().arena.alloc_slice_fill_iter(
                self.0
                    .iter()
                    .map(|&arg| arg.try_fold_with(v))
                    .collect::<Result<Vec<_>, V::Error>>()?,
            ),
        ))
    }
}

impl<'t> TypeVisitable<'t> for GenArg<'t> {
    fn visit_with<V: TypeVisitor<'t>>(&self, v: &mut V) {
        match self {
            GenArg::Ty(ty) => v.visit_ty(ty),
        }
    }
}
impl<'t> TypeFoldable<'t> for GenArg<'t> {
    fn try_fold_with<V: FallibleTypeFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
        match self {
            GenArg::Ty(ty) => Ok(GenArg::Ty(v.try_fold_ty(ty)?)),
        }
    }
}

impl<'t> TypeVisitable<'t> for Clause<'t> {
    fn visit_with<V: TypeVisitor<'t>>(&self, v: &mut V) {
        match self {
            Clause::Bound(binder) => binder.value.visit_with(v),
            Clause::AliasEq(_, args, ty) => {
                args.visit_with(v);
                ty.visit_with(v);
            }
            Clause::Trait(_, args) => {
                args.visit_with(v);
            }
            Clause::WellFormed(ty) => {
                ty.visit_with(v);
            }
        }
    }
}
impl<'t> TypeFoldable<'t> for Clause<'t> {
    fn try_fold_with<V: FallibleTypeFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
        Ok(match self {
            Clause::Bound(binder) => Clause::Bound(Binder {
                value: v.tcx().arena.alloc(binder.value.try_fold_with(v)?),
                vars: binder.vars,
            }),
            Clause::AliasEq(id, args, ty) => {
                Clause::AliasEq(id, args.try_fold_with(v)?, ty.try_fold_with(v)?)
            }
            Clause::Trait(id, args) => Clause::Trait(id, args.try_fold_with(v)?),
            Clause::WellFormed(ty) => Clause::WellFormed(ty.try_fold_with(v)?),
        })
    }
}

impl<'t> TypeVisitable<'t> for Bounds<'t> {
    fn visit_with<V: TypeVisitor<'t>>(&self, v: &mut V) {
        for clause in self.clauses {
            clause.visit_with(v);
        }
    }
}
impl<'t> TypeFoldable<'t> for Bounds<'t> {
    fn try_fold_with<V: FallibleTypeFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
        Ok(Bounds {
            clauses: v.tcx().arena.alloc_slice_fill_iter(
                self.clauses
                    .iter()
                    .map(|clause| clause.try_fold_with(v))
                    .collect::<Result<Vec<_>, V::Error>>()?,
            ),
        })
    }
}

//
//

trait TypeVisitableExt<'t> {
    fn references_err(&self) -> bool;
}

impl<'t, T: TypeVisitable<'t>> TypeVisitableExt<'t> for T {
    fn references_err(&self) -> bool {
        struct ErrVisitor(bool);

        impl<'t> TypeVisitor<'t> for ErrVisitor {
            fn visit_ty(&mut self, ty: &'_ Ty<'_>) {
                match ty {
                    Ty::Unit
                    | Ty::Infer(_)
                    | Ty::Bound(_, _)
                    | Ty::Placeholder(_, _)
                    | Ty::Int
                    | Ty::Float => return,
                    Ty::Alias(_, args) | Ty::FnDef(_, args) | Ty::Adt(_, args) => {
                        args.visit_with(self)
                    }
                    Ty::Error => {
                        self.0 = true;
                        return;
                    }
                }
            }

            fn visit_binder<T: TypeVisitable<'t>>(&mut self, binder: Binder<'t, T>) {
                binder.value.visit_with(self);
            }
        }

        let mut visitor = ErrVisitor(false);
        self.visit_with(&mut visitor);
        visitor.0
    }
}
