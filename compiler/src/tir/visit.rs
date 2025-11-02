use crate::solve::{GoalKind, Response, VarValues};

use super::*;

pub trait Visitor<'t>: Sized {
    #![allow(unused_variables)]

    fn visit_term(&mut self, term: &Term<'t>) {}

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

pub trait TermVisitor<'t> {
    fn visit_term(&mut self, t: &'t Term<'t>);
    fn visit_binder<T: TermVisitable<'t>>(&mut self, binder: Binder<'t, T>);
}
pub trait TermFolder<'t>: FallibleTermFolder<'t, Error = core::convert::Infallible> {
    fn tcx(&self) -> &'t TirCtx<'t>;
    fn fold_term(&mut self, term: &'t Term<'t>) -> &'t Term<'t>;
    fn fold_binder<T: TermFoldable<'t>>(&mut self, binder: Binder<'t, T>) -> Binder<'t, T>;
}
pub trait FallibleTermFolder<'t> {
    type Error;
    fn tcx(&self) -> &'t TirCtx<'t>;
    fn try_fold_term(&mut self, t: &'t Term<'t>) -> Result<&'t Term<'t>, Self::Error>;
    fn try_fold_binder<T: TermFoldable<'t>>(
        &mut self,
        binder: Binder<'t, T>,
    ) -> Result<Binder<'t, T>, Self::Error>;
}

impl<'t, F: TermFolder<'t>> FallibleTermFolder<'t> for F {
    type Error = core::convert::Infallible;

    fn tcx(&self) -> &'t TirCtx<'t> {
        TermFolder::tcx(self)
    }

    fn try_fold_term(&mut self, t: &'t Term<'t>) -> Result<&'t Term<'t>, Self::Error> {
        Ok(TermFolder::fold_term(self, t))
    }

    fn try_fold_binder<T: TermFoldable<'t>>(
        &mut self,
        binder: Binder<'t, T>,
    ) -> Result<Binder<'t, T>, Self::Error> {
        Ok(TermFolder::fold_binder(self, binder))
    }
}

pub trait TermVisitable<'t>: Sized {
    fn visit_with<V: TermVisitor<'t>>(&self, v: &mut V);
}
pub trait TermSuperVisitable<'t>: TermVisitable<'t> {
    fn super_visit_with<V: TermVisitor<'t>>(&self, v: &mut V);
}
pub trait TermFoldable<'t>: Sized {
    fn try_fold_with<V: FallibleTermFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error>;
    fn fold_with<V: TermFolder<'t>>(self, v: &mut V) -> Self {
        self.try_fold_with(v).unwrap()
    }
}
pub trait TermSuperFoldable<'t>: TermFoldable<'t> {
    fn try_super_fold_with<V: FallibleTermFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error>;
    fn super_fold_with<V: TermFolder<'t>>(self, v: &mut V) -> Self {
        self.try_super_fold_with(v).unwrap()
    }
}

impl<'t> TermVisitable<'t> for &'t Term<'t> {
    fn visit_with<V: TermVisitor<'t>>(&self, v: &mut V) {
        v.visit_term(self);
    }
}
impl<'t> TermSuperVisitable<'t> for &'t Term<'t> {
    fn super_visit_with<V: TermVisitor<'t>>(&self, v: &mut V) {
        match self {
            Term::Unit
            | Term::Infer(_)
            | Term::Bound(_, _)
            | Term::Placeholder(_, _)
            | Term::IntTy
            | Term::FloatTy
            | Term::Error => (),
            Term::Alias(_, args) | Term::FnDef(_, args) | Term::Adt(_, args) => args.visit_with(v),
            _ => todo!(),
        }
    }
}
impl<'t> TermFoldable<'t> for &'t Term<'t> {
    fn try_fold_with<V: FallibleTermFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
        v.try_fold_term(self)
    }
}
impl<'t> TermSuperFoldable<'t> for &'t Term<'t> {
    fn try_super_fold_with<V: FallibleTermFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
        Ok(match self {
            Term::Unit
            | Term::Infer(_)
            | Term::Bound(_, _)
            | Term::Placeholder(_, _)
            | Term::IntTy
            | Term::FloatTy
            | Term::Error => self,

            Term::Alias(id, args) => v
                .tcx()
                .arena
                .alloc(Term::Alias(*id, args.try_fold_with(v)?)),
            Term::FnDef(id, args) => v
                .tcx()
                .arena
                .alloc(Term::FnDef(*id, args.try_fold_with(v)?)),
            Term::Adt(id, args) => v.tcx().arena.alloc(Term::Adt(*id, args.try_fold_with(v)?)),

            _ => todo!(),
        })
    }
}

impl<'t> TermVisitable<'t> for GenArgs<'t> {
    fn visit_with<V: TermVisitor<'t>>(&self, v: &mut V) {
        for arg in self.0 {
            arg.visit_with(v);
        }
    }
}
impl<'t> TermFoldable<'t> for GenArgs<'t> {
    fn try_fold_with<V: FallibleTermFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
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

impl<'t> TermVisitable<'t> for Clause<'t> {
    fn visit_with<V: TermVisitor<'t>>(&self, v: &mut V) {
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
impl<'t> TermFoldable<'t> for Clause<'t> {
    fn try_fold_with<V: FallibleTermFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
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

impl<'t> TermVisitable<'t> for Bounds<'t> {
    fn visit_with<V: TermVisitor<'t>>(&self, v: &mut V) {
        for clause in self.clauses {
            clause.visit_with(v);
        }
    }
}
impl<'t> TermFoldable<'t> for Bounds<'t> {
    fn try_fold_with<V: FallibleTermFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
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

impl<'t> TermVisitable<'t> for GoalKind<'t> {
    fn visit_with<V: TermVisitor<'t>>(&self, v: &mut V) {
        match self {
            GoalKind::WellFormed(ty) => ty.visit_with(v),
            GoalKind::StructurallyNorm(_id, args, ty) => {
                args.visit_with(v);
                ty.visit_with(v);
            }
            GoalKind::Equate(ty1, ty2) => {
                ty1.visit_with(v);
                ty2.visit_with(v);
            }
            GoalKind::Trait(_, args) => args.visit_with(v),
        }
    }
}

impl<'t> TermFoldable<'t> for GoalKind<'t> {
    fn try_fold_with<V: FallibleTermFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
        match self {
            GoalKind::WellFormed(ty) => Ok(GoalKind::WellFormed(ty.try_fold_with(v)?)),
            GoalKind::StructurallyNorm(id, args, ty) => Ok(GoalKind::StructurallyNorm(
                id,
                args.try_fold_with(v)?,
                ty.try_fold_with(v)?,
            )),
            GoalKind::Equate(ty1, ty2) => Ok(GoalKind::Equate(
                ty1.try_fold_with(v)?,
                ty2.try_fold_with(v)?,
            )),
            GoalKind::Trait(id, args) => Ok(GoalKind::Trait(id, args.try_fold_with(v)?)),
        }
    }
}

impl<'t> TermVisitable<'t> for VarValues<'t> {
    fn visit_with<V: TermVisitor<'t>>(&self, v: &mut V) {
        for ty in self.0 {
            ty.visit_with(v)
        }
    }
}

impl<'t> TermFoldable<'t> for VarValues<'t> {
    fn try_fold_with<V: FallibleTermFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
        let tys = self
            .0
            .iter()
            .map(|ty| ty.try_fold_with(v))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(VarValues(
            v.tcx().arena.alloc_slice_fill_iter(tys.into_iter()),
        ))
    }
}

impl<'t> TermVisitable<'t> for Response<'t> {
    fn visit_with<V: TermVisitor<'t>>(&self, v: &mut V) {
        self.var_values.visit_with(v)
    }
}

impl<'t> TermFoldable<'t> for Response<'t> {
    fn try_fold_with<V: FallibleTermFolder<'t>>(self, v: &mut V) -> Result<Self, V::Error> {
        Ok(Response {
            var_values: self.var_values.try_fold_with(v)?,
        })
    }
}

//
//

pub trait TermVisitableExt<'t> {
    fn references_err(&self) -> bool;
    fn has_escaping_bound_vars(&self) -> bool;
}

impl<'t, T: TermVisitable<'t>> TermVisitableExt<'t> for T {
    fn references_err(&self) -> bool {
        struct ErrVisitor(bool);

        impl<'t> TermVisitor<'t> for ErrVisitor {
            fn visit_term(&mut self, t: &'t Term<'t>) {
                match t {
                    Term::Error => {
                        self.0 = true;
                        return;
                    }
                    _ => t.super_visit_with(self),
                }
            }

            fn visit_binder<T: TermVisitable<'t>>(&mut self, binder: Binder<'t, T>) {
                binder.value.visit_with(self);
            }
        }

        let mut visitor = ErrVisitor(false);
        self.visit_with(&mut visitor);
        visitor.0
    }

    fn has_escaping_bound_vars(&self) -> bool {
        struct HasEscapingBoundVars {
            result: bool,
            escaping_level: DebruijnIndex,
        }

        impl<'t> TermVisitor<'t> for HasEscapingBoundVars {
            fn visit_term(&mut self, ty: &'t Term<'t>) {
                match ty {
                    Term::Bound(debruijn, _) if debruijn.0 >= self.escaping_level.0 => {
                        self.result = true;
                        return;
                    }
                    _ => ty.super_visit_with(self),
                }
            }

            fn visit_binder<T: TermVisitable<'t>>(&mut self, binder: Binder<'t, T>) {
                self.escaping_level.0 += 1;
                binder.skip_binder().visit_with(self);
                self.escaping_level.0 -= 1;
            }
        }

        let mut visitor = HasEscapingBoundVars {
            result: false,
            escaping_level: DebruijnIndex(0),
        };
        self.visit_with(&mut visitor);
        visitor.result
    }
}
