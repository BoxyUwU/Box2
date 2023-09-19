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
        super_visit_variant_def(v, variant);
    }
}

pub fn super_visit_variant_def<'t, V: Visitor<'t>>(v: &mut V, def: &Variant<'t>) {
    for field in def.fields {
        super_visit_field_def(v, field);
    }

    for ty in def.adts {
        super_visit_type_def(v, ty);
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
}
pub trait TypeFolder<'t> {
    fn tcx(&self) -> &'t TirCtx<'t>;
    fn fold_ty(&mut self, ty: &'t Ty<'t>) -> &'t Ty<'t>;
}

pub trait TypeVisitable<'t>: Sized {
    fn visit_with<V: TypeVisitor<'t>>(self, v: &mut V);
}
pub trait TypeSuperVisitable<'t>: TypeVisitable<'t> {
    fn super_visit_with<V: TypeVisitor<'t>>(self, v: &mut V);
}
pub trait TypeFoldable<'t>: Sized {
    fn fold_with<V: TypeFolder<'t>>(self, v: &mut V) -> Self;
}
pub trait TypeSuperFoldable<'t>: TypeFoldable<'t> {
    fn super_fold_with<V: TypeFolder<'t>>(self, v: &mut V) -> Self;
}

impl<'t> TypeVisitable<'t> for &'t Ty<'t> {
    fn visit_with<V: TypeVisitor<'t>>(self, v: &mut V) {
        v.visit_ty(self);
    }
}
impl<'t> TypeSuperVisitable<'t> for &'t Ty<'t> {
    fn super_visit_with<V: TypeVisitor<'t>>(self, v: &mut V) {
        match self {
            Ty::Unit
            | Ty::Infer(_)
            | Ty::Bound(_, _)
            | Ty::Placeholder(_, _)
            | Ty::Int
            | Ty::Float
            | Ty::Error => (),
            Ty::Adt(_, args) => args.visit_with(v),
        }
    }
}
impl<'t> TypeFoldable<'t> for &'t Ty<'t> {
    fn fold_with<V: TypeFolder<'t>>(self, v: &mut V) -> Self {
        v.fold_ty(self)
    }
}
impl<'t> TypeSuperFoldable<'t> for &'t Ty<'t> {
    fn super_fold_with<V: TypeFolder<'t>>(self, v: &mut V) -> Self {
        match self {
            Ty::Unit
            | Ty::Infer(_)
            | Ty::Bound(_, _)
            | Ty::Placeholder(_, _)
            | Ty::Int
            | Ty::Float
            | Ty::Error => self,
            Ty::Adt(id, args) => v.tcx().arena.alloc(Ty::Adt(*id, args.fold_with(v))),
        }
    }
}

impl<'t> TypeVisitable<'t> for GenArgs<'t> {
    fn visit_with<V: TypeVisitor<'t>>(self, v: &mut V) {
        for arg in self.0 {
            arg.visit_with(v);
        }
    }
}
impl<'t> TypeFoldable<'t> for GenArgs<'t> {
    fn fold_with<V: TypeFolder<'t>>(self, v: &mut V) -> Self {
        GenArgs(
            v.tcx()
                .arena
                .alloc_slice_fill_iter(self.0.iter().map(|&arg| arg.fold_with(v))),
        )
    }
}

impl<'t> TypeVisitable<'t> for GenArg<'t> {
    fn visit_with<V: TypeVisitor<'t>>(self, v: &mut V) {
        match self {
            GenArg::Ty(ty) => v.visit_ty(ty),
        }
    }
}
impl<'t> TypeFoldable<'t> for GenArg<'t> {
    fn fold_with<V: TypeFolder<'t>>(self, v: &mut V) -> Self {
        match self {
            GenArg::Ty(ty) => GenArg::Ty(v.fold_ty(ty)),
        }
    }
}
