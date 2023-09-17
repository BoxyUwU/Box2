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
