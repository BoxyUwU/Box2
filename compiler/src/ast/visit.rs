use super::*;

pub trait Visitor: Sized {
    #![allow(unused_variables)]

    fn visit_expr(&mut self, expr: &Expr<'_>) {}

    fn visit_mod(&mut self, module: &Module<'_>) {
        super_visit_mod(self, module)
    }
    fn visit_type_def(&mut self, def: &TypeDef<'_>) {
        super_visit_type_def(self, def)
    }
    fn visit_variant_def(&mut self, def: &VariantDef<'_>) {
        super_visit_variant_def(self, def)
    }
    fn visit_field_def(&mut self, def: &FieldDef<'_>) {
        super_visit_field_def(self, def)
    }
    fn visit_type_alias(&mut self, alias: &TypeAlias<'_>) {
        super_visit_type_alias(self, alias)
    }
    fn visit_fn(&mut self, func: &Fn<'_>) {
        super_visit_fn(self, func)
    }
    fn visit_use(&mut self, u: &Use<'_>) {
        super_visit_use(self, u)
    }
    fn visit_trait(&mut self, trait_: &Trait<'_>) {
        super_visit_trait(self, trait_)
    }
    fn visit_impl(&mut self, impl_: &Impl<'_>) {
        super_visit_impl(self, impl_)
    }

    fn visit_bounds(&mut self, bounds: &Bounds<'_>) {
        super_visit_bounds(self, bounds)
    }
}

pub fn super_visit_item<V: Visitor>(v: &mut V, item: &Item<'_>) {
    match item {
        Item::Mod(m) => v.visit_mod(m),
        Item::TypeDef(t) => v.visit_type_def(t),
        Item::VariantDef(variant) => v.visit_variant_def(variant),
        Item::FieldDef(f) => v.visit_field_def(f),
        Item::TypeAlias(t) => v.visit_type_alias(t),
        Item::Fn(f) => v.visit_fn(f),
        Item::Use(u) => v.visit_use(u),
        Item::Trait(t) => v.visit_trait(t),
        Item::Impl(i) => v.visit_impl(i),
    }
}

pub fn super_visit_mod<V: Visitor>(v: &mut V, module: &Module<'_>) {
    for i in module.items {
        super_visit_item(v, i);
    }
}

pub fn super_visit_type_def<V: Visitor>(v: &mut V, def: &TypeDef<'_>) {
    for variant in def.variants {
        v.visit_variant_def(variant);
    }
}

pub fn super_visit_variant_def<V: Visitor>(v: &mut V, def: &VariantDef<'_>) {
    for field in def.field_defs {
        v.visit_field_def(field);
    }

    for ty in def.type_defs {
        v.visit_type_def(ty);
    }
}

pub fn super_visit_field_def<V: Visitor>(_v: &mut V, _def: &FieldDef<'_>) {}

pub fn super_visit_type_alias<V: Visitor>(v: &mut V, alias: &TypeAlias<'_>) {
    v.visit_bounds(&alias.bounds)
}

pub fn super_visit_fn<V: Visitor>(v: &mut V, func: &Fn<'_>) {
    v.visit_bounds(&func.bounds);
    if let Some(expr) = func.body {
        v.visit_expr(expr);
    }
}

pub fn super_visit_use<V: Visitor>(_v: &mut V, _u: &Use<'_>) {}

pub fn super_visit_assoc_item<V: Visitor>(v: &mut V, assoc_item: &AssocItem<'_>) {
    match assoc_item {
        AssocItem::Fn(f) => v.visit_fn(f),
        AssocItem::Type(t) => v.visit_type_alias(t),
    }
}

pub fn super_visit_trait<V: Visitor>(v: &mut V, trait_: &Trait<'_>) {
    v.visit_bounds(&trait_.bounds);
    for assoc_item in trait_.assoc_items {
        super_visit_assoc_item(v, assoc_item)
    }
}

pub fn super_visit_impl<V: Visitor>(v: &mut V, impl_: &Impl<'_>) {
    v.visit_bounds(&impl_.bounds);
    for assoc_item in impl_.assoc_items {
        super_visit_assoc_item(v, assoc_item)
    }
}

pub fn super_visit_bounds<V: Visitor>(_v: &mut V, _bounds: &Bounds<'_>) {
    // lol
}
