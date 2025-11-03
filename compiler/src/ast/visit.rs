use super::*;

pub trait Visitor<'ast>: Sized {
    #![allow(unused_variables)]

    fn visit_term(&mut self, term: &'ast Term<'ast>) {}

    fn visit_mod(&mut self, module: &'ast Module<'ast>) {
        super_visit_mod(self, module)
    }
    fn visit_type_def(&mut self, def: &'ast TypeDef<'ast>) {
        super_visit_type_def(self, def)
    }
    fn visit_variant_def(&mut self, def: &'ast VariantDef<'ast>) {
        super_visit_variant_def(self, def)
    }
    fn visit_field_def(&mut self, def: &'ast FieldDef<'ast>) {
        super_visit_field_def(self, def)
    }
    fn visit_type_alias(&mut self, alias: &'ast TypeAlias<'ast>) {
        super_visit_type_alias(self, alias)
    }
    fn visit_fn(&mut self, func: &'ast Fn<'ast>) {
        super_visit_fn(self, func)
    }
    fn visit_use(&mut self, u: &'ast Use<'ast>) {
        super_visit_use(self, u)
    }
    fn visit_trait(&mut self, trait_: &'ast Trait<'ast>) {
        super_visit_trait(self, trait_)
    }
    fn visit_impl(&mut self, impl_: &'ast Impl<'ast>) {
        super_visit_impl(self, impl_)
    }

    fn visit_bounds(&mut self, bounds: &'ast Bounds<'ast>) {
        super_visit_bounds(self, bounds)
    }
}

pub fn super_visit_item<'ast, V: Visitor<'ast>>(v: &mut V, item: &'ast Item<'ast>) {
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

pub fn super_visit_mod<'ast, V: Visitor<'ast>>(v: &mut V, module: &'ast Module<'ast>) {
    for i in module.items {
        super_visit_item(v, i);
    }
}

pub fn super_visit_type_def<'ast, V: Visitor<'ast>>(v: &mut V, def: &'ast TypeDef<'ast>) {
    for variant in def.variants {
        v.visit_variant_def(variant);
    }
}

pub fn super_visit_variant_def<'ast, V: Visitor<'ast>>(v: &mut V, def: &VariantDef<'ast>) {
    for field in def.field_defs {
        v.visit_field_def(field);
    }

    for ty in def.type_defs {
        v.visit_type_def(ty);
    }
}

pub fn super_visit_field_def<'ast, V: Visitor<'ast>>(_v: &mut V, _def: &'ast FieldDef<'ast>) {}

pub fn super_visit_type_alias<'ast, V: Visitor<'ast>>(v: &mut V, alias: &'ast TypeAlias<'ast>) {
    v.visit_bounds(&alias.bounds)
}

pub fn super_visit_fn<'ast, V: Visitor<'ast>>(v: &mut V, func: &'ast Fn<'ast>) {
    v.visit_bounds(&func.bounds);
    if let Some(term) = func.body {
        v.visit_term(term);
    }
}

pub fn super_visit_use<'ast, V: Visitor<'ast>>(_v: &mut V, _u: &'ast Use<'ast>) {}

pub fn super_visit_assoc_item<'ast, V: Visitor<'ast>>(
    v: &mut V,
    assoc_item: &'ast AssocItem<'ast>,
) {
    match assoc_item {
        AssocItem::Fn(f) => v.visit_fn(f),
        AssocItem::Type(t) => v.visit_type_alias(t),
    }
}

pub fn super_visit_trait<'ast, V: Visitor<'ast>>(v: &mut V, trait_: &'ast Trait<'ast>) {
    v.visit_bounds(&trait_.bounds);
    for assoc_item in trait_.assoc_items {
        super_visit_assoc_item(v, assoc_item)
    }
}

pub fn super_visit_impl<'ast, V: Visitor<'ast>>(v: &mut V, impl_: &'ast Impl<'ast>) {
    v.visit_bounds(&impl_.bounds);
    for assoc_item in impl_.assoc_items {
        super_visit_assoc_item(v, assoc_item)
    }
}

pub fn super_visit_bounds<'ast, V: Visitor<'ast>>(_v: &mut V, _bounds: &'ast Bounds<'ast>) {
    // lol
}
