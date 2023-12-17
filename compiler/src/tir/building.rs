use std::collections::HashMap;

use codespan_reporting::diagnostic::Label;

use crate::ast::visit::Visitor;
use crate::ast::{self, NodeId, Nodes};
use crate::resolve::DefKind;
use crate::typeck::InferCtxt;

use super::super::tir;
use super::*;

fn diag_gen_args_provided_when_shouldnt(span: Span) -> Diagnostic<usize> {
    Diagnostic::error()
        .with_message(&format!("unexpected generic args provided"))
        .with_labels(vec![
            Label::primary(0, span).with_message("args provided here")
        ])
}

fn diag_wrong_gen_args_count(span: Span, expected_count: usize) -> Diagnostic<usize> {
    Diagnostic::error()
        .with_message(&format!("unexpected amount of generic args provided"))
        .with_labels(vec![
            Label::primary(0, span).with_message(&format!("Expected {expected_count} args"))
        ])
}

fn diag_infer_var_in_signature(span: Span) -> Diagnostic<usize> {
    Diagnostic::error()
        .with_message(&format!(
            "inferring types is not allowed in item signatures"
        ))
        .with_labels(vec![Label::primary(0, span)])
}

pub struct ItemTirBuilder<'t> {
    empty_tir: &'t TirCtx<'t>,
    next_tir_id: TirId,
    next_body_id: BodyId,

    generics: HashMap<TirId, &'t Generics<'t>>,
    lowered_ids: HashMap<NodeId, TirId>,
    bodies: HashMap<NodeId, (TirId, Vec<NodeId>, BodyId)>,
}
impl<'t> ItemTirBuilder<'t> {
    pub fn get_body_id(&self, id: NodeId) -> Option<BodyId> {
        self.bodies.get(&id).map(|(_, _, id)| *id)
    }

    pub fn get_generics(&self, id: TirId) -> &'t Generics<'t> {
        self.generics[&id]
    }

    pub fn register_item(&self, id: TirId, item: &'t Item<'t>) {
        let mut items = self.empty_tir.items.borrow_mut();
        let prev_inserted = items.insert(id, item);
        assert!(prev_inserted.is_none());
    }

    pub fn new_body_id(&mut self, owner: TirId, ast_inputs: Vec<NodeId>, expr: NodeId) -> BodyId {
        let body_id = self.next_body_id.clone();
        self.next_body_id.0 += 1;
        let inserted_already = self.bodies.insert(expr, (owner, ast_inputs, body_id));
        assert!(inserted_already.is_none());
        body_id
    }

    pub fn new_lowered_tir_id(&mut self, id: NodeId) -> TirId {
        let tir_id = self.new_tir_id();
        let inserted_already = self.lowered_ids.insert(id, tir_id);
        assert!(inserted_already.is_none());
        tir_id
    }

    pub fn new_tir_id(&mut self) -> TirId {
        let tir_id = self.next_tir_id.clone();
        self.next_tir_id.0 += 1;
        tir_id
    }
}

pub struct BodyTirBuilder<'t> {
    pub partial_tir: &'t TirCtx<'t>,
    pub lowered_ids: HashMap<NodeId, TirId>,
    pub infcx: InferCtxt<'t>,
}

pub trait TirBuilder<'t> {
    fn arena(&self) -> &'t Bump;
    fn get_id(&self, id: NodeId) -> Option<TirId>;
    fn get_generics(&self, id: TirId) -> &'t Generics<'t>;
    fn get_item(&self, id: TirId) -> &'t Item<'t>;
    fn err(&self, err: Diagnostic<usize>);

    fn allow_infers(&self) -> bool;
    fn ty_infer(&mut self, span: Span) -> &'t Ty<'t>;
}
impl<'t> TirBuilder<'t> for ItemTirBuilder<'t> {
    fn arena(&self) -> &'t Bump {
        &self.empty_tir.arena
    }

    fn get_id(&self, id: NodeId) -> Option<TirId> {
        self.lowered_ids.get(&id).copied()
    }

    fn get_generics(&self, id: TirId) -> &'t Generics<'t> {
        self.get_generics(id)
    }

    fn get_item(&self, id: TirId) -> &'t Item<'t> {
        self.empty_tir.items.borrow().get(&id).unwrap()
    }

    fn err(&self, err: Diagnostic<usize>) {
        self.empty_tir.err(err)
    }

    fn allow_infers(&self) -> bool {
        false
    }

    fn ty_infer(&mut self, _: Span) -> &'t Ty<'t> {
        unreachable!("cannot create infer vars in `ItemTirBuilder`");
    }
}
impl<'t> TirBuilder<'t> for BodyTirBuilder<'t> {
    fn arena(&self) -> &'t Bump {
        &self.partial_tir.arena
    }

    fn get_id(&self, id: NodeId) -> Option<TirId> {
        self.lowered_ids.get(&id).copied()
    }

    fn get_generics(&self, id: TirId) -> &'t Generics<'t> {
        match self.partial_tir.items.borrow().get(&id).unwrap() {
            Item::Mod(_) | Item::Variant(_) | Item::Field(_) => panic!("no generics on item"),

            Item::Fn(f) => f.generics,
            Item::Adt(a) => a.generics,
            Item::TyAlias(t) => t.generics,
            Item::Trait(t) => t.generics,
            Item::Impl(i) => i.generics,
        }
    }

    fn get_item(&self, id: TirId) -> &'t Item<'t> {
        self.partial_tir.items.borrow().get(&id).unwrap()
    }

    fn err(&self, err: Diagnostic<usize>) {
        self.partial_tir.err(err)
    }

    fn allow_infers(&self) -> bool {
        true
    }

    fn ty_infer(&mut self, span: Span) -> &'t Ty<'t> {
        let infer_id = self.infcx.new_var(span);
        self.arena().alloc(Ty::Infer(infer_id))
    }
}

pub fn build<'a, 't>(
    ast: &'a Nodes<'a>,
    root: NodeId,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    empty_tir: &'t TirCtx<'t>,
) -> (
    &'t Mod<'t>,
    HashMap<BodyId, BodySource<'t>>,
    &'t TirCtx<'t>,
    HashMap<NodeId, TirId>,
) {
    struct EarlyTirBuild<'t> {
        tir_builder: ItemTirBuilder<'t>,

        generics_stack: Vec<&'t Generics<'t>>,
    }

    impl<'t> EarlyTirBuild<'t> {
        fn push_generics(&mut self, id: TirId, generics: &ast::Generics<'_>) {
            for param in generics.params {
                self.tir_builder.new_lowered_tir_id(param.id);
            }
            let generics = build_generics(
                *generics,
                id,
                &mut self.tir_builder,
                self.generics_stack.last().copied(),
            );
            self.generics_stack.push(generics);
            self.tir_builder.generics.insert(id, generics);
        }
        fn pop_generics(&mut self) {
            self.generics_stack
                .pop()
                .expect("popping generics when nothing is on stack");
        }
    }
    impl<'t> ast::visit::Visitor for EarlyTirBuild<'t> {
        fn visit_mod(&mut self, module: &ast::Module<'_>) {
            self.tir_builder.new_lowered_tir_id(module.id);
            ast::visit::super_visit_mod(self, module)
        }

        fn visit_type_def(&mut self, def: &ast::TypeDef<'_>) {
            let id = self.tir_builder.new_lowered_tir_id(def.id);
            self.push_generics(id, &def.generics);
            ast::visit::super_visit_type_def(self, def);
            self.pop_generics();
        }

        fn visit_variant_def(&mut self, def: &ast::VariantDef<'_>) {
            self.tir_builder.new_lowered_tir_id(def.id);
            ast::visit::super_visit_variant_def(self, def);
        }

        fn visit_field_def(&mut self, def: &ast::FieldDef<'_>) {
            self.tir_builder.new_lowered_tir_id(def.id);
            ast::visit::super_visit_field_def(self, def);
        }

        fn visit_type_alias(&mut self, alias: &ast::TypeAlias<'_>) {
            let id = self.tir_builder.new_lowered_tir_id(alias.id);
            self.push_generics(id, &alias.generics);
            ast::visit::super_visit_type_alias(self, alias);
            self.pop_generics();
        }

        fn visit_fn(&mut self, func: &ast::Fn<'_>) {
            let owner = self.tir_builder.new_lowered_tir_id(func.id);
            self.push_generics(owner, &func.generics);

            if let Some(body) = func.body {
                self.tir_builder.new_body_id(
                    owner,
                    func.params.iter().map(|param| param.id).collect::<Vec<_>>(),
                    body.id,
                );
            }

            ast::visit::super_visit_fn(self, func);
            self.pop_generics();
        }

        fn visit_trait(&mut self, trait_: &ast::Trait<'_>) {
            let id = self.tir_builder.new_lowered_tir_id(trait_.id);
            self.push_generics(id, &trait_.generics);
            ast::visit::super_visit_trait(self, trait_);
            self.pop_generics();
        }

        fn visit_impl(&mut self, impl_: &ast::Impl<'_>) {
            let id = self.tir_builder.new_lowered_tir_id(impl_.id);
            self.push_generics(id, &impl_.generics);
            ast::visit::super_visit_impl(self, impl_);
            self.pop_generics();
        }
    }

    let module = ast.get(root).unwrap_mod();

    let tir_builder = ItemTirBuilder {
        empty_tir,
        next_tir_id: TirId(0),
        next_body_id: BodyId(0),

        generics: HashMap::new(),
        lowered_ids: HashMap::new(),
        bodies: HashMap::new(),
    };
    let mut early_builder = EarlyTirBuild {
        tir_builder,
        generics_stack: vec![],
    };
    early_builder.visit_mod(module);
    let mut tir_builder = early_builder.tir_builder;

    let module = build_mod(ast, module, resolutions, &mut tir_builder);

    let body_sources = std::mem::take(&mut tir_builder.bodies)
        .into_iter()
        .map(|(expr_id, (owner, params, body_id))| {
            let item = tir_builder.empty_tir.get_item(owner);
            let (params, ret_ty) = match item {
                Item::Fn(func) => (
                    empty_tir.arena.alloc_slice_fill_iter(
                        func.params
                            .iter()
                            .zip(params.iter())
                            .map(|(param, node_id)| (*node_id, param.ty)),
                    ),
                    func.ret_ty,
                ),

                Item::Variant(_)
                | Item::Field(_)
                | Item::Mod(_)
                | Item::Adt(_)
                | Item::TyAlias(_)
                | Item::Trait(_)
                | Item::Impl(_) => {
                    unreachable!()
                }
            };
            (
                body_id,
                BodySource {
                    expr: expr_id,
                    ret: ret_ty,
                    params,
                },
            )
        })
        .collect::<HashMap<_, _>>();

    (
        module,
        body_sources,
        tir_builder.empty_tir,
        tir_builder.lowered_ids,
    )
}

pub fn build_ty<'t>(
    ty: &ast::Ty,
    tcx: &mut impl TirBuilder<'t>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    item_generics: &Generics<'t>,
) -> EarlyBinder<&'t Ty<'t>> {
    match ty.kind {
        ast::TyKind::Infer => match tcx.allow_infers() {
            true => EarlyBinder(tcx.ty_infer(ty.span)),
            false => {
                tcx.err(diag_infer_var_in_signature(ty.span));
                EarlyBinder(&Ty::Error)
            }
        },
        ast::TyKind::Path(path) => {
            let (_, args) = build_args_for_path(&path, tcx, resolutions, item_generics);
            match resolutions[&ty.id] {
                Res::Def(DefKind::Adt, id) => {
                    let tir_id = tcx.get_id(id).unwrap();
                    EarlyBinder(tcx.arena().alloc(Ty::Adt(tir_id, args.skip_binder())))
                }
                Res::Def(DefKind::GenericParam, id) => {
                    let tir_id = tcx.get_id(id).unwrap();
                    let var_idx = item_generics.param_id_to_var[&tir_id];
                    EarlyBinder(
                        tcx.arena()
                            .alloc(Ty::Bound(DebruijnIndex(0), BoundVar(var_idx))),
                    )
                }
                Res::Def(_, _) | Res::Local(_) => unreachable!(),
            }
        }
    }
}

pub fn build_args_for_path<'t>(
    path: &ast::Path<'_>,
    tcx: &mut impl TirBuilder<'t>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    generics: &Generics<'t>,
) -> (TirId, EarlyBinder<GenArgs<'t>>) {
    let mut args = vec![];

    for seg in path.segments {
        let seg = build_path_seg(**seg, tcx, resolutions, generics);
        args.extend(seg.skip_binder().args.0.into_iter().map(|arg| *arg));
    }

    let (Res::Def(_, id) | Res::Local(id)) = resolutions[&path.segments.last().unwrap().id];

    (
        tcx.get_id(id).unwrap(),
        EarlyBinder(GenArgs(tcx.arena().alloc_slice_fill_iter(args))),
    )
}

pub fn build_path_seg<'t, T: TirBuilder<'t>>(
    seg: ast::PathSeg<'_>,
    tcx: &mut T,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    generics: &Generics<'t>,
) -> EarlyBinder<&'t PathSeg<'t>> {
    let lower_args = |tcx: &mut T, args: ast::GenArgs<'_>| {
        GenArgs(
            tcx.arena()
                .alloc_slice_fill_iter(args.0.iter().map(|arg| match arg {
                    ast::GenArg::Ty(ty) => {
                        GenArg::Ty(build_ty(ty, tcx, resolutions, generics).skip_binder())
                    }
                })),
        )
    };

    let res = resolutions[&seg.id].map_id(|id| tcx.get_id(id).unwrap());
    let seg = match res {
        Res::Def(DefKind::TypeAlias | DefKind::Adt | DefKind::Func | DefKind::Trait, _) => {
            let args = lower_args(tcx, seg.args);
            let (Res::Def(_, id) | Res::Local(id)) = res;
            let generics = tcx.get_generics(id);

            if args.0.len() != generics.params.len() {
                tcx.err(diag_wrong_gen_args_count(seg.span, generics.params.len()));
                PathSeg {
                    args: GenArgs(tcx.arena().alloc_slice_fill_iter(
                        (0..generics.params.len()).map(|_| GenArg::Ty(&Ty::Error)),
                    )),
                    res,
                }
            } else {
                PathSeg { args, res }
            }
        }
        Res::Def(DefKind::GenericParam | DefKind::Mod | DefKind::Variant, _) => {
            if seg.args.0.len() > 0 {
                tcx.err(diag_gen_args_provided_when_shouldnt(seg.span));
            }

            PathSeg {
                args: GenArgs(&[]),
                res,
            }
        }
        Res::Def(DefKind::Field, _) => unreachable!("paths cant resolve to fields"),
        Res::Local(_) => panic!("no"),
    };
    EarlyBinder(tcx.arena().alloc(seg))
}

/// Not all ast items are present in Tir, if attempting to build tir for such an item kind
/// then `None` will be returned.
pub fn build_item<'a, 't>(
    ast: &'a Nodes<'a>,
    item: &ast::Item<'a>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    tir: &mut ItemTirBuilder<'t>,
) -> Option<&'t Item<'t>> {
    let item = match item {
        ast::Item::Mod(m) => Item::Mod(*build_mod(ast, m, resolutions, tir)),
        ast::Item::TypeDef(t) => Item::Adt(*build_adt_def(ast, t, resolutions, tir)),
        ast::Item::TypeAlias(a) => Item::TyAlias(*build_type_alias(ast, a, resolutions, tir)),
        ast::Item::Fn(f) => Item::Fn(*build_fn(ast, f, resolutions, tir)),
        ast::Item::Trait(t) => Item::Trait(*build_trait(ast, t, resolutions, tir)),
        ast::Item::Impl(i) => Item::Impl(*build_impl(ast, i, resolutions, tir)),

        ast::Item::Use(_) | ast::Item::VariantDef(_) | ast::Item::FieldDef(_) => return None,
    };
    let item = tir.empty_tir.arena.alloc(item);
    Some(&*item)
}

pub fn build_generics<'a, 't>(
    generics: ast::Generics<'a>,
    tir_item: TirId,
    tir: &mut ItemTirBuilder<'t>,
    parent_generics: Option<&'t Generics<'t>>,
) -> &'t tir::Generics<'t> {
    let parent_count = parent_generics
        .map(|generics| generics.parent_count + (generics.params.len() as u32))
        .unwrap_or(0);

    let params = generics.params.iter().enumerate().map(|(n, param)| {
        let param_id = tir.get_id(param.id).unwrap();
        tir::GenParam {
            id: param_id,
            kind: match param.kind {
                ast::GenericParamKind::Type => tir::GenParamKind::Ty,
            },
            name: tir.empty_tir.arena.alloc(param.name.to_string()),
            index: parent_count + (n as u32),
        }
    });
    let params = tir.empty_tir.arena.alloc_slice_fill_iter(params);

    let generics = tir::Generics {
        item: tir_item,
        parent: parent_generics.map(|generics| generics.item),
        params,
        parent_count,
        param_id_to_var: tir.empty_tir.arena.alloc(
            parent_generics
                .map(|generics| {
                    let mut generics = generics.param_id_to_var.clone();
                    generics.extend(params.iter().map(|param| (param.id, param.index)));
                    generics
                })
                .unwrap_or_else(|| {
                    params
                        .iter()
                        .map(|param| (param.id, param.index))
                        .collect::<HashMap<_, _>>()
                }),
        ),
    };
    tir.empty_tir.arena.alloc(generics)
}

pub fn build_mod<'a, 't>(
    ast: &'a Nodes<'a>,
    mod_: &ast::Module<'a>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    tir: &mut ItemTirBuilder<'t>,
) -> &'t Mod<'t> {
    let id = tir.get_id(mod_.id).unwrap();

    let items = tir.empty_tir.arena.alloc_slice_fill_iter(
        mod_.items
            .iter()
            .flat_map(|nested_item| build_item(ast, nested_item, resolutions, tir))
            .collect::<Vec<_>>()
            .into_iter()
            .copied(),
    );

    let tir_mod = tir::Mod {
        id,
        name: tir.empty_tir.arena.alloc(mod_.name.to_string()),
        items,
    };
    let tir_mod = tir.empty_tir.arena.alloc(tir_mod);
    tir.register_item(id, tir.empty_tir.arena.alloc(tir::Item::Mod(*tir_mod)));
    tir_mod
}

pub fn build_adt_def<'a, 't>(
    ast: &'a Nodes<'a>,
    adt: &ast::TypeDef<'a>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    tir: &mut ItemTirBuilder<'t>,
) -> &'t Adt<'t> {
    let id = tir.get_id(adt.id).unwrap();

    let generics = tir.get_generics(id);

    let variants = adt
        .variants
        .iter()
        .map(|variant| {
            let variant_id = tir.get_id(variant.id).unwrap();

            let adts = variant
                .type_defs
                .iter()
                .map(|type_def| build_adt_def(ast, type_def, resolutions, tir))
                .collect::<Vec<_>>()
                .into_iter();
            let adts = tir.empty_tir.arena.alloc_slice_fill_iter(adts);

            let fields = variant
                .field_defs
                .iter()
                .map(|field_def| {
                    let field_id = tir.get_id(field_def.id).unwrap();
                    let field = tir::Field {
                        id: field_id,
                        name: tir.empty_tir.arena.alloc(field_def.name.to_string()),
                        ty: build_ty(field_def.ty, tir, resolutions, &generics),
                    };
                    &*tir.empty_tir.arena.alloc(Item::Field(field))
                })
                .collect::<Vec<_>>();
            for f in fields.iter() {
                tir.register_item(f.unwrap_field().id, f);
            }
            let fields = tir
                .empty_tir
                .arena
                .alloc_slice_fill_iter(fields.into_iter().map(|item| item.unwrap_field()));

            let variant = tir::Variant {
                id: variant_id,
                name: variant
                    .name
                    .map(|name| tir.empty_tir.arena.alloc(name.to_string()).as_str()),
                adts,
                fields,
            };
            &*tir.empty_tir.arena.alloc(Item::Variant(variant))
        })
        .collect::<Vec<_>>();
    for v in variants.iter() {
        tir.register_item(v.unwrap_variant().id, v);
    }
    let variants = &*tir
        .empty_tir
        .arena
        .alloc_slice_fill_iter(variants.into_iter().map(|item| item.unwrap_variant()));

    let tir_adt = tir::Adt {
        id,
        name: tir.empty_tir.arena.alloc(adt.name.to_string()),
        generics,
        variants,
    };
    let tir_adt = tir.empty_tir.arena.alloc(tir_adt);
    tir.register_item(id, tir.empty_tir.arena.alloc(tir::Item::Adt(*tir_adt)));
    tir_adt
}

fn build_type_alias<'a, 't>(
    _ast: &'a Nodes<'a>,
    alias: &ast::TypeAlias<'a>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    tir: &mut ItemTirBuilder<'t>,
) -> &'t TyAlias<'t> {
    let id = tir.get_id(alias.id).unwrap();

    let generics = tir.get_generics(id);

    let tir_alias = tir::TyAlias {
        id,
        name: tir.empty_tir.arena.alloc(alias.name.to_string()),
        generics,
        ty: alias.ty.map(|ty| build_ty(ty, tir, resolutions, generics)),
    };
    let tir_alias = tir.empty_tir.arena.alloc(tir_alias);
    tir.register_item(
        id,
        tir.empty_tir.arena.alloc(tir::Item::TyAlias(*tir_alias)),
    );
    tir_alias
}

fn build_fn<'a, 't>(
    _ast: &'a Nodes<'a>,
    func: &ast::Fn<'a>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    tir: &mut ItemTirBuilder<'t>,
) -> &'t Fn<'t> {
    let id = tir.get_id(func.id).unwrap();
    let generics = tir.get_generics(id);

    let params = func
        .params
        .iter()
        .map(|param| tir::Param {
            ty: build_ty(param.ty.unwrap(), tir, resolutions, &generics),
            span: param.span,
        })
        .collect::<Vec<_>>()
        .into_iter();
    let params = tir.empty_tir.arena.alloc_slice_fill_iter(params);

    let tir_fn = tir::Fn {
        id,
        name: tir.empty_tir.arena.alloc(func.name.to_string()),
        generics,
        params,
        ret_ty: func
            .ret_ty
            .map(|ty| build_ty(ty, tir, resolutions, &generics))
            .unwrap_or_else(|| EarlyBinder(&*tir.empty_tir.arena.alloc(Ty::Unit))),
        body: func.body.map(|expr| {
            tir.get_body_id(expr.id)
                .expect("bodyids and tirids should have been pre generated before building tir")
        }),
    };
    let tir_fn = tir.empty_tir.arena.alloc(tir_fn);
    tir.register_item(id, tir.empty_tir.arena.alloc(tir::Item::Fn(*tir_fn)));
    tir_fn
}

fn build_trait<'a, 't>(
    ast: &'a Nodes<'a>,
    trait_: &ast::Trait<'a>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    tir: &mut ItemTirBuilder<'t>,
) -> &'t Trait<'t> {
    let id = tir.get_id(trait_.id).unwrap();
    let generics = tir.get_generics(id);

    let assoc_items = trait_
        .assoc_items
        .iter()
        .map(|assoc_item| match assoc_item {
            ast::AssocItem::Fn(f) => AssocItem::Fn(*build_fn(ast, f, resolutions, tir)),
            ast::AssocItem::Type(t) => {
                AssocItem::TyAlias(*build_type_alias(ast, t, resolutions, tir))
            }
        })
        .collect::<Vec<_>>()
        .into_iter();
    let assoc_items = tir.empty_tir.arena.alloc_slice_fill_iter(assoc_items);

    let tir_trait = tir::Trait {
        id,
        name: tir.empty_tir.arena.alloc(trait_.ident.to_string()),
        generics,
        assoc_items,
    };
    let tir_trait = tir.empty_tir.arena.alloc(tir_trait);
    tir.register_item(id, tir.empty_tir.arena.alloc(tir::Item::Trait(*tir_trait)));
    tir_trait
}

fn build_impl<'a, 't>(
    ast: &'a Nodes<'a>,
    impl_: &ast::Impl<'a>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    tir: &mut ItemTirBuilder<'t>,
) -> &'t Impl<'t> {
    let id = tir.get_id(impl_.id).unwrap();
    let generics = tir.get_generics(id);

    let assoc_items = impl_
        .assoc_items
        .iter()
        .map(|assoc_item| match assoc_item {
            ast::AssocItem::Fn(f) => AssocItem::Fn(*build_fn(ast, f, resolutions, tir)),
            ast::AssocItem::Type(t) => {
                AssocItem::TyAlias(*build_type_alias(ast, t, resolutions, tir))
            }
        })
        .collect::<Vec<_>>()
        .into_iter();
    let assoc_items = tir.empty_tir.arena.alloc_slice_fill_iter(assoc_items);

    let of_trait = {
        for ast::PathSeg { args, span, .. } in
            impl_.of_trait.segments[..(impl_.of_trait.segments.len() - 1)].iter()
        {
            if args.0.len() > 0 {
                tir.empty_tir
                    .err(diag_gen_args_provided_when_shouldnt(*span));
            }
        }
        let ast::PathSeg { args, .. } = impl_.of_trait.segments.last().unwrap();
        let args = EarlyBinder(GenArgs(tir.empty_tir.arena.alloc_slice_fill_iter(
            args.0.iter().map(|arg| match arg {
                ast::GenArg::Ty(ty) => {
                    GenArg::Ty(build_ty(ty, tir, resolutions, generics).skip_binder())
                }
            }),
        )));
        let res = resolutions.get(&impl_.id).unwrap();
        match res {
            Res::Def(DefKind::Trait, id) => {
                let tir_id = tir.get_id(*id).unwrap();
                (tir_id, args)
            }
            _ => unreachable!(),
        }
    };

    let tir_impl = tir::Impl {
        id,
        of_trait,
        generics,
        assoc_items,
    };
    let tir_impl = tir.empty_tir.arena.alloc(tir_impl);
    tir.register_item(id, tir.empty_tir.arena.alloc(tir::Item::Impl(*tir_impl)));
    tir_impl
}
