use std::collections::HashMap;

use codespan_reporting::diagnostic::Label;

use crate::ast::visit::Visitor;
use crate::ast::{self, NodeId, Nodes};
use crate::resolve::DefKind;

use super::super::tir;
use super::*;

/*
1. Tir Pre-Build
    - assemble all TirIds and generics defined on items
2. Tir ConcreteBuild
    - lower items, and terms which don't involve inference variables
3. Tir InferenceBuild
    - lower and check/infer terms that can contain inference variables
*/

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

fn diag_non_trait_resolution_of_trait_bound(span: Span) -> Diagnostic<usize> {
    Diagnostic::error()
        .with_message(&format!("path must resolve to a trait"))
        .with_labels(vec![Label::primary(0, span)])
}

fn diag_unexpected_res_of_path_ty(span: Span, actual_res: &str) -> Diagnostic<usize> {
    Diagnostic::error()
        .with_message(&format!(
            "path resolved to {} which is not valid for a type",
            actual_res
        ))
        .with_labels(vec![Label::primary(0, span)])
}

fn diag_non_alias_in_alias_eq_bound(span: Span) -> Diagnostic<usize> {
    Diagnostic::error()
        .with_message(&format!(
            "alias equality bound with non alias type on the left hand side"
        ))
        .with_labels(vec![Label::primary(0, span)])
}

pub struct ItemTirBuilder<'t> {
    empty_tir: &'t TirCtx<'t>,
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

    pub fn reset_in_scope_binders_in<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        todo!()
    }

    pub fn enter_generics<T>(
        &mut self,
        item: TirId,
        f: impl FnOnce(&mut Self, &'t Generics<'t>) -> T,
    ) -> T {
        todo!()
    }
}

pub trait TirBuilder<'t> {
    fn resolutions(&self) -> &HashMap<NodeId, Res<NodeId>>;
    fn in_scope_binders(&self) -> &InScopeBinders;
    fn in_scope_binders_mut(&mut self) -> &mut InScopeBinders;

    fn arena(&self) -> &'t Bump;
    fn get_id(&self, id: NodeId) -> Option<TirId>;
    fn get_generics(&self, id: TirId) -> &'t Generics<'t>;
    fn get_item(&self, id: TirId) -> &'t Item<'t>;
    fn err(&self, err: Diagnostic<usize>);

    fn allow_infers(&self) -> bool;
    fn ty_infer(&mut self, span: Span) -> &'t Term<'t>;
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

    fn ty_infer(&mut self, _: Span) -> &'t Term<'t> {
        unreachable!("cannot create infer vars in `ItemTirBuilder`");
    }

    fn resolutions(&self) -> &HashMap<NodeId, Res<NodeId>> {
        todo!()
    }

    fn in_scope_binders(&self) -> &InScopeBinders {
        todo!()
    }

    fn in_scope_binders_mut(&mut self) -> &mut InScopeBinders {
        todo!()
    }
}

pub struct InScopeBinders {
    early_params: Vec<HashMap<TirId, u32>>,
    binders: Vec<HashMap<TirId, u32>>,
}

impl InScopeBinders {
    pub fn new<'a, 't: 'a>(item_generics: impl IntoIterator<Item = &'a Generics<'t>>) -> Self {
        Self {
            early_params: item_generics
                .into_iter()
                .map(|generics| generics.param_id_to_var.clone())
                .collect(),
            binders: vec![],
        }
    }

    fn enter_generics<'t, B: TirBuilder<'t>, T>(
        &mut self,
        tcx: &mut B,
        item: TirId,
        f: impl FnOnce(&mut InScopeBinders, &mut B, &'t Generics<'t>) -> T,
    ) -> T {
        assert_eq!(self.binders.len(), 0);

        let generics = tcx.get_generics(item);
        self.early_params.push(generics.param_id_to_var.clone());
        let r = f(self, tcx, generics);
        self.early_params.pop();
        r
    }

    fn try_lower_binder<'t, B: TirBuilder<'t>, T, U>(
        &mut self,
        tcx: &mut B,
        ast_binder: ast::Binder<'_, T>,
        f: impl FnOnce(&mut InScopeBinders, &mut B, T) -> Option<U>,
    ) -> Option<Binder<'t, U>> {
        self.binders.push(
            ast_binder
                .vars
                .iter()
                .enumerate()
                .map(|(n, var)| (tcx.get_id(var.id).unwrap(), n as u32))
                .collect(),
        );

        let lowered_value = f(self, tcx, ast_binder.value);

        self.binders.pop();

        Some(Binder {
            value: lowered_value?,
            vars: tcx
                .arena()
                .alloc_slice_fill_iter(ast_binder.vars.iter().map(|var| match var.kind {
                    ast::GenericParamKind::Type => BoundVarKind::Ty,
                })),
        })
    }

    fn lower_binder<'t, B: TirBuilder<'t>, T, U>(
        &mut self,
        tcx: &mut B,
        ast_binder: ast::Binder<'_, T>,
        f: impl FnOnce(&mut InScopeBinders, &mut B, T) -> U,
    ) -> Binder<'t, U> {
        self.try_lower_binder(tcx, ast_binder, |a, b, c| Some(f(a, b, c)))
            .unwrap()
    }

    fn bound_var_for_param(&self, param: TirId) -> (DebruijnIndex, BoundVar) {
        self.binders
            .iter()
            .rev()
            .enumerate()
            .chain(self.early_params.iter().map(|hm| (self.binders.len(), hm)))
            .find_map(|(depth, var_map)| {
                Some((
                    DebruijnIndex(depth as u32),
                    BoundVar(*(var_map.get(&param)?) as u32),
                ))
            })
            .unwrap_or_else(|| panic!("param {:?} was resolved to something not in scope", param))
    }
}

struct EarlyTirBuild<'t> {
    tir: &'t TirCtx<'t>,
    generics_stack: Vec<&'t Generics<'t>>,
    next_tir_id: TirId,
    next_body_id: BodyId,

    generics: HashMap<TirId, &'t Generics<'t>>,
    lowered_ids: HashMap<NodeId, TirId>,
    bodies: HashMap<NodeId, (TirId, Vec<NodeId>, BodyId)>,
}

impl<'t> EarlyTirBuild<'t> {
    fn register_params(&mut self, params: &[&ast::GenericParam<'_>]) {
        for param in params {
            self.new_lowered_tir_id(param.id);
        }
    }
    fn push_generics(&mut self, id: TirId, generics: &ast::Generics<'_>) {
        self.register_params(generics.params);
        let generics = build_generics(*generics, id, self, self.generics_stack.last().copied());
        self.generics_stack.push(generics);
        self.generics.insert(id, generics);
    }
    fn pop_generics(&mut self) {
        self.generics_stack
            .pop()
            .expect("popping generics when nothing is on stack");
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

    pub fn get_id(&self, id: NodeId) -> TirId {
        self.lowered_ids[&id]
    }
}
impl<'t> ast::visit::Visitor<'_> for EarlyTirBuild<'t> {
    fn visit_mod(&mut self, module: &ast::Module<'_>) {
        self.new_lowered_tir_id(module.id);
        ast::visit::super_visit_mod(self, module)
    }

    fn visit_type_def(&mut self, def: &ast::TypeDef<'_>) {
        let id = self.new_lowered_tir_id(def.id);
        self.push_generics(id, &def.generics);
        ast::visit::super_visit_type_def(self, def);
        self.pop_generics();
    }

    fn visit_variant_def(&mut self, def: &ast::VariantDef<'_>) {
        self.new_lowered_tir_id(def.id);
        ast::visit::super_visit_variant_def(self, def);
    }

    fn visit_field_def(&mut self, def: &ast::FieldDef<'_>) {
        self.new_lowered_tir_id(def.id);
        ast::visit::super_visit_field_def(self, def);
    }

    fn visit_type_alias(&mut self, alias: &ast::TypeAlias<'_>) {
        let id = self.new_lowered_tir_id(alias.id);
        self.push_generics(id, &alias.generics);
        ast::visit::super_visit_type_alias(self, alias);
        self.pop_generics();
    }

    fn visit_fn(&mut self, func: &ast::Fn<'_>) {
        let owner = self.new_lowered_tir_id(func.id);
        self.push_generics(owner, &func.generics);

        if let Some(body) = func.body {
            self.new_body_id(
                owner,
                func.params.iter().map(|param| param.id).collect::<Vec<_>>(),
                body.id,
            );
        }

        ast::visit::super_visit_fn(self, func);
        self.pop_generics();
    }

    fn visit_trait(&mut self, trait_: &ast::Trait<'_>) {
        let id = self.new_lowered_tir_id(trait_.id);
        self.push_generics(id, &trait_.generics);
        ast::visit::super_visit_trait(self, trait_);
        self.pop_generics();
    }

    fn visit_impl(&mut self, impl_: &ast::Impl<'_>) {
        let id = self.new_lowered_tir_id(impl_.id);
        self.push_generics(id, &impl_.generics);
        ast::visit::super_visit_impl(self, impl_);
        self.pop_generics();
    }

    fn visit_bounds(&mut self, bounds: &ast::Bounds<'_>) {
        for clause in bounds.clauses {
            if let ast::ClauseKind::Bound(binder) = clause.kind {
                self.register_params(binder.vars);
            }
        }
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
    let module = ast.get(root).unwrap_mod();

    let mut early_builder = EarlyTirBuild {
        tir: empty_tir,
        generics_stack: vec![],

        next_tir_id: TirId(0),
        next_body_id: BodyId(0),

        generics: HashMap::new(),
        lowered_ids: HashMap::new(),
        bodies: HashMap::new(),
    };
    early_builder.visit_mod(module);

    let EarlyTirBuild {
        generics,
        lowered_ids,
        bodies,
        ..
    } = early_builder;

    let mut tir_builder = ItemTirBuilder {
        empty_tir,
        generics,
        lowered_ids,
        bodies,
    };
    let module = build_mod(ast, module, resolutions, &mut tir_builder);

    let ItemTirBuilder {
        bodies,
        empty_tir: tir,
        lowered_ids,
        ..
    } = tir_builder;

    let body_sources = bodies
        .into_iter()
        .map(|(expr_id, (owner, params, body_id))| {
            let item = tir.get_item(owner);
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
                    term: expr_id,
                    ret: ret_ty,
                    params,
                },
            )
        })
        .collect::<HashMap<_, _>>();

    (module, body_sources, tir, lowered_ids)
}

pub fn build_term<'ast, 't>(
    builder: &mut impl TirBuilder<'t>,
    term: &'ast ast::Term<'ast>,
) -> &'t Term<'t> {
    let arena = builder.arena();

    match term.kind {
        ast::TermKind::Let {
            param,
            init,
            cont,
            sp: _,
        } => {
            let var_ty = param
                .ty
                .map(|ty| build_term(builder, ty))
                .unwrap_or_else(|| builder.ty_infer(todo!()));

            let init = build_term(builder, init);

            let param_id = builder.get_id(param.id).unwrap();
            builder
                .in_scope_binders_mut()
                .binders
                .push(HashMap::from([(param_id, 0)]));

            let cont = build_term(builder, cont);

            builder.in_scope_binders_mut().binders.pop().unwrap();

            let vars = arena.alloc_slice_copy(&[BoundVarKind::Var(var_ty)]);
            arena.alloc(Term::Let {
                ty: var_ty,
                init,
                _in: Binder::bind_with_vars(cont, vars),
            })
        }
        ast::TermKind::Path(path) => {
            // let args: EarlyBinder<GenArgs<'_>> = build_args_for_path(&path, tcx, resolutions, item_generics);
            let args: EarlyBinder<GenArgs<'_>> = todo!();
            let resolutions = builder.resolutions();
            match resolutions[&term.id] {
                Res::Def(DefKind::Adt, id) => {
                    let tir_id = builder.get_id(id).unwrap();
                    arena.alloc(Term::Adt(tir_id, args.skip_binder()))
                }
                Res::Def(DefKind::TypeAlias, id) => {
                    let tir_id = builder.get_id(id).unwrap();
                    arena.alloc(Term::Alias(tir_id, args.skip_binder()))
                }
                Res::Def(DefKind::Func, id) => {
                    let tir_id = builder.get_id(id).unwrap();
                    let path = Term::Path(tir::Path {
                        res: Res::Def(DefKind::Func, tir_id),
                        segs: todo!(),
                    });
                    arena.alloc(path)
                }
                // FIXME: no way to typeof(func)
                // Res::Def(DefKind::Func, id) => {
                //     let tir_id = builder.get_id(id).unwrap();
                //     builder
                //         .arena
                //         .alloc(Term::FnDef(tir_id, args.skip_binder()))
                // }
                Res::Local(id) | Res::Def(DefKind::GenericParam, id) => {
                    let tir_id = builder.get_id(id).unwrap();
                    let (debruijn_idx, bound_var) =
                        builder.in_scope_binders().bound_var_for_param(tir_id);
                    arena.alloc(Term::Bound(debruijn_idx, bound_var))
                }
                Res::Def(DefKind::Variant, _) => {
                    builder.err(diag_unexpected_res_of_path_ty(path.span, "a variant"));
                    arena.alloc(Term::Error)
                }
                Res::Def(DefKind::Trait, _) => {
                    builder.err(diag_unexpected_res_of_path_ty(path.span, "a trait"));
                    arena.alloc(Term::Error)
                }
                Res::Def(DefKind::Mod, _) => {
                    builder.err(diag_unexpected_res_of_path_ty(path.span, "a module"));
                    arena.alloc(Term::Error)
                }

                Res::Err => arena.alloc(Term::Error),

                Res::Def(DefKind::Impl, _) | Res::Def(DefKind::Field, _) => unreachable!(),
            }
        }
        ast::TermKind::FnCall(fn_call) => {
            let args = arena
                .alloc_slice_fill_iter(fn_call.args.iter().map(|term| build_term(builder, term)));

            arena.alloc(Term::FnCall(FnCall {
                func: build_term(builder, fn_call.func),
                args,
            }))
        }
        ast::TermKind::TypeInit(type_init) => {
            let res = builder.resolutions().get(&term.id).unwrap();
            match res {
                Res::Def(DefKind::Adt, adt_id) => {
                    let adt_id = builder.get_id(*adt_id).unwrap();

                    let ty_args = type_init
                        .path
                        .segments
                        .last()
                        .unwrap()
                        .args
                        .0
                        .iter()
                        .map(|term| build_term(builder, term));
                    let ty_args = arena.alloc_slice_fill_iter(ty_args);
                    arena.alloc(Term::Adt(adt_id, tir::GenArgs(ty_args)))
                }
                Res::Def(DefKind::Variant, variant_id) => {
                    let variant_id = builder.get_id(*variant_id).unwrap();

                    let ty_args = type_init
                        .path
                        .segments
                        .iter()
                        .rev()
                        .nth(1)
                        .unwrap()
                        .args
                        .0
                        .iter()
                        .map(|term| build_term(builder, term));
                    let ty_args = arena.alloc_slice_fill_iter(ty_args);
                    arena.alloc(Term::Adt(variant_id, tir::GenArgs(ty_args)))
                }
                _ => unreachable!(),
            }
        }
        ast::TermKind::BinOp(bin_op, expr, expr1, span) => todo!(),
        ast::TermKind::UnOp(un_op, expr, span) => todo!(),
        ast::TermKind::Lit(literal, span) => todo!(),
        ast::TermKind::FieldInit(field_init) => todo!(),
        ast::TermKind::Infer(_) => match builder.allow_infers() {
            true => builder.ty_infer(todo!()),
            false => {
                builder.err(diag_infer_var_in_signature(todo!()));
                &Term::Error
            }
        },
    }
}

pub fn build_args_for_path<'t>(
    tcx: &mut impl TirBuilder<'t>,
    path: &ast::Path<'_>,
) -> EarlyBinder<GenArgs<'t>> {
    let mut args = vec![];

    for seg in path.segments {
        let seg = build_path_seg(tcx, **seg);
        args.extend(seg.skip_binder().args.0.into_iter().map(|arg| *arg));
    }

    EarlyBinder(GenArgs(tcx.arena().alloc_slice_fill_iter(args)))
}

pub fn build_path_seg<'t, T: TirBuilder<'t>>(
    tcx: &mut T,
    seg: ast::PathSeg<'_>,
) -> EarlyBinder<&'t PathSeg<'t>> {
    let lower_args = |tcx: &mut T, args: ast::GenArgs<'_>| {
        GenArgs(
            tcx.arena()
                .alloc_slice_fill_iter(args.0.iter().map(|term| build_term(tcx, term))),
        )
    };

    let res = tcx.resolutions()[&seg.id].map_id(|id| tcx.get_id(id).unwrap());
    let seg = match res {
        Res::Def(DefKind::TypeAlias | DefKind::Adt | DefKind::Func | DefKind::Trait, id) => {
            let args = lower_args(tcx, seg.args);
            let generics = tcx.get_generics(id);

            if args.0.len() != generics.params.len() {
                tcx.err(diag_wrong_gen_args_count(seg.span, generics.params.len()));
                PathSeg {
                    args: GenArgs(
                        tcx.arena().alloc_slice_fill_iter(
                            (0..generics.params.len()).map(|_| &Term::Error),
                        ),
                    ),
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
        Res::Def(DefKind::Field | DefKind::Impl, _) => unreachable!("paths cant resolve to fields"),
        Res::Err => PathSeg {
            args: GenArgs(&[]),
            res: tir::Res::Err,
        },
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
        ast::Item::TypeAlias(a) => Item::TyAlias(*build_type_alias(tir, a)),
        ast::Item::Fn(f) => Item::Fn(*build_fn(tir, f)),
        ast::Item::Trait(t) => Item::Trait(*build_trait(tir, t)),
        ast::Item::Impl(i) => Item::Impl(*build_impl(tir, i)),

        ast::Item::Use(_) | ast::Item::VariantDef(_) | ast::Item::FieldDef(_) => return None,
    };
    let item = tir.empty_tir.arena.alloc(item);
    Some(&*item)
}

pub fn build_generics<'a, 't>(
    generics: ast::Generics<'a>,
    tir_item: TirId,
    builder: &mut EarlyTirBuild<'t>,
    parent_generics: Option<&'t Generics<'t>>,
) -> &'t tir::Generics<'t> {
    let parent_count = parent_generics
        .map(|generics| generics.parent_count + (generics.params.len() as u32))
        .unwrap_or(0);

    let params = generics.params.iter().enumerate().map(|(n, param)| {
        let param_id = builder.get_id(param.id);
        tir::GenParam {
            id: param_id,
            kind: match param.kind {
                ast::GenericParamKind::Type => tir::GenParamKind::Ty,
            },
            name: builder.tir.arena.alloc(param.name.to_string()),
            index: parent_count + (n as u32),
        }
    });
    let params = builder.tir.arena.alloc_slice_fill_iter(params);

    let generics = tir::Generics {
        item: tir_item,
        parent: parent_generics.map(|generics| generics.item),
        params,
        parent_count,
        param_id_to_var: builder.tir.arena.alloc(
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
    builder.tir.arena.alloc(generics)
}

pub fn build_binder<'t, T, U, R: TirBuilder<'t>>(
    tir: &mut R,
    binder: ast::Binder<'_, T>,
    f: impl FnOnce(&mut R, T) -> Option<U>,
) -> Option<Binder<'t, U>> {
    todo!()
}

pub fn build_clause<'a, 't>(
    tir: &mut ItemTirBuilder<'t>,
    clause: &ast::Clause<'a>,
) -> Option<tir::Clause<'t>> {
    match &clause.kind {
        ast::ClauseKind::AliasEq(t1, t2) => {
            let t1 = build_term(tir, t1);
            let t2 = build_term(tir, t2);
            match *t1 {
                Term::Alias(id, args) => Some(tir::Clause::AliasEq(id, args, t2)),
                _ => {
                    tir.err(diag_non_alias_in_alias_eq_bound(todo!()));
                    None
                }
            }
        }
        ast::ClauseKind::Trait(path) => match tir.resolutions()[&clause.id] {
            Res::Def(DefKind::Trait, id) => {
                let id = tir.get_id(id).unwrap();
                let args = build_args_for_path(tir, path);
                Some(tir::Clause::Trait(id, args.skip_binder()))
            }
            Res::Local(_) | Res::Def(_, _) => {
                tir.err(diag_non_trait_resolution_of_trait_bound(path.span));
                None
            }
            Res::Err => None,
        },
        ast::ClauseKind::Bound(binder) => {
            let bound_clause = build_binder(tir, *binder, |tir, clause| {
                build_clause(tir, clause).map(|clause| &*tir.arena().alloc(clause))
            })?;
            Some(tir::Clause::Bound(bound_clause))
        }
    }
}

pub fn build_bounds<'a, 't>(
    tir: &mut ItemTirBuilder<'t>,
    bounds: ast::Bounds<'a>,
    params_introduced_with_bounds: &[GenParam<'t>],
) -> EarlyBinder<tir::Bounds<'t>> {
    let mut clauses = bounds
        .clauses
        .iter()
        .flat_map(|clause| build_clause(tir, clause))
        .collect::<Vec<_>>();
    clauses.extend(params_introduced_with_bounds.iter().map(|param| {
        let (debruijn_idx, bound_var) = tir.in_scope_binders().bound_var_for_param(param.id);
        tir::Clause::WellFormed(tir.arena().alloc(Term::Bound(debruijn_idx, bound_var)))
    }));

    let clauses = tir.arena().alloc_slice_fill_iter(clauses);
    EarlyBinder(tir::Bounds { clauses })
}

pub fn build_mod<'a, 't>(
    ast: &'a Nodes<'a>,
    mod_: &ast::Module<'a>,
    resolutions: &HashMap<NodeId, Res<NodeId>>,
    tir: &mut ItemTirBuilder<'t>,
) -> &'t Mod<'t> {
    let id = tir.get_id(mod_.id).unwrap();

    let items = tir.reset_in_scope_binders_in(|tir| {
        tir.empty_tir.arena.alloc_slice_fill_iter(
            mod_.items
                .iter()
                .flat_map(|nested_item| build_item(ast, nested_item, resolutions, tir))
                .collect::<Vec<_>>()
                .into_iter()
                .copied(),
        )
    });

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

    tir.reset_in_scope_binders_in(|tir| {
        tir.enter_generics(id, |tir, generics| {
            let bounds = build_bounds(tir, adt.bounds, generics.params);

            let variants =
                adt.variants
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
                                    ty: EarlyBinder(
                                        tir.empty_tir.arena.alloc(build_term(tir, field_def.ty)),
                                    ),
                                };
                                &*tir.empty_tir.arena.alloc(Item::Field(field))
                            })
                            .collect::<Vec<_>>();
                        for f in fields.iter() {
                            tir.register_item(f.unwrap_field().id, f);
                        }
                        let fields = tir.empty_tir.arena.alloc_slice_fill_iter(
                            fields.into_iter().map(|item| item.unwrap_field()),
                        );

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
                bounds,
                variants,
            };
            let tir_adt = tir.empty_tir.arena.alloc(tir_adt);
            tir.register_item(id, tir.empty_tir.arena.alloc(tir::Item::Adt(*tir_adt)));
            tir_adt
        })
    })
}

fn build_type_alias<'a, 't>(
    tir: &mut ItemTirBuilder<'t>,
    alias: &ast::TypeAlias<'a>,
) -> &'t TyAlias<'t> {
    let id = tir.get_id(alias.id).unwrap();

    tir.enter_generics(id, |tir, generics| {
        let bounds = build_bounds(tir, alias.bounds, generics.params);

        let tir_alias = tir::TyAlias {
            id,
            name: tir.empty_tir.arena.alloc(alias.name.to_string()),
            generics,
            bounds,
            ty: alias.ty.map(|term| EarlyBinder(build_term(tir, term))),
        };
        let tir_alias = tir.empty_tir.arena.alloc(tir_alias);
        tir.register_item(
            id,
            tir.empty_tir.arena.alloc(tir::Item::TyAlias(*tir_alias)),
        );
        tir_alias
    })
}

fn build_fn<'a, 't>(tir: &mut ItemTirBuilder<'t>, func: &ast::Fn<'a>) -> &'t Fn<'t> {
    let id = tir.get_id(func.id).unwrap();
    tir.enter_generics(id, |tir, generics| {
        let bounds = build_bounds(tir, func.bounds, generics.params);

        let params = func
            .params
            .iter()
            .map(|param| tir::Param {
                ty: EarlyBinder(build_term(tir, param.ty.unwrap())),
                span: param.span,
            })
            .collect::<Vec<_>>()
            .into_iter();
        let params = tir.empty_tir.arena.alloc_slice_fill_iter(params);

        let tir_fn = tir::Fn {
            id,
            name: tir.empty_tir.arena.alloc(func.name.to_string()),
            generics,
            bounds,
            params,
            ret_ty: func
                .ret_ty
                .map(|ty| EarlyBinder(build_term(tir, ty)))
                .unwrap_or_else(|| EarlyBinder(&*tir.empty_tir.arena.alloc(Term::Unit))),
            body: func.body.map(|expr| {
                tir.get_body_id(expr.id)
                    .expect("bodyids and tirids should have been pre generated before building tir")
            }),
        };
        let tir_fn = tir.empty_tir.arena.alloc(tir_fn);
        tir.register_item(id, tir.empty_tir.arena.alloc(tir::Item::Fn(*tir_fn)));
        tir_fn
    })
}

fn build_trait<'a, 't>(tir: &mut ItemTirBuilder<'t>, trait_: &ast::Trait<'a>) -> &'t Trait<'t> {
    let id = tir.get_id(trait_.id).unwrap();

    tir.reset_in_scope_binders_in(|tir| {
        tir.enter_generics(id, |tir, generics| {
            let bounds = build_bounds(tir, trait_.bounds, generics.params);

            let assoc_items = trait_
                .assoc_items
                .iter()
                .map(|assoc_item| match assoc_item {
                    ast::AssocItem::Fn(f) => AssocItem::Fn(*build_fn(tir, f)),
                    ast::AssocItem::Type(t) => AssocItem::TyAlias(*build_type_alias(tir, t)),
                })
                .collect::<Vec<_>>()
                .into_iter();
            let assoc_items = tir.empty_tir.arena.alloc_slice_fill_iter(assoc_items);

            let tir_trait = tir::Trait {
                id,
                name: tir.empty_tir.arena.alloc(trait_.ident.to_string()),
                generics,
                bounds,
                assoc_items,
            };
            let tir_trait = tir.empty_tir.arena.alloc(tir_trait);
            tir.register_item(id, tir.empty_tir.arena.alloc(tir::Item::Trait(*tir_trait)));
            tir_trait
        })
    })
}

fn build_impl<'a, 't>(tir: &mut ItemTirBuilder<'t>, impl_: &ast::Impl<'a>) -> &'t Impl<'t> {
    let id = tir.get_id(impl_.id).unwrap();

    tir.reset_in_scope_binders_in(|tir| {
        tir.enter_generics(id, |tir, generics| {
            let bounds = build_bounds(tir, impl_.bounds, generics.params);

            let assoc_items = impl_
                .assoc_items
                .iter()
                .map(|assoc_item| match assoc_item {
                    ast::AssocItem::Fn(f) => AssocItem::Fn(*build_fn(tir, f)),
                    ast::AssocItem::Type(t) => AssocItem::TyAlias(*build_type_alias(tir, t)),
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
                let args =
                    EarlyBinder(GenArgs(tir.empty_tir.arena.alloc_slice_fill_iter(
                        args.0.iter().map(|term| build_term(tir, term)),
                    )));
                let res = tir.resolutions().get(&impl_.id).unwrap();
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
                bounds,
                assoc_items,
            };
            let tir_impl = tir.empty_tir.arena.alloc(tir_impl);
            tir.register_item(id, tir.empty_tir.arena.alloc(tir::Item::Impl(*tir_impl)));
            tir_impl
        })
    })
}
