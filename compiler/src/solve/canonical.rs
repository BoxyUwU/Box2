use std::collections::HashMap;

use crate::{
    tir::{
        visit::{TypeFoldable, TypeFolder, TypeSuperFoldable},
        Binder, BoundVar, Bounds, DebruijnIndex, InferId, TirCtx, Ty, Universe,
    },
    tokenize::Span,
    typeck::InferCtxt,
};

pub struct Canonical<'t, T> {
    value: T,
    vars: &'t [CanonicalVar],
    highest_universe: Universe,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum CanonicalizerMode {
    Input,
    Response,
}

pub struct OriginalValues<'t>(pub &'t [&'t Ty<'t>]);

pub struct VarValues<'t>(pub &'t [&'t Ty<'t>]);

pub struct Response<'t> {
    pub var_values: VarValues<'t>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum CanonicalVar {
    ExistentialTy(Universe),
    UniversalTy(Universe, BoundVar),
}
impl CanonicalVar {
    pub fn universe(&self) -> Universe {
        let (Self::ExistentialTy(u) | Self::UniversalTy(u, _)) = self;
        *u
    }

    pub fn update_universe(&mut self, new_u: Universe) {
        let (Self::ExistentialTy(u) | Self::UniversalTy(u, _)) = self;
        *u = new_u;
    }
}

impl<'t, T: TypeFoldable<'t>> Canonical<'t, T> {
    fn instantiate(self, infcx: &InferCtxt<'t>, var_values: &VarValues<'t>) -> T {
        struct CanonicalInstantiator<'a, 't> {
            tcx: &'t TirCtx<'t>,
            var_values: &'a VarValues<'t>,
            outtermost_debruijn: DebruijnIndex,
        }
        impl<'a, 't> CanonicalInstantiator<'a, 't> {
            pub fn new(tcx: &'t TirCtx<'t>, var_values: &'a VarValues<'t>) -> Self {
                Self {
                    tcx,
                    var_values,
                    outtermost_debruijn: DebruijnIndex(0),
                }
            }
        }
        impl<'t> TypeFolder<'t> for CanonicalInstantiator<'_, 't> {
            fn tcx(&self) -> &'t TirCtx<'t> {
                self.tcx
            }

            fn fold_ty(&mut self, ty: &'t Ty<'t>) -> &'t Ty<'t> {
                match ty {
                    Ty::Bound(debruijn, var) if *debruijn == self.outtermost_debruijn => {
                        self.var_values.0[var.0 as usize]
                    }
                    _ => ty.super_fold_with(self),
                }
            }

            fn fold_binder<T: TypeFoldable<'t>>(&mut self, binder: Binder<'t, T>) -> Binder<'t, T> {
                self.outtermost_debruijn.0 += 1;
                let vars = binder.vars();
                let r = binder.skip_binder().fold_with(self);
                self.outtermost_debruijn.0 -= 1;
                Binder::bind_with_vars(r, vars)
            }
        }

        self.value
            .fold_with(&mut CanonicalInstantiator::new(infcx.tcx, &var_values))
    }
}

impl<'t> InferCtxt<'t> {
    pub fn canonicalize<T: TypeFoldable<'t>>(
        &self,
        value: T,
        mode: CanonicalizerMode,
    ) -> (OriginalValues<'t>, Canonical<'t, T>) {
        struct Canonicalizer<'a, 't> {
            infcx: &'a InferCtxt<'t>,
            outtermost_debruijn: DebruijnIndex,

            mode: CanonicalizerMode,

            canonical_vars: Vec<CanonicalVar>,
            original_vars: Vec<&'t Ty<'t>>,

            canonicalized_placeholders: HashMap<(Universe, BoundVar), &'t Ty<'t>>,
            canonicalized_infers: HashMap<InferId, &'t Ty<'t>>,
        }

        impl<'a, 't> Canonicalizer<'a, 't> {
            pub fn new(infcx: &'a InferCtxt<'t>, mode: CanonicalizerMode) -> Self {
                Self {
                    infcx,
                    outtermost_debruijn: DebruijnIndex(0),

                    mode,

                    canonical_vars: vec![],
                    original_vars: vec![],

                    canonicalized_placeholders: HashMap::new(),
                    canonicalized_infers: HashMap::new(),
                }
            }

            pub fn canonicalize_placeholder(&mut self, u: Universe, var: BoundVar) -> &'t Ty<'t> {
                *self
                    .canonicalized_placeholders
                    .entry((u, var))
                    .or_insert_with(|| {
                        let idx = self.canonical_vars.len();

                        let bound_var = match self.mode {
                            CanonicalizerMode::Input => BoundVar(idx as u32),
                            CanonicalizerMode::Response => var,
                        };

                        self.canonical_vars.push(CanonicalVar::UniversalTy(
                            Universe::new_raw(u.idx(), 0),
                            bound_var,
                        ));
                        self.original_vars
                            .push(self.infcx.tcx.arena.alloc(Ty::Placeholder(u, var)));
                        &*self
                            .infcx
                            .tcx
                            .arena
                            .alloc(Ty::Bound(self.outtermost_debruijn, bound_var))
                    })
            }

            pub fn canonicalize_infer(&mut self, id: InferId) -> &'t Ty<'t> {
                *self.canonicalized_infers.entry(id).or_insert_with(|| {
                    let idx = self.canonical_vars.len();
                    self.canonical_vars
                        .push(CanonicalVar::ExistentialTy(Universe::new_raw(
                            self.infcx.universe_of_var(id).idx(),
                            0,
                        )));
                    self.original_vars
                        .push(self.infcx.tcx.arena.alloc(Ty::Infer(id)));
                    self.infcx
                        .tcx
                        .arena
                        .alloc(Ty::Bound(self.outtermost_debruijn, BoundVar(idx as u32)))
                })
            }
        }

        impl<'t> TypeFolder<'t> for Canonicalizer<'_, 't> {
            fn tcx(&self) -> &'t TirCtx<'t> {
                self.infcx.tcx
            }

            fn fold_ty(&mut self, ty: &'t Ty<'t>) -> &'t Ty<'t> {
                let ty = self
                    .infcx
                    .tcx
                    .arena
                    .alloc(self.infcx.shallow_resolve_ty(*ty));

                match ty {
                    Ty::Placeholder(universe, var) => {
                        self.canonicalize_placeholder(*universe, *var)
                    }
                    Ty::Infer(var) => self.canonicalize_infer(*var),
                    _ => ty.super_fold_with(self),
                }
            }

            fn fold_binder<T: TypeFoldable<'t>>(&mut self, binder: Binder<'t, T>) -> Binder<'t, T> {
                self.outtermost_debruijn.0 += 1;
                let vars = binder.vars();
                let value = binder.skip_binder().fold_with(self);
                self.outtermost_debruijn.0 -= 1;
                Binder::bind_with_vars(value, vars)
            }
        }

        let mut canonicalizer = Canonicalizer::new(self, mode);
        let value = value.fold_with(&mut canonicalizer);

        let max_universe = match mode {
            CanonicalizerMode::Response => {
                for var in canonicalizer.canonical_vars.iter_mut() {
                    var.update_universe(Universe::ROOT);
                }
                Universe::ROOT
            }
            CanonicalizerMode::Input => {
                let mut curr_new_universe = Universe::ROOT;
                let mut next_orig_universe = Some(Universe::ROOT);
                let mut prev_was_existential = false;
                while let Some(orig_universe) = next_orig_universe {
                    next_orig_universe = None;

                    let mut update_vars = |existentials: bool| {
                        for var in canonicalizer.canonical_vars.iter_mut() {
                            if (existentials && matches!(var, CanonicalVar::UniversalTy(_, _)))
                                || (!existentials && matches!(var, CanonicalVar::ExistentialTy(_)))
                            {
                                continue;
                            }

                            if var.universe() != orig_universe {
                                if next_orig_universe
                                    .map(|universe| var.universe().idx() < universe.idx())
                                    .unwrap_or(true)
                                {
                                    next_orig_universe = Some(var.universe())
                                }

                                continue;
                            }

                            if existentials {
                                prev_was_existential = true;
                            } else {
                                if prev_was_existential {
                                    curr_new_universe =
                                        Universe::new_raw(curr_new_universe.idx() + 1, 0);
                                }
                                prev_was_existential = false;
                            }
                            var.update_universe(curr_new_universe);
                        }
                    };

                    update_vars(false);
                    update_vars(true);
                }

                curr_new_universe
            }
        };

        (
            OriginalValues(
                self.tcx
                    .arena
                    .alloc_slice_fill_iter(canonicalizer.original_vars.into_iter()),
            ),
            Canonical {
                value,
                vars: self
                    .tcx
                    .arena
                    .alloc_slice_fill_iter(canonicalizer.canonical_vars.into_iter()),
                highest_universe: max_universe,
            },
        )
    }

    pub fn new_from_canonical<T: TypeFoldable<'t>>(
        tcx: &'t TirCtx<'t>,
        canonical: Canonical<'t, T>,
    ) -> (InferCtxt<'t>, T, VarValues<'t>) {
        let mut infcx = InferCtxt::new(tcx);

        for _ in 0..(canonical.highest_universe.idx()) {
            infcx.enter_new_universe();
        }

        let var_values = VarValues(
            tcx.arena
                .alloc_slice_fill_iter(canonical.vars.into_iter().enumerate().map(
                    |(bound_var, canonical_var)| {
                        &*match canonical_var {
                            CanonicalVar::ExistentialTy(u) => tcx
                                .arena
                                .alloc(Ty::Infer(infcx.new_var_in_universe(*u, Span::new(0..0)))),
                            CanonicalVar::UniversalTy(u, _) => tcx
                                .arena
                                .alloc(Ty::Placeholder(*u, BoundVar(bound_var as u32))),
                        }
                    },
                )),
        );

        let value = canonical.instantiate(&infcx, &var_values);

        (infcx, value, var_values)
    }

    pub fn create_canonical_response(
        &mut self,
        var_values: VarValues<'t>,
    ) -> Canonical<'t, Response<'t>> {
        let (_, canonical_var_values) = self.canonicalize(var_values, CanonicalizerMode::Response);

        Canonical {
            value: Response {
                var_values: canonical_var_values.value,
            },
            vars: canonical_var_values.vars,
            highest_universe: canonical_var_values.highest_universe,
        }
    }

    pub fn instantiate_canonical_response(
        &mut self,
        orig_values: OriginalValues<'t>,
        response: Canonical<'t, Response<'t>>,
        bounds: Bounds<'t>,
    ) {
        let var_values = VarValues(
            self.tcx
                .arena
                .alloc_slice_fill_iter(response.vars.iter().map(|var_info| {
                    match var_info {
                        CanonicalVar::ExistentialTy(_) => self
                            .tcx
                            .arena
                            .alloc(Ty::Infer(self.new_var(Span::new(0..0)))),
                        CanonicalVar::UniversalTy(_, var) => orig_values.0[var.0 as usize],
                    }
                })),
        );

        let response = response.instantiate(self, &var_values);

        assert_eq!(response.var_values.0.len(), orig_values.0.len());

        for (ty_a, ty_b) in response.var_values.0.iter().zip(orig_values.0.iter()) {
            self.eq(**ty_a, **ty_b, bounds).unwrap();
        }
    }
}
