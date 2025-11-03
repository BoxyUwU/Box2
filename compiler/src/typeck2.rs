use std::{cell::RefCell, collections::HashMap, ops::Deref};

use crate::{
    ast,
    resolve::{DefKind, Res},
    solve::{Goal, GoalKind, NoSolution},
    tir::{
        self,
        visit::{FallibleTermFolder, TermFoldable, TermFolder, TermSuperFoldable},
        Binder, BodySource, BoundVar, BoundVarKind, Bounds, Clause, DebruijnIndex, FnCall, InferId,
        Term, TirCtx, TirId, Universe, UniverseStorage,
    },
    tokenize::Span,
};

fn check_body<'ast, 't>(
    ast: &'ast crate::ast::Nodes<'ast>,
    tir: &'t TirCtx<'t>,
    body_owner: tir::Fn,
    body_source: BodySource<'t>,
) {
    let root_node = ast.get(body_source.term);
}

pub struct InScopeBinders2 {
    pub binders: Vec<HashMap<ast::NodeId, BoundVar>>,
}

impl InScopeBinders2 {
    fn get_bound_term(&self, id: ast::NodeId) -> (DebruijnIndex, BoundVar) {
        self.binders
            .iter()
            .rev()
            .enumerate()
            .find_map(|(n, binder)| binder.get(&id).map(|bv| (DebruijnIndex(n as u32), *bv)))
            .unwrap()
    }
}

pub struct Lowerer<'m, 't> {
    pub resolutions: &'m HashMap<ast::NodeId, Res<ast::NodeId>>,
    pub tir: &'t TirCtx<'t>,
    pub id_map: HashMap<ast::NodeId, TirId>,
    pub in_scope_binders: InScopeBinders2,
}

impl<'m, 't> Lowerer<'m, 't> {
    pub fn node_to_term<'ast>(&mut self, node: &'ast ast::Node<'ast>) -> &'t Term<'t> {
        match node {
            ast::Node::Clause(..)
            | ast::Node::Item(..)
            | ast::Node::Param(..)
            | ast::Node::GenericParam(..)
            | ast::Node::PathSeg(..) => unreachable!(),

            ast::Node::Term(term) => self.term_to_term(term),
        }
    }

    pub fn term_to_term<'ast>(&mut self, term: &'ast ast::Term<'ast>) -> &'t Term<'t> {
        let tir = self.tir;

        match term.kind {
            ast::TermKind::Let {
                param,
                init,
                cont,
                sp: _,
            } => {
                let var_ty = param
                    .ty
                    .map(|ty| self.term_to_term(ty))
                    .unwrap_or_else(|| self.infer_term());

                let init = self.term_to_term(init);

                self.in_scope_binders
                    .binders
                    .push(HashMap::from([(param.id, BoundVar(0))]));

                let cont = self.term_to_term(cont);

                self.in_scope_binders.binders.pop().unwrap();

                let vars = self
                    .tir
                    .arena
                    .alloc_slice_copy(&[BoundVarKind::Var(var_ty)]);
                self.tir.arena.alloc(Term::Let {
                    ty: var_ty,
                    init,
                    _in: Binder::bind_with_vars(cont, vars),
                })
            }
            ast::TermKind::Path(path) => {
                let res = self.resolutions.get(&term.id).unwrap();

                match res {
                    Res::Local(id) => {
                        let (dbj, bv) = self.in_scope_binders.get_bound_term(*id);
                        self.tir.arena.alloc(Term::Bound(dbj, bv))
                    }
                    Res::Def(DefKind::Func, id) => {
                        let ty_args = path
                            .segments
                            .last()
                            .unwrap()
                            .args
                            .0
                            .iter()
                            .map(|term| self.term_to_term(term));
                        let ty_args = tir.arena.alloc_slice_fill_iter(ty_args);

                        let id = self.id_map[id];
                        self.tir.arena.alloc(Term::FnDef(id, tir::GenArgs(ty_args)))
                    }
                    _ => todo!(),
                }
            }
            ast::TermKind::FnCall(fn_call) => {
                let args = self
                    .tir
                    .arena
                    .alloc_slice_fill_iter(fn_call.args.iter().map(|expr| self.term_to_term(expr)));

                self.tir.arena.alloc(Term::FnCall(FnCall {
                    func: self.term_to_term(fn_call.func),
                    args,
                }))
            }
            ast::TermKind::TypeInit(type_init) => {
                let res = self.resolutions.get(&term.id).unwrap();
                match res {
                    Res::Def(DefKind::Adt, adt_id) => {
                        let ty_args = type_init
                            .path
                            .segments
                            .last()
                            .unwrap()
                            .args
                            .0
                            .iter()
                            .map(|term| self.term_to_term(term));
                        let ty_args = tir.arena.alloc_slice_fill_iter(ty_args);
                        let adt_id = self.id_map[adt_id];
                        tir.arena.alloc(Term::Adt(adt_id, tir::GenArgs(ty_args)))
                    }
                    Res::Def(DefKind::Variant, variant_id) => {
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
                            .map(|term| self.term_to_term(term));
                        let ty_args = tir.arena.alloc_slice_fill_iter(ty_args);
                        let variant_id = self.id_map[variant_id];
                        self.tir
                            .arena
                            .alloc(Term::Adt(variant_id, tir::GenArgs(ty_args)))
                    }
                    _ => unreachable!(),
                }
            }
            ast::TermKind::BinOp(bin_op, expr, expr1, span) => todo!(),
            ast::TermKind::UnOp(un_op, expr, span) => todo!(),
            ast::TermKind::Lit(literal, span) => todo!(),
            ast::TermKind::FieldInit(field_init) => todo!(),
            ast::TermKind::Infer(_) => self.infer_term(),
        }
    }

    fn infer_term(&mut self) -> &'t Term<'t> {
        self.tir.arena.alloc(Term::Infer(InferId(0)))
    }
}

fn mk<T>() -> T {
    loop {}
}

struct BodyBuilder;

#[derive(Copy, Clone)]
pub enum InferVarValue<'t> {
    Known { known: &'t Term<'t> },
    Unknown { universe: Universe },
}

#[derive(Copy, Clone)]
pub enum Unification<'t> {
    Unconstrained(InferVarValue<'t>),
    EqTo(InferId),
}

pub struct TermVarStorage<'t> {
    unifications: Vec<Unification<'t>>,
    spans: Vec<Span>,
}
impl<'t> TermVarStorage<'t> {
    pub fn new() -> Self {
        Self {
            unifications: vec![],
            spans: vec![],
        }
    }

    pub fn new_key(&mut self, u: Universe, sp: Span) -> InferId {
        self.unifications
            .push(Unification::Unconstrained(InferVarValue::Unknown {
                universe: u,
            }));
        self.spans.push(sp);
        InferId((self.unifications.len() - 1) as u32)
    }

    pub fn probe_var(&self, mut var: InferId) -> (InferId, InferVarValue<'t>) {
        loop {
            match self.unifications[var.0 as usize] {
                Unification::Unconstrained(unconstrained_value) => {
                    return (var, unconstrained_value)
                }
                Unification::EqTo(new_var) => var = new_var,
            }
        }
    }

    pub fn instantiate(&mut self, var: InferId, to: &'t Term<'t>) {
        let (id, value) = self.probe_var(var);
        assert!(matches!(value, InferVarValue::Unknown { .. }));
        assert!(!matches!(to, Term::Infer(_)));

        self.unifications[id.0 as usize] =
            Unification::Unconstrained(InferVarValue::Known { known: to });
    }

    pub fn unify_vars(&mut self, v1: InferId, v2: InferId) {
        let v1 = self.probe_var(v1);
        let v2 = self.probe_var(v2);

        let unified_value = match (v1.1, v2.1) {
            (InferVarValue::Known { .. }, InferVarValue::Known { .. }) => {
                unreachable!("attempted to unify two vars which are already resolved to non infers")
            }
            (InferVarValue::Known { .. }, InferVarValue::Unknown { .. }) => v1.1,
            (InferVarValue::Unknown { .. }, InferVarValue::Known { .. }) => v2.1,
            (InferVarValue::Unknown { universe: u1 }, InferVarValue::Unknown { universe: u2 }) => {
                InferVarValue::Unknown {
                    universe: if u1.idx() < u2.idx() { u1 } else { u2 },
                }
            }
        };

        let (value_var, redirect_var) = if v1.0 .0 < v2.0 .0 {
            (v1.0, v2.0)
        } else {
            (v2.0, v1.0)
        };

        self.unifications[value_var.0 as usize] = Unification::Unconstrained(unified_value);
        self.unifications[redirect_var.0 as usize] = Unification::EqTo(value_var);
    }
}

pub struct InferCtxt<'t> {
    pub tcx: &'t TirCtx<'t>,
    term_var_storage: TermVarStorage<'t>,
    universes: UniverseStorage,
}
impl<'t> Deref for InferCtxt<'t> {
    type Target = TirCtx<'t>;
    fn deref(&self) -> &TirCtx<'t> {
        &self.tcx
    }
}

impl<'t> InferCtxt<'t> {
    pub fn new(tcx: &'t TirCtx<'t>) -> Self {
        Self {
            tcx,
            term_var_storage: TermVarStorage::new(),
            universes: UniverseStorage::new(),
        }
    }

    fn tcx(&self) -> &'t TirCtx<'t> {
        self.tcx
    }

    pub fn current_universe(&self) -> Universe {
        self.universes.current_universe()
    }

    pub fn enter_new_universe(&mut self) -> Universe {
        self.universes.enter_new_universe()
    }

    pub fn exit_current_universe(&mut self) {
        self.universes.exit_current_universe()
    }

    pub fn is_universe_alive(&self, universe: Universe) -> bool {
        self.universes.is_universe_alive(universe)
    }

    pub fn new_var(&mut self, span: Span) -> InferId {
        self.term_var_storage.new_key(self.current_universe(), span)
    }

    pub fn new_var_in_universe(&mut self, universe: Universe, span: Span) -> InferId {
        assert!(self.is_universe_alive(universe));
        self.term_var_storage.new_key(universe, span)
    }

    pub fn instantiate_var(&mut self, var: InferId, to: &'t Term<'t>) {
        self.term_var_storage.instantiate(var, to);
    }

    pub fn unify_vars(&mut self, var1: InferId, var2: InferId) {
        self.term_var_storage.unify_vars(var1, var2);
    }

    pub fn universe_of_var(&self, var: InferId) -> Universe {
        match self.term_var_storage.probe_var(var).1 {
            InferVarValue::Known { .. } => {
                panic!("universe_of_var called on var that was unified with a non infer")
            }
            InferVarValue::Unknown { universe } => universe,
        }
    }

    pub fn span_of_var(&self, var: InferId) -> Span {
        self.term_var_storage.spans[var.0 as usize]
    }

    pub fn shallow_resolve_var(&self, var: InferId) -> Term<'t> {
        let (var, value) = self.term_var_storage.probe_var(var);
        match value {
            InferVarValue::Known { known } => *known,
            InferVarValue::Unknown { .. } => Term::Infer(var),
        }
    }

    pub fn shallow_resolve_term(&self, t: Term<'t>) -> Term<'t> {
        match t {
            Term::Infer(var) => self.shallow_resolve_var(var),
            _ => t,
        }
    }

    pub fn deeply_resolve_ty(&self, t: Term<'t>) -> Term<'t> {
        struct DeeplyResolve<'a, 't> {
            infcx: &'a InferCtxt<'t>,
        }
        impl<'t> TermFolder<'t> for DeeplyResolve<'_, 't> {
            fn tcx(&self) -> &'t TirCtx<'t> {
                self.infcx.tcx()
            }

            fn fold_term(&mut self, t: &'t Term<'t>) -> &'t Term<'t> {
                let t = self
                    .infcx
                    .tcx()
                    .arena
                    .alloc(self.infcx.shallow_resolve_term(*t));
                t.super_fold_with(self)
            }

            fn fold_binder<T: TermFoldable<'t>>(
                &mut self,
                _binder: Binder<'t, T>,
            ) -> Binder<'t, T> {
                unreachable!("binders in types are not supported");
            }
        }
        *DeeplyResolve { infcx: self }.fold_term(&*self.tcx().arena.alloc(t))
    }

    pub fn eq(
        &mut self,
        a: Term<'t>,
        b: Term<'t>,
        bounds: Bounds<'t>,
    ) -> Result<Vec<Goal<'t>>, NoSolution> {
        let mut eq = Equate {
            infcx: self,
            bounds,
            goals: vec![],
        };
        match eq.eq(a, b) {
            Err(NoSolution) => Err(NoSolution),
            Ok(_) => Ok(eq.goals),
        }
    }
}

struct Generalizer<'a, 't> {
    infcx: &'a mut InferCtxt<'t>,
    var: InferId,

    in_alias: bool,
}
impl<'a, 't> Generalizer<'a, 't> {
    fn new(infcx: &'a mut InferCtxt<'t>, var: InferId) -> Self {
        assert_eq!(
            infcx.shallow_resolve_term(Term::Infer(var)),
            Term::Infer(var)
        );

        Self {
            infcx,
            var,
            in_alias: false,
        }
    }
}
impl<'t> FallibleTermFolder<'t> for Generalizer<'_, 't> {
    type Error = ();

    fn tcx(&self) -> &'t TirCtx<'t> {
        self.infcx.tcx()
    }

    fn try_fold_term(&mut self, t: &'t Term<'t>) -> Result<&'t Term<'t>, ()> {
        let t = self.infcx.shallow_resolve_term(*t);

        match t {
            // FIXME(universes)
            Term::Infer(var) => {
                if self.var == var {
                    return Err(());
                } else {
                    Ok(self
                        .infcx
                        .tcx()
                        .arena
                        .alloc(Term::Infer(self.infcx.new_var(Span::new(0..0)))))
                }
            }

            Term::Alias(id, args) => {
                let old_in_alias = self.in_alias;
                self.in_alias = true;
                let r = match args.try_fold_with(self) {
                    Ok(args) => Ok(&*self.infcx.tcx().arena.alloc(Term::Alias(id, args))),
                    Err(_) if self.in_alias == false => Ok(&*self
                        .infcx
                        .tcx()
                        .arena
                        .alloc(Term::Infer(self.infcx.new_var(Span::new(0..0))))),
                    Err(_) => Err(()),
                };
                self.in_alias = old_in_alias;
                r
            }
            // FIXME(universes)
            Term::Placeholder(_, _)
            | Term::Bound(_, _)
            | Term::FnDef(_, _)
            | Term::Adt(_, _)
            | Term::Unit
            | Term::IntTy
            | Term::FloatTy
            | Term::Error
            | _ => (self.infcx.tcx().arena.alloc(t)).try_super_fold_with(self),
        }
    }

    fn try_fold_binder<T: TermFoldable<'t>>(
        &mut self,
        _binder: Binder<'t, T>,
    ) -> Result<Binder<'t, T>, Self::Error> {
        unreachable!("binders in types are not supported");
    }
}

struct Equate<'a, 't> {
    infcx: &'a mut InferCtxt<'t>,
    bounds: Bounds<'t>,
    goals: Vec<Goal<'t>>,
}
impl<'a, 't> Equate<'a, 't> {
    fn eq(&mut self, a: Term<'t>, b: Term<'t>) -> Result<(), NoSolution> {
        let a = self.infcx.shallow_resolve_term(a);
        let b = self.infcx.shallow_resolve_term(b);

        let instantiate = |equate: &mut Equate<'a, 't>, var: InferId, with: Term<'t>| {
            let tcx: &TirCtx<'_> = equate.infcx.tcx();
            match Generalizer::new(equate.infcx, var).try_fold_term(tcx.arena.alloc(with)) {
                Ok(new_a) => {
                    equate.infcx.instantiate_var(var, new_a);
                    equate.eq(*new_a, with)
                }
                Err(()) => Err(NoSolution),
            }
        };

        match (a, b) {
            (Term::Error, _) | (_, Term::Error) => Ok(()),

            (Term::Infer(a), Term::Infer(b)) => match a == b {
                true => Ok(()),
                false => {
                    self.infcx.unify_vars(a, b);
                    Ok(())
                }
            },

            // FIXME: universe errors
            (Term::Infer(var), ty) | (ty, Term::Infer(var)) => instantiate(self, var, ty),

            (alias @ Term::Alias(_, _), ty) | (ty, alias @ Term::Alias(_, _)) => {
                self.goals.push(Goal {
                    bounds: self.bounds,
                    kind: Binder::dummy(
                        self.infcx.tcx,
                        GoalKind::Equate(
                            self.infcx.tcx.arena.alloc(alias),
                            self.infcx.tcx.arena.alloc(ty),
                        ),
                    ),
                });
                Ok(())
            }

            (
                Term::Placeholder(_, _) | Term::IntTy | Term::FloatTy | Term::Unit,
                Term::Placeholder(_, _) | Term::IntTy | Term::FloatTy | Term::Unit,
            ) => match a == b {
                true => Ok(()),
                false => Err(NoSolution),
            },
            (
                Term::FnDef(a_id, a_args) | Term::Adt(a_id, a_args),
                Term::FnDef(b_id, b_args) | Term::Adt(b_id, b_args),
            ) if a_id == b_id => {
                for (a_arg, b_arg) in a_args.0.iter().zip(b_args.0.iter()) {
                    self.eq(**a_arg, **b_arg)?;
                }
                Ok(())
            }
            (Term::FnDef(_, _) | Term::Adt(_, _), _) | (_, Term::FnDef(_, _) | Term::Adt(_, _)) => {
                Err(NoSolution)
            }
            (Term::Bound(_, _), _) | (_, Term::Bound(_, _)) => unreachable!(),
            _ => todo!(), // expr terms now can be eq'd
        }
    }
}
