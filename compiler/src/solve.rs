pub mod canonical;

use crate::tir::{Binder, Bounds, GenArgs, Term, TirId};

pub use canonical::*;

pub struct Goal<'t> {
    pub bounds: Bounds<'t>,
    pub kind: Binder<'t, GoalKind<'t>>,
}

pub enum GoalKind<'t> {
    WellFormed(&'t Term<'t>),
    StructurallyNorm(TirId, GenArgs<'t>, &'t Term<'t>),
    Equate(&'t Term<'t>, &'t Term<'t>),
    Trait(TirId, GenArgs<'t>),
}

#[derive(Debug)]
pub struct NoSolution;
