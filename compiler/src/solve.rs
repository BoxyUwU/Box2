pub mod canonical;

use crate::tir::{Binder, Bounds, GenArgs, TirId, Ty};

pub use canonical::*;

pub struct Goal<'t> {
    pub bounds: Bounds<'t>,
    pub kind: Binder<'t, GoalKind<'t>>,
}

pub enum GoalKind<'t> {
    WellFormed(&'t Ty<'t>),
    StructurallyNorm(TirId, GenArgs<'t>, &'t Ty<'t>),
    Equate(&'t Ty<'t>, &'t Ty<'t>),
    Trait(TirId, GenArgs<'t>),
}

#[derive(Debug)]
pub struct NoSolution;
