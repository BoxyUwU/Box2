use crate::tir::{Bounds, GenArgs, TirId, Ty};

pub struct Goal<'t> {
    pub bounds: Bounds<'t>,
    pub kind: GoalKind<'t>,
}

pub enum GoalKind<'t> {
    WellFormed(Ty<'t>),
    NormalizesTo(TirId, GenArgs<'t>, Ty<'t>),
    Equate(Ty<'t>, Ty<'t>),
    Trait(TirId, GenArgs<'t>),
}

pub struct NoSolution;
