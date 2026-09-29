//! What a solver can conclude about a formula.
//!
//! Two of the three answers are conclusions and one is the absence of one.
//! [`SatResult::Sat`] carries a model, so it is self-certifying: the caller can
//! check it. [`SatResult::Unsat`] claims no model exists. [`SatResult::Unknown`]
//! claims nothing at all -- the search gave up before deciding, and the formula
//! may be satisfiable or not.
//!
//! The third answer exists so that a solver whose counters are finite can stop
//! rather than overflow. `sat_cdcl` counts conflicts in a `u32`; a run that
//! exhausts it has to say *something*, and neither `Sat` nor `Unsat` would be
//! true. Folding it into `Unsat` -- the shape `Option<Model>` forces -- would
//! have the solver call a satisfiable formula unsatisfiable, which is exactly
//! the failure the soundness theorem is there to rule out.

/// The three answers, over whatever a model is represented by: a `Map` at the
/// `Expr` layer, a vector of assignments at the CNF layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatResult<T> {
    /// A model, which the caller can check against the formula.
    Sat(T),
    /// No model exists.
    Unsat,
    /// The search stopped without deciding.
    Unknown,
}
