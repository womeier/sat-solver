#![allow(dead_code)]
use crate::cnf::{Clause, Cnf, Literal};
#[cfg(test)]
use crate::expr::letter;
use crate::expr::{Expr, Map, collect_vars};
use crate::sat::SatSolver;
use crate::sat_naive::initial_valuation;
use crate::{cnf_transform_hybrid, cnf_transform_naive, cnf_transform_tseitin};

// A CNF with no clauses left is trivially satisfied: every original clause has
// been discharged by the partial assignment built so far.
fn is_satisfied(cnf: &Cnf) -> bool {
    cnf.0.is_empty()
}

// An empty clause has no literal left that could make it true, so a CNF
// containing one is a conflict -- this is how `assign_cnf` signals that the
// current partial assignment falsified a clause outright.
fn has_empty_clause(cnf: &Cnf) -> bool {
    for clause in cnf.0.iter() {
        if clause.0.is_empty() {
            return true;
        }
    }
    false
}

// Unit propagation: a clause with exactly one literal left forces that
// literal's polarity, with no choice (and no backtracking point) involved.
// Returns the literal by value rather than by reference, since the caller
// builds a new CNF from `cnf` right after.
fn find_unit_literal(cnf: &Cnf) -> Option<Literal> {
    for clause in cnf.0.iter() {
        if clause.0.len() == 1 {
            return Some(clause.0[0].clone());
        }
    }
    None
}

// Decision heuristic: the first variable occurring anywhere in `cnf`. Any
// choice whatsoever is sound and complete -- both branches are tried -- so this
// first version picks the cheapest one. (Returns `None` only for a CNF whose
// every clause is empty; the search rules that out via `has_empty_clause`
// before ever asking.)
fn find_branch_var(cnf: &Cnf) -> Option<u16> {
    for clause in cnf.0.iter() {
        if !clause.0.is_empty() {
            return Some(clause.0[0].var);
        }
    }
    None
}

// Simplifies one clause under `var := value`. A literal of `var` whose polarity
// agrees with `value` makes the whole clause true, so the clause disappears
// (`None`); one that disagrees is false and simply drops out of the clause. A
// clause consisting only of such false literals shrinks to the empty clause.
fn assign_clause(clause: &Clause, var: u16, value: bool) -> Option<Clause> {
    let mut lits = Vec::new();
    for lit in clause.0.iter() {
        if lit.var == var {
            // `lit` is true under `var := value` exactly when its polarity
            // disagrees with `negated`.
            if lit.negated != value {
                return None;
            }
        } else {
            lits.push(lit.clone());
        }
    }
    Some(Clause(lits))
}

// Simplifies the whole CNF under `var := value`. The result mentions `var`
// nowhere, which is what makes the search terminate (one variable fewer per
// level) and what makes the assignment stable: no deeper call can ever revisit
// a variable an outer level already decided.
fn assign_cnf(cnf: &Cnf, var: u16, value: bool) -> Cnf {
    let mut clauses = Vec::new();
    for clause in cnf.0.iter() {
        if let Some(c) = assign_clause(clause, var, value) {
            clauses.push(c);
        }
    }
    Cnf(clauses)
}

// The DPLL search proper: propagate units while any exist, otherwise split on a
// variable and try `true` before `false`.
//
// `val` is threaded mutably through the entire search, so a failed branch
// leaves its decisions behind as stale entries. That is harmless, and
// deliberately not cleaned up: a successful leaf has an *empty* residual CNF,
// i.e. every clause was already satisfied by the literals decided on the path
// to that leaf, and those are exactly the entries the successful path wrote
// last (each decided variable vanishes from the CNF, so no deeper call
// overwrites it). Variables left undecided keep whatever `val` happened to hold
// -- any value satisfies the formula.
fn dpll(cnf: &Cnf, val: &mut Map) -> bool {
    if is_satisfied(cnf) {
        return true;
    }
    if has_empty_clause(cnf) {
        return false;
    }

    if let Some(lit) = find_unit_literal(cnf) {
        let value = !lit.negated;
        val.insert(lit.var, value);
        return dpll(&assign_cnf(cnf, lit.var, value), val);
    }

    match find_branch_var(cnf) {
        Some(v) => {
            val.insert(v, true);
            if dpll(&assign_cnf(cnf, v, true), val) {
                return true;
            }

            val.insert(v, false);
            dpll(&assign_cnf(cnf, v, false), val)
        }
        // Unreachable: a CNF that is neither empty nor holds an empty clause has
        // a literal, hence a variable.
        None => false,
    }
}

/// Which CNF transformation the search runs on.
///
/// All three are interchangeable as far as the *verdict* goes -- `solve_sat_with`
/// returns the same satisfiability answer whichever is picked, and a `Some` model
/// always satisfies the original `expr`. They differ only in the CNF that DPLL
/// has to search, and the difference is large in both directions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Transform {
    /// Distribute OR over AND ([`cnf_transform_naive`]). Worst-case
    /// exponential, but a near no-op on input that is already in CNF -- which is
    /// everything `dimacs` reads. Logically *equivalent* to `expr` rather than
    /// merely equisatisfiable, which is what makes it the cheapest arm to state
    /// correct: it introduces no variable, so `Cnf.lean` can prove
    /// `eval_cnf (to_cnf e) v = evaluate e v` at a fixed valuation.
    Naive,
    /// Name every internal node with a gate variable ([`cnf_transform_tseitin`]).
    /// Linear in the size of `expr`, which is the only way to get through a
    /// deeply nested non-clausal formula at all -- but it names nodes whether or
    /// not they needed naming, so on an already-clausal input it is pure
    /// overhead: a uf50-218 instance goes from 218 clauses over 50 variables to
    /// 1960 over 703, and DPLL then branches on gate variables that are in fact
    /// determined by the original ones.
    Tseitin,
    /// Distribute where that is cheap, name only where it is not
    /// ([`cnf_transform_hybrid`]). Reproduces `Naive` exactly on already-clausal
    /// input -- same CNF, clause for clause -- while staying linear on the
    /// formulas that make `Naive` blow up. It dominates the other two, and is
    /// the default.
    Hybrid,
}

// The CNF the search actually runs on.
fn encode(expr: &Expr, transform: Transform) -> Cnf {
    match transform {
        Transform::Naive => cnf_transform_naive::to_cnf(expr),
        Transform::Tseitin => match cnf_transform_tseitin::to_cnf(expr) {
            Ok(cnf) => cnf,
            // Out of `u16` room to name gates: reachable only for a formula
            // with more internal nodes than there are variable indices left
            // above its largest variable. Falling back costs less than it looks
            // like -- an input that large comes from `dimacs`, whose `Expr` is
            // already in CNF, and on those the naive transformation's
            // distribution step never fires.
            Err(()) => cnf_transform_naive::to_cnf(expr),
        },
        Transform::Hybrid => match cnf_transform_hybrid::to_cnf(expr) {
            Ok(cnf) => cnf,
            // Same fallback, and rarer still: only the subformulas that
            // actually needed naming consume a variable index.
            Err(()) => cnf_transform_naive::to_cnf(expr),
        },
    }
}

// Adds every variable the CNF mentions to `val`, set to false.
//
// `initial_valuation` covers the variables of the `Expr`, which is what the
// caller needs to be able to `evaluate` the returned map -- but it is not all
// the search will touch. A transformation that names subformulas
// (`cnf_transform_tseitin`, `cnf_transform_hybrid`) puts gate variables in the
// CNF that `collect_vars` of the original `Expr` has never heard of, and `dpll`
// has to start from a map that already covers every variable it can branch on:
// a variable it decides but cannot record is one the returned model would be
// silently missing.
//
// Called immediately after `initial_valuation`, where every variable present is
// false already, so inserting `false` unconditionally clobbers nothing -- and
// for `Transform::Naive`, whose CNF mentions no variable outside `expr`, it
// leaves the map exactly as it found it.
fn seed_cnf_vars(cnf: &Cnf, val: &mut Map) {
    for clause in cnf.0.iter() {
        for lit in clause.0.iter() {
            val.insert(lit.var, false);
        }
    }
}

pub fn solve_sat_with(expr: &Expr, transform: Transform) -> Option<Map> {
    let vars = collect_vars(expr);
    // Start from a *total* valuation (all false), not an empty map: callers get
    // a map `evaluate` can actually run on (it errors on an incomplete one), and
    // the search is free to leave variables undecided.
    let mut val = initial_valuation(&vars);
    let cnf = encode(expr, transform);
    seed_cnf_vars(&cnf, &mut val);

    if dpll(&cnf, &mut val) {
        Some(val)
    } else {
        None
    }
}

/// DPLL on the default ([`Transform::Hybrid`]) encoding. This is the signature
/// `SatSolver` wants, and the one the Lean proofs are stated about.
pub fn solve_sat(expr: &Expr) -> Option<Map> {
    solve_sat_with(expr, Transform::Hybrid)
}

/// DPLL on the naive encoding, as a plain `fn(&Expr) -> Option<Map>` so it can
/// sit in a [`SatSolver`] next to the default one and be benchmarked against it.
pub fn solve_sat_naive(expr: &Expr) -> Option<Map> {
    solve_sat_with(expr, Transform::Naive)
}

/// DPLL on the Tseitin encoding, likewise shaped for a [`SatSolver`].
pub fn solve_sat_tseitin(expr: &Expr) -> Option<Map> {
    solve_sat_with(expr, Transform::Tseitin)
}

/// DPLL on the hybrid encoding -- the same search `solve_sat` runs, exported
/// under its own name so the benchmark harness can label it.
pub fn solve_sat_hybrid(expr: &Expr) -> Option<Map> {
    solve_sat_with(expr, Transform::Hybrid)
}

pub static SAT_SOLVER_DPLL: SatSolver = SatSolver {
    solve: solve_sat,
    description: "dpll",
};

pub static SAT_SOLVER_DPLL_NAIVE: SatSolver = SatSolver {
    solve: solve_sat_naive,
    description: "dpll-naive",
};

pub static SAT_SOLVER_DPLL_TSEITIN: SatSolver = SatSolver {
    solve: solve_sat_tseitin,
    description: "dpll-tseitin",
};

pub static SAT_SOLVER_DPLL_HYBRID: SatSolver = SatSolver {
    solve: solve_sat_hybrid,
    description: "dpll-hybrid",
};

#[cfg(test)]
fn lit(var: u16, negated: bool) -> Literal {
    Literal { var, negated }
}

#[test]
fn is_satisfied_only_for_the_empty_cnf() {
    assert!(is_satisfied(&Cnf(Vec::new())));
    assert!(!is_satisfied(&Cnf(vec![Clause(Vec::new())])));
    assert!(!is_satisfied(&Cnf(vec![Clause(vec![lit(
        letter('x'),
        false
    )])])));
}

#[test]
fn has_empty_clause_finds_a_conflict_anywhere() {
    assert!(!has_empty_clause(&Cnf(Vec::new())));
    assert!(has_empty_clause(&Cnf(vec![
        Clause(vec![lit(letter('x'), false)]),
        Clause(Vec::new()),
    ])));
    assert!(!has_empty_clause(&Cnf(vec![Clause(vec![lit(
        letter('x'),
        false
    )])])));
}

#[test]
fn find_unit_literal_returns_the_first_singleton_clause() {
    let cnf = Cnf(vec![
        Clause(vec![lit(letter('x'), false), lit(letter('y'), false)]),
        Clause(vec![lit(letter('z'), true)]),
        Clause(vec![lit(letter('w'), false)]),
    ]);
    assert_eq!(find_unit_literal(&cnf), Some(lit(letter('z'), true)));
}

#[test]
fn find_unit_literal_none_when_every_clause_is_longer() {
    let cnf = Cnf(vec![
        Clause(Vec::new()),
        Clause(vec![lit(letter('x'), false), lit(letter('y'), false)]),
    ]);
    assert_eq!(find_unit_literal(&cnf), None);
}

#[test]
fn find_branch_var_skips_empty_clauses() {
    let cnf = Cnf(vec![
        Clause(Vec::new()),
        Clause(vec![lit(letter('y'), true), lit(letter('x'), false)]),
    ]);
    assert_eq!(find_branch_var(&cnf), Some(letter('y')));
    assert_eq!(find_branch_var(&Cnf(vec![Clause(Vec::new())])), None);
}

#[test]
fn assign_clause_drops_a_satisfied_clause() {
    // (x ∨ y) under x := true is satisfied outright.
    let clause = Clause(vec![lit(letter('x'), false), lit(letter('y'), false)]);
    assert_eq!(assign_clause(&clause, letter('x'), true), None);
    // (¬x ∨ y) under x := false, likewise.
    let clause = Clause(vec![lit(letter('x'), true), lit(letter('y'), false)]);
    assert_eq!(assign_clause(&clause, letter('x'), false), None);
}

#[test]
fn assign_clause_removes_false_literals() {
    // (x ∨ y) under x := false shrinks to (y).
    let clause = Clause(vec![lit(letter('x'), false), lit(letter('y'), false)]);
    assert_eq!(
        assign_clause(&clause, letter('x'), false),
        Some(Clause(vec![lit(letter('y'), false)]))
    );
    // (x) under x := false becomes the empty (conflicting) clause.
    let clause = Clause(vec![lit(letter('x'), false)]);
    assert_eq!(
        assign_clause(&clause, letter('x'), false),
        Some(Clause(Vec::new()))
    );
}

#[test]
fn assign_clause_leaves_unrelated_clauses_alone() {
    let clause = Clause(vec![lit(letter('y'), false), lit(letter('z'), true)]);
    assert_eq!(
        assign_clause(&clause, letter('x'), true),
        Some(clause.clone())
    );
}

#[test]
fn assign_cnf_simplifies_every_clause() {
    // (x ∨ y) ∧ (¬x ∨ z) ∧ (y ∨ z) under x := true keeps the last two clauses,
    // with ¬x dropped from the second.
    let cnf = Cnf(vec![
        Clause(vec![lit(letter('x'), false), lit(letter('y'), false)]),
        Clause(vec![lit(letter('x'), true), lit(letter('z'), false)]),
        Clause(vec![lit(letter('y'), false), lit(letter('z'), false)]),
    ]);
    assert_eq!(
        assign_cnf(&cnf, letter('x'), true),
        Cnf(vec![
            Clause(vec![lit(letter('z'), false)]),
            Clause(vec![lit(letter('y'), false), lit(letter('z'), false)]),
        ])
    );
}

#[test]
fn assign_cnf_mentions_the_assigned_variable_nowhere() {
    let cnf = Cnf(vec![
        Clause(vec![lit(letter('x'), false), lit(letter('y'), false)]),
        Clause(vec![lit(letter('x'), true), lit(letter('x'), false)]),
    ]);
    for value in [true, false] {
        let Cnf(clauses) = assign_cnf(&cnf, letter('x'), value);
        for Clause(lits) in clauses {
            for l in lits {
                assert_ne!(l.var, letter('x'));
            }
        }
    }
}

#[test]
fn dpll_propagates_units_to_a_conflict() {
    // (x) ∧ (¬x) is unsatisfiable, and pure unit propagation finds it.
    let cnf = Cnf(vec![
        Clause(vec![lit(letter('x'), false)]),
        Clause(vec![lit(letter('x'), true)]),
    ]);
    let mut val = Map::new();
    assert!(!dpll(&cnf, &mut val));
}

#[test]
fn dpll_finds_an_assignment_that_needs_backtracking() {
    // (x ∨ y) ∧ (¬x) forces x := false via the second clause, then y := true.
    let cnf = Cnf(vec![
        Clause(vec![lit(letter('x'), false), lit(letter('y'), false)]),
        Clause(vec![lit(letter('x'), true)]),
    ]);
    let mut val = Map::new();
    assert!(dpll(&cnf, &mut val));
    assert_eq!(val.get(&letter('x')), Some(false));
    assert_eq!(val.get(&letter('y')), Some(true));
}

#[test]
fn solve_sat_agrees_with_the_naive_solver_on_the_examples() {
    use crate::expr::{evaluate, example_expr_sat, example_expr_unsat};

    for transform in [Transform::Naive, Transform::Tseitin, Transform::Hybrid] {
        let sat = example_expr_sat();
        let val = solve_sat_with(&sat, transform).expect("example_expr_sat is satisfiable");
        // The returned valuation must cover every variable (so `evaluate` can
        // run at all) and actually satisfy the formula. Under `Tseitin` it also
        // carries gate variables, which `evaluate` simply never reads.
        assert_eq!(evaluate(&sat, &val), Ok(true), "{transform:?}");

        assert_eq!(
            solve_sat_with(&example_expr_unsat(), transform),
            None,
            "{transform:?}"
        );
    }
}

#[test]
fn solve_sat_matches_the_naive_solver_exhaustively() {
    use crate::expr::parse_expr;

    // Same satisfiability verdict as the (proved-correct) naive solver on a
    // handful of formulas exercising negation, backtracking and the
    // variable-free edge case.
    for src in [
        "T",
        "F",
        "x",
        "~x",
        "(x & ~x)",
        "(x | ~x)",
        "((x | y) & (~x | ~y))",
        "((x & y) | (~x & ~y))",
        "~(~x & ~(y | z))",
        "((x | y) & ((~x | z) & (~y | ~z)))",
    ] {
        let expr = parse_expr(src).unwrap().1;
        let naive_res = crate::sat_naive::solve_sat(&expr);
        // Both encodings have to reach the same verdict, and any model either
        // of them returns has to satisfy the original formula.
        for transform in [Transform::Naive, Transform::Tseitin, Transform::Hybrid] {
            let dpll_res = solve_sat_with(&expr, transform);
            assert_eq!(
                dpll_res.is_some(),
                naive_res.is_some(),
                "disagreement on {src} under {transform:?}"
            );
            if let Some(val) = dpll_res {
                assert_eq!(
                    crate::expr::evaluate(&expr, &val),
                    Ok(true),
                    "bad witness for {src} under {transform:?}"
                );
            }
        }
    }
}

#[test]
fn the_default_transform_is_the_hybrid_one() {
    // What keeps the SATLIB numbers (and the Lean theorems) about `solve_sat`
    // honest: the exported entry point must be the hybrid arm, not one of the
    // other two.
    use crate::expr::parse_expr;

    let expr = parse_expr("((x | y) & ((~x | z) & (~y | ~z)))").unwrap().1;
    assert_eq!(
        solve_sat(&expr),
        solve_sat_with(&expr, Transform::Hybrid),
        "solve_sat must agree with Transform::Hybrid exactly, model included"
    );
    // Tseitin really is a different object, so the assertion above is not
    // vacuous...
    assert_ne!(
        encode(&expr, Transform::Naive),
        encode(&expr, Transform::Tseitin)
    );
    // ...while the naive arm deliberately *is* identical here: the formula is
    // already clausal, so the hybrid's rule never names anything, which is why
    // changing the default cost the SATLIB numbers nothing.
    assert_eq!(
        encode(&expr, Transform::Naive),
        encode(&expr, Transform::Hybrid)
    );
}
