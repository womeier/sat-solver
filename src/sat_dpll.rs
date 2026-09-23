#![allow(dead_code)]
use crate::cnf::{Clause, Cnf, Literal, to_cnf};
use crate::expr::{Expr, Map, collect_vars};
use crate::sat::SatSolver;
use crate::sat_naive::initial_valuation;

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
fn find_branch_var(cnf: &Cnf) -> Option<u8> {
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
fn assign_clause(clause: &Clause, var: u8, value: bool) -> Option<Clause> {
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
fn assign_cnf(cnf: &Cnf, var: u8, value: bool) -> Cnf {
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

pub fn solve_sat(expr: &Expr) -> Option<Map> {
    let vars = collect_vars(expr);
    // Start from a *total* valuation over `expr`'s variables (all false), not an
    // empty map: callers get a map `evaluate` can actually run on (it errors on
    // an incomplete one), and the search is free to leave variables undecided.
    let mut val = initial_valuation(&vars);
    let cnf = to_cnf(expr);

    if dpll(&cnf, &mut val) {
        Some(val)
    } else {
        None
    }
}

pub static SAT_SOLVER_DPLL: SatSolver = SatSolver {
    solve: solve_sat,
    description: "dpll",
};

#[cfg(test)]
fn lit(var: u8, negated: bool) -> Literal {
    Literal { var, negated }
}

#[test]
fn is_satisfied_only_for_the_empty_cnf() {
    assert!(is_satisfied(&Cnf(Vec::new())));
    assert!(!is_satisfied(&Cnf(vec![Clause(Vec::new())])));
    assert!(!is_satisfied(&Cnf(vec![Clause(vec![lit(b'x', false)])])));
}

#[test]
fn has_empty_clause_finds_a_conflict_anywhere() {
    assert!(!has_empty_clause(&Cnf(Vec::new())));
    assert!(has_empty_clause(&Cnf(vec![
        Clause(vec![lit(b'x', false)]),
        Clause(Vec::new()),
    ])));
    assert!(!has_empty_clause(&Cnf(vec![Clause(vec![lit(
        b'x', false
    )])])));
}

#[test]
fn find_unit_literal_returns_the_first_singleton_clause() {
    let cnf = Cnf(vec![
        Clause(vec![lit(b'x', false), lit(b'y', false)]),
        Clause(vec![lit(b'z', true)]),
        Clause(vec![lit(b'w', false)]),
    ]);
    assert_eq!(find_unit_literal(&cnf), Some(lit(b'z', true)));
}

#[test]
fn find_unit_literal_none_when_every_clause_is_longer() {
    let cnf = Cnf(vec![
        Clause(Vec::new()),
        Clause(vec![lit(b'x', false), lit(b'y', false)]),
    ]);
    assert_eq!(find_unit_literal(&cnf), None);
}

#[test]
fn find_branch_var_skips_empty_clauses() {
    let cnf = Cnf(vec![
        Clause(Vec::new()),
        Clause(vec![lit(b'y', true), lit(b'x', false)]),
    ]);
    assert_eq!(find_branch_var(&cnf), Some(b'y'));
    assert_eq!(find_branch_var(&Cnf(vec![Clause(Vec::new())])), None);
}

#[test]
fn assign_clause_drops_a_satisfied_clause() {
    // (x ∨ y) under x := true is satisfied outright.
    let clause = Clause(vec![lit(b'x', false), lit(b'y', false)]);
    assert_eq!(assign_clause(&clause, b'x', true), None);
    // (¬x ∨ y) under x := false, likewise.
    let clause = Clause(vec![lit(b'x', true), lit(b'y', false)]);
    assert_eq!(assign_clause(&clause, b'x', false), None);
}

#[test]
fn assign_clause_removes_false_literals() {
    // (x ∨ y) under x := false shrinks to (y).
    let clause = Clause(vec![lit(b'x', false), lit(b'y', false)]);
    assert_eq!(
        assign_clause(&clause, b'x', false),
        Some(Clause(vec![lit(b'y', false)]))
    );
    // (x) under x := false becomes the empty (conflicting) clause.
    let clause = Clause(vec![lit(b'x', false)]);
    assert_eq!(
        assign_clause(&clause, b'x', false),
        Some(Clause(Vec::new()))
    );
}

#[test]
fn assign_clause_leaves_unrelated_clauses_alone() {
    let clause = Clause(vec![lit(b'y', false), lit(b'z', true)]);
    assert_eq!(assign_clause(&clause, b'x', true), Some(clause.clone()));
}

#[test]
fn assign_cnf_simplifies_every_clause() {
    // (x ∨ y) ∧ (¬x ∨ z) ∧ (y ∨ z) under x := true keeps the last two clauses,
    // with ¬x dropped from the second.
    let cnf = Cnf(vec![
        Clause(vec![lit(b'x', false), lit(b'y', false)]),
        Clause(vec![lit(b'x', true), lit(b'z', false)]),
        Clause(vec![lit(b'y', false), lit(b'z', false)]),
    ]);
    assert_eq!(
        assign_cnf(&cnf, b'x', true),
        Cnf(vec![
            Clause(vec![lit(b'z', false)]),
            Clause(vec![lit(b'y', false), lit(b'z', false)]),
        ])
    );
}

#[test]
fn assign_cnf_mentions_the_assigned_variable_nowhere() {
    let cnf = Cnf(vec![
        Clause(vec![lit(b'x', false), lit(b'y', false)]),
        Clause(vec![lit(b'x', true), lit(b'x', false)]),
    ]);
    for value in [true, false] {
        let Cnf(clauses) = assign_cnf(&cnf, b'x', value);
        for Clause(lits) in clauses {
            for l in lits {
                assert_ne!(l.var, b'x');
            }
        }
    }
}

#[test]
fn dpll_propagates_units_to_a_conflict() {
    // (x) ∧ (¬x) is unsatisfiable, and pure unit propagation finds it.
    let cnf = Cnf(vec![
        Clause(vec![lit(b'x', false)]),
        Clause(vec![lit(b'x', true)]),
    ]);
    let mut val = Map::new();
    assert!(!dpll(&cnf, &mut val));
}

#[test]
fn dpll_finds_an_assignment_that_needs_backtracking() {
    // (x ∨ y) ∧ (¬x) forces x := false via the second clause, then y := true.
    let cnf = Cnf(vec![
        Clause(vec![lit(b'x', false), lit(b'y', false)]),
        Clause(vec![lit(b'x', true)]),
    ]);
    let mut val = Map::new();
    assert!(dpll(&cnf, &mut val));
    assert_eq!(val.get(&b'x'), Some(&false));
    assert_eq!(val.get(&b'y'), Some(&true));
}

#[test]
fn solve_sat_agrees_with_the_naive_solver_on_the_examples() {
    use crate::expr::{evaluate, example_expr_sat, example_expr_unsat};

    let sat = example_expr_sat();
    let val = solve_sat(&sat).expect("example_expr_sat is satisfiable");
    // The returned valuation must cover every variable (so `evaluate` can run at
    // all) and actually satisfy the formula.
    assert_eq!(evaluate(&sat, &val), Ok(true));

    assert_eq!(solve_sat(&example_expr_unsat()), None);
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
        let dpll_res = solve_sat(&expr);
        let naive_res = crate::sat_naive::solve_sat(&expr);
        assert_eq!(
            dpll_res.is_some(),
            naive_res.is_some(),
            "disagreement on {src}"
        );
        if let Some(val) = dpll_res {
            assert_eq!(
                crate::expr::evaluate(&expr, &val),
                Ok(true),
                "bad witness for {src}"
            );
        }
    }
}
