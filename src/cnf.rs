#![allow(dead_code)]
//! The CNF representation and its evaluator. The transformations that *build* a
//! `Cnf` from an `Expr` live in the sibling modules
//! [`crate::cnf_transform_naive`] and [`crate::cnf_transform_tseitin`].

use crate::expr::Map;
#[cfg(test)]
use crate::expr::letter;

// Fields are public so that the transformations that build a CNF, and the
// solvers that take one apart (`sat_dpll`), can both reach the literals.
#[derive(Debug, Clone, PartialEq)]
pub struct Literal {
    pub var: u16,
    pub negated: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Clause(pub Vec<Literal>);

#[derive(Debug, Clone, PartialEq)]
pub struct Cnf(pub Vec<Clause>);

// Evaluation, mirroring `expr::evaluate`'s Result<bool, ()> style (Err on an
// incomplete valuation).

fn eval_literal(lit: &Literal, valuation: &Map) -> Result<bool, ()> {
    match valuation.get(&lit.var) {
        Some(b) => Ok(if lit.negated { !b } else { b }),
        None => Err(()),
    }
}

fn eval_clause(clause: &Clause, valuation: &Map) -> Result<bool, ()> {
    for lit in clause.0.iter() {
        if eval_literal(lit, valuation)? {
            return Ok(true);
        }
    }
    Ok(false)
}

pub fn eval_cnf(cnf: &Cnf, valuation: &Map) -> Result<bool, ()> {
    for clause in cnf.0.iter() {
        if !eval_clause(clause, valuation)? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[test]
fn eval_literal_reads_and_negates() {
    let mut valuation = Map::new();
    valuation.insert(letter('x'), true);
    let pos = Literal {
        var: letter('x'),
        negated: false,
    };
    let neg = Literal {
        var: letter('x'),
        negated: true,
    };
    assert_eq!(eval_literal(&pos, &valuation), Ok(true));
    assert_eq!(eval_literal(&neg, &valuation), Ok(false));
}

#[test]
fn eval_literal_missing_variable_errs() {
    let valuation = Map::new();
    let lit = Literal {
        var: letter('x'),
        negated: false,
    };
    assert_eq!(eval_literal(&lit, &valuation), Err(()));
}

#[test]
fn eval_clause_true_if_any_literal_true() {
    let mut valuation = Map::new();
    valuation.insert(letter('x'), false);
    valuation.insert(letter('y'), true);
    let clause = Clause(vec![
        Literal {
            var: letter('x'),
            negated: false,
        },
        Literal {
            var: letter('y'),
            negated: false,
        },
    ]);
    assert_eq!(eval_clause(&clause, &valuation), Ok(true));
}

#[test]
fn eval_clause_false_if_all_literals_false() {
    let mut valuation = Map::new();
    valuation.insert(letter('x'), false);
    valuation.insert(letter('y'), false);
    let clause = Clause(vec![
        Literal {
            var: letter('x'),
            negated: false,
        },
        Literal {
            var: letter('y'),
            negated: false,
        },
    ]);
    assert_eq!(eval_clause(&clause, &valuation), Ok(false));
}

#[test]
fn eval_clause_short_circuits_before_a_missing_variable() {
    // The first literal is already satisfied, so `y` (absent from the
    // valuation) should never be looked up.
    let mut valuation = Map::new();
    valuation.insert(letter('x'), true);
    let clause = Clause(vec![
        Literal {
            var: letter('x'),
            negated: false,
        },
        Literal {
            var: letter('y'),
            negated: false,
        },
    ]);
    assert_eq!(eval_clause(&clause, &valuation), Ok(true));
}

#[test]
fn eval_clause_errs_on_missing_variable() {
    let valuation = Map::new();
    let clause = Clause(vec![Literal {
        var: letter('x'),
        negated: false,
    }]);
    assert_eq!(eval_clause(&clause, &valuation), Err(()));
}

#[test]
fn eval_cnf_true_when_every_clause_true() {
    let mut valuation = Map::new();
    valuation.insert(letter('x'), true);
    valuation.insert(letter('y'), true);
    let cnf = Cnf(vec![
        Clause(vec![Literal {
            var: letter('x'),
            negated: false,
        }]),
        Clause(vec![Literal {
            var: letter('y'),
            negated: false,
        }]),
    ]);
    assert_eq!(eval_cnf(&cnf, &valuation), Ok(true));
}

#[test]
fn eval_cnf_false_when_some_clause_false() {
    let mut valuation = Map::new();
    valuation.insert(letter('x'), true);
    valuation.insert(letter('y'), false);
    let cnf = Cnf(vec![
        Clause(vec![Literal {
            var: letter('x'),
            negated: false,
        }]),
        Clause(vec![Literal {
            var: letter('y'),
            negated: false,
        }]),
    ]);
    assert_eq!(eval_cnf(&cnf, &valuation), Ok(false));
}

#[test]
fn eval_cnf_errs_on_missing_variable() {
    let valuation = Map::new();
    let cnf = Cnf(vec![Clause(vec![Literal {
        var: letter('x'),
        negated: false,
    }])]);
    assert_eq!(eval_cnf(&cnf, &valuation), Err(()));
}
