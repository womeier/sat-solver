#![allow(dead_code)]
use crate::expr::{Expr, Map};

#[derive(Debug, Clone, PartialEq)]
pub struct Literal {
    var: u8,
    negated: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Clause(Vec<Literal>);

#[derive(Debug, Clone, PartialEq)]
pub struct Cnf(Vec<Clause>);

fn clause_union(c1: &Clause, c2: &Clause) -> Clause {
    let mut lits = Vec::new();
    for l in c1.0.iter() {
        lits.push(l.clone());
    }
    for l in c2.0.iter() {
        lits.push(l.clone());
    }
    Clause(lits)
}

// Conjunction of two CNFs is just concatenating their clause lists.
fn conj_cnf(c1: Cnf, c2: Cnf) -> Cnf {
    let Cnf(mut clauses) = c1;
    let Cnf(c2clauses) = c2;
    for c in c2clauses {
        clauses.push(c);
    }
    Cnf(clauses)
}

// Disjunction of two CNFs distributes: every clause of the result pairs one
// clause from each side.
fn distribute(c1: &Cnf, c2: &Cnf) -> Cnf {
    let mut result = Vec::new();
    for clause1 in c1.0.iter() {
        for clause2 in c2.0.iter() {
            result.push(clause_union(clause1, clause2));
        }
    }
    Cnf(result)
}

// Converts `expr` to CNF, threading a polarity flag that pushes negations
// down to literals and switches AND/OR (De Morgan) on the way -- this single
// pass does the job of the textbook two-pass "push to NNF, then distribute
// OR over AND" algorithm, and needs no auxiliary variables (unlike Tseitin),
// so it stays logically *equivalent* to `expr`, not just equisatisfiable.
fn cnf_rec(expr: &Expr, negate: bool) -> Cnf {
    match expr {
        Expr::True => {
            if negate {
                Cnf(vec![Clause(Vec::new())])
            } else {
                Cnf(Vec::new())
            }
        }
        Expr::False => {
            if negate {
                Cnf(Vec::new())
            } else {
                Cnf(vec![Clause(Vec::new())])
            }
        }
        Expr::Variable(v) => Cnf(vec![Clause(vec![Literal {
            var: *v,
            negated: negate,
        }])]),
        Expr::Neg(e) => cnf_rec(e, !negate),
        Expr::Conj(e1, e2) => {
            if negate {
                distribute(&cnf_rec(e1, true), &cnf_rec(e2, true))
            } else {
                conj_cnf(cnf_rec(e1, false), cnf_rec(e2, false))
            }
        }
        Expr::Disj(e1, e2) => {
            if negate {
                conj_cnf(cnf_rec(e1, true), cnf_rec(e2, true))
            } else {
                distribute(&cnf_rec(e1, false), &cnf_rec(e2, false))
            }
        }
    }
}

pub fn to_cnf(expr: &Expr) -> Cnf {
    cnf_rec(expr, false)
}

// Evaluation, mirroring `expr::evaluate`'s Result<bool, ()> style (Err on an
// incomplete valuation).

fn eval_literal(lit: &Literal, valuation: &Map) -> Result<bool, ()> {
    match valuation.get(&lit.var) {
        Some(b) => Ok(if lit.negated { !*b } else { *b }),
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
fn to_cnf_preserves_semantics_on_examples() {
    use crate::expr::{example_expr_sat, example_expr_unsat, evaluate};

    for expr in [example_expr_sat(), example_expr_unsat()] {
        let mut valuation = Map::new();
        valuation.insert(b'x', true);
        valuation.insert(b'y', false);

        let direct = evaluate(&expr, &valuation);
        let via_cnf = eval_cnf(&to_cnf(&expr), &valuation);
        assert_eq!(direct, via_cnf);
    }
}

#[test]
fn to_cnf_distributes_disjunction() {
    // (x ∨ (y ∧ z)) should become (x ∨ y) ∧ (x ∨ z) -- two clauses, each of
    // size 2.
    let expr = Expr::Disj(
        Box::new(Expr::Variable(b'x')),
        Box::new(Expr::Conj(
            Box::new(Expr::Variable(b'y')),
            Box::new(Expr::Variable(b'z')),
        )),
    );
    let Cnf(clauses) = to_cnf(&expr);
    assert_eq!(clauses.len(), 2);
    for Clause(lits) in clauses {
        assert_eq!(lits.len(), 2);
    }
}
