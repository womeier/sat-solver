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

#[test]
fn clause_union_concatenates_literals() {
    let x = Clause(vec![Literal {
        var: b'x',
        negated: false,
    }]);
    let y = Clause(vec![Literal {
        var: b'y',
        negated: true,
    }]);
    let Clause(lits) = clause_union(&x, &y);
    assert_eq!(
        lits,
        vec![
            Literal {
                var: b'x',
                negated: false,
            },
            Literal {
                var: b'y',
                negated: true,
            },
        ]
    );
}

#[test]
fn clause_union_with_empty_clause_is_identity() {
    let x = Clause(vec![Literal {
        var: b'x',
        negated: false,
    }]);
    let empty = Clause(Vec::new());
    assert_eq!(clause_union(&x, &empty), x);
    assert_eq!(clause_union(&empty, &x), x);
}

#[test]
fn conj_cnf_concatenates_clause_lists() {
    let c1 = Cnf(vec![Clause(vec![Literal {
        var: b'x',
        negated: false,
    }])]);
    let c2 = Cnf(vec![
        Clause(vec![Literal {
            var: b'y',
            negated: false,
        }]),
        Clause(vec![Literal {
            var: b'z',
            negated: true,
        }]),
    ]);
    let Cnf(clauses) = conj_cnf(c1, c2);
    assert_eq!(clauses.len(), 3);
}

#[test]
fn distribute_cross_products_every_pair_of_clauses() {
    let c1 = Cnf(vec![
        Clause(vec![Literal {
            var: b'a',
            negated: false,
        }]),
        Clause(vec![Literal {
            var: b'b',
            negated: false,
        }]),
    ]);
    let c2 = Cnf(vec![
        Clause(vec![Literal {
            var: b'c',
            negated: false,
        }]),
        Clause(vec![Literal {
            var: b'd',
            negated: false,
        }]),
        Clause(vec![Literal {
            var: b'e',
            negated: false,
        }]),
    ]);
    let Cnf(clauses) = distribute(&c1, &c2);
    // 2 * 3 clauses, each the union of one literal from each side.
    assert_eq!(clauses.len(), 6);
    for Clause(lits) in &clauses {
        assert_eq!(lits.len(), 2);
    }
}

#[test]
fn cnf_rec_pushes_negation_through_conjunction() {
    // ¬(x ∧ y) should become ¬x ∨ ¬y -- a single clause with two negated
    // literals (De Morgan, via the `negate` polarity flag rather than an
    // explicit NNF pass).
    let expr = Expr::Neg(Box::new(Expr::Conj(
        Box::new(Expr::Variable(b'x')),
        Box::new(Expr::Variable(b'y')),
    )));
    let Cnf(clauses) = cnf_rec(&expr, false);
    assert_eq!(clauses.len(), 1);
    let Clause(lits) = &clauses[0];
    assert_eq!(
        *lits,
        vec![
            Literal {
                var: b'x',
                negated: true,
            },
            Literal {
                var: b'y',
                negated: true,
            },
        ]
    );
}

#[test]
fn eval_literal_reads_and_negates() {
    let mut valuation = Map::new();
    valuation.insert(b'x', true);
    let pos = Literal {
        var: b'x',
        negated: false,
    };
    let neg = Literal {
        var: b'x',
        negated: true,
    };
    assert_eq!(eval_literal(&pos, &valuation), Ok(true));
    assert_eq!(eval_literal(&neg, &valuation), Ok(false));
}

#[test]
fn eval_literal_missing_variable_errs() {
    let valuation = Map::new();
    let lit = Literal {
        var: b'x',
        negated: false,
    };
    assert_eq!(eval_literal(&lit, &valuation), Err(()));
}

#[test]
fn eval_clause_true_if_any_literal_true() {
    let mut valuation = Map::new();
    valuation.insert(b'x', false);
    valuation.insert(b'y', true);
    let clause = Clause(vec![
        Literal {
            var: b'x',
            negated: false,
        },
        Literal {
            var: b'y',
            negated: false,
        },
    ]);
    assert_eq!(eval_clause(&clause, &valuation), Ok(true));
}

#[test]
fn eval_clause_false_if_all_literals_false() {
    let mut valuation = Map::new();
    valuation.insert(b'x', false);
    valuation.insert(b'y', false);
    let clause = Clause(vec![
        Literal {
            var: b'x',
            negated: false,
        },
        Literal {
            var: b'y',
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
    valuation.insert(b'x', true);
    let clause = Clause(vec![
        Literal {
            var: b'x',
            negated: false,
        },
        Literal {
            var: b'y',
            negated: false,
        },
    ]);
    assert_eq!(eval_clause(&clause, &valuation), Ok(true));
}

#[test]
fn eval_clause_errs_on_missing_variable() {
    let valuation = Map::new();
    let clause = Clause(vec![Literal {
        var: b'x',
        negated: false,
    }]);
    assert_eq!(eval_clause(&clause, &valuation), Err(()));
}

#[test]
fn eval_cnf_true_when_every_clause_true() {
    let mut valuation = Map::new();
    valuation.insert(b'x', true);
    valuation.insert(b'y', true);
    let cnf = Cnf(vec![
        Clause(vec![Literal {
            var: b'x',
            negated: false,
        }]),
        Clause(vec![Literal {
            var: b'y',
            negated: false,
        }]),
    ]);
    assert_eq!(eval_cnf(&cnf, &valuation), Ok(true));
}

#[test]
fn eval_cnf_false_when_some_clause_false() {
    let mut valuation = Map::new();
    valuation.insert(b'x', true);
    valuation.insert(b'y', false);
    let cnf = Cnf(vec![
        Clause(vec![Literal {
            var: b'x',
            negated: false,
        }]),
        Clause(vec![Literal {
            var: b'y',
            negated: false,
        }]),
    ]);
    assert_eq!(eval_cnf(&cnf, &valuation), Ok(false));
}

#[test]
fn eval_cnf_errs_on_missing_variable() {
    let valuation = Map::new();
    let cnf = Cnf(vec![Clause(vec![Literal {
        var: b'x',
        negated: false,
    }])]);
    assert_eq!(eval_cnf(&cnf, &valuation), Err(()));
}
