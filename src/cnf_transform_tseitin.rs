#![allow(dead_code)]
//! The Tseitin CNF transformation: name every internal node of the formula with
//! a fresh variable, and constrain that variable to *equal* the node it names.
//!
//! Each gate costs one variable and at most three clauses, so the output grows
//! linearly in the size of the input where
//! [`crate::cnf_transform_naive::to_cnf`] grows exponentially.
//!
//! The price is that the result is only **equisatisfiable** with the input, not
//! equivalent: it lives over a larger variable set. Because the defining
//! clauses are full biconditionals (`g ↔ ...`, rather than the single
//! implication a Plaisted-Greenbaum encoding would emit), the gate values are
//! *forced* — every model of the input extends to exactly one model of the CNF,
//! and every model of the CNF restricted to the original variables is a model
//! of the input. No projection step is needed in practice: a `Map` produced by
//! solving the CNF assigns the original variables alongside the auxiliary ones,
//! and `expr::evaluate` simply never looks the auxiliary ones up.
//!
//! Fresh variables are numbered from one past the largest variable occurring in
//! the input, so a formula with more internal nodes than the `u16` variable
//! space can name is rejected with `Err` rather than silently aliasing a gate
//! onto a real variable.

#[cfg(test)]
use crate::cnf::eval_cnf;
use crate::cnf::{Clause, Cnf, Literal};
use crate::expr::{Expr, collect_vars};
#[cfg(test)]
use crate::expr::{Map, evaluate};

fn pos(var: u16) -> Literal {
    Literal {
        var,
        negated: false,
    }
}

fn neg(var: u16) -> Literal {
    Literal { var, negated: true }
}

fn flip(lit: &Literal) -> Literal {
    Literal {
        var: lit.var,
        negated: !lit.negated,
    }
}

struct Encoder {
    /// Next unused variable index. Held as `u32` so that running off the end of
    /// the `u16` variable space is a comparison rather than an overflow.
    next: u32,
    /// The variable pinned true by a unit clause, standing in for `⊤` (and, as
    /// its negative literal, for `⊥`). Allocated on first use, so a formula
    /// without constants -- everything `dimacs` reads -- pays nothing for it.
    true_var: Option<u16>,
    clauses: Vec<Clause>,
}

impl Encoder {
    fn new(expr: &Expr) -> Self {
        let mut next: u32 = 0;
        for v in collect_vars(expr) {
            if v as u32 >= next {
                next = v as u32 + 1;
            }
        }
        Encoder {
            next,
            true_var: None,
            clauses: Vec::new(),
        }
    }

    fn fresh(&mut self) -> Result<u16, ()> {
        if self.next > u16::MAX as u32 {
            return Err(());
        }
        let v = self.next as u16;
        self.next += 1;
        Ok(v)
    }

    fn constant(&mut self, value: bool) -> Result<Literal, ()> {
        let v = match self.true_var {
            Some(v) => v,
            None => {
                let v = self.fresh()?;
                self.clauses.push(Clause(vec![pos(v)]));
                self.true_var = Some(v);
                v
            }
        };
        Ok(if value { pos(v) } else { neg(v) })
    }

    /// Emits the clauses defining `expr` and returns the literal standing for
    /// its truth value.
    fn encode(&mut self, expr: &Expr) -> Result<Literal, ()> {
        match expr {
            Expr::True => self.constant(true),
            Expr::False => self.constant(false),
            // A variable is already a literal, and a negation is just the
            // opposite polarity of one -- neither needs a gate.
            Expr::Variable(v) => Ok(pos(*v)),
            Expr::Neg(e) => {
                let l = self.encode(e)?;
                Ok(flip(&l))
            }
            Expr::Conj(e1, e2) => {
                let l1 = self.encode(e1)?;
                let l2 = self.encode(e2)?;
                let g = self.fresh()?;
                // g → l1, g → l2, and l1 ∧ l2 → g.
                self.clauses.push(Clause(vec![neg(g), l1.clone()]));
                self.clauses.push(Clause(vec![neg(g), l2.clone()]));
                self.clauses
                    .push(Clause(vec![pos(g), flip(&l1), flip(&l2)]));
                Ok(pos(g))
            }
            Expr::Disj(e1, e2) => {
                let l1 = self.encode(e1)?;
                let l2 = self.encode(e2)?;
                let g = self.fresh()?;
                // g → l1 ∨ l2, and l1 → g, l2 → g.
                self.clauses
                    .push(Clause(vec![neg(g), l1.clone(), l2.clone()]));
                self.clauses.push(Clause(vec![pos(g), flip(&l1)]));
                self.clauses.push(Clause(vec![pos(g), flip(&l2)]));
                Ok(pos(g))
            }
        }
    }
}

/// Converts `expr` to an equisatisfiable CNF of size linear in `expr`.
///
/// `Err(())` means the gate variables would not fit in the `u16` variable
/// space: the input has more internal nodes than there are variable indices
/// left above its largest variable.
pub fn to_cnf(expr: &Expr) -> Result<Cnf, ()> {
    let mut encoder = Encoder::new(expr);
    let root = encoder.encode(expr)?;
    // Assert the root: the formula holds exactly when its top gate does.
    encoder.clauses.push(Clause(vec![root]));
    Ok(Cnf(encoder.clauses))
}

// Every variable occurring anywhere in `cnf`, in order of first appearance.
#[cfg(test)]
fn cnf_vars(cnf: &Cnf) -> Vec<u16> {
    let mut vars: Vec<u16> = Vec::new();
    for Clause(lits) in cnf.0.iter() {
        for lit in lits.iter() {
            if !vars.contains(&lit.var) {
                vars.push(lit.var);
            }
        }
    }
    vars
}

// How many ways `base` extends to a model of `cnf`, by brute force over the
// variables of `cnf` that `base` leaves unset. Only usable on tiny formulas.
#[cfg(test)]
fn count_extensions(cnf: &Cnf, base: &Map) -> u32 {
    let free: Vec<u16> = cnf_vars(cnf)
        .into_iter()
        .filter(|v| base.get(v).is_none())
        .collect();
    let mut count = 0;
    for mask in 0u32..(1u32 << free.len()) {
        let mut valuation = base.clone();
        for (i, v) in free.iter().enumerate() {
            valuation.insert(*v, (mask >> i) & 1 == 1);
        }
        if eval_cnf(cnf, &valuation) == Ok(true) {
            count += 1;
        }
    }
    count
}

#[cfg(test)]
fn var(i: u16) -> Expr {
    Expr::Variable(i)
}

#[test]
fn a_variable_needs_no_gate() {
    let Cnf(clauses) = to_cnf(&var(0)).unwrap();
    // Just the asserted root, which is the variable's own literal.
    assert_eq!(clauses, vec![Clause(vec![pos(0)])]);
}

#[test]
fn negation_needs_no_gate() {
    // ¬¬x collapses to x: each `Neg` flips a polarity instead of allocating.
    let expr = Expr::Neg(Box::new(Expr::Neg(Box::new(var(0)))));
    let Cnf(clauses) = to_cnf(&expr).unwrap();
    assert_eq!(clauses, vec![Clause(vec![pos(0)])]);
}

#[test]
fn conjunction_emits_its_three_defining_clauses() {
    // x0 ∧ x1, so the gate is x2 -- one past the largest input variable.
    let expr = Expr::Conj(Box::new(var(0)), Box::new(var(1)));
    let Cnf(clauses) = to_cnf(&expr).unwrap();
    assert_eq!(
        clauses,
        vec![
            Clause(vec![neg(2), pos(0)]),
            Clause(vec![neg(2), pos(1)]),
            Clause(vec![pos(2), neg(0), neg(1)]),
            Clause(vec![pos(2)]),
        ]
    );
}

#[test]
fn disjunction_emits_its_three_defining_clauses() {
    let expr = Expr::Disj(Box::new(var(0)), Box::new(var(1)));
    let Cnf(clauses) = to_cnf(&expr).unwrap();
    assert_eq!(
        clauses,
        vec![
            Clause(vec![neg(2), pos(0), pos(1)]),
            Clause(vec![pos(2), neg(0)]),
            Clause(vec![pos(2), neg(1)]),
            Clause(vec![pos(2)]),
        ]
    );
}

#[test]
fn negated_operands_enter_the_gate_clauses_as_flipped_literals() {
    // (¬x0) ∧ x1 -- the negation shows up inside the gate's clauses rather
    // than as a gate of its own, so the shape is the same as `x0 ∧ x1` with
    // the polarities of x0 swapped.
    let expr = Expr::Conj(Box::new(Expr::Neg(Box::new(var(0)))), Box::new(var(1)));
    let Cnf(clauses) = to_cnf(&expr).unwrap();
    assert_eq!(
        clauses,
        vec![
            Clause(vec![neg(2), neg(0)]),
            Clause(vec![neg(2), pos(1)]),
            Clause(vec![pos(2), pos(0), neg(1)]),
            Clause(vec![pos(2)]),
        ]
    );
}

#[test]
fn both_constants_share_one_forced_variable() {
    // ⊤ ∧ ⊥. The constant variable is allocated once (x0, pinned by a unit
    // clause) and ⊥ takes its negative literal; x1 is the conjunction gate.
    let expr = Expr::Conj(Box::new(Expr::True), Box::new(Expr::False));
    let cnf = to_cnf(&expr).unwrap();
    assert_eq!(cnf_vars(&cnf), vec![0, 1]);
    assert_eq!(
        cnf.0,
        vec![
            Clause(vec![pos(0)]),
            Clause(vec![neg(1), pos(0)]),
            Clause(vec![neg(1), neg(0)]),
            Clause(vec![pos(1), neg(0), pos(0)]),
            Clause(vec![pos(1)]),
        ]
    );
    // ...and the whole thing is unsatisfiable, as ⊤ ∧ ⊥ should be.
    assert_eq!(count_extensions(&cnf, &Map::new()), 0);
}

#[test]
fn every_model_of_the_formula_extends_to_exactly_one_model_of_the_cnf() {
    use crate::expr::{example_expr_sat, example_expr_unsat, parse_expr};

    let exprs = [
        example_expr_sat(),
        example_expr_unsat(),
        parse_expr("((a | b) & ~(a & b))").unwrap().1,
        parse_expr("(~(a & b) | (c & ~a))").unwrap().1,
        parse_expr("((a & b) | (~a & ~b))").unwrap().1,
    ];

    for expr in exprs {
        let cnf = to_cnf(&expr).unwrap();
        let vars = collect_vars(&expr);
        for mask in 0u32..(1u32 << vars.len()) {
            let mut base = Map::new();
            for (i, v) in vars.iter().enumerate() {
                base.insert(*v, (mask >> i) & 1 == 1);
            }
            // The gate variables are forced, so a satisfying valuation of the
            // original variables extends in exactly one way, and a falsifying
            // one not at all. (A Plaisted-Greenbaum encoding would only get
            // the "at least one" half of this.)
            let expected = if evaluate(&expr, &base) == Ok(true) {
                1
            } else {
                0
            };
            assert_eq!(
                count_extensions(&cnf, &base),
                expected,
                "{expr} at {base:?}"
            );
        }
    }
}

#[test]
fn size_stays_linear_where_distribution_explodes() {
    // (x0 ∧ x1) ∨ (x2 ∧ x3) ∨ ... -- n conjunctions joined by n-1
    // disjunctions, the family the naive transformation turns into 2^n
    // clauses (one per way of picking a conjunct from each disjunct).
    let n: u16 = 12;
    let mut expr = Expr::Conj(Box::new(var(0)), Box::new(var(1)));
    for i in 1..n {
        let pair = Expr::Conj(Box::new(var(2 * i)), Box::new(var(2 * i + 1)));
        expr = Expr::Disj(Box::new(expr), Box::new(pair));
    }

    let Cnf(distributed) = crate::cnf_transform_naive::to_cnf(&expr);
    assert_eq!(distributed.len(), 1 << n);

    // Three clauses for each of the n + (n-1) gates, plus the asserted root.
    let Cnf(named) = to_cnf(&expr).unwrap();
    assert_eq!(named.len(), 3 * (2 * n as usize - 1) + 1);
}

#[test]
fn gate_variables_run_out_at_the_u16_ceiling() {
    // A balanced conjunction over 2^17 leaves has 2^17 - 1 internal nodes,
    // more gates than a `u16` has room to name. Built bottom-up because a
    // tree that deep would blow the stack in `encode` -- balanced, it recurses
    // only 17 frames.
    let mut level: Vec<Expr> = (0..1 << 17).map(|_| var(0)).collect();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len() / 2);
        let mut pairs = level.into_iter();
        while let (Some(a), Some(b)) = (pairs.next(), pairs.next()) {
            next.push(Expr::Conj(Box::new(a), Box::new(b)));
        }
        level = next;
    }
    assert!(to_cnf(&level[0]).is_err());
}
