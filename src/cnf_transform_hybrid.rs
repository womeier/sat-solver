#![allow(dead_code)]
//! The hybrid CNF transformation: distribute where distributing is cheap, and
//! name a subformula with a fresh variable only where it is not.
//!
//! This is the Boy de la Tour renaming strategy, and it is the one you actually
//! want. [`crate::cnf_transform_naive`] is exponential on nested formulas;
//! [`crate::cnf_transform_tseitin`] is linear but names *every* internal node,
//! which is pure overhead on input that was already clausal (a uf50-218
//! instance goes from 218 clauses over 50 variables to 1960 over 703). The
//! hybrid pays for a gate variable only at the disjunctions where distribution
//! would cost more than naming does, so it reproduces the naive output exactly
//! on already-clausal input -- every SATLIB instance, everything `dimacs` reads
//! -- while staying linear on the family that makes the naive transform blow up.
//!
//! ## The decision rule
//!
//! Both operands of a disjunction have already been turned into CNFs, of `n`
//! and `m` clauses. Distributing costs `n * m` clauses. Naming one side costs
//! `n + m`: one definition clause per clause of the named side, plus `m`
//! clauses from distributing a single literal against the other side. So
//! distribute exactly when `n * m <= n + m`, which for small operands -- in
//! particular `n = m = 1`, a disjunction of literals -- is always. The larger
//! side is the one named, since that leaves the smaller clause count for the
//! enclosing node to work with.
//!
//! ## Why the one-directional definition is enough
//!
//! Naming a CNF `F` by `g` emits only `g → F`, i.e. one clause `¬g ∨ C` per
//! clause `C` of `F` -- not the biconditional Tseitin would use. That is sound
//! here because `g` occurs only *positively* outside its own definition: the
//! recursion pushes negations down to the literals before any CNF is built, so
//! a CNF once built is only ever concatenated, distributed, or prefixed with
//! some other `¬g'`, and never negated. The definition clauses themselves are
//! set aside and conjoined at the very end, so `¬g` appears nowhere else.
//!
//! A model of the output therefore satisfies the input once restricted to the
//! original variables, and every model of the input extends to one (set each
//! `g` to the truth value of the subformula it names). Unlike Tseitin's forced
//! gates that extension is not unique, so this transformation preserves
//! satisfiability but not model count -- fine for SAT, wrong for #SAT.

#[cfg(test)]
use crate::cnf::eval_cnf;
use crate::cnf::{Clause, Cnf, Literal};
use crate::cnf_transform_naive::{conj_cnf, distribute};
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

struct Renamer {
    /// Next unused variable index. Held as `u32` so that running off the end of
    /// the `u16` variable space is a comparison rather than an overflow.
    next: u32,
    /// Definition clauses for the subformulas named so far, conjoined onto the
    /// result at the end. Kept apart from the body precisely so that no `¬g`
    /// ever gets distributed into anything.
    defs: Vec<Clause>,
}

impl Renamer {
    fn new(expr: &Expr) -> Self {
        let mut next: u32 = 0;
        for v in collect_vars(expr) {
            if v as u32 >= next {
                next = v as u32 + 1;
            }
        }
        Renamer {
            next,
            defs: Vec::new(),
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

    // Replaces `cnf` by a single fresh variable `g`, filing `g → cnf` (one
    // clause `¬g ∨ C` per clause `C` of `cnf`) under the definitions.
    fn rename(&mut self, cnf: Cnf) -> Result<Cnf, ()> {
        let g = self.fresh()?;
        for Clause(mut lits) in cnf.0 {
            let mut clause = vec![neg(g)];
            clause.append(&mut lits);
            self.defs.push(Clause(clause));
        }
        Ok(Cnf(vec![Clause(vec![pos(g)])]))
    }

    // The disjunction of two CNFs: distribute when that costs no more than
    // naming would, otherwise name the bigger side and distribute against that.
    fn disjoin(&mut self, c1: Cnf, c2: Cnf) -> Result<Cnf, ()> {
        let n = c1.0.len();
        let m = c2.0.len();
        if n * m <= n + m {
            return Ok(distribute(&c1, &c2));
        }
        if n >= m {
            let named = self.rename(c1)?;
            Ok(distribute(&named, &c2))
        } else {
            let named = self.rename(c2)?;
            Ok(distribute(&c1, &named))
        }
    }

    // The same polarity-threading recursion as the naive transformation -- the
    // `negate` flag pushes negations down to the literals and swaps AND/OR on
    // the way (De Morgan) -- with `disjoin` standing in for the unconditional
    // `distribute`. Constants need no special machinery: `⊤` is the empty CNF
    // and `⊥` the CNF holding one empty clause, so unlike Tseitin this never
    // burns a variable on them.
    fn cnf(&mut self, expr: &Expr, negate: bool) -> Result<Cnf, ()> {
        match expr {
            Expr::True => Ok(if negate {
                Cnf(vec![Clause(Vec::new())])
            } else {
                Cnf(Vec::new())
            }),
            Expr::False => Ok(if negate {
                Cnf(Vec::new())
            } else {
                Cnf(vec![Clause(Vec::new())])
            }),
            Expr::Variable(v) => Ok(Cnf(vec![Clause(vec![Literal {
                var: *v,
                negated: negate,
            }])])),
            Expr::Neg(e) => self.cnf(e, !negate),
            Expr::Conj(e1, e2) => {
                let c1 = self.cnf(e1, negate)?;
                let c2 = self.cnf(e2, negate)?;
                if negate {
                    self.disjoin(c1, c2)
                } else {
                    Ok(conj_cnf(c1, c2))
                }
            }
            Expr::Disj(e1, e2) => {
                let c1 = self.cnf(e1, negate)?;
                let c2 = self.cnf(e2, negate)?;
                if negate {
                    Ok(conj_cnf(c1, c2))
                } else {
                    self.disjoin(c1, c2)
                }
            }
        }
    }
}

/// Converts `expr` to an equisatisfiable CNF, introducing a variable only where
/// distribution would cost more than naming.
///
/// `Err(())` means a gate variable would not fit in the `u16` variable space.
/// Note that this is rarer than for [`crate::cnf_transform_tseitin::to_cnf`]:
/// only the subformulas that actually needed naming consume an index.
pub fn to_cnf(expr: &Expr) -> Result<Cnf, ()> {
    let mut renamer = Renamer::new(expr);
    let body = renamer.cnf(expr, false)?;
    // Body first, definitions after: it keeps the original variables at the
    // front of the clause list, which is what `sat_dpll::find_branch_var` picks
    // its decision variable from.
    Ok(conj_cnf(body, Cnf(renamer.defs)))
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

// A 3-CNF over `vars` variables, shaped exactly the way `dimacs` shapes one:
// a conjunction of disjunctions of (possibly negated) literals.
#[cfg(test)]
fn clausal(clauses: &[[(u16, bool); 3]]) -> Expr {
    fn literal(v: u16, negated: bool) -> Expr {
        if negated {
            Expr::Neg(Box::new(var(v)))
        } else {
            var(v)
        }
    }
    let mut out: Option<Expr> = None;
    for c in clauses.iter() {
        let clause = Expr::Disj(
            Box::new(Expr::Disj(
                Box::new(literal(c[0].0, c[0].1)),
                Box::new(literal(c[1].0, c[1].1)),
            )),
            Box::new(literal(c[2].0, c[2].1)),
        );
        out = Some(match out {
            None => clause,
            Some(acc) => Expr::Conj(Box::new(acc), Box::new(clause)),
        });
    }
    out.unwrap()
}

#[test]
fn clausal_input_comes_out_byte_for_byte_as_the_naive_transform() {
    // The property the whole module exists for: on input that is already in
    // CNF -- every SATLIB instance -- the hybrid introduces nothing at all and
    // reproduces the naive transformation exactly.
    let expr = clausal(&[
        [(0, false), (1, true), (2, false)],
        [(1, false), (3, false), (4, true)],
        [(2, true), (3, true), (0, false)],
        [(4, false), (0, true), (1, false)],
    ]);
    let hybrid = to_cnf(&expr).unwrap();
    assert_eq!(hybrid, crate::cnf_transform_naive::to_cnf(&expr));
    // No gate variables: only the five originals appear.
    let mut vars = cnf_vars(&hybrid);
    vars.sort();
    assert_eq!(vars, vec![0, 1, 2, 3, 4]);
}

#[test]
fn a_disjunction_of_literals_never_names_anything() {
    // n = m = 1, so `n * m <= n + m` and the rule distributes.
    let expr = Expr::Disj(Box::new(var(0)), Box::new(Expr::Neg(Box::new(var(1)))));
    let Cnf(clauses) = to_cnf(&expr).unwrap();
    assert_eq!(clauses, vec![Clause(vec![pos(0), neg(1)])]);
}

#[test]
fn constants_need_no_variable() {
    // Unlike Tseitin, which pins a variable true to stand in for `⊤`.
    assert_eq!(to_cnf(&Expr::True).unwrap(), Cnf(Vec::new()));
    assert_eq!(to_cnf(&Expr::False).unwrap(), Cnf(vec![Clause(Vec::new())]));
}

#[test]
fn distributes_up_to_the_break_even_point() {
    // (x0 ∧ x1) ∨ (x2 ∧ x3): n = m = 2, so n * m = 4 and n + m = 4 -- naming
    // would cost the same, so the rule distributes and introduces nothing.
    let expr = Expr::Disj(
        Box::new(Expr::Conj(Box::new(var(0)), Box::new(var(1)))),
        Box::new(Expr::Conj(Box::new(var(2)), Box::new(var(3)))),
    );
    let cnf = to_cnf(&expr).unwrap();
    assert_eq!(cnf, crate::cnf_transform_naive::to_cnf(&expr));
    assert_eq!(cnf.0.len(), 4);
    let mut vars = cnf_vars(&cnf);
    vars.sort();
    assert_eq!(vars, vec![0, 1, 2, 3]);
}

#[test]
fn names_the_bigger_side_once_distribution_costs_more() {
    // ((x0 ∧ x1) ∧ x2) ∨ (x3 ∧ x4): n = 3, m = 2, so n * m = 6 > 5 = n + m.
    // The three-clause side is named by x5, leaving two body clauses and three
    // definition clauses -- five in total, against the naive transform's six.
    let expr = Expr::Disj(
        Box::new(Expr::Conj(
            Box::new(Expr::Conj(Box::new(var(0)), Box::new(var(1)))),
            Box::new(var(2)),
        )),
        Box::new(Expr::Conj(Box::new(var(3)), Box::new(var(4)))),
    );
    let Cnf(clauses) = to_cnf(&expr).unwrap();
    assert_eq!(
        clauses,
        vec![
            // body: the named side distributed against the small one
            Clause(vec![pos(5), pos(3)]),
            Clause(vec![pos(5), pos(4)]),
            // definitions: x5 → (x0 ∧ x1 ∧ x2)
            Clause(vec![neg(5), pos(0)]),
            Clause(vec![neg(5), pos(1)]),
            Clause(vec![neg(5), pos(2)]),
        ]
    );
    assert_eq!(crate::cnf_transform_naive::to_cnf(&expr).0.len(), 6);
}

#[test]
fn every_model_of_the_formula_extends_to_a_model_of_the_cnf() {
    use crate::expr::{example_expr_sat, example_expr_unsat, parse_expr};

    let exprs = [
        example_expr_sat(),
        example_expr_unsat(),
        parse_expr("((a | b) & ~(a & b))").unwrap().1,
        parse_expr("(~(a & b) | (c & ~a))").unwrap().1,
        parse_expr("((a & b) | (~a & ~b))").unwrap().1,
        parse_expr("(((a & b) | (c & d)) | ((~a & ~c) | (b & ~d)))")
            .unwrap()
            .1,
    ];

    for expr in exprs {
        let cnf = to_cnf(&expr).unwrap();
        let vars = collect_vars(&expr);
        for mask in 0u32..(1u32 << vars.len()) {
            let mut base = Map::new();
            for (i, v) in vars.iter().enumerate() {
                base.insert(*v, (mask >> i) & 1 == 1);
            }
            // At least one extension when the formula holds, none when it does
            // not. Unlike Tseitin the count is not pinned to exactly one: the
            // definitions are one-directional, so a `g` may be false even where
            // the subformula it names is true.
            let extensions = count_extensions(&cnf, &base);
            if evaluate(&expr, &base) == Ok(true) {
                assert!(extensions >= 1, "{expr} at {base:?} has no extension");
            } else {
                assert_eq!(extensions, 0, "{expr} at {base:?} should not extend");
            }
        }
    }
}

#[test]
fn size_stays_linear_where_distribution_explodes() {
    // The same family `cnf_transform_tseitin` is measured on: n conjunctions
    // joined by n-1 disjunctions, which the naive transform turns into 2^n
    // clauses.
    let n: u16 = 12;
    let mut expr = Expr::Conj(Box::new(var(0)), Box::new(var(1)));
    for i in 1..n {
        let pair = Expr::Conj(Box::new(var(2 * i)), Box::new(var(2 * i + 1)));
        expr = Expr::Disj(Box::new(expr), Box::new(pair));
    }

    let Cnf(distributed) = crate::cnf_transform_naive::to_cnf(&expr);
    assert_eq!(distributed.len(), 1 << n);

    let Cnf(hybrid) = to_cnf(&expr).unwrap();
    let Cnf(tseitin) = crate::cnf_transform_tseitin::to_cnf(&expr).unwrap();
    // Linear, and in this case tighter than Tseitin's 3-clauses-per-node.
    assert!(
        hybrid.len() < 8 * n as usize,
        "hybrid emitted {} clauses",
        hybrid.len()
    );
    assert!(
        hybrid.len() < tseitin.len(),
        "hybrid {} vs tseitin {}",
        hybrid.len(),
        tseitin.len()
    );
}

#[test]
fn gate_variables_run_out_at_the_u16_ceiling() {
    // A balanced *disjunction* over 2^17 leaves, each leaf a two-clause
    // conjunction: every level past the break-even point has to name a side,
    // so this exhausts the variable space the way the Tseitin encoder does.
    // Built bottom-up to keep the recursion depth logarithmic.
    let mut level: Vec<Expr> = (0..1 << 17)
        .map(|_| Expr::Conj(Box::new(var(0)), Box::new(var(1))))
        .collect();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len() / 2);
        let mut pairs = level.into_iter();
        while let (Some(a), Some(b)) = (pairs.next(), pairs.next()) {
            next.push(Expr::Disj(Box::new(a), Box::new(b)));
        }
        level = next;
    }
    assert!(to_cnf(&level[0]).is_err());
}
