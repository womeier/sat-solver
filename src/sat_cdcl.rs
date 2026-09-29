#![allow(dead_code)]
//! CDCL: DPLL plus conflict-driven clause learning.
//!
//! [`crate::sat_dpll`] backtracks *chronologically* -- on a conflict it flips the
//! most recent decision and forgets everything it just learned about why that
//! branch failed. CDCL keeps the reason. Every conflict is analysed down to the
//! decisions that actually caused it, that explanation is recorded as a new
//! clause, and the search jumps straight back to the level where the new clause
//! forces something -- possibly many levels at once, and never through the
//! decisions the conflict did not depend on. The learned clauses accumulate, so
//! the same dead end is refuted once and then pruned by propagation rather than
//! rediscovered.
//!
//! What is here is the classic CDCL loop, with the pieces that are algorithmic
//! rather than engineering:
//!
//! - **1-UIP conflict analysis** ([`Solver::analyze`]) -- resolve the conflicting
//!   clause against the reasons of its conflict-level literals until one literal
//!   of that level is left, the first unique implication point.
//! - **Non-chronological backjumping** ([`Solver::backtrack`]) -- to the highest
//!   level mentioned by the learned clause, not to the previous decision.
//! - **VSIDS-style decisions** ([`Solver::pick_branch_var`]) -- branch on the
//!   variable that recent conflicts mentioned most, with activities halved
//!   periodically so the heuristic tracks *recent* conflicts.
//! - **Phase saving** -- a decision reuses the value the variable last held,
//!   which is what makes a restart cheap rather than a fresh start.
//! - **Geometric restarts** -- abandon the trail (never the clauses) on a growing
//!   conflict budget, to escape a bad early decision.
//!
//! Deliberately not here, and why:
//!
//! - **Watched literals.** Propagation rescans the clause database
//!   ([`Solver::propagate`]); a production solver visits only the clauses that
//!   could have become unit. This is the same trade `sat_dpll` makes by building
//!   a fresh residual CNF per node: the O(clauses) version is the one whose
//!   invariants can be checked by reading it, which is what this repository is
//!   for. Everything the README reports was measured with propagation in this
//!   shape, so the gap it shows against DPLL is the algorithm's, not an
//!   optimization's.
//! - **Clause deletion.** Clause indices are used as `reason` handles, so
//!   deleting or reordering clauses means rewriting every reason that points past
//!   the hole. Keeping every learned clause costs memory and propagation time but
//!   no correctness argument.
//! - **Clause minimization** (self-subsuming resolution over the learned clause).
//!
//! Unlike `sat_naive` and `sat_dpll`, nothing here is proved in Lean yet -- the
//! module is still excluded from extraction, and `PLAN.md` lists what a proof
//! would have to establish. The tests below are what stands in for it: the
//! pieces individually, a 300-instance random 3-SAT differential check against
//! the proved-correct `sat_naive`, the pigeonhole family, and (in
//! `tests/satlib.rs`) all 3000 SATLIB instances with every model model-checked.

use crate::cnf::{Clause, Cnf, Literal};
#[cfg(test)]
use crate::expr::letter;
use crate::expr::{Expr, Map, collect_vars};
use crate::sat::SatSolver;
use crate::sat_dpll::{Transform, encode};
use crate::sat_naive::initial_valuation;
use crate::sat_result::SatResult;

// Conflicts between activity halvings. Small enough that the heuristic forgets
// the early search, large enough that a single conflict cannot dominate it.
const DECAY_INTERVAL: u32 = 128;

// Conflicts the first restart interval allows; each subsequent one is 1.5x the
// last. Growth is what makes the restarts finite: a search that needs n
// conflicts to finish is eventually given an interval longer than n.
const FIRST_RESTART: u32 = 100;

// What one clause has to say about the current assignment.
enum Status {
    // Every literal is false: the assignment refutes this clause outright.
    Conflict,
    // Exactly one literal is unassigned and every other is false, so that
    // literal is forced -- there is no choice and no backtracking point here.
    Unit(Literal),
    // Already satisfied, or still has two unassigned literals: either way it
    // constrains nothing yet.
    Silent,
}

// One CDCL search over one clause database.
//
// Everything indexed "by variable" below is a `Vec` of length `num_vars`,
// indexed by the variable itself -- the same slot-array trick `expr::Map` uses,
// for the same reason: variables are small dense `u16`s, so a lookup is an
// index, not a search.
struct Solver {
    // Problem clauses first, learned ones appended as conflicts are analysed.
    // Indices into this are stable for the lifetime of the search, which is what
    // lets `reason` hold one.
    clauses: Vec<Clause>,
    // Where the learned clauses begin, i.e. how many clauses came from the CNF.
    problem_clauses: usize,
    // The current partial assignment. `None` is unassigned.
    value: Vec<Option<bool>>,
    // The decision level each variable was assigned at (stale while unassigned).
    level: Vec<usize>,
    // The clause that forced each assignment, or `None` for a decision (and,
    // again, stale while unassigned).
    reason: Vec<Option<usize>>,
    // The value each variable last held, for phase saving.
    phase: Vec<bool>,
    // VSIDS activity: bumped for every variable a conflict analysis touches,
    // halved every `DECAY_INTERVAL` conflicts.
    activity: Vec<u32>,
    // Whether the variable occurs in any clause at all. Indices below the
    // largest one used need slots either way (the slot array is indexed by the
    // variable), but deciding a variable no clause mentions would be a decision
    // level spent on nothing -- and `expr::letter` makes those the common case,
    // since it maps `x` to 120.
    occurs: Vec<bool>,
    // Scratch flags for `analyze`, which clears every one it sets before
    // returning -- so that a conflict costs O(conflict size), not O(num_vars).
    seen: Vec<bool>,
    // Assignments in the order they were made...
    trail: Vec<u16>,
    // ...and the `trail` index each decision level starts at, so `trail_lim`'s
    // length *is* the current decision level.
    trail_lim: Vec<usize>,
    conflicts: u32,
}

impl Solver {
    fn new(cnf: &Cnf) -> Solver {
        // One slot per variable index up to the largest the CNF mentions, so that
        // "by variable" is a plain array index. Indices in that range that occur
        // in no clause are tracked in `occurs` and never decided.
        let mut num_vars = 0;
        for clause in cnf.0.iter() {
            for lit in clause.0.iter() {
                if lit.var as usize + 1 > num_vars {
                    num_vars = lit.var as usize + 1;
                }
            }
        }

        let mut value = Vec::new();
        let mut level = Vec::new();
        let mut reason = Vec::new();
        let mut phase = Vec::new();
        let mut activity = Vec::new();
        let mut seen = Vec::new();
        let mut occurs = Vec::new();
        for _ in 0..num_vars {
            value.push(None);
            level.push(0);
            reason.push(None);
            phase.push(false);
            activity.push(0);
            seen.push(false);
            occurs.push(false);
        }
        for clause in cnf.0.iter() {
            for lit in clause.0.iter() {
                occurs[lit.var as usize] = true;
            }
        }

        Solver {
            clauses: cnf.0.clone(),
            problem_clauses: cnf.0.len(),
            value,
            level,
            reason,
            phase,
            activity,
            seen,
            occurs,
            trail: Vec::new(),
            trail_lim: Vec::new(),
            conflicts: 0,
        }
    }

    fn num_vars(&self) -> usize {
        self.value.len()
    }

    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    // `Some(true)` if the literal is satisfied, `Some(false)` if falsified,
    // `None` if its variable is unassigned. A literal of value `b` is satisfied
    // exactly when `b` disagrees with `negated`.
    fn lit_value(&self, lit: &Literal) -> Option<bool> {
        match self.value[lit.var as usize] {
            Some(b) => Some(b != lit.negated),
            None => None,
        }
    }

    fn status(&self, clause: usize) -> Status {
        let mut unassigned: Option<Literal> = None;
        // By index rather than `.iter()`: aeneas cannot translate an early
        // `return` out of a loop whose iterator was built from an indexed place,
        // which is what `self.clauses[clause].0.iter()` is. `analyze` loops by
        // index for the same reason.
        for j in 0..self.clauses[clause].0.len() {
            let lit = &self.clauses[clause].0[j];
            match self.lit_value(lit) {
                Some(true) => return Status::Silent,
                Some(false) => {}
                None => {
                    if unassigned.is_some() {
                        // Two unassigned literals: nothing is forced.
                        return Status::Silent;
                    }
                    unassigned = Some(lit.clone());
                }
            }
        }
        match unassigned {
            Some(lit) => Status::Unit(lit),
            // No unassigned literal and none satisfied: all false.
            None => Status::Conflict,
        }
    }

    // Records `var := value` at the current decision level. `reason` is the
    // clause that forced it, or `None` when it is a decision -- the distinction
    // conflict analysis runs on.
    fn assign(&mut self, var: u16, value: bool, reason: Option<usize>) {
        let i = var as usize;
        self.value[i] = Some(value);
        self.level[i] = self.decision_level();
        self.reason[i] = reason;
        self.phase[i] = value;
        self.trail.push(var);
    }

    // Unit propagation to a fixpoint: assign every literal the assignment
    // forces, and stop at the first clause it falsifies (returning that
    // clause's index, which is what `analyze` starts from).
    //
    // The rescan-everything shape is the honest O(clauses) version of what
    // watched literals do; see the module docs.
    fn propagate(&mut self) -> Option<usize> {
        // One flat loop rather than "repeat a full pass until nothing changed":
        // a cursor that wraps back to 0 whenever the pass it just finished
        // assigned something. The passes, and their order, are exactly the
        // nested version's -- but a `return` out of an *inner* loop is what
        // aeneas cannot translate, and this shape has no inner loop.
        let mut i = 0;
        let mut progress = false;
        loop {
            if i == self.clauses.len() {
                if !progress {
                    return None;
                }
                progress = false;
                i = 0;
                continue;
            }
            match self.status(i) {
                Status::Conflict => return Some(i),
                Status::Unit(lit) => {
                    self.assign(lit.var, !lit.negated, Some(i));
                    progress = true;
                }
                Status::Silent => {}
            }
            i += 1;
        }
    }

    fn bump(&mut self, var: u16) {
        let i = var as usize;
        self.activity[i] = self.activity[i].saturating_add(1);
    }

    fn decay(&mut self) {
        for i in 0..self.activity.len() {
            self.activity[i] >>= 1;
        }
    }

    // First-UIP conflict analysis.
    //
    // Start from the falsified clause and repeatedly resolve it against the
    // reason of its most recently assigned conflict-level literal. Each
    // resolution step replaces one conflict-level literal by the literals that
    // forced it; the process ends when exactly one conflict-level literal is
    // left -- the first unique implication point, the single assignment of this
    // level that the conflict provably depends on.
    //
    // Returns the learned clause with its asserting literal (the negated UIP)
    // first, and the level to jump back to: the highest level any *other*
    // literal of the clause was assigned at. That level is strictly below the
    // conflict level, which is what makes the search progress.
    fn analyze(&mut self, conflict: usize) -> (Clause, usize) {
        let conflict_level = self.decision_level();
        // Literals from levels below the conflict level; they go into the
        // learned clause as they are, already false under the assignment.
        let mut lower: Vec<Literal> = Vec::new();
        // Conflict-level literals seen but not yet resolved away.
        let mut pending = 0;
        // Every variable `seen` was set for, so it can be cleared again.
        let mut marked: Vec<u16> = Vec::new();
        // Where in the trail the walk for the next literal to resolve resumes.
        let mut index = self.trail.len();
        let mut clause = conflict;
        // The variable the last resolution step was on, whose literal in
        // `clause` is therefore not part of the explanation.
        let mut resolved: Option<u16> = None;

        let uip = loop {
            for j in 0..self.clauses[clause].0.len() {
                let lit = self.clauses[clause].0[j].clone();
                let v = lit.var as usize;
                if Some(lit.var) == resolved || self.seen[v] {
                    continue;
                }
                // A level-0 literal is false under *every* extension of the
                // level-0 assignment, so it explains nothing and would only
                // make the learned clause longer.
                if self.level[v] == 0 {
                    continue;
                }
                self.seen[v] = true;
                marked.push(lit.var);
                self.bump(lit.var);
                if self.level[v] == conflict_level {
                    pending += 1;
                } else {
                    lower.push(lit);
                }
            }

            // Walk the trail back to the most recent conflict-level literal
            // still pending: that is the one to resolve on next. The walk can
            // only run out while `pending > 0` if the trail were missing an
            // assignment it recorded, so this loop terminates.
            let v = loop {
                index -= 1;
                let v = self.trail[index];
                if self.seen[v as usize] && self.level[v as usize] == conflict_level {
                    break v;
                }
            };

            pending -= 1;
            if pending == 0 {
                break v;
            }

            // `v` is not the UIP, so it was propagated rather than decided (the
            // level's decision is the last conflict-level literal the walk can
            // reach, and it is reached with `pending == 1`).
            clause = self.reason[v as usize].expect("a propagated literal has a reason");
            resolved = Some(v);
        };

        // The asserting literal is the UIP's assignment, negated: false under
        // the assignment that produced the conflict, and forced true once the
        // backjump undoes that assignment.
        let mut lits = Vec::new();
        lits.push(Literal {
            var: uip,
            negated: self.value[uip as usize].expect("the UIP is assigned"),
        });

        let mut backjump = 0;
        for lit in lower {
            let l = self.level[lit.var as usize];
            if l > backjump {
                backjump = l;
            }
            lits.push(lit);
        }

        for v in marked {
            self.seen[v as usize] = false;
        }

        (Clause(lits), backjump)
    }

    // Undoes every assignment made above `level`, keeping the learned clauses
    // and the saved phases. Non-chronological: `level` comes from conflict
    // analysis and can be far below `decision_level() - 1`.
    fn backtrack(&mut self, level: usize) {
        if self.decision_level() <= level {
            return;
        }
        let target = self.trail_lim[level];
        while self.trail.len() > target {
            let v = self.trail.pop().unwrap() as usize;
            self.value[v] = None;
            self.reason[v] = None;
        }
        self.trail_lim.truncate(level);
    }

    // The decision heuristic: the unassigned variable with the highest activity,
    // i.e. the one the most recent conflicts mentioned most often. Ties go to the
    // lowest index, which makes the search deterministic (and, before the first
    // conflict, identical to `sat_dpll`'s "first variable there is").
    fn pick_branch_var(&self) -> Option<u16> {
        let mut best: Option<u16> = None;
        let mut best_activity = 0;
        for v in 0..self.num_vars() {
            if self.value[v].is_some() || !self.occurs[v] {
                continue;
            }
            if best.is_none() || self.activity[v] > best_activity {
                best = Some(v as u16);
                best_activity = self.activity[v];
            }
        }
        best
    }

    // The CDCL loop: propagate, and either analyse the conflict it found or make
    // a decision. Returns whether the clause database is satisfiable; on `true`
    // the assignment in `value` is a model of it.
    fn solve(&mut self) -> bool {
        self.search(FIRST_RESTART)
    }

    // `solve`, with the first restart interval spelled out so the tests can
    // shrink it and make restarts the common case rather than a rare one.
    fn search(&mut self, first_restart: u32) -> bool {
        let mut budget = first_restart;
        let mut since_restart = 0;

        loop {
            match self.propagate() {
                Some(conflict) => {
                    self.conflicts += 1;
                    since_restart += 1;
                    if self.conflicts % DECAY_INTERVAL == 0 {
                        self.decay();
                    }

                    // A conflict with no decision above it is a conflict the
                    // level-0 assignments alone produce, and those are forced by
                    // the clauses themselves: unsatisfiable.
                    if self.decision_level() == 0 {
                        return false;
                    }

                    let (learned, backjump) = self.analyze(conflict);
                    self.backtrack(backjump);

                    // The learned clause is *asserting* at `backjump`: every
                    // literal but the first is false there, so the first is
                    // forced. Assigning it here rather than waiting for
                    // `propagate` to notice is not an optimization -- it is what
                    // records the new clause as the reason, so the next conflict
                    // analysis can resolve through this one.
                    let idx = self.clauses.len();
                    let asserting = learned.0[0].clone();
                    self.clauses.push(learned);
                    self.assign(asserting.var, !asserting.negated, Some(idx));
                }
                None => {
                    if since_restart >= budget {
                        // Abandon the trail, keep the clauses and the phases: the
                        // search restarts from a different order of decisions but
                        // with everything it learned, and phase saving means it
                        // re-reaches the same assignments cheaply.
                        self.backtrack(0);
                        since_restart = 0;
                        budget += budget / 2;
                        continue;
                    }

                    match self.pick_branch_var() {
                        // Nothing left to assign and nothing in conflict: every
                        // clause is satisfied.
                        None => return true,
                        Some(v) => {
                            self.trail_lim.push(self.trail.len());
                            let value = self.phase[v as usize];
                            self.assign(v, value, None);
                        }
                    }
                }
            }
        }
    }

    // How many clauses the search added to the ones it was given.
    fn learned(&self) -> usize {
        self.clauses.len() - self.problem_clauses
    }
}

/// CDCL on a CNF: [`SatResult::Unsat`] if it has no model, otherwise a value
/// for every variable it mentions.
///
/// Separate from [`solve_sat_with`] because the CNF is where CDCL's contract
/// actually lives -- the `Expr` layer above it is just the encoding -- and
/// because it is what a DIMACS front end wants.
///
/// [`SatResult::Unknown`] is not returned yet: `search` still decides every
/// formula it is given. The answer exists ahead of the counter that will
/// produce it, so that adding the counter is a change to one function rather
/// than to every signature above it.
pub fn solve_cnf(cnf: &Cnf) -> SatResult<Vec<(u16, bool)>> {
    let mut solver = Solver::new(cnf);
    if !solver.solve() {
        return SatResult::Unsat;
    }

    // Only variables the CNF mentions are ever assigned, so the assigned slots
    // are exactly the model.
    let mut model = Vec::new();
    for v in 0..solver.num_vars() {
        if let Some(b) = solver.value[v] {
            model.push((v as u16, b));
        }
    }
    SatResult::Sat(model)
}

/// CDCL on the CNF `transform` produces, returning a model of `expr`.
///
/// The valuation starts as `initial_valuation(collect_vars(expr))` for the same
/// reason `sat_dpll`'s does: callers get a map `evaluate` can run on, even for a
/// variable the encoding dropped. Gate variables the transformation introduced
/// are in the returned map too, and `evaluate` never looks at them.
pub fn solve_sat_with(expr: &Expr, transform: Transform) -> SatResult<Map> {
    let vars = collect_vars(expr);
    let mut val = initial_valuation(&vars);
    let cnf = encode(expr, transform);

    match solve_cnf(&cnf) {
        SatResult::Unsat => SatResult::Unsat,
        SatResult::Unknown => SatResult::Unknown,
        SatResult::Sat(model) => {
            for (var, value) in model {
                val.insert(var, value);
            }
            SatResult::Sat(val)
        }
    }
}

/// CDCL on the default ([`Transform::Hybrid`]) encoding -- the same CNF
/// `sat_dpll::solve_sat` searches, so the two are directly comparable.
pub fn solve_sat(expr: &Expr) -> SatResult<Map> {
    solve_sat_with(expr, Transform::Hybrid)
}

pub static SAT_SOLVER_CDCL: SatSolver = SatSolver {
    solve: solve_sat,
    description: "cdcl",
};

#[cfg(test)]
fn lit(var: u16, negated: bool) -> Literal {
    Literal { var, negated }
}

// A tiny CNF over the variables 0..n, written as `(sign, var)` pairs, to keep
// the tests below readable.
#[cfg(test)]
fn cnf(clauses: &[&[(bool, u16)]]) -> Cnf {
    let mut out = Vec::new();
    for clause in clauses {
        let mut lits = Vec::new();
        for (negated, var) in clause.iter() {
            lits.push(lit(*var, *negated));
        }
        out.push(Clause(lits));
    }
    Cnf(out)
}

#[test]
fn status_reads_a_clause_against_the_assignment() {
    // (x ∨ ¬y ∨ z), with x and y assigned.
    let mut s = Solver::new(&cnf(&[&[(false, 0), (true, 1), (false, 2)]]));

    // Nothing assigned: two unassigned literals, so nothing is forced.
    assert!(matches!(s.status(0), Status::Silent));

    // x := true satisfies it outright.
    s.assign(0, true, None);
    assert!(matches!(s.status(0), Status::Silent));

    // x := false, y := true leaves only z.
    s.value[0] = Some(false);
    s.assign(1, true, None);
    match s.status(0) {
        Status::Unit(l) => assert_eq!(l, lit(2, false)),
        _ => panic!("expected a unit clause"),
    }

    // ...and z := false falsifies every literal.
    s.assign(2, false, None);
    assert!(matches!(s.status(0), Status::Conflict));
}

#[test]
fn status_of_the_empty_clause_is_a_conflict() {
    let s = Solver::new(&cnf(&[&[]]));
    assert!(matches!(s.status(0), Status::Conflict));
}

#[test]
fn propagate_chains_forced_assignments() {
    // (x) ∧ (¬x ∨ y) ∧ (¬y ∨ z): one unit clause drags the other two along.
    let mut s = Solver::new(&cnf(&[
        &[(false, 0)],
        &[(true, 0), (false, 1)],
        &[(true, 1), (false, 2)],
    ]));
    assert_eq!(s.propagate(), None);
    assert_eq!(s.value[0], Some(true));
    assert_eq!(s.value[1], Some(true));
    assert_eq!(s.value[2], Some(true));
    // All three were propagated, so each has the clause that forced it as its
    // reason -- and all sit at level 0, where no decision has been made.
    assert_eq!(s.reason[1], Some(1));
    assert_eq!(s.reason[2], Some(2));
    assert_eq!(s.level[2], 0);
}

#[test]
fn propagate_reports_the_falsified_clause() {
    // (x) ∧ (¬x): the second clause is the conflict.
    let mut s = Solver::new(&cnf(&[&[(false, 0)], &[(true, 0)]]));
    assert_eq!(s.propagate(), Some(1));
}

#[test]
fn analyze_learns_an_asserting_clause_and_a_backjump_level() {
    // Two independent decisions, the second of which forces a conflict:
    //   (¬a ∨ x) ∧ (¬b ∨ ¬x)
    // Decide a := true at level 1, b := true at level 2. Propagation then makes
    // x both true (first clause) and false (second), and the conflict depends on
    // both decisions -- so the learned clause has to mention both, and the jump
    // goes back to level 1.
    let a = 0;
    let b = 1;
    let x = 2;
    let mut s = Solver::new(&cnf(&[&[(true, a), (false, x)], &[(true, b), (true, x)]]));

    s.trail_lim.push(s.trail.len());
    s.assign(a, true, None);
    assert_eq!(s.propagate(), None);
    assert_eq!(s.value[x as usize], Some(true));

    s.trail_lim.push(s.trail.len());
    s.assign(b, true, None);
    let conflict = s.propagate().expect("b := true conflicts");

    let (learned, backjump) = s.analyze(conflict);
    assert_eq!(backjump, 1);
    // The UIP is `b`, the only level-2 assignment the conflict depends on, so the
    // clause is (¬b ∨ ¬x): under x := true, b is forced false. Note that 1-UIP
    // stops there rather than resolving ¬x further down to the decision that
    // forced it (which would give the weaker, longer (¬b ∨ ¬a)) -- the literals
    // of lower levels go into the clause exactly as the conflict found them.
    assert_eq!(learned, Clause(vec![lit(b, true), lit(x, true)]));
    // `analyze` must leave no scratch state behind.
    for v in 0..s.num_vars() {
        assert!(!s.seen[v]);
    }
}

#[test]
fn analyze_drops_level_zero_literals() {
    // (x) is a unit clause, so x := true holds at level 0 unconditionally. A
    // conflict that mentions ¬x should not carry it into the learned clause:
    //   (x) ∧ (¬a ∨ y) ∧ (¬x ∨ ¬y)
    let x = 0;
    let a = 1;
    let y = 2;
    let mut s = Solver::new(&cnf(&[
        &[(false, x)],
        &[(true, a), (false, y)],
        &[(true, x), (true, y)],
    ]));
    assert_eq!(s.propagate(), None);

    s.trail_lim.push(s.trail.len());
    s.assign(a, true, None);
    let conflict = s.propagate().expect("a := true conflicts");

    let (learned, backjump) = s.analyze(conflict);
    // Only `a` is left: the clause is the unit (¬a), and it holds globally.
    assert_eq!(learned, Clause(vec![lit(a, true)]));
    assert_eq!(backjump, 0);
}

#[test]
fn backtrack_undoes_only_the_levels_above() {
    let mut s = Solver::new(&cnf(&[&[(false, 0), (false, 1), (false, 2)]]));
    s.trail_lim.push(s.trail.len());
    s.assign(0, true, None);
    s.trail_lim.push(s.trail.len());
    s.assign(1, true, None);
    s.trail_lim.push(s.trail.len());
    s.assign(2, true, None);
    assert_eq!(s.decision_level(), 3);

    s.backtrack(1);
    assert_eq!(s.decision_level(), 1);
    assert_eq!(s.value[0], Some(true));
    assert_eq!(s.value[1], None);
    assert_eq!(s.value[2], None);
    // Phases survive a backjump -- that is what makes a restart cheap.
    assert!(s.phase[1]);
    assert!(s.phase[2]);
}

#[test]
fn learning_records_what_the_conflict_proved() {
    // (a ∨ b) ∧ (a ∨ ¬b) ∧ (¬a ∨ c). The first decision is a := false (phases
    // start false), which forces b true and then immediately falsifies the second
    // clause. Resolving that conflict against the reason for b eliminates b
    // entirely and leaves the unit (a) -- a fact about the formula, not about the
    // branch, so it is learned at level 0 and never revisited.
    let mut s = Solver::new(&cnf(&[
        &[(false, 0), (false, 1)],
        &[(false, 0), (true, 1)],
        &[(true, 0), (false, 2)],
    ]));
    assert!(s.solve());
    assert_eq!(s.learned(), 1, "one conflict, one clause");
    assert_eq!(s.clauses[s.problem_clauses], Clause(vec![lit(0, false)]));
    // The unit clause is what put `a` back at level 0, where nothing can undo it.
    assert_eq!(s.value[0], Some(true));
    assert_eq!(s.level[0], 0);
    // Every problem clause is satisfied by the assignment it stopped at.
    for i in 0..s.problem_clauses {
        let mut satisfied = false;
        for l in s.clauses[i].0.iter() {
            if s.lit_value(l) == Some(true) {
                satisfied = true;
            }
        }
        assert!(satisfied, "clause {i} is not satisfied by the model");
    }
}

#[test]
fn solve_cnf_refutes_an_unsatisfiable_cnf() {
    // All four clauses over two variables: nothing can satisfy them.
    let unsat = cnf(&[
        &[(false, 0), (false, 1)],
        &[(false, 0), (true, 1)],
        &[(true, 0), (false, 1)],
        &[(true, 0), (true, 1)],
    ]);
    assert_eq!(solve_cnf(&unsat), SatResult::Unsat);
}

#[test]
fn solve_cnf_assigns_every_variable_on_success() {
    let sat = cnf(&[&[(false, 0), (false, 1)], &[(true, 0), (false, 2)]]);
    let SatResult::Sat(model) = solve_cnf(&sat) else {
        panic!("satisfiable")
    };
    assert_eq!(model.len(), 3);
}

#[test]
fn solve_cnf_ignores_variables_no_clause_mentions() {
    // `letter('x')` is 120, so the slot arrays are 122 long -- but only two of
    // those variables exist, and deciding the other 120 would be 120 decision
    // levels spent on nothing.
    let sat = cnf(&[&[(false, letter('x')), (true, letter('y'))]]);
    let SatResult::Sat(model) = solve_cnf(&sat) else {
        panic!("satisfiable")
    };
    assert_eq!(model.len(), 2);
    assert_eq!(model[0].0, letter('x'));
    assert_eq!(model[1].0, letter('y'));
}

#[test]
fn solve_sat_agrees_with_the_naive_solver_on_the_examples() {
    use crate::expr::{evaluate, example_expr_sat, example_expr_unsat};

    for transform in [Transform::Naive, Transform::Tseitin, Transform::Hybrid] {
        let sat = example_expr_sat();
        let SatResult::Sat(val) = solve_sat_with(&sat, transform) else {
            panic!("example_expr_sat is satisfiable under {transform:?}")
        };
        assert_eq!(evaluate(&sat, &val), Ok(true), "{transform:?}");

        assert_eq!(
            solve_sat_with(&example_expr_unsat(), transform),
            SatResult::Unsat,
            "{transform:?}"
        );
    }
}

#[test]
fn solve_sat_matches_the_naive_solver() {
    use crate::expr::parse_expr;

    // The same formulas `sat_dpll` is checked on: negation, backtracking, and
    // the variable-free edge cases (where the CNF is empty or holds the empty
    // clause, and CDCL never gets to make a decision at all).
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
        for transform in [Transform::Naive, Transform::Tseitin, Transform::Hybrid] {
            let cdcl_res = solve_sat_with(&expr, transform);
            assert_eq!(
                matches!(cdcl_res, SatResult::Sat(_)),
                matches!(naive_res, SatResult::Sat(_)),
                "disagreement on {src} under {transform:?}"
            );
            if let SatResult::Sat(val) = cdcl_res {
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
fn solve_sat_matches_the_naive_solver_on_random_3_sat() {
    // The real test of the conflict machinery: a few hundred random 3-SAT
    // instances at the phase transition (clause/variable ratio 4.26), where the
    // SAT/UNSAT split is near even, checked against the proved-correct naive
    // solver -- verdict for verdict, and model-checked where it says SAT.
    //
    // Eight variables keeps `naive`'s 2^n enumeration cheap enough to run in a
    // debug build. The generator is a plain LCG so the set is fixed: a failure
    // here is reproducible, and shrinking it by hand is possible.
    use crate::expr::evaluate;

    const VARS: u16 = 8;
    const CLAUSES: usize = 34;
    const INSTANCES: usize = 300;

    let mut state: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = move |n: u64| {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (state >> 33) % n
    };

    let mut sat_seen = 0;
    let mut unsat_seen = 0;

    for instance in 0..INSTANCES {
        // Build the instance as an `Expr` in CNF, the way `dimacs` does, so all
        // three solvers can take it unchanged.
        let mut formula: Option<Expr> = None;
        for _ in 0..CLAUSES {
            let mut clause: Option<Expr> = None;
            for _ in 0..3 {
                let var = next(VARS as u64) as u16;
                let atom = Expr::Variable(var);
                let l = if next(2) == 1 {
                    Expr::Neg(Box::new(atom))
                } else {
                    atom
                };
                clause = Some(match clause {
                    None => l,
                    Some(c) => Expr::Disj(Box::new(c), Box::new(l)),
                });
            }
            let clause = clause.unwrap();
            formula = Some(match formula {
                None => clause,
                Some(f) => Expr::Conj(Box::new(f), Box::new(clause)),
            });
        }
        let expr = formula.unwrap();

        let naive_res = crate::sat_naive::solve_sat(&expr);
        let cdcl_res = solve_sat(&expr);
        assert_eq!(
            matches!(cdcl_res, SatResult::Sat(_)),
            matches!(naive_res, SatResult::Sat(_)),
            "disagreement on random instance {instance}: {expr}"
        );
        match cdcl_res {
            SatResult::Sat(val) => {
                sat_seen += 1;
                assert_eq!(
                    evaluate(&expr, &val),
                    Ok(true),
                    "bad witness for random instance {instance}: {expr}"
                );
            }
            SatResult::Unsat => unsat_seen += 1,
            SatResult::Unknown => panic!("gave up on random instance {instance}: {expr}"),
        }
    }

    // The point of the 4.26 ratio: both verdicts have to show up, or the test
    // is only exercising one half of the search.
    assert!(sat_seen > 20, "only {sat_seen} satisfiable instances");
    assert!(unsat_seen > 20, "only {unsat_seen} unsatisfiable instances");
}

#[test]
fn solve_sat_matches_dpll_on_the_shared_encoding() {
    // CDCL and DPLL run on the *same* CNF (`sat_dpll::encode` under
    // `Transform::Hybrid`), so any disagreement is in the search, not the
    // encoding. The models need not match -- different searches find different
    // ones -- so only the verdict is compared, plus soundness of CDCL's model.
    use crate::expr::{evaluate, parse_expr};

    for src in [
        "T",
        "F",
        "(x & ~x)",
        "((x | y) & (~x | ~y))",
        "~(~x & ~(y | z))",
        "((x | y) & ((~x | z) & (~y | ~z)))",
        "(((a | b) & (~a | c)) & ((~b | ~c) & (a | ~c)))",
    ] {
        let expr = parse_expr(src).unwrap().1;
        let dpll_res = crate::sat_dpll::solve_sat(&expr);
        let cdcl_res = solve_sat(&expr);
        assert_eq!(
            matches!(cdcl_res, SatResult::Sat(_)),
            matches!(dpll_res, SatResult::Sat(_)),
            "disagreement on {src}"
        );
        if let SatResult::Sat(val) = cdcl_res {
            assert_eq!(evaluate(&expr, &val), Ok(true), "bad witness for {src}");
        }
    }
}

#[test]
fn refutes_the_pigeonhole_principle() {
    // Five pigeons into four holes: the standard structured-UNSAT family, and the
    // one that documents the limit of every resolution-based solver (its
    // refutations grow exponentially in the number of holes). Small enough here
    // that it is a termination-and-verdict test, not a benchmark -- but it does
    // exercise long conflict chains and restarts, which the random 3-SAT
    // instances above mostly do not.
    const PIGEONS: u16 = 5;
    const HOLES: u16 = 4;
    let var = |pigeon: u16, hole: u16| pigeon * HOLES + hole;

    let mut clauses = Vec::new();
    // Every pigeon sits in some hole.
    for p in 0..PIGEONS {
        let mut lits = Vec::new();
        for h in 0..HOLES {
            lits.push(lit(var(p, h), false));
        }
        clauses.push(Clause(lits));
    }
    // No hole takes two pigeons.
    for h in 0..HOLES {
        for p in 0..PIGEONS {
            for q in (p + 1)..PIGEONS {
                clauses.push(Clause(vec![lit(var(p, h), true), lit(var(q, h), true)]));
            }
        }
    }

    assert_eq!(solve_cnf(&Cnf(clauses)), SatResult::Unsat);
}

#[test]
fn restarts_do_not_lose_the_answer() {
    // A restart abandons the trail, so a solver that restarts constantly must
    // still terminate with the right verdict -- and with a budget of 1 every
    // single conflict triggers one.
    let unsat = cnf(&[
        &[(false, 0), (false, 1)],
        &[(false, 0), (true, 1)],
        &[(true, 0), (false, 1)],
        &[(true, 0), (true, 1)],
    ]);
    let mut s = Solver::new(&unsat);
    assert!(!s.search(1));

    // The same, satisfiable: (x ∨ y) ∧ (¬x ∨ y) forces y.
    let sat = cnf(&[
        &[(false, letter('x')), (false, letter('y'))],
        &[(true, letter('x')), (false, letter('y'))],
    ]);
    let mut s = Solver::new(&sat);
    assert!(s.search(1));
    assert_eq!(s.value[letter('y') as usize], Some(true));
}
