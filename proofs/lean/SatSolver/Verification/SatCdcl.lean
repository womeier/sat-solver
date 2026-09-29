/- CDCL (`sat_cdcl`): soundness and completeness of the whole solver, and the conflict
analysis at the heart of it.

`sat_cdcl.solve_sat_sound` and `solve_sat_complete` are worded exactly as `SatDpll.lean`'s
proved pair, because CDCL is meant to be a drop-in replacement for DPLL on the identical
CNF. Beneath them is a tree of nine statements, and all nine are proved: `analyze.spec`
(1-UIP conflict analysis, given a well-formed state), the four obligations that establish
and preserve that state (`new`, `assign`, `propagate`, `backtrack`),
`Solver.search.spec` (the CDCL loop -- soundness, completeness *and* termination), the
`solve_cnf` pair (CDCL's contract on a CNF, which is what a DIMACS front end calls) and
the two roots. `conflictState.hypotheses` exhibits a state satisfying every hypothesis
`analyze.spec` takes, so that theorem is not vacuous either.

The roots carry two bounds `sat_dpll`'s do not, and they are exponential in the number of
variables: `Solver.searchMeasure` is what makes the search terminate, and the same measure
bounds the conflicts still to come -- which the Rust counts in a `u32`. So the theorems
here speak about expressions of a handful of variables. That is a statement about the
counter, not about the solver; see "The termination measure" and `searchRoom`.

`SatSolver/PrintAxioms.lean` checks `sorry`-freedom per theorem. The two
`native_decide` axioms the roots report come in with the extraction, not with any proof:
Aeneas discharges "this string literal is at most `u32::MAX` bytes" that way, and
`analyze_loop0` holds two `.expect` messages.

Stated the way the rest of this directory was (see `PLAN.md`): the whole tree
top-down first, so the shapes are fixed and mutually consistent, then discharged from
the leaves up.

### What the statement says

`analyze` is handed the index of a clause every literal of which is false, and returns
a *learned* clause together with a *backjump level*. Four things have to hold:

1. **Resolution soundness.** The learned clause is entailed by the clause database it
   started from (`Entails`). This is the invariant the whole module rests on, and the
   one that makes CDCL's proof qualitatively different from DPLL's: `search` appends
   the learned clause to the database, so the database the next conflict is analysed
   against is only sound because this holds of every earlier conflict.
2. **It is false under the current assignment**, so appending it is what makes the
   search *move*: the state it backjumps into is not one it has been in before.
3. **It is asserting at the backjump level**: the head literal is the negated UIP and
   sits at the conflict level, every other literal sits at a level `≤ backjump`, and
   no literal sits at level 0. So undoing every assignment above `backjump` leaves
   the tail still false and the head unassigned -- and hence forced.
4. **The backjump level is strictly below the conflict level**, which is what makes
   the search progress rather than re-derive the same conflict.

Plus a frame condition: `analyze` leaves every field of the solver alone except
`activity` (the VSIDS bumps). In particular the `seen` scratch array comes back
exactly as it went in, which is the proof obligation the mutation-for-speed in
`analyze` creates and which the Rust tests check behaviourally.

### The implication graph

There is no graph data structure to model. The graph is implicit in three slot arrays
and the trail (`Solver.WF` below): nodes are the assigned variables, the in-edges of
`v` are the literals of `db[reason v]`, and `trail` is a topological order of it *by
construction* -- when `propagate` assigns `v` from a unit clause every other literal
of that clause is already false, hence already assigned, hence already earlier on the
trail. That is the whole acyclicity argument, and it is why the reasoning here is
induction on trail position rather than anything resembling a reachability fixpoint.
-/
import SatSolver.Extraction
import SatSolver.Verification.Prelude
import SatSolver.Verification.Cnf
import SatSolver.Verification.CollectVars
import SatSolver.Verification.SatDpll

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

/- The loop specs below run `simp_all` over the wide contexts `-loops-to-rec` produces
(one parameter per solver field), which the default budget does not cover. -/
set_option maxHeartbeats 1000000

namespace sat_solver

/-! ### Entailment and resolution

The only genuinely logical content in conflict analysis: each step of `analyze`'s
outer loop is one resolution step, and resolution preserves entailment. -/

/-- `db` entails `cl` when every valuation satisfying `db` satisfies `cl`. Appending an
    entailed clause to a CNF cannot change what satisfies it, which is why learning is
    sound. -/
def Entails (db : List (List cnf.Literal)) (cl : List cnf.Literal) : Prop :=
  ∀ w : Std.U16 → Bool, Cnf.eval w db = true → Clause.eval w cl = true

/-- A clause of the database is entailed by it. This is where every resolution chain
    in `analyze` bottoms out: the conflicting clause, and each `reason`. -/
theorem Entails.of_mem {db : List (List cnf.Literal)} {cl : List cnf.Literal}
    (h : cl ∈ db) : Entails db cl := by
  intro w hdb
  simp only [Cnf.eval, List.all_eq_true] at hdb
  exact hdb cl h

/-- **Adding literals to an entailed clause keeps it entailed.** Conflict analysis
    needs this because its derived clause is not built by resolution alone: the scan
    folds the clause under resolution into a set of marks, which loses both the order
    and the duplicates, and what comes back out is a clause with the same literals in
    a different arrangement. -/
theorem Entails.weaken {db : List (List cnf.Literal)} {c d : List cnf.Literal}
    (h : Entails db c) (hsub : ∀ lit ∈ c, lit ∈ d) : Entails db d := by
  intro w hdb
  have := h w hdb
  simp only [Clause.eval, List.any_eq_true] at this ⊢
  obtain ⟨l, hl, hle⟩ := this
  exact ⟨l, hsub l hl, hle⟩

/-- A literal is true under `w` exactly when `w` disagrees with its `negated` flag. -/
theorem Literal.eval_true_iff (w : Std.U16 → Bool) (lit : cnf.Literal) :
    Literal.eval w lit = true ↔ w lit.var = !lit.negated := by
  simp only [Literal.eval]
  cases lit.negated <;> simp

/-- **Resolution is sound.** If `db` entails both `c` and `d`, every literal of `c` on
    `v` has polarity `p` and every literal of `d` on `v` the opposite polarity, then
    `db` entails the resolvent: their concatenation with every literal of `v` dropped.

    The two polarity hypotheses are the whole content of "this is a resolution step
    rather than an unsound deletion". In `analyze` they come from the assignment:
    the clause being resolved has `v` *false* and `v`'s reason has `v` *true*, so the
    literals disagree. -/
theorem Entails.resolution {db : List (List cnf.Literal)} {c d : List cnf.Literal}
    {v : Std.U16} {p : Bool} (hc : Entails db c) (hd : Entails db d)
    (hcp : ∀ lit ∈ c, lit.var = v → lit.negated = p)
    (hdp : ∀ lit ∈ d, lit.var = v → lit.negated = !p) :
    Entails db ((c.filter (fun lit => lit.var != v)) ++
                (d.filter (fun lit => lit.var != v))) := by
  intro w hdb
  have hc' := hc w hdb
  have hd' := hd w hdb
  simp only [Clause.eval, List.any_eq_true] at hc' hd'
  obtain ⟨l1, hl1, hl1e⟩ := hc'
  obtain ⟨l2, hl2, hl2e⟩ := hd'
  simp only [Clause.eval, List.any_append, Bool.or_eq_true, List.any_eq_true,
    List.mem_filter, bne_iff_ne, ne_eq]
  by_cases h1 : l1.var = v
  · by_cases h2 : l2.var = v
    · -- Both clauses are satisfied only on their `v` literal, and those disagree.
      exfalso
      rw [Literal.eval_true_iff] at hl1e hl2e
      rw [h1, hcp l1 hl1 h1] at hl1e
      rw [h2, hdp l2 hl2 h2] at hl2e
      rw [hl1e] at hl2e
      cases p <;> simp at hl2e
    · exact Or.inr ⟨l2, ⟨hl2, h2⟩, hl2e⟩
  · exact Or.inl ⟨l1, ⟨hl1, h1⟩, hl1e⟩

/-! ### Reading the solver state

Accessors that turn the extracted slot arrays into ordinary Lean values, so nothing
below has to touch `alloc.vec.Vec` or the `core.option.Option` wrappers. Each reads
out of range as "absent", which `Solver.WF` rules out for every variable that matters. -/

/-- The clause database as plain lists of literals. -/
def Solver.db (s : sat_cdcl.Solver) : List (List cnf.Literal) :=
  s.clauses.val.map (fun cl => cl.val)

/-- Clause `i` of the database. -/
def Solver.clauseAt (s : sat_cdcl.Solver) (i : Std.Usize) : Option (List cnf.Literal) :=
  (Solver.db s)[i.val]?

/-- The value assigned to `v`, or `none` when it is unassigned. -/
def Solver.valueOf (s : sat_cdcl.Solver) (v : Std.U16) : Option Bool :=
  match s.value.val[v.val]? with
  | some (some b) => some b
  | _ => none

/-- The clause that forced `v`, or `none` for a decision (or an unassigned variable). -/
def Solver.reasonOf (s : sat_cdcl.Solver) (v : Std.U16) : Option Std.Usize :=
  match s.reason.val[v.val]? with
  | some (some r) => some r
  | _ => none

/-- The decision level `v` was assigned at. Stale while `v` is unassigned, which is
    exactly the implicit invariant the Rust relies on: `level` is only ever read for
    an assigned variable, and `Solver.WF` is what makes that explicit. -/
def Solver.levelOf (s : sat_cdcl.Solver) (v : Std.U16) : Nat :=
  (s.level.val[v.val]?).elim 0 (·.val)

/-- The current decision level: `trail_lim`'s length *is* the level. -/
def Solver.decisionLevel (s : sat_cdcl.Solver) : Nat := s.trail_lim.val.length

/-- `lit` is false under the partial assignment. -/
def Solver.litFalse (s : sat_cdcl.Solver) (lit : cnf.Literal) : Prop :=
  Solver.valueOf s lit.var = some lit.negated

/-- `lit` is true under the partial assignment. -/
def Solver.litTrue (s : sat_cdcl.Solver) (lit : cnf.Literal) : Prop :=
  Solver.valueOf s lit.var = some (!lit.negated)

/-- The literal on `v` the assignment makes true. -/
def Solver.trueLit (s : sat_cdcl.Solver) (v : Std.U16) : cnf.Literal :=
  { var := v, negated := !((Solver.valueOf s v).getD false) }

/-- The literal on `v` the assignment makes false -- the one conflict analysis puts into
    the learned clause. `analyze` never builds it explicitly except for the UIP, but it
    is what the marked variables stand for. -/
def Solver.falseLit (s : sat_cdcl.Solver) (v : Std.U16) : cnf.Literal :=
  { var := v, negated := (Solver.valueOf s v).getD false }

/-- A false literal really is false under any total valuation extending the
    assignment. This is the bridge from the partial assignment to `Literal.eval`. -/
theorem Solver.litFalse.eval {s : sat_cdcl.Solver} {lit : cnf.Literal}
    {w : Std.U16 → Bool} (h : Solver.litFalse s lit)
    (hw : ∀ v b, Solver.valueOf s v = some b → w v = b) :
    Literal.eval w lit = false := by
  have := hw lit.var lit.negated h
  simp only [Literal.eval, this]
  cases lit.negated <;> simp

/-! ### The implication graph, as an invariant on the slot arrays -/

/-- What `analyze` assumes about the state it is handed. Nodes of the implication
    graph are the assigned variables; `reason_wf` is its edge relation *and* its
    acyclicity, since it forces every antecedent of `v` to sit earlier on the trail. -/
structure Solver.WF (s : sat_cdcl.Solver) : Prop where
  /-- Every variable with a value slot has a level, a reason, a saved phase, a `seen`
      slot and an activity score: `Solver::new` grows the slot arrays together. -/
  level_length : s.level.val.length = s.value.val.length
  reason_length : s.reason.val.length = s.value.val.length
  seen_length : s.seen.val.length = s.value.val.length
  activity_length : s.activity.val.length = s.value.val.length
  /-- `phase` is the one slot array `analyze` never reads, which is why this field was
      not here until `assign` needed it: `assign` writes the saved phase on every
      assignment, and `search` reads it to pick a decision's polarity. -/
  phase_length : s.phase.val.length = s.value.val.length
  /-- `occurs` is the other array `analyze` never reads, and the fifth field the statements
      did not have: it marks the variables the *problem* mentions, and `pick_branch_var`,
      which decides only on a marked variable, indexes it by a value slot. Nothing writes
      it after `Solver::new`, which is why every proof below discharges this field by
      rewriting with "`occurs` is untouched". -/
  occurs_length : s.occurs.val.length = s.value.val.length
  /-- **Clauses are short.** The only assumption here that is about the *input* rather
      than about the solver: `analyze` counts conflict-level literals in an `i32` and
      pushes the rest onto `Vec`s, and a clause is scanned in one pass, so a clause plus
      a trail's worth of marks has to fit. At most `2 ^ 31 - 65537` literals per clause
      on any platform -- the parser would run out of memory first. -/
  db_len : ∀ d ∈ Solver.db s, d.length + 2 ^ 16 ≤ Std.I32.max
  /-- **Every variable a clause mentions has a slot.** `Solver::new` sizes the arrays from
      the CNF it is given, and a learned clause is built out of variables that are on the
      trail, so they already have one.

      The fourth field the statements did not have: `analyze` never needs it (it reads
      only literals the assignment has already falsified, which are assigned and therefore
      in range), but `propagate` scans *every* clause, including ones no literal of which
      is assigned yet. -/
  db_vars : ∀ cl ∈ Solver.db s, ∀ lit ∈ cl, lit.var.val < s.value.val.length
  /-- Only variables with a slot reach the trail. -/
  trail_bound : ∀ v ∈ s.trail.val, v.val < s.value.val.length
  /-- The trail holds exactly the assigned variables, each of them once. -/
  trail_iff : ∀ v : Std.U16, (Solver.valueOf s v).isSome = true ↔ v ∈ s.trail.val
  trail_nodup : s.trail.val.Nodup
  /-- `analyze` is entered with every scratch flag clear, and restores that. -/
  seen_clear : ∀ b ∈ s.seen.val, b = false
  /-- No assignment sits above the current decision level. -/
  level_le : ∀ v ∈ s.trail.val, Solver.levelOf s v ≤ Solver.decisionLevel s
  /-- Levels along the trail never decrease: `backtrack` pops a suffix, and `assign`
      only ever appends at the current level. -/
  level_mono : ∀ i j (hi : i < s.trail.val.length) (hj : j < s.trail.val.length), i ≤ j →
    Solver.levelOf s s.trail.val[i] ≤ Solver.levelOf s s.trail.val[j]
  /-- **The edges.** A variable with a reason was forced by a clause of the database
      that had become unit on it: the clause holds the literal of `v` the assignment
      makes true, and every *other* literal of the clause is false, was assigned
      earlier on the trail, and sits at no higher level.

      "Every other literal", rather than "every literal on another variable", is what
      rules out a reason clause holding both polarities of `v` -- such a clause is
      never unit, since falsifying one of the two literals assigns the other. The
      strict trail inequality is also what makes this the acyclicity of the implication
      graph: it is unsatisfiable for a literal on `v` itself. -/
  reason_wf : ∀ (v : Std.U16) (r : Std.Usize), Solver.reasonOf s v = some r →
    ∃ cl, Solver.clauseAt s r = some cl ∧
      Solver.trueLit s v ∈ cl ∧
      (∀ lit ∈ cl, lit ≠ Solver.trueLit s v →
        Solver.litFalse s lit ∧
        s.trail.val.idxOf lit.var < s.trail.val.idxOf v ∧
        Solver.levelOf s lit.var ≤ Solver.levelOf s v)
  /-- **A `reason` is only meaningful while its variable is assigned.** `backtrack`
      clears `reason` as it pops, so a variable off the trail has none.

      The third field the statements did not have and the proofs needed: without it, a
      variable off the trail could carry a stale reason clause, and `backtrack` -- which
      unassigns that clause's literals -- could not be shown to preserve `reason_wf` for
      it. `assign` is what maintains it: it sets `reason` only for the variable it pushes
      onto the trail. -/
  reason_assigned : ∀ v : Std.U16, Solver.reasonOf s v ≠ none → v ∈ s.trail.val
  /-- Nothing is *decided* at level 0: `assign` only reaches level 0 from `propagate`,
      since a decision pushes `trail_lim` first. So a level-0 assignment always has a
      reason, and `entails_trueLit_of_level_zero` can walk it down to the database. -/
  level_zero_has_reason : ∀ v ∈ s.trail.val, Solver.levelOf s v = 0 →
    ∃ r, Solver.reasonOf s v = some r
  /-- Every level above 0 *that anything is assigned at* was opened by a decision -- a
      trail entry at that level with no reason.

      Quantified over the trail rather than over `1 ≤ k ≤ decisionLevel`, which is how
      this field read when it was written and which is not an invariant of the code:
      `search` pushes `trail_lim` and *then* calls `assign`, so between the two the top
      level exists and is empty. Weakening it costs nothing -- the levels `analyze`
      reasons about are levels its conflict clause has literals at, so they are
      inhabited -- and it is what `assign` can actually preserve. -/
  decision_of_level : ∀ u ∈ s.trail.val, 0 < Solver.levelOf s u →
    ∃ v ∈ s.trail.val, Solver.levelOf s v = Solver.levelOf s u ∧
      Solver.reasonOf s v = none
  /-- **`trail_lim[j]` is where level `j + 1` begins on the trail.** `search` pushes
      `trail.len()` onto `trail_lim` just before deciding, so the entries before
      `trail_lim[j]` are exactly those at levels `≤ j`.

      This field was not here either until `backtrack` needed it: nothing else in the
      solver reads `trail_lim`'s *contents* (`decisionLevel` is only its length), but
      "`backtrack level` undoes exactly the assignments above `level`" is a statement
      about `trail_lim[level]`, and without this it is not a statement about levels at
      all. -/
  trail_lim_spec : ∀ (j : Nat) (hj : j < s.trail_lim.val.length),
    (s.trail_lim.val[j]).val ≤ s.trail.val.length ∧
    ∀ (i : Nat) (hi : i < s.trail.val.length),
      (i < (s.trail_lim.val[j]).val ↔ Solver.levelOf s s.trail.val[i] ≤ j)
  /-- **A level's decision comes first.** `assign` pushes the decision before anything
      it propagates, so the one entry at a level above 0 with no reason is the earliest
      entry at that level.

      This is what makes `analyze`'s `.expect("a propagated literal has a reason")`
      safe: while more than one conflict-level variable is still pending there is one
      behind the variable the walk just returned, so that variable is not the decision.
      It does not follow from `level_mono`, which makes each level's entries contiguous
      but says nothing about their order within the level. -/
  decision_first : ∀ u ∈ s.trail.val, 0 < Solver.levelOf s u →
    Solver.reasonOf s u = none →
    ∀ w ∈ s.trail.val, Solver.levelOf s w = Solver.levelOf s u →
      s.trail.val.idxOf u ≤ s.trail.val.idxOf w

/-- A clause the database has at some index is a member of it. -/
theorem Solver.mem_db_of_clauseAt {s : sat_cdcl.Solver} {i : Std.Usize}
    {cl : List cnf.Literal} (h : Solver.clauseAt s i = some cl) : cl ∈ Solver.db s :=
  List.mem_of_getElem? h

/-- The database's list-of-lists view and the extracted `Vec` of `Vec`s agree. -/
theorem Solver.clauseAt_eq {s : sat_cdcl.Solver} {i : Std.Usize} {cl : List cnf.Literal}
    (h : Solver.clauseAt s i = some cl) :
    ∃ c : cnf.Clause, s.clauses.val[i.val]? = some c ∧ c.val = cl := by
  simp only [Solver.clauseAt, Solver.db, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨c, hc, hcl⟩ := h
  exact ⟨c, hc, hcl⟩

/-- **The trail is short.** Its entries are distinct `u16` variables, so there are at
    most `2 ^ 16` of them. That is what keeps `analyze`'s `pending` counter -- an `i32`,
    since that is what Rust infers for it -- from overflowing. -/
theorem Solver.trail_length_le {s : sat_cdcl.Solver} (hwf : Solver.WF s) :
    s.trail.val.length ≤ 2 ^ 16 := by
  have hmap : (s.trail.val.map (·.val)).Nodup := by
    refine List.Nodup.map ?_ hwf.trail_nodup
    intro a b hab
    exact (Std.UScalar.eq_equiv a b).mpr (by simpa using hab)
  have hsub : s.trail.val.map (·.val) ⊆ List.range (2 ^ 16) := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨u, _, rfl⟩ := hx
    simp only [List.mem_range]
    have := u.hBounds
    simp_all
  simpa using (List.Nodup.subperm hmap hsub).length_le

/-- A literal the assignment makes false cannot be satisfied by a valuation that
    satisfies the unit clause on its variable. Both `entails_trueLit_of_level_zero` and
    `Entails.drop_level_zero` turn on this. -/
theorem Solver.eval_false_of_litFalse {s : sat_cdcl.Solver} {l : cnf.Literal}
    {w : Std.U16 → Bool} (hfl : Solver.litFalse s l)
    (h : Clause.eval w [Solver.trueLit s l.var] = true) : Literal.eval w l = false := by
  have hval : Solver.valueOf s l.var = some l.negated := hfl
  simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false,
    Literal.eval_true_iff, Solver.trueLit, Bool.not_not, hval, Option.getD_some] at h
  simp only [Literal.eval, h]
  cases l.negated <;> simp

/-- **Level-0 assignments are facts about the formula, not about the branch.** A
    variable assigned at level 0 was forced by a chain of clauses of the database, so
    the database entails the unit clause asserting it.

    This is what licenses the one step of `analyze` that is *not* resolution against a
    reason: it skips the level-0 literals of the clause it is resolving. Dropping a
    literal from a clause is in general unsound -- here it is a resolution step against
    the unit clause this lemma produces, so `Entails.resolution` covers it after all.

    The recursion is on trail position, which is the only well-founded order the
    implication graph comes with, and `reason_wf` is what makes it decrease. -/
theorem Solver.entails_trueLit_of_level_zero {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    (v : Std.U16) (hv : v ∈ s.trail.val) (h0 : Solver.levelOf s v = 0) :
    Entails (Solver.db s) [Solver.trueLit s v] := by
  obtain ⟨r, hr⟩ := hwf.level_zero_has_reason v hv h0
  obtain ⟨cl, hcl, htrue, hrest⟩ := hwf.reason_wf v r hr
  intro w hdb
  have hclw := Entails.of_mem (Solver.mem_db_of_clauseAt hcl) w hdb
  simp only [Clause.eval, List.any_eq_true] at hclw
  obtain ⟨l, hl, hlw⟩ := hclw
  by_cases hlv : l = Solver.trueLit s v
  · subst hlv
    simp [Clause.eval, hlw]
  · -- Any other literal of the reason is false under the assignment and sits earlier
    -- on the trail, so the recursion says the database entails *its* negation too --
    -- and then `w` cannot satisfy it, contradicting the clause being satisfied there.
    exfalso
    obtain ⟨hfalse, hidx, hle⟩ := hrest l hl hlv
    simp only [Solver.litFalse] at hfalse
    have hmem : l.var ∈ s.trail.val := by
      rw [← hwf.trail_iff, hfalse]; rfl
    have hlvl : Solver.levelOf s l.var = 0 := by omega
    have hrec := Solver.entails_trueLit_of_level_zero hwf l.var hmem hlvl w hdb
    rw [Solver.eval_false_of_litFalse hfalse hrec] at hlw
    simp at hlw
termination_by s.trail.val.idxOf v
decreasing_by omega

/-- **Level-0 literals can be dropped** from a clause all of whose literals are false:
    each of them is false under *every* model of the database, so the shorter clause is
    still entailed. This is the one step of `analyze` that is not resolution against a
    reason -- it is how the conflict clause loses its level-0 literals before the first
    resolution, and it is why the learned clause can be asserting at level 0. -/
theorem Entails.drop_level_zero {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    {cl : List cnf.Literal} (h : Entails (Solver.db s) cl)
    (hfalse : ∀ lit ∈ cl, Solver.litFalse s lit) :
    Entails (Solver.db s) (cl.filter (fun lit => !(Solver.levelOf s lit.var == 0))) := by
  intro w hdb
  have hcl := h w hdb
  simp only [Clause.eval, List.any_eq_true] at hcl
  obtain ⟨l, hl, hlw⟩ := hcl
  have hfl := hfalse l hl
  have hval : Solver.valueOf s l.var = some l.negated := hfl
  have hlvl : Solver.levelOf s l.var ≠ 0 := by
    intro h0
    have hmem : l.var ∈ s.trail.val := by rw [← hwf.trail_iff, hval]; rfl
    have hrec := Solver.entails_trueLit_of_level_zero hwf l.var hmem h0 w hdb
    rw [Solver.eval_false_of_litFalse hfl hrec] at hlw
    simp at hlw
  simp only [Clause.eval, List.any_eq_true, List.mem_filter]
  exact ⟨l, ⟨hl, by simp [hlvl]⟩, hlw⟩

/-- **Spec for `decision_level`**: `trail_lim`'s length *is* the decision level. -/
@[step]
theorem sat_cdcl.Solver.decision_level.spec (s : sat_cdcl.Solver) :
    sat_cdcl.Solver.decision_level s ⦃ (r : Std.Usize) =>
      r.val = Solver.decisionLevel s ⦄ := by
  unfold sat_cdcl.Solver.decision_level
  step*
  simpa [Solver.decisionLevel] using r_post

/-! ### Leaves: the two loops that do no reasoning

`analyze`'s last two loops are pure bookkeeping -- assemble the learned clause and its
backjump level, then clear the scratch flags. Both are fully discharged here; the
running-maximum and flag-clearing lemmas below are what the outer loop will consume. -/

/-- The running maximum `analyze`'s clause-assembly loop keeps: the highest level any
    literal of `ls` sits at, starting from `b`. -/
def maxLevel (lvl : List Std.Usize) (b : Nat) (ls : List cnf.Literal) : Nat :=
  ls.foldl (fun acc lit => max acc ((lvl[lit.var.val]?).elim 0 (·.val))) b

theorem le_maxLevel (lvl : List Std.Usize) (b : Nat) (ls : List cnf.Literal) :
    b ≤ maxLevel lvl b ls := by
  induction ls generalizing b with
  | nil => simp [maxLevel]
  | cons a rest ih => exact le_trans (le_max_left _ _) (ih _)

/-- The maximum is below `n` as soon as the starting point and every level is. This is
    what turns "every literal but the UIP sits below the conflict level" into "the
    backjump level is below the conflict level". -/
theorem maxLevel_le {lvl : List Std.Usize} {b n : Nat} {ls : List cnf.Literal}
    (hb : b ≤ n) (h : ∀ lit ∈ ls, (lvl[lit.var.val]?).elim 0 (·.val) ≤ n) :
    maxLevel lvl b ls ≤ n := by
  induction ls generalizing b with
  | nil => simpa [maxLevel] using hb
  | cons a rest ih =>
    exact ih (max_le hb (h a (by simp))) (fun lit hlit => h lit (by simp [hlit]))

theorem level_le_maxLevel {lvl : List Std.Usize} {b : Nat} {ls : List cnf.Literal}
    {lit : cnf.Literal} (h : lit ∈ ls) :
    (lvl[lit.var.val]?).elim 0 (·.val) ≤ maxLevel lvl b ls := by
  induction ls generalizing b with
  | nil => simp at h
  | cons a rest ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_trans (le_max_right b _) (le_maxLevel _ _ _)
    · exact ih h'

/-- **Spec for `analyze`'s clause-assembly loop**: it appends the lower-level literals
    to the clause under construction and maxes their levels into `backjump`. -/
@[step]
theorem sat_cdcl.Solver.analyze_loop0_loop2.spec
    (iter : alloc.vec.into_iter.IntoIter cnf.Literal) (lvl : alloc.vec.Vec Std.Usize)
    (lits : alloc.vec.Vec cnf.Literal) (backjump : Std.Usize)
    (hbound : ∀ lit ∈ iter.val, lit.var.val < lvl.val.length)
    (hlen : lits.val.length + iter.val.length ≤ Usize.max) :
    sat_cdcl.Solver.analyze_loop0_loop2 iter lvl lits backjump ⦃
      (lits' : alloc.vec.Vec cnf.Literal) (backjump' : Std.Usize) =>
        lits'.val = lits.val ++ iter.val
        ∧ backjump'.val = maxLevel lvl.val backjump.val iter.val ⦄ := by
  unfold sat_cdcl.Solver.analyze_loop0_loop2
  step*
  all_goals
    obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all [maxLevel]
    | cons e es =>
      try split
      all_goals try step*
      all_goals try (simp_all [maxLevel]; done)
      all_goals (simp_all [maxLevel])
      -- What is left is the `if` on the running maximum (`max` collapses on the
      -- branch condition) and the overflow bound for the next `push`.
      all_goals first
        | omega
        | (congr 1; omega)
termination_by iter.val.length
decreasing_by
  all_goals
    obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es => simp_all

/-- Clearing flag `i` when it is already clear changes nothing. -/
theorem List.set_false_of_getElem?_false {l : List Bool} {i : Nat}
    (h : l[i]? = some false) : l.set i false = l := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j = i
  · subst hj
    rw [List.getElem?_set_self (by grind [List.getElem?_eq_some_iff]), h]
  · rw [List.getElem?_set_ne (Ne.symm hj)]

@[simp]
theorem length_foldl_set_false (xs : List Std.U16) (l : List Bool) :
    (xs.foldl (fun l x => l.set x.val false) l).length = l.length := by
  induction xs generalizing l with
  | nil => simp
  | cons a rest ih => simp [ih]

theorem getElem?_foldl_set_false_of_not_mem {xs : List Std.U16} {l : List Bool} {i : Nat}
    (h : ∀ x ∈ xs, x.val ≠ i) :
    (xs.foldl (fun l x => l.set x.val false) l)[i]? = l[i]? := by
  induction xs generalizing l with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih (fun x hx => h x (by simp [hx]))]
    exact List.getElem?_set_ne (h a (by simp))

theorem getElem?_foldl_set_false_of_mem : ∀ (xs : List Std.U16) (l : List Bool)
    (x : Std.U16), x ∈ xs → x.val < l.length →
    (xs.foldl (fun l x => l.set x.val false) l)[x.val]? = some false := by
  intro xs
  induction xs with
  | nil => intro l x hx _; simp at hx
  | cons a rest ih =>
    intro l x hx hlt
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · by_cases hmem : ∃ y ∈ rest, y.val = x.val
      · obtain ⟨y, hy, hyv⟩ := hmem
        have := ih (l.set x.val false) y hy (by rw [List.length_set, hyv]; exact hlt)
        rwa [hyv] at this
      · rw [getElem?_foldl_set_false_of_not_mem (by grind)]
        exact List.getElem?_set_self (by simpa using hlt)
    · exact ih _ x hx' (by simpa using hlt)

/-- **Spec for `analyze`'s flag-clearing loop**: it clears exactly the marked slots. -/
@[step]
theorem sat_cdcl.Solver.analyze_loop0_loop3.spec
    (iter : alloc.vec.into_iter.IntoIter Std.U16) (flags : alloc.vec.Vec Bool)
    (hbound : ∀ x ∈ iter.val, x.val < flags.val.length) :
    sat_cdcl.Solver.analyze_loop0_loop3 iter flags ⦃
      (flags' : alloc.vec.Vec Bool) =>
        flags'.val = iter.val.foldl (fun l x => l.set x.val false) flags.val ⦄ := by
  unfold sat_cdcl.Solver.analyze_loop0_loop3
  step*
  all_goals
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
termination_by iter.val.length
decreasing_by
  obtain ⟨l, hl⟩ := iter
  cases l with
  | nil => simp_all
  | cons e es => simp_all

/-- **The scratch array really is restored.** If `flags` is `base` with exactly the
    variables of `xs` flipped, clearing `xs` gives `base` back -- which is the
    `s'.seen = s.seen` half of `analyze`'s frame condition, and the obligation that
    marking with a shared array rather than a local set creates. -/
theorem foldl_set_false_eq_base {base flags : List Bool} {xs : List Std.U16}
    (hlen : flags.length = base.length)
    (hbase : ∀ b ∈ base, b = false)
    (hbound : ∀ x ∈ xs, x.val < flags.length)
    (hother : ∀ i, (∀ x ∈ xs, x.val ≠ i) → flags[i]? = base[i]?) :
    xs.foldl (fun l x => l.set x.val false) flags = base := by
  apply List.ext_getElem?
  intro i
  by_cases hmem : ∃ x ∈ xs, x.val = i
  · obtain ⟨x, hx, rfl⟩ := hmem
    rw [getElem?_foldl_set_false_of_mem xs flags x hx (hbound x hx)]
    have hlt : x.val < base.length := by rw [← hlen]; exact hbound x hx
    rw [List.getElem?_eq_getElem hlt, hbase _ (List.getElem_mem hlt)]
  · rw [getElem?_foldl_set_false_of_not_mem (by grind), hother i (by grind)]

/-! ### The trail walk -/

/-- **Spec for `analyze`'s backward trail walk**: it returns the *latest* trail
position below `index` holding a marked conflict-level variable. "Latest" is what makes
the result the *first* UIP rather than just some UIP, and hence the learned clause the
smallest one this conflict supports.

The precondition is the interesting part, and the sharpest obligation in the file. The
walk is unguarded -- `index - 1` with no bounds test -- so on a `Usize` the subtraction
not underflowing has to be *proved*, and `hwitness` is what proves it: while a marked
conflict-level variable still sits behind the cursor, the walk stops at or before it.
In `analyze` that witness comes from `pending > 0` together with
`Solver.WF.decision_of_level`, which guarantees the level's own decision is reachable
as a last resort. Note `index` is initialized outside `analyze`'s outer loop and never
reset, so the witness has to be re-established across resolution steps, not merely
within one -- that is the price of visiting each trail position at most once. -/
@[step]
theorem sat_cdcl.Solver.analyze_loop0_loop1.spec
    (lvl : alloc.vec.Vec Std.Usize) (seen : alloc.vec.Vec Bool)
    (trail : alloc.vec.Vec Std.U16) (conflict_level index : Std.Usize)
    (hindex : index.val ≤ trail.val.length)
    (hbound : ∀ v ∈ trail.val, v.val < lvl.val.length ∧ v.val < seen.val.length)
    (hwitness : ∃ j u, j < index.val ∧ trail.val[j]? = some u ∧
      seen.val[u.val]? = some true ∧ lvl.val[u.val]? = some conflict_level) :
    sat_cdcl.Solver.analyze_loop0_loop1 lvl seen trail conflict_level index ⦃
      (index' : Std.Usize) (v : Std.U16) =>
        index'.val < index.val
        ∧ trail.val[index'.val]? = some v
        ∧ seen.val[v.val]? = some true
        ∧ lvl.val[v.val]? = some conflict_level
        ∧ ∀ k u, index'.val < k → k < index.val → trail.val[k]? = some u →
            ¬(seen.val[u.val]? = some true ∧ lvl.val[u.val]? = some conflict_level) ⦄ := by
  unfold sat_cdcl.Solver.analyze_loop0_loop1
  -- `step*` discharges the two recursive branches against this theorem's own
  -- statement, `index - 1` included: the witness moves down with the cursor, because
  -- the position just vacated is one the branch condition says is not the one sought.
  step*
  all_goals
    have hv3 : v3 ∈ trail.val := List.mem_of_getElem? v3_post
    have hb := hbound v3 hv3
    simp_all
  -- Left over is the stopping branch: the walk did move, and the range it skipped
  -- between the new cursor and the old one is empty.
  refine ⟨by omega, ?_⟩
  intro k u hk1 hk2
  omega
termination_by index.val
decreasing_by all_goals scalar_tac

/-! ### The resolution loop

`analyze`'s outer loop is where the reasoning is. Each iteration scans one clause, walks
back to the most recent conflict-level variable still pending, and -- unless that was
the last one -- resolves that variable's reason in. The clause it has derived is never
materialized: it lives in `lower` (the literals below the conflict level, as the clauses
they came from held them) and in the `seen` flags of the conflict-level variables still
behind the cursor. `Solver.resolvent` is that clause, and `Solver.Analyzing` is the
invariant tying it to the database. -/

/-- Has the scan marked `u`? -/
def Solver.isMarked (seen : List Bool) (u : Std.U16) : Bool := (seen[u.val]?).getD false

/-- The conflict-level variables the scan has marked and the walk has not resolved on
    yet: marked, at the conflict level, and still behind the cursor. `pending` counts
    exactly these, which is what supplies the trail walk its witness -- and why the
    walk's `index - 1` cannot underflow. -/
def Solver.pendingVars (s : sat_cdcl.Solver) (seen : List Bool)
    (conflict_level index : Nat) : List Std.U16 :=
  (s.trail.val.take index).filter
    (fun u => Solver.isMarked seen u && Solver.levelOf s u == conflict_level)

/-- **The clause conflict analysis has derived so far**: the collected lower-level
    literals, plus the false literal of every conflict-level variable still pending. -/
def Solver.resolvent (s : sat_cdcl.Solver) (seen : List Bool) (lower : List cnf.Literal)
    (conflict_level index : Nat) : List cnf.Literal :=
  lower ++ (Solver.pendingVars s seen conflict_level index).map (Solver.falseLit s)

/-- The literals of the clause under resolution that the scan carries into the
    resolvent: all but the one just resolved on, and all but the level-0 ones --
    `entails_trueLit_of_level_zero` is what licenses dropping those. -/
def Solver.carried (s : sat_cdcl.Solver) (cl : List cnf.Literal)
    (resolved : Option Std.U16) : List cnf.Literal :=
  cl.filter (fun lit => !(resolved == some lit.var) && !(Solver.levelOf s lit.var == 0))

/-- The pure model of `analyze`'s clause scan: walk the literals, skip the one just
    resolved on, the already-marked ones and the level-0 ones, and mark the rest --
    counting the conflict-level ones into `pending` and collecting the others into
    `lower`. `pending` is an `Int` because that is what the extraction makes of Rust's
    inferred `i32`.

    It takes the level *function* rather than the solver, because the loop hands its
    recursive call the solver `bump` returned: same levels, different `activity`. -/
def Solver.scan (lvl : Std.U16 → Nat) (resolved : Option Std.U16) (conflict_level : Nat) :
    List cnf.Literal → List Bool × List cnf.Literal × Int × List Std.U16 →
      List Bool × List cnf.Literal × Int × List Std.U16
  | [], acc => acc
  | lit :: rest, (seen, lower, pending, marked) =>
    if resolved = some lit.var ∨ Solver.isMarked seen lit.var = true ∨ lvl lit.var = 0 then
      Solver.scan lvl resolved conflict_level rest (seen, lower, pending, marked)
    else if lvl lit.var = conflict_level then
      Solver.scan lvl resolved conflict_level rest
        (seen.set lit.var.val true, lower, pending + 1, marked ++ [lit.var])
    else
      Solver.scan lvl resolved conflict_level rest
        (seen.set lit.var.val true, lower ++ [lit], pending, marked ++ [lit.var])

/-! ### Counting the pending marks

`pending` is a count, and the scan changes it one mark at a time. These two lemmas are
what turn "the array now says `true` at one more slot" into "the count went up by one":
the variable whose flag flipped occurs in the trail exactly once. -/

/-- Flipping exactly one element's verdict adds one to the count, provided the list
    holds that element once. -/
theorem List.length_filter_flip {α : Type} [DecidableEq α] (l : List α) (p q : α → Bool)
    (u : α) (hnodup : l.Nodup) (hmem : u ∈ l)
    (hother : ∀ w ∈ l, w ≠ u → p w = q w) (hpu : p u = true) (hqu : q u = false) :
    (l.filter p).length = (l.filter q).length + 1 := by
  induction l with
  | nil => simp at hmem
  | cons a rest ih =>
    obtain ⟨hnot, hrestnd⟩ := List.nodup_cons.mp hnodup
    rcases List.mem_cons.mp hmem with rfl | hrest
    · have hsame : rest.filter p = rest.filter q :=
        List.filter_congr fun w hw => hother w (by simp [hw]) (by rintro rfl; exact hnot hw)
      simp [hpu, hqu, hsame]
    · have hane : a ≠ u := by rintro rfl; exact hnot hrest
      have hpa : p a = q a := hother a (by simp) hane
      have hrec := ih hrestnd hrest fun w hw => hother w (by simp [hw])
      simp only [List.filter_cons, hpa]
      cases q a <;> simp [hrec]

/-- Marking a variable the filter rejects anyway leaves the list alone. -/
theorem List.filter_flip_of_reject {α : Type} [DecidableEq α] (l : List α)
    (p q : α → Bool) (u : α) (hother : ∀ w ∈ l, w ≠ u → p w = q w)
    (hpu : p u = false) (hqu : q u = false) :
    l.filter p = l.filter q :=
  List.filter_congr fun w _ => by
    by_cases h : w = u
    · subst h; rw [hpu, hqu]
    · exact hother w ‹_› h

/-- A variable the trail holds before the cursor is in the prefix the count runs over. -/
theorem Solver.mem_take_of_idxOf {s : sat_cdcl.Solver} {u : Std.U16} {index : Nat}
    (hmem : u ∈ s.trail.val) (hidx : s.trail.val.idxOf u < index) :
    u ∈ s.trail.val.take index := by
  have hget : (s.trail.val.take index)[s.trail.val.idxOf u]? = some u := by
    rw [List.getElem?_take_of_lt hidx]
    exact List.getElem?_idxOf hmem
  exact List.mem_of_getElem? hget

/-- The prefix the count runs over is duplicate-free. -/
theorem Solver.take_nodup {s : sat_cdcl.Solver} (hwf : Solver.WF s) (index : Nat) :
    (s.trail.val.take index).Nodup :=
  List.Nodup.sublist (List.take_sublist index _) hwf.trail_nodup

/-- Two scalars with the same value are the same scalar -- for variables, that two
    slots with the same index belong to the same variable. -/
theorem Solver.uscalar_eq_of_val {ty : Std.UScalarTy} {u w : Std.UScalar ty}
    (h : w.val = u.val) : w = u :=
  (Std.UScalar.eq_equiv w u).mpr (by simpa using h)

/-- **Marking a fresh conflict-level variable raises the count by one.** -/
theorem Solver.length_pendingVars_mark {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    {seen : List Bool} {K index : Nat} {u : Std.U16}
    (hnew : Solver.isMarked seen u = false) (hlvl : Solver.levelOf s u = K)
    (hmem : u ∈ s.trail.val) (hidx : s.trail.val.idxOf u < index)
    (hbound : u.val < seen.length) :
    (Solver.pendingVars s (seen.set u.val true) K index).length
      = (Solver.pendingVars s seen K index).length + 1 := by
  refine List.length_filter_flip _ _ _ u (Solver.take_nodup hwf index)
    (Solver.mem_take_of_idxOf hmem hidx) ?_ ?_ ?_
  · intro w _ hwu
    have hne : u.val ≠ w.val := fun h => hwu (Solver.uscalar_eq_of_val h.symm)
    simp only [Solver.isMarked, List.getElem?_set_ne hne]
  · simp [Solver.isMarked, List.getElem?_set_self (by simpa using hbound), hlvl]
  · simp [hnew]

/-- **Marking a variable below the conflict level leaves the count alone.** -/
theorem Solver.pendingVars_mark_other {s : sat_cdcl.Solver} {seen : List Bool}
    {K index : Nat} {u : Std.U16} (hlvl : Solver.levelOf s u ≠ K) :
    Solver.pendingVars s (seen.set u.val true) K index
      = Solver.pendingVars s seen K index := by
  refine List.filter_flip_of_reject _ _ _ u ?_ ?_ ?_
  · intro w _ hwu
    have hne : u.val ≠ w.val := fun h => hwu (Solver.uscalar_eq_of_val h.symm)
    simp only [Solver.isMarked, List.getElem?_set_ne hne]
  · simp [hlvl]
  · simp [hlvl]

/-- Marks are only ever added. -/
theorem Solver.isMarked_set {seen : List Bool} {u w : Std.U16}
    (h : Solver.isMarked seen w = true) :
    Solver.isMarked (seen.set u.val true) w = true := by
  simp only [Solver.isMarked] at h ⊢
  have hlt : w.val < seen.length := by
    by_contra hc
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at h
    simp at h
  by_cases hwu : w.val = u.val
  · rw [hwu, List.getElem?_set_self (by simpa [← hwu] using hlt)]
    rfl
  · rw [List.getElem?_set_ne (Ne.symm hwu)]
    exact h

/-- A mark is a `true` in the slot array. -/
theorem Solver.isMarked_iff {seen : List Bool} {u : Std.U16} :
    Solver.isMarked seen u = true ↔ seen[u.val]? = some true := by
  simp only [Solver.isMarked]
  rcases h : seen[u.val]? with _ | b
  · simp
  · cases b <;> simp

/-- A false literal's variable is assigned, so it has a slot. -/
theorem Solver.lt_length_of_litFalse {s : sat_cdcl.Solver} {lit : cnf.Literal}
    (h : Solver.litFalse s lit) : lit.var.val < s.value.val.length := by
  by_contra hc
  simp only [Solver.litFalse, Solver.valueOf,
    List.getElem?_eq_none (Nat.le_of_not_lt hc)] at h
  simp at h

/-- A false literal's variable is on the trail. -/
theorem Solver.mem_trail_of_litFalse {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    {lit : cnf.Literal} (h : Solver.litFalse s lit) : lit.var ∈ s.trail.val := by
  rw [← hwf.trail_iff, h]; rfl

/-- A false literal *is* the false literal of its variable. -/
theorem Solver.falseLit_eq {s : sat_cdcl.Solver} {lit : cnf.Literal}
    (h : Solver.litFalse s lit) : Solver.falseLit s lit.var = lit := by
  have hval : Solver.valueOf s lit.var = some lit.negated := h
  simp only [Solver.falseLit, hval, Option.getD_some]

/-- Reading a level out of the slot array. -/
theorem Solver.levelOf_of_getElem {s : sat_cdcl.Solver} {u : Std.U16} {k : Std.Usize}
    (h : s.level.val[u.val]? = some k) : Solver.levelOf s u = k.val := by
  rw [Solver.levelOf, h]; rfl

/-- And back: a level above 0 really is in the array. -/
theorem Solver.getElem_of_levelOf {s : sat_cdcl.Solver} {u : Std.U16} {k : Std.Usize}
    (h : Solver.levelOf s u = k.val) (hk : 0 < k.val) :
    s.level.val[u.val]? = some k := by
  rcases hl : s.level.val[u.val]? with _ | x
  · rw [Solver.levelOf, hl] at h; simp only [Option.elim_none] at h; omega
  · rw [Solver.levelOf, hl] at h
    simp only [Option.elim_some] at h
    exact congrArg some (Solver.uscalar_eq_of_val h)

/-- In a duplicate-free list, a position *is* the index of what sits there. -/
theorem Solver.idxOf_eq_of_getElem? {l : List Std.U16} {j : Nat} {u : Std.U16}
    (hnd : l.Nodup) (h : l[j]? = some u) : l.idxOf u = j := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp h
  rw [← hget, List.Nodup.idxOf_getElem hnd j hj]

/-- So a variable in the prefix before the cursor sits before the cursor. -/
theorem Solver.idxOf_lt_of_mem_take {l : List Std.U16} {n : Nat} {u : Std.U16}
    (hnd : l.Nodup) (h : u ∈ l.take n) : l.idxOf u < n := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem h
  rw [List.getElem?_take] at hj
  split at hj
  · rw [Solver.idxOf_eq_of_getElem? hnd hj]; assumption
  · simp at hj

/-- The false literal of an assigned variable really is false. -/
theorem Solver.litFalse_falseLit {s : sat_cdcl.Solver} (hwf : Solver.WF s) {u : Std.U16}
    (h : u ∈ s.trail.val) : Solver.litFalse s (Solver.falseLit s u) := by
  have hsome := (hwf.trail_iff u).mpr h
  rcases hv : Solver.valueOf s u with _ | b
  · rw [hv] at hsome; simp at hsome
  · simp [Solver.litFalse, Solver.falseLit, hv]

/-! ### The resolvent, as a set of literals

`Solver.resolvent` is a list, but only its literals matter: `Entails.weaken` is what
moves between the arrangements the Rust and the proof build. -/

theorem Solver.mem_resolvent_of_lower {s : sat_cdcl.Solver} {seen : List Bool}
    {lower : List cnf.Literal} {K index : Nat} {lit : cnf.Literal} (h : lit ∈ lower) :
    lit ∈ Solver.resolvent s seen lower K index :=
  List.mem_append_left _ h

theorem Solver.mem_resolvent_of_pending {s : sat_cdcl.Solver} {seen : List Bool}
    {lower : List cnf.Literal} {K index : Nat} {u : Std.U16}
    (hmark : Solver.isMarked seen u = true) (hlvl : Solver.levelOf s u = K)
    (hmem : u ∈ s.trail.val) (hidx : s.trail.val.idxOf u < index) :
    Solver.falseLit s u ∈ Solver.resolvent s seen lower K index := by
  refine List.mem_append_right _ (List.mem_map_of_mem ?_)
  simp only [Solver.pendingVars, List.mem_filter, hmark, hlvl, beq_self_eq_true,
    Bool.and_self]
  exact ⟨Solver.mem_take_of_idxOf hmem hidx, trivial⟩

theorem Solver.mem_resolvent_mono {s : sat_cdcl.Solver} {seen seen' : List Bool}
    {lower lower' : List cnf.Literal} {K index : Nat}
    (hseen : ∀ w, Solver.isMarked seen w = true → Solver.isMarked seen' w = true)
    (hlower : ∀ lit ∈ lower, lit ∈ lower') :
    ∀ lit ∈ Solver.resolvent s seen lower K index,
      lit ∈ Solver.resolvent s seen' lower' K index := by
  intro lit hlit
  rcases List.mem_append.mp hlit with h | h
  · exact List.mem_append_left _ (hlower lit h)
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
    simp only [Solver.pendingVars, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hu
    exact List.mem_append_right _ (List.mem_map_of_mem (by
      simp only [Solver.pendingVars, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
      exact ⟨hu.1, hseen u hu.2.1, hu.2.2⟩))

/-- Weakening the filter can only lengthen the result. -/
theorem List.length_filter_mono {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have ih' := ih fun x hx => h x (by simp [hx])
    rcases hp : p a with _ | _
    · rcases hq : q a with _ | _ <;> simp [hp, hq] <;> omega
    · have hq : q a = true := h a (by simp) hp
      simp [hp, hq]; omega

/-- More marks, more pending variables. -/
theorem Solver.length_pendingVars_mono {s : sat_cdcl.Solver} {seen seen' : List Bool}
    {K index : Nat}
    (h : ∀ w, Solver.isMarked seen w = true → Solver.isMarked seen' w = true) :
    (Solver.pendingVars s seen K index).length
      ≤ (Solver.pendingVars s seen' K index).length := by
  refine List.length_filter_mono _ _ _ fun u _ hu => ?_
  simp only [Bool.and_eq_true] at hu ⊢
  exact ⟨h u hu.1, hu.2⟩

/-- Extending the cursor by one adds at most the variable at that position. -/
theorem Solver.pendingVars_succ {s : sat_cdcl.Solver} {seen : List Bool} {K n : Nat} :
    Solver.pendingVars s seen K (n + 1)
      = Solver.pendingVars s seen K n
        ++ (s.trail.val[n]?.toList).filter
            (fun u => Solver.isMarked seen u && Solver.levelOf s u == K) := by
  simp only [Solver.pendingVars, List.take_add_one, List.filter_append]

/-- Moving the cursor over positions that hold nothing pending changes nothing. -/
theorem Solver.pendingVars_stable {s : sat_cdcl.Solver} {seen : List Bool} {K : Nat}
    (a : Nat) : ∀ b, a ≤ b →
      (∀ k u, a ≤ k → k < b → s.trail.val[k]? = some u →
        ¬(Solver.isMarked seen u = true ∧ Solver.levelOf s u = K)) →
      Solver.pendingVars s seen K b = Solver.pendingVars s seen K a := by
  intro b
  induction b with
  | zero => intro hab _; rw [Nat.le_zero.mp hab]
  | succ n ih =>
    intro hab hgap
    rcases Nat.lt_or_ge n a with h | h
    · rw [show a = n + 1 by omega]
    · rw [Solver.pendingVars_succ, ih h fun k u hk1 hk2 => hgap k u hk1 (by omega)]
      rcases hv : s.trail.val[n]? with _ | u
      · simp
      · have hno := hgap n u h (by omega) hv
        have : (Solver.isMarked seen u && Solver.levelOf s u == K) = false := by
          by_cases h1 : Solver.isMarked seen u = true <;>
            by_cases h2 : Solver.levelOf s u = K <;> simp_all
        simp [this]

/-- **What the trail walk does to the count.** It returns the latest pending variable
    behind the cursor, so the count over the old cursor is the count over the new one
    plus that variable -- which is why one iteration of the resolution loop decrements
    `pending` by exactly one. -/
theorem Solver.pendingVars_split {s : sat_cdcl.Solver} {seen : List Bool}
    {K index index1 : Nat} {v : Std.U16} (hlt : index1 < index)
    (hv : s.trail.val[index1]? = some v)
    (hmark : Solver.isMarked seen v = true) (hlvl : Solver.levelOf s v = K)
    (hgap : ∀ k u, index1 < k → k < index → s.trail.val[k]? = some u →
      ¬(Solver.isMarked seen u = true ∧ Solver.levelOf s u = K)) :
    Solver.pendingVars s seen K index = Solver.pendingVars s seen K index1 ++ [v] := by
  rw [Solver.pendingVars_stable (index1 + 1) index (by omega)
      fun k u hk1 hk2 hget => hgap k u (by omega) hk2 hget,
    Solver.pendingVars_succ, hv]
  simp [hmark, hlvl]

/-- **What the marks mean.** The bookkeeping half of the resolution loop's invariant:
    everything about `seen`, `marked`, `lower` and `pending` that does not mention the
    clause under resolution. This is exactly what the clause scan preserves, which is
    why it is a structure of its own. -/
structure Solver.Marking (s : sat_cdcl.Solver) (seen : List Bool)
    (lower : List cnf.Literal) (marked : List Std.U16) (pending : Int) (index : Nat) :
    Prop where
  /-- `pending` counts the conflict-level variables left to resolve on. -/
  pending_eq : pending = (Solver.pendingVars s seen (Solver.decisionLevel s) index).length
  /-- The scratch array is `s.seen` with exactly the marked variables flipped. -/
  seen_length : seen.length = s.seen.val.length
  seen_of_marked : ∀ u ∈ marked, seen[u.val]? = some true
  marked_of_seen : ∀ i, seen[i]? = some true → ∃ u ∈ marked, u.val = i
  /-- Marked variables are assigned, above level 0, and marked once. -/
  marked_trail : ∀ u ∈ marked, u ∈ s.trail.val
  marked_level : ∀ u ∈ marked, 0 < Solver.levelOf s u
  marked_nodup : marked.Nodup
  /-- What is collected for the learned clause is false and strictly between level 0 and
      the conflict level, and it is exactly the marked variables below that level: the
      two halves of `resolvent` do not overlap, and together they are the whole clause. -/
  lower_false : ∀ lit ∈ lower, Solver.litFalse s lit
  lower_level : ∀ lit ∈ lower, 0 < Solver.levelOf s lit.var ∧
    Solver.levelOf s lit.var < Solver.decisionLevel s
  lower_marked : ∀ lit ∈ lower, lit.var ∈ marked
  lower_nodup : (lower.map (·.var)).Nodup
  lower_of_marked : ∀ u ∈ marked, Solver.levelOf s u < Solver.decisionLevel s →
    Solver.falseLit s u ∈ lower
  /-- The cursor is inside the trail. -/
  index_le : index ≤ s.trail.val.length

/-- **The invariant of `analyze`'s resolution loop**, at the top of an iteration: `cl`
    is the clause about to be scanned, `resolved` the variable the last step resolved
    on, and `index` the trail cursor.

    `entails` is the one field that is about logic rather than bookkeeping, and it is
    stated over the resolvent *plus what the scan of `cl` is about to carry into it* --
    which is what makes one iteration exactly one application of `Entails.resolution`.
    `clause_behind` is where the implication graph's acyclicity is spent: every literal
    of `cl` sits behind the cursor, so the scan cannot reintroduce a variable the walk
    has already resolved away and dropped from the resolvent. -/
structure Solver.Analyzing (s : sat_cdcl.Solver) (seen : List Bool)
    (lower : List cnf.Literal) (marked : List Std.U16) (pending : Int) (index : Nat)
    (cl : List cnf.Literal) (resolved : Option Std.U16) : Prop
    extends Solver.Marking s seen lower marked pending index where
  /-- **Resolution soundness**, the invariant the learned clause inherits. -/
  entails : Entails (Solver.db s)
    (Solver.resolvent s seen lower (Solver.decisionLevel s) index ++
      Solver.carried s cl resolved)
  /-- There is something left to do: either a marked conflict-level variable behind the
      cursor, or -- on the first iteration, where nothing is marked yet -- a
      conflict-level literal in the clause for the scan to mark. -/
  pending_pos : 0 < pending ∨ ∃ lit ∈ cl, Solver.levelOf s lit.var = Solver.decisionLevel s
    ∧ resolved ≠ some lit.var
  /-- The clause under resolution is one of the database's, and every literal of it but
      the one just resolved on is false and sits behind the cursor. -/
  clause_mem : cl ∈ Solver.db s
  clause_bound : ∀ lit ∈ cl, lit.var.val < s.value.val.length
  clause_false : ∀ lit ∈ cl, resolved ≠ some lit.var → Solver.litFalse s lit
  clause_behind : ∀ lit ∈ cl, resolved ≠ some lit.var →
    s.trail.val.idxOf lit.var < index

/-- **The clause scan preserves the marking invariant, and folds the clause into the
    resolvent.** This is the semantic half of the scan: `analyze_loop0_loop0.spec` says
    the Rust computes `Solver.scan`, and this says what `Solver.scan` means.

    The last conjunct is the one the resolution step needs: every literal of the clause
    that the scan did not skip ends up *in* the resolvent -- as itself if it sits below
    the conflict level, and as the false literal of a pending variable if it sits at
    it. So the clause is absorbed, and the next resolution step has only the reason
    clause left to carry. -/
theorem Solver.scan_marking (s : sat_cdcl.Solver) (hwf : Solver.WF s)
    (resolved : Option Std.U16) (index : Nat) :
    ∀ (xs : List cnf.Literal) (seen : List Bool) (lower : List cnf.Literal)
      (pending : Int) (marked : List Std.U16) (seen' : List Bool)
      (lower' : List cnf.Literal) (pending' : Int) (marked' : List Std.U16),
      (∀ lit ∈ xs, resolved ≠ some lit.var → Solver.litFalse s lit) →
      (∀ lit ∈ xs, resolved ≠ some lit.var → s.trail.val.idxOf lit.var < index) →
      Solver.Marking s seen lower marked pending index →
      Solver.scan (Solver.levelOf s) resolved (Solver.decisionLevel s) xs
          (seen, lower, pending, marked) = (seen', lower', pending', marked') →
      Solver.Marking s seen' lower' marked' pending' index
      ∧ (∀ w, Solver.isMarked seen w = true → Solver.isMarked seen' w = true)
      ∧ (∀ lit ∈ lower, lit ∈ lower')
      ∧ (∀ lit ∈ xs, resolved ≠ some lit.var → Solver.levelOf s lit.var ≠ 0 →
          lit ∈ Solver.resolvent s seen' lower' (Solver.decisionLevel s) index) := by
  intro xs
  induction xs with
  | nil =>
    intro seen lower pending marked seen' lower' pending' marked' _ _ hm heq
    simp only [Solver.scan, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    exact ⟨hm, fun _ h => h, fun _ h => h, by simp⟩
  | cons lit rest ih =>
    intro seen lower pending marked seen' lower' pending' marked' hfalse hbehind hm heq
    rw [Solver.scan] at heq
    -- Facts about the literal this step is looking at, when it is not the one the last
    -- resolution step consumed.
    have hlit : lit ∈ lit :: rest := List.mem_cons_self ..
    split at heq
    · -- Skipped: it is the resolved variable, already marked, or at level 0.
      rename_i hskip
      obtain ⟨hm', hmono, hlow, hres⟩ :=
        ih seen lower pending marked seen' lower' pending' marked'
          (fun l hl => hfalse l (List.mem_cons_of_mem _ hl))
          (fun l hl => hbehind l (List.mem_cons_of_mem _ hl)) hm heq
      refine ⟨hm', hmono, hlow, ?_⟩
      intro l hl hnr hnz
      rcases List.mem_cons.mp hl with rfl | hl'
      · -- It was skipped because it is already marked, and a marked variable is
        -- already in the resolvent.
        have hmark : Solver.isMarked seen l.var = true := by
          rcases hskip with h | h | h
          · exact absurd h hnr
          · exact h
          · exact absurd h hnz
        have hfl := hfalse l hlit hnr
        have hmemtr := Solver.mem_trail_of_litFalse hwf hfl
        by_cases hK : Solver.levelOf s l.var = Solver.decisionLevel s
        · have := Solver.mem_resolvent_of_pending (lower := lower) hmark hK hmemtr
            (hbehind l hlit hnr)
          rw [Solver.falseLit_eq hfl] at this
          exact Solver.mem_resolvent_mono hmono hlow _ this
        · obtain ⟨u, hu, huv⟩ := hm.marked_of_seen l.var.val (Solver.isMarked_iff.mp hmark)
          have hlt : Solver.levelOf s l.var < Solver.decisionLevel s :=
            lt_of_le_of_ne (hwf.level_le _ hmemtr) hK
          have := hm.lower_of_marked u hu (by rw [Solver.uscalar_eq_of_val huv]; exact hlt)
          rw [Solver.uscalar_eq_of_val huv, Solver.falseLit_eq hfl] at this
          exact Solver.mem_resolvent_of_lower (hlow l this)
      · exact hres l hl' hnr hnz
    · -- Marked here for the first time.
      rename_i hnew
      push Not at hnew
      obtain ⟨hnr, hnmark, hnz⟩ := hnew
      have hfl : Solver.litFalse s lit := hfalse lit hlit hnr
      have hmemtr : lit.var ∈ s.trail.val := Solver.mem_trail_of_litFalse hwf hfl
      have hidx : s.trail.val.idxOf lit.var < index := hbehind lit hlit hnr
      have hslot : lit.var.val < seen.length := by
        rw [hm.seen_length, hwf.seen_length]; exact Solver.lt_length_of_litFalse hfl
      have hnmark' : Solver.isMarked seen lit.var = false := by
        simpa using hnmark
      have hnotmarked : lit.var ∉ marked := fun hc =>
        by simp [Solver.isMarked_iff.mpr (hm.seen_of_marked _ hc)] at hnmark'
      -- The common half of the two branches: the bookkeeping fields that do not
      -- depend on which side of the conflict level the literal is on.
      have hsl : (seen.set lit.var.val true).length = s.seen.val.length := by
        rw [List.length_set]; exact hm.seen_length
      have hsom : ∀ u ∈ marked ++ [lit.var],
          (seen.set lit.var.val true)[u.val]? = some true := by
        intro u hu
        rcases List.mem_append.mp hu with hu' | hu'
        · exact Solver.isMarked_iff.mp
            (Solver.isMarked_set (Solver.isMarked_iff.mpr (hm.seen_of_marked u hu')))
        · simp only [List.mem_singleton] at hu'
          subst hu'
          exact List.getElem?_set_self (by simpa using hslot)
      have hmos : ∀ i, (seen.set lit.var.val true)[i]? = some true →
          ∃ u ∈ marked ++ [lit.var], u.val = i := by
        intro i hi
        by_cases hiv : i = lit.var.val
        · exact ⟨lit.var, by simp, hiv.symm⟩
        · rw [List.getElem?_set_ne (Ne.symm hiv)] at hi
          obtain ⟨u, hu, huv⟩ := hm.marked_of_seen i hi
          exact ⟨u, List.mem_append_left _ hu, huv⟩
      have hmt : ∀ u ∈ marked ++ [lit.var], u ∈ s.trail.val := by
        intro u hu
        rcases List.mem_append.mp hu with hu' | hu'
        · exact hm.marked_trail u hu'
        · simp only [List.mem_singleton] at hu'; subst hu'; exact hmemtr
      have hml : ∀ u ∈ marked ++ [lit.var], 0 < Solver.levelOf s u := by
        intro u hu
        rcases List.mem_append.mp hu with hu' | hu'
        · exact hm.marked_level u hu'
        · simp only [List.mem_singleton] at hu'; subst hu'; omega
      have hmn : (marked ++ [lit.var]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hm.marked_nodup, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb
        exact fun hc => hnotmarked (hc ▸ ha)
      have hmono1 : ∀ w, Solver.isMarked seen w = true →
          Solver.isMarked (seen.set lit.var.val true) w = true :=
        fun _ h => Solver.isMarked_set h
      split at heq
      · -- At the conflict level: counted into `pending`, not collected.
        rename_i hK
        have hm1 : Solver.Marking s (seen.set lit.var.val true) lower
            (marked ++ [lit.var]) (pending + 1) index := by
          refine
            { pending_eq := ?_
              seen_length := hsl
              seen_of_marked := hsom
              marked_of_seen := hmos
              marked_trail := hmt
              marked_level := hml
              marked_nodup := hmn
              lower_false := hm.lower_false
              lower_level := hm.lower_level
              lower_marked := ?_
              lower_nodup := hm.lower_nodup
              lower_of_marked := ?_
              index_le := hm.index_le }
          · have hpe := hm.pending_eq
            rw [Solver.length_pendingVars_mark hwf hnmark' hK hmemtr hidx hslot]
            omega
          · exact fun l hl => List.mem_append_left _ (hm.lower_marked l hl)
          · intro u hu hlt
            rcases List.mem_append.mp hu with hu' | hu'
            · exact hm.lower_of_marked u hu' hlt
            · simp only [List.mem_singleton] at hu'; subst hu'; omega
        obtain ⟨hm', hmono, hlow, hres⟩ :=
          ih _ _ _ _ seen' lower' pending' marked'
            (fun l hl => hfalse l (List.mem_cons_of_mem _ hl))
            (fun l hl => hbehind l (List.mem_cons_of_mem _ hl)) hm1 heq
        refine ⟨hm', fun w hw => hmono w (hmono1 w hw), hlow, ?_⟩
        intro l hl hnr' hnz'
        rcases List.mem_cons.mp hl with rfl | hl'
        · have := Solver.mem_resolvent_of_pending (lower := lower)
            (Solver.isMarked_iff.mpr (hsom l.var (by simp))) hK hmemtr hidx
          rw [Solver.falseLit_eq hfl] at this
          exact Solver.mem_resolvent_mono hmono hlow _ this
        · exact hres l hl' hnr' hnz'
      · -- Below the conflict level: collected into the learned clause.
        rename_i hK
        have hlt : Solver.levelOf s lit.var < Solver.decisionLevel s :=
          lt_of_le_of_ne (hwf.level_le _ hmemtr) hK
        have hm1 : Solver.Marking s (seen.set lit.var.val true) (lower ++ [lit])
            (marked ++ [lit.var]) pending index := by
          refine
            { pending_eq := ?_
              seen_length := hsl
              seen_of_marked := hsom
              marked_of_seen := hmos
              marked_trail := hmt
              marked_level := hml
              marked_nodup := hmn
              lower_false := ?_
              lower_level := ?_
              lower_marked := ?_
              lower_nodup := ?_
              lower_of_marked := ?_
              index_le := hm.index_le }
          · rw [Solver.pendingVars_mark_other hK]; exact hm.pending_eq
          · intro l hl
            rcases List.mem_append.mp hl with hl' | hl'
            · exact hm.lower_false l hl'
            · simp only [List.mem_singleton] at hl'; subst hl'; exact hfl
          · intro l hl
            rcases List.mem_append.mp hl with hl' | hl'
            · exact hm.lower_level l hl'
            · simp only [List.mem_singleton] at hl'; subst hl'; omega
          · intro l hl
            rcases List.mem_append.mp hl with hl' | hl'
            · exact List.mem_append_left _ (hm.lower_marked l hl')
            · simp only [List.mem_singleton] at hl'; subst hl'; simp
          · rw [List.map_append, List.nodup_append]
            refine ⟨hm.lower_nodup, by simp, ?_⟩
            intro a ha b hb
            simp only [List.map_cons, List.map_nil, List.mem_cons,
              List.not_mem_nil, or_false] at hb
            subst hb
            obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
            exact fun hc => hnotmarked (hc ▸ hm.lower_marked l hl)
          · intro u hu hlt'
            rcases List.mem_append.mp hu with hu' | hu'
            · exact List.mem_append_left _ (hm.lower_of_marked u hu' hlt')
            · simp only [List.mem_singleton] at hu'
              subst hu'
              simp [Solver.falseLit_eq hfl]
        obtain ⟨hm', hmono, hlow, hres⟩ :=
          ih _ _ _ _ seen' lower' pending' marked'
            (fun l hl => hfalse l (List.mem_cons_of_mem _ hl))
            (fun l hl => hbehind l (List.mem_cons_of_mem _ hl)) hm1 heq
        refine ⟨hm', fun w hw => hmono w (hmono1 w hw),
          fun l hl => hlow l (List.mem_append_left _ hl), ?_⟩
        intro l hl hnr' hnz'
        rcases List.mem_cons.mp hl with rfl | hl'
        · exact Solver.mem_resolvent_of_lower (hlow l (by simp))
        · exact hres l hl' hnr' hnz'

/-- `Solver.scan_marking` in the shape the resolution loop meets it: the scan runs over
    the whole clause, from the invariant the loop is holding. -/
theorem Solver.scan_of_Analyzing (s : sat_cdcl.Solver) (hwf : Solver.WF s)
    {seen : List Bool} {lower : List cnf.Literal} {marked : List Std.U16}
    {pending : Int} {index : Nat} {cl : List cnf.Literal} {resolved : Option Std.U16}
    {conflict_level : Std.Usize} (hcl : conflict_level.val = Solver.decisionLevel s)
    (hinv : Solver.Analyzing s seen lower marked pending index cl resolved)
    {seen' : List Bool} {lower' : List cnf.Literal} {pending' : Int}
    {marked' : List Std.U16}
    (heq : (seen', lower', pending', marked') =
      Solver.scan (Solver.levelOf s) resolved conflict_level.val (List.drop 0 cl)
        (seen, lower, pending, marked)) :
    Solver.Marking s seen' lower' marked' pending' index
    ∧ (∀ w, Solver.isMarked seen w = true → Solver.isMarked seen' w = true)
    ∧ (∀ lit ∈ lower, lit ∈ lower')
    ∧ (∀ lit ∈ cl, resolved ≠ some lit.var → Solver.levelOf s lit.var ≠ 0 →
        lit ∈ Solver.resolvent s seen' lower' (Solver.decisionLevel s) index) := by
  refine Solver.scan_marking s hwf resolved index cl seen lower pending marked
    seen' lower' pending' marked' (fun l hl hnr => hinv.clause_false l hl hnr)
    (fun l hl hnr => hinv.clause_behind l hl hnr) hinv.toMarking ?_
  rw [← hcl]
  simpa using heq.symm

/-- **Everything in the resolvent is false and above level 0** -- which is what makes
    the resolvent a clause the conflict actually refutes, and what lets the next
    resolution step drop the level-0 literals of the reason without touching it. -/
theorem Solver.mem_resolvent_false {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    {seen : List Bool} {lower : List cnf.Literal} {marked : List Std.U16}
    {pending : Int} {index : Nat}
    (hm : Solver.Marking s seen lower marked pending index)
    (hpos : 0 < Solver.decisionLevel s) :
    ∀ lit ∈ Solver.resolvent s seen lower (Solver.decisionLevel s) index,
      Solver.litFalse s lit ∧ 0 < Solver.levelOf s lit.var := by
  intro lit hlit
  rcases List.mem_append.mp hlit with h | h
  · exact ⟨hm.lower_false lit h, (hm.lower_level lit h).1⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
    simp only [Solver.pendingVars, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hu
    refine ⟨Solver.litFalse_falseLit hwf (List.mem_of_mem_take hu.1), ?_⟩
    simp only [Solver.falseLit, hu.2.2]
    exact hpos

/-- **How big the bookkeeping can get.** Marked variables are distinct trail entries,
    the collected literals sit on distinct marked variables, and `pending` counts a
    sublist of the trail -- so all three are bounded by the trail's length, which
    `trail_length_le` puts at `2 ^ 16`. This is what keeps `pending`'s `i32` and the
    two `Vec`s inside their types for a whole pass over a clause. -/
theorem Solver.Marking.bounds {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    {seen : List Bool} {lower : List cnf.Literal} {marked : List Std.U16}
    {pending : Int} {index : Nat}
    (hm : Solver.Marking s seen lower marked pending index) :
    marked.length ≤ 2 ^ 16 ∧ lower.length ≤ 2 ^ 16 ∧ 0 ≤ pending ∧ pending ≤ 2 ^ 16 := by
  have htrail := Solver.trail_length_le hwf
  have hmarked : marked.length ≤ s.trail.val.length :=
    (List.Nodup.subperm hm.marked_nodup fun u hu => hm.marked_trail u hu).length_le
  have hlower : lower.length ≤ marked.length := by
    have hsp : (lower.map (·.var)).Subperm marked :=
      List.Nodup.subperm hm.lower_nodup (by
        intro a ha
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
        exact hm.lower_marked l hl)
    simpa using hsp.length_le
  have hp := hm.pending_eq
  have hpl : (Solver.pendingVars s seen (Solver.decisionLevel s) index).length
      ≤ s.trail.val.length :=
    le_trans (List.length_filter_le _ _) (by simp)
  omega

/-- **`Option::expect`** is the extraction of a Rust `panic!`: the proof has to supply
    the value it is being told is there. Not a `step` spec -- `step` would have to guess
    that value -- so the two uses in `analyze` rewrite with it by hand. -/
theorem Option.expect_some {T : Type} (val : T) (msg : Std.Str) :
    core.option.Option.expect (some val) msg = ok val := by
  simp [core.option.Option.expect]

/-- **Spec for `bump`**: a VSIDS bump reaches `activity` and nothing else, and leaves
    its length alone so the next bump is still in bounds. That the learned clause does
    not depend on `activity` at all is why `analyze`'s frame condition can exempt it and
    then say nothing further about it. -/
@[step]
theorem sat_cdcl.Solver.bump.spec (s : sat_cdcl.Solver) (var : Std.U16)
    (hvar : var.val < s.activity.val.length) :
    sat_cdcl.Solver.bump s var ⦃ (s' : sat_cdcl.Solver) =>
      s' = { s with activity := s'.activity }
      ∧ s'.activity.val.length = s.activity.val.length ⦄ := by
  unfold sat_cdcl.Solver.bump
  step*
  -- `saturating_add` is a pure function the extraction binds monadically, which `step`
  -- does not see through on its own.
  simp only [core.num.U32.saturating_add, rust_primitives.arithmetic.saturating_add_u32]
  step*

/-- **`Iterator::next` on a `usize` range**, in the form Aeneas's `step` consumes.
    `CoreModels` gives the iterator an `mvcgen`-style spec, which `step` does not see;
    the clause scan is the one loop in this file driven by a range rather than by an
    `into_iter`, so it needs this. -/
@[step]
theorem IteratorRange.next_usize.spec (r : core.ops.range.Range Std.Usize) :
    core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep r ⦃
      (o : Option Std.Usize) (rg : core.ops.range.Range Std.Usize) =>
        rg.«end» = r.«end»
        ∧ (∀ x, o = some x → x = r.start ∧ r.start.val < r.«end».val
            ∧ rg.start.val = r.start.val + 1)
        ∧ (o = none → r.«end».val ≤ r.start.val ∧ rg.start = r.start) ⦄ := by
  obtain ⟨i, e⟩ := r
  unfold core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep
  by_cases h : i.val < e.val
  · simp_all [compare, compareOfLessAndEq,
      core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd,
      core.Usize.Insts.CoreCloneClone.clone,
      core.Usize.Insts.CoreIterRangeStep.forward_checked,
      core.convert.TryFromUTInfallible.Blanket.try_from,
      core.convert.From.Blanket.from,
      core.num.Usize.checked_add, core.num.Usize.overflowing_add,
      rust_primitives.arithmetic.overflowing_add_usize]
    -- The step cannot overflow: `i < e ≤ usize::MAX`.
    have hov := UScalar.overflowing_add_eq i 1#usize
    rcases hprod : UScalar.overflowing_add i 1#usize with ⟨r, b⟩
    rw [hprod] at hov
    simp only [gt_iff_lt] at hov ⊢
    rw [if_neg (by scalar_tac)] at hov
    simp [hov.1, hov.2]
  · have hlt : (i.val < e.val) = False := by simp; omega
    by_cases h' : i.val = e.val <;>
      simp [compare, compareOfLessAndEq, hlt, h',
        core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd]
    omega

/-- **`Option<u16>`'s `PartialEq`**, likewise: the scan compares the literal's variable
    against the one the last resolution step consumed. -/
@[step]
theorem Option.eq_u16.spec (x y : core.option.Option Std.U16) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
      core.U16.Insts.CoreCmpPartialEqU16 x y ⦃ (b : Bool) => b = true ↔ x = y ⦄ := by
  rcases x with _ | a <;> rcases y with _ | b <;>
    simp [core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.U16.Insts.CoreCmpPartialEqU16]

/-- **Spec for `analyze`'s clause scan.** It marks the literals of the clause under
    resolution that are new, which `Solver.scan` models exactly; nothing else about the
    solver changes but `activity`, whose VSIDS bumps the learned clause does not depend
    on. Stating this against a model rather than against the invariant directly keeps
    the mechanical half (one `step*` induction over the range) apart from the semantic
    half (what the marks mean), the way `maxLevel` and the `List.set` lemmas do for the
    two bookkeeping loops. -/
@[step]
theorem sat_cdcl.Solver.analyze_loop0_loop0.spec (s : sat_cdcl.Solver)
    (iter : core.ops.range.Range Std.Usize) (activity : alloc.vec.Vec Std.U32)
    (seen : alloc.vec.Vec Bool) (conflict_level : Std.Usize)
    (lower : alloc.vec.Vec cnf.Literal) (pending : Std.I32)
    (marked : alloc.vec.Vec Std.U16) (clause : Std.Usize)
    (resolved : core.option.Option Std.U16) (cl : List cnf.Literal)
    (hclause : Solver.clauseAt s clause = some cl)
    (hstart : iter.start.val ≤ cl.length)
    (hend : iter.«end».val = cl.length)
    (hseen : seen.val.length = s.value.val.length)
    (hlevel : s.level.val.length = s.value.val.length)
    (hact : activity.val.length = s.value.val.length)
    (hvars : ∀ lit ∈ cl, lit.var.val < s.value.val.length)
    (hfits : marked.val.length + (cl.length - iter.start.val) ≤ Std.Usize.max ∧
      lower.val.length + (cl.length - iter.start.val) ≤ Std.Usize.max ∧
      pending.val + (cl.length - iter.start.val) ≤ Std.I32.max) :
    sat_cdcl.Solver.analyze_loop0_loop0 iter s.clauses s.problem_clauses s.value s.level
      s.reason s.phase activity s.occurs seen s.trail s.trail_lim s.conflicts
      conflict_level lower pending marked clause resolved ⦃
      (clauses' : alloc.vec.Vec cnf.Clause) (problem_clauses' : Std.Usize)
      (value' : alloc.vec.Vec (core.option.Option Bool))
      (level' : alloc.vec.Vec Std.Usize)
      (reason' : alloc.vec.Vec (core.option.Option Std.Usize))
      (phase' : alloc.vec.Vec Bool) (_activity' : alloc.vec.Vec Std.U32)
      (occurs' : alloc.vec.Vec Bool) (seen' : alloc.vec.Vec Bool)
      (trail' : alloc.vec.Vec Std.U16) (trail_lim' : alloc.vec.Vec Std.Usize)
      (conflicts' : Std.U32) (lower' : alloc.vec.Vec cnf.Literal) (pending' : Std.I32)
      (marked' : alloc.vec.Vec Std.U16) =>
        (seen'.val, lower'.val, pending'.val, marked'.val) =
          Solver.scan (Solver.levelOf s) resolved conflict_level.val (cl.drop iter.start.val)
            (seen.val, lower.val, pending.val, marked.val)
        ∧ clauses' = s.clauses ∧ problem_clauses' = s.problem_clauses
        ∧ value' = s.value ∧ level' = s.level ∧ reason' = s.reason ∧ phase' = s.phase
        ∧ occurs' = s.occurs ∧ trail' = s.trail ∧ trail_lim' = s.trail_lim
        ∧ conflicts' = s.conflicts
        ∧ _activity'.val.length = activity.val.length ⦄ := by
  unfold sat_cdcl.Solver.analyze_loop0_loop0
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next]
  obtain ⟨c0, hcget, hcval⟩ := Solver.clauseAt_eq hclause
  have hclen : clause.val < s.clauses.val.length := by
    grind [List.getElem?_eq_some_iff]
  -- `step*` runs the body out and applies this theorem's own statement to each of the
  -- four recursive branches; what it leaves behind is bookkeeping.
  step*
  -- The clause the recursive calls scan is this one.
  all_goals try exact cl
  -- Every branch that consumed a literal consumed `cl[st]`: it is in the clause, hence
  -- in range of every slot array, and it heads what is left to scan.
  all_goals try
    (obtain ⟨hjst, hlt, hnext⟩ := o_post2 j (by assumption)
     have hst : iter.start.val < cl.length := by omega
     have hcc : c = c0 := by rw [hcget] at c_post; exact (Option.some.inj c_post).symm
     have hgetv : cl[iter.start.val]'hst = lit := by
       have h2 : cl[iter.start.val]? = some lit := by
         rw [lit_post, ← hcval, ← hcc, ← hjst]; exact l_post
       rw [List.getElem?_eq_getElem hst] at h2
       exact Option.some.inj h2
     have hmem : lit ∈ cl := hgetv ▸ List.getElem_mem hst
     have hvar : lit.var.val < s.value.val.length := hvars lit hmem
     have hv10 : v10.val = lit.var.val := by simp [v10_post]
     have hdrop : cl.drop iter.start.val = lit :: cl.drop iter1.start.val := by
       rw [hnext, List.drop_eq_getElem_cons hst, hgetv])
  -- `bump` touches `activity` and nothing else, so the solver the recursive call gets
  -- is this one as far as anything here reads it.
  all_goals try
    (have hsclauses : self.clauses = s.clauses := by rw [self_post1]
     have hsproblem : self.problem_clauses = s.problem_clauses := by rw [self_post1]
     have hsvalue : self.value = s.value := by rw [self_post1]
     have hslevel : self.level = s.level := by rw [self_post1]
     have hsreason : self.reason = s.reason := by rw [self_post1]
     have hsphase : self.phase = s.phase := by rw [self_post1]
     have hsoccurs : self.occurs = s.occurs := by rw [self_post1]
     have hstrail : self.trail = s.trail := by rw [self_post1]
     have hstlim : self.trail_lim = s.trail_lim := by rw [self_post1]
     have hsconf : self.conflicts = s.conflicts := by rw [self_post1]
     have hsseen : self.seen = index_mut_back true := by rw [self_post1]
     have hslvl : Solver.levelOf self = Solver.levelOf s := by
       funext v; simp only [Solver.levelOf, hslevel])
  all_goals first
    -- The cursor has run off the end of the clause: nothing left to scan.
    | (have hge : cl.length ≤ iter.start.val := by
         have := (o_post3 (by assumption)).1; omega
       rw [List.drop_eq_nil_of_le hge]
       rfl)
    -- Slot indices, after `bump` and before it.
    | (simp only [hslevel]; rw [hv10]; omega)
    | (rw [hv10]; omega)
    | (simp only [hact]; exact hvar)
    -- The next iteration still fits: one more literal scanned is one fewer to come.
    | (obtain ⟨hf1, hf2, hf3⟩ := hfits
       have hm : marked1.val.length = marked.val.length + 1 := by simp [marked1_post]
       have hl : lower1.val.length = lower.val.length + 1 := by simp [lower1_post]
       exact ⟨by omega, by omega, by omega⟩)
    | (obtain ⟨hf1, hf2, hf3⟩ := hfits
       have hm : marked1.val.length = marked.val.length + 1 := by simp [marked1_post]
       exact ⟨by omega, by omega, by omega⟩)
    | (obtain ⟨hf1, hf2, hf3⟩ := hfits
       exact ⟨by omega, by omega, by omega⟩)
    -- The next iteration scans the same clause of the same database.
    | (have h : Solver.clauseAt self clause = Solver.clauseAt s clause := by
         simp only [Solver.clauseAt, Solver.db, hsclauses]
       rw [h]; exact hclause)
    | (rw [o_post1]; exact hend)
    | (rw [hsvalue]; exact hvars)
    | omega
    -- The literal was the one the last resolution step consumed.
    | (have hb : b = true := by assumption
       refine ⟨?_, clauses'_post2, clauses'_post3, clauses'_post4, clauses'_post5,
         clauses'_post6, clauses'_post7, clauses'_post8, clauses'_post9,
         clauses'_post10, clauses'_post11, clauses'_post12⟩
       rw [hdrop, Solver.scan, if_pos (Or.inl (b_post.mp hb).symm)]
       exact clauses'_post1)
    -- It was already marked.
    | (have hb1 : b1 = true := by assumption
       have hmark : Solver.isMarked seen.val lit.var = true := by
         simp only [Solver.isMarked, ← hv10, b1_post, hb1, Option.getD_some]
       refine ⟨?_, clauses'_post2, clauses'_post3, clauses'_post4, clauses'_post5,
         clauses'_post6, clauses'_post7, clauses'_post8, clauses'_post9,
         clauses'_post10, clauses'_post11, clauses'_post12⟩
       rw [hdrop, Solver.scan, if_pos (Or.inr (Or.inl hmark))]
       exact clauses'_post1)
    -- It sits at level 0, so it is a fact about the formula and gets dropped.
    | (have hi2 : i2 = 0#usize := by assumption
       have hz : Solver.levelOf s lit.var = 0 := by
         simp [Solver.levelOf, ← hv10, i2_post, hi2]
       refine ⟨?_, clauses'_post2, clauses'_post3, clauses'_post4, clauses'_post5,
         clauses'_post6, clauses'_post7, clauses'_post8, clauses'_post9,
         clauses'_post10, clauses'_post11, clauses'_post12⟩
       rw [hdrop, Solver.scan, if_pos (Or.inr (Or.inr hz))]
       exact clauses'_post1)
    -- It is new and sits at the conflict level: mark it and count it into `pending`.
    | (have hi3 : i3 = conflict_level := by assumption
       have hlvl2 : Solver.levelOf s lit.var = i2.val := by
         simp [Solver.levelOf, ← hv10, i2_post]
       have hi23 : i3 = i2 := by
         rw [hslevel, i2_post] at i3_post
         exact (Option.some.inj i3_post).symm
       have hfresh : ¬ (resolved = core.option.Option.Some lit.var ∨
           Solver.isMarked seen.val lit.var = true ∨ Solver.levelOf s lit.var = 0) := by
         simp only [not_or, Solver.isMarked, ← hv10, b1_post, hlvl2]
         refine ⟨fun hcon => ‹¬ b = true› (b_post.mpr hcon.symm),
           by simpa using ‹¬ b1 = true›,
           fun hcon =>
             ‹¬ i2 = 0#usize› ((Std.UScalar.eq_equiv i2 0#usize).mpr (by simpa using hcon))⟩
       have hconf : Solver.levelOf s lit.var = conflict_level.val := by
         rw [hlvl2, ← hi23, hi3]
       refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       case _ =>
         rw [hslvl, hsseen, __post2 true, hv10, pending1_post, marked1_post]
           at clauses'_post1
         rw [hdrop, Solver.scan, if_neg hfresh, if_pos hconf]
         exact clauses'_post1
       all_goals simp only [hsclauses, hsproblem, hsvalue, hslevel, hsreason, hsphase,
         hsoccurs, hstrail, hstlim, hsconf] at *
       all_goals first | assumption | omega)
    -- It is new and sits below the conflict level: it goes into the learned clause.
    | (have hlvl2 : Solver.levelOf s lit.var = i2.val := by
         simp [Solver.levelOf, ← hv10, i2_post]
       have hi23 : i3 = i2 := by
         rw [hslevel, i2_post] at i3_post
         exact (Option.some.inj i3_post).symm
       have hfresh : ¬ (resolved = core.option.Option.Some lit.var ∨
           Solver.isMarked seen.val lit.var = true ∨ Solver.levelOf s lit.var = 0) := by
         simp only [not_or, Solver.isMarked, ← hv10, b1_post, hlvl2]
         refine ⟨fun hcon => ‹¬ b = true› (b_post.mpr hcon.symm),
           by simpa using ‹¬ b1 = true›,
           fun hcon =>
             ‹¬ i2 = 0#usize› ((Std.UScalar.eq_equiv i2 0#usize).mpr (by simpa using hcon))⟩
       have hconf : ¬ (Solver.levelOf s lit.var = conflict_level.val) := by
         rw [hlvl2, ← hi23]
         exact fun hcon =>
           ‹¬ i3 = conflict_level› ((Std.UScalar.eq_equiv i3 conflict_level).mpr hcon)
       refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       case _ =>
         rw [hslvl, hsseen, __post2 true, hv10, lower1_post, marked1_post]
           at clauses'_post1
         rw [hdrop, Solver.scan, if_neg hfresh, if_neg hconf]
         exact clauses'_post1
       all_goals simp only [hsclauses, hsproblem, hsvalue, hslevel, hsreason, hsphase,
         hsoccurs, hstrail, hstlim, hsconf] at *
       all_goals first | assumption | omega)
termination_by cl.length - iter.start.val
decreasing_by
  -- The cursor moved forward, and it had not reached the end.
  all_goals
    obtain ⟨-, hlt, hnext⟩ := o_post2 _ (by assumption)
    omega

/-- **Spec for `analyze`'s resolution loop**: from a state satisfying the invariant it
    returns the learned clause and the backjump level `analyze.spec` promises, and puts
    every field of the solver back as it found it except `activity`.

    `pending` cannot overflow its `i32`: it never exceeds the length of the trail, and
    `trail_length_le` bounds that by `2 ^ 16`. -/
@[step]
theorem sat_cdcl.Solver.analyze_loop0.spec (s : sat_cdcl.Solver)
    (empty : alloc.vec.Vec cnf.Literal) (activity : alloc.vec.Vec Std.U32)
    (seen : alloc.vec.Vec Bool) (conflict_level : Std.Usize)
    (lower : alloc.vec.Vec cnf.Literal) (pending : Std.I32)
    (marked : alloc.vec.Vec Std.U16) (index clause : Std.Usize)
    (resolved : core.option.Option Std.U16) (cl : List cnf.Literal)
    (hwf : Solver.WF s)
    (hempty : empty.val = [])
    (hact : activity.val.length = s.value.val.length)
    (hconflict_level : conflict_level.val = Solver.decisionLevel s)
    (hpos : 0 < Solver.decisionLevel s)
    (hclause : Solver.clauseAt s clause = some cl)
    (hinv : Solver.Analyzing s seen.val lower.val marked.val pending.val index.val cl
      resolved) :
    sat_cdcl.Solver.analyze_loop0 empty s.clauses s.problem_clauses s.value s.level
      s.reason s.phase activity s.occurs seen s.trail s.trail_lim s.conflicts
      conflict_level lower pending marked index clause resolved ⦃
      (lits : alloc.vec.Vec cnf.Literal) (backjump : Std.Usize)
      (clauses' : alloc.vec.Vec cnf.Clause) (problem_clauses' : Std.Usize)
      (value' : alloc.vec.Vec (core.option.Option Bool))
      (level' : alloc.vec.Vec Std.Usize)
      (reason' : alloc.vec.Vec (core.option.Option Std.Usize))
      (phase' : alloc.vec.Vec Bool) (_activity' : alloc.vec.Vec Std.U32)
      (occurs' : alloc.vec.Vec Bool) (seen' : alloc.vec.Vec Bool)
      (trail' : alloc.vec.Vec Std.U16) (trail_lim' : alloc.vec.Vec Std.Usize)
      (conflicts' : Std.U32) =>
        Entails (Solver.db s) lits.val
        ∧ (∀ lit ∈ lits.val, Solver.litFalse s lit)
        ∧ (∃ uip rest, lits.val = uip :: rest
            ∧ Solver.levelOf s uip.var = Solver.decisionLevel s
            ∧ (∀ lit ∈ rest, 0 < Solver.levelOf s lit.var)
            ∧ (∀ lit ∈ rest, Solver.levelOf s lit.var ≤ backjump.val))
        ∧ backjump.val < Solver.decisionLevel s
        ∧ clauses' = s.clauses ∧ problem_clauses' = s.problem_clauses
        ∧ value' = s.value ∧ level' = s.level ∧ reason' = s.reason ∧ phase' = s.phase
        ∧ occurs' = s.occurs ∧ seen'.val = s.seen.val ∧ trail' = s.trail
        ∧ trail_lim' = s.trail_lim ∧ conflicts' = s.conflicts
        ∧ lits.val.length ≤ 2 ^ 16 + 1
        ∧ _activity'.val.length = activity.val.length ⦄ := by
  unfold sat_cdcl.Solver.analyze_loop0
  -- `step*` runs the body down to the two `expect`s -- the clause scan, the trail walk
  -- and the recursive call included -- leaving their preconditions and the two
  -- branches of `pending == 0`.
  step*
  -- The conflicting clause is in the database, so it is indexable.
  · obtain ⟨c0, hcget, -⟩ := Solver.clauseAt_eq hclause
    grind [List.getElem?_eq_some_iff]
  -- The scan runs over the whole clause.
  · obtain ⟨c0, hcget, hcval⟩ := Solver.clauseAt_eq hclause
    have hcc : c = c0 := by rw [hcget] at c_post; exact (Option.some.inj c_post).symm
    simp [i2_post, hcc, hcval]
  · rw [hinv.seen_length]; exact hwf.seen_length
  · exact hwf.level_length
  · exact hinv.clause_bound
  -- Nothing overflows over one pass of the clause.
  · obtain ⟨hb1, hb2, hb3, hb4⟩ := Solver.Marking.bounds hwf hinv.toMarking
    have hdb := hwf.db_len cl hinv.clause_mem
    have hmx : (Std.I32.max : Int) ≤ (Std.Usize.max : Int) := by scalar_tac
    simp only []
    exact ⟨by omega, by omega, by omega⟩
  -- The cursor is still inside the trail, and the trail is still inside the arrays.
  · rw [v10_post9]; exact hinv.index_le
  · obtain ⟨hmark2, -, -, -⟩ :=
      Solver.scan_of_Analyzing s hwf hconflict_level hinv v10_post1
    rw [v10_post9, v10_post5]
    intro v hv
    exact ⟨by rw [hwf.level_length]; exact hwf.trail_bound v hv,
      by rw [hmark2.seen_length, hwf.seen_length]; exact hwf.trail_bound v hv⟩
  -- The walk's witness: something is still pending, so the walk stops at or before it.
  · obtain ⟨hmark2, hmono2, -, hres2⟩ :=
      Solver.scan_of_Analyzing s hwf hconflict_level hinv v10_post1
    have hne : Solver.pendingVars s v17.val (Solver.decisionLevel s) index.val ≠ [] := by
      intro hnil
      rcases hinv.pending_pos with hp | ⟨lit, hlit, hlvl, hnr⟩
      · have h1 := hinv.pending_eq
        have h2 := Solver.length_pendingVars_mono (s := s)
          (K := Solver.decisionLevel s) (index := index.val) hmono2
        rw [hnil] at h2
        simp only [List.length_nil, Nat.le_zero] at h2
        omega
      · have hmem := hres2 lit hlit hnr (by omega)
        rw [Solver.resolvent, hnil] at hmem
        simp only [List.map_nil, List.append_nil] at hmem
        exact absurd (hmark2.lower_level lit hmem).2 (by omega)
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hne
    simp only [Solver.pendingVars, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hu
    obtain ⟨hutake, humark, hulvl⟩ := hu
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hutake
    rw [List.getElem?_take] at hj
    split at hj
    · refine ⟨j, u, ‹_›, by rw [v10_post9]; exact hj,
        Solver.isMarked_iff.mp humark, ?_⟩
      rw [v10_post5]
      exact Solver.getElem_of_levelOf (by rw [hulvl, hconflict_level]) (by omega)
    · simp at hj
  -- `pending` is a count, so subtracting one from it stays in range.
  · obtain ⟨hmark2, -, -, -⟩ :=
      Solver.scan_of_Analyzing s hwf hconflict_level hinv v10_post1
    obtain ⟨-, -, hb3, -⟩ := Solver.Marking.bounds hwf hmark2
    scalar_tac
  -- The UIP has a value slot and a reason slot.
  · have hv20 : v20 ∈ s.trail.val := by
      rw [← v10_post9]; exact List.mem_of_getElem? index1_post2
    rw [v10_post4, i5_post]
    simpa using hwf.trail_bound _ hv20
  -- The break: the walk has reached the UIP, so the resolvent is the learned clause.
  · obtain ⟨hmark2, hmono2, hlow2, hres2⟩ :=
      Solver.scan_of_Analyzing s hwf hconflict_level hinv v10_post1
    have hv20mem : v20 ∈ s.trail.val := by
      rw [← v10_post9]; exact List.mem_of_getElem? index1_post2
    have hv20lvl : Solver.levelOf s v20 = Solver.decisionLevel s := by
      rw [← hconflict_level]
      exact Solver.levelOf_of_getElem (by rw [← v10_post5]; exact index1_post4)
    have hoval : s.value.val[v20.val]? = some o := by
      rw [← v10_post4, show v20.val = i5.val by rw [i5_post]; simp]
      exact o_post
    have hval_eq : Solver.valueOf s v20 = o := by
      rw [Solver.valueOf, hoval]; cases o <;> rfl
    obtain ⟨bv, hbv⟩ : ∃ b, Solver.valueOf s v20 = some b := by
      rcases hv : Solver.valueOf s v20 with _ | b
      · exact absurd ((hwf.trail_iff v20).mpr hv20mem) (by rw [hv]; simp)
      · exact ⟨b, rfl⟩
    rw [show o = some bv by rw [← hval_eq]; exact hbv, Option.expect_some]
    unfold alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    step*
    -- The collected literals and the marks are in range of the slot arrays.
    · rw [v10_post5]
      intro lit hlit
      rw [hwf.level_length]
      exact Solver.lt_length_of_litFalse (hmark2.lower_false lit hlit)
    · obtain ⟨-, hb2, -, -⟩ := Solver.Marking.bounds hwf hmark2
      simp only [lits_post, hempty, List.nil_append, List.length_cons, List.length_nil]
      scalar_tac
    · intro x hx
      rw [hmark2.seen_length, hwf.seen_length]
      exact hwf.trail_bound x (hmark2.marked_trail x hx)
    -- The learned clause.
    · have hz : pending2 = 0#i32 := by assumption
      have hv20mark : Solver.isMarked v17.val v20 = true :=
        Solver.isMarked_iff.mpr index1_post3
      -- The walk returned the last pending variable, and it was the only one left.
      have hsplit : Solver.pendingVars s v17.val (Solver.decisionLevel s) index.val
          = Solver.pendingVars s v17.val (Solver.decisionLevel s) index1.val ++ [v20] := by
        refine Solver.pendingVars_split index1_post1
          (by rw [← v10_post9]; exact index1_post2) hv20mark hv20lvl ?_
        rintro k u hk1 hk2 hget ⟨hm, hl⟩
        exact index1_post5 k u hk1 hk2 (by rw [v10_post9]; exact hget)
          ⟨Solver.isMarked_iff.mp hm, by
            rw [v10_post5]
            exact Solver.getElem_of_levelOf (by rw [hl, hconflict_level]) (by omega)⟩
      have hnil : Solver.pendingVars s v17.val (Solver.decisionLevel s) index1.val = [] := by
        have h1 := hmark2.pending_eq
        rw [hsplit] at h1
        simp only [List.length_append, List.length_cons, List.length_nil] at h1
        have hz' : pending2.val = 0 := by rw [hz]; rfl
        exact List.eq_nil_of_length_eq_zero (by omega)
      have hresolvent :
          Solver.resolvent s v17.val lower2.val (Solver.decisionLevel s) index.val
            = lower2.val ++ [Solver.falseLit s v20] := by
        rw [Solver.resolvent, hsplit, hnil]; simp
      -- The invariant's clause, with the scan folded into it.
      have hent : Entails (Solver.db s)
          (Solver.resolvent s v17.val lower2.val (Solver.decisionLevel s) index.val) := by
        refine Entails.weaken hinv.entails ?_
        intro lit hlit
        rcases List.mem_append.mp hlit with h | h
        · exact Solver.mem_resolvent_mono hmono2 hlow2 lit h
        · rw [Solver.carried, List.mem_filter] at h
          obtain ⟨hmem, hcond⟩ := h
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
            beq_eq_false_iff_ne, ne_eq] at hcond
          exact hres2 lit hmem hcond.1 hcond.2
      have hlits1 : lits1.val = Solver.falseLit s v20 :: lower2.val := by
        rw [lits1_post1, lits_post, hempty]
        simp only [List.nil_append, List.singleton_append]
        congr 1
        simp only [Solver.falseLit, hbv, Option.getD_some]
      refine ⟨?_, ?_, ⟨Solver.falseLit s v20, lower2.val, hlits1, ?_, ?_, ?_⟩, ?_,
        v10_post2, v10_post3, v10_post4, v10_post5, v10_post6, v10_post7, v10_post8, ?_,
        v10_post9, v10_post10, v10_post11, ?_, v10_post12⟩
      · rw [hlits1]
        refine Entails.weaken (hresolvent ▸ hent) ?_
        intro lit hlit
        rcases List.mem_append.mp hlit with h | h
        · exact List.mem_cons_of_mem _ h
        · simp only [List.mem_singleton] at h
          subst h
          exact List.mem_cons_self ..
      · rw [hlits1]
        intro lit hlit
        rcases List.mem_cons.mp hlit with rfl | h
        · simp [Solver.litFalse, Solver.falseLit, hbv]
        · exact hmark2.lower_false lit h
      · simpa [Solver.falseLit] using hv20lvl
      · exact fun lit h => (hmark2.lower_level lit h).1
      · intro lit hlit
        rw [lits1_post2, v10_post5]
        exact level_le_maxLevel hlit
      · rw [lits1_post2, v10_post5]
        have hle : maxLevel s.level.val 0 lower2.val ≤ Solver.decisionLevel s - 1 :=
          maxLevel_le (by omega) fun lit hlit =>
            Nat.le_sub_one_of_lt (hmark2.lower_level lit hlit).2
        omega
      -- The scratch array comes back as it went in.
      · rw [v21_post]
        refine foldl_set_false_eq_base hmark2.seen_length hwf.seen_clear ?_ ?_
        · intro x hx
          rw [hmark2.seen_length, hwf.seen_length]
          exact hwf.trail_bound x (hmark2.marked_trail x hx)
        · intro i hi
          have hlen : v17.val.length = s.seen.val.length := hmark2.seen_length
          by_cases hlt : i < s.seen.val.length
          · have hlt' : i < v17.val.length := by omega
            rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hlt',
              hwf.seen_clear _ (List.getElem_mem hlt)]
            congr 1
            by_contra hc
            have htrue : v17.val[i] = true := by
              cases h : v17.val[i] <;> simp_all
            obtain ⟨u, hu, huv⟩ :=
              hmark2.marked_of_seen i (by rw [List.getElem?_eq_getElem hlt', htrue])
            exact hi u hu huv
          · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
      -- The learned clause is short: one literal per marked variable, and the marked
      -- variables are distinct entries of the trail.
      · obtain ⟨-, hb2, -, -⟩ := Solver.Marking.bounds hwf hmark2
        rw [hlits1]
        simp only [List.length_cons]
        omega
  · have hv20 : v20 ∈ s.trail.val := by
      rw [← v10_post9]; exact List.mem_of_getElem? index1_post2
    rw [v10_post6, i5_post]
    simpa [hwf.reason_length] using hwf.trail_bound _ hv20
  -- The resolution step: more than one conflict-level variable is still pending, so
  -- the walk's variable was propagated, and its reason is the next clause to resolve.
  · obtain ⟨hmark2, hmono2, hlow2, hres2⟩ :=
      Solver.scan_of_Analyzing s hwf hconflict_level hinv v10_post1
    have hz : ¬ pending2 = 0#i32 := by assumption
    have hv20mem : v20 ∈ s.trail.val := by
      rw [← v10_post9]; exact List.mem_of_getElem? index1_post2
    have hv20lvl : Solver.levelOf s v20 = Solver.decisionLevel s := by
      rw [← hconflict_level]
      exact Solver.levelOf_of_getElem (by rw [← v10_post5]; exact index1_post4)
    have hv20mark : Solver.isMarked v17.val v20 = true :=
      Solver.isMarked_iff.mpr index1_post3
    have hsplit : Solver.pendingVars s v17.val (Solver.decisionLevel s) index.val
        = Solver.pendingVars s v17.val (Solver.decisionLevel s) index1.val ++ [v20] := by
      refine Solver.pendingVars_split index1_post1
        (by rw [← v10_post9]; exact index1_post2) hv20mark hv20lvl ?_
      rintro k u hk1 hk2 hget ⟨hm, hl⟩
      exact index1_post5 k u hk1 hk2 (by rw [v10_post9]; exact hget)
        ⟨Solver.isMarked_iff.mp hm, by
          rw [v10_post5]
          exact Solver.getElem_of_levelOf (by rw [hl, hconflict_level]) (by omega)⟩
    have hpend2 : pending2.val
        = (Solver.pendingVars s v17.val (Solver.decisionLevel s) index1.val).length := by
      have h1 := hmark2.pending_eq
      rw [hsplit] at h1
      simp only [List.length_append, List.length_cons, List.length_nil] at h1
      omega
    have hne : Solver.pendingVars s v17.val (Solver.decisionLevel s) index1.val ≠ [] := by
      intro hnil
      exact hz ((Std.IScalar.eq_equiv pending2 0#i32).mpr (by rw [hpend2, hnil]; rfl))
    have hidxv : s.trail.val.idxOf v20 = index1.val :=
      Solver.idxOf_eq_of_getElem? hwf.trail_nodup (by rw [← v10_post9]; exact index1_post2)
    -- `v20` is not the decision that opened the conflict level: something the walk has
    -- not reached yet is still pending, and the decision comes first.
    obtain ⟨r, hr⟩ : ∃ r, Solver.reasonOf s v20 = some r := by
      rcases hrr : Solver.reasonOf s v20 with _ | r
      · exfalso
        obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hne
        simp only [Solver.pendingVars, List.mem_filter, Bool.and_eq_true,
          beq_iff_eq] at hu
        obtain ⟨hutake, humark, hulvl⟩ := hu
        have hidxu : s.trail.val.idxOf u < index1.val :=
          Solver.idxOf_lt_of_mem_take hwf.trail_nodup hutake
        have hle := hwf.decision_first v20 hv20mem (by omega) hrr u
          (List.mem_of_mem_take hutake) (by rw [hulvl, hv20lvl])
        omega
      · exact ⟨r, rfl⟩
    have horeason : s.reason.val[v20.val]? = some o := by
      rw [← v10_post6, show v20.val = i5.val by rw [i5_post]; simp]
      exact o_post
    have hreq : Solver.reasonOf s v20 = o := by
      rw [Solver.reasonOf, horeason]; cases o <;> rfl
    obtain ⟨cl2, hcl2, htrue2, hrest2⟩ := hwf.reason_wf v20 r hr
    -- Nothing in the resolvent behind the new cursor is on `v20`: `lower` sits below
    -- the conflict level, and the pending variables sit before `v20` on the trail.
    have hAv : ∀ lit ∈ Solver.resolvent s v17.val lower2.val (Solver.decisionLevel s)
        index1.val, lit.var ≠ v20 := by
      intro lit hlit
      rcases List.mem_append.mp hlit with h | h
      · intro hc
        have hlt := (hmark2.lower_level lit h).2
        rw [hc, hv20lvl] at hlt
        omega
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
        simp only [Solver.pendingVars, List.mem_filter, Bool.and_eq_true,
          beq_iff_eq] at hu
        have hidxu : s.trail.val.idxOf u < index1.val :=
          Solver.idxOf_lt_of_mem_take hwf.trail_nodup hu.1
        intro hc
        simp only [Solver.falseLit] at hc
        rw [hc] at hidxu
        omega
    have hmark3 : Solver.Marking s v17.val lower2.val marked1.val pending2.val
        index1.val :=
      { pending_eq := hpend2
        seen_length := hmark2.seen_length
        seen_of_marked := hmark2.seen_of_marked
        marked_of_seen := hmark2.marked_of_seen
        marked_trail := hmark2.marked_trail
        marked_level := hmark2.marked_level
        marked_nodup := hmark2.marked_nodup
        lower_false := hmark2.lower_false
        lower_level := hmark2.lower_level
        lower_marked := hmark2.lower_marked
        lower_nodup := hmark2.lower_nodup
        lower_of_marked := hmark2.lower_of_marked
        index_le := by have := hmark2.index_le; omega }
    -- The recursive call gets the solver's own fields back, so name them that way.
    subst v10_post2 v10_post3 v10_post4 v10_post5 v10_post6 v10_post7 v10_post8
      v10_post9 v10_post10 v10_post11
    rw [show o = some r by rw [← hreq]; exact hr, Option.expect_some]
    step*
    -- `step` reads the next clause off `hcl2` itself; what is left is the invariant,
    -- and the postcondition the recursive call hands back.
    · -- The invariant, one resolution step on.
      refine
        { toMarking := hmark3
          entails := ?_
          pending_pos := Or.inl (by
            have hlen : 0 < (Solver.pendingVars s v17.val (Solver.decisionLevel s)
                index1.val).length := by
              rcases hp : Solver.pendingVars s v17.val (Solver.decisionLevel s)
                index1.val with _ | ⟨a, t⟩
              · exact absurd hp hne
              · simp
            omega)
          clause_mem := Solver.mem_db_of_clauseAt hcl2
          clause_bound := ?_
          clause_false := ?_
          clause_behind := ?_ }
      · -- **One iteration is one resolution step.**
        have hentIdx : Entails (Solver.db s)
            (Solver.resolvent s v17.val lower2.val (Solver.decisionLevel s) index.val) := by
          refine Entails.weaken hinv.entails ?_
          intro lit hlit
          rcases List.mem_append.mp hlit with h | h
          · exact Solver.mem_resolvent_mono hmono2 hlow2 lit h
          · rw [Solver.carried, List.mem_filter] at h
            obtain ⟨hmem, hcond⟩ := h
            simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
              beq_eq_false_iff_ne, ne_eq] at hcond
            exact hres2 lit hmem hcond.1 hcond.2
        rw [show Solver.resolvent s v17.val lower2.val (Solver.decisionLevel s) index.val
            = Solver.resolvent s v17.val lower2.val (Solver.decisionLevel s) index1.val
              ++ [Solver.falseLit s v20] by
          rw [Solver.resolvent, Solver.resolvent, hsplit]; simp] at hentIdx
        have hcp : ∀ lit ∈ (Solver.resolvent s v17.val lower2.val
            (Solver.decisionLevel s) index1.val ++ [Solver.falseLit s v20]),
            lit.var = v20 → lit.negated = (Solver.valueOf s v20).getD false := by
          intro lit hlit hvar
          rcases List.mem_append.mp hlit with h | h
          · exact absurd hvar (hAv lit h)
          · simp only [List.mem_singleton] at h
            subst h
            simp [Solver.falseLit]
        have hdp : ∀ lit ∈ cl2, lit.var = v20 →
            lit.negated = !((Solver.valueOf s v20).getD false) := by
          intro lit hlit hvar
          by_cases hcase : lit = Solver.trueLit s v20
          · rw [hcase]; simp [Solver.trueLit]
          · exfalso
            have hlt := (hrest2 lit hlit hcase).2.1
            rw [hvar] at hlt
            omega
        have hstep := Entails.resolution hentIdx
          (Entails.of_mem (Solver.mem_db_of_clauseAt hcl2)) hcp hdp
        have hfalse : ∀ lit ∈ ((Solver.resolvent s v17.val lower2.val
            (Solver.decisionLevel s) index1.val ++ [Solver.falseLit s v20]).filter
              (fun lit => lit.var != v20)
            ++ cl2.filter (fun lit => lit.var != v20)), Solver.litFalse s lit := by
          intro lit hlit
          rcases List.mem_append.mp hlit with h | h
          · rw [List.mem_filter] at h
            rcases List.mem_append.mp h.1 with h' | h'
            · exact (Solver.mem_resolvent_false hwf hmark3 hpos lit h').1
            · simp only [List.mem_singleton] at h'
              subst h'
              exact absurd h.2 (by simp [Solver.falseLit])
          · rw [List.mem_filter] at h
            refine (hrest2 lit h.1 ?_).1
            intro hc
            rw [hc] at h
            simp [Solver.trueLit] at h
        refine Entails.weaken (Entails.drop_level_zero hwf hstep hfalse) ?_
        intro lit hlit
        rw [List.mem_filter] at hlit
        obtain ⟨hmem, hlvl0⟩ := hlit
        rcases List.mem_append.mp hmem with h | h
        · rw [List.mem_filter] at h
          rcases List.mem_append.mp h.1 with h' | h'
          · exact List.mem_append_left _ h'
          · simp only [List.mem_singleton] at h'
            subst h'
            exact absurd h.2 (by simp [Solver.falseLit])
        · rw [List.mem_filter] at h
          refine List.mem_append_right _ ?_
          rw [Solver.carried, List.mem_filter]
          refine ⟨h.1, ?_⟩
          simp only [Bool.and_eq_true]
          refine ⟨?_, hlvl0⟩
          have hne2 : ¬ (v20 = lit.var) := fun hc =>
            (by simpa using h.2 : lit.var ≠ v20) hc.symm
          simp [hne2]
      · intro lit hlit
        by_cases hcase : lit = Solver.trueLit s v20
        · rw [hcase]
          exact hwf.trail_bound v20 hv20mem
        · exact Solver.lt_length_of_litFalse (hrest2 lit hlit hcase).1
      · intro lit hlit hne'
        refine (hrest2 lit hlit ?_).1
        intro hc
        exact hne' (by rw [hc]; rfl)
      · intro lit hlit hne'
        have hlt := (hrest2 lit hlit ?_).2.1
        · omega
        · intro hc
          exact hne' (by rw [hc]; rfl)
    -- The postcondition is the recursive call's, unchanged.
    · exact ⟨lits_post1, lits_post2,
        ⟨_, _, lits_post3, lits_post4, lits_post5, lits_post6⟩, lits_post7,
        lits_post8, lits_post9, lits_post10, lits_post11, lits_post12, lits_post13,
        lits_post14, lits_post15, lits_post16, lits_post17, lits_post18, lits_post19,
        by rw [lits_post20, v10_post12]⟩

/-! ### The statement

Last, because it is assembled from everything above: `analyze.spec` is the theorem the
rest of the file exists for. The order matches `SatDpll.lean`, where `solve_sat`'s
soundness and completeness also come at the bottom. -/

/-- **Specification of `sat_cdcl::analyze`** (1-UIP conflict analysis).

Given a well-formed state at a decision level above 0 and a clause every literal of
which is false, `analyze` succeeds and returns a clause that is (1) entailed by the
database, (2) false under the current assignment, (3) asserting at the returned
backjump level -- head at the conflict level, tail at levels in `(0, backjump]` -- and
(4) a backjump level strictly below the conflict level. It leaves every field of the
solver but `activity` exactly as it found it, `seen` included. -/
theorem sat_cdcl.Solver.analyze.spec (s : sat_cdcl.Solver) (conflict : Std.Usize)
    (hwf : Solver.WF s)
    (hlevel : 0 < Solver.decisionLevel s)
    (hcl : ∃ cl, Solver.clauseAt s conflict = some cl ∧
      (∀ lit ∈ cl, Solver.litFalse s lit) ∧
      (∃ lit ∈ cl, Solver.levelOf s lit.var = Solver.decisionLevel s)) :
    sat_cdcl.Solver.analyze s conflict ⦃
      (r : cnf.Clause × Std.Usize) (s' : sat_cdcl.Solver) =>
        Entails (Solver.db s) r.1.val
        ∧ (∀ lit ∈ r.1.val, Solver.litFalse s lit)
        ∧ (∃ uip rest, r.1.val = uip :: rest
            ∧ Solver.levelOf s uip.var = Solver.decisionLevel s
            ∧ (∀ lit ∈ rest, 0 < Solver.levelOf s lit.var)
            ∧ (∀ lit ∈ rest, Solver.levelOf s lit.var ≤ r.2.val))
        ∧ r.2.val < Solver.decisionLevel s
        ∧ s' = { s with activity := s'.activity }
        ∧ r.1.val.length ≤ 2 ^ 16 + 1
        ∧ s'.activity.val.length = s.activity.val.length ⦄ := by
  obtain ⟨cl, hclause, hclfalse, hconflictlit⟩ := hcl
  unfold sat_cdcl.Solver.analyze
  -- `step*` runs the body down to the resolution loop and applies its spec, leaving
  -- two goals: the loop's invariant on the state `analyze` starts from, and the
  -- postcondition, which is that spec's read off the reassembled solver.
  step*
  case hact => exact hwf.activity_length
  case hinv =>
    -- Nothing is marked yet, so the resolvent is empty and the whole invariant is a
    -- statement about the conflict clause.
    have hseen : ∀ u : Std.U16, Solver.isMarked s.seen.val u = false := by
      intro u
      simp only [Solver.isMarked]
      cases h : s.seen.val[u.val]? with
      | none => simp
      | some b => simp [hwf.seen_clear b (List.mem_of_getElem? h)]
    have hpending :
        Solver.pendingVars s s.seen.val (Solver.decisionLevel s) index.val = [] := by
      simp [Solver.pendingVars, hseen]
    have hmem : ∀ lit ∈ cl, lit.var ∈ s.trail.val := by
      intro lit hlit
      have hval : Solver.valueOf s lit.var = some lit.negated := hclfalse lit hlit
      rw [← hwf.trail_iff, hval]
      rfl
    exact {
      entails := by
        have h := Entails.drop_level_zero hwf
          (Entails.of_mem (Solver.mem_db_of_clauseAt hclause)) hclfalse
        simpa [Solver.resolvent, hpending, lower_post, Solver.carried] using h
      pending_eq := by simp [hpending]
      pending_pos := by
        obtain ⟨lit, hlit, hlvl⟩ := hconflictlit
        exact Or.inr ⟨lit, hlit, hlvl, by simp⟩
      seen_length := rfl
      seen_of_marked := by simp [marked_post]
      marked_of_seen := by
        intro i hi
        exact absurd (hwf.seen_clear true (List.mem_of_getElem? hi)) (by simp)
      marked_trail := by simp [marked_post]
      marked_level := by simp [marked_post]
      marked_nodup := by simp [marked_post]
      lower_false := by simp [lower_post]
      lower_level := by simp [lower_post]
      lower_marked := by simp [lower_post]
      lower_nodup := by simp [lower_post]
      lower_of_marked := by simp [marked_post]
      index_le := by simp [index_post]
      clause_mem := Solver.mem_db_of_clauseAt hclause
      clause_bound := fun lit hlit => hwf.trail_bound _ (hmem lit hlit)
      clause_false := fun lit hlit _ => hclfalse lit hlit
      clause_behind := by
        intro lit hlit _
        rw [index_post]
        exact List.idxOf_lt_length_of_mem (hmem lit hlit) }
  -- The postcondition: the loop's own, read off the solver the extraction reassembles
  -- from the fields it returned.
  refine ⟨v_post1, v_post2, ⟨_, _, v_post3, v_post4, v_post5, v_post6⟩, v_post7, ?_,
    v_post19, v_post20⟩
  have hseen : v8 = s.seen := Subtype.ext v_post15
  simp_all

/-! ### The hypotheses are not vacuous

`analyze.spec` is stated over a `Solver.WF` state at a decision level above 0 with a
conflicting clause, and nothing above shows such a state exists. A contradictory
`Solver.WF` would make the theorem worth nothing, so here is a state that satisfies
every hypothesis of it: one variable, decided true at level 1, conflicting with the
unit clause `¬x₀`. -/

/-- A one-variable conflicting state: `x₀` decided true at level 1, clause `¬x₀`. -/
def conflictState : sat_cdcl.Solver where
  clauses := ⟨[⟨[{ var := 0#u16, negated := true }], by scalar_tac⟩], by scalar_tac⟩
  problem_clauses := 1#usize
  value := ⟨[core.option.Option.Some true], by scalar_tac⟩
  level := ⟨[1#usize], by scalar_tac⟩
  reason := ⟨[core.option.Option.None], by scalar_tac⟩
  phase := ⟨[true], by scalar_tac⟩
  activity := ⟨[0#u32], by scalar_tac⟩
  occurs := ⟨[true], by scalar_tac⟩
  seen := ⟨[false], by scalar_tac⟩
  trail := ⟨[0#u16], by scalar_tac⟩
  trail_lim := ⟨[0#usize], by scalar_tac⟩
  conflicts := 0#u32

theorem conflictState.wf : Solver.WF conflictState := by
  have hnone : ∀ {α : Type} (a : α) (v : Std.U16), ¬ (v.val = 0) →
      ([a] : List α)[v.val]? = none := by
    intro α a v h
    exact List.getElem?_eq_none (by simp; omega)
  have htrail : conflictState.trail.val = [0#u16] := rfl
  have hdl : Solver.decisionLevel conflictState = 1 := rfl
  have hval : ∀ v : Std.U16, Solver.valueOf conflictState v
      = if v.val = 0 then some true else none := by
    intro v
    by_cases h : v.val = 0
    · simp [Solver.valueOf, conflictState, h]
    · simp [Solver.valueOf, conflictState, h]
  have hlvl : ∀ v : Std.U16, Solver.levelOf conflictState v
      = if v.val = 0 then 1 else 0 := by
    intro v
    by_cases h : v.val = 0
    · simp [Solver.levelOf, conflictState, h]
    · simp [Solver.levelOf, conflictState, h]
  have hreason : ∀ v : Std.U16, Solver.reasonOf conflictState v = none := by
    intro v
    by_cases h : v.val = 0
    · simp [Solver.reasonOf, conflictState, h]
    · simp [Solver.reasonOf, conflictState, hnone _ v h]
  have hmem : ∀ v : Std.U16, v ∈ conflictState.trail.val ↔ v.val = 0 := by
    intro v
    rw [htrail]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨fun h => by rw [h]; rfl, fun h => Solver.uscalar_eq_of_val (by simpa using h)⟩
  refine
    { level_length := rfl
      reason_length := rfl
      seen_length := rfl
      activity_length := rfl
      phase_length := rfl
      occurs_length := rfl
      db_len := ?_
      db_vars := ?_
      trail_bound := ?_
      trail_iff := ?_
      trail_nodup := by rw [htrail]; simp
      seen_clear := by simp [conflictState]
      level_le := ?_
      level_mono := ?_
      reason_wf := by simp [hreason]
      reason_assigned := by intro v h; rw [hreason v] at h; exact absurd rfl h
      level_zero_has_reason := ?_
      decision_of_level := ?_
      trail_lim_spec := ?_
      decision_first := ?_ }
  · intro d hd
    simp only [Solver.db, conflictState, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hd
    subst hd
    scalar_tac
  · intro d hd lit hlit
    simp only [Solver.db, conflictState, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hd
    subst hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
    subst hlit
    simp [conflictState]
  · intro v hv
    rw [hmem] at hv
    simp [conflictState, hv]
  · intro v
    rw [hmem, hval]
    by_cases h : v.val = 0 <;> simp [h]
  · intro v hv
    rw [hmem] at hv
    simp [hlvl, hv, hdl]
  · intro i j hi hj _
    have hi0 : i = 0 := by
      have : i < 1 := by simpa [conflictState] using hi
      omega
    have hj0 : j = 0 := by
      have : j < 1 := by simpa [conflictState] using hj
      omega
    subst hi0; subst hj0
    exact le_rfl
  · intro v hv h0
    rw [hmem] at hv
    rw [hlvl, if_pos hv] at h0
    exact absurd h0 (by omega)
  · intro u hu _
    rw [hmem] at hu
    exact ⟨0#u16, (hmem _).mpr rfl, by simp [hlvl, hu], hreason _⟩
  · intro j hj
    have hj0 : j = 0 := by
      have : j < 1 := by simpa [conflictState] using hj
      omega
    subst hj0
    refine ⟨by simp [conflictState], ?_⟩
    intro i hi
    have hi0 : i = 0 := by
      have : i < 1 := by simpa [conflictState] using hi
      omega
    subst hi0
    simp [conflictState, Solver.levelOf]
  · intro u hu _ _ w hw _
    rw [hmem] at hu hw
    have hu0 : u = 0#u16 := Solver.uscalar_eq_of_val (by simpa using hu)
    have hw0 : w = 0#u16 := Solver.uscalar_eq_of_val (by simpa using hw)
    rw [hu0, hw0]

/-- Everything `analyze.spec` asks for, on that state. -/
theorem conflictState.hypotheses :
    Solver.WF conflictState
    ∧ 0 < Solver.decisionLevel conflictState
    ∧ ∃ cl, Solver.clauseAt conflictState 0#usize = some cl
      ∧ (∀ lit ∈ cl, Solver.litFalse conflictState lit)
      ∧ (∃ lit ∈ cl, Solver.levelOf conflictState lit.var
          = Solver.decisionLevel conflictState) := by
  refine ⟨conflictState.wf, by simp [Solver.decisionLevel, conflictState],
    [{ var := 0#u16, negated := true }], rfl, ?_, ?_⟩
  · intro lit hlit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
    subst hlit
    simp [Solver.litFalse, Solver.valueOf, conflictState]
  · exact ⟨{ var := 0#u16, negated := true }, by simp,
      by simp [Solver.levelOf, Solver.decisionLevel, conflictState]⟩

/-! ### The whole correctness statement

`analyze.spec` is one node of a tree whose root is "`sat_cdcl::solve_sat` is a SAT
solver". The rest of that tree is stated here, top-down, the way the other files in this
directory were written (see `PLAN.md`): shapes fixed and mutually consistent first, then
discharged from the leaves up.

**Every statement in this section was written before it was proved, and several of them
were wrong.** That is what the top-down order bought, and it is worth recording what it
caught, because none of it is visible in the finished proofs: `Solver.WF` was missing five
fields; `search.spec` was not a true statement (checked `u32` arithmetic can fail, and a
first restart interval of `1` never terminates); `propagate.spec`'s "nothing is falsified"
hypothesis was not inductive; `analyze.spec` did not report the learned clause's length or
that the activity array keeps its own; `new.spec` did not report the slot count as the
*least* bound on the CNF's variables, without which the `solve_cnf` pair is vacuous. Each
one was found by a proof that could not close, not by reading the code.

The two roots are `solve_sat_sound` and `solve_sat_complete`, stated exactly as
`SatDpll.lean`'s proved `sat_dpll.solve_sat_sound`/`_complete` -- same conclusion, same
encoding, and the same two bounds hypotheses plus three more -- because CDCL is meant to be
a drop-in replacement for DPLL on the identical CNF, and a statement that differs in shape
would hide that.

None of the nine carries `@[step]` or any other attribute, deliberately: `step*` picks up
attributed specs automatically, and a spec of a whole function that a caller must supply
hypotheses to is one a caller should apply by name (`step with`), not one that should fire
on sight.

**These are total-correctness statements.** `⦃ ⦄` is `Aeneas.Std.WP.spec`, and
`spec div p ↔ False`, so each one asserts that the call *returns* as well as what it
returns. For `search.spec` that is the termination of CDCL search -- the hardest single
obligation here. `⦃ ⦄div` (`dspec`, which `div` satisfies) is the deliberate fallback if
that is to be deferred: it would weaken exactly `search.spec` and the two `solve_cnf`
statements to partial correctness and leave their content otherwise unchanged. Nothing
in this directory uses it today.
-/

/-- The clause-length bound `Solver.WF.db_len` asks for, as a statement about the input:
    `Solver.new` copies the CNF's clauses across unchanged, so this is what makes that
    field hold of the state it returns. -/
def CnfShort (c : List (List cnf.Literal)) : Prop :=
  ∀ cl ∈ c, cl.length + 2 ^ 16 ≤ Std.I32.max

/-! #### The state invariant

`Solver.WF` is what `analyze.spec` assumes. It is established once, by `new`, and
preserved by the three functions that write to the slot arrays -- `assign`, `propagate`,
`backtrack`. All four are proved below, so `analyze.spec` is no longer conditional on an
invariant nothing establishes: what is left is carrying it across `search`'s calls, where
the clause database itself changes. Each of the four statements carries, besides `Solver.WF`, the frame
conditions the caller needs -- what the database, the decision level and the trail did --
because `search.spec` has to thread all of them through the loop. -/

/-- **The inner loop of `new`'s variable count**: `num_vars` comes out above every
    literal's variable index, and never above `2 ^ 16`, since it is only ever set to a
    `u16` plus one. The upper bound is what makes the seven `Vec` pushes below safe.

    The last conjunct is the other half of "above every variable index": `num_vars` is
    the *least* such bound, so a caller who knows the variables fit below `m` knows the
    slot arrays are no longer than `m`. That is what `solve_cnf` needs, since the search
    measure -- and so the room the `u32` counters want -- is exponential in the number of
    slots: without it the only bound available is `2 ^ 16`, and `3 ^ (2 ^ 16)` makes the
    hypotheses unsatisfiable rather than merely demanding. -/
@[step]
theorem sat_cdcl.Solver.new_loop0_loop0.spec (iter : core.slice.iter.Iter cnf.Literal)
    (num_vars : Std.Usize) (hle : num_vars.val ≤ 2 ^ 16) :
    sat_cdcl.Solver.new_loop0_loop0 iter num_vars ⦃ (r : Std.Usize) =>
      num_vars.val ≤ r.val ∧ r.val ≤ 2 ^ 16
      ∧ (∀ lit ∈ iter.val, lit.var.val < r.val)
      ∧ ∀ m, num_vars.val ≤ m → (∀ lit ∈ iter.val, lit.var.val < m) → r.val ≤ m ⦄ := by
  unfold sat_cdcl.Solver.new_loop0_loop0
  step*
  all_goals
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      first
      | (simp_all; done)
      | (obtain ⟨heq, hiter⟩ := o_post
         have hlite : lit = e := by
           have h1 : o = some lit := by assumption
           rw [h1] at heq; exact Option.some.inj heq
         subst hlite
         refine ⟨by scalar_tac, r_post2, ?_, ?_⟩
         · intro w hw
           rcases List.mem_cons.mp (by simpa using hw) with rfl | hw'
           · scalar_tac
           · exact r_post3 w (by rw [hiter]; exact hw')
         · intro m hm hall
           have hm2 : lit.var.val < m := hall lit (by simp)
           refine r_post4 m (by scalar_tac) ?_
           intro w hw
           exact hall w (by simp only [hiter] at hw; simp [hw]))
termination_by iter.val.length
decreasing_by
  all_goals
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all

/-- The outer loop of the same pass, one clause at a time. Both halves -- upper bound
    and least upper bound -- come across from the inner loop unchanged. -/
@[step]
theorem sat_cdcl.Solver.new_loop0.spec (iter : core.slice.iter.Iter cnf.Clause)
    (num_vars : Std.Usize) (hle : num_vars.val ≤ 2 ^ 16) :
    sat_cdcl.Solver.new_loop0 iter num_vars ⦃ (r : Std.Usize) =>
      num_vars.val ≤ r.val ∧ r.val ≤ 2 ^ 16
      ∧ (∀ cl ∈ iter.val, ∀ lit ∈ cl.val, lit.var.val < r.val)
      ∧ ∀ m, num_vars.val ≤ m → (∀ cl ∈ iter.val, ∀ lit ∈ cl.val, lit.var.val < m) →
          r.val ≤ m ⦄ := by
  unfold sat_cdcl.Solver.new_loop0
  step*
  all_goals
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      first
      | (simp_all; done)
      | (obtain ⟨heq, hiter⟩ := o_post
         have hcle : clause = e := by
           have h1 : o = some clause := by assumption
           rw [h1] at heq; exact Option.some.inj heq
         subst hcle
         refine ⟨by omega, r_post2, ?_, ?_⟩
         · intro cl hcl lit hlit
           rcases List.mem_cons.mp (by simpa using hcl) with rfl | hcl'
           · have h := num_vars1_post3 lit (by rw [iter2_post, s_post]; exact hlit)
             omega
           · exact r_post3 cl (by rw [hiter]; exact hcl') lit hlit
         · intro m hm hall
           refine r_post4 m ?_ ?_
           · refine num_vars1_post4 m hm ?_
             intro lit hlit
             exact hall clause (by simp) lit
               (by rw [iter2_post, s_post] at hlit; exact hlit)
           · intro cl hcl lit hlit
             exact hall cl (by rw [hiter] at hcl; simp [hcl]) lit hlit)
termination_by iter.val.length
decreasing_by
  all_goals
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all

/-- One more slot, as a `replicate`: `new`'s initialisation loop pushes one entry per
    step, and `end - start` counts the steps it has left. -/
theorem List.cons_replicate_sub {α : Type} (x : α) {e s : Nat} (h : s < e) :
    x :: List.replicate (e - (s + 1)) x = List.replicate (e - s) x := by
  have hs : e - s = (e - (s + 1)) + 1 := by omega
  rw [hs, List.replicate_succ]

/-- **`new`'s initialisation loop**: one push onto each of the seven slot arrays per
    variable, so each comes back with `num_vars` copies of its zero value appended.
    `seen` and `occurs` are handed the same (empty) `Vec` the extraction reuses for
    `phase`, which is why their postconditions are stated against `phase`. -/
@[step]
theorem sat_cdcl.Solver.new_loop1.spec (iter : core.ops.range.Range Std.Usize)
    (value : alloc.vec.Vec (core.option.Option Bool)) (level : alloc.vec.Vec Std.Usize)
    (reason : alloc.vec.Vec (core.option.Option Std.Usize)) (phase : alloc.vec.Vec Bool)
    (activity : alloc.vec.Vec Std.U32) (seen occurs : alloc.vec.Vec Bool)
    (hv : value.val.length + (iter.«end».val - iter.start.val) ≤ Usize.max)
    (hl : level.val.length + (iter.«end».val - iter.start.val) ≤ Usize.max)
    (hr : reason.val.length + (iter.«end».val - iter.start.val) ≤ Usize.max)
    (hp : phase.val.length + (iter.«end».val - iter.start.val) ≤ Usize.max)
    (ha : activity.val.length + (iter.«end».val - iter.start.val) ≤ Usize.max)
    (hs : seen.val.length + (iter.«end».val - iter.start.val) ≤ Usize.max)
    (ho : occurs.val.length + (iter.«end».val - iter.start.val) ≤ Usize.max) :
    sat_cdcl.Solver.new_loop1 iter value level reason phase activity seen occurs ⦃
      (value' : alloc.vec.Vec (core.option.Option Bool)) (level' : alloc.vec.Vec Std.Usize)
      (reason' : alloc.vec.Vec (core.option.Option Std.Usize)) (phase' : alloc.vec.Vec Bool)
      (activity' : alloc.vec.Vec Std.U32) (seen' : alloc.vec.Vec Bool)
      (occurs' : alloc.vec.Vec Bool) =>
        value'.val = value.val ++ List.replicate (iter.«end».val - iter.start.val)
            core.option.Option.None
        ∧ level'.val = level.val ++ List.replicate (iter.«end».val - iter.start.val) 0#usize
        ∧ reason'.val = reason.val ++ List.replicate (iter.«end».val - iter.start.val)
            core.option.Option.None
        ∧ phase'.val = phase.val ++ List.replicate (iter.«end».val - iter.start.val) false
        ∧ activity'.val = activity.val ++ List.replicate (iter.«end».val - iter.start.val)
            0#u32
        ∧ seen'.val = seen.val ++ List.replicate (iter.«end».val - iter.start.val) false
        ∧ occurs'.val = occurs.val ++ List.replicate (iter.«end».val - iter.start.val)
            false ⦄ := by
  unfold sat_cdcl.Solver.new_loop1
  step*
  all_goals simp_all
  all_goals
    obtain ⟨-, hlt, hstart⟩ := o_post2
    first
    | omega
    | simp [List.cons_replicate_sub _ hlt]
termination_by iter.«end».val - iter.start.val
decreasing_by
  all_goals
    obtain ⟨-, hlt, hstart⟩ := o_post2 _ (by assumption)
    rw [o_post1]
    omega

/-- **The inner loop of `new`'s `occurs` pass**: it marks every literal's variable and
    never unmarks one. Stated as "marks these, preserves those" rather than as a fold,
    because that is all `new.spec` needs and it composes directly with the outer loop. -/
@[step]
theorem sat_cdcl.Solver.new_loop2_loop0.spec (iter : core.slice.iter.Iter cnf.Literal)
    (occurs : alloc.vec.Vec Bool)
    (hbound : ∀ lit ∈ iter.val, lit.var.val < occurs.val.length) :
    sat_cdcl.Solver.new_loop2_loop0 iter occurs ⦃ (occurs' : alloc.vec.Vec Bool) =>
      occurs'.val.length = occurs.val.length
      ∧ (∀ lit ∈ iter.val, occurs'.val[lit.var.val]? = some true)
      ∧ (∀ i : Nat, occurs.val[i]? = some true → occurs'.val[i]? = some true) ⦄ := by
  unfold sat_cdcl.Solver.new_loop2_loop0
  step*
  all_goals
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      first
      | (simp_all; done)
      | (obtain ⟨hlit, hiter⟩ := o_post
         have hel : e = lit := by simp_all
         subst hel
         have hi : i.val = e.var.val := by rw [i_post]; simp
         have hset : (index_mut_back true).val = occurs.val.set e.var.val true := by
           rw [‹∀ y : Bool, (index_mut_back y).val = occurs.val.set i.val y› true, hi]
         have hlt : e.var.val < occurs.val.length := hbound e (by simp)
         refine ⟨by rw [occurs'_post1, hset]; simp, ?_, ?_⟩
         · intro l hl'
           rcases List.mem_cons.mp (show l ∈ e :: es by simpa using hl') with rfl | hl''
           · refine occurs'_post3 _ ?_
             rw [hset]
             exact List.getElem?_set_self (by simpa using hlt)
           · exact occurs'_post2 l (by rw [hiter]; exact hl'')
         · intro j hj
           refine occurs'_post3 j ?_
           rw [hset]
           by_cases hjv : j = e.var.val
           · subst hjv
             exact List.getElem?_set_self (by simpa using hlt)
           · rw [List.getElem?_set_ne (Ne.symm hjv)]
             exact hj)
termination_by iter.val.length
decreasing_by
  all_goals
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all

/-- The outer loop of the `occurs` pass. -/
@[step]
theorem sat_cdcl.Solver.new_loop2.spec (iter : core.slice.iter.Iter cnf.Clause)
    (occurs : alloc.vec.Vec Bool)
    (hbound : ∀ cl ∈ iter.val, ∀ lit ∈ cl.val, lit.var.val < occurs.val.length) :
    sat_cdcl.Solver.new_loop2 iter occurs ⦃ (occurs' : alloc.vec.Vec Bool) =>
      occurs'.val.length = occurs.val.length
      ∧ (∀ cl ∈ iter.val, ∀ lit ∈ cl.val, occurs'.val[lit.var.val]? = some true)
      ∧ (∀ i : Nat, occurs.val[i]? = some true → occurs'.val[i]? = some true) ⦄ := by
  unfold sat_cdcl.Solver.new_loop2
  step*
  all_goals
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      first
      | (simp_all; done)
      | (obtain ⟨hlit, hiter⟩ := o_post
         have hel : e = clause := by simp_all
         subst hel
         first
         | (intro cl hcl lit hlit'
            rw [occurs1_post1]
            refine hbound cl ?_ lit hlit'
            rw [hiter] at hcl
            simpa using List.mem_cons_of_mem _ hcl)
         | (refine ⟨by rw [occurs'_post1, occurs1_post1], ?_, ?_⟩
            · intro cl hcl lit hlit'
              rcases List.mem_cons.mp (show cl ∈ e :: es by simpa using hcl) with rfl | hcl'
              · exact occurs'_post3 _ (occurs1_post2 lit
                  (by rw [iter2_post, s_post]; simp_all))
              · exact occurs'_post2 cl (by rw [hiter]; exact hcl') lit hlit'
            · intro j hj
              exact occurs'_post3 j (occurs1_post3 j hj)))
termination_by iter.val.length
decreasing_by
  all_goals
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all

/-- **Cloning a clause is the identity.** `cnf.Clause` *is* a `Vec cnf.Literal`, so this
    is `Vec`'s clone spec fed `Literal`'s, and `Subtype.ext` to turn "same list" into
    "same clause". `new` clones the CNF into `clauses`, which is the only place in the
    solver that clones anything but a literal.

    It lives here rather than next to `cnf.Literal`'s in `Cnf.lean` on purpose: a new
    `@[step]` lemma changes what `step*` does in every proof that can see it, and
    everything in `Cnf.lean`'s import graph is already proved. -/
@[step]
theorem cnf.Clause.Insts.CoreCloneClone.clone.spec (self : cnf.Clause) :
    cnf.Clause.Insts.CoreCloneClone.clone self ⦃ (c : cnf.Clause) => c = self ⦄ := by
  unfold cnf.Clause.Insts.CoreCloneClone.clone
  step*
  · exact fun x => cnf.Literal.Insts.CoreCloneClone.clone.spec x
  · exact Subtype.ext v_post

/-- Nothing is assigned in a state whose `value` array is all `None`. -/
theorem Solver.valueOf_replicate {s : sat_cdcl.Solver} {n : Nat}
    (h : s.value.val = List.replicate n core.option.Option.None) (v : Std.U16) :
    Solver.valueOf s v = none := by
  simp only [Solver.valueOf, h, List.getElem?_replicate]
  by_cases hv : v.val < n <;> simp [hv]

/-- Likewise for `reason`: no variable has one. -/
theorem Solver.reasonOf_replicate {s : sat_cdcl.Solver} {n : Nat}
    (h : s.reason.val = List.replicate n core.option.Option.None) (v : Std.U16) :
    Solver.reasonOf s v = none := by
  simp only [Solver.reasonOf, h, List.getElem?_replicate]
  by_cases hv : v.val < n <;> simp [hv]

/-- **The invariant holds of a freshly built state.** Every slot array is a `replicate`
    of its zero value, nothing is on the trail and no level has been opened, so every
    field of `Solver.WF` that says anything at all is vacuous -- except `db_len`, which
    is about the input. This is `Solver.new`'s half of the invariant, factored out of the
    extraction so the loop bookkeeping above and the invariant reasoning stay apart. -/
theorem Solver.wf_of_fresh (s : sat_cdcl.Solver) (n : Nat)
    (hvalue : s.value.val = List.replicate n core.option.Option.None)
    (hlevel : s.level.val = List.replicate n 0#usize)
    (hreason : s.reason.val = List.replicate n core.option.Option.None)
    (hseen : s.seen.val = List.replicate n false)
    (hphase : s.phase.val = List.replicate n false)
    (hactivity : s.activity.val = List.replicate n 0#u32)
    (hoccurs : s.occurs.val.length = n)
    (htrail : s.trail.val = [])
    (htrail_lim : s.trail_lim.val = [])
    (hdb : ∀ d ∈ Solver.db s, d.length + 2 ^ 16 ≤ Std.I32.max)
    (hdbvars : ∀ cl ∈ Solver.db s, ∀ lit ∈ cl, lit.var.val < s.value.val.length) :
    Solver.WF s := by
  have hnone := Solver.valueOf_replicate hvalue
  have hrnone := Solver.reasonOf_replicate hreason
  have hdl : Solver.decisionLevel s = 0 := by
    simp [Solver.decisionLevel, htrail_lim]
  refine
    { level_length := by rw [hlevel, hvalue]; simp
      reason_length := by rw [hreason, hvalue]; simp
      seen_length := by rw [hseen, hvalue]; simp
      activity_length := by rw [hactivity, hvalue]; simp
      phase_length := by rw [hphase, hvalue]; simp
      occurs_length := by rw [hoccurs, hvalue]; simp
      db_len := hdb
      db_vars := hdbvars
      trail_bound := by rw [htrail]; simp
      trail_iff := ?_
      trail_nodup := by rw [htrail]; simp
      seen_clear := ?_
      level_le := by rw [htrail]; simp
      level_mono := ?_
      reason_wf := by intro v r h; rw [hrnone v] at h; exact absurd h (by simp)
      reason_assigned := by intro v h; rw [hrnone v] at h; exact absurd rfl h
      level_zero_has_reason := by rw [htrail]; simp
      decision_of_level := by rw [htrail]; simp
      trail_lim_spec := by rw [htrail_lim]; simp
      decision_first := by rw [htrail]; simp }
  · intro v
    rw [hnone v, htrail]
    simp
  · intro b hb
    rw [hseen] at hb
    exact List.eq_of_mem_replicate hb
  · intro i j hi hj hij
    rw [htrail] at hi
    simp at hi

/-- **`Solver::new` establishes the invariant.** The database is the CNF, nothing is
    assigned, the level is 0, and every variable the CNF mentions has a slot and is
    marked in `occurs` -- which is what makes `pick_branch_var` eventually assign it, and
    hence what makes a `true` answer a model of the whole CNF rather than of the part it
    happened to look at.

    The proof is the five loop specs above plus `Solver.wf_of_fresh`: `step*` runs the
    body, and what is left is reading the `replicate`s off the loop that built them. -/
theorem sat_cdcl.Solver.new.spec (cc : cnf.Cnf) (hshort : CnfShort (Cnf.contents cc)) :
    sat_cdcl.Solver.new cc ⦃ (s : sat_cdcl.Solver) =>
      Solver.WF s
      ∧ Solver.db s = Cnf.contents cc
      ∧ s.problem_clauses.val = (Cnf.contents cc).length
      ∧ Solver.decisionLevel s = 0
      ∧ s.trail.val = []
      ∧ (∀ v ∈ cnfVars (Cnf.contents cc),
          v.val < s.value.val.length ∧ s.occurs.val[v.val]? = some true)
      ∧ s.value.val.length ≤ 2 ^ 16
      ∧ (∀ m, (∀ v ∈ cnfVars (Cnf.contents cc), v.val < m) → s.value.val.length ≤ m)
      ∧ s.conflicts.val = 0 ⦄ := by
  unfold sat_cdcl.Solver.new
  step*
  · exact fun x => cnf.Clause.Insts.CoreCloneClone.clone.spec x
  · have hval : value1.val = List.replicate num_vars.val core.option.Option.None := by
      rw [value1_post1, value_post]; simp
    have hlvl : level1.val = List.replicate num_vars.val 0#usize := by
      rw [value1_post2, level_post]; simp
    have hrsn : reason1.val = List.replicate num_vars.val core.option.Option.None := by
      rw [value1_post3, reason_post]; simp
    have hsn : seen.val = List.replicate num_vars.val false := by
      rw [value1_post6, phase_post]; simp
    have hph : phase1.val = List.replicate num_vars.val false := by
      rw [value1_post4, phase_post]; simp
    have hac : activity1.val = List.replicate num_vars.val 0#u32 := by
      rw [value1_post5, activity_post]; simp
    have hoc : occurs.val = List.replicate num_vars.val false := by
      rw [value1_post7, phase_post]; simp
    -- Every variable the CNF mentions is below `num_vars`, hence has a slot.
    have hmem : ∀ w ∈ cnfVars (Cnf.contents cc), w.val < num_vars.val := by
      intro w hw
      simp only [cnfVars, Cnf.contents, List.mem_flatMap, List.mem_map, clauseVars] at hw
      obtain ⟨d, ⟨cl, hcl, rfl⟩, lit, hlit, rfl⟩ := hw
      exact num_vars_post3 cl (by rw [iter_post, s_post]; exact hcl) lit hlit
    refine ⟨?_, ?_, by rw [i_post]; simp [Cnf.contents],
      by simp [Solver.decisionLevel, level_post], by simpa using v1_post, ?_, ?_, ?_, by simp⟩
    · refine Solver.wf_of_fresh _ num_vars.val (by simpa using hval) (by simpa using hlvl)
        (by simpa using hrsn) (by simpa using hsn) (by simpa using hph)
        (by simpa using hac) (by simp [occurs1_post1, hoc]) (by simpa using v1_post)
        (by simpa using level_post) ?_ ?_
      · intro d hd
        refine hshort d ?_
        simpa only [Solver.db, Cnf.contents, v_post] using hd
      · intro d hd lit hlit
        have hdmem : d ∈ Cnf.contents cc := by
          simpa only [Solver.db, Cnf.contents, v_post] using hd
        have hvar : lit.var ∈ cnfVars (Cnf.contents cc) := by
          simp only [cnfVars, List.mem_flatMap, clauseVars, List.mem_map]
          exact ⟨d, hdmem, lit, hlit, rfl⟩
        simp only [hval, List.length_replicate]
        exact hmem lit.var hvar
    · simp only [Solver.db, Cnf.contents, v_post]
    · intro w hw
      refine ⟨by simp only [hval, List.length_replicate]; exact hmem w hw, ?_⟩
      simp only [cnfVars, Cnf.contents, List.mem_flatMap, List.mem_map, clauseVars] at hw
      obtain ⟨d, ⟨cl, hcl, rfl⟩, lit, hlit, rfl⟩ := hw
      exact occurs1_post2 cl (by rw [iter1_post, s1_post]; exact hcl) lit hlit
    · simp only [hval, List.length_replicate]
      exact num_vars_post2
    · -- the slot count is the *least* bound on the CNF's variables, which is what turns
      -- a hypothesis about the input into one about `3 ^ s.value.val.length`
      intro m hm
      simp only [hval, List.length_replicate]
      refine num_vars_post4 m (by simp) ?_
      intro cl hcl lit hlit
      refine hm lit.var ?_
      simp only [cnfVars, Cnf.contents, List.mem_flatMap, List.mem_map, clauseVars]
      exact ⟨cl.val, ⟨cl, by rw [iter_post, s_post] at hcl; exact hcl, rfl⟩, lit, hlit, rfl⟩

/-! #### Reading one slot back after a write

`assign`, `propagate` and `backtrack` all write single slots through `index_mut`, and
every invariant field is a statement about `Solver.valueOf`/`levelOf`/`reasonOf`. These
four turn "the array is the old one with slot `u` set" into "the accessor at `u` is the
new value, and elsewhere unchanged", which is the only way the proofs below touch
`List.set`. -/

/-- After `assign` wrote `value[u]`. -/
theorem Solver.valueOf_set {s s' : sat_cdcl.Solver} {u : Std.U16} {b : Bool}
    (h : s'.value.val = s.value.val.set u.val (core.option.Option.Some b))
    (hlt : u.val < s.value.val.length) (w : Std.U16) :
    Solver.valueOf s' w = if w.val = u.val then some b else Solver.valueOf s w := by
  simp only [Solver.valueOf, h]
  by_cases hw : w.val = u.val
  · rw [hw, List.getElem?_set_self hlt]
    simp
  · rw [List.getElem?_set_ne (Ne.symm hw)]
    simp [hw]

/-- After `assign` wrote `level[u]`. -/
theorem Solver.levelOf_set {s s' : sat_cdcl.Solver} {u : Std.U16} {k : Std.Usize}
    (h : s'.level.val = s.level.val.set u.val k)
    (hlt : u.val < s.level.val.length) (w : Std.U16) :
    Solver.levelOf s' w = if w.val = u.val then k.val else Solver.levelOf s w := by
  simp only [Solver.levelOf, h]
  by_cases hw : w.val = u.val
  · rw [hw, List.getElem?_set_self hlt]
    simp
  · rw [List.getElem?_set_ne (Ne.symm hw)]
    simp [hw]

/-- `reason` at another variable. Split into three rather than stated with an `if`,
    because the `Option`-of-`Option` match in `Solver.reasonOf` does not survive one. -/
theorem Solver.reasonOf_set_ne {s s' : sat_cdcl.Solver} {u w : Std.U16}
    {r : core.option.Option Std.Usize}
    (h : s'.reason.val = s.reason.val.set u.val r) (hw : w.val ≠ u.val) :
    Solver.reasonOf s' w = Solver.reasonOf s w := by
  simp only [Solver.reasonOf, h, List.getElem?_set_ne (Ne.symm hw)]

/-- `reason` at a variable just recorded as a decision. -/
theorem Solver.reasonOf_set_none {s s' : sat_cdcl.Solver} {u : Std.U16}
    (h : s'.reason.val = s.reason.val.set u.val core.option.Option.None)
    (hlt : u.val < s.reason.val.length) :
    Solver.reasonOf s' u = none := by
  simp only [Solver.reasonOf, h, List.getElem?_set_self hlt]

/-- `reason` at a variable just recorded as propagated. -/
theorem Solver.reasonOf_set_some {s s' : sat_cdcl.Solver} {u : Std.U16} {x : Std.Usize}
    (h : s'.reason.val = s.reason.val.set u.val (core.option.Option.Some x))
    (hlt : u.val < s.reason.val.length) :
    Solver.reasonOf s' u = some x := by
  simp only [Solver.reasonOf, h, List.getElem?_set_self hlt]

/-- A fresh entry appended to the trail lands at the end -- which is what makes every
    antecedent of a propagation sit strictly earlier on the trail than the variable it
    forces, i.e. what keeps the implication graph acyclic. -/
theorem List.idxOf_append_singleton_self {α : Type} [BEq α] [LawfulBEq α] {l : List α}
    {a : α} (h : a ∉ l) : (l ++ [a]).idxOf a = l.length := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    have hb : ¬ (b = a) := fun hc => h (by simp [hc])
    simp [hb, ih (fun hc => h (List.mem_cons_of_mem _ hc))]

/-- **`assign`'s half of the invariant**, as a statement about states rather than about
    the extraction: given the five slot writes `assign` performs, a well-formed state
    stays well-formed. This is where the two fields the Rust relies on silently are
    earned:

    * `decision_first` -- a decision is the earliest entry at its level -- comes from
      `hdecision`: `search` has just opened the level, so nothing else sits at it yet,
      and the new entry goes to the end of the trail.
    * `reason_wf`'s strict trail inequality, the acyclicity of the implication graph,
      comes from `hunit` plus `hfresh`: every other literal of the reason clause is
      already false, hence already assigned, hence already on the trail, and the new
      entry is appended after all of them (`List.idxOf_append_singleton_self`).

    `hopen` is the other half of `decision_of_level`, and it is the hypothesis writing
    this proof turned up: a *propagation* at a level above 0 does not itself open that
    level, so it can only preserve "every level with an entry has a decision" if the
    level already has one. `search` supplies it -- a propagation at level `k > 0` happens
    after the decision at `k`. -/
theorem Solver.wf_assign {s s' : sat_cdcl.Solver} {var : Std.U16} {value : Bool}
    {reason : core.option.Option Std.Usize} {k : Std.Usize}
    (hwf : Solver.WF s)
    (hslot : var.val < s.value.val.length)
    (hfresh : Solver.valueOf s var = none)
    (hdecision : reason = core.option.Option.None →
      0 < Solver.decisionLevel s ∧
      ∀ w ∈ s.trail.val, Solver.levelOf s w < Solver.decisionLevel s)
    (hopen : ∀ r, reason = core.option.Option.Some r → 0 < Solver.decisionLevel s →
      ∃ v ∈ s.trail.val, Solver.levelOf s v = Solver.decisionLevel s ∧
        Solver.reasonOf s v = none)
    (hunit : ∀ r, reason = core.option.Option.Some r →
      ∃ cl, Solver.clauseAt s r = some cl
        ∧ ({ var := var, negated := !value } : cnf.Literal) ∈ cl
        ∧ ∀ lit ∈ cl, lit ≠ ({ var := var, negated := !value } : cnf.Literal) →
            Solver.litFalse s lit)
    (hk : k.val = Solver.decisionLevel s)
    (hvalue : s'.value.val = s.value.val.set var.val (core.option.Option.Some value))
    (hlevel : s'.level.val = s.level.val.set var.val k)
    (hreason : s'.reason.val = s.reason.val.set var.val reason)
    (hphase : s'.phase.val = s.phase.val.set var.val value)
    (htrail : s'.trail.val = s.trail.val ++ [var])
    (hclauses : s'.clauses = s.clauses)
    (htlim : s'.trail_lim = s.trail_lim)
    (hseen : s'.seen = s.seen)
    (hactivity : s'.activity = s.activity)
    (hoccurs : s'.occurs = s.occurs) :
    Solver.WF s' := by
  have hlenr : var.val < s.reason.val.length := by rw [hwf.reason_length]; exact hslot
  have hdl : Solver.decisionLevel s' = Solver.decisionLevel s := by
    simp [Solver.decisionLevel, htlim]
  have hvarnot : var ∉ s.trail.val := by
    intro hc
    have h := (hwf.trail_iff var).mpr hc
    rw [hfresh] at h
    simp at h
  have hval' := Solver.valueOf_set hvalue hslot
  have hlvl' := Solver.levelOf_set hlevel (by rw [hwf.level_length]; exact hslot)
  have hne : ∀ w ∈ s.trail.val, w.val ≠ var.val := by
    intro w hw hc
    exact hvarnot (by rw [← Solver.uscalar_eq_of_val hc]; exact hw)
  have hvalvar : Solver.valueOf s' var = some value := by rw [hval' var]; simp
  have hlvlvar : Solver.levelOf s' var = Solver.decisionLevel s := by
    rw [hlvl' var]; simp [hk]
  have hvalold : ∀ w ∈ s.trail.val, Solver.valueOf s' w = Solver.valueOf s w := by
    intro w hw; rw [hval' w, if_neg (hne w hw)]
  have hlvlold : ∀ w ∈ s.trail.val, Solver.levelOf s' w = Solver.levelOf s w := by
    intro w hw; rw [hlvl' w, if_neg (hne w hw)]
  have hrsnold : ∀ w ∈ s.trail.val, Solver.reasonOf s' w = Solver.reasonOf s w := by
    intro w hw; exact Solver.reasonOf_set_ne hreason (hne w hw)
  have hmem : ∀ w : Std.U16, w ∈ s'.trail.val ↔ (w ∈ s.trail.val ∨ w = var) := by
    intro w; rw [htrail]; simp
  have hold : ∀ w : Std.U16, w ∈ s'.trail.val → ¬ (w.val = var.val) →
      w ∈ s.trail.val := by
    intro w hw hnv
    rcases (hmem w).mp hw with h | h
    · exact h
    · exact absurd (by rw [h]) hnv
  -- Literals false in `s` are on variables other than `var`, since `var` is unassigned.
  have hlitne : ∀ lit : cnf.Literal, Solver.litFalse s lit → lit.var.val ≠ var.val := by
    intro lit hl hc
    have hl' : Solver.valueOf s lit.var = some lit.negated := hl
    rw [Solver.uscalar_eq_of_val hc, hfresh] at hl'
    simp at hl'
  have hlitfalse : ∀ lit : cnf.Literal, Solver.litFalse s lit → Solver.litFalse s' lit := by
    intro lit hl
    have hne' := hlitne lit hl
    show Solver.valueOf s' lit.var = some lit.negated
    rw [hval' lit.var, if_neg hne']
    exact hl
  have hlen : s'.value.val.length = s.value.val.length := by rw [hvalue]; simp
  have hidxold : ∀ w ∈ s.trail.val, s'.trail.val.idxOf w = s.trail.val.idxOf w := by
    intro w hw; rw [htrail]; exact List.idxOf_append_of_mem hw
  have hidxvar : s'.trail.val.idxOf var = s.trail.val.length := by
    rw [htrail]; exact List.idxOf_append_singleton_self hvarnot
  have hclause : ∀ (r : Std.Usize) (cl : List cnf.Literal),
      Solver.clauseAt s r = some cl → Solver.clauseAt s' r = some cl := by
    intro r cl h; simpa only [Solver.clauseAt, Solver.db, hclauses] using h
  refine
    { level_length := by rw [hlevel, hlen]; simpa using hwf.level_length
      reason_length := by rw [hreason, hlen]; simpa using hwf.reason_length
      seen_length := by rw [hseen, hlen]; exact hwf.seen_length
      activity_length := by rw [hactivity, hlen]; exact hwf.activity_length
      phase_length := by rw [hphase, hlen]; simpa using hwf.phase_length
      occurs_length := by rw [hoccurs, hlen]; exact hwf.occurs_length
      db_len := by rw [Solver.db, hclauses]; exact hwf.db_len
      db_vars := by rw [Solver.db, hclauses, hlen]; exact hwf.db_vars
      trail_bound := ?_
      trail_iff := ?_
      trail_nodup := by
        rw [htrail, List.nodup_append]
        refine ⟨hwf.trail_nodup, by simp, ?_⟩
        simpa using hne
      seen_clear := by rw [hseen]; exact hwf.seen_clear
      level_le := ?_
      level_mono := ?_
      reason_wf := ?_
      reason_assigned := ?_
      level_zero_has_reason := ?_
      decision_of_level := ?_
      trail_lim_spec := ?_
      decision_first := ?_ }
  -- trail_bound
  · intro w hw
    rw [hlen]
    by_cases hnv : w.val = var.val
    · rw [hnv]; exact hslot
    · exact hwf.trail_bound w (hold w hw hnv)
  -- trail_iff
  · intro w
    by_cases hnv : w.val = var.val
    · have hveq : w = var := Solver.uscalar_eq_of_val hnv
      subst hveq
      rw [hvalvar]
      simp [(hmem w).mpr (Or.inr rfl)]
    · rw [hval' w, if_neg hnv, hmem w, hwf.trail_iff]
      have : ¬ (w = var) := fun hc => hnv (by rw [hc])
      simp [this]
  -- level_le
  · intro w hw
    rw [hdl]
    by_cases hnv : w.val = var.val
    · rw [Solver.uscalar_eq_of_val hnv, hlvlvar]
    · rw [hlvlold w (hold w hw hnv)]
      exact hwf.level_le w (hold w hw hnv)
  -- level_mono
  · intro i j hi hj hij
    have hlen' : s'.trail.val.length = s.trail.val.length + 1 := by rw [htrail]; simp
    rw [hlen'] at hi hj
    have hgi : s'.trail.val[i] = (s.trail.val ++ [var])[i]'(by rw [← htrail]; omega) :=
      List.getElem_of_eq htrail _
    have hgj : s'.trail.val[j] = (s.trail.val ++ [var])[j]'(by rw [← htrail]; omega) :=
      List.getElem_of_eq htrail _
    rw [hgi, hgj]
    by_cases hjn : j < s.trail.val.length
    · have hin : i < s.trail.val.length := lt_of_le_of_lt hij hjn
      rw [List.getElem_append_left hin, List.getElem_append_left hjn,
        hlvlold _ (List.getElem_mem hin), hlvlold _ (List.getElem_mem hjn)]
      exact hwf.level_mono i j hin hjn hij
    · have hjeq : j = s.trail.val.length := by omega
      subst hjeq
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      by_cases hin : i < s.trail.val.length
      · rw [List.getElem_append_left hin, hlvlold _ (List.getElem_mem hin), hlvlvar]
        exact hwf.level_le _ (List.getElem_mem hin)
      · have hieq : i = s.trail.val.length := by omega
        subst hieq
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp

  -- reason_wf
  · intro v r hr
    by_cases hnv : v.val = var.val
    · have hveq : v = var := Solver.uscalar_eq_of_val hnv
      rw [hveq] at hr ⊢
      have hrs : reason = core.option.Option.Some r := by
        cases hrc : reason with
        | none =>
          rw [Solver.reasonOf_set_none (by rw [hreason, hrc]) hlenr] at hr
          simp at hr
        | some x =>
          rw [Solver.reasonOf_set_some (by rw [hreason, hrc]) hlenr] at hr
          have hxr : x = r := by injection hr
          simp [hxr]
      obtain ⟨cl, hcl, hmemlit, hrest⟩ := hunit r hrs
      have htl : Solver.trueLit s' var = { var := var, negated := !value } := by
        simp [Solver.trueLit, hvalvar]
      refine ⟨cl, hclause r cl hcl, by rw [htl]; exact hmemlit, ?_⟩
      intro lit hlit hlitneq
      rw [htl] at hlitneq
      have hlf := hrest lit hlit hlitneq
      refine ⟨hlitfalse lit hlf, ?_, ?_⟩
      · rw [hidxold _ (Solver.mem_trail_of_litFalse hwf hlf), hidxvar]
        exact List.idxOf_lt_length_of_mem (Solver.mem_trail_of_litFalse hwf hlf)
      · rw [hlvlold _ (Solver.mem_trail_of_litFalse hwf hlf), hlvlvar]
        exact hwf.level_le _ (Solver.mem_trail_of_litFalse hwf hlf)
    · rw [Solver.reasonOf_set_ne hreason hnv] at hr
      obtain ⟨cl, hcl, hmemlit, hrest⟩ := hwf.reason_wf v r hr
      have hvalv : Solver.valueOf s' v = Solver.valueOf s v := by
        rw [hval' v, if_neg hnv]
      have hlvlv : Solver.levelOf s' v = Solver.levelOf s v := by
        rw [hlvl' v, if_neg hnv]
      have htl : Solver.trueLit s' v = Solver.trueLit s v := by
        simp [Solver.trueLit, hvalv]
      -- The trail position of `v` moves only if `v` was not on the trail at all, and
      -- then it lands past every old entry, which is all the inequality needs.
      have hidxv : s.trail.val.idxOf v ≤ s'.trail.val.idxOf v := by
        by_cases hvm : v ∈ s.trail.val
        · rw [hidxold v hvm]
        · have hvnot : v ∉ s'.trail.val := by
            rw [hmem v]
            exact fun hc => hc.elim hvm (fun h => hnv (by rw [h]))
          rw [List.idxOf_eq_length hvnot, List.idxOf_eq_length hvm, htrail]
          simp
      refine ⟨cl, hclause r cl hcl, by rw [htl]; exact hmemlit, ?_⟩
      intro lit hlit hlitneq
      rw [htl] at hlitneq
      obtain ⟨hlf, hidx, hlvl⟩ := hrest lit hlit hlitneq
      refine ⟨hlitfalse lit hlf, ?_, ?_⟩
      · calc s'.trail.val.idxOf lit.var
            = s.trail.val.idxOf lit.var :=
              hidxold _ (Solver.mem_trail_of_litFalse hwf hlf)
          _ < s.trail.val.idxOf v := hidx
          _ ≤ s'.trail.val.idxOf v := hidxv
      · rw [hlvlold _ (Solver.mem_trail_of_litFalse hwf hlf), hlvlv]
        exact hlvl
  -- reason_assigned
  · intro v hr
    by_cases hnv : v.val = var.val
    · rw [Solver.uscalar_eq_of_val hnv]
      exact (hmem var).mpr (Or.inr rfl)
    · rw [Solver.reasonOf_set_ne hreason hnv] at hr
      exact (hmem v).mpr (Or.inl (hwf.reason_assigned v hr))
  -- level_zero_has_reason
  · intro v hv h0
    by_cases hnv : v.val = var.val
    · have hveq : v = var := Solver.uscalar_eq_of_val hnv
      rw [hveq] at h0 ⊢
      cases hrc : reason with
      | none =>
        exfalso
        have hpos := (hdecision hrc).1
        rw [hlvlvar] at h0
        omega
      | some x =>
        exact ⟨x, Solver.reasonOf_set_some (by rw [hreason, hrc]) hlenr⟩
    · have hvmem := hold v hv hnv
      obtain ⟨r, hr⟩ := hwf.level_zero_has_reason v hvmem
        (by rw [← hlvlold v hvmem]; exact h0)
      exact ⟨r, by rw [hrsnold v hvmem]; exact hr⟩
  -- decision_of_level
  · intro u hu hpos
    by_cases hnv : u.val = var.val
    · have hveq : u = var := Solver.uscalar_eq_of_val hnv
      rw [hveq] at hpos ⊢
      cases hrc : reason with
      | none =>
        exact ⟨var, (hmem var).mpr (Or.inr rfl), rfl,
          Solver.reasonOf_set_none (by rw [hreason, hrc]) hlenr⟩
      | some x =>
        rw [hlvlvar] at hpos
        obtain ⟨w, hwmem, hwlvl, hwrsn⟩ := hopen x hrc hpos
        exact ⟨w, (hmem w).mpr (Or.inl hwmem),
          by rw [hlvlold w hwmem, hwlvl, hlvlvar],
          by rw [hrsnold w hwmem]; exact hwrsn⟩
    · have hvmem := hold u hu hnv
      rw [hlvlold u hvmem] at hpos
      obtain ⟨w, hwmem, hwlvl, hwrsn⟩ := hwf.decision_of_level u hvmem hpos
      exact ⟨w, (hmem w).mpr (Or.inl hwmem),
        by rw [hlvlold w hwmem, hwlvl, hlvlold u hvmem],
        by rw [hrsnold w hwmem]; exact hwrsn⟩
  -- trail_lim_spec
  · intro j hj
    have htlimv : s'.trail_lim.val = s.trail_lim.val := by rw [htlim]
    have hjlen : j < s.trail_lim.val.length := by rw [← htlimv]; exact hj
    have hlimel : s'.trail_lim.val[j] = s.trail_lim.val[j]'hjlen :=
      List.getElem_of_eq htlimv _
    rw [hlimel]
    obtain ⟨hb, hiff⟩ := hwf.trail_lim_spec j hjlen
    have hjdl : j < Solver.decisionLevel s := hjlen
    have hlen' : s'.trail.val.length = s.trail.val.length + 1 := by rw [htrail]; simp
    refine ⟨by rw [hlen']; omega, ?_⟩
    intro i hi
    rw [hlen'] at hi
    have hgi : s'.trail.val[i] = (s.trail.val ++ [var])[i]'(by rw [← htrail]; omega) :=
      List.getElem_of_eq htrail _
    rw [hgi]
    by_cases hin : i < s.trail.val.length
    · rw [List.getElem_append_left hin, hlvlold _ (List.getElem_mem hin)]
      exact hiff i hin
    · have hieq : i = s.trail.val.length := by omega
      subst hieq
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero, hlvlvar]
      constructor
      · intro h; omega
      · intro h; omega
  -- decision_first
  · intro u hu hpos hnone w hw hlvleq
    by_cases hnv : u.val = var.val
    · have hveq : u = var := Solver.uscalar_eq_of_val hnv
      rw [hveq] at hpos hnone hlvleq ⊢
      have hrc : reason = core.option.Option.None := by
        cases hrcc : reason with
        | none => rfl
        | some x =>
          exfalso
          rw [Solver.reasonOf_set_some (by rw [hreason, hrcc]) hlenr] at hnone
          simp at hnone
      obtain ⟨hdlpos, hbelow⟩ := hdecision hrc
      by_cases hwv : w.val = var.val
      · rw [Solver.uscalar_eq_of_val hwv]
      · exfalso
        have hwmem := hold w hw hwv
        rw [hlvlold w hwmem, hlvlvar] at hlvleq
        have := hbelow w hwmem
        omega
    · have humem := hold u hu hnv
      by_cases hwv : w.val = var.val
      · rw [Solver.uscalar_eq_of_val hwv, hidxvar, hidxold u humem]
        exact le_of_lt (List.idxOf_lt_length_of_mem humem)
      · have hwmem := hold w hw hwv
        rw [hidxold u humem, hidxold w hwmem]
        rw [hlvlold u humem] at hpos
        rw [hlvlold u humem, hlvlold w hwmem] at hlvleq
        exact hwf.decision_first u humem hpos (by rw [← hrsnold u humem]; exact hnone) w hwmem
          hlvleq

/-- **`assign` preserves the invariant.** The hypotheses on `reason` are the two ways
    the Rust calls it, and they are what `Solver.WF`'s `decision_first`,
    `decision_of_level` and `reason_wf` need:

    * a decision (`None`) is made at a level `search` has just opened by pushing
      `trail_lim`, so no trail entry sits at the current level yet -- that is what makes
      the new entry the earliest one at its level, i.e. `decision_first`;
    * a propagation (`Some r`) names a clause that has become unit on `var`, holding the
      literal this assignment makes true with every other literal already false. Since
      the trail only grows, "already false" is also "already earlier on the trail", which
      is `reason_wf`'s strict trail inequality and the acyclicity of the implication
      graph;
    * and a propagation at a level above 0 needs that level to have a decision already
      (`hopen`), since it does not open the level itself. That hypothesis was not in this
      statement when it was written: see `Solver.wf_assign`. -/
theorem sat_cdcl.Solver.assign.spec (s : sat_cdcl.Solver) (var : Std.U16) (value : Bool)
    (reason : core.option.Option Std.Usize)
    (hwf : Solver.WF s)
    (hslot : var.val < s.value.val.length)
    (hfresh : Solver.valueOf s var = none)
    (hdecision : reason = core.option.Option.None →
      0 < Solver.decisionLevel s ∧
      ∀ w ∈ s.trail.val, Solver.levelOf s w < Solver.decisionLevel s)
    (hopen : ∀ r, reason = core.option.Option.Some r → 0 < Solver.decisionLevel s →
      ∃ v ∈ s.trail.val, Solver.levelOf s v = Solver.decisionLevel s ∧
        Solver.reasonOf s v = none)
    (hunit : ∀ r, reason = core.option.Option.Some r →
      ∃ cl, Solver.clauseAt s r = some cl
        ∧ ({ var := var, negated := !value } : cnf.Literal) ∈ cl
        ∧ ∀ lit ∈ cl, lit ≠ ({ var := var, negated := !value } : cnf.Literal) →
            Solver.litFalse s lit) :
    sat_cdcl.Solver.assign s var value reason ⦃ (s' : sat_cdcl.Solver) =>
      Solver.WF s'
      ∧ Solver.db s' = Solver.db s
      ∧ Solver.decisionLevel s' = Solver.decisionLevel s
      ∧ s'.trail.val = s.trail.val ++ [var]
      ∧ Solver.valueOf s' var = some value
      ∧ Solver.levelOf s' var = Solver.decisionLevel s
      ∧ s'.value.val.length = s.value.val.length
      ∧ (∀ w, w ≠ var → Solver.valueOf s' w = Solver.valueOf s w
          ∧ Solver.levelOf s' w = Solver.levelOf s w
          ∧ Solver.reasonOf s' w = Solver.reasonOf s w)
      ∧ s'.occurs = s.occurs
      ∧ s'.conflicts = s.conflicts
      ∧ (reason = core.option.Option.None → Solver.reasonOf s' var = none)
      ∧ (∀ r, reason = core.option.Option.Some r → Solver.reasonOf s' var = some r) ⦄ := by
  unfold sat_cdcl.Solver.assign
  step*
  all_goals
    (have hiv : i.val = var.val := by rw [i_post]; simp)
    first
    | (rw [hiv, hwf.level_length]; exact hslot)
    | (rw [hiv, hwf.reason_length]; exact hslot)
    | (rw [hiv, hwf.phase_length]; exact hslot)
    | (have htl := Solver.trail_length_le hwf; scalar_tac)
    | (have hdlv : i1.val = Solver.decisionLevel s := by
         rw [i1_post]; simp [Solver.decisionLevel]
       have hv : (index_mut_back (core.option.Option.Some value)).val
           = s.value.val.set var.val (core.option.Option.Some value) := by
         rw [‹∀ y : core.option.Option Bool,
           (index_mut_back y).val = s.value.val.set i.val y› _, hiv]
       have hl : (index_mut_back1 i1).val = s.level.val.set var.val i1 := by
         rw [‹∀ y : Std.Usize,
           (index_mut_back1 y).val = s.level.val.set i.val y› _, hiv]
       have hr : (index_mut_back2 reason).val = s.reason.val.set var.val reason := by
         rw [‹∀ y : core.option.Option Std.Usize,
           (index_mut_back2 y).val = s.reason.val.set i.val y› _, hiv]
       have hp : (index_mut_back3 value).val = s.phase.val.set var.val value := by
         rw [‹∀ y : Bool,
           (index_mut_back3 y).val = s.phase.val.set i.val y› _, hiv]
       refine ⟨Solver.wf_assign hwf hslot hfresh hdecision hopen hunit hdlv hv hl hr hp
           v1_post rfl rfl rfl rfl rfl,
         by simp [Solver.db], rfl, v1_post, ?_, ?_, by rw [hv]; simp, ?_,
         fun hn => Solver.reasonOf_set_none (by rw [hr, hn]) (by rw [hwf.reason_length]; exact hslot),
         fun r hr' => Solver.reasonOf_set_some (by rw [hr, hr'])
           (by rw [hwf.reason_length]; exact hslot)⟩
       · rw [Solver.valueOf_set hv hslot var]; simp
       · rw [Solver.levelOf_set hl (by rw [hwf.level_length]; exact hslot) var, hdlv]
         simp
       · intro w hw
         have hne : ¬ (w.val = var.val) := fun hc => hw (Solver.uscalar_eq_of_val hc)
         refine ⟨?_, ?_, ?_⟩
         · rw [Solver.valueOf_set hv hslot w, if_neg hne]
         · rw [Solver.levelOf_set hl (by rw [hwf.level_length]; exact hslot) w, if_neg hne]
         · exact Solver.reasonOf_set_ne hr hne)

/-! #### What `backtrack` needs from the toolchain

`pop`, `truncate` and `unwrap` have no `@[step]` specs in Aeneas or `CoreModels`, and
`backtrack` is the first function here to call any of them. Like the `Clause` clone spec
above, they live in this file rather than in `Prelude.lean`: a new `@[step]` lemma changes
what `step*` does in every proof that can see it. The two `rust_primitives.sequence` ones
are the layer `pop`/`truncate` bottom out at. -/

/-- `unwrap` on something that is not `None`. Stated so that the value it returns is
    identified by the postcondition rather than passed in, which is what lets `step` apply
    it without guessing. -/
@[step]
theorem core.option.Option.unwrap.spec {T : Type} (o : core.option.Option T)
    (h : o ≠ core.option.Option.None) :
    core.option.Option.unwrap o ⦃ (y : T) => o = core.option.Option.Some y ⦄ := by
  unfold core.option.Option.unwrap
  cases o with
  | none => exact absurd rfl h
  | some x => simp

/-- The underlying sequence length. -/
@[step]
theorem rust_primitives.sequence.seq_len.spec {T : Type}
    (s : rust_primitives.sequence.Seq T) :
    rust_primitives.sequence.seq_len s ⦃ (l : Std.Usize) => l.val = s.val.length ⦄ := by
  unfold rust_primitives.sequence.seq_len
  simp [Slice.len]

/-- Removing one element: the rest is the list with that index cut out. -/
@[step]
theorem rust_primitives.sequence.seq_remove.spec {T : Type}
    (s : rust_primitives.sequence.Seq T) (i : Std.Usize) (h : i.val < s.val.length) :
    rust_primitives.sequence.seq_remove s i ⦃ (x : T)
      (rest : rust_primitives.sequence.Seq T) =>
      s.val[i.val]? = some x
      ∧ rest.val = s.val.take i.val ++ s.val.drop (i.val + 1) ⦄ := by
  unfold rust_primitives.sequence.seq_remove
  rw [dif_pos h]
  simp [List.get_eq_getElem, List.getElem?_eq_getElem h]

/-- Draining a range: only what is left over matters here. -/
@[step]
theorem rust_primitives.sequence.seq_drain.spec {T : Type}
    (s : rust_primitives.sequence.Seq T) (a b : Std.Usize)
    (h1 : a.val ≤ b.val) (h2 : b.val ≤ s.val.length) :
    rust_primitives.sequence.seq_drain s a b ⦃ (_drained : rust_primitives.sequence.Seq T)
      (rest : rust_primitives.sequence.Seq T) =>
      rest.val = s.val.take a.val ++ s.val.drop b.val ⦄ := by
  unfold rust_primitives.sequence.seq_drain
  rw [dif_pos ⟨h1, by simpa [Slice.length] using h2⟩]
  simp

/-- **`Vec::pop`.** The `self.val = [] → o = None` clause is not decoration: it is what
    lets `backtrack_loop`'s proof conclude the trail is non-empty from the fact that the
    pop produced a variable, which is in turn what makes the loop's measure decrease.
    Deriving it from the loop's `i > target` test instead is not available -- that
    hypothesis is inaccessible in the `decreasing_by` goal. -/
@[step]
theorem alloc.vec.Vec.pop.spec {T : Type} (self : alloc.vec.Vec T) :
    alloc.vec.Vec.pop self ⦃ (o : core.option.Option T) (rest : alloc.vec.Vec T) =>
      rest.val = self.val.dropLast
      ∧ (self.val ≠ [] → o ≠ core.option.Option.None)
      ∧ (self.val = [] → o = core.option.Option.None)
      ∧ (∀ x l, self.val = l ++ [x] → o = core.option.Option.Some x) ⦄ := by
  unfold alloc.vec.Vec.pop
  step*
  · -- the pop removes the last slot, which is where `dropLast` and `getLast` meet
    have hi : i.val = self.val.length - 1 := by omega
    refine ⟨?_, by simp, ?_, ?_⟩
    · rw [last_post2, hi, List.drop_eq_nil_of_le (by omega)]
      simp [List.dropLast_eq_take]
    · intro hc
      rw [hc] at l_post
      simp at l_post
      exact absurd l_post (by scalar_tac)
    · intro x l' hsplit
      have hi' : i.val = l'.length := by
        rw [hsplit] at l_post
        simp at l_post
        omega
      have hx : self.val[i.val]? = some x := by
        rw [hsplit, hi', List.getElem?_append_right (Nat.le_refl _)]
        simp
      rw [last_post1] at hx
      rw [Option.some.inj hx]
  · -- the empty case
    have hnil : self.val = [] := by
      have hz : self.val.length = 0 := by scalar_tac
      exact List.eq_nil_of_length_eq_zero hz
    simp [hnil]

/-- **`Vec::truncate`**, which is `take` for either ordering of `n` and the length. -/
@[step]
theorem alloc.vec.Vec.truncate.spec {T : Type} (self : alloc.vec.Vec T) (n : Std.Usize) :
    alloc.vec.Vec.truncate self n ⦃ (v : alloc.vec.Vec T) =>
      v.val = self.val.take n.val ⦄ := by
  unfold alloc.vec.Vec.truncate
  step*
  · have hd : List.drop l.val self.val = [] := List.drop_eq_nil_of_le (by omega)
    simp_all
  · exact (List.take_of_length_le (by scalar_tac)).symm

/-- **`backtrack`'s pop-and-clear loop.** It pops the trail down to `target`, clearing
    `value` and `reason` for every variable it pops, and leaves both arrays alone
    elsewhere. Stated over `take`/`drop` of the trail rather than over a fold: the caller
    reasons about levels, and `trail_lim_spec` turns a level bound into exactly this
    split.

    No `Nodup` hypothesis is needed even though a variable could in principle appear in
    both halves: if it does, the recursion clears it on the later occurrence anyway. -/
@[step]
theorem sat_cdcl.Solver.backtrack_loop.spec (v : alloc.vec.Vec (core.option.Option Bool))
    (v1 : alloc.vec.Vec (core.option.Option Std.Usize)) (v2 : alloc.vec.Vec Std.U16)
    (target : Std.Usize)
    (hbound : ∀ w ∈ v2.val, w.val < v.val.length ∧ w.val < v1.val.length) :
    sat_cdcl.Solver.backtrack_loop v v1 v2 target ⦃
      (v' : alloc.vec.Vec (core.option.Option Bool))
      (v1' : alloc.vec.Vec (core.option.Option Std.Usize))
      (v2' : alloc.vec.Vec Std.U16) =>
        v2'.val = v2.val.take target.val
        ∧ v'.val.length = v.val.length
        ∧ v1'.val.length = v1.val.length
        ∧ (∀ w : Std.U16, w ∈ v2.val.drop target.val →
            v'.val[w.val]? = some core.option.Option.None
            ∧ v1'.val[w.val]? = some core.option.Option.None)
        ∧ (∀ w : Std.U16, w ∉ v2.val.drop target.val →
            v'.val[w.val]? = v.val[w.val]? ∧ v1'.val[w.val]? = v1.val[w.val]?) ⦄ := by
  unfold sat_cdcl.Solver.backtrack_loop
  step*
  all_goals
    first
    | -- The loop is done: `target` is at or past the end, so nothing was popped.
      (have hbr : ¬ (i > target) := ‹¬ (i > target)›
       have hle : v2.val.length ≤ target.val := by scalar_tac
       refine ⟨(List.take_of_length_le hle).symm, ?_, fun w _ => trivial⟩
       intro w hw
       rw [List.drop_eq_nil_of_le hle] at hw
       simp at hw)
    | (have hbr : i > target := ‹i > target›
       have hgt : target.val < i.val := by scalar_tac
       have hne : v2.val ≠ [] := by
         intro hc
         have h := o_post3 hc
         rw [i1_post] at h
         simp at h
       obtain ⟨l, x, hsplit⟩ : ∃ l x, v2.val = l ++ [x] := by
         rcases List.eq_nil_or_concat v2.val with h | h
         · exact absurd h hne
         · obtain ⟨l', b, hb⟩ := h
           exact ⟨l', b, by rw [hb, List.concat_eq_append]⟩
       have hxmem : x ∈ v2.val := by rw [hsplit]; simp
       first
       | exact o_post2 hne
       | (have hix : i1 = x := by
            have h := o_post4 x l hsplit
            rw [i1_post] at h
            injection h
          have hv4 : v4.val = x.val := by rw [v4_post, hix]; simp
          rw [hv4]
          exact (hbound x hxmem).1)
       | (have hix : i1 = x := by
            have h := o_post4 x l hsplit
            rw [i1_post] at h
            injection h
          have hv4 : v4.val = x.val := by rw [v4_post, hix]; simp
          rw [hv4]
          exact (hbound x hxmem).2)
       | (intro w hw
          rw [o_post1] at hw
          have hwm : w ∈ v2.val := List.dropLast_subset _ hw
          rw [‹∀ y : core.option.Option Bool,
              (index_mut_back y).val = v.val.set v4.val y› _,
            ‹∀ y : core.option.Option Std.Usize,
              (index_mut_back1 y).val = v1.val.set v4.val y› _]
          simpa using hbound w hwm)
       | (have hix : i1 = x := by
            have h := o_post4 x l hsplit
            rw [i1_post] at h
            injection h
          have hv4 : v4.val = x.val := by rw [v4_post, hix]; simp
          have hsetv : (index_mut_back core.option.Option.None).val
              = v.val.set x.val core.option.Option.None := by
            rw [‹∀ y : core.option.Option Bool,
              (index_mut_back y).val = v.val.set v4.val y› _, hv4]
          have hsetv1 : (index_mut_back1 core.option.Option.None).val
              = v1.val.set x.val core.option.Option.None := by
            rw [‹∀ y : core.option.Option Std.Usize,
              (index_mut_back1 y).val = v1.val.set v4.val y› _, hv4]
          have hl3 : v3.val = l := by rw [o_post1, hsplit]; simp
          have hlen : target.val ≤ l.length := by
            rw [hsplit] at i_post
            simp at i_post
            omega
          have hxv : x.val < v.val.length := (hbound x hxmem).1
          have hxv1 : x.val < v1.val.length := (hbound x hxmem).2
          have hdrop : v2.val.drop target.val = l.drop target.val ++ [x] := by
            rw [hsplit, List.drop_append_of_le_length hlen]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [v'_post1, hl3, hsplit, List.take_append_of_le_length hlen]
          · rw [v'_post2, hsetv]; simp
          · rw [v'_post3, hsetv1]; simp
          · intro w hw
            rw [hdrop] at hw
            rcases List.mem_append.mp hw with hw' | hw'
            · exact v'_post4 w (by rw [hl3]; exact hw')
            · -- the variable just popped: cleared by the two writes, unless the
              -- recursion cleared it again on an earlier occurrence
              simp only [List.mem_singleton] at hw'
              subst hw'
              by_cases hin : w ∈ l.drop target.val
              · exact v'_post4 w (by rw [hl3]; exact hin)
              · obtain ⟨h1, h2⟩ := v'_post5 w (by rw [hl3]; exact hin)
                rw [h1, h2, hsetv, hsetv1, List.getElem?_set_self hxv,
                  List.getElem?_set_self hxv1]
                exact ⟨rfl, rfl⟩
          · intro w hw
            rw [hdrop] at hw
            have hwl : w ∉ l.drop target.val := fun hc => hw (List.mem_append_left _ hc)
            have hwx : w.val ≠ x.val := by
              intro hc
              exact hw (List.mem_append_right _ (by simp [Solver.uscalar_eq_of_val hc]))
            obtain ⟨h1, h2⟩ := v'_post5 w (by rw [hl3]; exact hwl)
            rw [h1, h2, hsetv, hsetv1, List.getElem?_set_ne (Ne.symm hwx),
              List.getElem?_set_ne (Ne.symm hwx)]
            exact ⟨rfl, rfl⟩))
termination_by v2.val.length
decreasing_by
  all_goals
    (have hne : v2.val ≠ [] := by
       intro hc
       have h := o_post3 hc
       rw [i1_post] at h
       simp at h
     have hpos : 0 < v2.val.length := List.length_pos_of_ne_nil hne
     rw [o_post1, List.length_dropLast]
     omega)

/-- **The entries `backtrack level` keeps are exactly those at levels `≤ level`.** This
    is `trail_lim_spec` read through `idxOf` rather than through a raw index, and it is
    what every clause of `backtrack`'s postcondition comes down to. -/
theorem Solver.mem_take_iff_level_le {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    {level tgt : Std.Usize} (hlt : level.val < s.trail_lim.val.length)
    (htgt : s.trail_lim.val[level.val] = tgt) {v : Std.U16} (hv : v ∈ s.trail.val) :
    Solver.levelOf s v ≤ level.val ↔ v ∈ s.trail.val.take tgt.val := by
  have hidx : s.trail.val.idxOf v < s.trail.val.length :=
    List.idxOf_lt_length_of_mem hv
  have hget : s.trail.val[s.trail.val.idxOf v] = v := List.getElem_idxOf hidx
  obtain ⟨-, hiff⟩ := hwf.trail_lim_spec level.val hlt
  rw [htgt] at hiff
  have hiff' := hiff _ hidx
  rw [hget] at hiff'
  constructor
  · intro hle
    exact Solver.mem_take_of_idxOf hv (hiff'.mpr hle)
  · intro hmem
    exact hiff'.mp (Solver.idxOf_lt_of_mem_take hwf.trail_nodup hmem)

/-- **`backtrack`'s half of the invariant.** The one argument that does real work is
    `reason_wf`: a kept variable's antecedents sit *earlier* on the trail than it does, so
    they are inside the kept prefix too, and the clause that forced it is still falsified
    the way `reason_wf` requires. `trail_nodup` is what makes "kept" and "cleared"
    exclusive, and `reason_assigned` is what rules out a variable off the trail holding a
    stale reason into the popped region. -/
theorem Solver.wf_backtrack {s s' : sat_cdcl.Solver} {level tgt : Std.Usize}
    (hwf : Solver.WF s)
    (hlt : level.val < s.trail_lim.val.length)
    (htgt : s.trail_lim.val[level.val] = tgt)
    (hvclear : ∀ w : Std.U16, w ∈ s.trail.val.drop tgt.val →
      s'.value.val[w.val]? = some core.option.Option.None
      ∧ s'.reason.val[w.val]? = some core.option.Option.None)
    (hvkeep : ∀ w : Std.U16, w ∉ s.trail.val.drop tgt.val →
      s'.value.val[w.val]? = s.value.val[w.val]?
      ∧ s'.reason.val[w.val]? = s.reason.val[w.val]?)
    (hvlen : s'.value.val.length = s.value.val.length)
    (hrlen : s'.reason.val.length = s.reason.val.length)
    (htrail : s'.trail.val = s.trail.val.take tgt.val)
    (htlim : s'.trail_lim.val = s.trail_lim.val.take level.val)
    (hlevelarr : s'.level = s.level)
    (hseen : s'.seen = s.seen) (hphase : s'.phase = s.phase)
    (hactivity : s'.activity = s.activity) (hclauses : s'.clauses = s.clauses)
    (hoccurs : s'.occurs = s.occurs) :
    Solver.WF s' := by
  have hlvl : ∀ w : Std.U16, Solver.levelOf s' w = Solver.levelOf s w := by
    intro w; simp [Solver.levelOf, hlevelarr]
  have htgtle : tgt.val ≤ s.trail.val.length := by
    have := (hwf.trail_lim_spec level.val hlt).1
    rwa [htgt] at this
  have hkept : ∀ {v : Std.U16}, v ∈ s.trail.val →
      (Solver.levelOf s v ≤ level.val ↔ v ∈ s.trail.val.take tgt.val) :=
    fun hv => Solver.mem_take_iff_level_le hwf hlt htgt hv
  have hdisj : ∀ w : Std.U16, w ∈ s.trail.val.take tgt.val →
      w ∉ s.trail.val.drop tgt.val :=
    fun w hw => List.disjoint_take_drop hwf.trail_nodup (Nat.le_refl _) hw
  have hsub : ∀ w : Std.U16, w ∈ s'.trail.val → w ∈ s.trail.val := by
    intro w hw; rw [htrail] at hw; exact List.mem_of_mem_take hw
  have hvalkeep : ∀ w : Std.U16, w ∈ s.trail.val.take tgt.val →
      Solver.valueOf s' w = Solver.valueOf s w := by
    intro w hw
    simp only [Solver.valueOf, (hvkeep w (hdisj w hw)).1]
  have hrsnkeep : ∀ w : Std.U16, w ∈ s.trail.val.take tgt.val →
      Solver.reasonOf s' w = Solver.reasonOf s w := by
    intro w hw
    simp only [Solver.reasonOf, (hvkeep w (hdisj w hw)).2]
  have hvalclear : ∀ w : Std.U16, w ∈ s.trail.val.drop tgt.val →
      Solver.valueOf s' w = none := by
    intro w hw
    simp [Solver.valueOf, (hvclear w hw).1]
  have hrsnclear : ∀ w : Std.U16, w ∈ s.trail.val.drop tgt.val →
      Solver.reasonOf s' w = none := by
    intro w hw
    simp [Solver.reasonOf, (hvclear w hw).2]
  have hvalout : ∀ w : Std.U16, w ∉ s.trail.val → Solver.valueOf s' w = Solver.valueOf s w := by
    intro w hw
    have : w ∉ s.trail.val.drop tgt.val := fun hc => hw (List.mem_of_mem_drop hc)
    simp only [Solver.valueOf, (hvkeep w this).1]
  have hdl : Solver.decisionLevel s' = level.val := by
    simp only [Solver.decisionLevel, htlim, List.length_take]
    omega
  have hidx : ∀ w : Std.U16, w ∈ s.trail.val.take tgt.val →
      s'.trail.val.idxOf w = s.trail.val.idxOf w := by
    intro w hw
    rw [htrail]
    conv_rhs => rw [← List.take_append_drop tgt.val s.trail.val]
    exact (List.idxOf_append_of_mem hw).symm
  refine
    { level_length := by rw [hlevelarr, hvlen]; exact hwf.level_length
      reason_length := by rw [hrlen, hvlen]; exact hwf.reason_length
      seen_length := by rw [hseen, hvlen]; exact hwf.seen_length
      activity_length := by rw [hactivity, hvlen]; exact hwf.activity_length
      phase_length := by rw [hphase, hvlen]; exact hwf.phase_length
      occurs_length := by rw [hoccurs, hvlen]; exact hwf.occurs_length
      db_len := by rw [Solver.db, hclauses]; exact hwf.db_len
      db_vars := by rw [Solver.db, hclauses, hvlen]; exact hwf.db_vars
      trail_bound := ?_
      trail_iff := ?_
      trail_nodup := by rw [htrail]; exact Solver.take_nodup hwf _
      seen_clear := by rw [hseen]; exact hwf.seen_clear
      level_le := ?_
      level_mono := ?_
      reason_wf := ?_
      reason_assigned := ?_
      level_zero_has_reason := ?_
      decision_of_level := ?_
      trail_lim_spec := ?_
      decision_first := ?_ }
  -- trail_bound
  · intro w hw
    rw [hvlen]
    exact hwf.trail_bound w (hsub w hw)
  -- trail_iff
  · intro w
    rw [htrail]
    by_cases hin : w ∈ s.trail.val.take tgt.val
    · rw [hvalkeep w hin, hwf.trail_iff]
      exact ⟨fun _ => hin, fun _ => List.mem_of_mem_take hin⟩
    · constructor
      · intro hsome
        exfalso
        by_cases hmem : w ∈ s.trail.val
        · have hdr : w ∈ s.trail.val.drop tgt.val := by
            rcases List.mem_append.mp
              (by rwa [List.take_append_drop tgt.val s.trail.val]) with h | h
            · exact absurd h hin
            · exact h
          rw [hvalclear w hdr] at hsome
          simp at hsome
        · rw [hvalout w hmem] at hsome
          exact hmem ((hwf.trail_iff w).mp hsome)
      · intro hmem
        exact absurd hmem hin
  -- level_le
  · intro w hw
    rw [hlvl w, hdl]
    rw [htrail] at hw
    exact (hkept (List.mem_of_mem_take hw)).mpr hw
  -- level_mono
  · intro i j hi hj hij
    have hi' : i < (s.trail.val.take tgt.val).length := by rw [← htrail]; exact hi
    have hj' : j < (s.trail.val.take tgt.val).length := by rw [← htrail]; exact hj
    have hgi : s'.trail.val[i] = (s.trail.val.take tgt.val)[i]'hi' :=
      List.getElem_of_eq htrail _
    have hgj : s'.trail.val[j] = (s.trail.val.take tgt.val)[j]'hj' :=
      List.getElem_of_eq htrail _
    rw [hgi, hgj]
    simp only [List.getElem_take, hlvl]
    exact hwf.level_mono i j _ _ hij
  -- reason_wf
  · intro v r hr
    have hvin : v ∈ s.trail.val.take tgt.val := by
      by_contra hc
      by_cases hmem : v ∈ s.trail.val
      · have hdr : v ∈ s.trail.val.drop tgt.val := by
          rcases List.mem_append.mp
            (by rwa [List.take_append_drop tgt.val s.trail.val]) with h | h
          · exact absurd h hc
          · exact h
        rw [hrsnclear v hdr] at hr
        simp at hr
      · -- a variable off the trail has no reason at all (`reason_assigned`)
        have heq : Solver.reasonOf s' v = Solver.reasonOf s v := by
          simp only [Solver.reasonOf,
            (hvkeep v (fun hd => hmem (List.mem_of_mem_drop hd))).2]
        rw [heq] at hr
        exact hmem (hwf.reason_assigned v (by rw [hr]; simp))
    obtain ⟨cl, hcl, hmemlit, hrest⟩ := hwf.reason_wf v r (by rwa [hrsnkeep v hvin] at hr)
    refine ⟨cl, by simpa only [Solver.clauseAt, Solver.db, hclauses] using hcl, ?_, ?_⟩
    · have : Solver.trueLit s' v = Solver.trueLit s v := by
        simp [Solver.trueLit, hvalkeep v hvin]
      rw [this]; exact hmemlit
    · intro lit hlit hne
      have htl : Solver.trueLit s' v = Solver.trueLit s v := by
        simp [Solver.trueLit, hvalkeep v hvin]
      rw [htl] at hne
      obtain ⟨hlf, hidxlt, hlvlle⟩ := hrest lit hlit hne
      -- the antecedent sits earlier on the trail than `v`, hence inside the prefix
      have hlmem : lit.var ∈ s.trail.val := Solver.mem_trail_of_litFalse hwf hlf
      have hlin : lit.var ∈ s.trail.val.take tgt.val := by
        refine Solver.mem_take_of_idxOf hlmem (lt_of_lt_of_le hidxlt ?_)
        exact le_of_lt (Solver.idxOf_lt_of_mem_take hwf.trail_nodup hvin)
      refine ⟨?_, ?_, ?_⟩
      · show Solver.valueOf s' lit.var = some lit.negated
        rw [hvalkeep lit.var hlin]; exact hlf
      · rw [hidx lit.var hlin, hidx v hvin]; exact hidxlt
      · rw [hlvl, hlvl]; exact hlvlle
  -- reason_assigned
  · intro v hr
    rw [htrail]
    by_cases hmem : v ∈ s.trail.val
    · by_cases hin : v ∈ s.trail.val.take tgt.val
      · exact hin
      · exfalso
        have hdr : v ∈ s.trail.val.drop tgt.val := by
          rcases List.mem_append.mp
            (by rwa [List.take_append_drop tgt.val s.trail.val]) with h | h
          · exact absurd h hin
          · exact h
        rw [hrsnclear v hdr] at hr
        exact hr rfl
    · exfalso
      have heq : Solver.reasonOf s' v = Solver.reasonOf s v := by
        simp only [Solver.reasonOf,
          (hvkeep v (fun hd => hmem (List.mem_of_mem_drop hd))).2]
      rw [heq] at hr
      exact hmem (hwf.reason_assigned v hr)
  -- level_zero_has_reason
  · intro v hv h0
    rw [htrail] at hv
    rw [hlvl v] at h0
    obtain ⟨r, hr⟩ := hwf.level_zero_has_reason v (List.mem_of_mem_take hv) h0
    exact ⟨r, by rw [hrsnkeep v hv]; exact hr⟩
  -- decision_of_level
  · intro u hu hpos
    rw [htrail] at hu
    rw [hlvl u] at hpos
    obtain ⟨w, hwmem, hwlvl, hwrsn⟩ :=
      hwf.decision_of_level u (List.mem_of_mem_take hu) hpos
    have hwin : w ∈ s.trail.val.take tgt.val := by
      refine (hkept hwmem).mp ?_
      rw [hwlvl]
      exact (hkept (List.mem_of_mem_take hu)).mpr hu
    refine ⟨w, by rw [htrail]; exact hwin, ?_, ?_⟩
    · rw [hlvl, hlvl]; exact hwlvl
    · rw [hrsnkeep w hwin]; exact hwrsn
  -- trail_lim_spec
  · intro j hj
    have hjtake : j < (s.trail_lim.val.take level.val).length := by rw [← htlim]; exact hj
    simp only [List.length_take] at hjtake
    have hjlt : j < s.trail_lim.val.length := by omega
    have hjlevel : j < level.val := by omega
    have hlimel : s'.trail_lim.val[j] = s.trail_lim.val[j]'hjlt := by
      rw [List.getElem_of_eq htlim]
      exact List.getElem_take ..
    obtain ⟨hb, hiff⟩ := hwf.trail_lim_spec j hjlt
    -- earlier levels start earlier on the trail: otherwise the entry at `tgt` would
    -- have to sit at a level both `≤ j` and above `level`
    have hle : (s.trail_lim.val[j]'hjlt).val ≤ tgt.val := by
      by_contra hc
      push Not at hc
      have htlt : tgt.val < s.trail.val.length := by omega
      obtain ⟨-, hiff'⟩ := hwf.trail_lim_spec level.val hlt
      rw [htgt] at hiff'
      have h1 : Solver.levelOf s s.trail.val[tgt.val] ≤ j := (hiff tgt.val htlt).mp hc
      have h2 : ¬ (Solver.levelOf s s.trail.val[tgt.val] ≤ level.val) := by
        intro hcon
        have := (hiff' tgt.val htlt).mpr hcon
        omega
      omega
    have htrlen : s'.trail.val.length = tgt.val := by
      rw [htrail]
      simp only [List.length_take]
      omega
    refine ⟨?_, ?_⟩
    · rw [hlimel, htrlen]
      exact hle
    · intro i hi
      rw [htrlen] at hi
      have hitl : i < s.trail.val.length := by omega
      have hgi : s'.trail.val[i] = s.trail.val[i]'hitl := by
        rw [List.getElem_of_eq htrail]
        exact List.getElem_take ..
      rw [hlimel, hgi, hlvl]
      exact hiff i hitl
  -- decision_first
  · intro u hu hpos hnone w hw hlvleq
    rw [htrail] at hu hw
    rw [hidx u hu, hidx w hw]
    rw [hlvl u] at hpos
    rw [hlvl u, hlvl w] at hlvleq
    exact hwf.decision_first u (List.mem_of_mem_take hu) hpos
      (by rwa [hrsnkeep u hu] at hnone) w (List.mem_of_mem_take hw) hlvleq

/-- **`backtrack` preserves the invariant.** It restores a prefix of the trail: every
    assignment at a level above `level` is undone, everything at or below it is kept, and
    the clauses (learned ones included) and saved phases stay. Note what it does *not*
    clear -- `level` and `phase` keep their entries for now-unassigned variables, which is
    why `Solver.WF` reads `levelOf` only for variables on the trail.

    The last two conjuncts are what `search`'s termination measure reads: *which* prefix
    (`trail_lim[level]`'s, spelled without a dependent index by quantifying over the entry),
    and that the entries it kept kept their reasons, since the measure's digit for an entry
    is whether it has one. -/
theorem sat_cdcl.Solver.backtrack.spec (s : sat_cdcl.Solver) (level : Std.Usize)
    (hwf : Solver.WF s) :
    sat_cdcl.Solver.backtrack s level ⦃ (s' : sat_cdcl.Solver) =>
      Solver.WF s'
      ∧ Solver.db s' = Solver.db s
      ∧ s'.clauses = s.clauses
      ∧ s'.problem_clauses = s.problem_clauses
      ∧ s'.value.val.length = s.value.val.length
      ∧ s'.occurs = s.occurs
      ∧ Solver.decisionLevel s' = min level.val (Solver.decisionLevel s)
      ∧ (∀ v ∈ s.trail.val, Solver.levelOf s v ≤ level.val →
          Solver.valueOf s' v = Solver.valueOf s v
            ∧ Solver.levelOf s' v = Solver.levelOf s v)
      ∧ (∀ v ∈ s.trail.val, level.val < Solver.levelOf s v →
          Solver.valueOf s' v = none)
      ∧ s'.conflicts = s.conflicts
      ∧ (∀ tgt, s.trail_lim.val[level.val]? = some tgt →
          s'.trail.val = s.trail.val.take tgt.val)
      ∧ (∀ v ∈ s'.trail.val, Solver.reasonOf s' v = Solver.reasonOf s v) ⦄ := by
  unfold sat_cdcl.Solver.backtrack
  step*
  -- Nothing to undo: the decision level is already at or below `level`.
  · have hle : Solver.decisionLevel s ≤ level.val := by
      have hbr : i ≤ level := ‹i ≤ level›
      scalar_tac
    refine ⟨hwf, by omega, fun v _ _ => trivial, ?_, ?_, fun v _ => trivial⟩
    · intro v hv hgt
      exact absurd (hwf.level_le v hv) (by omega)
    · -- `level` is at or above the top, so `trail_lim` has no entry for it
      intro tgt htgt
      rw [List.getElem?_eq_none (by simp only [Solver.decisionLevel] at hle; omega)] at htgt
      exact absurd htgt (by simp)
  -- `level` is a live decision level, so `trail_lim` has an entry for it.
  · have hbr : ¬ (i ≤ level) := ‹¬ (i ≤ level)›
    have : level.val < Solver.decisionLevel s := by scalar_tac
    simpa [Solver.decisionLevel] using this
  -- Every trail entry has a `value` and a `reason` slot.
  · intro w hw
    exact ⟨hwf.trail_bound w hw, by rw [hwf.reason_length]; exact hwf.trail_bound w hw⟩
  -- The real case: pop down to `trail_lim[level]`, then truncate.
  · have hbr : ¬ (i ≤ level) := ‹¬ (i ≤ level)›
    have hlt : level.val < s.trail_lim.val.length := by
      have : level.val < Solver.decisionLevel s := by scalar_tac
      simpa [Solver.decisionLevel] using this
    have htgt : s.trail_lim.val[level.val]'hlt = target :=
      Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans target_post)
    have hkept : ∀ {w : Std.U16}, w ∈ s.trail.val →
        (Solver.levelOf s w ≤ level.val ↔ w ∈ s.trail.val.take target.val) :=
      fun hw => Solver.mem_take_iff_level_le hwf hlt htgt hw
    have hdisj : ∀ w : Std.U16, w ∈ s.trail.val.take target.val →
        w ∉ s.trail.val.drop target.val :=
      fun w hw => List.disjoint_take_drop hwf.trail_nodup (Nat.le_refl _) hw
    have htgtle : target.val ≤ s.trail.val.length := by
      have h := (hwf.trail_lim_spec level.val hlt).1
      rw [htgt] at h
      exact h
    refine ⟨Solver.wf_backtrack hwf hlt htgt v_post4 v_post5 v_post2 v_post3 v_post1
        (by simpa using v3_post) rfl rfl rfl rfl rfl rfl, by simp [Solver.db],
      by simpa using v_post2, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Solver.decisionLevel, v3_post, List.length_take]
      try omega
    · intro w hw hle
      have hin : w ∈ s.trail.val.take target.val := (hkept hw).mp hle
      refine ⟨?_, rfl⟩
      simp only [Solver.valueOf, (v_post5 w (hdisj w hin)).1]
    · intro w hw hgt
      have hnotin : w ∉ s.trail.val.take target.val := fun hc =>
        absurd ((hkept hw).mpr hc) (by omega)
      have hdr : w ∈ s.trail.val.drop target.val := by
        rcases List.mem_append.mp
          (by rwa [List.take_append_drop target.val s.trail.val]) with h | h
        · exact absurd h hnotin
        · exact h
      simp [Solver.valueOf, (v_post4 w hdr).1]
    -- the trail it leaves is the prefix `trail_lim[level]` names
    · intro tgt htgt
      rw [Option.some.inj (htgt.symm.trans target_post)]
      exact v_post1
    -- and the entries it kept kept their reasons
    · intro w hw
      have hw' : w ∈ s.trail.val.take target.val := by rw [← v_post1]; exact hw
      simp only [Solver.reasonOf, (v_post5 w (hdisj w hw')).2]

/-! #### `propagate`

Four specs the nine statements did not mention, because `propagate` is the first function
here that calls them: `lit_value`, `status` (the per-clause scan), `Option::is_some`, and
`propagate`'s own loop. -/

/-- **`lit_value`**: the literal's value under the assignment, as the three cases the
    scan distinguishes. -/
@[step]
theorem sat_cdcl.Solver.lit_value.spec (s : sat_cdcl.Solver) (lit : cnf.Literal)
    (hlt : lit.var.val < s.value.val.length) :
    sat_cdcl.Solver.lit_value s lit ⦃ (o : core.option.Option Bool) =>
      (o = core.option.Option.None ↔ Solver.valueOf s lit.var = none)
      ∧ (o = core.option.Option.Some false ↔ Solver.litFalse s lit)
      ∧ (o = core.option.Option.Some true ↔ Solver.litTrue s lit) ⦄ := by
  unfold sat_cdcl.Solver.lit_value
  step*
  all_goals
    (have hiv : i.val = lit.var.val := by rw [i_post]; simp
     rw [hiv] at o_post
     first
     | (have hval : Solver.valueOf s lit.var = none := by
          simp [Solver.valueOf, o_post, ‹o = core.option.Option.None›]
        simp [Solver.litFalse, Solver.litTrue, hval])
     | (have hval : Solver.valueOf s lit.var = some b := by
          simp [Solver.valueOf, o_post, ‹o = core.option.Option.Some b›]
        simp only [Solver.litFalse, Solver.litTrue, hval]
        cases b <;> cases lit.negated <;> simp))

/-- `Option::is_some`, which the scan uses to tell a first unassigned literal from a
    second. -/
@[step]
theorem core.option.Option.is_some.spec {T : Type} (o : core.option.Option T) :
    core.option.Option.is_some o ⦃ (b : Bool) =>
      b = true ↔ o ≠ core.option.Option.None ⦄ := by
  unfold core.option.Option.is_some
  match o with
  | core.option.Option.None => simp
  | core.option.Option.Some x => simp

/-- The literal the scan is looking at really is a literal of the clause it indexed.
    Every branch of `status`'s loop needs this, so it is factored out. -/
theorem Solver.scan_position {s : sat_cdcl.Solver} {c : cnf.Clause} {cl : List cnf.Literal}
    {clause j : Std.Usize} {lit : cnf.Literal}
    (hcl : Solver.clauseAt s clause = some cl)
    (hc : s.clauses.val[clause.val]? = some c)
    (hlit : c.val[j.val]? = some lit) (hjlt : j.val < cl.length) :
    cl[j.val] = lit ∧ lit ∈ cl := by
  obtain ⟨c0, hcget, hc0⟩ := Solver.clauseAt_eq hcl
  have hcc : c0 = c := Option.some.inj (hcget.symm.trans hc)
  have hcl' : c.val = cl := by rw [← hcc]; exact hc0
  rw [hcl'] at hlit
  have h := (List.getElem?_eq_some_iff.mp hlit).2
  exact ⟨h, by rw [← h]; exact List.getElem_mem hjlt⟩

/-- **`status`'s scan of one clause.** `unassigned` holds the single unassigned literal
    found so far; `hbefore` is the invariant that every earlier position is either false
    or *is* that literal. The three cases of the answer are then what `propagate` needs:
    `Conflict` means every literal is false, `Unit lit` means `lit` is the only unassigned
    one and all the others are false, and `Silent` means at least one literal is not false
    -- which is all the fixpoint argument uses. -/
@[step]
theorem sat_cdcl.Solver.status_loop.spec (s : sat_cdcl.Solver)
    (iter : core.ops.range.Range Std.Usize) (clause : Std.Usize)
    (unassigned : core.option.Option cnf.Literal) (cl : List cnf.Literal)
    (hcl : Solver.clauseAt s clause = some cl)
    (hend : iter.«end».val = cl.length)
    (hstart : iter.start.val ≤ cl.length)
    (hbound : ∀ lit ∈ cl, lit.var.val < s.value.val.length)
    (hunass : ∀ lit, unassigned = core.option.Option.Some lit →
      lit ∈ cl ∧ Solver.valueOf s lit.var = none)
    (hbefore : ∀ (k : Nat), k < iter.start.val → ∀ (hk2 : k < cl.length),
      Solver.litFalse s cl[k] ∨ unassigned = core.option.Option.Some cl[k]) :
    sat_cdcl.Solver.status_loop iter s.clauses s.problem_clauses s.value s.level
      s.reason s.phase s.activity s.occurs s.seen s.trail s.trail_lim s.conflicts
      clause unassigned ⦃ (st : sat_cdcl.Status) =>
        (st = sat_cdcl.Status.Conflict → ∀ lit ∈ cl, Solver.litFalse s lit)
        ∧ (∀ lit, st = sat_cdcl.Status.Unit lit →
            lit ∈ cl ∧ Solver.valueOf s lit.var = none
            ∧ ∀ l ∈ cl, l ≠ lit → Solver.litFalse s l)
        ∧ (st = sat_cdcl.Status.Silent → ∃ lit ∈ cl, ¬ Solver.litFalse s lit) ⦄ := by
  unfold sat_cdcl.Solver.status_loop
  obtain ⟨c0, hcget, hc0⟩ := Solver.clauseAt_eq hcl
  have hclause_lt : clause.val < s.clauses.val.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hcget
    exact h
  step*
  -- the scan ran off the end with nothing unassigned: every literal is false
  · rename_i hun
    refine ⟨fun _ l hl => ?_, by simp, by simp⟩
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hl
    obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
    have hstart_ge : cl.length ≤ iter.start.val := by
      have := (o_post3 (by assumption)).1
      omega
    rcases hbefore k (by omega) hklt with h | h
    · rwa [hkeq] at h
    · rw [hun] at h
      simp at h
  -- the scan ran off the end with exactly one literal unassigned: a unit clause
  · rename_i lit hun
    refine ⟨by simp, ?_, by simp⟩
    intro l hst
    have hleq : l = lit := by injection hst.symm
    subst hleq
    obtain ⟨hmem, hnone⟩ := hunass l hun
    have hstart_ge : cl.length ≤ iter.start.val := by
      have := (o_post3 (by assumption)).1
      omega
    refine ⟨hmem, hnone, ?_⟩
    intro l' hl' hne
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hl'
    obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
    rcases hbefore k (by omega) hklt with h | h
    · rwa [hkeq] at h
    · exfalso
      rw [hun, hkeq] at h
      exact hne (by injection h.symm)
  -- the `lit_value` index bound
  · have hjs := o_post2 j (by assumption)
    obtain ⟨-, hmem⟩ :=
      Solver.scan_position hcl c_post lit_post (by rw [hjs.1]; omega)
    exact hbound lit hmem
  -- a second unassigned literal: nothing is forced
  · have hjs := o_post2 j (by assumption)
    obtain ⟨-, hmem⟩ :=
      Solver.scan_position hcl c_post lit_post (by rw [hjs.1]; omega)
    refine ⟨by simp, by simp, fun _ => ⟨lit, hmem, ?_⟩⟩
    have hnone : Solver.valueOf s lit.var = none := o1_post1.mp (by assumption)
    intro hf
    have hf' : Solver.valueOf s lit.var = some lit.negated := hf
    rw [hnone] at hf'
    simp at hf'
  -- the recursion that records this literal as the unassigned one
  · have hjs := o_post2 j (by assumption)
    obtain ⟨-, hmem⟩ :=
      Solver.scan_position hcl c_post lit_post (by rw [hjs.1]; omega)
    intro l' hl'
    have hll : l' = l := by injection hl'.symm
    subst hll
    rw [l_post]
    exact ⟨hmem, o1_post1.mp (by assumption)⟩
  -- positions before `j` are unchanged; `j` itself is the literal just recorded
  · have hjs := o_post2 j (by assumption)
    obtain ⟨hlitcl, -⟩ :=
      Solver.scan_position hcl c_post lit_post (by rw [hjs.1]; omega)
    have hun : unassigned = core.option.Option.None := by
      by_contra hc'
      exact absurd (b_post.mpr hc') (by assumption)
    intro k hk hklt
    rw [hjs.2.2] at hk
    rcases Nat.lt_or_ge k iter.start.val with hk' | hk'
    · rcases hbefore k hk' hklt with h | h
      · exact Or.inl h
      · rw [hun] at h
        simp at h
    · have hkj : k = j.val := by rw [hjs.1]; omega
      subst hkj
      exact Or.inr (by rw [hlitcl, l_post])
  -- a satisfied literal: nothing is forced
  · have hjs := o_post2 j (by assumption)
    obtain ⟨-, hmem⟩ :=
      Solver.scan_position hcl c_post lit_post (by rw [hjs.1]; omega)
    refine ⟨by simp, by simp, fun _ => ⟨lit, hmem, ?_⟩⟩
    have htrue : Solver.litTrue s lit := o1_post3.mp (by simp_all)
    intro hf
    have hf' : Solver.valueOf s lit.var = some lit.negated := hf
    have ht' : Solver.valueOf s lit.var = some (!lit.negated) := htrue
    rw [hf'] at ht'
    simp at ht'
  -- positions before `j` are unchanged; `j` itself is false
  · have hjs := o_post2 j (by assumption)
    obtain ⟨hlitcl, -⟩ :=
      Solver.scan_position hcl c_post lit_post (by rw [hjs.1]; omega)
    intro k hk hklt
    rw [hjs.2.2] at hk
    rcases Nat.lt_or_ge k iter.start.val with hk' | hk'
    · exact hbefore k hk' hklt
    · have hkj : k = j.val := by rw [hjs.1]; omega
      subst hkj
      refine Or.inl ?_
      rw [hlitcl]
      exact o1_post2.mp (by simp_all)
termination_by cl.length - iter.start.val
decreasing_by
  all_goals
    (have hjs := o_post2 j (by assumption)
     omega)

/-- **`status`.** Deliberately *not* `@[step]`: the clause `cl` is not determined by the
    call, so `step` could not instantiate it; `propagate`'s proof supplies it by hand with
    `step with`. -/
theorem sat_cdcl.Solver.status.spec (s : sat_cdcl.Solver) (clause : Std.Usize)
    (cl : List cnf.Literal)
    (hcl : Solver.clauseAt s clause = some cl)
    (hbound : ∀ lit ∈ cl, lit.var.val < s.value.val.length) :
    sat_cdcl.Solver.status s clause ⦃ (st : sat_cdcl.Status) =>
      (st = sat_cdcl.Status.Conflict → ∀ lit ∈ cl, Solver.litFalse s lit)
      ∧ (∀ lit, st = sat_cdcl.Status.Unit lit →
          lit ∈ cl ∧ Solver.valueOf s lit.var = none
          ∧ ∀ l ∈ cl, l ≠ lit → Solver.litFalse s l)
      ∧ (st = sat_cdcl.Status.Silent → ∃ lit ∈ cl, ¬ Solver.litFalse s lit) ⦄ := by
  unfold sat_cdcl.Solver.status
  obtain ⟨c0, hcget, hc0⟩ := Solver.clauseAt_eq hcl
  step*
  obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hcget
  exact h

/-- **The trail is strictly shorter than the slot arrays while anything is unassigned.**
    This is the first component of `propagate`'s termination measure: each propagation
    moves one variable onto the trail, and the trail cannot outgrow the arrays because its
    entries are distinct. -/
theorem Solver.trail_length_lt {s : sat_cdcl.Solver} (hwf : Solver.WF s) {u : Std.U16}
    (hu : u.val < s.value.val.length) (hun : Solver.valueOf s u = none) :
    s.trail.val.length < s.value.val.length := by
  have hnd : (s.trail.val.map (·.val)).Nodup := by
    refine List.Nodup.map ?_ hwf.trail_nodup
    intro a b hab
    exact (Std.UScalar.eq_equiv a b).mpr (by simpa using hab)
  have hunot : u ∉ s.trail.val := by
    rw [← hwf.trail_iff, hun]
    simp
  have hsub : (s.trail.val.map (·.val)) ⊆ (List.range s.value.val.length).erase u.val := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have hne : w.val ≠ u.val := by
      intro hc
      exact hunot (by rw [← Solver.uscalar_eq_of_val hc]; exact hw)
    exact (List.mem_erase_of_ne hne).mpr (by simp [hwf.trail_bound w hw])
  obtain ⟨m, hperm, hsubl⟩ := List.subperm_of_subset hnd hsub
  have h1 : s.trail.val.length = m.length := by
    have := hperm.length_eq
    simp only [List.length_map] at this
    omega
  have h2 := hsubl.length_le
  rw [List.length_erase_of_mem (by simp [hu])] at h2
  simp only [List.length_range] at h2
  omega

/-- The solver `propagate`'s loop reassembles from the fields it returns. Naming it keeps
    the loop's postcondition readable -- `-loops-to-rec` explodes the state into thirteen
    components, and every clause of that postcondition is about the state they make up. -/
def Solver.ofFields (clauses : alloc.vec.Vec cnf.Clause) (problem_clauses : Std.Usize)
    (value : alloc.vec.Vec (core.option.Option Bool)) (level : alloc.vec.Vec Std.Usize)
    (reason : alloc.vec.Vec (core.option.Option Std.Usize)) (phase : alloc.vec.Vec Bool)
    (activity : alloc.vec.Vec Std.U32) (occurs seen : alloc.vec.Vec Bool)
    (trail : alloc.vec.Vec Std.U16) (trail_lim : alloc.vec.Vec Std.Usize)
    (conflicts : Std.U32) : sat_cdcl.Solver :=
  { clauses := clauses, problem_clauses := problem_clauses, value := value, level := level,
    reason := reason, phase := phase, activity := activity, occurs := occurs, seen := seen,
    trail := trail, trail_lim := trail_lim, conflicts := conflicts }

@[simp]
theorem Solver.ofFields_self (s : sat_cdcl.Solver) :
    Solver.ofFields s.clauses s.problem_clauses s.value s.level s.reason s.phase s.activity
      s.occurs s.seen s.trail s.trail_lim s.conflicts = s := rfl

/-- **`propagate`'s loop.** One flat loop with a cursor that wraps back to 0 whenever the
    pass it finished assigned something -- the shape aeneas forced, since a `return` out of
    an inner loop is untranslatable.

    Three invariants ride along. `hpass` is the fixpoint argument: while `progress` is
    false nothing has been assigned during this pass, so the clauses behind the cursor are
    still not falsified -- which is what makes the `None` answer mean "no clause is
    falsified". `hcf` is what makes the *conflict* answer usable by `analyze`: a clause
    that is falsified mentions the current decision level. It is preserved because a
    clause can only become falsified by this pass's own assignment, and those are all at
    the current level. `hopen` is `assign`'s precondition, threaded through.

    **Termination** is lexicographic on `(unassigned slots, progress, clauses left)`:
    a propagation shrinks the first (`Solver.trail_length_lt`), the wrap-around shrinks the
    second, and a clause that forces nothing shrinks the third. The wrap is why a single
    measure will not do. -/
@[step]
theorem sat_cdcl.Solver.propagate_loop.spec (sv : sat_cdcl.Solver) (i : Std.Usize)
    (progress : Bool)
    (hwf : Solver.WF sv)
    (hi : i.val ≤ sv.clauses.val.length)
    (hpass : progress = false → ∀ (k : Nat), k < i.val → ∀ cl, (Solver.db sv)[k]? = some cl →
      ∃ lit ∈ cl, ¬ Solver.litFalse sv lit)
    (hcf : ∀ cl ∈ Solver.db sv, (∀ lit ∈ cl, Solver.litFalse sv lit) →
      0 < Solver.decisionLevel sv →
      ∃ lit ∈ cl, Solver.levelOf sv lit.var = Solver.decisionLevel sv)
    (hopen : 0 < Solver.decisionLevel sv → ∃ v ∈ sv.trail.val,
      Solver.levelOf sv v = Solver.decisionLevel sv ∧ Solver.reasonOf sv v = none)
    (hvars : ∀ cl ∈ Solver.db sv, ∀ lit ∈ cl, lit.var.val < sv.value.val.length) :
    sat_cdcl.Solver.propagate_loop sv i progress ⦃
      (r : core.option.Option Std.Usize) (cls : alloc.vec.Vec cnf.Clause) (pc : Std.Usize)
      (val : alloc.vec.Vec (core.option.Option Bool)) (lvl : alloc.vec.Vec Std.Usize)
      (rsn : alloc.vec.Vec (core.option.Option Std.Usize)) (phs : alloc.vec.Vec Bool)
      (act : alloc.vec.Vec Std.U32) (occ : alloc.vec.Vec Bool) (sn : alloc.vec.Vec Bool)
      (trl : alloc.vec.Vec Std.U16) (tlim : alloc.vec.Vec Std.Usize) (cfl : Std.U32) =>
        Solver.WF (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl)
        ∧ Solver.db (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl)
            = Solver.db sv
        ∧ Solver.decisionLevel
            (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl)
              = Solver.decisionLevel sv
        ∧ (∃ suffix, trl.val = sv.trail.val ++ suffix)
        ∧ (∀ v b, Solver.valueOf sv v = some b →
            Solver.valueOf (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl) v
              = some b)
        ∧ (∀ conflict, r = core.option.Option.Some conflict →
            ∃ cl, Solver.clauseAt
                (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl) conflict
                  = some cl
              ∧ (∀ lit ∈ cl, Solver.litFalse
                  (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl) lit)
              ∧ (0 < Solver.decisionLevel sv → ∃ lit ∈ cl,
                  Solver.levelOf
                    (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl) lit.var
                      = Solver.decisionLevel sv))
        ∧ (r = core.option.Option.None → ∀ cl ∈ Solver.db sv, ∃ lit ∈ cl,
            ¬ Solver.litFalse
              (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl) lit)
        ∧ val.val.length = sv.value.val.length
        ∧ occ = sv.occurs
        ∧ cfl = sv.conflicts
        ∧ (∀ cl ∈ Solver.db (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl),
            (∀ lit ∈ cl, Solver.litFalse (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl) lit) →
            0 < Solver.decisionLevel (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl) →
            ∃ lit ∈ cl, Solver.levelOf (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl) lit.var
              = Solver.decisionLevel (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl))
        ∧ (∀ v ∈ sv.trail.val,
            Solver.levelOf (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl) v = Solver.levelOf sv v
            ∧ Solver.reasonOf (Solver.ofFields cls pc val lvl rsn phs act occ sn trl tlim cfl) v = Solver.reasonOf sv v) ⦄ := by
  unfold sat_cdcl.Solver.propagate_loop
  step*
  -- the fixpoint exit: a whole pass with nothing assigned, so nothing is falsified
  · rename_i hprog
    have hiend : i.val = sv.clauses.val.length := by
      have hbr : i = i1 := ‹i = i1›
      rw [hbr]
      omega
    have hpf : progress = false := by
      simpa using hprog
    refine ⟨?_, rfl, rfl, ⟨[], by simp⟩, fun v b h => h, by simp, ?_,
      by simpa [Solver.ofFields] using hcf, fun v hv => ⟨rfl, rfl⟩⟩
    · simpa [Solver.ofFields] using hwf
    · intro _ cl hcl
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hcl
      obtain ⟨hklt, -⟩ := List.getElem?_eq_some_iff.mp hk
      have hkl : k < i.val := by
        simp only [Solver.db, List.length_map] at hklt
        omega
      obtain ⟨lit, hlit, hnf⟩ := hpass hpf k hkl cl hk
      exact ⟨lit, hlit, by simpa [Solver.ofFields] using hnf⟩
  -- the scan of clause `i`
  · have hilt : i.val < sv.clauses.val.length := by
      have hbr : ¬ (i = i1) := ‹¬ (i = i1)›
      have : i.val ≠ i1.val := fun hc => hbr (Solver.uscalar_eq_of_val hc)
      omega
    obtain ⟨cl, hcl⟩ : ∃ cl, Solver.clauseAt sv i = some cl := by
      refine ⟨(Solver.db sv)[i.val]'(by simp [Solver.db]; omega), ?_⟩
      exact List.getElem?_eq_getElem (by simp [Solver.db]; omega)
    have hclmem : cl ∈ Solver.db sv := Solver.mem_db_of_clauseAt hcl
    step with (sat_cdcl.Solver.status.spec sv i cl hcl
      (fun lit hlit => hvars cl hclmem lit hlit))
    step*
    -- conflict: the clause at `i` is falsified, and `hcf` says it mentions this level
    · refine ⟨by simpa using hwf, by simp, by simp, ⟨[], by simp⟩,
        fun v b h => by simpa using h, ?_, by simp,
        by simpa [Solver.ofFields] using hcf, fun v hv => ⟨rfl, rfl⟩⟩
      intro conflict hconf
      have hceq : i = conflict := by injection hconf
      subst hceq
      refine ⟨cl, by simpa using hcl, ?_, ?_⟩
      · intro lit hlit
        simpa using s_post1 (by assumption) lit hlit
      · intro hdl
        obtain ⟨lit, hlit, hlvl⟩ := hcf cl hclmem (s_post1 (by assumption)) hdl
        exact ⟨lit, hlit, by simpa using hlvl⟩
    -- unit: assign the forced literal and carry on
    · obtain ⟨hlitmem, hlitnone, hothers⟩ := s_post2 lit (by assumption)
      have hlitvar : lit.var.val < sv.value.val.length := hvars cl hclmem lit hlitmem
      step with (sat_cdcl.Solver.assign.spec sv lit.var _ (core.option.Option.Some i)
        hwf hlitvar hlitnone (by simp) (fun r hr hdl => hopen hdl)
        (by
          intro r hr
          have hri : r = i := by injection hr.symm
          subst hri
          refine ⟨cl, hcl, ?_, ?_⟩
          · have hneg : (!(decide (¬ lit.negated = true))) = lit.negated := by
              cases lit.negated <;> simp
            have hlit : cnf.Literal.mk lit.var (!(decide (¬ lit.negated = true))) = lit := by
              rw [hneg]
            rw [hlit]
            exact hlitmem
          · intro l hl hne
            refine hothers l hl ?_
            intro hc
            refine hne ?_
            have hneg : (!(decide (¬ lit.negated = true))) = lit.negated := by
              cases lit.negated <;> simp
            rw [hc, hneg]))
      step*
      -- the cursor is still inside the database
      · have hlen : self1.clauses.val.length = sv.clauses.val.length := by
          simpa [Solver.db] using congrArg List.length self1_post2
        omega
      -- a clause falsified by this assignment mentions the variable it assigned, and
      -- that variable sits at the current level; otherwise it was already falsified
      · intro cl' hcl' hallfalse hdl
        by_cases hmem : ∃ l ∈ cl', l.var = lit.var
        · obtain ⟨l, hl, hlv⟩ := hmem
          exact ⟨l, hl, by rw [hlv, self1_post6, self1_post3]⟩
        · push Not at hmem
          have hall : ∀ l ∈ cl', Solver.litFalse sv l := by
            intro l hl
            have hv := (self1_post8 l.var (hmem l hl)).1
            have hf : Solver.valueOf self1 l.var = some l.negated := hallfalse l hl
            rw [hv] at hf
            exact hf
          obtain ⟨l, hl, hlvl⟩ := hcf cl' (by rw [← self1_post2]; exact hcl') hall
            (by rw [self1_post3] at hdl; exact hdl)
          refine ⟨l, hl, ?_⟩
          rw [(self1_post8 l.var (hmem l hl)).2.1, hlvl, self1_post3]
      -- the decision that opened this level is still there
      · intro hdl
        obtain ⟨v, hvmem, hvlvl, hvrsn⟩ := hopen (by rw [self1_post3] at hdl; exact hdl)
        have hvne : v ≠ lit.var := by
          intro hc
          rw [hc, ← hwf.trail_iff, hlitnone] at hvmem
          simp at hvmem
        refine ⟨v, by rw [self1_post4]; exact List.mem_append_left _ hvmem, ?_, ?_⟩
        · rw [(self1_post8 v hvne).2.1, hvlvl, self1_post3]
        · rw [(self1_post8 v hvne).2.2]
          exact hvrsn
      -- and the loop's own postcondition, read through the assignment
      · refine ⟨r_post1, by rw [r_post2, self1_post2], by rw [r_post3, self1_post3], ?_, ?_,
          ?_, ?_, by rw [r_post8, self1_post7], by rw [r_post9, self1_post9],
          by rw [r_post10, self1_post10], r_post11, ?_⟩
        · obtain ⟨suf, hsuf⟩ : ∃ suf, trl.val = self1.trail.val ++ suf := ⟨_, r_post4⟩
          refine ⟨[lit.var] ++ suf, ?_⟩
          rw [hsuf, self1_post4]
          simp
        · intro v b hv
          refine r_post5 v b ?_
          by_cases hveq : v = lit.var
          · rw [hveq, hlitnone] at hv
            simp at hv
          · rw [(self1_post8 v hveq).1]
            exact hv
        · intro conflict hconf
          obtain ⟨cl', hcl', hallf, hlvl⟩ := r_post6 conflict hconf
          refine ⟨cl', hcl', hallf, ?_⟩
          rw [← self1_post3]
          exact hlvl
        · intro hr cl' hcl'
          exact r_post7 hr cl' (by rw [self1_post2]; exact hcl')
        · intro v hv
          have hvne : v ≠ lit.var := by
            intro hc
            rw [hc, ← hwf.trail_iff, hlitnone] at hv
            simp at hv
          have hv' : v ∈ self1.trail.val := by
            rw [self1_post4]; exact List.mem_append_left _ hv
          obtain ⟨hl, hr⟩ := r_post12 v hv'
          exact ⟨by rw [hl, (self1_post8 v hvne).2.1],
            by rw [hr, (self1_post8 v hvne).2.2]⟩
    -- silent: nothing forced here, so the pass invariant extends by one clause
    · intro hpf k hk cl' hcl'
      rcases Nat.lt_or_ge k i.val with hk' | hk'
      · exact hpass hpf k hk' cl' hcl'
      · have hki : k = i.val := by omega
        subst hki
        have hcc : cl' = cl := by
          rw [Solver.clauseAt] at hcl
          exact Option.some.inj (hcl'.symm.trans hcl)
        rw [hcc]
        exact s_post3 (by assumption)
termination_by (sv.value.val.length - sv.trail.val.length, cond progress 1 0,
  sv.clauses.val.length - i.val)
decreasing_by
  all_goals
    first
    -- the wrap back to the start of the database: `progress` goes from true to false
    | (apply Prod.Lex.right
       apply Prod.Lex.left
       rw [‹progress = true›]
       simp)
    -- a propagation: one more variable is on the trail, and the trail cannot outgrow
    -- the slot arrays
    | (apply Prod.Lex.left
       have hlt := Solver.trail_length_lt hwf hlitvar hlitnone
       have h4 := congrArg List.length self1_post4
       simp only [List.length_append, List.length_cons, List.length_nil] at h4
       omega)
    -- a clause that forced nothing: the cursor advances
    | (apply Prod.Lex.right
       apply Prod.Lex.right
       scalar_tac)

/-- **`propagate` preserves the invariant, and says what its answer means.** `hcf` ("a
    falsified clause mentions the current level") is the caller's obligation, and it does
    real work in the conflict case: the clause `propagate` conflicts on must hold a literal
    at the *current* level, which is exactly the third hypothesis of `analyze.spec` and
    `hcf` is the only way to get it. `propagate` hands `hcf` back for the state it returns,
    since that is what makes it an invariant of `search`'s loop rather than a fact about one
    call.

    This hypothesis was "nothing is falsified yet" when this spec was written, which
    `search` cannot supply: the assignment that follows a backjump can falsify a clause,
    and then the next call has one. `hcf` is the weaker statement that *is* inductive --
    everything falsified mentions the level the search is on -- and it is all the proof
    ever used the stronger one for.

    The `none` case is the fixpoint claim, in the one form the model argument needs: no
    clause of the database is falsified. (Propagation to a fixpoint also leaves no clause
    *unit*, which is what makes the search progress, but no correctness statement above
    consumes that.)

    `hopen` was not in this statement when it was written, and is the same hypothesis
    `assign.spec` grew: a propagation at a level above 0 does not open that level, so it
    preserves "every level with an entry has a decision" only if one is already there.
    `search` supplies it -- `propagate` runs either at level 0 or just after a decision. -/
theorem sat_cdcl.Solver.propagate.spec (s : sat_cdcl.Solver)
    (hwf : Solver.WF s)
    (hcf : ∀ cl ∈ Solver.db s, (∀ lit ∈ cl, Solver.litFalse s lit) →
      0 < Solver.decisionLevel s →
      ∃ lit ∈ cl, Solver.levelOf s lit.var = Solver.decisionLevel s)
    (hopen : 0 < Solver.decisionLevel s → ∃ v ∈ s.trail.val,
      Solver.levelOf s v = Solver.decisionLevel s ∧ Solver.reasonOf s v = none) :
    sat_cdcl.Solver.propagate s ⦃ (r : core.option.Option Std.Usize)
      (s' : sat_cdcl.Solver) =>
        Solver.WF s'
        ∧ Solver.db s' = Solver.db s
        ∧ Solver.decisionLevel s' = Solver.decisionLevel s
        ∧ (∃ suffix, s'.trail.val = s.trail.val ++ suffix)
        ∧ (∀ v b, Solver.valueOf s v = some b → Solver.valueOf s' v = some b)
        ∧ (∀ conflict, r = core.option.Option.Some conflict →
            ∃ cl, Solver.clauseAt s' conflict = some cl
              ∧ (∀ lit ∈ cl, Solver.litFalse s' lit)
              ∧ (0 < Solver.decisionLevel s' →
                  ∃ lit ∈ cl, Solver.levelOf s' lit.var = Solver.decisionLevel s'))
        ∧ (r = core.option.Option.None →
            ∀ cl ∈ Solver.db s', ∃ lit ∈ cl, ¬ Solver.litFalse s' lit)
        ∧ s'.value.val.length = s.value.val.length
        ∧ s'.occurs = s.occurs
        ∧ s'.conflicts = s.conflicts
        ∧ (∀ cl ∈ Solver.db s', (∀ lit ∈ cl, Solver.litFalse s' lit) →
            0 < Solver.decisionLevel s' →
            ∃ lit ∈ cl, Solver.levelOf s' lit.var = Solver.decisionLevel s')
        ∧ (∀ v ∈ s.trail.val, Solver.levelOf s' v = Solver.levelOf s v
            ∧ Solver.reasonOf s' v = Solver.reasonOf s v) ⦄ := by
  unfold sat_cdcl.Solver.propagate
  step*
  -- `hcf` -- the "falsified clauses mention this level" invariant -- is the caller's, and
  -- `step*` matches it against the loop's straight away; what is left is the slot bound
  -- every variable a clause mentions has a slot
  · exact hwf.db_vars
  -- the loop's postcondition is this one, on the state the extraction reassembles
  · simp only [Solver.ofFields] at o_post1 o_post2 o_post3 o_post5 o_post6 o_post7
    simp only [Solver.ofFields] at o_post11 o_post12
    refine ⟨o_post1, o_post2, o_post3, ⟨_, o_post4⟩, o_post5, ?_, ?_, o_post8, o_post9,
      o_post10, o_post11, o_post12⟩
    · intro conflict hconf
      obtain ⟨cl, hcl, hallf, hlvl⟩ := o_post6 conflict hconf
      exact ⟨cl, hcl, hallf, by rw [o_post3]; exact hlvl⟩
    · intro hr cl hcl
      exact o_post7 hr cl (by rw [← o_post2]; exact hcl)

/-! #### What `search` calls before it decides

`pick_branch_var` and `decay` are the last two functions of the solver without a spec, and
neither is about the implication graph: one picks an unassigned variable, the other halves
the activity scores. They are here because `search` calls them, and because
`pick_branch_var` returning `None` is *half of the `true` answer* -- the other half is
`propagate`'s fixpoint. -/

/-- `Option::is_none`, the mirror of `is_some` above: the decision heuristic asks it
    whether it has a candidate yet. -/
@[step]
theorem core.option.Option.is_none.spec {T : Type} (o : core.option.Option T) :
    core.option.Option.is_none o ⦃ (b : Bool) =>
      b = true ↔ o = core.option.Option.None ⦄ := by
  unfold core.option.Option.is_none
  match o with
  | core.option.Option.None => step*
  | core.option.Option.Some x => step*

/-- **The decision heuristic's scan.** Both halves of the answer are about the variables
    the scan has passed: a `Some` is unassigned and has a slot (which is `assign`'s
    precondition), and a `None` means every *marked* variable below the cursor is already
    assigned (which is what makes the search's `true` answer total on the problem's
    variables).

    `hbound` is the hypothesis this file needed and did not have: the loop counts in
    `usize` and casts the index down to the `u16` a variable is, so without
    `value.len() ≤ 2 ^ 16` the returned variable is a *different* variable from the one
    the scan looked at, and none of the above follows. `Solver::new` sizes the arrays from
    the largest variable of the CNF, so the bound holds -- `new_loop0.spec` is where it
    comes from -- but nothing in `Solver.WF` records it. -/
@[step]
theorem sat_cdcl.Solver.pick_branch_var_loop.spec (iter : core.ops.range.Range Std.Usize)
    (s : sat_cdcl.Solver) (best : core.option.Option Std.U16) (best_activity : Std.U32)
    (hwf : Solver.WF s)
    (hend : iter.«end».val ≤ s.value.val.length)
    (hbound : s.value.val.length ≤ 2 ^ 16)
    (hbest : ∀ v, best = core.option.Option.Some v →
      v.val < s.value.val.length ∧ Solver.valueOf s v = none)
    (hscan : best = core.option.Option.None → ∀ v : Std.U16, v.val < iter.start.val →
      s.occurs.val[v.val]? = some true → (Solver.valueOf s v).isSome = true) :
    sat_cdcl.Solver.pick_branch_var_loop iter s best best_activity ⦃
      (r : core.option.Option Std.U16) =>
        (∀ v, r = core.option.Option.Some v →
          v.val < s.value.val.length ∧ Solver.valueOf s v = none)
        ∧ (r = core.option.Option.None → ∀ v : Std.U16, v.val < iter.«end».val →
            s.occurs.val[v.val]? = some true → (Solver.valueOf s v).isSome = true) ⦄ := by
  unfold sat_cdcl.Solver.pick_branch_var_loop
  step*
  all_goals obtain ⟨hvs, hvlt, hstart⟩ := o_post2 _ ‹o = some _›
  all_goals
    (have hslot : v.val < s.value.val.length := by scalar_tac
     have hlt16 : v.val < 2 ^ 16 := Nat.lt_of_lt_of_le hslot hbound
     first
     -- the two slot bounds: `occurs` and `activity` are as long as `value`
     | (rw [hwf.occurs_length]; exact hslot)
     | (rw [hwf.activity_length]; exact hslot)
     -- the cursor's variable is unassigned, so it is a legal decision -- and this is
     -- where `hbound` is spent, on the cast down to `u16`
     | (intro w hw
        have hcast : w = UScalar.cast UScalarTy.U16 v := by
          injection hw with hiw
          rw [← hiw]
          assumption
        have hwv : w.val = v.val := by
          rw [hcast, UScalar.cast_val_eq]
          exact Nat.mod_eq_of_lt hlt16
        have hnone : o1 = core.option.Option.None := by
          by_contra hc
          exact absurd (b_post.mpr hc) ‹¬ b = true›
        exact ⟨by omega, by simp [Solver.valueOf, hwv, o1_post, hnone]⟩)
     -- the cursor's variable is assigned, so the scan invariant extends by one
     | (intro hbn w hw hocc
        rcases Nat.lt_or_ge w.val iter.start.val with h | h
        · exact hscan hbn w h hocc
        · have hwv : w.val = v.val := by scalar_tac
          obtain ⟨x, hx⟩ : ∃ x, o1 = core.option.Option.Some x := by
            match o1 with
            | core.option.Option.None => exact absurd rfl (b_post.mp ‹b = true›)
            | core.option.Option.Some x => exact ⟨x, rfl⟩
          simp [Solver.valueOf, hwv, o1_post, hx]))
termination_by iter.«end».val - iter.start.val
decreasing_by
  all_goals
    obtain ⟨-, hlt, hstart⟩ := o_post2 _ (by assumption)
    rw [o_post1]
    omega

/-- **`pick_branch_var`**: the scan over the whole slot array. `None` is the statement the
    search's `true` answer is read off: every variable that occurs in the problem is
    assigned. -/
@[step]
theorem sat_cdcl.Solver.pick_branch_var.spec (s : sat_cdcl.Solver) (hwf : Solver.WF s)
    (hbound : s.value.val.length ≤ 2 ^ 16) :
    sat_cdcl.Solver.pick_branch_var s ⦃ (r : core.option.Option Std.U16) =>
      (∀ v, r = core.option.Option.Some v →
        v.val < s.value.val.length ∧ Solver.valueOf s v = none)
      ∧ (r = core.option.Option.None → ∀ v : Std.U16, v.val < s.value.val.length →
          s.occurs.val[v.val]? = some true → (Solver.valueOf s v).isSome = true) ⦄ := by
  unfold sat_cdcl.Solver.pick_branch_var sat_cdcl.Solver.num_vars
  step*

/-- **`decay`'s loop** halves every activity score. All the invariant asks of it is that it
    keeps the array's length. -/
@[step]
theorem sat_cdcl.Solver.decay_loop.spec (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec Std.U32) (hend : iter.«end».val ≤ v.val.length) :
    sat_cdcl.Solver.decay_loop iter v ⦃ (v' : alloc.vec.Vec Std.U32) =>
      v'.val.length = v.val.length ⦄ := by
  unfold sat_cdcl.Solver.decay_loop
  step*
termination_by iter.«end».val - iter.start.val
decreasing_by
  all_goals
    obtain ⟨-, hlt, hstart⟩ := o_post2 _ (by assumption)
    rw [o_post1]
    omega

/-- **Only `activity` changed.** `activity` is the one array no field of the invariant
    reads except for its length, so every other field transports along the update. This is
    what makes `analyze`'s `s' = { s with activity := s'.activity }` and `decay` invariant-
    preserving for free. -/
theorem Solver.wf_activity {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    (act : alloc.vec.Vec Std.U32) (hlen : act.val.length = s.activity.val.length) :
    Solver.WF { s with activity := act } :=
  { hwf with activity_length := by rw [hlen]; exact hwf.activity_length }

/-- The same, in the form `analyze.spec`'s postcondition hands it over. -/
theorem Solver.wf_of_activity_eq {s s' : sat_cdcl.Solver} (hwf : Solver.WF s)
    (heq : s' = { s with activity := s'.activity })
    (hlen : s'.activity.val.length = s.activity.val.length) : Solver.WF s' := by
  have h := Solver.wf_activity hwf s'.activity hlen
  rwa [← heq] at h

/-- **`decay` preserves the invariant** and changes nothing else. -/
theorem sat_cdcl.Solver.decay.spec (s : sat_cdcl.Solver) (hwf : Solver.WF s) :
    sat_cdcl.Solver.decay s ⦃ (s' : sat_cdcl.Solver) =>
      Solver.WF s' ∧ s' = { s with activity := s'.activity } ⦄ := by
  unfold sat_cdcl.Solver.decay
  step*
  exact Solver.wf_activity hwf v v_post

/-- **`decay`, or not.** `search` halves the activity scores every `DECAY_INTERVAL`
    conflicts, and the two arms of that `if` have the same spec -- so giving the `if` itself
    one keeps the conflict branch of the search from being proved twice. -/
theorem sat_cdcl.Solver.decay_if.spec (s : sat_cdcl.Solver) (hwf : Solver.WF s)
    (c : Prop) [Decidable c] :
    (if c then sat_cdcl.Solver.decay s else ok s) ⦃ (s' : sat_cdcl.Solver) =>
      Solver.WF s' ∧ s' = { s with activity := s'.activity } ⦄ := by
  split
  · exact sat_cdcl.Solver.decay.spec s hwf
  · exact ⟨hwf, rfl⟩

/-! #### The termination measure

Every other loop in this file terminates because a counter runs down: `propagate` assigns,
`analyze` resolves, `backtrack` pops. `search` is the one that goes *backwards* -- a
backjump undoes assignments, and a restart undoes all of them -- so the measure is the
only part of its proof that has no analogue anywhere above.

**The trail as a numeral.** Read the trail as a base-3 number with one digit per slot, most
significant first: `0` where the trail has run out, `1` for a decision, `2` for a
propagation. Every step of the search makes this number *bigger*. A decision or a
propagation appends a digit where there was a `0`. A backjump is the interesting case: it
replaces the trail `P, d, …` -- `d` the decision it jumps back over -- with `P, ℓ`, where
`ℓ` is propagated by the clause just learned. The digit at that position goes from `1` to
`2`, and the assignments the backjump threw away are worth strictly less than that, because
they are the lower-order digits. This is the standard argument (Nieuwenhuis, Oliveras and
Tinelli's ordering on DPLL states) in the form a `termination_by` can consume: `3 ^ n` minus
the numeral, which is a natural that strictly drops.

**Restarts break it, and the budget pays for them.** `backtrack 0` throws the trail away, so
the numeral goes back down. What decreases there is the restart budget's remaining growth:
`search` takes a restart only after `budget` conflicts since the last one, and grows the
budget by half of itself each time, so `restartsLeft` -- how many times the budget can still
grow before it passes the bound on the number of steps a restart window can have -- drops by
one. The measure is lexicographic: `restartsLeft` outside, the trail numeral inside.

This is also what bounds the solver's `u32` counters, which is not a side issue: the
extraction's arithmetic is *checked*, so `self.conflicts + 1` overflowing is a failure, and
`⦃ ⦄` rules failure out. Every conflict drops the measure by at least one, so the measure
bounds the number of conflicts still to come -- which is what `search.spec`'s `hroom`
hypothesis says the counter has room for. -/

/-- A trail read as a base-3 numeral of `n` digits, most significant first. -/
def trailNumeral (n : Nat) (ds : List Nat) : Nat :=
  match n, ds with
  | 0, _ => 0
  | _ + 1, [] => 0
  | m + 1, d :: ds => d * 3 ^ m + trailNumeral m ds

@[simp] theorem trailNumeral_nil (n : Nat) : trailNumeral n [] = 0 := by
  cases n <;> simp [trailNumeral]

@[simp] theorem trailNumeral_zero (ds : List Nat) : trailNumeral 0 ds = 0 := by
  simp [trailNumeral]

theorem trailNumeral_cons (m : Nat) (d : Nat) (ds : List Nat) :
    trailNumeral (m + 1) (d :: ds) = d * 3 ^ m + trailNumeral m ds := by
  simp [trailNumeral]

/-- Every digit is at most `2`, so the numeral fits in `n` digits. -/
theorem trailNumeral_lt (n : Nat) (ds : List Nat) (h : ∀ d ∈ ds, d ≤ 2) :
    trailNumeral n ds < 3 ^ n := by
  induction n generalizing ds with
  | zero => simp
  | succ m ih =>
    match ds with
    | [] => simp
    | d :: ds =>
      have hd : d ≤ 2 := h d (by simp)
      have hrest := ih ds (fun x hx => h x (by simp [hx]))
      rw [trailNumeral_cons]
      have hmul : d * 3 ^ m ≤ 2 * 3 ^ m := Nat.mul_le_mul_right _ hd
      have : 3 ^ (m + 1) = 3 * 3 ^ m := by ring
      omega

/-- Reading a prefix, then the rest with that many digits fewer. -/
theorem trailNumeral_append (n : Nat) (ds es : List Nat) (h : ds.length ≤ n) :
    trailNumeral n (ds ++ es) = trailNumeral n ds + trailNumeral (n - ds.length) es := by
  induction ds generalizing n with
  | nil => simp
  | cons d ds ih =>
    match n with
    | 0 => simp at h
    | m + 1 =>
      have hle : ds.length ≤ m := by simpa using h
      simp only [List.cons_append, trailNumeral_cons, ih m hle, List.length_cons,
        Nat.succ_sub_succ]
      omega

/-- Each trail entry's digit: a decision is `1`, a propagation `2`. -/
def Solver.trailDigits (s : sat_cdcl.Solver) : List Nat :=
  s.trail.val.map (fun v => if Solver.reasonOf s v = none then 1 else 2)

/-- The trail, as the numeral. -/
def Solver.trailNum (s : sat_cdcl.Solver) : Nat :=
  trailNumeral s.value.val.length (Solver.trailDigits s)

/-- What the search still has to climb. -/
def Solver.trailLeft (s : sat_cdcl.Solver) : Nat :=
  3 ^ s.value.val.length - Solver.trailNum s

@[simp] theorem Solver.length_trailDigits (s : sat_cdcl.Solver) :
    (Solver.trailDigits s).length = s.trail.val.length := by
  simp [Solver.trailDigits]

theorem Solver.trailDigits_le (s : sat_cdcl.Solver) : ∀ d ∈ Solver.trailDigits s, d ≤ 2 := by
  intro d hd
  simp only [Solver.trailDigits, List.mem_map] at hd
  obtain ⟨v, -, rfl⟩ := hd
  split <;> omega

theorem Solver.trailNum_lt (s : sat_cdcl.Solver) :
    Solver.trailNum s < 3 ^ s.value.val.length :=
  trailNumeral_lt _ _ (Solver.trailDigits_le s)

/-- The order the measure is read in: a bigger numeral is less left to climb. -/
theorem Solver.trailLeft_lt_of_trailNum_lt {s s' : sat_cdcl.Solver}
    (hn : s'.value.val.length = s.value.val.length)
    (h : Solver.trailNum s < Solver.trailNum s') :
    Solver.trailLeft s' < Solver.trailLeft s := by
  have h1 := Solver.trailNum_lt s
  have h2 := Solver.trailNum_lt s'
  simp only [Solver.trailLeft, hn] at *
  omega

theorem Solver.trailLeft_le_of_trailNum_le {s s' : sat_cdcl.Solver}
    (hn : s'.value.val.length = s.value.val.length)
    (h : Solver.trailNum s ≤ Solver.trailNum s') :
    Solver.trailLeft s' ≤ Solver.trailLeft s := by
  have h1 := Solver.trailNum_lt s
  have h2 := Solver.trailNum_lt s'
  simp only [Solver.trailLeft, hn] at *
  omega

/-- The digits of a trail that grew, with the entries it already had reading the same. -/
theorem Solver.trailDigits_append {s s' : sat_cdcl.Solver} {suf : List Std.U16}
    (htrail : s'.trail.val = s.trail.val ++ suf)
    (hrsn : ∀ v ∈ s.trail.val, Solver.reasonOf s' v = Solver.reasonOf s v) :
    Solver.trailDigits s' = Solver.trailDigits s
      ++ suf.map (fun v => if Solver.reasonOf s' v = none then 1 else 2) := by
  simp only [Solver.trailDigits, htrail, List.map_append]
  congr 1
  exact List.map_congr_left (fun v hv => by rw [hrsn v hv])

/-- **The trail has at most one entry per slot.** `trail_length_le` bounds it by `2 ^ 16`,
    which is what `analyze`'s `i32` counter needs; the measure needs the sharper bound. -/
theorem Solver.trail_length_le_slots {s : sat_cdcl.Solver} (hwf : Solver.WF s) :
    s.trail.val.length ≤ s.value.val.length := by
  have hnd : (s.trail.val.map (·.val)).Nodup := by
    refine List.Nodup.map ?_ hwf.trail_nodup
    intro a b hab
    exact (Std.UScalar.eq_equiv a b).mpr (by simpa using hab)
  have hsub : s.trail.val.map (·.val) ⊆ List.range s.value.val.length := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    simpa using hwf.trail_bound u hu
  simpa using (List.Nodup.subperm hnd hsub).length_le

/-- **A trail that only grew has climbed at least as far.** -/
theorem Solver.trailNum_le_of_append {s s' : sat_cdcl.Solver} (hwf' : Solver.WF s')
    {suf : List Std.U16}
    (hn : s'.value.val.length = s.value.val.length)
    (htrail : s'.trail.val = s.trail.val ++ suf)
    (hrsn : ∀ v ∈ s.trail.val, Solver.reasonOf s' v = Solver.reasonOf s v) :
    Solver.trailNum s ≤ Solver.trailNum s' := by
  have hlen : s.trail.val.length ≤ s.value.val.length := by
    have h := Solver.trail_length_le_slots hwf'
    rw [htrail, hn] at h
    simp only [List.length_append] at h
    omega
  simp only [Solver.trailNum, Solver.trailDigits_append htrail hrsn, hn]
  rw [trailNumeral_append _ _ _ (by simpa using hlen)]
  omega

/-- **One more assignment has climbed strictly further.** The new entry's digit is `1` or
    `2` at a position the numeral had as `0`. -/
theorem Solver.trailNum_lt_of_assign {s s' : sat_cdcl.Solver} (hwf' : Solver.WF s')
    {var : Std.U16}
    (hn : s'.value.val.length = s.value.val.length)
    (htrail : s'.trail.val = s.trail.val ++ [var])
    (hrsn : ∀ v ∈ s.trail.val, Solver.reasonOf s' v = Solver.reasonOf s v) :
    Solver.trailNum s < Solver.trailNum s' := by
  have hlen : s.trail.val.length < s.value.val.length := by
    have h := Solver.trail_length_le_slots hwf'
    rw [htrail, hn] at h
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  have hsub : s.value.val.length - s.trail.val.length
      = (s.value.val.length - s.trail.val.length - 1) + 1 := by omega
  have hpos : 0 < trailNumeral (s.value.val.length - s.trail.val.length)
      [if Solver.reasonOf s' var = none then 1 else 2] := by
    rw [hsub, trailNumeral_cons]
    have h3 : 0 < 3 ^ (s.value.val.length - s.trail.val.length - 1) :=
      Nat.pow_pos (by omega)
    split <;> omega
  simp only [Solver.trailNum, Solver.trailDigits_append htrail hrsn, hn, List.map_cons,
    List.map_nil]
  rw [trailNumeral_append _ _ _ (by simpa using Nat.le_of_lt hlen)]
  simp only [Solver.length_trailDigits]
  omega

/-- **The backjump climbs strictly further, too** -- which is the whole reason a measure on
    the trail works for a search that *undoes* assignments. The trail it replaces has a
    decision at position `p`; the one it puts there instead is propagated, by the learned
    clause. Everything the old trail had above `p` is worth strictly less than that one
    digit's worth of difference. -/
theorem Solver.trailNum_lt_of_backjump {s s' : sat_cdcl.Solver} (hwf : Solver.WF s)
    {p : Nat} {var : Std.U16}
    (hn : s'.value.val.length = s.value.val.length)
    (hp : p < s.trail.val.length)
    (hdec : Solver.reasonOf s (s.trail.val[p]) = none)
    (htrail : s'.trail.val = s.trail.val.take p ++ [var])
    (hvar : Solver.reasonOf s' var ≠ none)
    (hrsn : ∀ v ∈ s.trail.val.take p, Solver.reasonOf s' v = Solver.reasonOf s v) :
    Solver.trailNum s < Solver.trailNum s' := by
  have hlen : s.trail.val.length ≤ s.value.val.length := Solver.trail_length_le_slots hwf
  have hpn : p < s.value.val.length := Nat.lt_of_lt_of_le hp hlen
  have hplen : (s.trail.val.take p).length = p := by
    simp only [List.length_take]
    omega
  have hsplit : s.trail.val
      = s.trail.val.take p ++ (s.trail.val[p] :: s.trail.val.drop (p + 1)) := by
    rw [← List.drop_eq_getElem_cons hp, List.take_append_drop]
  -- the two digit lists, sharing the prefix below `p`
  have hds : Solver.trailDigits s
      = (s.trail.val.take p).map (fun v => if Solver.reasonOf s v = none then 1 else 2)
        ++ (1 :: (s.trail.val.drop (p + 1)).map
              (fun v => if Solver.reasonOf s v = none then 1 else 2)) := by
    simp only [Solver.trailDigits]
    nth_rewrite 1 [hsplit]
    rw [List.map_append, List.map_cons, if_pos hdec]
  have hds' : Solver.trailDigits s'
      = (s.trail.val.take p).map (fun v => if Solver.reasonOf s v = none then 1 else 2)
        ++ [2] := by
    simp only [Solver.trailDigits, htrail, List.map_append, List.map_cons, List.map_nil,
      if_neg hvar]
    congr 1
    exact List.map_congr_left (fun v hv => by rw [hrsn v hv])
  have hpsub : s.value.val.length - p = (s.value.val.length - p - 1) + 1 := by omega
  have hrest : trailNumeral (s.value.val.length - p - 1)
      ((s.trail.val.drop (p + 1)).map
        (fun v => if Solver.reasonOf s v = none then 1 else 2))
      < 3 ^ (s.value.val.length - p - 1) := by
    refine trailNumeral_lt _ _ ?_
    intro d hd
    simp only [List.mem_map] at hd
    obtain ⟨v, -, rfl⟩ := hd
    split <;> omega
  simp only [Solver.trailNum, hds, hds', hn]
  rw [trailNumeral_append _ _ _ (by simp only [List.length_map, hplen]; omega),
    trailNumeral_append _ _ _ (by simp only [List.length_map, hplen]; omega),
    List.length_map, hplen, hpsub, trailNumeral_cons, trailNumeral_cons, trailNumeral_nil]
  omega

/-- How many more times the restart budget can grow before it passes `bound`. `search`
    grows it by half of itself on every restart, so this is a logarithm -- and it is `0`
    once the budget is past the bound, which is the point: a restart needs `budget`
    conflicts since the last one, and there cannot be more than `bound` of those. -/
def restartsLeft (bound budget : Nat) : Nat :=
  if 2 ≤ budget ∧ budget ≤ bound then restartsLeft bound (budget + budget / 2) + 1 else 0
termination_by bound + 1 - budget
decreasing_by omega

/-- One restart spends one of them. -/
theorem restartsLeft_lt (bound budget : Nat) (h2 : 2 ≤ budget) (hle : budget ≤ bound) :
    restartsLeft bound (budget + budget / 2) < restartsLeft bound budget := by
  have h : restartsLeft bound budget = restartsLeft bound (budget + budget / 2) + 1 := by
    rw [restartsLeft, if_pos (And.intro h2 hle)]
  omega

/-- `restartsLeft` is a count of steps that each grow the budget by at least one, so it
    cannot exceed the distance left to the bound. -/
theorem restartsLeft_le_sub (bound budget : Nat) :
    restartsLeft bound budget ≤ bound + 1 - budget := by
  rw [restartsLeft]
  split
  · rename_i h
    have ih := restartsLeft_le_sub bound (budget + budget / 2)
    omega
  · omega
termination_by bound + 1 - budget
decreasing_by omega

/-- The crude form of the same, which is the one a caller can state without knowing the
    budget: at most `bound` restarts, whatever the budget started at. -/
theorem restartsLeft_le (bound budget : Nat) : restartsLeft bound budget ≤ bound := by
  by_cases h : 2 ≤ budget ∧ budget ≤ bound
  · have := restartsLeft_le_sub bound budget
    omega
  · rw [restartsLeft, if_neg h]
    omega

/-- The measure `search` descends: the restart budget's remaining growth is the outer
    component, the trail numeral the inner one. A conflict or a decision climbs the trail
    (`trailLeft` drops); a restart abandons the trail but grows the budget. -/
def Solver.searchMeasure (s : sat_cdcl.Solver) (budget : Std.U32) : Nat :=
  restartsLeft (3 ^ s.value.val.length) budget.val * (3 ^ s.value.val.length + 1)
    + Solver.trailLeft s

/-- There is always at least one step left in the measure -- which is what gives the
    counters their headroom for the step about to be taken. -/
theorem Solver.searchMeasure_pos (s : sat_cdcl.Solver) (budget : Std.U32) :
    0 < Solver.searchMeasure s budget := by
  have := Solver.trailNum_lt s
  simp only [Solver.searchMeasure, Solver.trailLeft]
  omega

theorem Solver.trailLeft_le (s : sat_cdcl.Solver) :
    Solver.trailLeft s ≤ 3 ^ s.value.val.length := by
  simp only [Solver.trailLeft]
  exact Nat.sub_le _ _

/-- A step that climbs the trail and leaves the budget alone. -/
theorem Solver.searchMeasure_lt_of_trailLeft {s s' : sat_cdcl.Solver} {budget : Std.U32}
    (hn : s'.value.val.length = s.value.val.length)
    (h : Solver.trailLeft s' < Solver.trailLeft s) :
    Solver.searchMeasure s' budget < Solver.searchMeasure s budget := by
  simp only [Solver.searchMeasure, hn]
  omega

/-- A restart: the trail goes back to level 0, and the budget grows instead. -/
theorem Solver.searchMeasure_lt_of_restart {s s' : sat_cdcl.Solver} {budget budget' : Std.U32}
    (hn : s'.value.val.length = s.value.val.length)
    (h2 : 2 ≤ budget.val) (hle : budget.val ≤ 3 ^ s.value.val.length)
    (hbud : budget'.val = budget.val + budget.val / 2) :
    Solver.searchMeasure s' budget' < Solver.searchMeasure s budget := by
  have hstep := restartsLeft_lt (3 ^ s.value.val.length) budget.val h2 hle
  have htl := Solver.trailLeft_le s'
  rw [hn] at htl
  have hkey : restartsLeft (3 ^ s.value.val.length) budget'.val
        * (3 ^ s.value.val.length + 1) + (3 ^ s.value.val.length + 1)
      ≤ restartsLeft (3 ^ s.value.val.length) budget.val * (3 ^ s.value.val.length + 1) := by
    have hlt : restartsLeft (3 ^ s.value.val.length) budget'.val + 1
        ≤ restartsLeft (3 ^ s.value.val.length) budget.val := by
      rw [hbud]; omega
    calc restartsLeft (3 ^ s.value.val.length) budget'.val * (3 ^ s.value.val.length + 1)
            + (3 ^ s.value.val.length + 1)
        = (restartsLeft (3 ^ s.value.val.length) budget'.val + 1)
            * (3 ^ s.value.val.length + 1) := by ring
      _ ≤ restartsLeft (3 ^ s.value.val.length) budget.val
            * (3 ^ s.value.val.length + 1) := Nat.mul_le_mul_right _ hlt
  simp only [Solver.searchMeasure, hn]
  omega

/-- **The measure, bounded by a statement about the input.** `Solver.searchMeasure` is
    what `search.spec`'s three numeric hypotheses are stated against, and it mentions the
    solver. A caller that only knows the CNF's variables fit below `n` needs a bound in
    terms of `n`, and this is the crudest one that works: at most `3 ^ n` restarts, each
    worth at most one full trail's worth of steps, plus the trail the last window climbs.

    It is doubly exponential in the variable count, and that is not slack in the argument
    -- it is slack in the *statement*, which is all a caller has to satisfy. Sharpening it
    would sharpen the hypothesis, not the theorem. -/
def searchRoom (n : Nat) : Nat := 3 ^ n * 3 ^ n + 2 * 3 ^ n

theorem Solver.searchMeasure_le_searchRoom (s : sat_cdcl.Solver) (budget : Std.U32)
    {n : Nat} (hn : s.value.val.length ≤ n) :
    Solver.searchMeasure s budget ≤ searchRoom n := by
  have h3 : (3 : Nat) ^ s.value.val.length ≤ 3 ^ n :=
    Nat.pow_le_pow_right (by norm_num) hn
  have hr : restartsLeft (3 ^ s.value.val.length) budget.val ≤ 3 ^ s.value.val.length :=
    restartsLeft_le _ _
  have ht : Solver.trailLeft s ≤ 3 ^ s.value.val.length := Solver.trailLeft_le s
  have hmul : restartsLeft (3 ^ s.value.val.length) budget.val
      * (3 ^ s.value.val.length + 1) ≤ 3 ^ n * (3 ^ n + 1) :=
    Nat.mul_le_mul (le_trans hr h3) (by omega)
  have hexp : (3 : Nat) ^ n * (3 ^ n + 1) = 3 ^ n * 3 ^ n + 3 ^ n := by ring
  simp only [Solver.searchMeasure, searchRoom]
  omega

/-! #### Learning a clause, and the two answers

What is left before the loop itself: the database *grows*, and the two answers have to be
read off the state the loop stops in.

Growing it is `Solver.wf_push`, and the reason it is not free is `db_len`: the invariant
needs every clause to be short, so a *learned* clause has to be short too. That is why
`analyze.spec` now reports the length of what it returns -- its literals sit on distinct
marked variables, which are distinct entries of the trail, so there are at most `2 ^ 16` of
them plus the UIP. `Solver.Marking.bounds` had the bound already; nothing had asked for it.

The answers are `Solver.unsat_of_conflict_level_zero'` (a conflict with no decision above it
is a refutation: at level 0 the assignment is forced by the database itself, so the clause it
conflicts on is false under *every* model) and `Solver.model_of_fixpoint` (a fixpoint of
propagation with every variable assigned is a model: a clause nothing has falsified holds a
literal that is not false, and an assigned literal that is not false is true).
`Entails.trans` is what moves both from the database the search holds to the problem it was
given. -/

/-- Entailment composes: a database every clause of which `db₀` entails adds nothing to it. -/
theorem Entails.trans {db₀ db : List (List cnf.Literal)} {cl : List cnf.Literal}
    (hdb : ∀ c ∈ db, Entails db₀ c) (h : Entails db cl) : Entails db₀ cl := by
  intro w hw
  refine h w ?_
  simp only [Cnf.eval, List.all_eq_true]
  intro c hc
  exact hdb c hc w hw

/-- **A conflict at level 0 refutes the database.** Every literal of the conflicting clause
    is false, and at level 0 that means the database itself forces it false. -/
theorem Solver.unsat_of_conflict_level_zero {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    {cl : List cnf.Literal} (hdl : Solver.decisionLevel s = 0)
    (hcl : cl ∈ Solver.db s) (hfalse : ∀ lit ∈ cl, Solver.litFalse s lit)
    (w : Std.U16 → Bool) : Cnf.eval w (Solver.db s) ≠ true := by
  intro hw
  have hclw := Entails.of_mem hcl w hw
  simp only [Clause.eval, List.any_eq_true] at hclw
  obtain ⟨l, hl, hlw⟩ := hclw
  have hf := hfalse l hl
  have hmem : l.var ∈ s.trail.val := Solver.mem_trail_of_litFalse hwf hf
  have hlvl : Solver.levelOf s l.var = 0 := by
    have := hwf.level_le l.var hmem
    omega
  have hent := Solver.entails_trueLit_of_level_zero hwf l.var hmem hlvl w hw
  rw [Solver.eval_false_of_litFalse hf hent] at hlw
  simp at hlw

/-- The same, for the problem the search was handed. -/
theorem Solver.unsat_of_conflict_level_zero' {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    {db₀ : List (List cnf.Literal)} {cl : List cnf.Literal}
    (hsound : ∀ c ∈ Solver.db s, Entails db₀ c)
    (hdl : Solver.decisionLevel s = 0)
    (hcl : cl ∈ Solver.db s) (hfalse : ∀ lit ∈ cl, Solver.litFalse s lit)
    (w : Std.U16 → Bool) : Cnf.eval w db₀ ≠ true := by
  intro hw
  refine Solver.unsat_of_conflict_level_zero hwf hdl hcl hfalse w ?_
  simp only [Cnf.eval, List.all_eq_true]
  intro c hc
  exact hsound c hc w hw

/-- **A literal the assignment has not falsified is true, once its variable is assigned.**
    This is the other half of the `true` answer: `propagate` leaves no clause falsified, and
    `pick_branch_var` leaves no variable unassigned. -/
theorem Solver.eval_true_of_not_litFalse {s : sat_cdcl.Solver} {lit : cnf.Literal}
    {w : Std.U16 → Bool} (hassigned : (Solver.valueOf s lit.var).isSome = true)
    (hnf : ¬ Solver.litFalse s lit)
    (hw : ∀ v b, Solver.valueOf s v = some b → w v = b) :
    Literal.eval w lit = true := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hassigned
  have hne : b ≠ lit.negated := by
    intro hc
    exact hnf (by rw [Solver.litFalse, hb, hc])
  rw [Literal.eval_true_iff, hw lit.var b hb]
  cases hn : lit.negated <;> cases b <;> simp_all

/-- **Propagation to fixpoint with everything assigned is a model.** -/
theorem Solver.model_of_fixpoint {s : sat_cdcl.Solver} {db₀ : List (List cnf.Literal)}
    (hproblem : ∀ cl ∈ db₀, cl ∈ Solver.db s)
    (hfix : ∀ cl ∈ Solver.db s, ∃ lit ∈ cl, ¬ Solver.litFalse s lit)
    (hassigned : ∀ v ∈ cnfVars db₀, (Solver.valueOf s v).isSome = true)
    (w : Std.U16 → Bool) (hw : ∀ v b, Solver.valueOf s v = some b → w v = b) :
    Cnf.eval w db₀ = true := by
  simp only [Cnf.eval, List.all_eq_true]
  intro cl hcl
  obtain ⟨lit, hlit, hnf⟩ := hfix cl (hproblem cl hcl)
  have hvar : lit.var ∈ cnfVars db₀ := by
    simp only [cnfVars, List.mem_flatMap, clauseVars, List.mem_map]
    exact ⟨cl, hcl, lit, hlit, rfl⟩
  simp only [Clause.eval, List.any_eq_true]
  exact ⟨lit, hlit, Solver.eval_true_of_not_litFalse (hassigned lit.var hvar) hnf hw⟩

/-- **Pushing a clause preserves the invariant.** Only three fields of `Solver.WF` are about
    the database at all: the two bounds on a clause, which the pushed clause has to satisfy
    itself, and `reason_wf`, whose indices still name the same clauses because the push is
    at the end. -/
theorem Solver.wf_push {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    {cls : alloc.vec.Vec cnf.Clause} {c : cnf.Clause}
    (hcls : cls.val = s.clauses.val ++ [c])
    (hshort : c.val.length + 2 ^ 16 ≤ Std.I32.max)
    (hvars : ∀ lit ∈ c.val, lit.var.val < s.value.val.length) :
    Solver.WF { s with clauses := cls } := by
  have hdb : Solver.db { s with clauses := cls } = Solver.db s ++ [c.val] := by
    simp [Solver.db, hcls]
  refine { hwf with db_len := ?_, db_vars := ?_, reason_wf := ?_ }
  · intro d hd
    rw [hdb] at hd
    rcases List.mem_append.mp hd with h | h
    · exact hwf.db_len d h
    · simp only [List.mem_singleton] at h
      rw [h]
      exact hshort
  · intro d hd
    rw [hdb] at hd
    rcases List.mem_append.mp hd with h | h
    · exact hwf.db_vars d h
    · simp only [List.mem_singleton] at h
      rw [h]
      exact hvars
  · intro v r hr
    obtain ⟨d, hd, htrue, hrest⟩ := hwf.reason_wf v r hr
    refine ⟨d, ?_, htrue, hrest⟩
    have hlt : r.val < (Solver.db s).length := by
      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hd
      exact h
    simp only [Solver.clauseAt, hdb]
    rw [List.getElem?_append_left hlt]
    exact hd

/-! #### The search

The one statement that is qualitatively new next to `SatDpll.lean`: the database
*changes* as the search runs, so soundness of the answer cannot be read off the clauses
it was handed. `db₀` is the problem, and "every clause the database holds is entailed by
`db₀`" is the invariant that makes learning sound -- `analyze.spec`'s first conjunct is
one step of it, and this is where that step gets carried across `search`'s calls.

**The invariant is a structure**, like `Solver.Marking` and `Solver.Analyzing` above, and for
the same reason: there are eleven clauses and each step of the loop has to re-establish all
of them. Three of them are about the `u32` counters rather than about the search, and one --
`levels` -- is a fact `Solver.WF` cannot state, since `search` pushes `trail_lim` and only
then assigns, so the state in between has an empty top level.

Each step of the loop then gets a lemma taking the specs' postconditions and giving back the
invariant plus what the measure did. Stating them over two states related by hypotheses,
rather than inside the loop's proof, is what keeps the semantic work separate from the
thirteen-component state the extraction threads around. -/

/-- Opening a level preserves the invariant. -/
theorem Solver.wf_open_level {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    {tlim : alloc.vec.Vec Std.Usize} {k : Std.Usize}
    (htlim : tlim.val = s.trail_lim.val ++ [k])
    (hk : k.val = s.trail.val.length) :
    Solver.WF { s with trail_lim := tlim } := by
  have hdl : Solver.decisionLevel { s with trail_lim := tlim }
      = Solver.decisionLevel s + 1 := by
    simp [Solver.decisionLevel, htlim]
  refine { hwf with level_le := ?_, trail_lim_spec := ?_ }
  · intro v hv
    show Solver.levelOf s v ≤ tlim.val.length
    have h := hwf.level_le v hv
    simp only [Solver.decisionLevel] at h
    rw [htlim]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · show ∀ (j : Nat) (hj : j < tlim.val.length),
      (tlim.val[j]).val ≤ s.trail.val.length ∧
      ∀ (i : Nat) (hi : i < s.trail.val.length),
        (i < (tlim.val[j]).val ↔ Solver.levelOf s s.trail.val[i] ≤ j)
    intro j hj
    have hlen : tlim.val.length = s.trail_lim.val.length + 1 := by
      rw [htlim]; simp
    rcases Nat.lt_or_ge j s.trail_lim.val.length with hlt | hge
    · have hel : tlim.val[j] = (s.trail_lim.val ++ [k])[j]'(by rw [← htlim]; exact hj) :=
        List.getElem_of_eq htlim _
      rw [hel, List.getElem_append_left hlt]
      exact hwf.trail_lim_spec j hlt
    · have hjeq : j = s.trail_lim.val.length := by omega
      subst hjeq
      have hel : tlim.val[s.trail_lim.val.length]
          = (s.trail_lim.val ++ [k])[s.trail_lim.val.length]'(by rw [← htlim]; exact hj) :=
        List.getElem_of_eq htlim _
      rw [hel, List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero, hk]
      refine ⟨Nat.le_refl _, fun i hi => ⟨fun _ => hwf.level_le _ (List.getElem_mem hi),
        fun _ => hi⟩⟩

/-- The conflict counter is not part of the invariant. -/
theorem Solver.wf_conflicts {s : sat_cdcl.Solver} (hwf : Solver.WF s) (c : Std.U32) :
    Solver.WF { s with conflicts := c } := { hwf with }

/-- **The invariant `search`'s loop carries.** -/
structure Solver.Searching (s : sat_cdcl.Solver) (db₀ : List (List cnf.Literal))
    (budget since_restart : Std.U32) : Prop where
  /-- The state is well formed, and small enough for the decision heuristic's cast. -/
  wf : Solver.WF s
  bound : s.value.val.length ≤ 2 ^ 16
  /-- **Learning is sound**: every clause the database holds is entailed by the problem,
      and every clause of the problem is still there. -/
  sound : ∀ cl ∈ Solver.db s, Entails db₀ cl
  problem : ∀ cl ∈ db₀, cl ∈ Solver.db s
  /-- Whatever is falsified was falsified by the level the search is on. -/
  falsified : ∀ cl ∈ Solver.db s, (∀ lit ∈ cl, Solver.litFalse s lit) →
    0 < Solver.decisionLevel s →
    ∃ lit ∈ cl, Solver.levelOf s lit.var = Solver.decisionLevel s
  /-- Every variable of the problem has a slot and is marked, so the heuristic will get
      to it. -/
  vars : ∀ v ∈ cnfVars db₀,
    v.val < s.value.val.length ∧ s.occurs.val[v.val]? = some true
  /-- Every level that is open was opened by a decision. Weaker than it sounds and
      stronger than `Solver.WF`'s `decision_of_level`, which cannot say this: `search`
      pushes `trail_lim` and only then assigns, and the state in between has an empty top
      level. It is an invariant of the loop, not of the state. -/
  levels : ∀ k, 0 < k → k ≤ Solver.decisionLevel s → ∃ v ∈ s.trail.val,
    Solver.levelOf s v = k ∧ Solver.reasonOf s v = none
  /-- The restart budget never shrinks, and 1 is excluded: see `search.spec`. -/
  budget_ge : 2 ≤ budget.val
  /-- Conflicts since the last restart are steps this window has taken, and a window
      cannot take more steps than the trail numeral has room for. -/
  window : since_restart.val + Solver.trailLeft s ≤ 3 ^ s.value.val.length
  /-- The conflict counter has room for every conflict still to come. -/
  room : s.conflicts.val + Solver.searchMeasure s budget ≤ Std.U32.max
  /-- The clause vector has room for every clause still to be learned -- the same
      accounting as `room`, one index wider. -/
  db_room : (Solver.db s).length + Solver.searchMeasure s budget ≤ Std.Usize.max
  /-- And the budget has room to grow. -/
  fits : 2 * 3 ^ s.value.val.length ≤ Std.U32.max

theorem Solver.Searching.conflicts_lt {s : sat_cdcl.Solver} {db₀ : List (List cnf.Literal)}
    {budget since_restart : Std.U32}
    (hinv : Solver.Searching s db₀ budget since_restart) :
    s.conflicts.val < Std.U32.max := by
  have h := hinv.room
  have hpos := Solver.searchMeasure_pos s budget
  omega

theorem Solver.Searching.since_restart_lt {s : sat_cdcl.Solver}
    {db₀ : List (List cnf.Literal)} {budget since_restart : Std.U32}
    (hinv : Solver.Searching s db₀ budget since_restart) :
    since_restart.val < Std.U32.max := by
  have h := hinv.window
  have hf := hinv.fits
  have := Solver.trailNum_lt s
  simp only [Solver.trailLeft] at h
  have h3 : 0 < 3 ^ s.value.val.length := Nat.pow_pos (by omega)
  omega

theorem Solver.Searching.budget_le {s : sat_cdcl.Solver} {db₀ : List (List cnf.Literal)}
    {budget since_restart : Std.U32}
    (hinv : Solver.Searching s db₀ budget since_restart)
    (hguard : budget.val ≤ since_restart.val) :
    budget.val ≤ 3 ^ s.value.val.length := by
  have h := hinv.window
  omega

/-- **Propagation keeps the invariant** and does not climb back down the measure. -/
theorem Solver.Searching.propagate {s s' : sat_cdcl.Solver} {db₀ : List (List cnf.Literal)}
    {budget since_restart : Std.U32}
    (hinv : Solver.Searching s db₀ budget since_restart)
    (hwf' : Solver.WF s')
    (hdb : Solver.db s' = Solver.db s)
    (hdl : Solver.decisionLevel s' = Solver.decisionLevel s)
    (hsuf : ∃ suf, s'.trail.val = s.trail.val ++ suf)
    (hlen : s'.value.val.length = s.value.val.length)
    (hocc : s'.occurs = s.occurs)
    (hconf : s'.conflicts = s.conflicts)
    (hcf' : ∀ cl ∈ Solver.db s', (∀ lit ∈ cl, Solver.litFalse s' lit) →
      0 < Solver.decisionLevel s' →
      ∃ lit ∈ cl, Solver.levelOf s' lit.var = Solver.decisionLevel s')
    (hframe : ∀ v ∈ s.trail.val, Solver.levelOf s' v = Solver.levelOf s v
      ∧ Solver.reasonOf s' v = Solver.reasonOf s v) :
    Solver.Searching s' db₀ budget since_restart
      ∧ Solver.searchMeasure s' budget ≤ Solver.searchMeasure s budget := by
  obtain ⟨suf, hsufeq⟩ := hsuf
  have hle : Solver.trailLeft s' ≤ Solver.trailLeft s :=
    Solver.trailLeft_le_of_trailNum_le hlen
      (Solver.trailNum_le_of_append hwf' hlen hsufeq (fun v hv => (hframe v hv).2))
  have hmeas : Solver.searchMeasure s' budget ≤ Solver.searchMeasure s budget := by
    simp only [Solver.searchMeasure, hlen]
    omega
  refine ⟨?_, hmeas⟩
  refine
    { wf := hwf'
      bound := by rw [hlen]; exact hinv.bound
      sound := by rw [hdb]; exact hinv.sound
      problem := by rw [hdb]; exact hinv.problem
      falsified := hcf'
      vars := ?_
      levels := ?_
      budget_ge := hinv.budget_ge
      window := ?_
      room := ?_
      db_room := ?_
      fits := by rw [hlen]; exact hinv.fits }
  · intro v hv
    obtain ⟨h1, h2⟩ := hinv.vars v hv
    exact ⟨by rw [hlen]; exact h1, by rw [hocc]; exact h2⟩
  · intro k hk hkle
    obtain ⟨v, hv, hvlvl, hvrsn⟩ := hinv.levels k hk (by rw [hdl] at hkle; exact hkle)
    exact ⟨v, by rw [hsufeq]; exact List.mem_append_left _ hv,
      by rw [(hframe v hv).1]; exact hvlvl, by rw [(hframe v hv).2]; exact hvrsn⟩
  · have h := hinv.window
    rw [hlen]
    omega
  · have h := hinv.room
    rw [hconf]
    omega
  · have h := hinv.db_room
    rw [hdb]
    omega

/-- **A restart keeps the invariant**, and pays for the trail it throws away with the
    budget it grows: this is the one step of the loop where the trail numeral goes *down*. -/
theorem Solver.Searching.restart {s s' : sat_cdcl.Solver} {db₀ : List (List cnf.Literal)}
    {budget budget' since_restart : Std.U32}
    (hinv : Solver.Searching s db₀ budget since_restart)
    (hguard : budget.val ≤ since_restart.val)
    (hwf' : Solver.WF s')
    (hdb : Solver.db s' = Solver.db s)
    (hdl : Solver.decisionLevel s' = 0)
    (hlen : s'.value.val.length = s.value.val.length)
    (hocc : s'.occurs = s.occurs)
    (hconf : s'.conflicts = s.conflicts)
    (hbud : budget'.val = budget.val + budget.val / 2) :
    Solver.Searching s' db₀ budget' 0#u32
      ∧ Solver.searchMeasure s' budget' < Solver.searchMeasure s budget := by
  have hmeas : Solver.searchMeasure s' budget' < Solver.searchMeasure s budget :=
    Solver.searchMeasure_lt_of_restart hlen hinv.budget_ge (hinv.budget_le hguard) hbud
  refine ⟨?_, hmeas⟩
  refine
    { wf := hwf'
      bound := by rw [hlen]; exact hinv.bound
      sound := by rw [hdb]; exact hinv.sound
      problem := by rw [hdb]; exact hinv.problem
      falsified := ?_
      vars := ?_
      levels := ?_
      budget_ge := ?_
      window := ?_
      room := ?_
      db_room := ?_
      fits := by rw [hlen]; exact hinv.fits }
  · intro cl _ _ hpos
    rw [hdl] at hpos
    exact absurd hpos (by omega)
  · intro v hv
    obtain ⟨h1, h2⟩ := hinv.vars v hv
    exact ⟨by rw [hlen]; exact h1, by rw [hocc]; exact h2⟩
  · intro k hk hkle
    rw [hdl] at hkle
    exact absurd hkle (by omega)
  · have h := hinv.budget_ge
    omega
  · have h := Solver.trailLeft_le s'
    simpa using h
  · have h := hinv.room
    rw [hconf]
    omega
  · have h := hinv.db_room
    rw [hdb]
    omega

/-- **A decision keeps the invariant** and climbs the trail: one more digit where the
    numeral had a `0`. `hfix` is `propagate`'s answer -- nothing is falsified -- and it is
    what makes the *new* level the only one a falsified clause can mention. -/
theorem Solver.Searching.decide {s s' : sat_cdcl.Solver} {db₀ : List (List cnf.Literal)}
    {budget since_restart : Std.U32} {var : Std.U16}
    (hinv : Solver.Searching s db₀ budget since_restart)
    (hfix : ∀ cl ∈ Solver.db s, ∃ lit ∈ cl, ¬ Solver.litFalse s lit)
    (hfresh : Solver.valueOf s var = none)
    (hwf' : Solver.WF s')
    (hdb : Solver.db s' = Solver.db s)
    (hdl : Solver.decisionLevel s' = Solver.decisionLevel s + 1)
    (htrail : s'.trail.val = s.trail.val ++ [var])
    (hlvl : Solver.levelOf s' var = Solver.decisionLevel s + 1)
    (hrsn : Solver.reasonOf s' var = none)
    (hlen : s'.value.val.length = s.value.val.length)
    (hocc : s'.occurs = s.occurs)
    (hconf : s'.conflicts = s.conflicts)
    (hframe : ∀ w, w ≠ var → Solver.valueOf s' w = Solver.valueOf s w
      ∧ Solver.levelOf s' w = Solver.levelOf s w
      ∧ Solver.reasonOf s' w = Solver.reasonOf s w) :
    Solver.Searching s' db₀ budget since_restart
      ∧ Solver.searchMeasure s' budget < Solver.searchMeasure s budget := by
  have hvarnot : var ∉ s.trail.val := by
    rw [← hinv.wf.trail_iff, hfresh]
    simp
  have hlt : Solver.trailLeft s' < Solver.trailLeft s :=
    Solver.trailLeft_lt_of_trailNum_lt hlen
      (Solver.trailNum_lt_of_assign hwf' hlen htrail
        (fun v hv => (hframe v (fun hc => hvarnot (by rw [← hc]; exact hv))).2.2))
  have hmeas : Solver.searchMeasure s' budget < Solver.searchMeasure s budget :=
    Solver.searchMeasure_lt_of_trailLeft hlen hlt
  refine ⟨?_, hmeas⟩
  refine
    { wf := hwf'
      bound := by rw [hlen]; exact hinv.bound
      sound := by rw [hdb]; exact hinv.sound
      problem := by rw [hdb]; exact hinv.problem
      falsified := ?_
      vars := ?_
      levels := ?_
      budget_ge := hinv.budget_ge
      window := ?_
      room := ?_
      db_room := ?_
      fits := by rw [hlen]; exact hinv.fits }
  -- the only literal that can have become false is the one just decided
  · intro cl hcl hall _
    obtain ⟨lit, hlit, hnf⟩ := hfix cl (by rw [hdb] at hcl; exact hcl)
    have hvareq : lit.var = var := by
      by_contra hne
      exact hnf (by rw [Solver.litFalse, ← (hframe lit.var hne).1]; exact hall lit hlit)
    exact ⟨lit, hlit, by rw [hvareq, hlvl, hdl]⟩
  · intro v hv
    obtain ⟨h1, h2⟩ := hinv.vars v hv
    exact ⟨by rw [hlen]; exact h1, by rw [hocc]; exact h2⟩
  -- the level the decision opened is the one it decided at
  · intro k hk hkle
    rw [hdl] at hkle
    rcases Nat.lt_or_ge k (Solver.decisionLevel s + 1) with hklt | hkge
    · obtain ⟨v, hv, hvlvl, hvrsn⟩ := hinv.levels k hk (by omega)
      have hne : v ≠ var := fun hc => hvarnot (by rw [← hc]; exact hv)
      exact ⟨v, by rw [htrail]; exact List.mem_append_left _ hv,
        by rw [(hframe v hne).2.1]; exact hvlvl, by rw [(hframe v hne).2.2]; exact hvrsn⟩
    · have hkeq : k = Solver.decisionLevel s + 1 := by omega
      exact ⟨var, by rw [htrail]; simp, by rw [hlvl, hkeq], hrsn⟩
  · have h := hinv.window
    rw [hlen]
    omega
  · have h := hinv.room
    rw [hconf]
    omega
  · have h := hinv.db_room
    rw [hdb]
    omega

/-- Only the conflict counter and the activity scores changed, so the trail numeral did not. -/
theorem Solver.trailLeft_congr {s s' : sat_cdcl.Solver}
    (hvalue : s'.value = s.value) (hreason : s'.reason = s.reason)
    (htrail : s'.trail = s.trail) :
    Solver.trailLeft s' = Solver.trailLeft s := by
  have h1 : Solver.trailDigits s' = Solver.trailDigits s := by
    simp [Solver.trailDigits, Solver.reasonOf, hreason, htrail]
  simp only [Solver.trailLeft, Solver.trailNum, h1, hvalue]

/-- And so the measure did not. -/
theorem Solver.searchMeasure_congr {s s' : sat_cdcl.Solver} {budget : Std.U32}
    (hvalue : s'.value = s.value) (hreason : s'.reason = s.reason)
    (htrail : s'.trail = s.trail) :
    Solver.searchMeasure s' budget = Solver.searchMeasure s budget := by
  simp only [Solver.searchMeasure, Solver.trailLeft_congr hvalue hreason htrail, hvalue]

/-- A state that differs from another only in its conflict counter and its activity scores
    agrees with it on every array the invariant reads. -/
theorem Solver.frame_of_conflicts_activity {s s' : sat_cdcl.Solver}
    (h : s' = { s with conflicts := s'.conflicts, activity := s'.activity }) :
    s'.clauses = s.clauses ∧ s'.value = s.value ∧ s'.level = s.level ∧ s'.reason = s.reason
      ∧ s'.phase = s.phase ∧ s'.occurs = s.occurs ∧ s'.seen = s.seen
      ∧ s'.trail = s.trail ∧ s'.trail_lim = s.trail_lim :=
  ⟨by rw [h], by rw [h], by rw [h], by rw [h], by rw [h], by rw [h], by rw [h], by rw [h],
    by rw [h]⟩

/-- **The trail entry a backjump lands on is a decision.** Everything before it is at a
    level at or below `j`, so the decision its own level must have -- `decision_of_level` --
    can only be this entry, since `decision_first` puts that decision before every entry at
    its level and there is none before this one. -/
theorem Solver.decision_at_trail_lim {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    {j : Nat} (hj : j < s.trail_lim.val.length) {tgt : Std.Usize}
    (htgt : s.trail_lim.val[j]? = some tgt) (hlt : tgt.val < s.trail.val.length) :
    Solver.reasonOf s (s.trail.val[tgt.val]) = none := by
  obtain ⟨hb, hiff⟩ := hwf.trail_lim_spec j hj
  have htgteq : s.trail_lim.val[j] = tgt :=
    Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans htgt)
  rw [htgteq] at hiff
  set e := s.trail.val[tgt.val] with he
  have hemem : e ∈ s.trail.val := List.getElem_mem hlt
  -- the entry at `tgt` is above level `j`
  have helvl : ¬ (Solver.levelOf s e ≤ j) := by
    intro hc
    exact absurd ((hiff tgt.val hlt).mpr hc) (by omega)
  have hepos : 0 < Solver.levelOf s e := by omega
  -- its level has a decision, which comes before every entry at that level
  obtain ⟨d, hd, hdlvl, hdrsn⟩ := hwf.decision_of_level e hemem hepos
  have hdfirst := hwf.decision_first d hd (by rw [hdlvl]; exact hepos) hdrsn e hemem hdlvl.symm
  -- and nothing before `tgt` is at that level, so the decision *is* the entry at `tgt`
  have hdidx : tgt.val ≤ s.trail.val.idxOf d := by
    by_contra hc
    have hdlt : s.trail.val.idxOf d < tgt.val := by omega
    have hget : s.trail.val[s.trail.val.idxOf d]'(by
        exact Nat.lt_of_lt_of_le hdlt (Nat.le_of_lt hlt)) = d :=
      List.getElem_idxOf (List.idxOf_lt_length_of_mem hd)
    have := (hiff (s.trail.val.idxOf d) (Nat.lt_of_lt_of_le hdlt (Nat.le_of_lt hlt))).mp hdlt
    rw [hget, hdlvl] at this
    exact helvl this
  have heidx : s.trail.val.idxOf e = tgt.val :=
    Solver.idxOf_eq_of_getElem? hwf.trail_nodup (List.getElem?_eq_getElem hlt)
  have hdeq : s.trail.val.idxOf d = tgt.val := by omega
  have hidxlt : s.trail.val.idxOf d < s.trail.val.length := List.idxOf_lt_length_of_mem hd
  have hgetd : s.trail.val[s.trail.val.idxOf d]? = some d := by
    rw [List.getElem?_eq_getElem hidxlt, List.getElem_idxOf hidxlt]
  rw [hdeq] at hgetd
  have hde : e = d :=
    Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hgetd)
  rw [hde]
  exact hdrsn

/-- The learned clause is short enough for the invariant, and its variables have slots. -/
theorem Solver.learned_ok {s₂ s₄ : sat_cdcl.Solver} {learned : List cnf.Literal}
    (hlfalse : ∀ lit ∈ learned, Solver.litFalse s₂ lit)
    (hlen : learned.length ≤ 2 ^ 16 + 1)
    (h4len : s₄.value.val.length = s₂.value.val.length) :
    learned.length + 2 ^ 16 ≤ Std.I32.max
      ∧ ∀ lit ∈ learned, lit.var.val < s₄.value.val.length := by
  refine ⟨by scalar_tac, ?_⟩
  intro lit hlit
  rw [h4len]
  exact Solver.lt_length_of_litFalse (hlfalse lit hlit)

/-- **Learning the clause and backjumping keeps the invariant, and climbs the trail.** -/
theorem Solver.Searching.learn {s₂ s₄ s₅ : sat_cdcl.Solver} {db₀ : List (List cnf.Literal)}
    {budget since_restart since_restart' : Std.U32} {c : Nat}
    {learned rest : List cnf.Literal} {uip : cnf.Literal} {backjump tgt idx : Std.Usize}
    (hwf₂ : Solver.WF s₂)
    (hbound : s₂.value.val.length ≤ 2 ^ 16)
    (hsound : ∀ cl ∈ Solver.db s₂, Entails db₀ cl)
    (hproblem : ∀ cl ∈ db₀, cl ∈ Solver.db s₂)
    (hcf : ∀ cl ∈ Solver.db s₂, (∀ lit ∈ cl, Solver.litFalse s₂ lit) →
      0 < Solver.decisionLevel s₂ →
      ∃ lit ∈ cl, Solver.levelOf s₂ lit.var = Solver.decisionLevel s₂)
    (hvars : ∀ v ∈ cnfVars db₀,
      v.val < s₂.value.val.length ∧ s₂.occurs.val[v.val]? = some true)
    (hlevels : ∀ k, 0 < k → k ≤ Solver.decisionLevel s₂ → ∃ v ∈ s₂.trail.val,
      Solver.levelOf s₂ v = k ∧ Solver.reasonOf s₂ v = none)
    (hbudget : 2 ≤ budget.val)
    (hfits : 2 * 3 ^ s₂.value.val.length ≤ Std.U32.max)
    (hwindow : since_restart.val + Solver.trailLeft s₂ ≤ 3 ^ s₂.value.val.length)
    (hconf₂ : s₂.conflicts.val = c + 1)
    (hroom : c + Solver.searchMeasure s₂ budget ≤ Std.U32.max)
    (hdbroom : (Solver.db s₂).length + Solver.searchMeasure s₂ budget ≤ Std.Usize.max)
    (hsr : since_restart'.val = since_restart.val + 1)
    (hent : Entails (Solver.db s₂) learned)
    (hlfalse : ∀ lit ∈ learned, Solver.litFalse s₂ lit)
    (hshape : learned = uip :: rest)
    (huiplvl : Solver.levelOf s₂ uip.var = Solver.decisionLevel s₂)
    (hbj : backjump.val < Solver.decisionLevel s₂)
    (hwf₄ : Solver.WF s₄)
    (h4db : Solver.db s₄ = Solver.db s₂)
    (h4len : s₄.value.val.length = s₂.value.val.length)
    (h4occ : s₄.occurs = s₂.occurs)
    (h4conf : s₄.conflicts = s₂.conflicts)
    (h4dl : Solver.decisionLevel s₄ = backjump.val)
    (h4keep : ∀ v ∈ s₂.trail.val, Solver.levelOf s₂ v ≤ backjump.val →
      Solver.valueOf s₄ v = Solver.valueOf s₂ v ∧ Solver.levelOf s₄ v = Solver.levelOf s₂ v)
    (h4drop : ∀ v ∈ s₂.trail.val, backjump.val < Solver.levelOf s₂ v →
      Solver.valueOf s₄ v = none)
    (htgt : s₂.trail_lim.val[backjump.val]? = some tgt)
    (h4trail : s₄.trail.val = s₂.trail.val.take tgt.val)
    (h4rsn : ∀ v ∈ s₄.trail.val, Solver.reasonOf s₄ v = Solver.reasonOf s₂ v)
    (hwf₅ : Solver.WF s₅)
    (h5db : Solver.db s₅ = Solver.db s₄ ++ [learned])
    (h5dl : Solver.decisionLevel s₅ = Solver.decisionLevel s₄)
    (h5trail : s₅.trail.val = s₄.trail.val ++ [uip.var])
    (h5lvl : Solver.levelOf s₅ uip.var = Solver.decisionLevel s₄)
    (h5rsn : Solver.reasonOf s₅ uip.var = some idx)
    (h5len : s₅.value.val.length = s₄.value.val.length)
    (h5occ : s₅.occurs = s₄.occurs)
    (h5conf : s₅.conflicts = s₄.conflicts)
    (h5frame : ∀ w, w ≠ uip.var → Solver.valueOf s₅ w = Solver.valueOf s₄ w
      ∧ Solver.levelOf s₅ w = Solver.levelOf s₄ w
      ∧ Solver.reasonOf s₅ w = Solver.reasonOf s₄ w) :
    Solver.Searching s₅ db₀ budget since_restart'
      ∧ Solver.searchMeasure s₅ budget < Solver.searchMeasure s₂ budget := by
  have hlen5 : s₅.value.val.length = s₂.value.val.length := by rw [h5len, h4len]
  have hdl5 : Solver.decisionLevel s₅ = backjump.val := by rw [h5dl, h4dl]
  have huipmem : uip.var ∈ s₂.trail.val :=
    Solver.mem_trail_of_litFalse hwf₂ (hlfalse uip (by rw [hshape]; simp))
  have huipnone : Solver.valueOf s₄ uip.var = none :=
    h4drop uip.var huipmem (by rw [huiplvl]; exact hbj)
  have huipnot4 : uip.var ∉ s₄.trail.val := by
    rw [← hwf₄.trail_iff, huipnone]
    simp
  -- everything `s₄` has assigned, `s₂` had assigned at a level at or below the backjump
  have hsub4 : ∀ v : Std.U16, (Solver.valueOf s₄ v).isSome = true →
      Solver.levelOf s₂ v ≤ backjump.val ∧ Solver.valueOf s₄ v = Solver.valueOf s₂ v := by
    intro v hv
    have hv4 : v ∈ s₄.trail.val := (hwf₄.trail_iff v).mp hv
    have hv2 : v ∈ s₂.trail.val := by
      rw [h4trail] at hv4
      exact List.mem_of_mem_take hv4
    have hle : Solver.levelOf s₂ v ≤ backjump.val := by
      by_contra hc
      rw [h4drop v hv2 (by omega)] at hv
      simp at hv
    exact ⟨hle, (h4keep v hv2 hle).1⟩
  -- **nothing is falsified after the backjump**: a clause false now was false before, and
  -- `hcf` says it had a literal at the level the backjump just threw away
  have hfix4 : ∀ cl ∈ Solver.db s₄, ∃ lit ∈ cl, ¬ Solver.litFalse s₄ lit := by
    intro cl hcl
    by_contra hc
    push Not at hc
    have hall2 : ∀ lit ∈ cl, Solver.litFalse s₂ lit := by
      intro lit hlit
      have h4 : Solver.valueOf s₄ lit.var = some lit.negated := hc lit hlit
      have hframe := (hsub4 lit.var (by rw [h4]; simp)).2
      show Solver.valueOf s₂ lit.var = some lit.negated
      rw [← hframe]
      exact h4
    obtain ⟨lit, hlit, hlvl⟩ := hcf cl (by rw [h4db] at hcl; exact hcl) hall2 (by omega)
    have hmem := Solver.mem_trail_of_litFalse hwf₂ (hall2 lit hlit)
    have hnone := h4drop lit.var hmem (by rw [hlvl]; exact hbj)
    have h4 : Solver.valueOf s₄ lit.var = some lit.negated := hc lit hlit
    rw [hnone] at h4
    simp at h4
  -- the prefix the backjump keeps stops strictly inside the trail
  have hjlt : backjump.val < s₂.trail_lim.val.length := by
    simpa [Solver.decisionLevel] using hbj
  have htgtlt : tgt.val < s₂.trail.val.length := by
    obtain ⟨hb, hiff⟩ := hwf₂.trail_lim_spec backjump.val hjlt
    have htgteq : s₂.trail_lim.val[backjump.val] = tgt :=
      Option.some.inj ((List.getElem?_eq_getElem hjlt).symm.trans htgt)
    rw [htgteq] at hiff hb
    have hidx : s₂.trail.val.idxOf uip.var < s₂.trail.val.length :=
      List.idxOf_lt_length_of_mem huipmem
    have hget : s₂.trail.val[s₂.trail.val.idxOf uip.var]'hidx = uip.var :=
      List.getElem_idxOf hidx
    by_contra hc
    have hle := (hiff (s₂.trail.val.idxOf uip.var) hidx).mp (by omega)
    rw [hget, huiplvl] at hle
    omega
  have hdec := Solver.decision_at_trail_lim hwf₂ hjlt htgt htgtlt
  have h5rsnframe : ∀ v ∈ s₂.trail.val.take tgt.val,
      Solver.reasonOf s₅ v = Solver.reasonOf s₂ v := by
    intro v hv
    have hv4 : v ∈ s₄.trail.val := by rw [h4trail]; exact hv
    have hne : v ≠ uip.var := fun hc => huipnot4 (by rw [← hc]; exact hv4)
    rw [(h5frame v hne).2.2, h4rsn v hv4]
  have hlt5 : Solver.trailLeft s₅ < Solver.trailLeft s₂ :=
    Solver.trailLeft_lt_of_trailNum_lt hlen5
      (Solver.trailNum_lt_of_backjump hwf₂ hlen5 htgtlt hdec
        (by rw [h5trail, h4trail]) (by rw [h5rsn]; simp) h5rsnframe)
  have hmeas : Solver.searchMeasure s₅ budget < Solver.searchMeasure s₂ budget :=
    Solver.searchMeasure_lt_of_trailLeft hlen5 hlt5
  refine ⟨?_, hmeas⟩
  refine
    { wf := hwf₅
      bound := by rw [hlen5]; exact hbound
      sound := ?_
      problem := ?_
      falsified := ?_
      vars := ?_
      levels := ?_
      budget_ge := hbudget
      window := ?_
      room := ?_
      db_room := ?_
      fits := by rw [hlen5]; exact hfits }
  -- the learned clause is entailed by the problem, so learning stays sound
  · intro cl hcl
    rw [h5db, h4db] at hcl
    rcases List.mem_append.mp hcl with h | h
    · exact hsound cl h
    · simp only [List.mem_singleton] at h
      rw [h]
      exact Entails.trans hsound hent
  · intro cl hcl
    rw [h5db, h4db]
    exact List.mem_append_left _ (hproblem cl hcl)
  -- a clause falsified now mentions the variable the assertion just assigned
  · intro cl hcl hall hpos
    by_cases hmem : ∃ lit ∈ cl, lit.var = uip.var
    · obtain ⟨lit, hlit, hlv⟩ := hmem
      exact ⟨lit, hlit, by rw [hlv, h5lvl, hdl5, h4dl]⟩
    · exfalso
      push Not at hmem
      have hcl4 : cl ∈ Solver.db s₄ := by
        rw [h5db] at hcl
        rcases List.mem_append.mp hcl with h | h
        · exact h
        · simp only [List.mem_singleton] at h
          exact absurd (hmem uip (by rw [h, hshape]; simp)) (by simp)
      obtain ⟨lit, hlit, hnf⟩ := hfix4 cl hcl4
      refine hnf ?_
      show Solver.valueOf s₄ lit.var = some lit.negated
      rw [← (h5frame lit.var (hmem lit hlit)).1]
      exact hall lit hlit
  · intro v hv
    obtain ⟨h1, h2⟩ := hvars v hv
    exact ⟨by rw [hlen5]; exact h1, by rw [h5occ, h4occ]; exact h2⟩
  -- every level still open is at or below the backjump, so its decision was kept
  · intro k hk hkle
    rw [hdl5] at hkle
    obtain ⟨v, hv, hvlvl, hvrsn⟩ := hlevels k hk (by omega)
    have hvle : Solver.levelOf s₂ v ≤ backjump.val := by rw [hvlvl]; exact hkle
    obtain ⟨hval, hlvl⟩ := h4keep v hv hvle
    have hv4 : v ∈ s₄.trail.val := by
      refine (hwf₄.trail_iff v).mp ?_
      rw [hval]
      exact (hwf₂.trail_iff v).mpr hv
    have hne : v ≠ uip.var := fun hc => huipnot4 (by rw [← hc]; exact hv4)
    refine ⟨v, by rw [h5trail]; exact List.mem_append_left _ hv4, ?_, ?_⟩
    · rw [(h5frame v hne).2.1, hlvl, hvlvl]
    · rw [(h5frame v hne).2.2, h4rsn v hv4, hvrsn]
  · rw [hlen5, hsr]
    omega
  · rw [h5conf, h4conf, hconf₂]
    omega
  · have hlen : (Solver.db s₅).length = (Solver.db s₂).length + 1 := by
      rw [h5db, h4db]
      simp
    rw [hlen]
    omega

/-- **A level begins no earlier than its own index.** While every open level has a decision,
    `trail_lim` is strictly increasing -- level `j + 1`'s decision lies at or after where
    level `j + 1` begins and strictly before where level `j + 2` does -- so there cannot be
    more open levels than trail entries. -/
theorem Solver.le_trail_lim {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    (hlevels : ∀ k, 0 < k → k ≤ Solver.decisionLevel s → ∃ v ∈ s.trail.val,
      Solver.levelOf s v = k ∧ Solver.reasonOf s v = none) :
    ∀ (j : Nat) (hj : j < s.trail_lim.val.length), j ≤ (s.trail_lim.val[j]).val := by
  intro j
  induction j with
  | zero => intro _; omega
  | succ m ih =>
    intro hj
    have hmlt : m < s.trail_lim.val.length := by omega
    have hmle := ih hmlt
    -- level `m + 1` has a decision somewhere on the trail
    obtain ⟨v, hv, hvlvl, -⟩ := hlevels (m + 1) (by omega)
      (by simp only [Solver.decisionLevel]; omega)
    have hidx : s.trail.val.idxOf v < s.trail.val.length :=
      List.idxOf_lt_length_of_mem hv
    have hget : s.trail.val[s.trail.val.idxOf v]'hidx = v := List.getElem_idxOf hidx
    obtain ⟨-, hiffm⟩ := hwf.trail_lim_spec m hmlt
    obtain ⟨-, hiffs⟩ := hwf.trail_lim_spec (m + 1) hj
    -- it is at or after where level `m + 1` begins, and strictly before the next
    have h1 : ¬ (s.trail.val.idxOf v < (s.trail_lim.val[m]).val) := by
      intro hc
      have := (hiffm _ hidx).mp hc
      rw [hget, hvlvl] at this
      omega
    have h2 : s.trail.val.idxOf v < (s.trail_lim.val[m + 1]).val := by
      refine (hiffs _ hidx).mpr ?_
      rw [hget, hvlvl]
    omega

/-- **There are no more open levels than trail entries.** -/
theorem Solver.decisionLevel_le_trail {s : sat_cdcl.Solver} (hwf : Solver.WF s)
    (hlevels : ∀ k, 0 < k → k ≤ Solver.decisionLevel s → ∃ v ∈ s.trail.val,
      Solver.levelOf s v = k ∧ Solver.reasonOf s v = none) :
    Solver.decisionLevel s ≤ s.trail.val.length := by
  rcases Nat.eq_zero_or_pos (Solver.decisionLevel s) with h0 | hpos
  · omega
  · have hlt : Solver.decisionLevel s - 1 < s.trail_lim.val.length := by
      simp only [Solver.decisionLevel] at hpos ⊢
      omega
    have hge := Solver.le_trail_lim hwf hlevels _ hlt
    obtain ⟨v, hv, hvlvl, -⟩ := hlevels (Solver.decisionLevel s) hpos (Nat.le_refl _)
    have hidx : s.trail.val.idxOf v < s.trail.val.length :=
      List.idxOf_lt_length_of_mem hv
    have hget : s.trail.val[s.trail.val.idxOf v]'hidx = v := List.getElem_idxOf hidx
    obtain ⟨-, hiff⟩ := hwf.trail_lim_spec _ hlt
    have h1 : ¬ (s.trail.val.idxOf v < (s.trail_lim.val[Solver.decisionLevel s - 1]).val) := by
      intro hc
      have := (hiff _ hidx).mp hc
      rw [hget, hvlvl] at this
      omega
    have key : Solver.decisionLevel s - 1 ≤ s.trail.val.idxOf v :=
      le_trans hge (Nat.le_of_not_lt h1)
    omega

/-- **The CDCL loop, as the extraction leaves it**: one recursive function taking the state,
    the restart budget and the conflicts since the last restart. The invariant is
    `Solver.Searching`; the four steps above are its four branches, and `termination_by` is
    the measure.

    What each branch does with the answer: `propagate` returning `None` with nothing left for
    `pick_branch_var` is the `true` answer (`Solver.model_of_fixpoint`); a conflict at level 0
    is the `false` answer (`Solver.unsat_of_conflict_level_zero'`); everything else recurses
    on a state the measure says is closer to done. -/
theorem sat_cdcl.Solver.search_loop.spec (s : sat_cdcl.Solver)
    (budget since_restart : Std.U32) (db₀ : List (List cnf.Literal))
    (hinv : Solver.Searching s db₀ budget since_restart) :
    sat_cdcl.Solver.search_loop s budget since_restart ⦃
      (sat : Bool) (s' : sat_cdcl.Solver) =>
        Solver.WF s'
        ∧ (∀ cl ∈ Solver.db s', Entails db₀ cl)
        ∧ s'.value.val.length = s.value.val.length
        ∧ (sat = true →
            (∀ v ∈ cnfVars db₀, (Solver.valueOf s' v).isSome = true)
            ∧ ∀ w : Std.U16 → Bool,
                (∀ v b, Solver.valueOf s' v = some b → w v = b) →
                Cnf.eval w db₀ = true)
        ∧ (sat = false → ∀ w : Std.U16 → Bool, Cnf.eval w db₀ ≠ true) ⦄ := by
  unfold sat_cdcl.Solver.search_loop
  step with (sat_cdcl.Solver.propagate.spec s hinv.wf hinv.falsified
    (fun hpos => hinv.levels _ hpos (Nat.le_refl _)))
  obtain ⟨hinv1, hm1⟩ := hinv.propagate o_post1 o_post2 o_post3 ⟨_, o_post4⟩ o_post8
    o_post9 o_post10 o_post11 o_post12
  step*
  -- the restart
  · step with (sat_cdcl.Solver.backtrack.spec self1 0#usize hinv1.wf)
    have hguard : budget.val ≤ since_restart.val := by
      have hbr : since_restart ≥ budget := ‹since_restart ≥ budget›
      scalar_tac
    have hbudle : budget.val ≤ 3 ^ self1.value.val.length := hinv1.budget_le hguard
    have hfits := hinv1.fits
    step
    step
    obtain ⟨hinv2, hdec0⟩ := hinv1.restart hguard self2_post1 self2_post2
      (by rw [self2_post7]; simp) self2_post5 self2_post6 self2_post10
      (by rw [budget1_post, i_post])
    have hdec : Solver.searchMeasure self2 budget1 < Solver.searchMeasure s budget :=
      Nat.lt_of_lt_of_le hdec0 hm1
    step with (sat_cdcl.Solver.search_loop.spec self2 budget1 0#u32 db₀ hinv2)
    exact ⟨sat_post1, sat_post2, by rw [sat_post3, self2_post5, o_post8], sat_post4,
      sat_post5⟩
  -- the decision heuristic's cast has room
  · exact hinv1.bound
  -- **the `true` answer**: propagation reached a fixpoint and the heuristic found nothing
  -- left to assign, so what is in `value` is a model of the problem
  · have hassigned : ∀ v ∈ cnfVars db₀, (Solver.valueOf self1 v).isSome = true := by
      intro v hv
      obtain ⟨h1, h2⟩ := hinv1.vars v hv
      refine o1_post2 ?_ v h1 h2
      assumption
    refine ⟨hinv1.wf, hinv1.sound, o_post8, fun _ => ⟨hassigned, ?_⟩, by simp⟩
    intro w hw
    exact Solver.model_of_fixpoint hinv1.problem (o_post7 (by assumption)) hassigned w hw
  -- `trail_lim` has room for another level: there are no more open levels than trail
  -- entries, and the trail holds at most one variable each
  · have h1 := Solver.decisionLevel_le_trail hinv1.wf hinv1.levels
    have h2 := Solver.trail_length_le hinv1.wf
    simp only [Solver.decisionLevel] at h1
    scalar_tac
  -- the saved phase of the variable the heuristic picked
  · obtain ⟨hvlt, -⟩ := o1_post1 v (by assumption)
    have hi1 : i1.val = v.val := by rw [i1_post]; simp
    rw [hi1, hinv1.wf.phase_length]
    exact hvlt
  -- **a decision**: open a level, then assign the variable the heuristic picked at it
  · obtain ⟨hvlt, hvnone⟩ := o1_post1 v (by assumption)
    have hdlopen : Solver.decisionLevel { self1 with trail_lim := v1 }
        = Solver.decisionLevel self1 + 1 := by
      simp [Solver.decisionLevel, v1_post]
    have hwfopen : Solver.WF { self1 with trail_lim := v1 } :=
      Solver.wf_open_level hinv1.wf v1_post (by rw [i_post])
    step with (sat_cdcl.Solver.assign.spec { self1 with trail_lim := v1 } v value
      core.option.Option.None hwfopen hvlt hvnone
      (fun _ => ⟨by rw [hdlopen]; omega, fun w hw => by
        have h := hinv1.wf.level_le w hw
        show Solver.levelOf self1 w < Solver.decisionLevel { self1 with trail_lim := v1 }
        rw [hdlopen]
        omega⟩)
      (by simp) (by simp))
    obtain ⟨hinv2, hdec0⟩ := hinv1.decide (o_post7 (by assumption)) hvnone self2_post1
      self2_post2 (by rw [self2_post3, hdlopen]) self2_post4
      (by rw [self2_post6, hdlopen]) self2_post11 self2_post7 self2_post9 self2_post10
      self2_post8
    have hdec : Solver.searchMeasure self2 budget < Solver.searchMeasure s budget :=
      Nat.lt_of_lt_of_le hdec0 hm1
    step with (sat_cdcl.Solver.search_loop.spec self2 budget since_restart db₀ hinv2)
    exact ⟨sat_post1, sat_post2, by rw [sat_post3, self2_post7, o_post8], sat_post4,
      sat_post5⟩
  -- the conflict counter has room for this conflict
  · have h := hinv1.conflicts_lt
    scalar_tac
  -- and so has the count since the last restart
  · have h := hinv1.since_restart_lt
    scalar_tac
  · simp [sat_cdcl.DECAY_INTERVAL]
  -- **a conflict**
  · step with (sat_cdcl.Solver.decay_if.spec { self1 with conflicts := i }
      (Solver.wf_conflicts hinv1.wf i) (i1 = 0#u32))
    -- the arrays are `self1`'s; only the counter and the scores moved
    have hconf2 : self2.conflicts = i := by rw [self2_post2]
    have hfr2 : self2
        = { self1 with conflicts := self2.conflicts, activity := self2.activity } := by
      rw [hconf2]; exact self2_post2
    obtain ⟨hc2, hv2, hl2, hr2, hp2, ho2, hs2, ht2, htl2⟩ :=
      Solver.frame_of_conflicts_activity hfr2
    have hdb2 : Solver.db self2 = Solver.db self1 := by simp [Solver.db, hc2]
    have hdl2 : Solver.decisionLevel self2 = Solver.decisionLevel self1 := by
      simp [Solver.decisionLevel, htl2]
    have hval2 : ∀ w, Solver.valueOf self2 w = Solver.valueOf self1 w := by
      intro w; simp [Solver.valueOf, hv2]
    have hlvl2 : ∀ w, Solver.levelOf self2 w = Solver.levelOf self1 w := by
      intro w; simp [Solver.levelOf, hl2]
    have hrsn2 : ∀ w, Solver.reasonOf self2 w = Solver.reasonOf self1 w := by
      intro w; simp [Solver.reasonOf, hr2]
    have hlf2 : ∀ l : cnf.Literal, Solver.litFalse self2 l ↔ Solver.litFalse self1 l := by
      intro l; simp [Solver.litFalse, hval2]
    have hcat2 : ∀ k, Solver.clauseAt self2 k = Solver.clauseAt self1 k := by
      intro k; simp [Solver.clauseAt, hdb2]
    have hmeas2 : Solver.searchMeasure self2 budget = Solver.searchMeasure self1 budget :=
      Solver.searchMeasure_congr hv2 hr2 ht2
    step*
    -- **the `false` answer**: a conflict with no decision above it is a refutation
    · obtain ⟨ccl, hccl, hcclfalse, -⟩ := o_post6 conflict (by assumption)
      have hdl0 : Solver.decisionLevel self2 = 0 := by
        have hbr : i2 = 0#usize := ‹i2 = 0#usize›
        rw [← i2_post, hbr]
        simp
      refine ⟨self2_post1, ?_, by rw [hv2, o_post8], by simp, fun _ w => ?_⟩
      · rw [hdb2]
        exact hinv1.sound
      · refine Solver.unsat_of_conflict_level_zero' (cl := ccl) self2_post1 ?_ hdl0 ?_ ?_ w
        · rw [hdb2]; exact hinv1.sound
        · rw [hdb2]
          exact Solver.mem_db_of_clauseAt hccl
        · intro lit hlit
          exact (hlf2 lit).mpr (hcclfalse lit hlit)
    -- **a conflict above level 0**: analyse it, learn, backjump, assert
    · obtain ⟨ccl, hccl, hcclfalse, hccllvl⟩ := o_post6 conflict (by assumption)
      have hlevel : 0 < Solver.decisionLevel self2 := by
        have hbr : ¬ (i2 = 0#usize) := ‹¬ (i2 = 0#usize)›
        have hne : i2.val ≠ 0 := fun hc => hbr (Solver.uscalar_eq_of_val (by simpa using hc))
        omega
      step with (sat_cdcl.Solver.analyze.spec self2 conflict self2_post1 hlevel
        ⟨ccl, by rw [hcat2]; exact hccl, fun l hl => (hlf2 l).mpr (hcclfalse l hl), by
          obtain ⟨l, hl, hlvl⟩ := hccllvl (by rw [hdl2] at hlevel; exact hlevel)
          exact ⟨l, hl, by rw [hlvl2, hdl2]; exact hlvl⟩⟩)
      -- `analyze` moved only the activity scores
      have hwf3 : Solver.WF self3 :=
        Solver.wf_of_activity_eq self2_post1 learned_post8 learned_post10
      have hv3 : self3.value = self2.value := by rw [learned_post8]
      have hl3 : self3.level = self2.level := by rw [learned_post8]
      have hr3 : self3.reason = self2.reason := by rw [learned_post8]
      have hc3 : self3.clauses = self2.clauses := by rw [learned_post8]
      have ht3 : self3.trail = self2.trail := by rw [learned_post8]
      have htl3 : self3.trail_lim = self2.trail_lim := by rw [learned_post8]
      have ho3 : self3.occurs = self2.occurs := by rw [learned_post8]
      have hcl3 : self3.conflicts = self2.conflicts := by rw [learned_post8]
      have hdb3 : Solver.db self3 = Solver.db self2 := by simp [Solver.db, hc3]
      have hdl3 : Solver.decisionLevel self3 = Solver.decisionLevel self2 := by
        simp [Solver.decisionLevel, htl3]
      have hval3 : ∀ w, Solver.valueOf self3 w = Solver.valueOf self2 w := by
        intro w; simp [Solver.valueOf, hv3]
      have hlvl3 : ∀ w, Solver.levelOf self3 w = Solver.levelOf self2 w := by
        intro w; simp [Solver.levelOf, hl3]
      have hrsn3 : ∀ w, Solver.reasonOf self3 w = Solver.reasonOf self2 w := by
        intro w; simp [Solver.reasonOf, hr3]
      step with (sat_cdcl.Solver.backtrack.spec self3 backjump hwf3)
      step*
      -- the clause vector has room for the learned clause
      · have h := hinv1.db_room
        have hpos := Solver.searchMeasure_pos self1 budget
        have hdblen : (Solver.db self4).length = (Solver.db self1).length := by
          rw [self4_post2, hdb3, hdb2]
        simp only [Solver.db, List.length_map] at hdblen h
        omega
      · -- name the learned clause's head, which is the literal the assertion assigns
        obtain ⟨uip, rest, hshape, huiplvl, hrestpos, hrestlvl⟩ :
            ∃ uip rest, learned.val = uip :: rest
              ∧ Solver.levelOf self2 uip.var = Solver.decisionLevel self2
              ∧ (∀ lit ∈ rest, 0 < Solver.levelOf self2 lit.var)
              ∧ (∀ lit ∈ rest, Solver.levelOf self2 lit.var ≤ backjump.val) :=
          ⟨_, _, learned_post3, learned_post4, learned_post5, learned_post6⟩
        have hluip : l = uip := by
          rw [hshape] at l_post
          simpa using l_post.symm
        have hasserting : asserting = uip := by rw [asserting_post, hluip]
        have h4len : self4.value.val.length = self2.value.val.length := by
          rw [self4_post5, hv3]
        obtain ⟨hshort, hlvars⟩ := Solver.learned_ok learned_post2 learned_post9 h4len
        have hwfpush : Solver.WF { self4 with clauses := v } :=
          Solver.wf_push self4_post1 v_post hshort hlvars
        have huipmem2 : uip.var ∈ self2.trail.val :=
          Solver.mem_trail_of_litFalse self2_post1 (learned_post2 uip (by rw [hshape]; simp))
        have hdl4 : Solver.decisionLevel self4 = backjump.val := by
          rw [self4_post7, hdl3]
          omega
        have huipfresh : Solver.valueOf self4 uip.var = none :=
          self4_post9 uip.var (by rw [ht3]; exact huipmem2)
            (by rw [hlvl3, huiplvl]; exact learned_post7)
        -- the level the backjump lands on still has its decision
        have hopen4 : 0 < backjump.val → ∃ w ∈ self4.trail.val,
            Solver.levelOf self4 w = backjump.val ∧ Solver.reasonOf self4 w = none := by
          intro hpos
          have hble : backjump.val ≤ Solver.decisionLevel self1 := by
            rw [← hdl2]
            omega
          obtain ⟨w, hw, hwlvl, hwrsn⟩ := hinv1.levels backjump.val hpos hble
          have hw3 : w ∈ self3.trail.val := by rw [ht3, ht2]; exact hw
          obtain ⟨hwval, hwlvl4⟩ := self4_post8 w hw3 (by simp [hlvl3, hlvl2, hwlvl])
          have hw4 : w ∈ self4.trail.val := by
            refine (self4_post1.trail_iff w).mp ?_
            rw [hwval, hval3, hval2]
            exact (hinv1.wf.trail_iff w).mpr hw
          exact ⟨w, hw4, by rw [hwlvl4, hlvl3, hlvl2, hwlvl],
            by rw [self4_post12 w hw4, hrsn3, hrsn2]; exact hwrsn⟩
        -- the learned clause is the reason the assertion records, and it is unit on the UIP
        have hdbpush : Solver.db { self4 with clauses := v }
            = Solver.db self4 ++ [learned.val] := by
          simp [Solver.db, v_post]
        have hidxeq : idx.val = (Solver.db self4).length := by
          rw [idx_post]; simp [Solver.db]
        have hclauseat : Solver.clauseAt { self4 with clauses := v } idx = some learned.val := by
          simp only [Solver.clauseAt, hdbpush, hidxeq]
          simp
        have hlitassert :
            cnf.Literal.mk asserting.var (!(decide (¬ asserting.negated = true))) = uip := by
          have h : (!(decide (¬ asserting.negated = true))) = asserting.negated := by
            cases asserting.negated <;> simp
          rw [h, hasserting]
        have hunit4 : ∀ lit ∈ learned.val, lit ≠ uip → Solver.litFalse self4 lit := by
          intro lit hlit hne
          have hrest : lit ∈ rest := by
            rw [hshape] at hlit
            rcases List.mem_cons.mp hlit with h | h
            · exact absurd h hne
            · exact h
          have hf2 : Solver.litFalse self2 lit := learned_post2 lit hlit
          have hmem : lit.var ∈ self2.trail.val := Solver.mem_trail_of_litFalse self2_post1 hf2
          obtain ⟨hv4, -⟩ := self4_post8 lit.var (by rw [ht3]; exact hmem)
            (by rw [hlvl3]; exact hrestlvl lit hrest)
          show Solver.valueOf self4 lit.var = some lit.negated
          rw [hv4, hval3]
          exact hf2
        step with (sat_cdcl.Solver.assign.spec { self4 with clauses := v } asserting.var
          (decide (¬ asserting.negated = true)) (core.option.Option.Some idx) hwfpush
          (by rw [hasserting]; exact hlvars uip (by rw [hshape]; simp))
          (by rw [hasserting]; exact huipfresh)
          (by simp)
          (fun r hr hpos => by
            have hpos4 : 0 < backjump.val := by rw [← hdl4]; exact hpos
            obtain ⟨w, hw4, hwlvl, hwrsn⟩ := hopen4 hpos4
            refine ⟨w, hw4, ?_, hwrsn⟩
            show Solver.levelOf self4 w = Solver.decisionLevel self4
            rw [hwlvl, hdl4])
          (fun r hr => ⟨learned.val, by injection hr with h; rw [← h]; exact hclauseat,
            by rw [hlitassert, hshape]; simp,
            fun lit hlit hne => hunit4 lit hlit (by rw [← hlitassert]; exact hne)⟩))
        -- where the prefix the backjump kept ends
        obtain ⟨tgt, htgt⟩ : ∃ tgt, self2.trail_lim.val[backjump.val]? = some tgt := by
          have hlt : backjump.val < self2.trail_lim.val.length := by
            simpa [Solver.decisionLevel] using learned_post7
          exact ⟨_, List.getElem?_eq_getElem hlt⟩
        obtain ⟨hinv2, hdec0⟩ := Solver.Searching.learn self2_post1
          (by rw [hv2]; exact hinv1.bound) (by rw [hdb2]; exact hinv1.sound)
          (by rw [hdb2]; exact hinv1.problem)
          (by
            intro cl hcl hall hpos
            rw [hdb2] at hcl
            rw [hdl2] at hpos ⊢
            obtain ⟨lit, hlit, hlvl⟩ := hinv1.falsified cl hcl
              (fun lit hlit => (hlf2 lit).mp (hall lit hlit)) hpos
            exact ⟨lit, hlit, by rw [hlvl2]; exact hlvl⟩)
          (by
            intro w hw
            obtain ⟨h1, h2⟩ := hinv1.vars w hw
            exact ⟨by rw [hv2]; exact h1, by rw [ho2]; exact h2⟩)
          (by
            intro k hk hkle
            rw [hdl2] at hkle
            obtain ⟨w, hw, hwlvl, hwrsn⟩ := hinv1.levels k hk hkle
            exact ⟨w, by rw [ht2]; exact hw, by rw [hlvl2]; exact hwlvl,
              by rw [hrsn2]; exact hwrsn⟩)
          hinv1.budget_ge (by rw [hv2]; exact hinv1.fits)
          (by
            have h := hinv1.window
            have htleq : Solver.trailLeft self2 = Solver.trailLeft self1 :=
              Solver.trailLeft_congr hv2 hr2 ht2
            rw [hv2, htleq]
            exact h)
          (by rw [hconf2, i_post]) (by rw [hmeas2]; exact hinv1.room)
          (by rw [hdb2, hmeas2]; exact hinv1.db_room)
          since_restart1_post learned_post1 learned_post2 hshape huiplvl learned_post7
          self4_post1 (by rw [self4_post2, hdb3]) h4len (by rw [self4_post6, ho3])
          (by rw [self4_post10, hcl3]) hdl4
          (fun w hw hle => by
            obtain ⟨h1, h2⟩ := self4_post8 w (by rw [ht3]; exact hw) (by rw [hlvl3]; exact hle)
            exact ⟨by rw [h1, hval3], by rw [h2, hlvl3]⟩)
          (fun w hw hgt => self4_post9 w (by rw [ht3]; exact hw) (by rw [hlvl3]; exact hgt))
          htgt (by rw [self4_post11 tgt (by rw [htl3]; exact htgt), ht3])
          (fun w hw => by rw [self4_post12 w hw, hrsn3])
          self5_post1 (by rw [self5_post2, hdbpush]) self5_post3
          (by rw [self5_post4, hasserting]) (by rw [← hasserting]; exact self5_post6)
          (by rw [← hasserting]; exact self5_post12 idx rfl) self5_post7 self5_post9
          self5_post10 (by rw [← hasserting]; exact self5_post8)
        have hdec : Solver.searchMeasure self5 budget < Solver.searchMeasure s budget := by
          rw [hmeas2] at hdec0
          exact Nat.lt_of_lt_of_le hdec0 hm1
        step with (sat_cdcl.Solver.search_loop.spec self5 budget since_restart1 db₀ hinv2)
        exact ⟨sat_post1, sat_post2,
          by rw [sat_post3, self5_post7, self4_post5, hv3, hv2, o_post8], sat_post4, sat_post5⟩
termination_by Solver.searchMeasure s budget

/-- **The CDCL loop.** Given a well-formed state whose database is sound for `db₀`, with
    nothing falsified and every variable of `db₀` present and marked in `occurs`,
    `search` returns whether `db₀` is satisfiable -- and on `true` the assignment in
    `value` is a model of it, total on `db₀`'s variables.

    Both directions run through the invariant rather than around it. On `false`, the
    search hit a conflict at level 0: the clause it conflicts on is entailed by `db₀` and
    false under an assignment forced by `db₀` alone, so `db₀` has no model. On `true`,
    `propagate` reached a fixpoint and `pick_branch_var` found nothing left, so every
    clause holds a literal that is not false and every variable is assigned -- which
    makes the not-false literal true.

    The restarts are why this is not a statement about one descent: `backtrack 0`
    abandons the trail and the loop starts over with a larger budget, keeping the
    clauses and the phases. That is also where the termination argument lives, and it is
    the one thing here `SatDpll.lean` has no analogue for.

    Six hypotheses this statement did not have. Three of them make it false as it was
    written:

    * `hbound`: `pick_branch_var` scans the slot arrays in `usize` and casts the index down
      to the `u16` a variable is, so without `value.len() ≤ 2 ^ 16` the variable `search`
      decides on need not be the one the heuristic chose.
    * `hroom`: `self.conflicts += 1` is *checked* `u32` arithmetic in the extraction, so a
      state whose counter is near `u32::MAX` makes the call fail -- and a `⦃ ⦄` triple rules
      failure out, so the theorem was simply not true of such a state. Every conflict drops
      `Solver.searchMeasure`, so the measure is a bound on the conflicts still to come, and
      this is the room the counter needs for them. It is an exponential bound in the number
      of variables, which is the honest shape: a `u32` cannot count the conflicts of a
      solver run on 50 variables, and the same is true of `budget`, whose growth this
      bounds as well.
    * `hbudget`: **`2 ≤ first_restart`, not `0 <`.** With a budget of 1, `budget += budget
      / 2` is a no-op, so the solver restarts after every single conflict, forever, and
      nothing in the measure above decreases across those restarts. Proving termination
      *there* needs "a learned clause is not one the database already has", which is a
      different and much harder argument than this file makes -- so the statement excludes
      it instead of pretending otherwise. `Solver::solve` passes `FIRST_RESTART = 100`.

    And three are the same accounting one step further:

    * `hdbroom`: pushing a learned clause needs the clause vector to have room, and the
      measure bounds the clauses still to be learned exactly as it bounds the conflicts.
    * `hfits`: the restart budget grows by half of itself, and `3 ^ n` is as far as it can
      grow before restarts stop happening, so it has to fit twice over.
    * `hlevels`: **every open level was opened by a decision.** This is the one hypothesis
      that is not about machine integers, and `Solver.WF` cannot state it: `search` pushes
      `trail_lim` and only *then* assigns, so the state `assign` is handed has an empty top
      level. It is an invariant of the loop (`Solver.Searching`'s `levels`), and `search`
      needs it of the state it is given -- `Solver::new`'s, where the trail is empty and it
      holds vacuously. Without it `propagate`'s `hopen` is unavailable, and so is the
      decision the backjump measure counts on.

    And one that *weakened*: `hfix` used to read "no clause of the database is falsified",
    which is what `propagate` reaching a fixpoint gives -- but it is false of a CNF holding
    the **empty** clause, and `solve_cnf` has to answer for that CNF too. What the proof
    actually spends it on is the loop invariant's `falsified`, so that is what the
    hypothesis now says: a falsified clause mentions the current level. At level 0 -- the
    state `Solver::new` returns -- it is vacuous, which is the point. -/
theorem sat_cdcl.Solver.search.spec (s : sat_cdcl.Solver)
    (db₀ : List (List cnf.Literal)) (first_restart : Std.U32)
    (hwf : Solver.WF s)
    (hbound : s.value.val.length ≤ 2 ^ 16)
    (hbudget : 2 ≤ first_restart.val)
    (hroom : s.conflicts.val + Solver.searchMeasure s first_restart ≤ Std.U32.max)
    (hsound : ∀ cl ∈ Solver.db s, Entails db₀ cl)
    (hproblem : ∀ cl ∈ db₀, cl ∈ Solver.db s)
    (hfix : ∀ cl ∈ Solver.db s, (∀ lit ∈ cl, Solver.litFalse s lit) →
      0 < Solver.decisionLevel s →
      ∃ lit ∈ cl, Solver.levelOf s lit.var = Solver.decisionLevel s)
    (hdbroom : (Solver.db s).length + Solver.searchMeasure s first_restart ≤ Std.Usize.max)
    (hfits : 2 * 3 ^ s.value.val.length ≤ Std.U32.max)
    (hvars : ∀ v ∈ cnfVars db₀,
      v.val < s.value.val.length ∧ s.occurs.val[v.val]? = some true)
    (hlevels : ∀ k, 0 < k → k ≤ Solver.decisionLevel s → ∃ v ∈ s.trail.val,
      Solver.levelOf s v = k ∧ Solver.reasonOf s v = none) :
    sat_cdcl.Solver.search s first_restart ⦃ (sat : Bool) (s' : sat_cdcl.Solver) =>
      Solver.WF s'
      ∧ (∀ cl ∈ Solver.db s', Entails db₀ cl)
      ∧ s'.value.val.length = s.value.val.length
      ∧ (sat = true →
          (∀ v ∈ cnfVars db₀, (Solver.valueOf s' v).isSome = true)
          ∧ ∀ w : Std.U16 → Bool,
              (∀ v b, Solver.valueOf s' v = some b → w v = b) →
              Cnf.eval w db₀ = true)
      ∧ (sat = false → ∀ w : Std.U16 → Bool, Cnf.eval w db₀ ≠ true) ⦄ := by
  unfold sat_cdcl.Solver.search
  refine sat_cdcl.Solver.search_loop.spec s first_restart 0#u32 db₀
    { wf := hwf
      bound := hbound
      sound := hsound
      problem := hproblem
      falsified := hfix
      vars := hvars
      levels := hlevels
      budget_ge := hbudget
      window := by simpa using Solver.trailLeft_le s
      room := hroom
      db_room := hdbroom
      fits := hfits }

/-! #### The CNF layer

Where CDCL's contract actually lives (`solve_cnf`'s own doc comment says so, and it is
what a DIMACS front end calls). Soundness is stated over *any* valuation agreeing with
the returned model, which is only a fair statement because the model fixes every
variable the CNF mentions -- hence the second conjunct, which the `Expr` layer above
then needs in its own right, to read gate variables back out of the map. -/

/-- **The model-reading loop**: one pass over the slot array, pushing every assigned slot
    as a `(u16, bool)` pair. Two things are claimed of the result, and both are needed:
    the pairs already there stay (the loop only pushes), and every assigned variable in
    the window ends up in it. The second is what makes a `true` answer a *model*: the
    search's postcondition is about `Solver.valueOf`, and the caller only ever sees the
    vector.

    `hbound` is spent on the `v as u16` cast, exactly as in `pick_branch_var`: without
    it the pair recorded for a slot past `2 ^ 16` would name a different variable. -/
@[step]
theorem sat_cdcl.solve_cnf_loop.spec (iter : core.ops.range.Range Std.Usize)
    (sv : sat_cdcl.Solver) (model : alloc.vec.Vec (Std.U16 × Bool))
    (hend : iter.«end».val ≤ sv.value.val.length)
    (hbound : sv.value.val.length ≤ 2 ^ 16)
    (hroom : model.val.length + (iter.«end».val - iter.start.val) ≤ Usize.max) :
    sat_cdcl.solve_cnf_loop iter sv model ⦃ (m' : alloc.vec.Vec (Std.U16 × Bool)) =>
      (∀ p ∈ model.val, p ∈ m'.val)
      ∧ (∀ p ∈ m'.val, p ∈ model.val ∨ Solver.valueOf sv p.1 = some p.2)
      ∧ ∀ v : Std.U16, iter.start.val ≤ v.val → v.val < iter.«end».val →
          ∀ b, Solver.valueOf sv v = some b → (v, b) ∈ m'.val ⦄ := by
  unfold sat_cdcl.solve_cnf_loop
  step*
  -- the cursor is past the end: the coverage claim is vacuous
  · obtain ⟨hge, -⟩ := o_post3 ‹o = none›
    exact ⟨fun p hp => hp, fun p hp => Or.inl hp,
      fun w hw1 hw2 => absurd hw2 (by omega)⟩
  -- the slot is unassigned: nothing to add, and `w` cannot be this variable
  · obtain ⟨hv, hlt, hstart⟩ := o_post2 _ ‹o = some _›
    have hvs : v.val = iter.start.val := by rw [hv]
    refine ⟨fun p hp => (m'_post1 p hp), fun p hp => m'_post2 p hp,
      fun w hw1 hw2 b hb => ?_⟩
    rcases Nat.lt_or_ge w.val (v.val + 1) with h | h
    · have hwv : w.val = v.val := by omega
      rw [Solver.valueOf, hwv, o1_post, ‹o1 = none›] at hb
      exact absurd hb (by simp)
    · exact m'_post3 w (by omega) (by rw [o_post1]; exact hw2) b hb
  -- the push has room: one entry for one step of the range
  · obtain ⟨hv, hlt, hstart⟩ := o_post2 _ ‹o = some _›
    have hvs : v.val = iter.start.val := by rw [hv]
    rw [model1_post, o_post1]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  -- the slot is assigned: `w` is either this variable, which the push just recorded, or
  -- one the rest of the scan covers
  · obtain ⟨hv, hlt, hstart⟩ := o_post2 _ ‹o = some _›
    have hvs : v.val = iter.start.val := by rw [hv]
    have hmodel : ∀ p ∈ model.val, p ∈ m'.val := fun p hp =>
      m'_post1 p (by rw [model1_post]; simp [hp])
    have hiv : i.val = v.val := by
      have h16 : v.val < 2 ^ 16 := by omega
      rw [i_post, UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt h16
    have hib : Solver.valueOf sv i = some b := by
      simp [Solver.valueOf, hiv, o1_post, ‹o1 = some b›]
    refine ⟨hmodel, ?_, fun w hw1 hw2 b' hb => ?_⟩
    · -- a pair in the result came either from the vector handed in or from this push,
      -- and the push recorded exactly what the slot holds
      intro p hp
      rcases m'_post2 p hp with h | h
      · rw [model1_post, List.mem_append] at h
        rcases h with h' | h'
        · exact Or.inl h'
        · rw [List.mem_singleton.mp h']
          exact Or.inr hib
      · exact Or.inr h
    rcases Nat.lt_or_ge w.val (v.val + 1) with h | h
    · have hwv : w.val = v.val := by omega
      have hwi : w = i := Solver.uscalar_eq_of_val (by rw [hwv, hiv])
      rw [Solver.valueOf, hwv, o1_post, ‹o1 = some b›] at hb
      have hbb : b' = b := by simpa using hb.symm
      rw [hwi, hbb]
      exact m'_post1 (i, b) (by rw [model1_post]; simp)
    · exact m'_post3 w (by omega) (by rw [o_post1]; exact hw2) b' hb
termination_by iter.«end».val - iter.start.val
decreasing_by
  all_goals
    obtain ⟨-, hlt, hstart⟩ := o_post2 _ (by assumption)
    rw [o_post1]
    omega


/-- **Soundness of `sat_cdcl::solve_cnf`**: a returned model satisfies the CNF, and
    covers every variable it mentions.

    Three hypotheses besides `CnfShort`, and all three are `search.spec`'s numeric ones
    pulled back to the input. `n` is any bound on the CNF's variables; `Solver::new` sizes
    the slot arrays from the largest variable it finds, so `new.spec`'s "the slot count is
    the least such bound" is what turns `n` into a bound on `s.value.len()` -- and hence on
    `3 ^ s.value.len()`, which is what the measure and the `u32` counters are stated
    against. Without that direction the only bound available is `2 ^ 16`, and
    `searchRoom (2 ^ 16)` exceeds `u32::MAX`, which would make this theorem vacuous rather
    than merely narrow.

    Narrow it is: `searchRoom n ≤ u32::MAX` holds up to about nine variables. That is the
    price of `self.conflicts` being a `u32` and of `searchRoom` being the crude bound it
    is; see `Solver.searchMeasure_le_searchRoom`.

    `hfix` is not among them. `search.spec` asks only that a falsified clause mention the
    current level, and `Solver::new` returns a state at level 0, so the hypothesis is
    vacuous -- which is exactly why it is stated that way: "no clause is falsified" fails
    for a CNF containing the *empty* clause, and `solve_cnf` has to answer for that CNF
    too (it answers `None`). -/
theorem sat_cdcl.solve_cnf_sound (cc : cnf.Cnf) (n : Nat)
    (hshort : CnfShort (Cnf.contents cc))
    (hvars : ∀ v ∈ cnfVars (Cnf.contents cc), v.val < n)
    (hroom : searchRoom n ≤ Std.U32.max)
    (hdbroom : (Cnf.contents cc).length + searchRoom n ≤ Std.Usize.max) :
    sat_cdcl.solve_cnf cc ⦃ (result : sat_result.SatResult (alloc.vec.Vec
      (Std.U16 × Bool))) =>
        ∀ model, result = sat_result.SatResult.Sat model →
          (∀ w : Std.U16 → Bool, (∀ p ∈ model.val, w p.1 = p.2) →
              Cnf.eval w (Cnf.contents cc) = true)
          ∧ (∀ v ∈ cnfVars (Cnf.contents cc), ∃ b, (v, b) ∈ model.val)
          ∧ (∀ p ∈ model.val, ∀ q ∈ model.val, p.1 = q.1 → p.2 = q.2) ⦄ := by
  unfold sat_cdcl.solve_cnf sat_cdcl.Solver.solve sat_cdcl.Solver.num_vars
  step with (sat_cdcl.Solver.new.spec cc hshort)
  have hNn : solver.value.val.length ≤ n := solver_post8 n hvars
  have hmeas : Solver.searchMeasure solver sat_cdcl.FIRST_RESTART ≤ searchRoom n :=
    Solver.searchMeasure_le_searchRoom solver _ hNn
  have h3 : (3 : Nat) ^ solver.value.val.length ≤ 3 ^ n :=
    Nat.pow_le_pow_right (by norm_num) hNn
  have hfits : 2 * 3 ^ solver.value.val.length ≤ Std.U32.max := by
    simp only [searchRoom] at hroom
    omega
  -- the state `new` returns satisfies every hypothesis of `search.spec`: the counters are
  -- at 0, the database is the problem, and the level is 0, which is what makes the two
  -- hypotheses about falsified clauses and open levels vacuous
  step with (sat_cdcl.Solver.search.spec solver (Cnf.contents cc) sat_cdcl.FIRST_RESTART
    solver_post1 solver_post7 (by simp [sat_cdcl.FIRST_RESTART])
    (by rw [solver_post9]; omega)
    (fun cl hcl => Entails.of_mem (by rw [solver_post2] at hcl; exact hcl))
    (fun cl hcl => by rw [solver_post2]; exact hcl)
    (fun cl hcl hall hpos => absurd hpos (by rw [solver_post4]; omega))
    (by rw [solver_post2]; omega) hfits solver_post6
    (fun k hk hle => absurd hle (by rw [solver_post4]; omega)))
  step*
  intro m hm
  have hm' : model1 = m := by injection hm
  subst hm'
  -- every assigned variable is in the vector: its slot exists, so the scan reached it
  have hcover : ∀ v : Std.U16, ∀ c : Bool,
      Solver.valueOf solver1 v = some c → (v, c) ∈ model1.val := by
    intro v c hc
    refine model1_post3 v (Nat.zero_le _) ?_ c hc
    rw [i_post]
    by_contra hge
    rw [Solver.valueOf, List.getElem?_eq_none (by omega)] at hc
    exact absurd hc (by simp)
  refine ⟨fun w hw => (b_post4 ‹b = true›).2 w
      fun v c hvc => hw (v, c) (hcover v c hvc), ?_, ?_⟩
  · intro v hv
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp ((b_post4 ‹b = true›).1 v hv)
    exact ⟨c, hcover v c hc⟩
  -- the vector holds no junk -- every pair in it is a slot read -- so it names each
  -- variable at most once, which is what the `Expr` layer needs to insert it into a map
  · intro p hp q hq hkey
    have hpv := (model1_post2 p hp).resolve_left (by rw [model_post]; simp)
    have hqv := (model1_post2 q hq).resolve_left (by rw [model_post]; simp)
    rw [hkey, hqv] at hpv
    exact (Option.some.inj hpv).symm

/-- **Completeness of `sat_cdcl::solve_cnf`**: a satisfiable CNF gets a model.

    Same three input bounds as the soundness direction, and for the same reason -- they are
    what `search.spec` asks of the state `Solver::new` builds, and neither direction can be
    stated without them. The proof is the same prelude and then nothing: `search.spec`'s
    `false` clause says the CNF has no model, `hsat` says it has one, and the `else` arm
    that would return `None` is unreachable. -/
theorem sat_cdcl.solve_cnf_complete (cc : cnf.Cnf) (w : Std.U16 → Bool) (n : Nat)
    (hshort : CnfShort (Cnf.contents cc))
    (hvars : ∀ v ∈ cnfVars (Cnf.contents cc), v.val < n)
    (hroom : searchRoom n ≤ Std.U32.max)
    (hdbroom : (Cnf.contents cc).length + searchRoom n ≤ Std.Usize.max)
    (hsat : Cnf.eval w (Cnf.contents cc) = true) :
    sat_cdcl.solve_cnf cc ⦃ (result : sat_result.SatResult (alloc.vec.Vec
      (Std.U16 × Bool))) => ∃ model, result = sat_result.SatResult.Sat model ⦄ := by
  unfold sat_cdcl.solve_cnf sat_cdcl.Solver.solve sat_cdcl.Solver.num_vars
  step with (sat_cdcl.Solver.new.spec cc hshort)
  have hNn : solver.value.val.length ≤ n := solver_post8 n hvars
  have hmeas : Solver.searchMeasure solver sat_cdcl.FIRST_RESTART ≤ searchRoom n :=
    Solver.searchMeasure_le_searchRoom solver _ hNn
  have h3 : (3 : Nat) ^ solver.value.val.length ≤ 3 ^ n :=
    Nat.pow_le_pow_right (by norm_num) hNn
  have hfits : 2 * 3 ^ solver.value.val.length ≤ Std.U32.max := by
    simp only [searchRoom] at hroom
    omega
  step with (sat_cdcl.Solver.search.spec solver (Cnf.contents cc) sat_cdcl.FIRST_RESTART
    solver_post1 solver_post7 (by simp [sat_cdcl.FIRST_RESTART])
    (by rw [solver_post9]; omega)
    (fun cl hcl => Entails.of_mem (by rw [solver_post2] at hcl; exact hcl))
    (fun cl hcl => by rw [solver_post2]; exact hcl)
    (fun cl hcl hall hpos => absurd hpos (by rw [solver_post4]; omega))
    (by rw [solver_post2]; omega) hfits solver_post6
    (fun k hk hle => absurd hle (by rw [solver_post4]; omega)))
  step*

/-- **`solve_sat_with` reading the model into the map.** Three things, and the third is
    the reason the second exists: keys already present stay present; a value already
    present survives unless a later pair overwrites it with something else; and therefore,
    *if* the vector names each variable at most once, every pair comes back out of the map
    with the value it went in with.

    Stating the last as an implication rather than taking the hypothesis is what lets
    `solve_sat_complete` use this spec at all -- that direction has no model to be
    functional. -/
@[step]
theorem sat_cdcl.solve_sat_with_loop.spec
    (iter : alloc.vec.into_iter.IntoIter (Std.U16 × Bool)) (val : expr.Map) :
    sat_cdcl.solve_sat_with_loop iter val ⦃ (val' : expr.Map) =>
      (∀ k, Map.lookupList val.val k ≠ none → Map.lookupList val'.val k ≠ none)
      ∧ (∀ k b, Map.lookupList val.val k = some b →
          (∀ q ∈ iter.val, q.1 = k → q.2 = b) → Map.lookupList val'.val k = some b)
      ∧ ((∀ p ∈ iter.val, ∀ q ∈ iter.val, p.1 = q.1 → p.2 = q.2) →
          ∀ p ∈ iter.val, Map.lookupList val'.val p.1 = some p.2) ⦄ := by
  unfold sat_cdcl.solve_sat_with_loop
  step*
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => exact ⟨fun k h => h, fun k b h _ => h, by simp⟩
    | cons e es => simp_all
  · obtain ⟨var, value⟩ := p
    step*
    all_goals
      obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e es =>
        obtain ⟨heq, hiter⟩ := o_post
        have hpe : e = (var, value) := by
          have h1 : o = some (var, value) := by assumption
          rw [h1] at heq; exact (Option.some.inj heq).symm
        subst hpe
        refine ⟨?_, ?_, ?_⟩
        · exact fun k h => val'_post1 k
            (by rw [__post2]; exact Map.lookupList_upsertList_ne_none _ k var value h)
        · intro k b hkb hall
          refine val'_post2 k b ?_ ?_
          · rw [__post2]
            by_cases hvk : k = var
            · subst hvk
              have hvb : value = b := hall (k, value) (by simp) rfl
              rw [← hvb]
              exact Map.lookupList_upsertList_self _ _ _
            · rw [Map.lookupList_upsertList_other _ _ _ _ hvk]; exact hkb
          · exact fun q hq hq1 => hall q (by rw [hiter] at hq; simp [hq]) hq1
        · intro hfun p hp
          rcases List.mem_cons.mp (by simpa using hp) with rfl | hp'
          · refine val'_post2 _ _ ?_ ?_
            · rw [__post2]; exact Map.lookupList_upsertList_self _ _ _
            · exact fun q hq hq1 =>
                hfun q (by rw [hiter] at hq; simp [hq]) (var, value) (by simp) hq1
          · refine val'_post3 ?_ p (by rw [hiter]; exact hp')
            intro a ha b hb hab
            exact hfun a (by rw [hiter] at ha; simp [ha]) b
              (by rw [hiter] at hb; simp [hb]) hab
termination_by iter.val.length
decreasing_by
  all_goals
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all

/-- **How many slots the encoded CNF needs.** `e`'s own variables reach `(varsOf e).foldl
    bump 0` -- the same fold `Renamer::new` and `Encoder::new` run -- and the hybrid
    transformation adds at most one gate per AST node, since the only thing that allocates
    one is `disjoin`. The naive transformation on the fallback arm adds none.

    This is the `n` the `solve_cnf` pair is stated against, and it is why
    `cnf_transform_hybrid.Encodes` had to grow a field: `Encodes` knew the gate counter
    started *above* `e`'s variables, and what a caller sizing an array needs is that it
    starts no higher than it has to. -/
def varBound (e : expr.Expr) : Nat := (varsOf e).foldl bump 0 + exprSize e

theorem varsOf_lt_varBound (e : expr.Expr) :
    ∀ k ∈ varsOf e, k.val < (varsOf e).foldl bump 0 :=
  mem_lt_foldl_bump (varsOf e) 0

/-- **The tail both roots share**, `sat_dpll.sound_tail`'s counterpart: the returned map
    represents its own readback on `e`'s variables, that readback agrees with the model the
    solver found, so it satisfies the CNF, so it satisfies `e` -- and `evaluate` on a map
    that represents a valuation returns what that valuation says.

    Where DPLL's version needs the CNF's variables in the map (its search clause is stated
    over valuations agreeing with the map on `cnfVars`), this one needs only the pairs to
    read back, because `solve_cnf_sound`'s search clause is stated over valuations agreeing
    with the *model*. -/
theorem sat_cdcl.sound_tail (e : expr.Expr) (cc : cnf.Cnf) (val' : expr.Map)
    (model : alloc.vec.Vec (Std.U16 × Bool))
    (hvars : ∀ k ∈ varsOf e, Map.lookupList val'.val k ≠ none)
    (hmodel : ∀ p ∈ model.val, Map.lookupList val'.val p.1 = some p.2)
    (hsearch : ∀ w : Std.U16 → Bool, (∀ p ∈ model.val, w p.1 = p.2) →
      Cnf.eval w (Cnf.contents cc) = true)
    (hcnf : ∀ w : Std.U16 → Bool,
      Cnf.eval w (Cnf.contents cc) = true → evalPure w e = true) :
    expr.evaluate e val' ⦃ (r : core.result.Result Bool Unit) =>
      r = core.result.Result.Ok true ⦄ := by
  have hrepr : Map.represents val' (varsOf e) (Map.readback val') :=
    Map.represents_readback val' (varsOf e) hvars
  have hag : ∀ p ∈ model.val, Map.readback val' p.1 = p.2 := by
    intro p hp
    simp [Map.readback, hmodel p hp]
  have hpure : evalPure (Map.readback val') e = true := hcnf _ (hsearch _ hag)
  have hev := expr.evaluate.spec_of_represents e val' (Map.readback val') hrepr
  rwa [hpure] at hev

/-! #### The roots

`sat_cdcl::solve_sat` encodes with the hybrid transformation -- the same `sat_dpll::encode`
call `sat_dpll::solve_sat` makes -- and then hands the CNF to `solve_cnf`. So these two
differ from `SatDpll.lean`'s pair only in which solver runs in the middle, and their
proofs split on the same `Result`: the hybrid arm, where
`cnf_transform_hybrid.Encodes.sound`/`.complete` relate the CNF's models to `e`'s, and
the fallback arm `encode` takes when the hybrid runs out of gate variables, where
`Cnf.eval_cnfPure` does.

What CDCL cannot borrow from `SatDpll.lean` is the *shape* of the tail. DPLL's `dpll`
returns the map it searched with; CDCL's `solve_cnf` returns a `Vec<(u16, bool)>` that
`solve_sat_with` then inserts into a map seeded only from `collect_vars e`. So there is an
extra loop to say something about, and what it has to say is "the pairs come back out of
the map with the values they went in with" -- which needs the model to name each variable
at most once. That is `solve_cnf_sound`'s third conjunct, and it is there because the
vector holds nothing but slot reads.

The coverage conjunct, by contrast, turns out *not* to be needed here: `expr.evaluate`
reads only `e`'s own variables, so `Map.represents` on `varsOf e` is enough, and that
holds because the map starts as `initial_valuation (collect_vars e)` and insertion only
adds keys. Coverage is still the honest thing for `solve_cnf` to promise -- it is what
makes a `true` answer a model of the whole CNF -- but the `Expr` layer spends the
functionality conjunct instead. -/

/-- **Soundness of `sat_cdcl::solve_sat`**: if it returns a valuation, that valuation
    satisfies `e`.

    The first two bounds are `sat_dpll.solve_sat_sound`'s, for the same reasons: `hquad`
    is what the hybrid transformation needs, `hbound` the naive transformation's
    worst-case blowup on the fallback arm.

    Three are new, and all three are `solve_cnf_sound`'s pulled back through `encode`:

    * `hshort` is `CnfShort`. Clauses of the naive transformation hold at most
      `exprSize e` literals and the hybrid's definition clauses one more, for the `neg g`
      that makes a definition an implication -- hence the `+ 1`.
    * `hroom` and `hdbroom` are the search's room, and `varBound e` is the bound on the
      *encoded* CNF's variables: `e`'s own, plus one gate per AST node. The clause count
      is the hybrid's `exprSize e ^ 2 + exprSize e` or the naive transformation's
      `2 ^ exprSize e`, and `hdbroom` covers whichever arm `encode` takes.

    `hroom` is the binding one and it is small: `searchRoom n ≤ u32::MAX` holds to about
    `n = 10`, so this theorem speaks about expressions of a handful of variables and
    nodes. It is not a statement about the solver's reach; it is a statement about what
    fits in the `u32` the Rust counts conflicts in. -/
theorem sat_cdcl.solve_sat_sound (e : expr.Expr) (hbound : 2 ^ exprSize e ≤ Usize.max)
    (hquad : exprSize e * exprSize e + exprSize e + 1 ≤ Usize.max)
    (hshort : exprSize e + 1 + 2 ^ 16 ≤ Std.I32.max)
    (hroom : searchRoom (varBound e) ≤ Std.U32.max)
    (hdbroom : exprSize e * exprSize e + exprSize e + 2 ^ exprSize e
      + searchRoom (varBound e) ≤ Std.Usize.max) :
    sat_cdcl.solve_sat e ⦃ (result : sat_result.SatResult expr.Map) =>
      ∀ v, result = sat_result.SatResult.Sat v →
        expr.evaluate e v ⦃ (r : core.result.Result Bool Unit) =>
          r = core.result.Result.Ok true ⦄ ⦄ := by
  have hsize : exprSize e ≤ Usize.max := le_trans Nat.lt_two_pow_self.le hbound
  have h2 : 0 < 2 ^ exprSize e := Nat.pow_pos (by norm_num)
  simp only [sat_cdcl.solve_sat, sat_cdcl.solve_sat_with, sat_dpll.encode]
  step*
  cases x with
  | Ok c =>
    have hEnc : cnf_transform_hybrid.Encodes e c := by simpa using x_post
    have hvarsC : ∀ v ∈ cnfVars (Cnf.contents c), v.val < varBound e :=
      cnf_transform_hybrid.Encodes.vars_lt hEnc (varsOf_lt_varBound e)
    have hshortC : CnfShort (Cnf.contents c) := by
      intro cl hcl
      have h := cnf_transform_hybrid.Encodes.clause_length_le hEnc cl hcl
      omega
    have hlenC : (Cnf.contents c).length ≤ exprSize e * exprSize e + exprSize e :=
      cnf_transform_hybrid.Encodes.length_le hEnc
    step with (sat_cdcl.solve_cnf_sound c (varBound e) hshortC hvarsC hroom (by omega))
    step*
    obtain ⟨hsearch, hcov, hfunm⟩ := cnf1_post model ‹cnf1 = sat_result.SatResult.Sat model›
    unfold alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    step*
    intro v hv
    have hv' : val1 = v := by injection hv
    subst hv'
    refine sat_cdcl.sound_tail e c val1 model ?_ (val1_post3 hfunm) hsearch
      (fun w hw => cnf_transform_hybrid.Encodes.sound hEnc hw)
    intro k hk
    refine val1_post1 k ?_
    rw [val_post k (by rw [s_post]; exact (vars_post1 k).mpr hk)]
    simp
  | Err u =>
    step*
    have hshortC : CnfShort (Cnf.contents cnf1) := by
      intro cl hcl
      have h := cnfPure_clause_length_le e false cl (by rw [← cnf1_post]; exact hcl)
      omega
    have hvarsC : ∀ v ∈ cnfVars (Cnf.contents cnf1), v.val < varBound e := by
      intro v hv
      have h := cnfVars_cnfPure_subset e false v (by rw [← cnf1_post]; exact hv)
      have := varsOf_lt_varBound e v h
      simp only [varBound]
      omega
    have hlenC : (Cnf.contents cnf1).length ≤ 2 ^ exprSize e := by
      rw [cnf1_post]; exact cnfPure_length_le e false
    step with (sat_cdcl.solve_cnf_sound cnf1 (varBound e) hshortC hvarsC hroom (by omega))
    step*
    obtain ⟨hsearch, hcov, hfunm⟩ := sr_post model ‹sr = sat_result.SatResult.Sat model›
    unfold alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    step*
    intro v hv
    have hv' : val1 = v := by injection hv
    subst hv'
    refine sat_cdcl.sound_tail e cnf1 val1 model ?_ (val1_post3 hfunm) hsearch ?_
    · intro k hk
      refine val1_post1 k ?_
      rw [val_post k (by rw [s_post]; exact (vars_post1 k).mpr hk)]
      simp
    · intro w hw
      rw [cnf1_post, Cnf.eval_cnfPure] at hw
      simpa using hw

/-- **Completeness of `sat_cdcl::solve_sat`**: if `e` has a satisfying valuation at all,
    it returns one. As in `SatDpll.lean`, `w` need not say anything about the gate
    variables the hybrid transformation introduces -- `Encodes.complete` extends it.

    Same five bounds, and the proof is `solve_cnf_complete` on each arm plus the
    observation that the `None` arm is then unreachable: nothing is claimed about the map,
    so the insertion loop's unconditional postcondition is all that is asked of it. -/
theorem sat_cdcl.solve_sat_complete (e : expr.Expr) (w : Std.U16 → Bool)
    (hbound : 2 ^ exprSize e ≤ Usize.max)
    (hquad : exprSize e * exprSize e + exprSize e + 1 ≤ Usize.max)
    (hshort : exprSize e + 1 + 2 ^ 16 ≤ Std.I32.max)
    (hroom : searchRoom (varBound e) ≤ Std.U32.max)
    (hdbroom : exprSize e * exprSize e + exprSize e + 2 ^ exprSize e
      + searchRoom (varBound e) ≤ Std.Usize.max)
    (hsat : evalPure w e = true) :
    sat_cdcl.solve_sat e ⦃ (result : sat_result.SatResult expr.Map) =>
      ∃ v, result = sat_result.SatResult.Sat v ⦄ := by
  have hsize : exprSize e ≤ Usize.max := le_trans Nat.lt_two_pow_self.le hbound
  have h2 : 0 < 2 ^ exprSize e := Nat.pow_pos (by norm_num)
  simp only [sat_cdcl.solve_sat, sat_cdcl.solve_sat_with, sat_dpll.encode]
  step*
  cases x with
  | Ok c =>
    have hEnc : cnf_transform_hybrid.Encodes e c := by simpa using x_post
    have hvarsC : ∀ v ∈ cnfVars (Cnf.contents c), v.val < varBound e :=
      cnf_transform_hybrid.Encodes.vars_lt hEnc (varsOf_lt_varBound e)
    have hshortC : CnfShort (Cnf.contents c) := by
      intro cl hcl
      have h := cnf_transform_hybrid.Encodes.clause_length_le hEnc cl hcl
      omega
    have hlenC : (Cnf.contents c).length ≤ exprSize e * exprSize e + exprSize e :=
      cnf_transform_hybrid.Encodes.length_le hEnc
    obtain ⟨w', -, hw'⟩ := cnf_transform_hybrid.Encodes.complete hEnc hsat
    step with (sat_cdcl.solve_cnf_complete c w' (varBound e) hshortC hvarsC hroom
      (by omega) hw')
    unfold alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    step*
  | Err u =>
    step*
    have hshortC : CnfShort (Cnf.contents cnf1) := by
      intro cl hcl
      have h := cnfPure_clause_length_le e false cl (by rw [← cnf1_post]; exact hcl)
      omega
    have hvarsC : ∀ v ∈ cnfVars (Cnf.contents cnf1), v.val < varBound e := by
      intro v hv
      have h := cnfVars_cnfPure_subset e false v (by rw [← cnf1_post]; exact hv)
      have := varsOf_lt_varBound e v h
      simp only [varBound]
      omega
    have hlenC : (Cnf.contents cnf1).length ≤ 2 ^ exprSize e := by
      rw [cnf1_post]; exact cnfPure_length_le e false
    have hcnf : Cnf.eval w (Cnf.contents cnf1) = true := by
      rw [cnf1_post, Cnf.eval_cnfPure, hsat]; simp
    step with (sat_cdcl.solve_cnf_complete cnf1 w (varBound e) hshortC hvarsC hroom
      (by omega) hcnf)
    unfold alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    step*

/-! #### Discharge order, in retrospect

Leaves up, as `PLAN.md` asks: `new.spec`, `assign.spec`, `backtrack.spec`,
`propagate.spec`, `search.spec`, the `solve_cnf` pair, then the two roots. All nine done;
no `sorry` left in this file.

Every layer sent one requirement down to the layer below, and that is the whole story of
how the statements changed. `search.spec` needed numeric room, so `new.spec` had to report
the counters at 0 *and* the slot count as the least bound on the CNF's variables -- the
first because `hroom` mentions `conflicts`, the second because without it the only bound
available is `2 ^ 16` and `searchRoom (2 ^ 16)` exceeds `u32::MAX`, which would have made
the `solve_cnf` pair vacuous rather than narrow. `solve_cnf` in turn had to answer for a CNF
holding the empty clause, which weakened `search.spec`'s `hfix`. And the roots needed all of
it pulled back through `encode`, which is where `cnf_transform_hybrid.Encodes` grew its own
new field: it knew the gate counter started *above* `e`'s variables, and what sizing an
array needs is that it starts no higher than it has to.

The last link is `solve_sat_with`'s insertion loop, the one thing here with no DPLL
counterpart -- DPLL searches the map it returns, CDCL copies a vector into it. Saying the
pairs read back out of the map is what needs the model to name each variable at most once,
and that is `solve_cnf_sound`'s third conjunct. -/

/-! ### What the proof rests on

The tree is closed, so this is no longer a list of gaps. It is the list of things that
carry the weight, and the two places the statements are narrower than the code:

* **`Solver.WF` is established, preserved, and carried across `search`.** `new.spec`
  builds it, `assign.spec`, `propagate.spec` and `backtrack.spec` preserve it, and
  `search.spec` carries it -- together with "every clause the database holds is entailed by
  the problem" -- across a loop that grows the database. Proving them added five fields the
  invariant did not have -- `phase_length`, `occurs_length`, `trail_lim_spec`,
  `reason_assigned` and `db_vars` -- each one a property `analyze` never reads and some
  other function needs. Two
  fields are worth singling out because they are the ones the Rust relies on silently:
  `decision_first` (a level's decision is its earliest trail entry) is what makes
  `.expect("a propagated literal has a reason")` safe, and `db_len` (clauses are
  shorter than `2 ^ 31 - 65537` literals) is the one assumption about the *input*
  rather than the solver, and what keeps `pending`'s `i32` and the two `Vec` pushes in
  range over a pass of a clause.

* **Termination of `analyze` is not a separate obligation: the specs already carry it.**
  `⦃ ⦄` is `Aeneas.Std.WP.spec`, and `spec div p ↔ False`, so a `⦃ ⦄` statement about a
  `partial_fixpoint` definition asserts that the call *returns* -- `analyze.spec` says
  `analyze` succeeds, divergence ruled out. The loops that need a measure carry one on
  the spec theorem rather than on the extracted definition
  (`analyze_loop0_loop1.spec`'s `termination_by index.val`: the trail cursor strictly
  decreases), and `analyze_loop0.spec` carries none, its recursive call being discharged
  within the `step*` run. A partial-correctness statement would be written with `⦃ ⦄div`
  (`dspec`, which `div` satisfies); nothing in this directory uses it.

* **Termination of the *search* was the hard obligation, and it is discharged.**
  `search.spec` is a `⦃ ⦄` statement, so proving it meant proving CDCL search terminates.
  DPLL's "one variable fewer per level" measure does not apply; the measure is the trail
  read as a base-3 numeral, one digit per slot, `1` for a decision and `2` for a
  propagation, which every step of the search makes strictly larger -- a backjump included,
  since it turns the decision it jumps over into a propagation of the clause just learned.
  Restarts abandon the trail, and what pays for them is the geometrically growing budget:
  `restartsLeft` counts how many times it can still grow before it exceeds the number of
  steps a restart window can have. `Solver.searchMeasure` is the pair.

  What this does *not* cover, and what the statement now says instead of pretending
  otherwise: a first restart interval of `1`, where the budget never grows and the solver
  restarts after every conflict forever. Termination there needs "a learned clause is not
  one the database already has", which is a different and much harder argument. And the
  three numeric hypotheses are exponential in the number of variables, because the
  counters they bound are `u32`s: the theorem covers formulas whose whole search fits in
  a `u32`'s worth of conflicts, not the 50-variable instances the benchmarks run.

* **The bounds are the narrow part, and they are narrow in the statement, not the
  argument.** `searchRoom n = 3 ^ n * 3 ^ n + 2 * 3 ^ n` bounds `Solver.searchMeasure` from
  above by way of `restartsLeft bound budget ≤ bound`, which is about as crude as a bound
  can be; `searchRoom n ≤ u32::MAX` therefore holds only to about `n = 10`. Sharpening
  `searchRoom` would widen the theorem without touching a line of the termination proof.
  What could *not* be sharpened away is the exponential: the measure really is exponential
  in the variable count, and `self.conflicts` really is a `u32`, so a machine-checked
  `⦃ ⦄` -- which rules out failure, overflow included -- cannot cover a 50-variable
  instance. Benchmarking is complementary to this, not redundant with it.

* **Two `native_decide` axioms come in with the extraction**, not with any proof here:
  Aeneas's `toStr` discharges "this string literal is at most `u32::MAX` bytes" with
  `decide +native`, so every extracted function holding a `panic!` message carries
  one axiom per message. `analyze_loop0` has two `.expect`s, so everything above
  `analyze.spec` -- the roots included -- depends on
  `analyze_loop0._native.decide.ax_1` and `_2` on top of the usual three. Nothing
  else in this directory does.

See `PLAN.md`.
-/

end sat_solver
