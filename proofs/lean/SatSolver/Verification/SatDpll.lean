/- Soundness + completeness for `sat_dpll::solve_sat` (DPLL: unit propagation plus
splitting, run on the CNF that `cnf::to_cnf` produces).

**Status: statements only.** Every proof below is `sorry`, following the same
top-down-then-bottom-up workflow the other proof files in this directory went
through (see `PLAN.md`): state the whole theorem tree first, so the shapes are
fixed and mutually consistent, then discharge it from the leaves up.

The structure mirrors `Cnf.lean`: a pure reference layer (`assignClause`/`assignCnf`
over plain lists, with the pure lemmas that carry the actual mathematical content),
then an extraction-matching layer of `⦃ ⦄` specs, one per generated function, and
finally the two top-level theorems.

The whole proof rests on one pure fact, `Cnf.eval_assignCnf`: simplifying a CNF
under `var := value` preserves its truth value for every valuation that *agrees*
with that assignment. Both directions of the search follow from it -- soundness
(the empty residual CNF at a successful leaf means every original clause was
already discharged) and completeness (a satisfying valuation survives
simplification along the branch it itself picks). -/
import SatSolver.Extraction
import SatSolver.Verification.Prelude
import SatSolver.Verification.MapLemmas
import SatSolver.Verification.CollectVars
import SatSolver.Verification.Semantics
import SatSolver.Verification.Cnf
import SatSolver.Verification.SatNaive

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

/-! ### Pure semantics -/

/-- "Assigning `var := value` satisfies this clause outright": the clause holds a
    literal of `var` whose polarity `value` makes true. This is exactly the test
    `assign_clause` performs as it scans, and the reason it can return `None`. -/
def clauseSatBy (var : Std.U8) (value : Bool) (cl : List cnf.Literal) : Bool :=
  cl.any (fun lit => lit.var = var && (lit.negated != value))

/-- Pure reference semantics for `sat_dpll::assign_clause`: simplify one clause
    under `var := value`. A literal of `var` whose polarity agrees with `value`
    satisfies the whole clause, which therefore disappears (`none`); the literals
    of `var` that disagree are false and drop out. Note that a clause of only
    such literals shrinks to `some []` -- the empty clause, i.e. a conflict, not
    a satisfied clause. -/
def assignClause (var : Std.U8) (value : Bool) (cl : List cnf.Literal) :
    Option (List cnf.Literal) :=
  if clauseSatBy var value cl then none
  else some (cl.filter (fun lit => lit.var != var))

/-! The two rewrites below are how every proof about `assignClause` proceeds:
`by_cases` on `clauseSatBy`, then rewrite. Casing on the `Option` directly fails
(dependent elimination can't see through the `if`). -/

@[simp]
theorem assignClause_of_satBy {var : Std.U8} {value : Bool} {cl : List cnf.Literal}
    (h : clauseSatBy var value cl = true) : assignClause var value cl = none := by
  simp [assignClause, h]

@[simp]
theorem assignClause_of_not_satBy {var : Std.U8} {value : Bool} {cl : List cnf.Literal}
    (h : clauseSatBy var value cl = false) :
    assignClause var value cl = some (cl.filter (fun lit => lit.var != var)) := by
  simp [assignClause, h]

theorem satBy_iff {var : Std.U8} {value : Bool} {cl : List cnf.Literal} :
    clauseSatBy var value cl = true ↔ ∃ lit ∈ cl, lit.var = var ∧ lit.negated ≠ value := by
  simp [clauseSatBy]

theorem not_satBy_iff {var : Std.U8} {value : Bool} {cl : List cnf.Literal} :
    clauseSatBy var value cl = false ↔ ∀ lit ∈ cl, lit.var = var → lit.negated = value := by
  simp [clauseSatBy]

theorem assignClause_inv_none {var : Std.U8} {value : Bool} {cl : List cnf.Literal}
    (h : assignClause var value cl = none) : clauseSatBy var value cl = true := by
  by_cases hsat : clauseSatBy var value cl = true
  · exact hsat
  · rw [Bool.not_eq_true] at hsat
    rw [assignClause_of_not_satBy hsat] at h
    simp at h

theorem assignClause_inv_some {var : Std.U8} {value : Bool} {cl cl' : List cnf.Literal}
    (h : assignClause var value cl = some cl') :
    clauseSatBy var value cl = false ∧ cl' = cl.filter (fun lit => lit.var != var) := by
  by_cases hsat : clauseSatBy var value cl = true
  · rw [assignClause_of_satBy hsat] at h; simp at h
  · rw [Bool.not_eq_true] at hsat
    rw [assignClause_of_not_satBy hsat, Option.some.injEq] at h
    exact ⟨hsat, h.symm⟩

/-! Cons-level rewrites for `assignClause`, mirroring the three cases
`assign_clause`'s loop body distinguishes as it scans. -/

theorem assignClause_cons_sat {var : Std.U8} {value : Bool} {lit : cnf.Literal}
    (rest : List cnf.Literal) (hvar : lit.var = var) (hneg : lit.negated ≠ value) :
    assignClause var value (lit :: rest) = none := by
  refine assignClause_of_satBy (satBy_iff.mpr ⟨lit, by simp, hvar, hneg⟩)

theorem assignClause_cons_drop {var : Std.U8} {value : Bool} {lit : cnf.Literal}
    (rest : List cnf.Literal) (hvar : lit.var = var) (hneg : lit.negated = value) :
    assignClause var value (lit :: rest) = assignClause var value rest := by
  have hcons : clauseSatBy var value (lit :: rest) = clauseSatBy var value rest := by
    simp [clauseSatBy, hvar, hneg]
  by_cases hsat : clauseSatBy var value rest = true
  · rw [assignClause_of_satBy hsat, assignClause_of_satBy (hcons.trans hsat)]
  · rw [Bool.not_eq_true] at hsat
    rw [assignClause_of_not_satBy hsat, assignClause_of_not_satBy (hcons.trans hsat)]
    simp [hvar]

theorem assignClause_cons_keep {var : Std.U8} {value : Bool} {lit : cnf.Literal}
    (rest : List cnf.Literal) (hvar : lit.var ≠ var) :
    assignClause var value (lit :: rest) =
      Option.map (fun cl => lit :: cl) (assignClause var value rest) := by
  have hcons : clauseSatBy var value (lit :: rest) = clauseSatBy var value rest := by
    simp [clauseSatBy, hvar]
  by_cases hsat : clauseSatBy var value rest = true
  · rw [assignClause_of_satBy hsat, assignClause_of_satBy (hcons.trans hsat)]; rfl
  · rw [Bool.not_eq_true] at hsat
    rw [assignClause_of_not_satBy hsat, assignClause_of_not_satBy (hcons.trans hsat)]
    simp [hvar]

/-- Pure reference semantics for `sat_dpll::assign_cnf`: simplify every clause,
    dropping the ones that became satisfied. -/
def assignCnf (var : Std.U8) (value : Bool) (c : List (List cnf.Literal)) :
    List (List cnf.Literal) :=
  c.filterMap (assignClause var value)

/-- Total number of literal occurrences in a CNF (`cnfVars` lists one variable per
    occurrence, so its length is exactly that). This is the search's termination
    measure: `assign_cnf` always deletes at least the assigned variable's own
    occurrences and never adds any. `sat_dpll.dpll` is a `partial_fixpoint`
    definition and `WP.spec` maps `div` to `False`, so its spec has to internalize
    termination via strong induction on this measure (the `∀ n, measure ≤ n → ...`
    trick `cnf.cnf_rec.spec` uses for `exprSize`) rather than `unfold` alone.
    A distinct-variable count would work too, but needs `dedup`/`Nodup` reasoning
    this one avoids. -/
def cnfSize (c : List (List cnf.Literal)) : Nat := (cnfVars c).length

/-- Membership in a simplified CNF: exactly the clauses that survived. -/
theorem mem_assignCnf {c : List (List cnf.Literal)} {var : Std.U8} {value : Bool}
    {cl' : List cnf.Literal} :
    cl' ∈ assignCnf var value c ↔ ∃ cl ∈ c, assignClause var value cl = some cl' := by
  simp only [assignCnf, List.mem_filterMap]

/-- Every surviving clause is its original with all of `var`'s literals dropped. -/
theorem assignCnf_mem_inv {c : List (List cnf.Literal)} {var : Std.U8} {value : Bool}
    {cl' : List cnf.Literal} (h : cl' ∈ assignCnf var value c) :
    ∃ cl ∈ c, cl' = cl.filter (fun lit => lit.var != var) := by
  obtain ⟨cl, hcl, hassign⟩ := mem_assignCnf.mp h
  exact ⟨cl, hcl, (assignClause_inv_some hassign).2⟩

/-! Cons-level rewrites for `assignCnf`, so the inductions below never have to
touch `List.filterMap` or case on the `Option`. -/

theorem assignCnf_cons_of_satBy {var : Std.U8} {value : Bool} {cl : List cnf.Literal}
    (rest : List (List cnf.Literal)) (h : clauseSatBy var value cl = true) :
    assignCnf var value (cl :: rest) = assignCnf var value rest := by
  simp only [assignCnf, List.filterMap_cons, assignClause_of_satBy h]

theorem assignCnf_cons_of_not_satBy {var : Std.U8} {value : Bool} {cl : List cnf.Literal}
    (rest : List (List cnf.Literal)) (h : clauseSatBy var value cl = false) :
    assignCnf var value (cl :: rest) =
      cl.filter (fun lit => lit.var != var) :: assignCnf var value rest := by
  simp only [assignCnf, List.filterMap_cons, assignClause_of_not_satBy h]

/-- A CNF containing the empty clause is false under every valuation -- this is
    what makes `has_empty_clause` a sound conflict test. -/
theorem Cnf.eval_eq_false_of_nil_mem (w : Std.U8 → Bool) {c : List (List cnf.Literal)}
    (h : [] ∈ c) : Cnf.eval w c = false := by
  simp only [Cnf.eval, Bool.eq_false_iff, ne_eq, List.all_eq_true, not_forall]
  exact ⟨[], h, by simp [Clause.eval]⟩

/-- A literal's value is determined by the assignment to its own variable. -/
theorem Literal.eval_eq (w : Std.U8 → Bool) (lit : cnf.Literal) {value : Bool}
    (hw : w lit.var = value) : Literal.eval w lit = (lit.negated != value) := by
  simp only [Literal.eval, hw]
  cases lit.negated <;> cases value <;> simp

/-- A unit clause forces its literal's polarity: every valuation satisfying the
    CNF assigns `lit.var` the only value that makes `lit` true. This is *the*
    justification for unit propagation committing without a backtracking point,
    and hence for `dpll`'s completeness in the propagation case. -/
theorem Literal.eq_of_unit_mem (w : Std.U8 → Bool) {c : List (List cnf.Literal)}
    {lit : cnf.Literal} (hmem : [lit] ∈ c) (hsat : Cnf.eval w c = true) :
    w lit.var = !lit.negated := by
  simp only [Cnf.eval, List.all_eq_true] at hsat
  have hcl := hsat [lit] hmem
  simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false] at hcl
  have := Literal.eval_eq w lit (value := w lit.var) rfl
  rw [this] at hcl
  cases hn : lit.negated <;> simp_all

/-- Clause-level half of the correctness of simplification: a clause that
    *disappears* was already satisfied. -/
theorem Clause.eval_of_satBy {w : Std.U8 → Bool} {cl : List cnf.Literal}
    {var : Std.U8} {value : Bool} (hw : w var = value)
    (h : clauseSatBy var value cl = true) : Clause.eval w cl = true := by
  obtain ⟨lit, hmem, hvar, hneg⟩ := satBy_iff.mp h
  simp only [Clause.eval, List.any_eq_true]
  refine ⟨lit, hmem, ?_⟩
  rw [Literal.eval_eq w lit (value := value) (by rw [hvar]; exact hw)]
  simp [hneg]

/-- Clause-level other half: the literals simplification *drops* were all false,
    so dropping them leaves the clause's value unchanged. -/
theorem Clause.eval_filter {w : Std.U8 → Bool} {var : Std.U8} {value : Bool}
    (hw : w var = value) (cl : List cnf.Literal)
    (h : clauseSatBy var value cl = false) :
    Clause.eval w (cl.filter (fun lit => lit.var != var)) = Clause.eval w cl := by
  rw [not_satBy_iff] at h
  simp only [Clause.eval]
  induction cl with
  | nil => simp
  | cons lit rest ih =>
    have hrest : ∀ l ∈ rest, l.var = var → l.negated = value :=
      fun l hl => h l (by simp [hl])
    by_cases hv : lit.var = var
    · /- `lit` is a literal of `var`, and it is false under `var := value`, so
         dropping it changes nothing. -/
      have hfalse : Literal.eval w lit = false := by
        rw [Literal.eval_eq w lit (value := value) (by rw [hv]; exact hw), h lit (by simp) hv]
        simp
      simp only [List.filter_cons, hv, bne_self_eq_false, Bool.false_eq_true, if_false,
        List.any_cons, hfalse, Bool.false_or]
      exact ih hrest
    · simp only [List.filter_cons, bne_iff_ne, ne_eq, hv, not_false_eq_true,
        if_true, List.any_cons]
      rw [ih hrest]

/-- **Core correctness theorem for the simplification step**: under any valuation
    that *agrees* with `var := value`, simplifying changes nothing. Read left to
    right it gives completeness (a satisfying valuation still satisfies the
    residual CNF of the branch matching its own value at `var`); right to left it
    gives soundness (satisfying the residual CNF suffices to satisfy the
    original). -/
theorem Cnf.eval_assignCnf (w : Std.U8 → Bool) (c : List (List cnf.Literal))
    (var : Std.U8) (value : Bool) (hw : w var = value) :
    Cnf.eval w (assignCnf var value c) = Cnf.eval w c := by
  induction c with
  | nil => simp [assignCnf, Cnf.eval]
  | cons cl rest ih =>
    by_cases hsat : clauseSatBy var value cl = true
    · rw [assignCnf_cons_of_satBy rest hsat, ih]
      simp only [Cnf.eval, List.all_cons, Clause.eval_of_satBy hw hsat, Bool.true_and]
    · rw [Bool.not_eq_true] at hsat
      rw [assignCnf_cons_of_not_satBy rest hsat]
      simp only [Cnf.eval, List.all_cons] at ih ⊢
      rw [Clause.eval_filter hw cl hsat, ih]

/-- Simplification never invents variables. Needed to compose the frame condition
    of a recursive call (which only covers the residual CNF's variables) with the
    caller's. -/
theorem cnfVars_assignCnf_subset {c : List (List cnf.Literal)} {var : Std.U8} {value : Bool}
    {k : Std.U8} (hk : k ∈ cnfVars (assignCnf var value c)) : k ∈ cnfVars c := by
  simp only [cnfVars, List.mem_flatMap] at hk ⊢
  obtain ⟨cl', hcl', hk⟩ := hk
  obtain ⟨cl, hcl, hcl'eq⟩ := assignCnf_mem_inv hcl'
  subst hcl'eq
  refine ⟨cl, hcl, ?_⟩
  simp only [clauseVars, List.mem_map] at hk ⊢
  obtain ⟨lit, hlit, hkeq⟩ := hk
  exact ⟨lit, List.mem_of_mem_filter hlit, hkeq⟩

/-- Simplification *eliminates* `var`: no deeper recursive call can ever mention,
    and therefore ever overwrite, a variable an outer level just decided. This is
    what makes the mutable `Map` threaded through the search stable on the
    decided literals, and it is the other half of the termination argument. -/
theorem not_mem_cnfVars_assignCnf (c : List (List cnf.Literal)) (var : Std.U8) (value : Bool) :
    var ∉ cnfVars (assignCnf var value c) := by
  simp only [cnfVars, List.mem_flatMap, not_exists]
  rintro cl' ⟨hcl', hvar⟩
  obtain ⟨cl, -, hcl'eq⟩ := assignCnf_mem_inv hcl'
  subst hcl'eq
  simp only [clauseVars, List.mem_map] at hvar
  obtain ⟨lit, hlit, hvareq⟩ := hvar
  have := List.of_mem_filter hlit
  simp only [bne_iff_ne, ne_eq] at this
  exact this hvareq

/-- The measure never grows (used for the head clause in the strict version
    below, where the *other* clauses only need monotonicity). -/
theorem cnfSize_assignCnf_le (c : List (List cnf.Literal)) (var : Std.U8) (value : Bool) :
    cnfSize (assignCnf var value c) ≤ cnfSize c := by
  induction c with
  | nil => simp [assignCnf, cnfSize, cnfVars]
  | cons cl rest ih =>
    by_cases hsat : clauseSatBy var value cl = true
    · rw [assignCnf_cons_of_satBy rest hsat]
      simp only [cnfSize, cnfVars, List.flatMap_cons, List.length_append] at ih ⊢
      exact le_trans ih (Nat.le_add_left _ _)
    · rw [Bool.not_eq_true] at hsat
      rw [assignCnf_cons_of_not_satBy rest hsat]
      simp only [cnfSize, cnfVars, List.flatMap_cons, List.length_append, clauseVars,
        List.length_map] at ih ⊢
      exact Nat.add_le_add (List.length_filter_le _ _) ih

/-- Termination: deciding a variable the CNF actually mentions strictly shrinks
    the measure, because every occurrence of that variable is deleted. -/
theorem cnfSize_assignCnf_lt {c : List (List cnf.Literal)} {var : Std.U8} (value : Bool)
    (hvar : var ∈ cnfVars c) : cnfSize (assignCnf var value c) < cnfSize c := by
  induction c with
  | nil => simp [cnfVars] at hvar
  | cons cl rest ih =>
    have hrest := cnfSize_assignCnf_le rest var value
    simp only [cnfSize, cnfVars] at hrest
    simp only [cnfVars, List.flatMap_cons, List.mem_append] at hvar
    /- The filtered head clause is never longer, and strictly shorter exactly when
       it mentions `var`. -/
    have hfilter_le : ((cl.filter (fun lit => lit.var != var)).map cnf.Literal.var).length ≤
        (clauseVars cl).length := by
      simp only [clauseVars, List.length_map]
      exact List.length_filter_le _ _
    by_cases hhead : var ∈ clauseVars cl
    · /- The head clause mentions `var`: it either disappears entirely or loses at
         least that one literal, and the tail can only shrink. -/
      have hpos : 0 < (clauseVars cl).length :=
        List.length_pos_iff.mpr (by intro h; rw [h] at hhead; simp at hhead)
      by_cases hsat : clauseSatBy var value cl = true
      · rw [assignCnf_cons_of_satBy rest hsat]
        simp only [cnfSize, cnfVars, List.flatMap_cons, List.length_append] at hrest ⊢
        scalar_tac
      · rw [Bool.not_eq_true] at hsat
        rw [assignCnf_cons_of_not_satBy rest hsat]
        have hfilter_lt : ((cl.filter (fun lit => lit.var != var)).map cnf.Literal.var).length <
            (clauseVars cl).length := by
          simp only [clauseVars, List.length_map]
          refine List.length_filter_lt_length_iff_exists.mpr ?_
          simp only [clauseVars, List.mem_map] at hhead
          obtain ⟨lit, hlit, hlitvar⟩ := hhead
          exact ⟨lit, hlit, by simp [hlitvar]⟩
        simp only [cnfSize, cnfVars, List.flatMap_cons, List.length_append, clauseVars]
          at hrest hfilter_lt ⊢
        scalar_tac
    · /- The head clause doesn't mention `var`, so the strict decrease comes from
         the tail, and the head can only shrink. -/
      have hlt := ih (by
        rcases hvar with hvar | hvar
        · exact absurd hvar hhead
        · simpa [cnfVars] using hvar)
      simp only [cnfSize, cnfVars] at hlt
      by_cases hsat : clauseSatBy var value cl = true
      · rw [assignCnf_cons_of_satBy rest hsat]
        simp only [cnfSize, cnfVars, List.flatMap_cons, List.length_append] at hlt ⊢
        scalar_tac
      · rw [Bool.not_eq_true] at hsat
        rw [assignCnf_cons_of_not_satBy rest hsat]
        simp only [cnfSize, cnfVars, List.flatMap_cons, List.length_append, clauseVars]
          at hlt hfilter_le ⊢
        scalar_tac

/-- Reads a `Map` back as a total valuation, defaulting the keys it doesn't hold
    to `false`. `solve_sat`'s soundness proof needs *some* total valuation to
    instantiate `dpll.spec`'s soundness clause with, and this is the one the
    returned map itself describes. -/
def Map.readback (m : expr.Map) : Std.U8 → Bool := fun k => (Map.lookupList m.val k).getD false

/-- A map that holds every key of `ks` represents its own readback there. -/
theorem Map.represents_readback (m : expr.Map) (ks : List Std.U8)
    (hpresent : ∀ k ∈ ks, Map.lookupList m.val k ≠ none) :
    Map.represents m ks (Map.readback m) := by
  intro k hk
  simp only [Map.readback]
  cases h : Map.lookupList m.val k with
  | none => exact absurd h (hpresent k hk)
  | some b => simp

/-! ### Extraction-matching layer -/

/-- **Spec theorem for `sat_solver::sat_dpll::is_satisfied`**: exactly the test
    "no clauses left", which is the success condition -- an empty conjunction is
    true, so every original clause has been discharged along the way. -/
@[step]
theorem sat_dpll.is_satisfied.spec (cnf1 : cnf.Cnf) :
    sat_dpll.is_satisfied cnf1 ⦃ (b : Bool) => b = true ↔ Cnf.contents cnf1 = [] ⦄ := by
  unfold sat_dpll.is_satisfied
  step*
  simp_all

/-- **Spec theorem for `sat_solver::sat_dpll::has_empty_clause`'s loop.** -/
@[step]
theorem sat_dpll.has_empty_clause_loop.spec (iter : core.slice.iter.Iter cnf.Clause) :
    sat_dpll.has_empty_clause_loop iter ⦃ (b : Bool) =>
      b = true ↔ [] ∈ iter.val.map (·.val) ⦄ := by
  unfold sat_dpll.has_empty_clause_loop
  step*
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
termination_by iter.val.length
decreasing_by
  obtain ⟨l, hl⟩ := iter
  cases l with
  | nil => simp_all
  | cons e es => simp_all

/-- **Spec theorem for `sat_solver::sat_dpll::has_empty_clause`**: the conflict
    test, sound by `Cnf.eval_eq_false_of_nil_mem`. -/
@[step]
theorem sat_dpll.has_empty_clause.spec (cnf1 : cnf.Cnf) :
    sat_dpll.has_empty_clause cnf1 ⦃ (b : Bool) =>
      b = true ↔ [] ∈ Cnf.contents cnf1 ⦄ := by
  unfold sat_dpll.has_empty_clause
  step*
  simp_all

/-- **Spec theorem for `sat_solver::sat_dpll::find_unit_literal`'s loop.** -/
@[step]
theorem sat_dpll.find_unit_literal_loop.spec (iter : core.slice.iter.Iter cnf.Clause) :
    sat_dpll.find_unit_literal_loop iter ⦃ (r : core.option.Option cnf.Literal) =>
      (∀ lit, r = some lit → [lit] ∈ iter.val.map (·.val)) ∧
      (r = none → ∀ cl ∈ iter.val.map (·.val), cl.length ≠ 1) ⦄ := by
  unfold sat_dpll.find_unit_literal_loop
  step*
  · obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es => simp_all
  · obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es =>
      /- The clause has length 1 and `l` is its element at index 0, so it *is*
         the singleton `[l]` -- the unit clause the postcondition asks for. -/
      simp_all [List.length_eq_one_iff]
      obtain ⟨a, ha⟩ := i_post
      rw [ha] at l_post
      simp only [List.getElem?_cons_zero, Option.some.injEq] at l_post
      left
      rw [ha, l_post]
  · obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es => simp_all
termination_by iter.val.length
decreasing_by
  obtain ⟨ls, hls⟩ := iter
  cases ls with
  | nil => simp_all
  | cons e es => simp_all

/-- **Spec theorem for `sat_solver::sat_dpll::find_unit_literal`**: whatever it
    returns really is a unit clause of `cnf1` -- which is all the search needs,
    since *which* unit gets propagated first is irrelevant to both soundness and
    completeness. -/
@[step]
theorem sat_dpll.find_unit_literal.spec (cnf1 : cnf.Cnf) :
    sat_dpll.find_unit_literal cnf1 ⦃ (r : core.option.Option cnf.Literal) =>
      (∀ lit, r = some lit → [lit] ∈ Cnf.contents cnf1) ∧
      (r = none → ∀ cl ∈ Cnf.contents cnf1, cl.length ≠ 1) ⦄ := by
  unfold sat_dpll.find_unit_literal
  step*
  simp_all

/-- **Spec theorem for `sat_solver::sat_dpll::find_branch_var`'s loop.** -/
@[step]
theorem sat_dpll.find_branch_var_loop.spec (iter : core.slice.iter.Iter cnf.Clause) :
    sat_dpll.find_branch_var_loop iter ⦃ (r : core.option.Option Std.U8) =>
      (∀ v, r = some v → v ∈ cnfVars (iter.val.map (·.val))) ∧
      (r = none → ∀ cl ∈ iter.val.map (·.val), cl = []) ⦄ := by
  unfold sat_dpll.find_branch_var_loop
  step*
  · obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es => simp_all
  · obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es =>
      /- The head clause is empty, so it contributes no variables: both conjuncts
         come straight from the recursive call's. -/
      simp_all
      intro v hv
      simpa [cnfVars, clauseVars] using r_post1 v hv
  · /- The `hi` side-condition of indexing: the clause isn't empty. -/
    rename_i hb
    have hne : clause.val ≠ [] := fun h => hb (b_post.mpr h)
    have := List.length_pos_iff.mpr hne
    scalar_tac
  · obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es =>
      /- `l` is the first literal of the first non-empty clause, so its variable
         is one of the CNF's. -/
      simp_all
      have hmem : l ∈ e.val := List.mem_of_getElem? l_post
      simp only [cnfVars, List.flatMap_cons, List.mem_append, clauseVars, List.mem_map]
      exact Or.inl ⟨l, hmem, rfl⟩
termination_by iter.val.length
decreasing_by
  obtain ⟨ls, hls⟩ := iter
  cases ls with
  | nil => simp_all
  | cons e es => simp_all

/-- **Spec theorem for `sat_solver::sat_dpll::find_branch_var`**: the decision
    heuristic is unconstrained (any variable of `cnf1` is a sound and complete
    split), so the spec only pins down that the variable *is* one of `cnf1`'s --
    plus the `none` case, which the search's own case analysis needs in order to
    rule that branch out as unreachable: a CNF with no non-empty clause is either
    empty (handled by `is_satisfied`) or holds the empty clause (handled by
    `has_empty_clause`). -/
@[step]
theorem sat_dpll.find_branch_var.spec (cnf1 : cnf.Cnf) :
    sat_dpll.find_branch_var cnf1 ⦃ (r : core.option.Option Std.U8) =>
      (∀ v, r = some v → v ∈ cnfVars (Cnf.contents cnf1)) ∧
      (r = none → ∀ cl ∈ Cnf.contents cnf1, cl = []) ⦄ := by
  unfold sat_dpll.find_branch_var
  step*
  simp_all

/-- **Spec theorem for `sat_solver::sat_dpll::assign_clause`'s loop**, generalized
    over the already-accumulated prefix `lits`.

    No `Usize.max` headroom hypothesis is needed beyond `Vec`'s own invariant: the
    loop pushes at most one literal per literal of the clause it is consuming, so
    the final push happens at `lits.val.length = clause.val.length - 1`. -/
@[step]
theorem sat_dpll.assign_clause_loop.spec (iter : core.slice.iter.Iter cnf.Literal)
    (var : Std.U8) (value : Bool) (lits : alloc.vec.Vec cnf.Literal)
    (hlen : lits.val.length + iter.val.length ≤ Usize.max) :
    sat_dpll.assign_clause_loop iter var value lits ⦃ (r : core.option.Option cnf.Clause) =>
      Option.map (fun (cl : cnf.Clause) => cl.val) r =
        Option.map (fun rest => lits.val ++ rest) (assignClause var value iter.val) ⦄ := by
  unfold sat_dpll.assign_clause_loop
  step*
  · /- Iterator exhausted: nothing of `var` was ever seen, so the clause survives
       as the accumulated prefix. -/
    obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all [assignClause, clauseSatBy]
    | cons e es => simp_all
  · /- A literal of `var` that `value` makes true: the clause is satisfied. -/
    obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es =>
      simp_all
      exact assignClause_cons_sat es ‹e.var = var› ‹¬e.negated = value›
  · obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es =>
      simp_all
      all_goals scalar_tac
  · /- A literal of `var` that `value` makes false: it drops out. -/
    obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es =>
      simp_all
      rw [assignClause_cons_drop es ‹e.var = var› (by simp_all)]
  · /- `Vec.push`'s headroom: one more literal fits, since the whole clause does. -/
    obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es =>
      simp_all
      all_goals scalar_tac
  · obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es =>
      simp_all
      all_goals scalar_tac
  · /- A literal of another variable: it is kept, and the accumulated prefix grows
       by exactly it. Done without `simp_all` on the way in: it normalizes
       `lit.var ≠ var` to a `U8.val` inequality, which no longer matches
       `assignClause_cons_keep`'s hypothesis. -/
    rcases hiter : iter.val with _ | ⟨e, es⟩
    · simp_all
    · simp only [hiter] at o_post
      obtain ⟨hoe, hiter1⟩ := o_post
      have hlit : lit = e := Option.some.inj ((‹o = some lit›).symm.trans hoe)
      subst hlit
      rw [assignClause_cons_keep es ‹¬lit.var = var›, Option.map_map, r_post, hiter1]
      simp [Function.comp_def, lits1_post, l_post]
termination_by iter.val.length
decreasing_by
  /- Two recursive calls (the drop and the keep branch), same argument for both:
     the iterator lost its head. -/
  all_goals
    rcases hiter : iter.val with _ | ⟨e, es⟩
    · simp_all
    · simp only [hiter] at o_post
      obtain ⟨-, hrest⟩ := o_post
      rw [hrest]
      simp

/-- **Spec theorem for `sat_solver::sat_dpll::assign_clause`**: matches
    `assignClause`. -/
@[step]
theorem sat_dpll.assign_clause.spec (clause : cnf.Clause) (var : Std.U8) (value : Bool) :
    sat_dpll.assign_clause clause var value ⦃ (r : core.option.Option cnf.Clause) =>
      Option.map (fun (cl : cnf.Clause) => cl.val) r = assignClause var value clause.val ⦄ := by
  unfold sat_dpll.assign_clause
  step*
  simp_all

/-- **Spec theorem for `sat_solver::sat_dpll::assign_cnf`'s loop**, generalized
    over the already-accumulated prefix `clauses`. -/
@[step]
theorem sat_dpll.assign_cnf_loop.spec (iter : core.slice.iter.Iter cnf.Clause)
    (var : Std.U8) (value : Bool) (clauses : alloc.vec.Vec cnf.Clause)
    (hlen : clauses.val.length + iter.val.length ≤ Usize.max) :
    sat_dpll.assign_cnf_loop iter var value clauses ⦃ (r : alloc.vec.Vec cnf.Clause) =>
      Cnf.contents r = Cnf.contents clauses ++ assignCnf var value (iter.val.map (·.val)) ⦄ := by
  unfold sat_dpll.assign_cnf_loop
  step*
  · /- Iterator exhausted. -/
    obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all [assignCnf]
    | cons e es => simp_all
  · obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es =>
      simp_all
      all_goals scalar_tac
  · /- The head clause was satisfied outright, so it disappears. -/
    rcases hiter : iter.val with _ | ⟨e, es⟩
    · simp_all
    · simp only [hiter] at o_post
      obtain ⟨hoe, hiter1⟩ := o_post
      have hcl : clause = e := Option.some.inj ((‹o = some clause›).symm.trans hoe)
      subst hcl
      rw [List.map_cons, assignCnf_cons_of_satBy _ (assignClause_inv_none (by simp_all)),
        r_post, hiter1]
  · obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es =>
      simp_all
      all_goals scalar_tac
  · obtain ⟨ls, hls⟩ := iter
    cases ls with
    | nil => simp_all
    | cons e es =>
      simp_all
      all_goals scalar_tac
  · /- The head clause survived, simplified: it is prepended to the rest. -/
    rcases hiter : iter.val with _ | ⟨e, es⟩
    · simp_all
    · simp only [hiter] at o_post
      obtain ⟨hoe, hiter1⟩ := o_post
      have hcl : clause = e := Option.some.inj ((‹o = some clause›).symm.trans hoe)
      subst hcl
      have heq : assignClause var value clause.val = some c.val := by
        rw [← o1_post, ‹o1 = some c›]; rfl
      obtain ⟨hsat, hc⟩ := assignClause_inv_some heq
      rw [List.map_cons, assignCnf_cons_of_not_satBy _ hsat, r_post, hiter1, ← hc]
      simp [Cnf.contents, clauses1_post]
termination_by iter.val.length
decreasing_by
  all_goals
    rcases hiter : iter.val with _ | ⟨e, es⟩
    · simp_all
    · simp only [hiter] at o_post
      obtain ⟨-, hrest⟩ := o_post
      rw [hrest]
      simp

/-- **Spec theorem for `sat_solver::sat_dpll::assign_cnf`**: matches `assignCnf`. -/
@[step]
theorem sat_dpll.assign_cnf.spec (cnf1 : cnf.Cnf) (var : Std.U8) (value : Bool) :
    sat_dpll.assign_cnf cnf1 var value ⦃ (r : cnf.Cnf) =>
      Cnf.contents r = assignCnf var value (Cnf.contents cnf1) ⦄ := by
  unfold sat_dpll.assign_cnf
  step*
  simp_all

/-- **Spec theorem for `sat_solver::sat_dpll::dpll`** -- the search invariant, and
    the one substantial proof in this file. Four clauses, in the order the
    recursion consumes them:

    1. *Frame*: variables the residual CNF doesn't mention are left untouched.
       This is what protects the literals decided at outer recursion levels, and
       it composes down the recursion because `assign_cnf` only ever shrinks the
       variable set (`cnfVars_assignCnf_subset`).
    2. *Presence is monotone*: a key already in the map stays in it. Together with
       `hpresent` this keeps `expr.Map.insert`'s disjunctive `hlen` side-condition
       discharged on the "already present, pure overwrite" side all the way down,
       so no `Usize.max` growth room is ever needed inside the search (same trick
       as `sat_naive.check_possible_valuations.spec`).
    3. *Soundness*: on success, *every* valuation agreeing with the returned map on
       the residual CNF's variables satisfies that CNF. Phrasing it for all such
       valuations rather than producing one witness is what lets `solve_sat`
       instantiate it with `Map.readback val1` -- the returned map read back as a
       total valuation. Note the invariant deliberately says nothing about the
       map's content at variables the search never decided: a successful leaf has
       an *empty* residual CNF, so those are genuinely free, and stale values left
       behind by a failed branch are harmless.
    4. *Completeness*: a satisfiable residual CNF always returns `true`.

    `sat_dpll.dpll` is a `partial_fixpoint` definition, so this has to be proved
    by strong induction on `cnfVarCount (Cnf.contents cnf1)`
    (`cnfVarCount_assignCnf_lt` supplies the decrease), not by `unfold` +
    `step*` alone. -/
@[step]
theorem sat_dpll.dpll.spec (cnf1 : cnf.Cnf) (val : expr.Map)
    (hpresent : ∀ k ∈ cnfVars (Cnf.contents cnf1), Map.lookupList val.val k ≠ none) :
    sat_dpll.dpll cnf1 val ⦃ (b : Bool) (val1 : expr.Map) =>
      (∀ k, k ∉ cnfVars (Cnf.contents cnf1) →
        Map.lookupList val1.val k = Map.lookupList val.val k) ∧
      (∀ k, Map.lookupList val.val k ≠ none → Map.lookupList val1.val k ≠ none) ∧
      (b = true → ∀ w : Std.U8 → Bool,
        (∀ k ∈ cnfVars (Cnf.contents cnf1), Map.lookupList val1.val k = some (w k)) →
        Cnf.eval w (Cnf.contents cnf1) = true) ∧
      ((∃ w : Std.U8 → Bool, Cnf.eval w (Cnf.contents cnf1) = true) → b = true) ⦄ := by
  sorry

/-- **Soundness**: if `sat_dpll::solve_sat` returns a valuation, it satisfies `e`.

    The returned map is total on `varsOf e` (it starts life as
    `sat_naive.initial_valuation (collect_vars e)` and the search only ever
    overwrites entries), so `evaluate` cannot error on it -- the statement is
    phrased as `Ok true`, never matched against `Err`, exactly like the naive
    solvers'.

    `hbound` is the classic worst-case CNF blowup bound `cnf.to_cnf.spec` needs;
    it subsumes the `exprSize e < Usize.max` that `initial_valuation.spec` and
    `collect_vars.spec` ask for, since `exprSize e < 2 ^ exprSize e`. -/
theorem sat_dpll.solve_sat_sound (e : expr.Expr) (hbound : 2 ^ exprSize e ≤ Usize.max) :
    sat_dpll.solve_sat e ⦃ (result : core.option.Option expr.Map) =>
      ∀ v, result = some v →
        expr.evaluate e v ⦃ (r : core.result.Result Bool Unit) =>
          r = core.result.Result.Ok true ⦄ ⦄ := by
  sorry

/-- **Completeness**: if `e` has a satisfying valuation at all, `sat_dpll::solve_sat`
    finds one.

    Unlike the naive solvers, this goes through the CNF: `Cnf.eval_cnfPure` turns
    `evalPure w e = true` into `Cnf.eval w (cnfPure e false) = true`, which is
    what `dpll.spec`'s completeness clause consumes. That step is only valid
    because `to_cnf` is equivalence-preserving rather than merely
    equisatisfiability-preserving (no auxiliary variables -- see `Cnf.lean`); a
    Tseitin-style encoding would need the witness to be extended to the auxiliary
    variables first. -/
theorem sat_dpll.solve_sat_complete (e : expr.Expr) (w : Std.U8 → Bool)
    (hbound : 2 ^ exprSize e ≤ Usize.max) (hsat : evalPure w e = true) :
    sat_dpll.solve_sat e ⦃ (result : core.option.Option expr.Map) => result ≠ none ⦄ := by
  sorry

end sat_solver
