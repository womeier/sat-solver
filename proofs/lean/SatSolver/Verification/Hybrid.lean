/- Pure reference semantics for `cnf_transform_hybrid::to_cnf`, and its correctness.

The hybrid sits between the other two transformations, and its proof does too. Like
`Cnf.lean` it distributes, so where it distributes it is exactly equivalence-preserving;
like `Tseitin.lean` it names subformulas, so where it names it is only equisatisfiable.

The one real difference from Tseitin is that the definitions are *one-directional*:
naming a clause list `c` by `g` emits only `g → c`, i.e. one clause `neg g :: cl` per
`cl ∈ c`, rather than a biconditional. So a gate is **not** forced -- `w g` may be false
where the subformula it names is true -- and consequently:

  * **Soundness** (`cnfRec_sound`) is an *implication*, not the equality Tseitin enjoys:
    satisfying the renamed CNF (together with the definitions) implies satisfying the
    original, and that is all.
  * **Completeness** (`cnfRec_complete`) is where it comes back: choosing `w g` to be
    the value `c` actually takes makes the replacement value-preserving, so the
    equality does hold for the witness the proof builds. -/
import SatSolver.Extraction
import SatSolver.Verification.Prelude
import SatSolver.Verification.MapLemmas
import SatSolver.Verification.Semantics
import SatSolver.Verification.Cnf
import SatSolver.Verification.Encoding

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

/-- Pure counterpart of `cnf_transform_hybrid::Renamer`. The definition clauses are
    kept apart from the body precisely so that no `neg g` is ever distributed into
    anything -- which is what keeps every gate positive outside its own definition. -/
structure Hybrid.State where
  next : Nat
  defs : List (List cnf.Literal)

namespace Hybrid

def fresh (s : State) : Option (Std.U16 × State) :=
  match freshVar s.next with
  | none => none
  | some v => some (v, { s with next := s.next + 1 })

@[simp]
theorem fresh_eq_some {s : State} {v : Std.U16} {s' : State} :
    fresh s = some (v, s') ↔
      v.val = s.next ∧ s.next < 2 ^ 16 ∧ s' = { s with next := s.next + 1 } := by
  simp only [fresh]
  cases h : freshVar s.next with
  | none =>
    rw [freshVar] at h
    simp only [reduceCtorEq, false_iff, not_and]
    intro hval hlt
    exact absurd (freshVar_eq_some.mpr ⟨hval, hlt⟩) (by rw [freshVar]; simp [h])
  | some u =>
    obtain ⟨huval, hlt⟩ := freshVar_eq_some.mp h
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨huval, hlt, rfl⟩
    · rintro ⟨hv, -, rfl⟩
      have : u = v := by apply UScalar.eq_of_val_eq; rw [huval, hv]
      simp [this]

/-- `Renamer::rename`: replace `c` by a single fresh variable, filing `g → c` under the
    definitions. -/
def rename (s : State) (c : List (List cnf.Literal)) :
    Option (List (List cnf.Literal) × State) :=
  match fresh s with
  | none => none
  | some (g, s1) =>
    some ([[pos g]], { s1 with defs := s1.defs ++ c.map (fun cl => neg g :: cl) })

/-- `Renamer::disjoin`: distributing costs `n * m` clauses, naming one side costs
    `n + m`, so distribute exactly when the former is no worse. -/
def disjoin (s : State) (c1 c2 : List (List cnf.Literal)) :
    Option (List (List cnf.Literal) × State) :=
  if c1.length * c2.length ≤ c1.length + c2.length then
    some (distributeList c1 c2, s)
  else if c2.length ≤ c1.length then
    match rename s c1 with
    | none => none
    | some (named, s1) => some (distributeList named c2, s1)
  else
    match rename s c2 with
    | none => none
    | some (named, s1) => some (distributeList c1 named, s1)

/-- `Renamer::cnf`: the same polarity-threading recursion as `cnfPure`, with `disjoin`
    standing in for the unconditional `distributeList`. -/
def cnfRec (s : State) : expr.Expr → Bool → Option (List (List cnf.Literal) × State)
  | .True, negate => some (if negate then [[]] else [], s)
  | .False, negate => some (if negate then [] else [[]], s)
  | .Variable v, negate => some ([[⟨v, negate⟩]], s)
  | .Neg e, negate => cnfRec s e (!negate)
  | .Conj e1 e2, negate =>
    match cnfRec s e1 negate with
    | none => none
    | some (c1, s1) =>
      match cnfRec s1 e2 negate with
      | none => none
      | some (c2, s2) => if negate then disjoin s2 c1 c2 else some (c1 ++ c2, s2)
  | .Disj e1 e2, negate =>
    match cnfRec s e1 negate with
    | none => none
    | some (c1, s1) =>
      match cnfRec s1 e2 negate with
      | none => none
      | some (c2, s2) => if negate then some (c1 ++ c2, s2) else disjoin s2 c1 c2

def initial (e : expr.Expr) : State :=
  { next := (varsOf e).foldl bump 0, defs := [] }

/-- Pure counterpart of `cnf_transform_hybrid::to_cnf`: body first, definitions after. -/
def toCnf (e : expr.Expr) : Option (List (List cnf.Literal)) :=
  match cnfRec (initial e) e false with
  | none => none
  | some (body, s) => some (body ++ s.defs)

/-- Every variable in `s.defs` is one the renamer has already reached. -/
def State.Wf (s : State) : Prop := ∀ k ∈ cnfVars s.defs, k.val < s.next

/-! ### Clause-list plumbing -/

/-- Consing a literal onto every clause of `c` ORs that literal against the whole CNF. -/
theorem Cnf.eval_map_cons (w : Std.U16 → Bool) (l0 : cnf.Literal)
    (c : List (List cnf.Literal)) :
    Cnf.eval w (c.map (fun cl => l0 :: cl)) = (Literal.eval w l0 || Cnf.eval w c) := by
  simp only [Cnf.eval, List.all_map, Function.comp_def, Clause.eval, List.any_cons]
  exact Cnf.eval_or_distrib (Literal.eval w l0) c (fun cl => cl.any (Literal.eval w))

theorem mem_cnfVars_map_cons {l0 : cnf.Literal} {c : List (List cnf.Literal)}
    {k : Std.U16} (hk : k ∈ cnfVars (c.map (fun cl => l0 :: cl))) :
    k = l0.var ∨ k ∈ cnfVars c := by
  simp only [cnfVars, List.flatMap_map, List.mem_flatMap, clauseVars,
    List.map_cons, List.mem_cons] at hk
  simp only [cnfVars, List.mem_flatMap]
  obtain ⟨cl, hcl, hk⟩ := hk
  rcases hk with rfl | hk
  · exact Or.inl rfl
  · exact Or.inr ⟨cl, hcl, hk⟩

/-! ### Monotonicity -/

theorem rename_defs_prefix {s s' : State} {c named : List (List cnf.Literal)}
    (h : rename s c = some (named, s')) : s.defs <+: s'.defs := by
  simp only [rename] at h
  split at h
  · simp at h
  · rename_i g s1 hf
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    rw [fresh_eq_some] at hf
    obtain ⟨-, -, rfl⟩ := hf
    subst hs'
    exact List.prefix_append _ _

theorem rename_next_le {s s' : State} {c named : List (List cnf.Literal)}
    (h : rename s c = some (named, s')) : s.next ≤ s'.next := by
  simp only [rename] at h
  split at h
  · simp at h
  · rename_i g s1 hf
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    rw [fresh_eq_some] at hf
    obtain ⟨-, -, rfl⟩ := hf
    subst hs'
    exact Nat.le_succ _

theorem disjoin_defs_prefix {s s' : State} {c1 c2 C : List (List cnf.Literal)}
    (h : disjoin s c1 c2 = some (C, s')) : s.defs <+: s'.defs := by
  simp only [disjoin] at h
  split at h
  · injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; exact List.prefix_refl _
  · split at h <;>
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hs'
        exact rename_defs_prefix hr

theorem disjoin_next_le {s s' : State} {c1 c2 C : List (List cnf.Literal)}
    (h : disjoin s c1 c2 = some (C, s')) : s.next ≤ s'.next := by
  simp only [disjoin] at h
  split at h
  · injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; exact Nat.le_refl _
  · split at h <;>
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hs'
        exact rename_next_le hr

/-- Naming costs exactly one gate. -/
theorem rename_next_eq {s s' : State} {c named : List (List cnf.Literal)}
    (h : rename s c = some (named, s')) : s'.next = s.next + 1 := by
  simp only [rename] at h
  split at h
  · simp at h
  · rename_i g s1 hf
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    rw [fresh_eq_some] at hf
    obtain ⟨-, -, rfl⟩ := hf
    subst hs'
    rfl

/-- ...and `disjoin` names at most one side, so it costs at most one. -/
theorem disjoin_next_le_succ {s s' : State} {c1 c2 C : List (List cnf.Literal)}
    (h : disjoin s c1 c2 = some (C, s')) : s'.next ≤ s.next + 1 := by
  simp only [disjoin] at h
  split at h
  · injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; omega
  · split at h <;>
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hs'
        rw [rename_next_eq hr]

/-- **At most one gate per AST node.** The counterpart of `cnfRec_next_le`, and the bound
    a caller needs to size an array by the encoded CNF: `disjoin` is the only thing that
    allocates, and there is one `disjoin` per binary node. -/
theorem cnfRec_next_le_add {e : expr.Expr} {negate : Bool} {s s' : State}
    {C : List (List cnf.Literal)} (h : cnfRec s e negate = some (C, s')) :
    s'.next ≤ s.next + exprSize e := by
  induction e generalizing s s' C negate with
  | True | False | Variable v =>
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; simp [exprSize]
  | Neg e ih =>
    have := ih h
    simp only [exprSize]
    omega
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        have hb1 := ih1 h1
        have hb2 := ih2 h2
        simp only [exprSize]
        split at h
        all_goals
          first
          | (injection h with h
             obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
             subst hs'; omega)
          | (have := disjoin_next_le_succ h; omega)

theorem cnfRec_defs_prefix {e : expr.Expr} {negate : Bool} {s s' : State}
    {C : List (List cnf.Literal)} (h : cnfRec s e negate = some (C, s')) :
    s.defs <+: s'.defs := by
  induction e generalizing s s' C negate with
  | True | False | Variable v =>
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; exact List.prefix_refl _
  | Neg e ih => exact ih h
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        /- `Conj` disjoins under negation and appends otherwise, `Disj` the other way
           round, so the two `split` branches arrive in opposite orders. -/
        split at h <;>
          first
            | (injection h with h
               obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
               subst hs'
               exact (ih1 h1).trans (ih2 h2))
            | exact ((ih1 h1).trans (ih2 h2)).trans (disjoin_defs_prefix h)

theorem cnfRec_next_le {e : expr.Expr} {negate : Bool} {s s' : State}
    {C : List (List cnf.Literal)} (h : cnfRec s e negate = some (C, s')) :
    s.next ≤ s'.next := by
  induction e generalizing s s' C negate with
  | True | False | Variable v =>
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; exact Nat.le_refl _
  | Neg e ih => exact ih h
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        split at h <;>
          first
            | (injection h with h
               obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
               subst hs'
               exact Nat.le_trans (ih1 h1) (ih2 h2))
            | exact Nat.le_trans (Nat.le_trans (ih1 h1) (ih2 h2)) (disjoin_next_le h)


/-! ### Freshness bookkeeping -/

theorem rename_vars_lt {s s' : State} {c named : List (List cnf.Literal)}
    (h : rename s c = some (named, s')) : ∀ k ∈ cnfVars named, k.val < s'.next := by
  simp only [rename] at h
  split at h
  · simp at h
  · rename_i g s1 hf
    injection h with h
    obtain ⟨hnamed, hs'⟩ := Prod.mk.injEq .. ▸ h
    rw [fresh_eq_some] at hf
    obtain ⟨hgval, -, rfl⟩ := hf
    subst hnamed; subst hs'
    intro k hk
    simp only [cnfVars, List.flatMap_cons, List.flatMap_nil, List.append_nil, clauseVars,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, var_pos] at hk
    subst hk; simp [hgval]

theorem rename_wf {s s' : State} {c named : List (List cnf.Literal)}
    (hwf : State.Wf s) (hc : ∀ k ∈ cnfVars c, k.val < s.next)
    (h : rename s c = some (named, s')) : State.Wf s' := by
  simp only [rename] at h
  split at h
  · simp at h
  · rename_i g s1 hf
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    rw [fresh_eq_some] at hf
    obtain ⟨hgval, -, rfl⟩ := hf
    subst hs'
    intro k hk
    show k.val < s.next + 1
    simp only [cnfVars_append] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact Nat.lt_succ_of_lt (hwf k hk)
    · rcases mem_cnfVars_map_cons hk with rfl | hk
      · simp [hgval]
      · exact Nat.lt_succ_of_lt (hc k hk)

theorem disjoin_vars_lt {s s' : State} {c1 c2 C : List (List cnf.Literal)}
    (h1 : ∀ k ∈ cnfVars c1, k.val < s.next) (h2 : ∀ k ∈ cnfVars c2, k.val < s.next)
    (h : disjoin s c1 c2 = some (C, s')) : ∀ k ∈ cnfVars C, k.val < s'.next := by
  have hmono := disjoin_next_le h
  simp only [disjoin] at h
  split at h
  · injection h with h
    obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hC; subst hs'
    intro k hk
    rcases mem_cnfVars_distributeList hk with hk | hk
    · exact h1 k hk
    · exact h2 k hk
  · split at h
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hC; subst hs'
        intro k hk
        rcases mem_cnfVars_distributeList hk with hk | hk
        · exact rename_vars_lt hr k hk
        · exact Nat.lt_of_lt_of_le (h2 k hk) (rename_next_le hr)
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hC; subst hs'
        intro k hk
        rcases mem_cnfVars_distributeList hk with hk | hk
        · exact Nat.lt_of_lt_of_le (h1 k hk) (rename_next_le hr)
        · exact rename_vars_lt hr k hk

theorem disjoin_wf {s s' : State} {c1 c2 C : List (List cnf.Literal)} (hwf : State.Wf s)
    (h1 : ∀ k ∈ cnfVars c1, k.val < s.next) (h2 : ∀ k ∈ cnfVars c2, k.val < s.next)
    (h : disjoin s c1 c2 = some (C, s')) : State.Wf s' := by
  simp only [disjoin] at h
  split at h
  · injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; exact hwf
  · split at h
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hs'; exact rename_wf hwf h1 hr
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hs'; exact rename_wf hwf h2 hr

theorem cnfRec_vars_lt {e : expr.Expr} {negate : Bool} {s s' : State}
    {C : List (List cnf.Literal)} (hvars : ∀ k ∈ varsOf e, k.val < s.next)
    (h : cnfRec s e negate = some (C, s')) : ∀ k ∈ cnfVars C, k.val < s'.next := by
  induction e generalizing s s' C negate with
  | True | False =>
    injection h with h
    obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hC; subst hs'
    intro k hk
    cases negate <;> simp [cnfVars, clauseVars] at hk
  | Variable v =>
    injection h with h
    obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hC; subst hs'
    intro k hk
    simp only [cnfVars, List.flatMap_cons, List.flatMap_nil, List.append_nil, clauseVars,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
    /- `subst` eliminates the binder `v` in favour of `k`, so the bound is read off
       `hvars` at `k`. -/
    subst hk; exact hvars k (by simp [varsOf])
  | Neg e ih => exact ih (by simpa [varsOf] using hvars) h
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        have hvars1 : ∀ k ∈ varsOf e1, k.val < s.next :=
          fun k hk => hvars k (by simp [varsOf, hk])
        have hvars2 : ∀ k ∈ varsOf e2, k.val < s1.next :=
          fun k hk => Nat.lt_of_lt_of_le (hvars k (by simp [varsOf, hk])) (cnfRec_next_le h1)
        have hc1 : ∀ k ∈ cnfVars c1, k.val < s2.next :=
          fun k hk => Nat.lt_of_lt_of_le (ih1 hvars1 h1 k hk) (cnfRec_next_le h2)
        have hc2 : ∀ k ∈ cnfVars c2, k.val < s2.next := ih2 hvars2 h2
        split at h <;>
          first
            | (injection h with h
               obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
               subst hC; subst hs'
               intro k hk
               simp only [cnfVars_append] at hk
               rcases List.mem_append.mp hk with hk | hk
               · exact hc1 k hk
               · exact hc2 k hk)
            | exact disjoin_vars_lt hc1 hc2 h

theorem cnfRec_wf {e : expr.Expr} {negate : Bool} {s s' : State}
    {C : List (List cnf.Literal)} (hwf : State.Wf s)
    (hvars : ∀ k ∈ varsOf e, k.val < s.next) (h : cnfRec s e negate = some (C, s')) :
    State.Wf s' := by
  induction e generalizing s s' C negate with
  | True | False | Variable v =>
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; exact hwf
  | Neg e ih => exact ih hwf (by simpa [varsOf] using hvars) h
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        have hvars1 : ∀ k ∈ varsOf e1, k.val < s.next :=
          fun k hk => hvars k (by simp [varsOf, hk])
        have hvars2 : ∀ k ∈ varsOf e2, k.val < s1.next :=
          fun k hk => Nat.lt_of_lt_of_le (hvars k (by simp [varsOf, hk])) (cnfRec_next_le h1)
        have hwf2 : State.Wf s2 := ih2 (ih1 hwf hvars1 h1) hvars2 h2
        have hc1 : ∀ k ∈ cnfVars c1, k.val < s2.next :=
          fun k hk => Nat.lt_of_lt_of_le (cnfRec_vars_lt hvars1 h1 k hk) (cnfRec_next_le h2)
        have hc2 : ∀ k ∈ cnfVars c2, k.val < s2.next := cnfRec_vars_lt hvars2 h2
        split at h <;>
          first
            | (injection h with h
               obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
               subst hs'; exact hwf2)
            | exact disjoin_wf hwf2 hc1 hc2 h

/-! ### Soundness

One-directional definitions give an implication, not an equality: a model of the
renamed CNF is a model of the original, but not conversely at the level of a single
valuation. -/

/-- Naming is sound: if the definitions hold and the single-variable stand-in holds,
    the clause list it replaced holds. -/
theorem rename_sound {s s' : State} {c named : List (List cnf.Literal)}
    {w : Std.U16 → Bool} (h : rename s c = some (named, s'))
    (hdefs : Cnf.eval w s'.defs = true) (hnamed : Cnf.eval w named = true) :
    Cnf.eval w c = true := by
  simp only [rename] at h
  split at h
  · simp at h
  · rename_i g s1 hf
    injection h with h
    obtain ⟨hn, hs'⟩ := Prod.mk.injEq .. ▸ h
    rw [fresh_eq_some] at hf
    obtain ⟨-, -, rfl⟩ := hf
    subst hn; subst hs'
    have hg : w g = true := by
      simpa [Cnf.eval, Clause.eval] using hnamed
    rw [Cnf.eval_append] at hdefs
    have := (Bool.and_eq_true _ _ |>.mp hdefs).2
    rw [Cnf.eval_map_cons] at this
    simpa [hg] using this

theorem disjoin_sound {s s' : State} {c1 c2 C : List (List cnf.Literal)}
    {w : Std.U16 → Bool} (h : disjoin s c1 c2 = some (C, s'))
    (hdefs : Cnf.eval w s'.defs = true) (hC : Cnf.eval w C = true) :
    (Cnf.eval w c1 || Cnf.eval w c2) = true := by
  simp only [disjoin] at h
  split at h
  · injection h with h
    obtain ⟨hC', hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hC'; subst hs'
    rwa [Cnf.eval_distributeList] at hC
  · split at h
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨hC', hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hC'; subst hs'
        rw [Cnf.eval_distributeList] at hC
        rcases Bool.or_eq_true _ _ |>.mp hC with hc | hc
        · simp [rename_sound hr hdefs hc]
        · simp [hc]
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨hC', hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hC'; subst hs'
        rw [Cnf.eval_distributeList] at hC
        rcases Bool.or_eq_true _ _ |>.mp hC with hc | hc
        · simp [hc]
        · simp [rename_sound hr hdefs hc]

/-- **Core soundness**: a valuation satisfying both the body and the definitions
    satisfies `e` at the polarity `negate` asks for. -/
theorem cnfRec_sound {e : expr.Expr} {negate : Bool} {s s' : State}
    {C : List (List cnf.Literal)} {w : Std.U16 → Bool}
    (h : cnfRec s e negate = some (C, s'))
    (hdefs : Cnf.eval w s'.defs = true) (hC : Cnf.eval w C = true) :
    (evalPure w e != negate) = true := by
  induction e generalizing s s' C negate with
  | True | False =>
    injection h with h
    obtain ⟨hC', -⟩ := Prod.mk.injEq .. ▸ h
    subst hC'
    cases negate <;> simp_all [evalPure, Cnf.eval, Clause.eval]
  | Variable v =>
    injection h with h
    obtain ⟨hC', -⟩ := Prod.mk.injEq .. ▸ h
    subst hC'
    simp only [Cnf.eval, List.all_cons, List.all_nil, Bool.and_true, Clause.eval,
      List.any_cons, List.any_nil, Bool.or_false, Literal.eval] at hC
    cases negate <;> simp_all [evalPure]
  | Neg e ih =>
    have := ih h hdefs hC
    cases negate <;> cases hv : evalPure w e <;> simp_all [evalPure]
  | Conj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        have hd2 : Cnf.eval w s2.defs = true := by
          cases negate
          · simp only [Bool.false_eq_true, if_false] at h
            injection h with h
            obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
            subst hs'; exact hdefs
          · simp only [if_true] at h
            exact eval_of_prefix (disjoin_defs_prefix h) hdefs
        have hd1 : Cnf.eval w s1.defs = true :=
          eval_of_prefix (cnfRec_defs_prefix h2) hd2
        cases negate
        · /- Positive polarity: the body is the concatenation, so both halves hold. -/
          simp only [Bool.false_eq_true, if_false] at h
          injection h with h
          obtain ⟨hC', -⟩ := Prod.mk.injEq .. ▸ h
          subst hC'
          rw [Cnf.eval_append] at hC
          obtain ⟨hc1, hc2⟩ := Bool.and_eq_true _ _ |>.mp hC
          have r1 := ih1 h1 hd1 hc1
          have r2 := ih2 h2 hd2 hc2
          simp_all [evalPure]
        · /- Negative polarity: De Morgan, so one half suffices. -/
          simp only [if_true] at h
          rcases Bool.or_eq_true _ _ |>.mp (disjoin_sound h hdefs hC) with hc | hc
          · have r1 := ih1 h1 hd1 hc
            cases hv : evalPure w e1 <;> simp_all [evalPure]
          · have r2 := ih2 h2 hd2 hc
            cases hv : evalPure w e2 <;> simp_all [evalPure]
  | Disj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        have hd2 : Cnf.eval w s2.defs = true := by
          cases negate
          · simp only [Bool.false_eq_true, if_false] at h
            exact eval_of_prefix (disjoin_defs_prefix h) hdefs
          · simp only [if_true] at h
            injection h with h
            obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
            subst hs'; exact hdefs
        have hd1 : Cnf.eval w s1.defs = true :=
          eval_of_prefix (cnfRec_defs_prefix h2) hd2
        cases negate
        · simp only [Bool.false_eq_true, if_false] at h
          rcases Bool.or_eq_true _ _ |>.mp (disjoin_sound h hdefs hC) with hc | hc
          · have r1 := ih1 h1 hd1 hc
            cases hv : evalPure w e1 <;> simp_all [evalPure]
          · have r2 := ih2 h2 hd2 hc
            cases hv : evalPure w e2 <;> simp_all [evalPure]
        · simp only [if_true] at h
          injection h with h
          obtain ⟨hC', -⟩ := Prod.mk.injEq .. ▸ h
          subst hC'
          rw [Cnf.eval_append] at hC
          obtain ⟨hc1, hc2⟩ := Bool.and_eq_true _ _ |>.mp hC
          have r1 := ih1 h1 hd1 hc1
          have r2 := ih2 h2 hd2 hc2
          simp_all [evalPure]


/-! ### Completeness

The mirror image of soundness: choosing each gate to be the value of the clause list it
names makes the substitution value-preserving, so the body ends up with exactly the
truth value the naive transformation would have given it -- and the definitions come
along for free. -/

theorem Cnf.eval_eq_of_agree {w w' : Std.U16 → Bool} {c : List (List cnf.Literal)}
    {n : Nat} (hc : ∀ k ∈ cnfVars c, k.val < n)
    (hag : ∀ k : Std.U16, k.val < n → w' k = w k) : Cnf.eval w' c = Cnf.eval w c :=
  Cnf.eval_congr c (fun k hk => hag k (hc k hk))

/-- Naming is complete: give the gate the value the clause list actually takes, and
    both the definition clauses and the one-literal stand-in come out right. -/
theorem rename_complete {s s' : State} {c named : List (List cnf.Literal)}
    (hwf : State.Wf s) (hc : ∀ k ∈ cnfVars c, k.val < s.next)
    (h : rename s c = some (named, s')) (w : Std.U16 → Bool)
    (hw : Cnf.eval w s.defs = true) :
    ∃ w', (∀ k : Std.U16, k.val < s.next → w' k = w k) ∧
          Cnf.eval w' s'.defs = true ∧ Cnf.eval w' named = Cnf.eval w c := by
  simp only [rename] at h
  split at h
  · simp at h
  · rename_i g s1 hf
    injection h with h
    obtain ⟨hn, hs'⟩ := Prod.mk.injEq .. ▸ h
    rw [fresh_eq_some] at hf
    obtain ⟨hgval, -, rfl⟩ := hf
    subst hn; subst hs'
    refine ⟨upd w g (Cnf.eval w c),
      fun k hk => upd_of_ne (ne_of_val_lt hk (le_of_eq hgval.symm)), ?_, ?_⟩
    · rw [Cnf.eval_append]
      refine Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩
      · rw [Cnf.eval_upd_of_lt hwf (le_of_eq hgval.symm)]; exact hw
      · rw [Cnf.eval_map_cons, eval_neg, upd_self,
            Cnf.eval_upd_of_lt hc (le_of_eq hgval.symm)]
        cases Cnf.eval w c <;> simp
    · simp [Cnf.eval, Clause.eval]

theorem disjoin_complete {s s' : State} {c1 c2 C : List (List cnf.Literal)}
    (hwf : State.Wf s) (h1 : ∀ k ∈ cnfVars c1, k.val < s.next)
    (h2 : ∀ k ∈ cnfVars c2, k.val < s.next)
    (h : disjoin s c1 c2 = some (C, s')) (w : Std.U16 → Bool)
    (hw : Cnf.eval w s.defs = true) :
    ∃ w', (∀ k : Std.U16, k.val < s.next → w' k = w k) ∧
          Cnf.eval w' s'.defs = true ∧
          Cnf.eval w' C = (Cnf.eval w c1 || Cnf.eval w c2) := by
  simp only [disjoin] at h
  split at h
  · /- Distributed: nothing was named, so the valuation is unchanged. -/
    injection h with h
    obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hC; subst hs'
    exact ⟨w, fun _ _ => rfl, hw, Cnf.eval_distributeList w c1 c2⟩
  · split at h
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hC; subst hs'
        obtain ⟨w', hag, hd, hn⟩ := rename_complete hwf h1 hr w hw
        refine ⟨w', hag, hd, ?_⟩
        rw [Cnf.eval_distributeList, hn, Cnf.eval_eq_of_agree h2 hag]
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hC; subst hs'
        obtain ⟨w', hag, hd, hn⟩ := rename_complete hwf h2 hr w hw
        refine ⟨w', hag, hd, ?_⟩
        rw [Cnf.eval_distributeList, hn, Cnf.eval_eq_of_agree h1 hag]

/-- **Core completeness**: the body ends up with exactly the truth value `e` has, and
    the definitions are all satisfied, under a valuation that leaves everything the
    renamer had already reached alone. -/
theorem cnfRec_complete {e : expr.Expr} {negate : Bool} {s s' : State}
    {C : List (List cnf.Literal)} (hwf : State.Wf s)
    (hvars : ∀ k ∈ varsOf e, k.val < s.next) (h : cnfRec s e negate = some (C, s'))
    (w : Std.U16 → Bool) (hw : Cnf.eval w s.defs = true) :
    ∃ w', (∀ k : Std.U16, k.val < s.next → w' k = w k) ∧
          Cnf.eval w' s'.defs = true ∧
          Cnf.eval w' C = (evalPure w e != negate) := by
  induction e generalizing s s' C negate w with
  | True | False =>
    injection h with h
    obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hC; subst hs'
    refine ⟨w, fun _ _ => rfl, hw, ?_⟩
    cases negate <;> simp [evalPure, Cnf.eval, Clause.eval]
  | Variable v =>
    injection h with h
    obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hC; subst hs'
    refine ⟨w, fun _ _ => rfl, hw, ?_⟩
    cases negate <;> cases hv : w v <;>
      simp [evalPure, Cnf.eval, Clause.eval, Literal.eval, hv]
  | Neg e ih =>
    obtain ⟨w', hag, hd, hv⟩ := ih hwf (by simpa [varsOf] using hvars) h w hw
    refine ⟨w', hag, hd, ?_⟩
    rw [hv]
    cases negate <;> cases he : evalPure w e <;> simp [evalPure, he]
  | Conj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        have hvars1 : ∀ k ∈ varsOf e1, k.val < s.next :=
          fun k hk => hvars k (by simp [varsOf, hk])
        have hvars2' : ∀ k ∈ varsOf e2, k.val < s.next :=
          fun k hk => hvars k (by simp [varsOf, hk])
        have hvars2 : ∀ k ∈ varsOf e2, k.val < s1.next :=
          fun k hk => Nat.lt_of_lt_of_le (hvars2' k hk) (cnfRec_next_le h1)
        have hwf1 : State.Wf s1 := cnfRec_wf hwf hvars1 h1
        have hwf2 : State.Wf s2 := cnfRec_wf hwf1 hvars2 h2
        have hc1' : ∀ k ∈ cnfVars c1, k.val < s1.next := cnfRec_vars_lt hvars1 h1
        have hc1 : ∀ k ∈ cnfVars c1, k.val < s2.next :=
          fun k hk => Nat.lt_of_lt_of_le (hc1' k hk) (cnfRec_next_le h2)
        have hc2 : ∀ k ∈ cnfVars c2, k.val < s2.next := cnfRec_vars_lt hvars2 h2
        obtain ⟨w1, hag1, hd1, hv1⟩ := ih1 hwf hvars1 h1 w hw
        obtain ⟨w2, hag2, hd2, hv2⟩ := ih2 hwf1 hvars2 h2 w1 hd1
        /- Lift both operand values to the later valuation: `w2` only differs from `w1`
           at gates `s1.next` and above, which neither `c1` nor `varsOf e2` mentions. -/
        have hag21 : ∀ k : Std.U16, k.val < s.next → w2 k = w k :=
          fun k hk => by
            rw [hag2 k (Nat.lt_of_lt_of_le hk (cnfRec_next_le h1)), hag1 k hk]
        have hlift1 : Cnf.eval w2 c1 = (evalPure w e1 != negate) := by
          rw [Cnf.eval_eq_of_agree hc1' hag2, hv1]
        have hlift2 : Cnf.eval w2 c2 = (evalPure w e2 != negate) := by
          rw [hv2, evalPure_congr e2 (fun k hk => hag1 k (hvars2' k hk))]
        cases negate
        · simp only [Bool.false_eq_true, if_false] at h
          /- The concatenation branch: both halves have to hold, and nothing is named,
             so `w2` is already the witness. -/
          injection h with h
          obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
          subst hC; subst hs'
          refine ⟨w2, hag21, hd2, ?_⟩
          rw [Cnf.eval_append, hlift1, hlift2]
          cases h1' : evalPure w e1 <;> cases h2' : evalPure w e2 <;>
            simp [evalPure, h1', h2']
        · simp only [if_true] at h
          /- The `disjoin` branch: `disjoin_complete` supplies the gate if the decision
             rule chose to name a side, and its agreement chains onto the recursive
             ones. -/
          obtain ⟨w3, hag3, hd3, hv3⟩ := disjoin_complete hwf2 hc1 hc2 h w2 hd2
          refine ⟨w3, fun k hk => ?_, hd3, ?_⟩
          · rw [hag3 k (Nat.lt_of_lt_of_le hk
                (Nat.le_trans (cnfRec_next_le h1) (cnfRec_next_le h2))), hag21 k hk]
          · rw [hv3, hlift1, hlift2]
            cases h1' : evalPure w e1 <;> cases h2' : evalPure w e2 <;>
              simp [evalPure, h1', h2']
  | Disj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        have hvars1 : ∀ k ∈ varsOf e1, k.val < s.next :=
          fun k hk => hvars k (by simp [varsOf, hk])
        have hvars2' : ∀ k ∈ varsOf e2, k.val < s.next :=
          fun k hk => hvars k (by simp [varsOf, hk])
        have hvars2 : ∀ k ∈ varsOf e2, k.val < s1.next :=
          fun k hk => Nat.lt_of_lt_of_le (hvars2' k hk) (cnfRec_next_le h1)
        have hwf1 : State.Wf s1 := cnfRec_wf hwf hvars1 h1
        have hwf2 : State.Wf s2 := cnfRec_wf hwf1 hvars2 h2
        have hc1' : ∀ k ∈ cnfVars c1, k.val < s1.next := cnfRec_vars_lt hvars1 h1
        have hc1 : ∀ k ∈ cnfVars c1, k.val < s2.next :=
          fun k hk => Nat.lt_of_lt_of_le (hc1' k hk) (cnfRec_next_le h2)
        have hc2 : ∀ k ∈ cnfVars c2, k.val < s2.next := cnfRec_vars_lt hvars2 h2
        obtain ⟨w1, hag1, hd1, hv1⟩ := ih1 hwf hvars1 h1 w hw
        obtain ⟨w2, hag2, hd2, hv2⟩ := ih2 hwf1 hvars2 h2 w1 hd1
        /- Lift both operand values to the later valuation: `w2` only differs from `w1`
           at gates `s1.next` and above, which neither `c1` nor `varsOf e2` mentions. -/
        have hag21 : ∀ k : Std.U16, k.val < s.next → w2 k = w k :=
          fun k hk => by
            rw [hag2 k (Nat.lt_of_lt_of_le hk (cnfRec_next_le h1)), hag1 k hk]
        have hlift1 : Cnf.eval w2 c1 = (evalPure w e1 != negate) := by
          rw [Cnf.eval_eq_of_agree hc1' hag2, hv1]
        have hlift2 : Cnf.eval w2 c2 = (evalPure w e2 != negate) := by
          rw [hv2, evalPure_congr e2 (fun k hk => hag1 k (hvars2' k hk))]
        cases negate
        · simp only [Bool.false_eq_true, if_false] at h
          /- The `disjoin` branch: `disjoin_complete` supplies the gate if the decision
             rule chose to name a side, and its agreement chains onto the recursive
             ones. -/
          obtain ⟨w3, hag3, hd3, hv3⟩ := disjoin_complete hwf2 hc1 hc2 h w2 hd2
          refine ⟨w3, fun k hk => ?_, hd3, ?_⟩
          · rw [hag3 k (Nat.lt_of_lt_of_le hk
                (Nat.le_trans (cnfRec_next_le h1) (cnfRec_next_le h2))), hag21 k hk]
          · rw [hv3, hlift1, hlift2]
            cases h1' : evalPure w e1 <;> cases h2' : evalPure w e2 <;>
              simp [evalPure, h1', h2']
        · simp only [if_true] at h
          /- The concatenation branch: both halves have to hold, and nothing is named,
             so `w2` is already the witness. -/
          injection h with h
          obtain ⟨hC, hs'⟩ := Prod.mk.injEq .. ▸ h
          subst hC; subst hs'
          refine ⟨w2, hag21, hd2, ?_⟩
          rw [Cnf.eval_append, hlift1, hlift2]
          cases h1' : evalPure w e1 <;> cases h2' : evalPure w e2 <;>
            simp [evalPure, h1', h2']

/-! ### The transformation as a whole -/

/-- The initial state is well-formed: it has filed no definitions at all. -/
theorem initial_wf (e : expr.Expr) : State.Wf (initial e) := by
  intro k hk; simp [initial, cnfVars] at hk

/-- ...and its counter already sits above every variable of `e`. -/
theorem varsOf_lt_initial (e : expr.Expr) : ∀ k ∈ varsOf e, k.val < (initial e).next :=
  fun k hk => mem_lt_foldl_bump (varsOf e) 0 k hk

/-- **Soundness**: every model of the hybrid CNF satisfies `e`.

    Where the decision rule distributed, this is the same equivalence `Cnf.lean` proves;
    where it named a side, it is the one-directional definition doing its job. -/
theorem toCnf_sound {e : expr.Expr} {c : List (List cnf.Literal)} {w : Std.U16 → Bool}
    (h : toCnf e = some c) (hw : Cnf.eval w c = true) : evalPure w e = true := by
  simp only [toCnf] at h
  split at h
  · simp at h
  · rename_i body s hs
    injection h with h
    subst h
    rw [Cnf.eval_append] at hw
    obtain ⟨hbody, hdefs⟩ := Bool.and_eq_true _ _ |>.mp hw
    simpa using cnfRec_sound hs hdefs hbody

/-- **Completeness**: every model of `e` extends to a model of the hybrid CNF that
    agrees with it on all of `e`'s own variables.

    Note this is strictly stronger than it looks for the clausal inputs the hybrid is
    built for: when nothing is named the witness is `w` itself, unchanged. -/
theorem toCnf_complete {e : expr.Expr} {c : List (List cnf.Literal)} {w : Std.U16 → Bool}
    (h : toCnf e = some c) (hsat : evalPure w e = true) :
    ∃ w', (∀ k ∈ varsOf e, w' k = w k) ∧ Cnf.eval w' c = true := by
  simp only [toCnf] at h
  split at h
  · simp at h
  · rename_i body s hs
    injection h with h
    subst h
    obtain ⟨w', hag, hdefs, hbody⟩ :=
      cnfRec_complete (initial_wf e) (varsOf_lt_initial e) hs w (by simp [initial, Cnf.eval])
    refine ⟨w', fun k hk => hag k (varsOf_lt_initial e k hk), ?_⟩
    rw [Cnf.eval_append]
    refine Bool.and_eq_true _ _ |>.mpr ⟨?_, hdefs⟩
    rw [hbody]
    simp [hsat]

/-! ### Size bounds

The extracted `disjoin` computes `n * m` in `usize` *before* deciding whether to
distribute, so the extraction layer needs that product not to overflow. These bounds are
what make that discharge: a body of at most one clause per AST node, and definitions of
at most one per pair of nodes. -/

theorem disjoin_length_le {s s' : State} {c1 c2 C : List (List cnf.Literal)}
    (h : disjoin s c1 c2 = some (C, s')) : C.length ≤ c1.length + c2.length := by
  simp only [disjoin] at h
  split at h
  · rename_i hle
    injection h with h
    obtain ⟨hC, -⟩ := Prod.mk.injEq .. ▸ h
    subst hC
    rw [distributeList_length]; exact hle
  · split at h
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨hC, -⟩ := Prod.mk.injEq .. ▸ h
        subst hC
        simp only [rename] at hr
        split at hr
        · simp at hr
        · rename_i g s1 hf
          injection hr with hr
          obtain ⟨hn, -⟩ := Prod.mk.injEq .. ▸ hr
          subst hn
          rw [distributeList_length]; simp
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨hC, -⟩ := Prod.mk.injEq .. ▸ h
        subst hC
        simp only [rename] at hr
        split at hr
        · simp at hr
        · rename_i g s1 hf
          injection hr with hr
          obtain ⟨hn, -⟩ := Prod.mk.injEq .. ▸ hr
          subst hn
          rw [distributeList_length]; simp

theorem disjoin_defs_length_le {s s' : State} {c1 c2 C : List (List cnf.Literal)}
    (h : disjoin s c1 c2 = some (C, s')) :
    s'.defs.length ≤ s.defs.length + (c1.length + c2.length) := by
  simp only [disjoin] at h
  split at h
  · injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; simp
  · split at h <;>
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hs'
        simp only [rename] at hr
        split at hr
        · simp at hr
        · rename_i g s1 hf
          injection hr with hr
          obtain ⟨-, hs1⟩ := Prod.mk.injEq .. ▸ hr
          rw [fresh_eq_some] at hf
          obtain ⟨-, -, rfl⟩ := hf
          subst hs1
          simp

theorem cnfRec_length_le {e : expr.Expr} {negate : Bool} {s s' : State}
    {C : List (List cnf.Literal)} (h : cnfRec s e negate = some (C, s')) :
    C.length ≤ exprSize e := by
  induction e generalizing s s' C negate with
  | True | False =>
    injection h with h
    obtain ⟨hC, -⟩ := Prod.mk.injEq .. ▸ h
    subst hC; cases negate <;> simp [exprSize]
  | Variable v =>
    injection h with h
    obtain ⟨hC, -⟩ := Prod.mk.injEq .. ▸ h
    subst hC; simp [exprSize]
  | Neg e ih => exact Nat.le_trans (ih h) (by simp [exprSize])
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        have b1 := ih1 h1
        have b2 := ih2 h2
        split at h <;>
          first
            | (injection h with h
               obtain ⟨hC, -⟩ := Prod.mk.injEq .. ▸ h
               subst hC
               simp only [exprSize, List.length_append]
               grind)
            | (have := disjoin_length_le h
               simp only [exprSize]
               grind)

theorem cnfRec_defs_length_le {e : expr.Expr} {negate : Bool} {s s' : State}
    {C : List (List cnf.Literal)} (h : cnfRec s e negate = some (C, s')) :
    s'.defs.length ≤ s.defs.length + exprSize e * exprSize e := by
  induction e generalizing s s' C negate with
  | True | False | Variable v =>
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; simp
  | Neg e ih =>
    refine Nat.le_trans (ih h) ?_
    simp only [exprSize]
    grind
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        have b1 := ih1 h1
        have b2 := ih2 h2
        have l1 := cnfRec_length_le h1
        have l2 := cnfRec_length_le h2
        split at h <;>
          first
            | (injection h with h
               obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
               subst hs'
               simp only [exprSize]
               grind)
            | (have := disjoin_defs_length_le h
               simp only [exprSize]
               grind)

/-- Clauses stay short: at most one literal per AST node. The extracted `rename` builds
    `[neg g] ++ cl` with `Vec::append`, whose own overflow check this discharges. -/
theorem cnfRec_clause_length_le {e : expr.Expr} {negate : Bool} {s s' : State}
    {C : List (List cnf.Literal)} (h : cnfRec s e negate = some (C, s')) :
    ∀ cl ∈ C, cl.length ≤ exprSize e := by
  induction e generalizing s s' C negate with
  | True | False =>
    injection h with h
    obtain ⟨hC, -⟩ := Prod.mk.injEq .. ▸ h
    subst hC; cases negate <;> simp [exprSize]
  | Variable v =>
    injection h with h
    obtain ⟨hC, -⟩ := Prod.mk.injEq .. ▸ h
    subst hC; simp [exprSize]
  | Neg e ih =>
    intro cl hcl
    exact Nat.le_trans (ih h cl hcl) (by simp [exprSize])
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        have b1 := ih1 h1
        have b2 := ih2 h2
        split at h <;>
        first
        | (injection h with h
           obtain ⟨hC, -⟩ := Prod.mk.injEq .. ▸ h
           subst hC
           intro cl hcl
           simp only [exprSize]
           rcases List.mem_append.mp hcl with hcl | hcl
           · exact Nat.le_trans (b1 cl hcl) (by grind)
           · exact Nat.le_trans (b2 cl hcl) (by grind))
        | (/- `disjoin`: either a distributed pair, or one literal against the other
             side's clause. -/
          simp only [disjoin] at h
          split at h
          · injection h with h
            obtain ⟨hC, -⟩ := Prod.mk.injEq .. ▸ h
            subst hC
            intro cl hcl
            obtain ⟨cl1, hcl1, cl2, hcl2, rfl⟩ := mem_distributeList.mp hcl
            simp only [List.length_append, exprSize]
            have := b1 cl1 hcl1
            have := b2 cl2 hcl2
            grind
          · split at h <;>
            · split at h
              · simp at h
              · rename_i hr
                injection h with h
                obtain ⟨hC, -⟩ := Prod.mk.injEq .. ▸ h
                subst hC
                simp only [rename] at hr
                split at hr
                · simp at hr
                · rename_i g s3 hf
                  injection hr with hr
                  obtain ⟨hn, -⟩ := Prod.mk.injEq .. ▸ hr
                  subst hn
                  intro cl hcl
                  obtain ⟨cl1, hcl1, cl2, hcl2, rfl⟩ := mem_distributeList.mp hcl
                  simp only [List.length_append, exprSize]
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl1 hcl2
                  first
                    | (subst hcl1
                       have := b2 cl2 hcl2
                       simp only [List.length_cons, List.length_nil]
                       grind)
                    | (subst hcl2
                       have := b1 cl1 hcl1
                       simp only [List.length_cons, List.length_nil]
                       grind))

/-- `rename` always returns the one-clause, one-literal stand-in. The extraction layer
    needs this to bound the `distribute` that follows it. -/
theorem rename_named {s s' : State} {c named : List (List cnf.Literal)}
    (h : rename s c = some (named, s')) : ∃ g, named = [[pos g]] := by
  simp only [rename] at h
  split at h
  · simp at h
  · rename_i g s1 hf
    injection h with h
    obtain ⟨hn, -⟩ := Prod.mk.injEq .. ▸ h
    exact ⟨g, hn.symm⟩

/-- `rename` files one definition clause per clause it names, each one literal longer. -/
theorem rename_defs_clause_length_le {s s' : State} {c named : List (List cnf.Literal)}
    {n : Nat} (h : rename s c = some (named, s'))
    (hs : ∀ cl ∈ s.defs, cl.length ≤ n + 1) (hc : ∀ cl ∈ c, cl.length ≤ n) :
    ∀ cl ∈ s'.defs, cl.length ≤ n + 1 := by
  simp only [rename] at h
  split at h
  · simp at h
  · rename_i g s1 hf
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    rw [fresh_eq_some] at hf
    obtain ⟨-, -, rfl⟩ := hf
    subst hs'
    intro cl hcl
    simp only [List.mem_append] at hcl
    rcases hcl with hcl | hcl
    · exact hs cl hcl
    · simp only [List.mem_map] at hcl
      obtain ⟨cl0, hcl0, rfl⟩ := hcl
      simp only [List.length_cons]
      have := hc cl0 hcl0
      grind

/-- The definition clauses `disjoin` files are one literal longer than the clauses they
    name. -/
theorem disjoin_defs_clause_length_le {s s' : State} {c1 c2 C : List (List cnf.Literal)}
    {n : Nat} (h : disjoin s c1 c2 = some (C, s'))
    (hs : ∀ cl ∈ s.defs, cl.length ≤ n + 1)
    (b1 : ∀ cl ∈ c1, cl.length ≤ n) (b2 : ∀ cl ∈ c2, cl.length ≤ n) :
    ∀ cl ∈ s'.defs, cl.length ≤ n + 1 := by
  simp only [disjoin] at h
  split at h
  · injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; exact hs
  · split at h
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hs'
        exact rename_defs_clause_length_le hr hs b1
    · split at h
      · simp at h
      · rename_i hr
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hs'
        exact rename_defs_clause_length_le hr hs b2

/-- ...and so do the definition clauses throughout the recursion. -/
theorem cnfRec_defs_clause_length_le {e : expr.Expr} {negate : Bool} {s s' : State}
    {C : List (List cnf.Literal)} {n : Nat} (h : cnfRec s e negate = some (C, s'))
    (hn : exprSize e ≤ n) (hs : ∀ cl ∈ s.defs, cl.length ≤ n + 1) :
    ∀ cl ∈ s'.defs, cl.length ≤ n + 1 := by
  induction e generalizing s s' C negate with
  | True | False | Variable v =>
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; exact hs
  | Neg e ih => exact ih h (by simp only [exprSize] at hn; grind) hs
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [cnfRec] at h
    split at h
    · simp at h
    · rename_i c1 s1 h1
      split at h
      · simp at h
      · rename_i c2 s2 h2
        simp only [exprSize] at hn
        have hn1 : exprSize e1 ≤ n := by grind
        have hn2 : exprSize e2 ≤ n := by grind
        have hs2 := ih2 h2 hn2 (ih1 h1 hn1 hs)
        have b1 : ∀ cl ∈ c1, cl.length ≤ n :=
          fun cl hcl => Nat.le_trans (cnfRec_clause_length_le h1 cl hcl) hn1
        have b2 : ∀ cl ∈ c2, cl.length ≤ n :=
          fun cl hcl => Nat.le_trans (cnfRec_clause_length_le h2 cl hcl) hn2
        split at h <;>
          first
            | (injection h with h
               obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
               subst hs'; exact hs2)
            | exact disjoin_defs_clause_length_le h hs2 b1 b2

end Hybrid

end sat_solver
