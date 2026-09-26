/- Pure reference semantics for `cnf_transform_tseitin::to_cnf`, and its correctness.

Unlike the naive transformation (`Cnf.lean`), Tseitin is *not* equivalence-preserving:
it names every internal node of the formula with a fresh gate variable, so the CNF it
produces lives over a larger variable set than the input. The two halves of correctness
therefore have to be stated separately, and only one of them needs freshness:

  * **Soundness** (`tseitinEncode_sound`) needs none. The defining clauses are full
    biconditionals, so *any* valuation satisfying them already pins every gate to the
    value of the subformula it names -- whether or not the gate was chosen freshly.
  * **Completeness** (`tseitinEncode_complete`) is where freshness earns its keep: the
    witness for the original variables has to be *extended* to the gates, and that
    extension is only harmless if the gate variables are ones nothing else mentions.

The invariant carrying freshness is `State.Wf`: every variable mentioned so far -- in
the clauses already emitted, and in the constant gate if one has been allocated -- lies
strictly below `next`, which is also where the next gate will come from. -/
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

/-! ### The encoder state -/

/-- Pure counterpart of `cnf_transform_tseitin::Encoder`. `next` is a `Nat` here for the
    same reason it is a `u32` in the Rust: running off the end of the `u16` variable
    space has to be a comparison rather than an overflow. -/
structure Tseitin.State where
  next : Nat
  trueVar : Option Std.U16
  clauses : List (List cnf.Literal)

namespace Tseitin

/-- Allocating a gate. `none` is the `u16` ceiling -- `Encoder::fresh`'s `Err(())`. -/
def fresh (s : State) : Option (Std.U16 × State) :=
  match freshVar s.next with
  | none => none
  | some v => some (v, { s with next := s.next + 1 })

@[simp]
theorem fresh_eq_some {s : State} {v : Std.U16} {s' : State} :
    fresh s = some (v, s') ↔
      v.val = s.next ∧ s.next < 2 ^ 16 ∧
        s' = { s with next := s.next + 1 } := by
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

/-- The literal standing for `⊤`/`⊥`, allocating the shared constant gate on first use
    (`Encoder::constant`). -/
def constant (s : State) (value : Bool) : Option (cnf.Literal × State) :=
  match s.trueVar with
  | some v => some (if value then pos v else neg v, s)
  | none =>
    match fresh s with
    | none => none
    | some (v, s1) =>
      some (if value then pos v else neg v,
        { s1 with trueVar := some v, clauses := s1.clauses ++ [[pos v]] })

/-- Pure counterpart of `Encoder::encode`: emits the defining clauses for `e` and
    returns the literal standing for its truth value. -/
def encode (s : State) : expr.Expr → Option (cnf.Literal × State)
  | .True => constant s true
  | .False => constant s false
  | .Variable v => some (pos v, s)
  | .Neg e =>
    match encode s e with
    | none => none
    | some (l, s1) => some (flip l, s1)
  | .Conj e1 e2 =>
    match encode s e1 with
    | none => none
    | some (l1, s1) =>
      match encode s1 e2 with
      | none => none
      | some (l2, s2) =>
        match fresh s2 with
        | none => none
        | some (g, s3) =>
          some (pos g,
            { s3 with clauses :=
                s3.clauses ++ [[neg g, l1], [neg g, l2], [pos g, flip l1, flip l2]] })
  | .Disj e1 e2 =>
    match encode s e1 with
    | none => none
    | some (l1, s1) =>
      match encode s1 e2 with
      | none => none
      | some (l2, s2) =>
        match fresh s2 with
        | none => none
        | some (g, s3) =>
          some (pos g,
            { s3 with clauses :=
                s3.clauses ++ [[neg g, l1, l2], [pos g, flip l1], [pos g, flip l2]] })

/-- The initial state: `next` one past the largest variable of `e` (`Encoder::new`). -/
def initial (e : expr.Expr) : State :=
  { next := (varsOf e).foldl bump 0, trueVar := none, clauses := [] }

/-- Pure counterpart of `cnf_transform_tseitin::to_cnf`. -/
def toCnf (e : expr.Expr) : Option (List (List cnf.Literal)) :=
  match encode (initial e) e with
  | none => none
  | some (root, s) => some (s.clauses ++ [[root]])

/-! ### Monotonicity

`encode` only ever appends clauses and only ever raises `next`; both facts are used
everywhere below, so they come first. -/

/-- `encode` extends the clause list rather than rewriting it. Stated as a list prefix
    so the appended part never has to be named -- the `Conj` and `Disj` cases append
    different clauses but compose identically. -/
theorem encode_clauses_prefix {e : expr.Expr} {s s' : State} {l : cnf.Literal}
    (h : encode s e = some (l, s')) : s.clauses <+: s'.clauses := by
  induction e generalizing s s' l with
  | True | False =>
    simp only [encode, constant] at h
    split at h
    · injection h with h; cases h; exact List.prefix_refl _
    · split at h
      · simp at h
      · rename_i v s1 hf
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        rw [fresh_eq_some] at hf
        subst hs'
        simp only [hf.2.2]
        exact List.prefix_append _ _
  | Variable v => injection h with h; cases h; exact List.prefix_refl _
  | Neg e ih =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      injection h with h
      obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hs'
      exact ih h1
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      split at h
      · simp at h
      · rename_i l2 s2 h2
        split at h
        · simp at h
        · rename_i g s3 hf
          injection h with h
          obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
          rw [fresh_eq_some] at hf
          subst hs'
          refine ((ih1 h1).trans (ih2 h2)).trans ?_
          simp only [hf.2.2]
          exact List.prefix_append _ _

/-- `encode` never lowers the fresh-variable counter. -/
theorem encode_next_le {e : expr.Expr} {s s' : State} {l : cnf.Literal}
    (h : encode s e = some (l, s')) : s.next ≤ s'.next := by
  induction e generalizing s s' l with
  | True | False =>
    simp only [encode, constant] at h
    split at h
    · injection h with h; cases h; exact Nat.le_refl _
    · split at h
      · simp at h
      · rename_i v s1 hf
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        rw [fresh_eq_some] at hf
        subst hs'
        simp [hf.2.2]
  | Variable v => injection h with h; cases h; exact Nat.le_refl _
  | Neg e ih =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      injection h with h
      obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hs'
      exact ih h1
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      split at h
      · simp at h
      · rename_i l2 s2 h2
        split at h
        · simp at h
        · rename_i g s3 hf
          injection h with h
          obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
          rw [fresh_eq_some] at hf
          subst hs'
          have := Nat.le_trans (ih1 h1) (ih2 h2)
          simp only [hf.2.2]
          exact Nat.le_trans this (Nat.le_succ _)

/-- Satisfying a longer clause list means satisfying the prefix it grew from. -/
theorem eval_of_encode_clauses {e : expr.Expr} {s s' : State} {l : cnf.Literal}
    {w : Std.U16 → Bool} (h : encode s e = some (l, s'))
    (hw : Cnf.eval w s'.clauses = true) : Cnf.eval w s.clauses = true :=
  eval_of_prefix (encode_clauses_prefix h) hw

/-! ### Well-formedness

`trueVar_clause` is the only part soundness needs: it says the shared constant gate
really was pinned true by a unit clause when it was allocated. The two bound fields are
what make a newly allocated gate genuinely *fresh*, and only completeness needs them. -/

/-- The shared constant gate, if allocated, is pinned true by a unit clause. This is
    the whole invariant soundness needs, and `encode` preserves it with no side
    conditions at all -- which is why `encode_sound` carries no freshness hypothesis. -/
def State.Pinned (s : State) : Prop := ∀ v, s.trueVar = some v → [pos v] ∈ s.clauses

/-- The full invariant, adding the two bounds that make a fresh gate genuinely fresh. -/
structure State.Wf (s : State) : Prop where
  pinned : State.Pinned s
  clauses_lt : ∀ k ∈ cnfVars s.clauses, k.val < s.next
  trueVar_lt : ∀ v, s.trueVar = some v → v.val < s.next

/-- `Pinned` survives any clause-list extension that leaves `trueVar` alone. -/
theorem State.Pinned.of_prefix {s s' : State} (hp : State.Pinned s)
    (hpre : s.clauses <+: s'.clauses) (htv : s'.trueVar = s.trueVar) : State.Pinned s' := by
  intro v hv
  rw [htv] at hv
  exact hpre.subset (hp v hv)

/-- `encode` preserves `Pinned`: it either leaves `trueVar` alone (and only appends
    clauses) or allocates it and appends its unit clause in the same step. -/
theorem encode_pinned {e : expr.Expr} {s s' : State} {l : cnf.Literal}
    (hp : State.Pinned s) (h : encode s e = some (l, s')) : State.Pinned s' := by
  induction e generalizing s s' l with
  | True | False =>
    simp only [encode, constant] at h
    split at h
    · injection h with h
      obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hs'; exact hp
    · split at h
      · simp at h
      · rename_i v s1 hf
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        rw [fresh_eq_some] at hf
        subst hs'
        intro v' hv'
        simp only [Option.some.injEq] at hv'
        subst hv'
        simp
  | Variable v =>
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; exact hp
  | Neg e ih =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      injection h with h
      obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hs'; exact ih hp h1
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      split at h
      · simp at h
      · rename_i l2 s2 h2
        split at h
        · simp at h
        · rename_i g s3 hf
          injection h with h
          obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
          rw [fresh_eq_some] at hf
          subst hs'
          refine (ih2 (ih1 hp h1) h2).of_prefix ?_ ?_
          · simp only [hf.2.2]; exact List.prefix_append _ _
          · simp [hf.2.2]

/-! ### Soundness

No freshness hypothesis anywhere beyond `Pinned`, which `encode` maintains by itself:
the defining clauses are biconditionals, so a valuation satisfying them has no choice
about what the gates mean. -/

/-- **Core soundness**: any valuation satisfying the clauses `encode` has accumulated
    reads the returned literal as the truth value of `e` itself. -/
theorem encode_sound {e : expr.Expr} {s s' : State} {l : cnf.Literal} {w : Std.U16 → Bool}
    (hp : State.Pinned s) (h : encode s e = some (l, s'))
    (hw : Cnf.eval w s'.clauses = true) :
    Literal.eval w l = evalPure w e := by
  induction e generalizing s s' l with
  | True | False =>
    simp only [encode, constant] at h
    split at h
    · /- The constant gate was allocated earlier, so its unit clause is already in
         `s.clauses`, and `s' = s`. -/
      rename_i v hv
      injection h with h
      obtain ⟨hl, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hl; subst hs'
      have : w v = true := by
        simpa using clause_eval_of_mem hw (hp v hv)
      simp [evalPure, this]
    · split at h
      · simp at h
      · /- The gate is allocated here, and its unit clause is the last thing appended. -/
        rename_i v s1 hf
        injection h with h
        obtain ⟨hl, hs'⟩ := Prod.mk.injEq .. ▸ h
        subst hl; subst hs'
        have : w v = true := by
          simpa using clause_eval_of_mem (cl := [pos v]) hw (by simp)
        simp [evalPure, this]
  | Variable v =>
    injection h with h
    obtain ⟨hl, -⟩ := Prod.mk.injEq .. ▸ h
    subst hl; simp [evalPure]
  | Neg e ih =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      injection h with h
      obtain ⟨hl, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hl; subst hs'
      simp only [eval_flip, evalPure, ih hp h1 hw]
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      split at h
      · simp at h
      · rename_i l2 s2 h2
        split at h
        · simp at h
        · rename_i g s3 hf
          injection h with h
          obtain ⟨hl, hs'⟩ := Prod.mk.injEq .. ▸ h
          rw [fresh_eq_some] at hf
          subst hl; subst hs'
          /- Peel the three defining clauses off the end, and recover the sub-results
             from the prefix that is left. -/
          rw [Cnf.eval_append] at hw
          obtain ⟨hpre, hdef⟩ := Bool.and_eq_true _ _ |>.mp hw
          simp only [hf.2.2] at hpre
          have hs1 : Cnf.eval w s1.clauses = true :=
            eval_of_prefix (encode_clauses_prefix h2) hpre
          have e1eq := ih1 hp h1 hs1
          have e2eq := ih2 (encode_pinned hp h1) h2 hpre
          simp only [Cnf.eval, List.all_cons, List.all_nil, Clause.eval, List.any_cons,
            List.any_nil, eval_pos, eval_neg, eval_flip, Bool.or_false] at hdef
          simp only [evalPure, ← e1eq, ← e2eq, eval_pos]
          revert hdef
          cases w g <;> cases Literal.eval w l1 <;> cases Literal.eval w l2 <;> simp


/-! ### Freshness bookkeeping -/

/-- The literal `encode` returns never mentions a variable the encoder has not yet
    reached -- which is what makes the *next* gate fresh for it. -/
theorem encode_lit_lt {e : expr.Expr} {s s' : State} {l : cnf.Literal}
    (hwf : State.Wf s) (hvars : ∀ k ∈ varsOf e, k.val < s.next)
    (h : encode s e = some (l, s')) : l.var.val < s'.next := by
  induction e generalizing s s' l with
  | True | False =>
    simp only [encode, constant] at h
    split at h
    · /- The constant gate was allocated on an earlier call, so its bound is the
         invariant's `trueVar_lt` rather than anything proved here. -/
      rename_i v hv
      injection h with h
      obtain ⟨hl, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hl; subst hs'
      split <;> simpa using hwf.trueVar_lt v hv
    · split at h
      · simp at h
      · rename_i v s1 hf
        injection h with h
        obtain ⟨hl, hs'⟩ := Prod.mk.injEq .. ▸ h
        rw [fresh_eq_some] at hf
        subst hl; subst hs'
        split <;> simp [hf.1, hf.2.2]
  | Variable v =>
    injection h with h
    obtain ⟨hl, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hl; subst hs'
    exact hvars v (by simp [varsOf])
  | Neg e ih =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      injection h with h
      obtain ⟨hl, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hl; subst hs'
      simpa using ih hwf (by simpa [varsOf] using hvars) h1
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      split at h
      · simp at h
      · rename_i l2 s2 h2
        split at h
        · simp at h
        · rename_i g s3 hf
          injection h with h
          obtain ⟨hl, hs'⟩ := Prod.mk.injEq .. ▸ h
          rw [fresh_eq_some] at hf
          subst hl; subst hs'
          simp only [var_pos, hf.2.2, hf.1]
          exact Nat.lt_succ_self _


/-- `encode` preserves the full invariant: the gate it allocates is above everything
    already mentioned, and the clauses it adds mention only the gate and the literals
    standing for the two operands, both of which `encode_lit_lt` already bounds. -/
theorem encode_wf {e : expr.Expr} {s s' : State} {l : cnf.Literal}
    (hwf : State.Wf s) (hvars : ∀ k ∈ varsOf e, k.val < s.next)
    (h : encode s e = some (l, s')) : State.Wf s' := by
  induction e generalizing s s' l with
  | True | False =>
    simp only [encode, constant] at h
    split at h
    · injection h with h
      obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hs'; exact hwf
    · split at h
      · simp at h
      · rename_i v s1 hf
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        rw [fresh_eq_some] at hf
        obtain ⟨hgval, -, rfl⟩ := hf
        subst hs'
        refine ⟨?_, ?_, ?_⟩
        · intro v' hv'
          simp only [Option.some.injEq] at hv'; subst hv'; simp
        · intro k hk
          simp only [cnfVars_append] at hk
          rcases List.mem_append.mp hk with hk | hk
          · exact Nat.lt_succ_of_lt (hwf.clauses_lt k hk)
          · simp only [cnfVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
              clauseVars, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
              or_false, var_pos] at hk
            subst hk; simp [hgval]
        · intro v' hv'
          simp only [Option.some.injEq] at hv'; subst hv'; simp [hgval]
  | Variable v =>
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; exact hwf
  | Neg e ih =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      injection h with h
      obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hs'
      exact ih hwf (by simpa [varsOf] using hvars) h1
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      split at h
      · simp at h
      · rename_i l2 s2 h2
        split at h
        · simp at h
        · rename_i g s3 hf
          injection h with h
          obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
          rw [fresh_eq_some] at hf
          obtain ⟨hgval, -, rfl⟩ := hf
          subst hs'
          have hvars1 : ∀ k ∈ varsOf e1, k.val < s.next :=
            fun k hk => hvars k (by simp [varsOf, hk])
          have hwf1 : State.Wf s1 := ih1 hwf hvars1 h1
          have hvars2 : ∀ k ∈ varsOf e2, k.val < s1.next :=
            fun k hk => Nat.lt_of_lt_of_le (hvars k (by simp [varsOf, hk])) (encode_next_le h1)
          have hwf2 : State.Wf s2 := ih2 hwf1 hvars2 h2
          /- Both operand literals were bounded when they were produced, and `next` has
             only gone up since. -/
          have hl1 : l1.var.val < s2.next :=
            Nat.lt_of_lt_of_le (encode_lit_lt hwf hvars1 h1) (encode_next_le h2)
          have hl2 : l2.var.val < s2.next := encode_lit_lt hwf1 hvars2 h2
          refine ⟨?_, ?_, ?_⟩
          · exact hwf2.pinned.of_prefix (List.prefix_append _ _) rfl
          · /- Every variable in the three new clauses is either the gate itself or one
               of the two operand literals; `Conj` and `Disj` arrange them differently,
               so the three bounds go into the context and `grind` picks the right one. -/
            intro k hk
            show k.val < s2.next + 1
            simp only [cnfVars_append] at hk
            rcases List.mem_append.mp hk with hk | hk
            · exact Nat.lt_succ_of_lt (hwf2.clauses_lt k hk)
            · simp only [cnfVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
                clauseVars, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
                List.not_mem_nil, or_false, var_pos, var_neg, var_flip] at hk
              have hg : g.val < s2.next + 1 := by simp [hgval]
              have h1' : l1.var.val < s2.next + 1 := Nat.lt_succ_of_lt hl1
              have h2' : l2.var.val < s2.next + 1 := Nat.lt_succ_of_lt hl2
              grind
          · intro v' hv'
            exact Nat.lt_succ_of_lt (hwf2.trueVar_lt v' hv')


/-- **Core completeness**: a valuation satisfying what the encoder has emitted so far
    extends to one that also satisfies the clauses `encode e` adds, without disturbing
    any variable the encoder has already reached.

    Freshness is exactly what makes the extension safe: the new gate sits at `next`,
    strictly above everything mentioned so far, so giving it the value its own
    definition forces cannot falsify a clause that is already there. -/
theorem encode_complete {e : expr.Expr} {s s' : State} {l : cnf.Literal}
    (hwf : State.Wf s) (hvars : ∀ k ∈ varsOf e, k.val < s.next)
    (h : encode s e = some (l, s')) (w : Std.U16 → Bool)
    (hw : Cnf.eval w s.clauses = true) :
    ∃ w', (∀ k : Std.U16, k.val < s.next → w' k = w k) ∧
          Cnf.eval w' s'.clauses = true := by
  induction e generalizing s s' l w with
  | True | False =>
    simp only [encode, constant] at h
    split at h
    · injection h with h
      obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hs'
      exact ⟨w, fun _ _ => rfl, hw⟩
    · split at h
      · simp at h
      · rename_i v s1 hf
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        rw [fresh_eq_some] at hf
        obtain ⟨hgval, -, rfl⟩ := hf
        subst hs'
        refine ⟨upd w v true,
          fun k hk => upd_of_ne (ne_of_val_lt hk (le_of_eq hgval.symm)), ?_⟩
        simp only [Cnf.eval_append]
        refine Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩
        · rw [Cnf.eval_upd_of_lt hwf.clauses_lt (le_of_eq hgval.symm)]; exact hw
        · simp [Cnf.eval, Clause.eval]
  | Variable v =>
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'
    exact ⟨w, fun _ _ => rfl, hw⟩
  | Neg e ih =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      injection h with h
      obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hs'
      exact ih hwf (by simpa [varsOf] using hvars) h1 w hw
  | Conj e1 e2 ih1 ih2 =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      split at h
      · simp at h
      · rename_i l2 s2 h2
        split at h
        · simp at h
        · rename_i g s3 hf
          injection h with h
          obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
          rw [fresh_eq_some] at hf
          obtain ⟨hgval, -, rfl⟩ := hf
          subst hs'
          have hvars1 : ∀ k ∈ varsOf e1, k.val < s.next :=
            fun k hk => hvars k (by simp [varsOf, hk])
          have hwf1 : State.Wf s1 := encode_wf hwf hvars1 h1
          have hvars2 : ∀ k ∈ varsOf e2, k.val < s1.next :=
            fun k hk => Nat.lt_of_lt_of_le (hvars k (by simp [varsOf, hk])) (encode_next_le h1)
          have hwf2 : State.Wf s2 := encode_wf hwf1 hvars2 h2
          have hl1 : l1.var.val < s2.next :=
            Nat.lt_of_lt_of_le (encode_lit_lt hwf hvars1 h1) (encode_next_le h2)
          have hl2 : l2.var.val < s2.next := encode_lit_lt hwf1 hvars2 h2
          have hne1 : l1.var ≠ g := ne_of_val_lt hl1 (le_of_eq hgval.symm)
          have hne2 : l2.var ≠ g := ne_of_val_lt hl2 (le_of_eq hgval.symm)
          obtain ⟨w1, hag1, hev1⟩ := ih1 hwf hvars1 h1 w hw
          obtain ⟨w2, hag2, hev2⟩ := ih2 hwf1 hvars2 h2 w1 hev1
          refine ⟨upd w2 g (Literal.eval w2 l1 && Literal.eval w2 l2), ?_, ?_⟩
          · /- The gate sits above everything either recursive call could have touched,
               so the update is invisible below `s.next`, where the two recursive
               agreements chain. -/
            intro k hk
            have hk2 : k.val < s2.next :=
              Nat.lt_of_lt_of_le hk (Nat.le_trans (encode_next_le h1) (encode_next_le h2))
            rw [upd_of_ne (ne_of_val_lt hk2 (le_of_eq hgval.symm)),
                hag2 k (Nat.lt_of_lt_of_le hk (encode_next_le h1)), hag1 k hk]
          · simp only [Cnf.eval_append]
            refine Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩
            · rw [Cnf.eval_upd_of_lt hwf2.clauses_lt (le_of_eq hgval.symm)]; exact hev2
            · simp only [Cnf.eval, List.all_cons, List.all_nil, Bool.and_true, Clause.eval,
                List.any_cons, List.any_nil, Bool.or_false, eval_pos, eval_neg, eval_flip,
                eval_upd_of_ne hne1, eval_upd_of_ne hne2, upd_self]
              cases Literal.eval w2 l1 <;> cases Literal.eval w2 l2 <;> simp
  | Disj e1 e2 ih1 ih2 =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      split at h
      · simp at h
      · rename_i l2 s2 h2
        split at h
        · simp at h
        · rename_i g s3 hf
          injection h with h
          obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
          rw [fresh_eq_some] at hf
          obtain ⟨hgval, -, rfl⟩ := hf
          subst hs'
          have hvars1 : ∀ k ∈ varsOf e1, k.val < s.next :=
            fun k hk => hvars k (by simp [varsOf, hk])
          have hwf1 : State.Wf s1 := encode_wf hwf hvars1 h1
          have hvars2 : ∀ k ∈ varsOf e2, k.val < s1.next :=
            fun k hk => Nat.lt_of_lt_of_le (hvars k (by simp [varsOf, hk])) (encode_next_le h1)
          have hwf2 : State.Wf s2 := encode_wf hwf1 hvars2 h2
          have hl1 : l1.var.val < s2.next :=
            Nat.lt_of_lt_of_le (encode_lit_lt hwf hvars1 h1) (encode_next_le h2)
          have hl2 : l2.var.val < s2.next := encode_lit_lt hwf1 hvars2 h2
          have hne1 : l1.var ≠ g := ne_of_val_lt hl1 (le_of_eq hgval.symm)
          have hne2 : l2.var ≠ g := ne_of_val_lt hl2 (le_of_eq hgval.symm)
          obtain ⟨w1, hag1, hev1⟩ := ih1 hwf hvars1 h1 w hw
          obtain ⟨w2, hag2, hev2⟩ := ih2 hwf1 hvars2 h2 w1 hev1
          refine ⟨upd w2 g (Literal.eval w2 l1 || Literal.eval w2 l2), ?_, ?_⟩
          · /- The gate sits above everything either recursive call could have touched,
               so the update is invisible below `s.next`, where the two recursive
               agreements chain. -/
            intro k hk
            have hk2 : k.val < s2.next :=
              Nat.lt_of_lt_of_le hk (Nat.le_trans (encode_next_le h1) (encode_next_le h2))
            rw [upd_of_ne (ne_of_val_lt hk2 (le_of_eq hgval.symm)),
                hag2 k (Nat.lt_of_lt_of_le hk (encode_next_le h1)), hag1 k hk]
          · simp only [Cnf.eval_append]
            refine Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩
            · rw [Cnf.eval_upd_of_lt hwf2.clauses_lt (le_of_eq hgval.symm)]; exact hev2
            · simp only [Cnf.eval, List.all_cons, List.all_nil, Bool.and_true, Clause.eval,
                List.any_cons, List.any_nil, Bool.or_false, eval_pos, eval_neg, eval_flip,
                eval_upd_of_ne hne1, eval_upd_of_ne hne2, upd_self]
              cases Literal.eval w2 l1 <;> cases Literal.eval w2 l2 <;> simp


/-! ### The transformation as a whole -/

/-- The initial state is well-formed: it has emitted nothing and allocated nothing. -/
theorem initial_wf (e : expr.Expr) : State.Wf (initial e) where
  pinned := by intro v hv; simp [initial] at hv
  clauses_lt := by intro k hk; simp [initial, cnfVars] at hk
  trueVar_lt := by intro v hv; simp [initial] at hv

/-- ...and its counter already sits above every variable of `e`, so the first gate is
    fresh for the formula as well as for the (empty) clause list. -/
theorem varsOf_lt_initial (e : expr.Expr) : ∀ k ∈ varsOf e, k.val < (initial e).next :=
  fun k hk => mem_lt_foldl_bump (varsOf e) 0 k hk

/-- **Soundness**: every model of the Tseitin CNF satisfies `e`.

    No restriction step is needed in the statement: `evalPure` reads only `e`'s own
    variables, so the gate values `w` also carries are simply never consulted. -/
theorem toCnf_sound {e : expr.Expr} {c : List (List cnf.Literal)} {w : Std.U16 → Bool}
    (h : toCnf e = some c) (hw : Cnf.eval w c = true) : evalPure w e = true := by
  simp only [toCnf] at h
  split at h
  · simp at h
  · rename_i root s hs
    injection h with h
    subst h
    rw [Cnf.eval_append] at hw
    obtain ⟨hbody, hroot⟩ := Bool.and_eq_true _ _ |>.mp hw
    have hsound := encode_sound (initial_wf e).pinned hs hbody
    simp only [Cnf.eval, List.all_cons, List.all_nil, Bool.and_true, Clause.eval,
      List.any_cons, List.any_nil, Bool.or_false] at hroot
    rw [← hsound]; exact hroot

/-- **Completeness**: every model of `e` extends to a model of the Tseitin CNF that
    agrees with it on all of `e`'s own variables.

    Together with `toCnf_sound` this is equisatisfiability, which is the most that can
    be asked of an encoding that introduces variables. -/
theorem toCnf_complete {e : expr.Expr} {c : List (List cnf.Literal)} {w : Std.U16 → Bool}
    (h : toCnf e = some c) (hsat : evalPure w e = true) :
    ∃ w', (∀ k ∈ varsOf e, w' k = w k) ∧ Cnf.eval w' c = true := by
  simp only [toCnf] at h
  split at h
  · simp at h
  · rename_i root s hs
    injection h with h
    subst h
    obtain ⟨w', hag, hev⟩ :=
      encode_complete (initial_wf e) (varsOf_lt_initial e) hs w (by simp [initial, Cnf.eval])
    have hagree : ∀ k ∈ varsOf e, w' k = w k :=
      fun k hk => hag k (varsOf_lt_initial e k hk)
    refine ⟨w', hagree, ?_⟩
    rw [Cnf.eval_append]
    refine Bool.and_eq_true _ _ |>.mpr ⟨hev, ?_⟩
    have hsound := encode_sound (initial_wf e).pinned hs hev
    simp only [Cnf.eval, List.all_cons, List.all_nil, Bool.and_true, Clause.eval,
      List.any_cons, List.any_nil, Bool.or_false]
    rw [hsound, evalPure_congr e hagree, hsat]

/-- The encoding is *linear*: at most three clauses per AST node. Used only to bound
    the `Vec::push` overflow side conditions in the extraction layer, never as a
    tightness claim -- the naive transform's corresponding bound is exponential. -/
theorem encode_clauses_length_le {e : expr.Expr} {s s' : State} {l : cnf.Literal}
    (h : encode s e = some (l, s')) :
    s'.clauses.length ≤ s.clauses.length + 3 * exprSize e := by
  induction e generalizing s s' l with
  | True | False =>
    simp only [encode, constant] at h
    split at h
    · injection h with h
      obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hs'; simp [exprSize]
    · split at h
      · simp at h
      · rename_i v s1 hf
        injection h with h
        obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
        rw [fresh_eq_some] at hf
        obtain ⟨-, -, rfl⟩ := hf
        subst hs'; simp [exprSize]
  | Variable v =>
    injection h with h
    obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
    subst hs'; simp [exprSize]
  | Neg e ih =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      injection h with h
      obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
      subst hs'
      exact Nat.le_trans (ih h1) (by simp [exprSize])
  | Conj e1 e2 ih1 ih2 | Disj e1 e2 ih1 ih2 =>
    simp only [encode] at h
    split at h
    · simp at h
    · rename_i l1 s1 h1
      split at h
      · simp at h
      · rename_i l2 s2 h2
        split at h
        · simp at h
        · rename_i g s3 hf
          injection h with h
          obtain ⟨-, hs'⟩ := Prod.mk.injEq .. ▸ h
          rw [fresh_eq_some] at hf
          obtain ⟨-, -, rfl⟩ := hf
          subst hs'
          have b1 := ih1 h1
          have b2 := ih2 h2
          simp only [exprSize, List.length_append]
          grind

end Tseitin

end sat_solver
