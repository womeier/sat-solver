/- Machinery shared by the two *encoding* transformations, `Tseitin.lean` and
`Hybrid.lean`.

Both introduce fresh variables, so both need the same three things, none of which the
equivalence-preserving transformation in `Cnf.lean` ever had to care about:

  * a way to mint a gate variable, failing at the `u16` ceiling (`freshVar`);
  * the fact that `Cnf.eval` depends only on the variables its clauses mention
    (`Cnf.eval_congr`), which is what makes giving a *fresh* variable a value
    harmless (`Cnf.eval_upd_of_lt`);
  * the running maximum `Encoder::new`/`Renamer::new` use to place the first gate
    above every variable of the input (`bump`). -/
import SatSolver.Extraction
import SatSolver.Verification.Prelude
import SatSolver.Verification.MapLemmas
import SatSolver.Verification.Semantics
import SatSolver.Verification.Cnf

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

/-! ### Literals -/

/-- Literal helpers, mirroring the Rust `pos`/`neg`/`flip`. -/
def pos (v : Std.U16) : cnf.Literal := ⟨v, false⟩
def neg (v : Std.U16) : cnf.Literal := ⟨v, true⟩
def flip (l : cnf.Literal) : cnf.Literal := ⟨l.var, !l.negated⟩

@[simp] theorem eval_pos (w : Std.U16 → Bool) (v) : Literal.eval w (pos v) = w v := by
  simp [Literal.eval, pos]
@[simp] theorem eval_neg (w : Std.U16 → Bool) (v) : Literal.eval w (neg v) = !w v := by
  simp [Literal.eval, neg]
@[simp] theorem eval_flip (w : Std.U16 → Bool) (l) :
    Literal.eval w (flip l) = !Literal.eval w l := by
  simp only [Literal.eval, flip]; cases l.negated <;> simp
@[simp] theorem var_pos (v) : (pos v).var = v := rfl
@[simp] theorem var_neg (v) : (neg v).var = v := rfl
@[simp] theorem var_flip (l) : (flip l).var = l.var := rfl

/-! ### Minting a gate variable -/

/-- The next gate index as a `u16`, or `none` at the ceiling. This is the whole content
    of `Encoder::fresh`/`Renamer::fresh`: both hold their counter as a `u32` so that
    running out of variable space is a comparison rather than an overflow. -/
def freshVar (n : Nat) : Option Std.U16 := UScalar.tryMkOpt .U16 n

@[simp]
theorem freshVar_eq_some {n : Nat} {v : Std.U16} :
    freshVar n = some v ↔ v.val = n ∧ n < 2 ^ 16 := by
  simp only [freshVar]
  cases h : UScalar.tryMkOpt .U16 n with
  | none =>
    simp only [reduceCtorEq, false_iff, not_and]
    intro hval
    simp only [UScalar.tryMkOpt] at h
    split at h
    · simp at h
    · rename_i hnb
      intro hlt
      exact absurd hlt (by simpa [UScalar.check_bounds] using hnb)
  | some u =>
    have huval : u.val = n := by
      simp only [UScalar.tryMkOpt] at h
      split at h
      · injection h with h; subst h
        exact UScalar.ofNatCore_val_eq _
      · simp at h
    have hlt : n < 2 ^ 16 := by rw [← huval]; exact u.hBounds
    constructor
    · intro heq; injection heq with heq; subst heq; exact ⟨huval, hlt⟩
    · rintro ⟨hv, -⟩
      have : u = v := by apply UScalar.eq_of_val_eq; rw [huval, hv]
      simp [this]

/-! ### Reading clause lists -/

theorem clause_eval_of_mem {w : Std.U16 → Bool} {c : List (List cnf.Literal)}
    {cl : List cnf.Literal} (h : Cnf.eval w c = true) (hmem : cl ∈ c) :
    Clause.eval w cl = true := by
  simp only [Cnf.eval, List.all_eq_true] at h
  exact h cl hmem

/-- A unit clause on `pos v` says exactly `w v = true`. -/
@[simp]
theorem clause_eval_unit_pos (w : Std.U16 → Bool) (v : Std.U16) :
    Clause.eval w [pos v] = w v := by simp [Clause.eval]

/-- Satisfying a longer clause list means satisfying the prefix it grew from. -/
theorem eval_of_append {w : Std.U16 → Bool} {c new : List (List cnf.Literal)}
    (h : Cnf.eval w (c ++ new) = true) : Cnf.eval w c = true := by
  rw [Cnf.eval_append] at h; exact (Bool.and_eq_true _ _ |>.mp h).1

theorem eval_of_prefix {w : Std.U16 → Bool} {c c' : List (List cnf.Literal)}
    (hpre : c <+: c') (h : Cnf.eval w c' = true) : Cnf.eval w c = true := by
  obtain ⟨new, rfl⟩ := hpre; exact eval_of_append h

/-! ### Valuation congruence

`Cnf.eval` only looks at the variables the clauses actually mention. This is what lets
a fresh gate be given a value without disturbing anything already emitted. -/

@[simp]
theorem cnfVars_cons (cl : List cnf.Literal) (c : List (List cnf.Literal)) :
    cnfVars (cl :: c) = clauseVars cl ++ cnfVars c := by simp [cnfVars]

theorem Clause.eval_congr {w1 w2 : Std.U16 → Bool} (cl : List cnf.Literal)
    (hagree : ∀ k ∈ clauseVars cl, w1 k = w2 k) :
    Clause.eval w1 cl = Clause.eval w2 cl := by
  induction cl with
  | nil => simp [Clause.eval]
  | cons l rest ih =>
    have hl : w1 l.var = w2 l.var := hagree l.var (by simp [clauseVars])
    have hrest : ∀ k ∈ clauseVars rest, w1 k = w2 k := by
      intro k hk; exact hagree k (by simp [clauseVars] at hk ⊢; tauto)
    have hr := ih hrest
    simp only [Clause.eval, List.any_cons] at hr ⊢
    rw [hr]
    simp only [Literal.eval, hl]

theorem Cnf.eval_congr {w1 w2 : Std.U16 → Bool} (c : List (List cnf.Literal))
    (hagree : ∀ k ∈ cnfVars c, w1 k = w2 k) : Cnf.eval w1 c = Cnf.eval w2 c := by
  induction c with
  | nil => simp [Cnf.eval]
  | cons cl rest ih =>
    have h1 : ∀ k ∈ clauseVars cl, w1 k = w2 k := by
      intro k hk; exact hagree k (by simp [hk])
    have h2 : ∀ k ∈ cnfVars rest, w1 k = w2 k := by
      intro k hk; exact hagree k (by simp [hk])
    have hr := ih h2
    simp only [Cnf.eval, List.all_cons] at hr ⊢
    rw [hr, Clause.eval_congr cl h1]

/-! ### Extending a valuation to a fresh variable -/

/-- Point update, used to give a freshly allocated gate its value. -/
def upd (w : Std.U16 → Bool) (v : Std.U16) (b : Bool) : Std.U16 → Bool :=
  fun k => if k = v then b else w k

@[simp] theorem upd_self (w : Std.U16 → Bool) (v : Std.U16) (b : Bool) : upd w v b v = b := by
  simp [upd]

theorem upd_of_ne {w : Std.U16 → Bool} {v k : Std.U16} {b : Bool} (h : k ≠ v) :
    upd w v b k = w k := by simp [upd, h]

theorem eval_upd_of_ne {w : Std.U16 → Bool} {v : Std.U16} {b : Bool} {l : cnf.Literal}
    (h : l.var ≠ v) : Literal.eval (upd w v b) l = Literal.eval w l := by
  simp only [Literal.eval, upd_of_ne h]

/-- A variable below a bound cannot be one allocated at or above it. -/
theorem ne_of_val_lt {k v : Std.U16} {n : Nat} (hk : k.val < n) (hv : n ≤ v.val) : k ≠ v := by
  intro he; subst he; exact absurd hk (Nat.not_lt.mpr hv)

/-- Updating at a variable strictly above everything a CNF mentions changes nothing. -/
theorem Cnf.eval_upd_of_lt {w : Std.U16 → Bool} {c : List (List cnf.Literal)}
    {v : Std.U16} {b : Bool} {n : Nat} (hc : ∀ k ∈ cnfVars c, k.val < n) (hv : n ≤ v.val) :
    Cnf.eval (upd w v b) c = Cnf.eval w c := by
  refine Cnf.eval_congr c fun k hk => upd_of_ne ?_
  intro hkv; subst hkv
  exact absurd (hc k hk) (Nat.not_lt.mpr hv)

/-! ### Placing the first gate above the input

`Encoder::new` and `Renamer::new` both fold this over `collect_vars`. -/

/-- Raise the counter past `v` if it is not already. -/
def bump (acc : Nat) (v : Std.U16) : Nat := if v.val ≥ acc then v.val + 1 else acc

theorem le_foldl_bump (l : List Std.U16) (acc : Nat) : acc ≤ l.foldl bump acc := by
  induction l generalizing acc with
  | nil => simp
  | cons v tl ih =>
    simp only [List.foldl_cons]
    refine Nat.le_trans ?_ (ih (bump acc v))
    simp only [bump]
    split
    · rename_i hge; exact Nat.le_trans hge (Nat.le_succ _)
    · exact Nat.le_refl _

theorem mem_lt_foldl_bump (l : List Std.U16) (acc : Nat) :
    ∀ k ∈ l, k.val < l.foldl bump acc := by
  induction l generalizing acc with
  | nil => simp
  | cons v tl ih =>
    intro k hk
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hk with rfl | hk
    · refine Nat.lt_of_lt_of_le ?_ (le_foldl_bump tl (bump acc k))
      simp only [bump]
      split
      · exact Nat.lt_succ_self _
      · rename_i hlt; exact Nat.not_le.mp hlt
    · exact ih (bump acc v) k hk

end sat_solver
