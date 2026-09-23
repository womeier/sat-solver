/- Hand-written lemmas characterizing `expr.Map.get`/`expr.Map.insert` purely in
terms of `List (Option Bool)` operations, so the rest of the proof never has to
touch the extracted indexing machinery.

`Map` is a slot array indexed by the variable itself (see `src/expr.rs`), so
`lookupList` is plain list indexing and `upsertList` is "grow to cover the index,
then `List.set`". The *names and statements* of the four laws relating them
(`lookupList_nil`, `lookupList_upsertList_self`, `lookupList_upsertList_other`,
and `upsertList_length`) are inherited from the earlier assoc-list
representation, which is what keeps `Semantics.lean`, `SatNaive.lean` and
`SatDpll.lean` insensitive to the switch: only `upsertList_length` changes shape,
since the array grows to `max len (k+1)` rather than by one entry.

Two things the assoc list needed and this representation does not:

* `Map.insert` no longer walks the map with `iter_mut`, so the backward-
  continuation encoding of `&mut` (three nested `back` functions) is gone.
* `insert` carries no `Usize.max` headroom hypothesis at all. The growth loop
  only pushes while `len ≤ i`, and `i` is a widened `u16`, so every push happens
  at a length below 65536 -- the scalar type discharges the side condition on its
  own. That is what lets the `hlen` disjunctions disappear from the callers. -/
import SatSolver.Extraction
import SatSolver.Verification.Prelude

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

/-- Grow `l` with unset slots until it has at least `n` of them. -/
def Map.padTo (l : List (Option Bool)) (n : Nat) : List (Option Bool) :=
  l ++ List.replicate (n - l.length) none

/-- Reference semantics for `expr.Map.get`: the contents of slot `k`. Out of
    range reads as `none`, exactly like an in-range slot that was never
    assigned -- `Map.get`'s explicit bounds check returns `None` there. -/
def Map.lookupList (l : List (Option Bool)) (k : Std.U16) : Option Bool :=
  l.getD k.val none

/-- Reference semantics for `expr.Map.insert`: grow to cover slot `k`, then set it. -/
def Map.upsertList (l : List (Option Bool)) (k : Std.U16) (v : Bool) : List (Option Bool) :=
  (Map.padTo l (k.val + 1)).set k.val (some v)

@[simp]
theorem Map.padTo_length (l : List (Option Bool)) (n : Nat) :
    (Map.padTo l n).length = max l.length n := by
  simp only [Map.padTo, List.length_append, List.length_replicate]
  omega

@[simp]
theorem Map.lookupList_nil (k : Std.U16) : Map.lookupList [] k = none := by
  simp [Map.lookupList]

/-- Padding with unset slots is invisible to `lookupList`: indices below the
    original length are untouched, and everything at or above it reads `none`
    either way (a fresh `none` slot, or off the end). -/
@[simp]
theorem Map.lookupList_padTo (l : List (Option Bool)) (n : Nat) (k : Std.U16) :
    Map.lookupList (Map.padTo l n) k = Map.lookupList l k := by
  simp only [Map.lookupList, Map.padTo, List.getD_eq_getElem?_getD]
  by_cases h : k.val < l.length
  · rw [List.getElem?_append_left h]
  · replace h : l.length ≤ k.val := Nat.le_of_not_lt h
    have hr : l[k.val]? = none := List.getElem?_eq_none h
    rw [List.getElem?_append_right h, hr]
    rcases lt_or_ge (k.val - l.length) (n - l.length) with hj | hj
    · simp [hj]
    · rw [List.getElem?_eq_none (by simpa using hj)]

@[simp]
theorem Map.upsertList_length (l : List (Option Bool)) (k : Std.U16) (v : Bool) :
    (Map.upsertList l k v).length = max l.length (k.val + 1) := by
  simp [Map.upsertList]

@[simp]
theorem Map.lookupList_upsertList_self (l : List (Option Bool)) (k : Std.U16) (v : Bool) :
    Map.lookupList (Map.upsertList l k v) k = some v := by
  simp [Map.lookupList, Map.upsertList, List.getD_eq_getElem?_getD]

theorem Map.lookupList_upsertList_other (l : List (Option Bool)) (k k' : Std.U16) (v : Bool)
    (h : k' ≠ k) : Map.lookupList (Map.upsertList l k v) k' = Map.lookupList l k' := by
  have hne : k'.val ≠ k.val := by
    intro he; exact h (by scalar_tac)
  conv_rhs => rw [← Map.lookupList_padTo l (k.val + 1) k']
  simp only [Map.lookupList, Map.upsertList, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne hne.symm]

/-- **Spec theorem for `sat_solver::expr::{sat_solver::expr::Map}::get`**
Reads slot `key`, or `none` when `key` is past the end of the array. -/
@[step]
theorem expr.Map.get.spec (self : expr.Map) (key : Std.U16) :
    expr.Map.get self key ⦃ (o : core.option.Option Bool) =>
      o = Map.lookupList self.val key ⦄ := by
  unfold expr.Map.get
  step*
  · -- in range: the element read is exactly the slot's contents
    have hik : i.val = key.val := by scalar_tac
    simp [Map.lookupList, List.getD_eq_getElem?_getD, ← hik, o_post]
  · -- out of range: `getD` falls through to the default
    have hik : i.val = key.val := by scalar_tac
    rw [Map.lookupList, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (show self.val.length ≤ key.val by scalar_tac)]
    rfl

/-- Pushing one unset slot onto an array still short of `n` leaves `padTo` at `n`
    unchanged -- one slot less to pad, one slot already there. This is the whole
    content of the growth loop's inductive step. -/
theorem Map.padTo_append_none (l : List (Option Bool)) (n : Nat) (h : l.length < n) :
    Map.padTo (l ++ [none]) n = Map.padTo l n := by
  simp only [Map.padTo, List.length_append, List.length_cons, List.length_nil,
    List.append_assoc]
  congr 1
  rw [show n - l.length = (n - (l.length + 1)) + 1 by omega, List.replicate_succ]
  rfl

/-- **Spec theorem for `sat_solver::expr::{sat_solver::expr::Map}::insert`'s growth loop.**
Pushes unset slots until the array covers index `i`, i.e. exactly `padTo`.

No headroom hypothesis beyond `i` itself: a push only happens while `len ≤ i`, so
every push sees a length of at most `i < Usize.max`, and `step*` discharges
`Vec.push`'s side condition on its own. -/
@[step]
theorem expr.Map.insert_loop.spec (self : expr.Map) (i : Std.Usize)
    (hi : i.val < Usize.max) :
    expr.Map.insert_loop self i ⦃ (v : alloc.vec.Vec (core.option.Option Bool)) =>
      v.val = Map.padTo self.val (i.val + 1) ⦄ := by
  unfold expr.Map.insert_loop
  step*
  · -- still short of `i`: recurse on the array with one more slot
    have hpad : Map.padTo (self.val ++ [none]) (i.val + 1)
        = Map.padTo self.val (i.val + 1) :=
      Map.padTo_append_none _ _ (by scalar_tac)
    simp_all
  · -- already long enough: `padTo` is a no-op
    have hzero : i.val + 1 - self.val.length = 0 := by scalar_tac
    simp [Map.padTo, hzero]
termination_by (i.val + 1) - self.val.length
decreasing_by
  simp_all
  scalar_tac

/-- **Spec theorem for `sat_solver::expr::{sat_solver::expr::Map}::insert`**
Sets slot `key` to `value` (growing first if needed) and reports what the slot
held before. -/
@[step]
theorem expr.Map.insert.spec (self : expr.Map) (key : Std.U16) (value : Bool) :
    expr.Map.insert self key value ⦃ (o : core.option.Option Bool) (m : expr.Map) =>
      o = Map.lookupList self.val key ∧ m.val = Map.upsertList self.val key value ⦄ := by
  unfold expr.Map.insert
  step*
  -- both reads are in range: the growth loop just made the array cover `i`
  case hi => rw [v_post, Map.padTo_length]; omega
  case hi => rw [v_post, Map.padTo_length]; omega
  · have hik : i.val = key.val := by scalar_tac
    refine ⟨?_, ?_⟩
    · -- the old value: reading the *padded* array at `key` reads the original,
      -- since padding only ever adds unset slots
      have hv : Map.lookupList v.val key = old := by
        simp only [Map.lookupList, List.getD_eq_getElem?_getD, ← hik, old_post,
          Option.getD_some]
      rw [← hv, v_post, Map.lookupList_padTo]
    · rw [__post2, v_post, hik]
      rfl

end sat_solver
