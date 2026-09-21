/- Hand-written lemmas characterizing `expr.Map.get`/`expr.Map.insert` purely in
terms of `List expr.Entry` operations, so the rest of the proof never has to touch
the `IterMut`/backward-continuation machinery these functions are extracted through. -/
import SatSolver.Extraction
import SatSolver.Verification.Prelude

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

/-- Reference semantics for `expr.Map.get`: the value of the first entry (scanning
    from the front) whose key matches, or `none` if there isn't one. -/
def Map.lookupList (l : List expr.Entry) (k : Std.U8) : Option Bool :=
  (l.find? (fun e => e.key = k)).map expr.Entry.value

/-- Reference semantics for `expr.Map.insert`: overwrite the value of the first
    matching entry in place, or append a fresh entry at the end if there is none. -/
def Map.upsertList (l : List expr.Entry) (k : Std.U8) (v : Bool) : List expr.Entry :=
  match l with
  | [] => [{ key := k, value := v }]
  | e :: rest =>
    if e.key = k then { e with value := v } :: rest
    else e :: Map.upsertList rest k v

@[simp]
theorem Map.lookupList_nil (k : Std.U8) : Map.lookupList [] k = none := by
  simp [Map.lookupList]

@[simp]
theorem Map.lookupList_cons_eq (e : expr.Entry) (rest : List expr.Entry) (k : Std.U8)
    (h : e.key = k) : Map.lookupList (e :: rest) k = some e.value := by
  simp [Map.lookupList, h]

@[simp]
theorem Map.lookupList_cons_ne (e : expr.Entry) (rest : List expr.Entry) (k : Std.U8)
    (h : e.key ≠ k) : Map.lookupList (e :: rest) k = Map.lookupList rest k := by
  simp [Map.lookupList, h]

@[simp]
theorem Map.upsertList_length (l : List expr.Entry) (k : Std.U8) (v : Bool) :
    (Map.upsertList l k v).length = if Map.lookupList l k = none then l.length + 1 else l.length := by
  induction l with
  | nil => simp [Map.upsertList]
  | cons e rest ih =>
    simp only [Map.upsertList]
    by_cases h : e.key = k
    · simp [h]
    · simp [h, ih]
      split_ifs
      · rfl
      · rfl

@[simp]
theorem Map.lookupList_upsertList_self (l : List expr.Entry) (k : Std.U8) (v : Bool) :
    Map.lookupList (Map.upsertList l k v) k = some v := by
  induction l with
  | nil => simp [Map.upsertList]
  | cons e rest ih =>
    simp only [Map.upsertList]
    by_cases h : e.key = k
    · simp [h]
    · simp [h, ih]

theorem Map.lookupList_upsertList_other (l : List expr.Entry) (k k' : Std.U8) (v : Bool)
    (h : k' ≠ k) : Map.lookupList (Map.upsertList l k v) k' = Map.lookupList l k' := by
  induction l with
  | nil => simp [Map.upsertList, Map.lookupList, Ne.symm h]
  | cons e rest ih =>
    simp only [Map.upsertList]
    by_cases he : e.key = k
    · rw [if_pos he]
      simp [he, Map.lookupList, Ne.symm h]
    · rw [if_neg he]
      by_cases he' : e.key = k'
      · rw [Map.lookupList_cons_eq _ _ _ he', Map.lookupList_cons_eq _ _ _ he']
      · rw [Map.lookupList_cons_ne _ _ _ he', Map.lookupList_cons_ne _ _ _ he', ih]

/-- **Spec theorem for `sat_solver::expr::{sat_solver::expr::Map}::get`'s loop.** -/
@[step]
theorem expr.Map.get_loop.spec (iter : core.slice.iter.Iter expr.Entry) (key : Std.U8) :
    expr.Map.get_loop iter key ⦃ (o : core.option.Option Bool) =>
      o = Map.lookupList iter.val key ⦄ := by
  unfold expr.Map.get_loop
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

/-- **Spec theorem for `sat_solver::expr::{sat_solver::expr::Map}::get`**
`Map.get` returns the value of the first matching entry, or `none`. -/
@[step]
theorem expr.Map.get.spec (self : expr.Map) (key : Std.U8) :
    expr.Map.get self key ⦃ (o : core.option.Option Bool) =>
      o = Map.lookupList self.val key ⦄ := by
  unfold expr.Map.get alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref
    alloc.vec.Vec.as_slice rust_primitives.sequence.seq_to_slice
    core.slice.Slice.iter rust_primitives.sequence.seq_from_slice
  step*

/-- **Spec theorem for `sat_solver::expr::{sat_solver::expr::Map}::insert`'s loop.**
Generalized over an arbitrary `prefix` (the entries already consumed by earlier
recursion levels) and the `back`/`deref_mut_back`/`iter_mut_back` backward
continuations threaded through the `&mut` translation -- `back` is characterized
purely by "reinserting `prefix` unchanged in front of whatever `iter` becomes",
which is all that's ever true of it at any call site (every entry skipped over
on the way here was left untouched, by construction of the `else` branch below). -/
@[step]
theorem expr.Map.insert_loop.spec
    (deref_mut_back : Slice expr.Entry → expr.Map)
    (iter_mut_back : core.slice.iter.IterMut expr.Entry → Slice expr.Entry)
    (iter : core.slice.iter.IterMut expr.Entry)
    (back : core.slice.iter.IterMut expr.Entry → core.slice.iter.IterMut expr.Entry)
    (key : Std.U8) (value : Bool) (pre : List expr.Entry)
    (hdmb : ∀ s', deref_mut_back s' = s')
    (himb : ∀ i', iter_mut_back i' = i')
    (hback : ∀ final : core.slice.iter.IterMut expr.Entry,
      pre.length + final.val.length ≤ Usize.max → (back final).val = pre ++ final.val)
    (hle : (pre ++ iter.val).length ≤ Usize.max)
    (hlen : Map.lookupList iter.val key ≠ none ∨ (pre ++ iter.val).length < Usize.max) :
    expr.Map.insert_loop deref_mut_back iter_mut_back iter back key value ⦃
      (o : core.option.Option Bool) (m : expr.Map) =>
        o = Map.lookupList iter.val key ∧
        m.val = pre ++ Map.upsertList iter.val key value ⦄ := by
  unfold expr.Map.insert_loop
  step*
  · exact pre ++ [entry]
  · -- hlen precondition for the final push, o = None (iter.val = [])
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil =>
      obtain ⟨ho, hiter1, hnb⟩ := o_post
      rcases hlen with hlen | hlen
      · simp_all
      · have hb0 : pre.length + iter1.val.length ≤ Usize.max := by rw [hiter1]; scalar_tac
        have hpre := hback iter1 hb0
        rw [hiter1] at hpre
        simp only [List.append_nil] at hpre
        rw [hnb iter1 none, hdmb, himb, hpre]
        scalar_tac
    | cons e es => simp_all
  · -- final result, o = None (iter.val = [])
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil =>
      obtain ⟨ho, hiter1, hnb⟩ := o_post
      rcases hlen with hlen | hlen
      · simp_all
      · have hb0 : pre.length + iter1.val.length ≤ Usize.max := by rw [hiter1]; scalar_tac
        have hpre := hback iter1 hb0
        rw [hiter1] at hpre
        simp only [List.append_nil] at hpre
        rw [v1_post, hnb iter1 none, hdmb, himb, hpre]
        simp [Map.upsertList]
    | cons e es => simp_all
  · -- entry.key = key: overwrite in place, stop
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      rename_i hoe hkey
      obtain ⟨heq, hiter1, hnb⟩ := o_post
      rw [heq] at hoe
      injection hoe with hee
      simp only [CoreModels.core.mem.replace, Aeneas.Std.core.mem.replace]
      step*
      have hb1 : iter1.val.length < Usize.max := by rw [hiter1]; scalar_tac
      have hnext := hnb iter1 (some { key := key, value := value }) hb1
      simp only at hnext
      have hb2 : pre.length + (next_back iter1 (some { key := key, value := value })).val.length
          ≤ Usize.max := by rw [hnext]; scalar_tac
      have hpre := hback (next_back iter1 (some { key := key, value := value })) hb2
      rw [hnext] at hpre
      rw [hdmb, himb, hpre, hiter1]
      have hek : e.key = key := by rw [hee]; exact hkey
      simp [Map.upsertList, hek, ← hee]
  · -- entry.key ≠ key: hback for the recursive call, prefix ++ [entry]
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      obtain ⟨heq, hiter1, hnb⟩ := o_post
      intro final hb
      have hb1 : final.val.length < Usize.max := by scalar_tac
      have hnext := hnb final (some entry) hb1
      simp only at hnext
      have hb2 : pre.length + (next_back final (some entry)).val.length ≤ Usize.max := by
        rw [hnext]; scalar_tac
      have hpre := hback (next_back final (some entry)) hb2
      rw [hnext] at hpre
      simpa using hpre
  · -- hle for the recursive call
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      obtain ⟨heq, hiter1, hnb⟩ := o_post
      rw [hiter1]
      simp only [List.append_assoc, List.singleton_append]
      simpa using hle
  · -- hlen for the recursive call
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
  · -- final result, entry.key ≠ key (recursive)
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      obtain ⟨heq, hiter1, hnb⟩ := o_post
      simp_all [Map.upsertList]
termination_by iter.val.length
decreasing_by
  obtain ⟨l, hl⟩ := iter
  cases l with
  | nil => simp_all
  | cons e es =>
    obtain ⟨ho, hiter1, hnb⟩ := o_post
    rw [hiter1]
    scalar_tac

/-- `expr::Entry` is a plain pair of `Copy` scalars, so cloning it is the identity. -/
@[step]
theorem expr.Entry.Insts.CoreCloneClone.clone.spec (self : expr.Entry) :
    expr.Entry.Insts.CoreCloneClone.clone self ⦃ (e : expr.Entry) => e = self ⦄ := by
  unfold expr.Entry.Insts.CoreCloneClone.clone
    core.U8.Insts.CoreCloneClone.clone core.Bool.Insts.CoreCloneClone.clone
  step*

/-- Cloning a `Map` is value-preserving, since `Entry`'s own clone is. -/
@[step]
theorem expr.Map.Insts.CoreCloneClone.clone.spec (self : expr.Map) :
    expr.Map.Insts.CoreCloneClone.clone self ⦃ (m : expr.Map) => m.val = self.val ⦄ := by
  unfold expr.Map.Insts.CoreCloneClone.clone
  step*
  exact fun x => expr.Entry.Insts.CoreCloneClone.clone.spec x

/-- **Spec theorem for `sat_solver::expr::{sat_solver::expr::Map}::insert`**
`Map.insert` overwrites the first matching entry in place, or appends a fresh one,
and reports the old value (if any). -/
@[step]
theorem expr.Map.insert.spec (self : expr.Map) (key : Std.U8) (value : Bool)
    (hlen : Map.lookupList self.val key ≠ none ∨ self.val.length < Usize.max) :
    expr.Map.insert self key value ⦃ (o : core.option.Option Bool) (m : expr.Map) =>
      o = Map.lookupList self.val key ∧ m.val = Map.upsertList self.val key value ⦄ := by
  unfold expr.Map.insert
  step*
  · exact []
  · simp
  · scalar_tac
  · simp_all
  · simp_all

end sat_solver
