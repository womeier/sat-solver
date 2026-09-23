/- `CoreModels` (hax's std-library shim, as opposed to `Aeneas.Std`) has almost no
`@[step]` lemmas registered for its own container/iterator primitives. These are
generic, reusable specs for the primitives our solvers' loops actually use, so the
rest of the proof can drive them with `step`/`step*` instead of unfolding by hand
every time. -/
import SatSolver.Extraction

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

/-- `CoreModels`'s shared slice iterator pops from the front of the underlying list. -/
@[step]
theorem core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next.spec
    {T : Type} (self : core.slice.iter.Iter T) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next self ⦃
      (o : core.option.Option T) (rest : core.slice.iter.Iter T) =>
        match self.val with
        | [] => o = none ∧ rest.val = []
        | e :: es => o = some e ∧ rest.val = es ⦄ := by
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
    rust_primitives.sequence.seq_len rust_primitives.sequence.seq_remove
  obtain ⟨l, hl⟩ := self
  cases l with
  | nil =>
    have h0 : Slice.len (⟨[], hl⟩ : Slice T) = 0#usize := by scalar_tac
    simp [h0]
  | cons e es => simp [Slice.len]

/-- `CoreModels`'s `Vec.deref` is the identity (`Vec T` and `Slice T` are the
    same underlying representation). -/
@[step]
theorem alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref.spec
    {T : Type} (self : alloc.vec.Vec T) :
    alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref self ⦃ (s : Slice T) =>
      s.val = self.val ⦄ := by
  unfold alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref alloc.vec.Vec.as_slice
    rust_primitives.sequence.seq_to_slice
  step*

/-- `CoreModels`'s `Slice.iter` is the identity. -/
@[step]
theorem core.slice.Slice.iter.spec {T : Type} (s : Slice T) :
    core.slice.Slice.iter s ⦃ (iter : core.slice.iter.Iter T) => iter.val = s.val ⦄ := by
  unfold core.slice.Slice.iter rust_primitives.sequence.seq_from_slice
  step*

@[step]
theorem alloc.vec.Vec.new.spec (T : Type) :
    alloc.vec.Vec.new T ⦃ (v : alloc.vec.Vec T) => v.val = [] ⦄ := by
  unfold alloc.vec.Vec.new rust_primitives.sequence.seq_empty
  step*
  simp [Slice.new]

@[step]
theorem alloc.vec.Vec.push.spec {T : Type} (self : alloc.vec.Vec T) (x : T)
    (hlen : self.val.length < Usize.max) :
    alloc.vec.Vec.push self x ⦃ (v : alloc.vec.Vec T) => v.val = self.val ++ [x] ⦄ := by
  unfold alloc.vec.Vec.push rust_primitives.sequence.seq_push
  simp [hlen]

/-- `CoreModels`'s `Vec.deref_mut` is the identity, with an identity backward
    function (`Vec T` and `Slice T` are the same underlying representation). -/
@[step]
theorem alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut.spec
    {T : Type} (self : alloc.vec.Vec T) :
    alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut self ⦃
      (s : Slice T) (back : Slice T → alloc.vec.Vec T) =>
        s.val = self.val ∧ ∀ s', back s' = s' ⦄ := by
  unfold alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut
    alloc.vec.Vec.as_mut_slice rust_primitives.sequence.seq_to_slice_mut
  step*

/-- `CoreModels`'s `Slice.iter_mut` is the identity, with an identity backward
    function. -/
@[step]
theorem core.slice.Slice.iter_mut.spec {T : Type} (s : Slice T) :
    core.slice.Slice.iter_mut s ⦃
      (iter : core.slice.iter.IterMut T) (back : core.slice.iter.IterMut T → Slice T) =>
        iter.val = s.val ∧ ∀ i', back i' = i' ⦄ := by
  unfold core.slice.Slice.iter_mut rust_primitives.sequence.seq_from_slice_mut
  step*

/-- `CoreModels`'s mutable slice iterator pops from the front of the underlying
    list, with a backward function that reinserts the (possibly updated) element
    at the front -- unless doing so would overflow `Usize.max`, in which case it's
    a no-op (mirroring `seq_remove_mut`'s own guard). -/
@[step]
theorem core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.next.spec
    {T : Type} (self : core.slice.iter.IterMut T) :
    core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.next self ⦃
      (o : core.option.Option T) (rest : core.slice.iter.IterMut T)
      (back : core.slice.iter.IterMut T → core.option.Option T →
        core.slice.iter.IterMut T) =>
        match self.val with
        | [] => o = none ∧ rest.val = [] ∧ ∀ s' x', back s' x' = s'
        | e :: es => o = some e ∧ rest.val = es ∧
            ∀ s' x', s'.val.length < Usize.max →
              (back s' x').val = (match x' with | some t => t | none => e) :: s'.val ⦄ := by
  unfold core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.next
    rust_primitives.sequence.seq_len rust_primitives.sequence.seq_remove_mut
  obtain ⟨l, hl⟩ := self
  cases l with
  | nil =>
    have h0 : Slice.len (⟨[], hl⟩ : Slice T) = 0#usize := by scalar_tac
    simp [h0]
  | cons e es =>
    have hlen0 : Slice.len (⟨e :: es, hl⟩ : Slice T) ≠ 0#usize := by scalar_tac
    simp [hlen0]
    intro s' x' hbound
    simp only [hbound]
    cases x' with
    | none => rfl
    | some t => rfl

@[step]
theorem core.slice.Slice.is_empty.spec {T : Type} (s : Slice T) :
    core.slice.Slice.is_empty s ⦃ (b : Bool) => b = true ↔ s.val = [] ⦄ := by
  unfold core.slice.Slice.is_empty core.slice.Slice.len
    rust_primitives.slice.slice_length
  step*
  grind [Slice.len_val, List.length_eq_zero_iff]

/-- The `RangeFrom { start := 1 }` slicing used by both naive solvers'
    `vars[1..]` -- returns the tail of the list. -/
@[step]
theorem core.Slice.Insts.CoreOpsIndexIndex.index.range_from_one.spec
    {T : Type} [Inhabited T] (s : Slice T) (hne : s.val ≠ []) :
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T)
      s ({ start := 1#usize } : core.ops.range.RangeFrom Std.Usize) ⦃
      (vs : Slice T) => vs.val = s.val.tail ⦄ := by
  unfold core.Slice.Insts.CoreOpsIndexIndex.index
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get
    rust_primitives.slice.slice_length rust_primitives.slice.slice_slice
  have h1 : (1#usize : Usize) ≤ s.len := by
    obtain ⟨l, hl⟩ := s
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  dsimp only
  step*
  rw [if_pos h1]
  step*
  have hslice : ∀ (l : List T), List.slice 1 l.length l = l.tail := by
    intro l
    cases l with
    | nil => simp [List.slice]
    | cons x xs => simp [List.slice_cons_nzero, List.slice_zero_j]
  rw [r_post1]
  simp only [Slice.slice, Slice.len_val]
  exact hslice s.val

/-- `CoreModels`'s `Vec.clone` builds a fresh vector by cloning every element in
order, so it's value-preserving whenever the element-level clone instance is
(true for every `Clone` instance actually used by this project, all of which
bottom out at `Copy` scalars). -/
@[step]
theorem alloc.vec.Vec.Insts.CoreCloneClone.clone_loop.spec {T : Type}
    (cloneInst : core.clone.Clone T) (hclone : ∀ x : T, cloneInst.clone x ⦃ (y : T) => y = x ⦄)
    (iter : core.slice.iter.Iter T) (acc : alloc.vec.Vec T)
    (hbound : acc.val.length + iter.val.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.CoreCloneClone.clone_loop cloneInst iter acc ⦃
      (r : alloc.vec.Vec T) => r.val = acc.val ++ iter.val ⦄ := by
  unfold alloc.vec.Vec.Insts.CoreCloneClone.clone_loop
  apply Aeneas.Std.loop.spec_decr_nat (fun p => p.1.val.length)
    (fun p => p.2.val ++ p.1.val = acc.val ++ iter.val)
  · rintro ⟨i, a⟩ hinv
    unfold alloc.vec.Vec.Insts.CoreCloneClone.clone_loop.body
    step*
    · obtain ⟨l, hl⟩ := i
      cases l with
      | nil => simp_all
      | cons e es => simp_all
    · obtain ⟨l, hl⟩ := i
      cases l with
      | nil => simp_all
      | cons e es =>
        obtain ⟨ho, hiter1⟩ := o_post
        have hit : it = e := by simp_all
        have hlen_eq : a.val.length + (e :: es).length = acc.val.length + iter.val.length := by
          have h := congrArg List.length hinv
          simpa using h
        have hlt : a.val.length < Usize.max := by scalar_tac
        unfold rust_primitives.sequence.seq_push
        simp_all
  · simp

@[step]
theorem alloc.vec.Vec.Insts.CoreCloneClone.clone.spec {T : Type}
    (cloneInst : core.clone.Clone T) (hclone : ∀ x : T, cloneInst.clone x ⦃ (y : T) => y = x ⦄)
    (self : alloc.vec.Vec T) :
    alloc.vec.Vec.Insts.CoreCloneClone.clone cloneInst self ⦃
      (v : alloc.vec.Vec T) => v.val = self.val ⦄ := by
  unfold alloc.vec.Vec.Insts.CoreCloneClone.clone rust_primitives.sequence.seq_empty
  step*
  · simp only [Slice.new]
    scalar_tac
  · simp_all [Slice.new]

/-- `CoreModels`'s `Vec::into_iter` iterator pops from the front of the underlying
    list, same as the shared/mutable slice iterators. -/
@[step]
theorem alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next.spec
    {T : Type} (self : alloc.vec.into_iter.IntoIter T) :
    alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next self ⦃
      (o : core.option.Option T) (rest : alloc.vec.into_iter.IntoIter T) =>
        match self.val with
        | [] => o = none ∧ rest.val = []
        | e :: es => o = some e ∧ rest.val = es ⦄ := by
  unfold alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    rust_primitives.sequence.seq_len rust_primitives.sequence.seq_remove
  obtain ⟨l, hl⟩ := self
  cases l with
  | nil =>
    have h0 : Slice.len (⟨[], hl⟩ : Slice T) = 0#usize := by scalar_tac
    simp [h0]
  | cons e es => simp [Slice.len]

/-- `Vec`'s own `is_empty`/`len`/indexing (as opposed to the slice ones, for which
`Aeneas.Std` does register specs) -- all three are thin wrappers over the
underlying `Seq`, and all three are used by `sat_dpll`. -/
@[step]
theorem alloc.vec.Vec.is_empty.spec {T : Type} (self : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty self ⦃ (b : Bool) => b = true ↔ self.val = [] ⦄ := by
  unfold alloc.vec.Vec.is_empty rust_primitives.sequence.seq_len
  step*
  grind [Slice.len_val, List.length_eq_zero_iff]

@[step]
theorem alloc.vec.Vec.len.spec {T : Type} (self : alloc.vec.Vec T) :
    alloc.vec.Vec.len self ⦃ (i : Std.Usize) => i.val = self.val.length ⦄ := by
  unfold alloc.vec.Vec.len rust_primitives.sequence.seq_len
  step*

/-- Indexing a `Vec` at a `Usize`. Stated via `getElem?` rather than `getElem!` so
it needs no `Inhabited` instance (the extracted element types don't have one) and
no dependent bound proof inside the postcondition. -/
@[step]
theorem alloc.vec.Vec.Insts.CoreOpsIndexIndex.index.usize.spec
    {T : Type} (self : alloc.vec.Vec T) (i : Std.Usize) (hi : i.val < self.val.length) :
    alloc.vec.Vec.Insts.CoreOpsIndexIndex.index
      (core.Usize.Insts.CoreSliceIndexSliceIndexSliceT T) self i ⦃ (x : T) =>
      self.val[i.val]? = some x ⦄ := by
  unfold alloc.vec.Vec.Insts.CoreOpsIndexIndex.index
    core.Slice.Insts.CoreOpsIndexIndex.index
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get
    rust_primitives.slice.slice_length rust_primitives.slice.slice_index
  step*
  have hlen : s.val.length = self.val.length := by rw [s_post]
  have hlt : i < s.len := by scalar_tac
  rw [if_pos hlt]
  step*
  simp_all

/-- Mutable indexing of a `Vec` at a `Usize`: the element, plus a backward
function that writes a replacement into that one slot and leaves the rest alone.
`Vec`'s `index_mut` bottoms out at `Slice.index_mut_usize`, whose `Aeneas.Std`
spec is already `@[step]`-registered; the two layers above it (`seq_to_slice_mut`
and the `SliceIndex usize` instance) are both identities. -/
@[step]
theorem alloc.vec.Vec.Insts.CoreOpsIndexIndexMut.index_mut.usize.spec
    {T : Type} (self : alloc.vec.Vec T) (i : Std.Usize) (hi : i.val < self.val.length) :
    alloc.vec.Vec.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Usize.Insts.CoreSliceIndexSliceIndexSliceT T) self i ⦃
      (x : T) (back : T → alloc.vec.Vec T) =>
      self.val[i.val]? = some x ∧ ∀ y, (back y).val = self.val.set i.val y ⦄ := by
  unfold alloc.vec.Vec.Insts.CoreOpsIndexIndexMut.index_mut
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get_unchecked_mut
    rust_primitives.slice.slice_index_mut
    rust_primitives.sequence.seq_to_slice_mut
  step*
  refine ⟨?_, ?_⟩
  · rw [t_post2]
    exact List.getElem?_eq_getElem (by scalar_tac)
  · intro y
    rw [t_post3]
    simp [Slice.set, Slice.setAtNat]

end sat_solver
