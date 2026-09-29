/- The extraction-matching layer for `cnf_transform_hybrid`.

Same job as `TseitinExtraction.lean`, and the same shape: an abstraction from the
extracted `Renamer` to the model state, then an `@[step]` spec per extracted function
saying the two agree. Two differences from Tseitin:

  * `disjoin` computes `n * m` in `usize` *before* deciding whether to distribute, so
    the specs carry a quadratic size precondition (`Hybrid.cnfRec_length_le` and
    `cnfRec_defs_length_le` are what discharge it). Tseitin has no such product.
  * `rename` contains a loop, so it needs a `rename_loop` spec of its own -- the
    Tseitin encoder is loop-free apart from `Encoder::new`. -/
import SatSolver.Extraction
import SatSolver.Verification.Prelude
import SatSolver.Verification.MapLemmas
import SatSolver.Verification.Semantics
import SatSolver.Verification.Cnf
import SatSolver.Verification.Encoding
import SatSolver.Verification.Hybrid

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

namespace Hybrid

/-- A `Vec` of `Vec`s of literals, read as the plain clause list the model uses. -/
def absClauses (v : alloc.vec.Vec cnf.Clause) : List (List cnf.Literal) :=
  v.val.map (fun cl => cl.val)

@[simp]
theorem absClauses_def (v : alloc.vec.Vec cnf.Clause) :
    absClauses v = v.val.map (fun cl => cl.val) := rfl

@[simp]
theorem absClauses_length (v : alloc.vec.Vec cnf.Clause) :
    (absClauses v).length = v.val.length := by simp [absClauses]

/-- The model state an extracted `Renamer` stands for. -/
def absRenamer (ren : cnf_transform_hybrid.Renamer) : State :=
  { next := ren.next.val, defs := absClauses ren.defs }

/-- The model's clause-list view and `Cnf.lean`'s are the same function. -/
theorem absClauses_eq_contents (v : cnf.Cnf) : absClauses v = Cnf.contents v := rfl

theorem mem_absClauses {v : alloc.vec.Vec cnf.Clause} {cl : cnf.Clause}
    (h : cl ∈ v.val) : cl.val ∈ absClauses v := by
  simp only [absClauses_def, List.mem_map]; exact ⟨cl, h, rfl⟩

@[simp]
theorem absRenamer_next (ren : cnf_transform_hybrid.Renamer) :
    (absRenamer ren).next = ren.next.val := rfl

@[simp]
theorem absRenamer_defs (ren : cnf_transform_hybrid.Renamer) :
    (absRenamer ren).defs = absClauses ren.defs := rfl

end Hybrid

open Hybrid

/-! ### Literal helpers -/

@[step]
theorem cnf_transform_hybrid.pos.spec (var : Std.U16) :
    cnf_transform_hybrid.pos var ⦃ (l : cnf.Literal) => l = _root_.sat_solver.pos var ⦄ := by
  unfold cnf_transform_hybrid.pos
  step*
  simp [_root_.sat_solver.pos]

@[step]
theorem cnf_transform_hybrid.neg.spec (var : Std.U16) :
    cnf_transform_hybrid.neg var ⦃ (l : cnf.Literal) => l = _root_.sat_solver.neg var ⦄ := by
  unfold cnf_transform_hybrid.neg
  step*
  simp [_root_.sat_solver.neg]

/-! ### Allocating a gate

Character for character the same function as `Encoder::fresh`, and the same proof. -/

@[step]
theorem cnf_transform_hybrid.Renamer.fresh.spec (self : cnf_transform_hybrid.Renamer) :
    cnf_transform_hybrid.Renamer.fresh self
    ⦃ (r : core.result.Result Std.U16 Unit) (ren : cnf_transform_hybrid.Renamer) =>
      match r with
      | core.result.Result.Ok v =>
        Hybrid.fresh (absRenamer self) = some (v, absRenamer ren) ∧ ren.defs = self.defs
      | core.result.Result.Err _ =>
        Hybrid.fresh (absRenamer self) = none ∧ ren = self ⦄ := by
  unfold cnf_transform_hybrid.Renamer.fresh
  have hmax : (UScalar.cast .U32 core.num.U16.MAX).val = 65535 := by
    simp [UScalar.cast_val_eq, core.num.U16.MAX, U16.rMax]
  step*
  · have hi : i.val = 65535 := by rw [i_post]; exact hmax
    have hnb : ¬ (self.next.val < 65536) := by scalar_tac
    simp [Hybrid.fresh, freshVar, UScalar.tryMkOpt, UScalar.check_bounds, hnb]
  · have hi : i.val = 65535 := by rw [i_post]; exact hmax
    have hlt : self.next.val < 2 ^ 16 := by scalar_tac
    have hv : v.val = self.next.val := by
      rw [v_post, UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt hlt
    rw [Hybrid.fresh_eq_some]
    refine ⟨hv, hlt, ?_⟩
    simp only [absRenamer, i1_post]

/-! ### Naming a clause list

`Renamer::rename` allocates a gate, then loops over the clause list prefixing `neg g`
onto each clause and filing the result under the definitions. -/

/- `Conj` and `Disj` (and the two iterator branches) produce the same goals in
different orders, so several proofs below drive them with one shared script built from
`first | ... | ...`. Lean's linters flag the alternatives that a given instantiation
does not take; they are taken by the other one. -/
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
@[step]
theorem cnf_transform_hybrid.Renamer.rename_loop.spec
    (iter : alloc.vec.into_iter.IntoIter cnf.Clause)
    (self : cnf_transform_hybrid.Renamer) (g : Std.U16)
    (hlen : self.defs.val.length + iter.val.length ≤ Usize.max)
    (hcl : ∀ cl ∈ iter.val, cl.val.length < Usize.max) :
    cnf_transform_hybrid.Renamer.rename_loop iter self g
    ⦃ (ren : cnf_transform_hybrid.Renamer) =>
      ren.next = self.next ∧
      absClauses ren.defs =
        absClauses self.defs ++
          (iter.val.map (fun cl => cl.val)).map
            (fun cl => _root_.sat_solver.neg g :: cl) ⦄ := by
  unfold cnf_transform_hybrid.Renamer.rename_loop
  unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
    rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
  step*
  /- Each bullet is a `Vec::append`/`Vec::push` overflow side condition, the recursive
     call's own clause bound, or the final clause-list equation; the shape of the
     argument is the same in all five -- destruct the iterator and let `simp_all` chase
     the `o_post` equations, then `grind` on the residual arithmetic. -/
  · obtain ⟨l0, hl0⟩ := iter
    cases l0 with
    | nil => simp_all
    | cons c0 cs => simp_all [absClauses, Array.to_slice, Array.make] <;> grind
  · obtain ⟨l0, hl0⟩ := iter
    cases l0 with
    | nil => simp_all
    | cons c0 cs => simp_all [absClauses, Array.to_slice, Array.make] <;> grind
  · obtain ⟨l0, hl0⟩ := iter
    cases l0 with
    | nil => simp_all
    | cons c0 cs => simp_all [absClauses, Array.to_slice, Array.make] <;> grind
  · obtain ⟨l0, hl0⟩ := iter
    cases l0 with
    | nil => simp_all
    | cons c0 cs => simp_all [absClauses, Array.to_slice, Array.make] <;> grind
  · obtain ⟨l0, hl0⟩ := iter
    cases l0 with
    | nil => simp_all
    | cons c0 cs => simp_all [absClauses, Array.to_slice, Array.make] <;> grind
  · obtain ⟨l0, hl0⟩ := iter
    cases l0 with
    | nil => simp_all
    | cons c0 cs => simp_all [absClauses, Array.to_slice, Array.make] <;> grind
termination_by iter.val.length
decreasing_by
  obtain ⟨l, hl⟩ := iter
  cases l with
  | nil => simp_all
  | cons e es => simp_all


/- `Conj` and `Disj` (and the two iterator branches) produce the same goals in
different orders, so several proofs below drive them with one shared script built from
`first | ... | ...`. Lean's linters flag the alternatives that a given instantiation
does not take; they are taken by the other one. -/
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
@[step]
theorem cnf_transform_hybrid.Renamer.rename.spec (self : cnf_transform_hybrid.Renamer)
    (cnf1 : cnf.Cnf) (hlen : self.defs.val.length + cnf1.val.length ≤ Usize.max)
    (hcl : ∀ cl ∈ cnf1.val, cl.val.length < Usize.max) :
    cnf_transform_hybrid.Renamer.rename self cnf1
    ⦃ (r : core.result.Result cnf.Cnf Unit) (ren : cnf_transform_hybrid.Renamer) =>
      match r with
      | core.result.Result.Ok c =>
        Hybrid.rename (absRenamer self) (absClauses cnf1) =
          some (absClauses c, absRenamer ren)
      | core.result.Result.Err _ =>
        Hybrid.rename (absRenamer self) (absClauses cnf1) = none ⦄ := by
  unfold cnf_transform_hybrid.Renamer.rename
    alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
  step*
  · cases r
    · /- Gate allocated: the loop files one definition per clause. -/
      rename_i g
      simp only at r_post
      obtain ⟨hfresh, hdefs⟩ := r_post
      simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch, hdefs]
      unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
        rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
      step*
      · simp only [Hybrid.rename, hfresh]
        simp [absRenamer, absClauses, self2_post1, l_post, y_post,
          y1_post, hdefs, Array.to_slice, Array.make]
        simpa [absClauses, hdefs, List.map_map] using self2_post2.symm
    · /- `fresh` failed. -/
      simp only at r_post
      obtain ⟨hfresh, hself⟩ := r_post
      simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket, core.convert.From.Blanket.from]
      step*
      simp [Hybrid.rename, hfresh]


/-! ### The decision rule

`disjoin` computes `n * m` in `usize`, so `hmul` is a genuine precondition of the Rust,
not proof bookkeeping -- `Hybrid.cnfRec_length_le` is what supplies it at the call site.
`hpair` is what `cnf_transform_naive::distribute` needs for its own `clause_union`. -/

/- `Conj` and `Disj` (and the two iterator branches) produce the same goals in
different orders, so several proofs below drive them with one shared script built from
`first | ... | ...`. Lean's linters flag the alternatives that a given instantiation
does not take; they are taken by the other one. -/
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
@[step]
theorem cnf_transform_hybrid.Renamer.disjoin.spec (self : cnf_transform_hybrid.Renamer)
    (c1 c2 : cnf.Cnf)
    (hpair : ∀ cl1 ∈ c1.val, ∀ cl2 ∈ c2.val,
      cl1.val.length + cl2.val.length ≤ Usize.max)
    (hcl1 : ∀ cl ∈ c1.val, cl.val.length < Usize.max)
    (hcl2 : ∀ cl ∈ c2.val, cl.val.length < Usize.max)
    (hmul : c1.val.length * c2.val.length ≤ Usize.max)
    (hadd : c1.val.length + c2.val.length ≤ Usize.max)
    (hdefs1 : self.defs.val.length + c1.val.length ≤ Usize.max)
    (hdefs2 : self.defs.val.length + c2.val.length ≤ Usize.max) :
    cnf_transform_hybrid.Renamer.disjoin self c1 c2
    ⦃ (r : core.result.Result cnf.Cnf Unit) (ren : cnf_transform_hybrid.Renamer) =>
      match r with
      | core.result.Result.Ok c =>
        Hybrid.disjoin (absRenamer self) (absClauses c1) (absClauses c2) =
          some (absClauses c, absRenamer ren)
      | core.result.Result.Err _ =>
        Hybrid.disjoin (absRenamer self) (absClauses c1) (absClauses c2) = none ⦄ := by
  unfold cnf_transform_hybrid.Renamer.disjoin
  step*
  · /- Distributed: the guard matched, and nothing was named. -/
    have hg : (Cnf.contents c1).length * (Cnf.contents c2).length ≤
        (Cnf.contents c1).length + (Cnf.contents c2).length := by
      simp only [Cnf.contents_def, List.length_map]; scalar_tac
    simp only [Hybrid.disjoin, absClauses_eq_contents, if_pos hg, c_post]
  · /- Named the left side. -/
    cases r
    · rename_i cr
      simp only at r_post
      obtain ⟨g, hnamed⟩ := Hybrid.rename_named r_post
      have hlen1 : cr.val.length = 1 := by
        have : (absClauses cr).length = 1 := by rw [hnamed]; simp
        simpa using this
      have hcls : ∀ cl ∈ cr.val, cl.val.length = 1 := by
        intro cl hcl
        have hmem : cl.val ∈ absClauses cr := by
          simp only [absClauses_def, List.mem_map]; exact ⟨cl, hcl, rfl⟩
        rw [hnamed] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rw [hmem]; simp
      simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
      step*
      · /- `distribute`'s pairwise clause bound: the named side is a single literal. -/
        intro cl1 hcl1' cl2 hcl2'
        rw [hcls cl1 hcl1']
        have := hcl2 cl2 hcl2'
        scalar_tac
      · simp only [Hybrid.disjoin]
        have hg : ¬ ((absClauses c1).length * (absClauses c2).length ≤
            (absClauses c1).length + (absClauses c2).length) := by
          simp only [absClauses_length]; scalar_tac
        have hge : (absClauses c2).length ≤ (absClauses c1).length := by
          simp only [absClauses_length]; scalar_tac
        rw [if_neg hg, if_pos hge, r_post]
        simp only [absClauses_eq_contents, c_post]
    · simp only at r_post
      simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket, core.convert.From.Blanket.from]
      step*
      simp only [Hybrid.disjoin]
      have hg : ¬ ((absClauses c1).length * (absClauses c2).length ≤
          (absClauses c1).length + (absClauses c2).length) := by
        simp only [absClauses_length]; scalar_tac
      have hge : (absClauses c2).length ≤ (absClauses c1).length := by
        simp only [absClauses_length]; scalar_tac
      rw [if_neg hg, if_pos hge, r_post]
  · /- Named the right side; mirror image of the previous case. -/
    cases r
    · rename_i cr
      simp only at r_post
      obtain ⟨g, hnamed⟩ := Hybrid.rename_named r_post
      have hlen1 : cr.val.length = 1 := by
        have h1 : (absClauses cr).length = 1 := by rw [hnamed]; simp
        simpa using h1
      have hcls : ∀ cl ∈ cr.val, cl.val.length = 1 := by
        intro cl hcl
        have hmem : cl.val ∈ absClauses cr := by
          simp only [absClauses_def, List.mem_map]; exact ⟨cl, hcl, rfl⟩
        rw [hnamed] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rw [hmem]; simp
      have hg : ¬ ((absClauses c1).length * (absClauses c2).length ≤
          (absClauses c1).length + (absClauses c2).length) := by
        simp only [absClauses_length]; scalar_tac
      have hlt : ¬ ((absClauses c2).length ≤ (absClauses c1).length) := by
        simp only [absClauses_length]; scalar_tac
      simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
      step*
      · intro cl1 hcl1' cl2 hcl2'
        rw [hcls cl2 hcl2']
        have := hcl1 cl1 hcl1'
        scalar_tac
      · simp only [Hybrid.disjoin]
        rw [if_neg hg, if_neg hlt, r_post]
        simp only [absClauses_eq_contents, c_post]
    · simp only at r_post
      have hg : ¬ ((absClauses c1).length * (absClauses c2).length ≤
          (absClauses c1).length + (absClauses c2).length) := by
        simp only [absClauses_length]; scalar_tac
      have hlt : ¬ ((absClauses c2).length ≤ (absClauses c1).length) := by
        simp only [absClauses_length]; scalar_tac
      simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket, core.convert.From.Blanket.from]
      step*
      simp only [Hybrid.disjoin]
      rw [if_neg hg, if_neg hlt, r_post]

/-! ### The recursion

One precondition covers every overflow side condition below: the body is at most one
clause per AST node (`cnfRec_length_le`), the definitions at most one per pair
(`cnfRec_defs_length_le`), and clauses at most one literal per node
(`cnfRec_clause_length_le`). -/

/- `Conj` and `Disj` (and the two iterator branches) produce the same goals in
different orders, so several proofs below drive them with one shared script built from
`first | ... | ...`. Lean's linters flag the alternatives that a given instantiation
does not take; they are taken by the other one. -/
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
@[step]
theorem cnf_transform_hybrid.Renamer.cnf.spec (self : cnf_transform_hybrid.Renamer)
    (expr1 : expr.Expr) (negate : Bool)
    (hb : self.defs.val.length + exprSize expr1 * exprSize expr1 + exprSize expr1 + 1
      ≤ Usize.max) :
    cnf_transform_hybrid.Renamer.cnf self expr1 negate
    ⦃ (r : core.result.Result cnf.Cnf Unit) (ren : cnf_transform_hybrid.Renamer) =>
      match r with
      | core.result.Result.Ok c =>
        Hybrid.cnfRec (absRenamer self) expr1 negate = some (absClauses c, absRenamer ren)
      | core.result.Result.Err _ =>
        Hybrid.cnfRec (absRenamer self) expr1 negate = none ⦄ := by
  induction expr1 generalizing self negate with
  | True =>
    unfold cnf_transform_hybrid.Renamer.cnf
    split
    · unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
        rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
      step*
      simp_all [Hybrid.cnfRec, absClauses, Array.to_slice, Array.make]
    · step*
      simp_all [Hybrid.cnfRec, absClauses]
  | False =>
    unfold cnf_transform_hybrid.Renamer.cnf
    split
    · step*
      simp_all [Hybrid.cnfRec, absClauses]
    · unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
        rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
      step*
      simp_all [Hybrid.cnfRec, absClauses, Array.to_slice, Array.make]
  | Variable v =>
    unfold cnf_transform_hybrid.Renamer.cnf
    unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
      rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
    step*
    simp_all [Hybrid.cnfRec, absClauses, Array.to_slice, Array.make]
  | Neg e ih =>
    unfold cnf_transform_hybrid.Renamer.cnf
    step*
    · simp only [exprSize] at hb ⊢
      have : exprSize e ≤ exprSize e * exprSize e + exprSize e := by grind
      grind
    · /- `!negate` in the model vs `decide ¬negate` in the extraction. -/
      simpa [Hybrid.cnfRec] using r_post
  | Conj e1 e2 ih1 ih2 =>
    unfold cnf_transform_hybrid.Renamer.cnf
    step*
    · /- `hb` for the left operand. -/
      simp only [exprSize] at hb ⊢
      grind
    · cases r
      · rename_i c1
        simp only at r_post
        have hd1 : self1.defs.val.length ≤ self.defs.val.length + exprSize e1 * exprSize e1 := by
          simpa using Hybrid.cnfRec_defs_length_le r_post
        have hl1 : c1.val.length ≤ exprSize e1 := by
          simpa using Hybrid.cnfRec_length_le r_post
        have hcl1 : ∀ cl ∈ c1.val, cl.val.length ≤ exprSize e1 := fun cl hcl =>
          Hybrid.cnfRec_clause_length_le r_post cl.val (mem_absClauses hcl)
        /- Stable names: the inner `step*` shadows `r_post`/`r1_post`. -/
        have hr1 := r_post
        simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
        step*
        · /- `hb` for the right operand. -/
          simp only [exprSize] at hb ⊢
          grind
        · cases r1
          · rename_i c2
            simp only at r1_post
            have hd2 : self2.defs.val.length ≤ self1.defs.val.length + exprSize e2 * exprSize e2 := by
              simpa using Hybrid.cnfRec_defs_length_le r1_post
            have hl2 : c2.val.length ≤ exprSize e2 := by
              simpa using Hybrid.cnfRec_length_le r1_post
            have hcl2 : ∀ cl ∈ c2.val, cl.val.length ≤ exprSize e2 := fun cl hcl =>
              Hybrid.cnfRec_clause_length_le r1_post cl.val (mem_absClauses hcl)
            have hr2 := r1_post
            simp only [exprSize] at hb
            simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
            step*
            · /- `disjoin`/`conj_cnf` preconditions and the result equation; the same
                 five arguments serve `Conj` and `Disj`, which differ only in which
                 polarity takes which branch. -/
              first
                | (intro cl1 ha1 cl2 ha2
                   have a1 := hcl1 cl1 ha1
                   have a2 := hcl2 cl2 ha2
                   grind)
                | (intro cl ha
                   first
                     | (have := hcl1 cl ha; grind)
                     | (have := hcl2 cl ha; grind))
                | (have := Nat.mul_le_mul hl1 hl2; grind)
                | grind
                | (simp only [Hybrid.cnfRec, hr1, hr2]
                   simp_all [absClauses])
            · /- `disjoin`/`conj_cnf` preconditions and the result equation; the same
                 five arguments serve `Conj` and `Disj`, which differ only in which
                 polarity takes which branch. -/
              first
                | (intro cl1 ha1 cl2 ha2
                   have a1 := hcl1 cl1 ha1
                   have a2 := hcl2 cl2 ha2
                   grind)
                | (intro cl ha
                   first
                     | (have := hcl1 cl ha; grind)
                     | (have := hcl2 cl ha; grind))
                | (have := Nat.mul_le_mul hl1 hl2; grind)
                | grind
                | (simp only [Hybrid.cnfRec, hr1, hr2]
                   simp_all [absClauses])
            · /- `disjoin`/`conj_cnf` preconditions and the result equation; the same
                 five arguments serve `Conj` and `Disj`, which differ only in which
                 polarity takes which branch. -/
              first
                | (intro cl1 ha1 cl2 ha2
                   have a1 := hcl1 cl1 ha1
                   have a2 := hcl2 cl2 ha2
                   grind)
                | (intro cl ha
                   first
                     | (have := hcl1 cl ha; grind)
                     | (have := hcl2 cl ha; grind))
                | (have := Nat.mul_le_mul hl1 hl2; grind)
                | grind
                | (simp only [Hybrid.cnfRec, hr1, hr2]
                   simp_all [absClauses])
            · /- `disjoin`/`conj_cnf` preconditions and the result equation; the same
                 five arguments serve `Conj` and `Disj`, which differ only in which
                 polarity takes which branch. -/
              first
                | (intro cl1 ha1 cl2 ha2
                   have a1 := hcl1 cl1 ha1
                   have a2 := hcl2 cl2 ha2
                   grind)
                | (intro cl ha
                   first
                     | (have := hcl1 cl ha; grind)
                     | (have := hcl2 cl ha; grind))
                | (have := Nat.mul_le_mul hl1 hl2; grind)
                | grind
                | (simp only [Hybrid.cnfRec, hr1, hr2]
                   simp_all [absClauses])
            · /- `disjoin`/`conj_cnf` preconditions and the result equation; the same
                 five arguments serve `Conj` and `Disj`, which differ only in which
                 polarity takes which branch. -/
              first
                | (intro cl1 ha1 cl2 ha2
                   have a1 := hcl1 cl1 ha1
                   have a2 := hcl2 cl2 ha2
                   grind)
                | (intro cl ha
                   first
                     | (have := hcl1 cl ha; grind)
                     | (have := hcl2 cl ha; grind))
                | (have := Nat.mul_le_mul hl1 hl2; grind)
                | grind
                | (simp only [Hybrid.cnfRec, hr1, hr2]
                   simp_all [absClauses])
          · simp only at r1_post
            simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
          core.convert.From.Blanket, core.convert.From.Blanket.from]
            step*
            simp [Hybrid.cnfRec, r_post, r1_post]
      · simp only at r_post
        simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
          core.convert.From.Blanket, core.convert.From.Blanket.from]
        step*
        simp [Hybrid.cnfRec, r_post]
  | Disj e1 e2 ih1 ih2 =>
    unfold cnf_transform_hybrid.Renamer.cnf
    step*
    · /- `hb` for the left operand. -/
      simp only [exprSize] at hb ⊢
      grind
    · cases r
      · rename_i c1
        simp only at r_post
        have hd1 : self1.defs.val.length ≤ self.defs.val.length + exprSize e1 * exprSize e1 := by
          simpa using Hybrid.cnfRec_defs_length_le r_post
        have hl1 : c1.val.length ≤ exprSize e1 := by
          simpa using Hybrid.cnfRec_length_le r_post
        have hcl1 : ∀ cl ∈ c1.val, cl.val.length ≤ exprSize e1 := fun cl hcl =>
          Hybrid.cnfRec_clause_length_le r_post cl.val (mem_absClauses hcl)
        /- Stable names: the inner `step*` shadows `r_post`/`r1_post`. -/
        have hr1 := r_post
        simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
        step*
        · /- `hb` for the right operand. -/
          simp only [exprSize] at hb ⊢
          grind
        · cases r1
          · rename_i c2
            simp only at r1_post
            have hd2 : self2.defs.val.length ≤ self1.defs.val.length + exprSize e2 * exprSize e2 := by
              simpa using Hybrid.cnfRec_defs_length_le r1_post
            have hl2 : c2.val.length ≤ exprSize e2 := by
              simpa using Hybrid.cnfRec_length_le r1_post
            have hcl2 : ∀ cl ∈ c2.val, cl.val.length ≤ exprSize e2 := fun cl hcl =>
              Hybrid.cnfRec_clause_length_le r1_post cl.val (mem_absClauses hcl)
            have hr2 := r1_post
            simp only [exprSize] at hb
            simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
            step*
            · /- `disjoin`/`conj_cnf` preconditions and the result equation; the same
                 five arguments serve `Conj` and `Disj`, which differ only in which
                 polarity takes which branch. -/
              first
                | (intro cl1 ha1 cl2 ha2
                   have a1 := hcl1 cl1 ha1
                   have a2 := hcl2 cl2 ha2
                   grind)
                | (intro cl ha
                   first
                     | (have := hcl1 cl ha; grind)
                     | (have := hcl2 cl ha; grind))
                | (have := Nat.mul_le_mul hl1 hl2; grind)
                | grind
                | (simp only [Hybrid.cnfRec, hr1, hr2]
                   simp_all [absClauses])
            · /- `disjoin`/`conj_cnf` preconditions and the result equation; the same
                 five arguments serve `Conj` and `Disj`, which differ only in which
                 polarity takes which branch. -/
              first
                | (intro cl1 ha1 cl2 ha2
                   have a1 := hcl1 cl1 ha1
                   have a2 := hcl2 cl2 ha2
                   grind)
                | (intro cl ha
                   first
                     | (have := hcl1 cl ha; grind)
                     | (have := hcl2 cl ha; grind))
                | (have := Nat.mul_le_mul hl1 hl2; grind)
                | grind
                | (simp only [Hybrid.cnfRec, hr1, hr2]
                   simp_all [absClauses])
            · /- `disjoin`/`conj_cnf` preconditions and the result equation; the same
                 five arguments serve `Conj` and `Disj`, which differ only in which
                 polarity takes which branch. -/
              first
                | (intro cl1 ha1 cl2 ha2
                   have a1 := hcl1 cl1 ha1
                   have a2 := hcl2 cl2 ha2
                   grind)
                | (intro cl ha
                   first
                     | (have := hcl1 cl ha; grind)
                     | (have := hcl2 cl ha; grind))
                | (have := Nat.mul_le_mul hl1 hl2; grind)
                | grind
                | (simp only [Hybrid.cnfRec, hr1, hr2]
                   simp_all [absClauses])
            · /- `disjoin`/`conj_cnf` preconditions and the result equation; the same
                 five arguments serve `Conj` and `Disj`, which differ only in which
                 polarity takes which branch. -/
              first
                | (intro cl1 ha1 cl2 ha2
                   have a1 := hcl1 cl1 ha1
                   have a2 := hcl2 cl2 ha2
                   grind)
                | (intro cl ha
                   first
                     | (have := hcl1 cl ha; grind)
                     | (have := hcl2 cl ha; grind))
                | (have := Nat.mul_le_mul hl1 hl2; grind)
                | grind
                | (simp only [Hybrid.cnfRec, hr1, hr2]
                   simp_all [absClauses])
            · /- `disjoin`/`conj_cnf` preconditions and the result equation; the same
                 five arguments serve `Conj` and `Disj`, which differ only in which
                 polarity takes which branch. -/
              first
                | (intro cl1 ha1 cl2 ha2
                   have a1 := hcl1 cl1 ha1
                   have a2 := hcl2 cl2 ha2
                   grind)
                | (intro cl ha
                   first
                     | (have := hcl1 cl ha; grind)
                     | (have := hcl2 cl ha; grind))
                | (have := Nat.mul_le_mul hl1 hl2; grind)
                | grind
                | (simp only [Hybrid.cnfRec, hr1, hr2]
                   simp_all [absClauses])
          · simp only at r1_post
            simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
          core.convert.From.Blanket, core.convert.From.Blanket.from]
            step*
            simp [Hybrid.cnfRec, r_post, r1_post]
      · simp only at r_post
        simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
          core.convert.From.Blanket, core.convert.From.Blanket.from]
        step*
        simp [Hybrid.cnfRec, r_post]


/-! ### The transformation as a whole -/

/- `Conj` and `Disj` (and the two iterator branches) produce the same goals in
different orders, so several proofs below drive them with one shared script built from
`first | ... | ...`. Lean's linters flag the alternatives that a given instantiation
does not take; they are taken by the other one. -/
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
@[step]
theorem cnf_transform_hybrid.Renamer.new_loop.spec
    (iter : alloc.vec.into_iter.IntoIter Std.U16) (next : Std.U32) :
    cnf_transform_hybrid.Renamer.new_loop iter next ⦃ (r : Std.U32) =>
      next.val ≤ r.val ∧ (∀ v ∈ iter.val, v.val < r.val)
      ∧ ∀ m, next.val ≤ m → (∀ v ∈ iter.val, v.val < m) → r.val ≤ m ⦄ := by
  unfold cnf_transform_hybrid.Renamer.new_loop
  step*
  all_goals
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      first
      | (simp_all; done)
      | (obtain ⟨heq, hiter⟩ := o_post
         have hlite : v = e := by
           have h1 : o = some v := by assumption
           rw [h1] at heq; exact Option.some.inj heq
         subst hlite
         refine ⟨by scalar_tac, ?_, ?_⟩
         · intro w hw
           rcases List.mem_cons.mp (by simpa using hw) with rfl | hw'
           · scalar_tac
           · exact r_post2 w (by rw [hiter]; exact hw')
         · intro m hm hall
           have hm2 : v.val < m := hall v (by simp)
           refine r_post3 m (by scalar_tac) ?_
           intro w hw
           exact hall w (by simp only [hiter] at hw; simp [hw]))
termination_by iter.val.length
decreasing_by
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all

@[step]
theorem cnf_transform_hybrid.Renamer.new.spec (e : expr.Expr)
    (hbound : exprSize e ≤ Usize.max) :
    cnf_transform_hybrid.Renamer.new e ⦃ (ren : cnf_transform_hybrid.Renamer) =>
      ren.defs.val = [] ∧ (∀ k ∈ varsOf e, k.val < ren.next.val)
      ∧ ∀ m, (∀ k ∈ varsOf e, k.val < m) → ren.next.val ≤ m ⦄ := by
  unfold cnf_transform_hybrid.Renamer.new
    alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
  step*
  exact ⟨v1_post, fun k hk => next_post2 k ((v_post1 k).mpr hk),
    fun m hm => next_post3 m (Nat.zero_le _) fun w hw => hm w ((v_post1 w).mp hw)⟩

/-- What `to_cnf` having returned `c` tells us about `c`: it is the body of a completed
    `Hybrid.cnfRec` run, started from a well-formed state whose counter already sits above
    every variable of `e`, with that run's definitions appended.

    Naming this rather than inlining it into `to_cnf.spec` is what lets a caller consume
    the extracted transformation without ever mentioning `Hybrid.cnfRec`: `SatDpll.lean`
    steps through `to_cnf`, receives an `Encodes e c`, and hands it straight to
    `Encodes.sound`/`Encodes.complete` below. The two `to_cnf.{sound,complete}` corollaries
    are the same two facts packaged as Hoare triples, for a caller that would rather read
    one statement about the generated code than two. -/
def cnf_transform_hybrid.Encodes (e : expr.Expr) (c : cnf.Cnf) : Prop :=
  ∃ s s' body, Hybrid.State.Wf s ∧ (∀ k ∈ varsOf e, k.val < s.next) ∧
    (∀ m, (∀ k ∈ varsOf e, k.val < m) → s.next ≤ m) ∧
    s.defs = [] ∧ Hybrid.cnfRec s e false = some (body, s') ∧
    absClauses c = body ++ s'.defs

/-- **Soundness, as an implication**: every model of a CNF the extracted `to_cnf`
    returned satisfies `e`. -/
theorem cnf_transform_hybrid.Encodes.sound {e : expr.Expr} {c : cnf.Cnf}
    {w : Std.U16 → Bool} (h : cnf_transform_hybrid.Encodes e c)
    (hw : Cnf.eval w (Cnf.contents c) = true) : evalPure w e = true := by
  obtain ⟨s, s', body, hwf, hvars, -, hdefs, hrec, habs⟩ := h
  -- `absClauses c` and `Cnf.contents c` are the same list (`absClauses_eq_contents`).
  have hw' : Cnf.eval w (absClauses c) = true := hw
  rw [habs, Cnf.eval_append] at hw'
  obtain ⟨hbody, hdefsev⟩ := Bool.and_eq_true _ _ |>.mp hw'
  simpa using Hybrid.cnfRec_sound hrec hdefsev hbody

/-- **Completeness, as an implication**: every model of `e` extends to a model of a CNF
    the extracted `to_cnf` returned, agreeing with it on all of `e`'s own variables. -/
theorem cnf_transform_hybrid.Encodes.complete {e : expr.Expr} {c : cnf.Cnf}
    {w : Std.U16 → Bool} (h : cnf_transform_hybrid.Encodes e c)
    (hsat : evalPure w e = true) :
    ∃ w', (∀ k ∈ varsOf e, w' k = w k) ∧ Cnf.eval w' (Cnf.contents c) = true := by
  obtain ⟨s, s', body, hwf, hvars, -, hdefs, hrec, habs⟩ := h
  obtain ⟨w', hag, hdefsev, hbody⟩ :=
    Hybrid.cnfRec_complete hwf hvars hrec w (by rw [hdefs]; simp [Cnf.eval])
  refine ⟨w', fun k hk => hag k (hvars k hk), ?_⟩
  show Cnf.eval w' (absClauses c) = true
  rw [habs, Cnf.eval_append]
  refine Bool.and_eq_true _ _ |>.mpr ⟨?_, hdefsev⟩
  rw [hbody]
  simp [hsat]

/-- **How wide the encoded CNF is**: every variable of it is either one of `e`'s own,
    below whatever bound `m` those satisfy, or a gate -- and there is at most one gate per
    AST node, since the only thing that allocates one is `disjoin`'s call to `rename`.

    This is what a caller that has to *size an array* by the CNF needs, and it is the one
    fact `Encodes` grew a field for: the bound is on `s.next`, the counter the first gate
    gets, and only `Renamer::new` knows it sits no higher than `e`'s variables force. -/
theorem cnf_transform_hybrid.Encodes.vars_lt {e : expr.Expr} {c : cnf.Cnf}
    (h : cnf_transform_hybrid.Encodes e c) {m : Nat}
    (hm : ∀ k ∈ varsOf e, k.val < m) :
    ∀ v ∈ cnfVars (Cnf.contents c), v.val < m + exprSize e := by
  obtain ⟨s, s', body, hwf, hvars, hlub, hdefs, hrec, habs⟩ := h
  have hnext : s'.next ≤ m + exprSize e :=
    le_trans (Hybrid.cnfRec_next_le_add hrec) (by have := hlub m hm; omega)
  have hbody := Hybrid.cnfRec_vars_lt hvars hrec
  have hdefsv := Hybrid.cnfRec_wf hwf hvars hrec
  intro v hv
  rw [← absClauses_eq_contents, habs, cnfVars_append, List.mem_append] at hv
  rcases hv with hv | hv
  · exact Nat.lt_of_lt_of_le (hbody v hv) hnext
  · exact Nat.lt_of_lt_of_le (hdefsv v hv) hnext

/-- **How long its clauses are**: at most one literal per AST node, plus the `neg g` a
    definition clause carries. -/
theorem cnf_transform_hybrid.Encodes.clause_length_le {e : expr.Expr} {c : cnf.Cnf}
    (h : cnf_transform_hybrid.Encodes e c) :
    ∀ cl ∈ Cnf.contents c, cl.length ≤ exprSize e + 1 := by
  obtain ⟨s, s', body, hwf, hvars, hlub, hdefs, hrec, habs⟩ := h
  intro cl hcl
  rw [← absClauses_eq_contents, habs, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · exact le_trans (Hybrid.cnfRec_clause_length_le hrec cl hcl) (Nat.le_succ _)
  · exact Hybrid.cnfRec_defs_clause_length_le hrec (Nat.le_refl _)
      (by rw [hdefs]; simp) cl hcl

/-- **How many clauses it has**: the body is one clause per node, the definitions one per
    node per naming. -/
theorem cnf_transform_hybrid.Encodes.length_le {e : expr.Expr} {c : cnf.Cnf}
    (h : cnf_transform_hybrid.Encodes e c) :
    (Cnf.contents c).length ≤ exprSize e * exprSize e + exprSize e := by
  obtain ⟨s, s', body, hwf, hvars, hlub, hdefs, hrec, habs⟩ := h
  have hb := Hybrid.cnfRec_length_le hrec
  have hd := Hybrid.cnfRec_defs_length_le hrec
  rw [hdefs] at hd
  rw [← absClauses_eq_contents, habs, List.length_append]
  simp only [List.length_nil, Nat.zero_add] at hd
  omega

@[step]
theorem cnf_transform_hybrid.to_cnf.spec (e : expr.Expr)
    (hbound : exprSize e * exprSize e + exprSize e + 1 ≤ Usize.max) :
    cnf_transform_hybrid.to_cnf e ⦃ (r : core.result.Result cnf.Cnf Unit) =>
      match r with
      | core.result.Result.Ok c => cnf_transform_hybrid.Encodes e c
      | core.result.Result.Err _ => True ⦄ := by
  unfold cnf_transform_hybrid.to_cnf
  step*
  · cases r
    · /- Body built; append the definitions. -/
      rename_i body
      simp only at r_post
      have hwf : Hybrid.State.Wf (absRenamer renamer) := by
        intro k hk; simp [absRenamer, absClauses, cnfVars, renamer_post1] at hk
      have hb1 : body.val.length ≤ exprSize e := by
        simpa using Hybrid.cnfRec_length_le r_post
      have hb2 : renamer1.defs.val.length ≤ exprSize e * exprSize e := by
        have hle := Hybrid.cnfRec_defs_length_le r_post
        simp only [absRenamer_defs, absClauses_length, renamer_post1] at hle
        simpa using hle
      simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
      step*
      · exact ⟨absRenamer renamer, absRenamer renamer1, absClauses body, hwf,
          by simpa using renamer_post2, by simpa using renamer_post3,
          by simp [absRenamer, absClauses, renamer_post1],
          r_post, by simp [absClauses, c_post]⟩
    · simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket.from]
      step*


/-! ### Correctness of the extracted transformation

As in `TseitinExtraction.lean`: these mention `cnf_transform_hybrid.to_cnf`, the
function hax generated from `src/cnf_transform_hybrid.rs`, and nothing else. -/

/-- **Soundness**: every model of the CNF that the extracted `to_cnf` returns satisfies
    `e`. -/
theorem cnf_transform_hybrid.to_cnf.sound (e : expr.Expr) (w : Std.U16 → Bool)
    (hbound : exprSize e * exprSize e + exprSize e + 1 ≤ Usize.max) :
    cnf_transform_hybrid.to_cnf e ⦃ (r : core.result.Result cnf.Cnf Unit) =>
      ∀ c, r = core.result.Result.Ok c →
        Cnf.eval w (absClauses c) = true → evalPure w e = true ⦄ := by
  step*
  rw [r_post2] at r_post1
  simp only at r_post1
  exact cnf_transform_hybrid.Encodes.sound r_post1 r_post3

/-- **Completeness**: every model of `e` extends to a model of the CNF that the
    extracted `to_cnf` returns, agreeing with it on all of `e`'s own variables. -/
theorem cnf_transform_hybrid.to_cnf.complete (e : expr.Expr) (w : Std.U16 → Bool)
    (hbound : exprSize e * exprSize e + exprSize e + 1 ≤ Usize.max)
    (hsat : evalPure w e = true) :
    cnf_transform_hybrid.to_cnf e ⦃ (r : core.result.Result cnf.Cnf Unit) =>
      ∀ c, r = core.result.Result.Ok c →
        ∃ w', (∀ k ∈ varsOf e, w' k = w k) ∧ Cnf.eval w' (absClauses c) = true ⦄ := by
  step*
  rw [r_post2] at r_post1
  simp only at r_post1
  exact cnf_transform_hybrid.Encodes.complete r_post1 hsat


end sat_solver
