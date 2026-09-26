/- The extraction-matching layer for `cnf_transform_tseitin`.

`Tseitin.lean` proves the encoding correct against a pure Lean model. This file is what
makes those theorems statements about the *Rust*: every extracted function gets an
`@[step]` spec saying it agrees with its counterpart in that model, under the
abstraction `absEncoder` below. Without this file, a transcription error between the
Rust and the model would go undetected.

Two things here have no analogue in `Cnf.lean`, which is why that file is shorter:

  * the encoder threads a **state** (`Encoder`), so every spec has to say what came out
    *and* what the state became, related through `absEncoder`;
  * every `?` in the Rust desugars to `Try.branch` on a `Result` plus a
    `ControlFlow` match, so each spec carries an explicit `Ok`/`Err` case split. The
    naive transform is total and has neither. -/
import SatSolver.Extraction
import SatSolver.Verification.Prelude
import SatSolver.Verification.MapLemmas
import SatSolver.Verification.Semantics
import SatSolver.Verification.Cnf
import SatSolver.Verification.Encoding
import SatSolver.Verification.Tseitin

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

namespace Tseitin

/-! ### The abstraction -/

/-- A `Vec` of `Vec`s of literals, read as the plain clause list the model uses. -/
def absClauses (v : alloc.vec.Vec cnf.Clause) : List (List cnf.Literal) :=
  v.val.map (fun cl => cl.val)

@[simp]
theorem absClauses_def (v : alloc.vec.Vec cnf.Clause) :
    absClauses v = v.val.map (fun cl => cl.val) := rfl

/-- The model state an extracted `Encoder` stands for. -/
def absEncoder (enc : cnf_transform_tseitin.Encoder) : State :=
  { next := enc.next.val
    trueVar :=
      match enc.true_var with
      | core.option.Option.None => none
      | core.option.Option.Some v => some v
    clauses := absClauses enc.clauses }

@[simp]
theorem absEncoder_next (enc : cnf_transform_tseitin.Encoder) :
    (absEncoder enc).next = enc.next.val := rfl

@[simp]
theorem absEncoder_clauses (enc : cnf_transform_tseitin.Encoder) :
    (absEncoder enc).clauses = absClauses enc.clauses := rfl

@[simp]
theorem absClauses_length (v : alloc.vec.Vec cnf.Clause) :
    (absClauses v).length = v.val.length := by simp [absClauses]

/-- Pushing one clause onto the `Vec` appends its literal list to the model's. -/
theorem absClauses_push {v : alloc.vec.Vec cnf.Clause} {w : alloc.vec.Vec cnf.Clause}
    {cl : cnf.Clause} (h : w.val = v.val ++ [cl]) :
    absClauses w = absClauses v ++ [cl.val] := by simp [absClauses, h]

end Tseitin

open Tseitin

/-! ### Literal helpers -/

@[step]
theorem cnf_transform_tseitin.pos.spec (var : Std.U16) :
    cnf_transform_tseitin.pos var ⦃ (l : cnf.Literal) => l = _root_.sat_solver.pos var ⦄ := by
  unfold cnf_transform_tseitin.pos
  step*
  simp [_root_.sat_solver.pos]

@[step]
theorem cnf_transform_tseitin.neg.spec (var : Std.U16) :
    cnf_transform_tseitin.neg var ⦃ (l : cnf.Literal) => l = _root_.sat_solver.neg var ⦄ := by
  unfold cnf_transform_tseitin.neg
  step*
  simp [_root_.sat_solver.neg]

@[step]
theorem cnf_transform_tseitin.flip.spec (lit : cnf.Literal) :
    cnf_transform_tseitin.flip lit ⦃ (l : cnf.Literal) => l = _root_.sat_solver.flip lit ⦄ := by
  unfold cnf_transform_tseitin.flip
  step*
  simp [_root_.sat_solver.flip]

/-! ### Allocating a gate

`Encoder::fresh` is where the `u32` counter meets the `u16` variable space: it compares
against `U16::MAX` and only then casts. The model's `freshVar` says the same thing with
`UScalar.tryMkOpt`, so the spec is mostly about lining those two up. -/

@[step]
theorem cnf_transform_tseitin.Encoder.fresh.spec (self : cnf_transform_tseitin.Encoder) :
    cnf_transform_tseitin.Encoder.fresh self
    ⦃ (r : core.result.Result Std.U16 Unit) (enc : cnf_transform_tseitin.Encoder) =>
      match r with
      | core.result.Result.Ok v =>
        Tseitin.fresh (absEncoder self) = some (v, absEncoder enc) ∧
          enc.true_var = self.true_var ∧ enc.clauses = self.clauses
      | core.result.Result.Err _ =>
        Tseitin.fresh (absEncoder self) = none ∧ enc = self ⦄ := by
  unfold cnf_transform_tseitin.Encoder.fresh
  have hmax : (UScalar.cast .U32 core.num.U16.MAX).val = 65535 := by
    simp [UScalar.cast_val_eq, core.num.U16.MAX, U16.rMax]
  step*
  · /- Above the ceiling: `freshVar` refuses for exactly the same reason. -/
    have hi : i.val = 65535 := by rw [i_post]; exact hmax
    have hnb : ¬ (self.next.val < 65536) := by scalar_tac
    simp [Tseitin.fresh, freshVar, UScalar.tryMkOpt, UScalar.check_bounds, hnb]
  · /- In range: the extracted cast and `ofNatCore` agree, so the two states match.
       (The `+ 1` overflow side condition is discharged by `step*` itself: the guard
       has already bounded `next` by 65535.) -/
    have hi : i.val = 65535 := by rw [i_post]; exact hmax
    have hlt : self.next.val < 2 ^ 16 := by scalar_tac
    have hv : v.val = self.next.val := by
      rw [v_post, UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt hlt
    rw [Tseitin.fresh_eq_some]
    refine ⟨hv, hlt, ?_⟩
    simp only [absEncoder, i1_post]

/-! ### The shared constant gate -/

/- `Conj` and `Disj` share one proof script (they differ only in the clauses they
emit), as do the `Ok`/`Err` and iterator branches. Lean's linters flag the simp
arguments and alternatives that a given instantiation does not use; the other one
uses them. -/
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
@[step]
theorem cnf_transform_tseitin.Encoder.constant.spec (self : cnf_transform_tseitin.Encoder)
    (value : Bool) (hlen : self.clauses.val.length + 1 ≤ Usize.max) :
    cnf_transform_tseitin.Encoder.constant self value
    ⦃ (r : core.result.Result cnf.Literal Unit) (enc : cnf_transform_tseitin.Encoder) =>
      match r with
      | core.result.Result.Ok l =>
        Tseitin.constant (absEncoder self) value = some (l, absEncoder enc)
      | core.result.Result.Err _ => Tseitin.constant (absEncoder self) value = none ⦄ := by
  unfold cnf_transform_tseitin.Encoder.constant
  step*
  · /- `true_var` unset: `?` on the `fresh` result, so split on it. -/
    cases r
    · rename_i g
      simp only at r_post
      obtain ⟨hfresh, htv, hcl⟩ := r_post
      simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch, hcl]
      unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
        rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
      step*
      · /- `value = true`: the gate's own positive literal. -/
        have htvnone : (absEncoder self).trueVar = none := by
          simp [absEncoder, ‹self.true_var = none›]
        simp only [Tseitin.constant, htvnone, hfresh]
        simp [absEncoder, absClauses, l_post, v_post, y_post, hcl,
          Array.to_slice, Array.make]
      · /- `value = false`: its negative literal, same gate and same clause. -/
        have htvnone : (absEncoder self).trueVar = none := by
          simp [absEncoder, ‹self.true_var = none›]
        simp only [Tseitin.constant, htvnone, hfresh]
        simp [absEncoder, absClauses, l_post, l1_post, v_post, y_post, hcl,
          Array.to_slice, Array.make]
    · simp only at r_post
      obtain ⟨hfresh, hself⟩ := r_post
      /- The `Err` path desugars to `from_residual` through the blanket `From T T`
         instance, which is the identity; unfold the projection so `step*` can see it. -/
      simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket, core.convert.From.Blanket.from]
      step*
      · /- `fresh` failed, so `constant` fails too. -/
        have htvnone : (absEncoder self).trueVar = none := by
          simp [absEncoder, ‹self.true_var = none›]
        simp only [Tseitin.constant, htvnone, hfresh]
  · /- `true_var` already set: no clause emitted, state unchanged. -/
    rename_i hsome hval
    simp [Tseitin.constant, absEncoder, hsome, l_post]
  · rename_i hsome hval
    simp [Tseitin.constant, absEncoder, hsome, l_post]

/-! ### The encoder proper

Structural induction on the expression. Each `?` in the Rust becomes a `cases` on the
`Result` plus a `Try.branch` reduction; each `vec![..]` literal becomes the
`into_vec`/`Dummy.into_vec`/`seq_from_boxed_slice`/`from_seq` unfolding chain that
`Cnf.lean` already needed. The `hlen` precondition is the linear clause bound from
`Tseitin.encode_clauses_length_le`, and it is what discharges every `Vec::push`
overflow side condition. -/

/- `Conj` and `Disj` share one proof script (they differ only in the clauses they
emit), as do the `Ok`/`Err` and iterator branches. Lean's linters flag the simp
arguments and alternatives that a given instantiation does not use; the other one
uses them. -/
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
@[step]
theorem cnf_transform_tseitin.Encoder.encode.spec (self : cnf_transform_tseitin.Encoder)
    (expr1 : expr.Expr)
    (hlen : self.clauses.val.length + 3 * exprSize expr1 ≤ Usize.max) :
    cnf_transform_tseitin.Encoder.encode self expr1
    ⦃ (r : core.result.Result cnf.Literal Unit) (enc : cnf_transform_tseitin.Encoder) =>
      match r with
      | core.result.Result.Ok l =>
        Tseitin.encode (absEncoder self) expr1 = some (l, absEncoder enc)
      | core.result.Result.Err _ =>
        Tseitin.encode (absEncoder self) expr1 = none ⦄ := by
  induction expr1 generalizing self with
  | True =>
    unfold cnf_transform_tseitin.Encoder.encode
    step*
    · simp only [exprSize] at hlen; grind
    · simp only [Tseitin.encode]; exact r_post
  | False =>
    unfold cnf_transform_tseitin.Encoder.encode
    step*
    · simp only [exprSize] at hlen; grind
    · simp only [Tseitin.encode]; exact r_post
  | Variable v =>
    unfold cnf_transform_tseitin.Encoder.encode
    step*
    simp [Tseitin.encode, l_post]
  | Neg e ih =>
    unfold cnf_transform_tseitin.Encoder.encode
    step*
    · simp only [exprSize] at hlen; grind
    · cases r
      · /- `Ok`: flip the operand's literal; no gate, no clause. -/
        simp only at r_post
        simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
        step*
        simp [Tseitin.encode, r_post, l_post]
      · /- `Err`: propagate it unchanged. -/
        simp only at r_post
        simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
          core.convert.From.Blanket, core.convert.From.Blanket.from]
        step*
        simp [Tseitin.encode, r_post]
  | Conj e1 e2 ih1 ih2 =>
    unfold cnf_transform_tseitin.Encoder.encode
    step*
    · simp only [exprSize] at hlen; grind
    · cases r
      · /- `e1` encoded; recurse on `e2`. -/
        simp only at r_post
        simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
        have hb1 : self1.clauses.val.length ≤ self.clauses.val.length + 3 * exprSize e1 := by
          simpa using Tseitin.encode_clauses_length_le r_post
        step*
        · simp only [exprSize] at hlen; grind
        · cases r1
          · /- `e2` encoded; allocate the gate. -/
            simp only at r1_post
            simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
            have hb2 : self2.clauses.val.length ≤ self1.clauses.val.length + 3 * exprSize e2 := by
              simpa using Tseitin.encode_clauses_length_le r1_post
            step*
            · cases r2
              · /- Gate allocated: emit the three defining clauses. -/
                rename_i g
                simp only at r2_post
                obtain ⟨hfresh, htv3, hcl3⟩ := r2_post
                have hpush : self2.clauses.val.length + 3 ≤ Usize.max := by
                  simp only [exprSize] at hlen; grind
                simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch, hcl3]
                unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
                  rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
                step*
                · /- `Vec::push` overflow side conditions, all from `hpush`. -/
                  grind
                · grind
                · /- The three emitted clauses are exactly the model's. -/
                  simp only [Tseitin.encode, r_post, r1_post, hfresh]
                  simp [absEncoder, absClauses, l_post, l1_post, l2_post, l3_post,
                    l4_post, l5_post, y_post, y1_post, y2_post, v_post, v1_post,
                    v2_post, hcl3, Array.to_slice, Array.make]
              · /- `fresh` failed, so the whole encode does. -/
                simp only at r2_post
                obtain ⟨hfresh, hself3⟩ := r2_post
                simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
                  core.convert.From.Blanket, core.convert.From.Blanket.from]
                step*
                simp [Tseitin.encode, r_post, r1_post, hfresh]
          · /- `e2` failed. -/
            simp only at r1_post
            simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
              core.convert.From.Blanket, core.convert.From.Blanket.from]
            step*
            simp [Tseitin.encode, r_post, r1_post]
      · /- `e1` failed. -/
        simp only at r_post
        simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
          core.convert.From.Blanket, core.convert.From.Blanket.from]
        step*
        simp [Tseitin.encode, r_post]
  | Disj e1 e2 ih1 ih2 =>
    unfold cnf_transform_tseitin.Encoder.encode
    step*
    · simp only [exprSize] at hlen; grind
    · cases r
      · /- `e1` encoded; recurse on `e2`. -/
        simp only at r_post
        simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
        have hb1 : self1.clauses.val.length ≤ self.clauses.val.length + 3 * exprSize e1 := by
          simpa using Tseitin.encode_clauses_length_le r_post
        step*
        · simp only [exprSize] at hlen; grind
        · cases r1
          · /- `e2` encoded; allocate the gate. -/
            simp only at r1_post
            simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
            have hb2 : self2.clauses.val.length ≤ self1.clauses.val.length + 3 * exprSize e2 := by
              simpa using Tseitin.encode_clauses_length_le r1_post
            step*
            · cases r2
              · /- Gate allocated: emit the three defining clauses. -/
                rename_i g
                simp only at r2_post
                obtain ⟨hfresh, htv3, hcl3⟩ := r2_post
                have hpush : self2.clauses.val.length + 3 ≤ Usize.max := by
                  simp only [exprSize] at hlen; grind
                simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch, hcl3]
                unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
                  rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
                step*
                · /- `Vec::push` overflow side conditions, all from `hpush`. -/
                  grind
                · grind
                · /- The three emitted clauses are exactly the model's. -/
                  simp only [Tseitin.encode, r_post, r1_post, hfresh]
                  simp [absEncoder, absClauses, l_post, l1_post, l2_post, l3_post,
                    l4_post, l5_post, y_post, y1_post, y2_post, v_post, v1_post,
                    v2_post, hcl3, Array.to_slice, Array.make]
              · /- `fresh` failed, so the whole encode does. -/
                simp only at r2_post
                obtain ⟨hfresh, hself3⟩ := r2_post
                simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
                  core.convert.From.Blanket, core.convert.From.Blanket.from]
                step*
                simp [Tseitin.encode, r_post, r1_post, hfresh]
          · /- `e2` failed. -/
            simp only at r1_post
            simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
              core.convert.From.Blanket, core.convert.From.Blanket.from]
            step*
            simp [Tseitin.encode, r_post, r1_post]
      · /- `e1` failed. -/
        simp only at r_post
        simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
          core.convert.From.Blanket, core.convert.From.Blanket.from]
        step*
        simp [Tseitin.encode, r_post]


/-! ### Placing the first gate above the input

`Encoder::new` folds a running maximum over `collect_vars`. The spec asks only for the
*bound* it establishes, not for the exact value: `collect_vars` returns a deduplicated
list in unspecified order, so an exact-value postcondition would have to argue that the
fold is permutation-invariant. The bound is all the correctness proofs consume. -/

/- `Conj` and `Disj` share one proof script (they differ only in the clauses they
emit), as do the `Ok`/`Err` and iterator branches. Lean's linters flag the simp
arguments and alternatives that a given instantiation does not use; the other one
uses them. -/
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
@[step]
theorem cnf_transform_tseitin.Encoder.new_loop.spec
    (iter : alloc.vec.into_iter.IntoIter Std.U16) (next : Std.U32) :
    cnf_transform_tseitin.Encoder.new_loop iter next ⦃ (r : Std.U32) =>
      next.val ≤ r.val ∧ ∀ v ∈ iter.val, v.val < r.val ⦄ := by
  unfold cnf_transform_tseitin.Encoder.new_loop
  step*
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all <;> scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all <;> scalar_tac
  · obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all <;> scalar_tac
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
theorem cnf_transform_tseitin.Encoder.new.spec (e : expr.Expr)
    (hbound : exprSize e ≤ Usize.max) :
    cnf_transform_tseitin.Encoder.new e ⦃ (enc : cnf_transform_tseitin.Encoder) =>
      enc.clauses.val = [] ∧ enc.true_var = core.option.Option.None ∧
        ∀ k ∈ varsOf e, k.val < enc.next.val ⦄ := by
  unfold cnf_transform_tseitin.Encoder.new
    alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
  step*


/-! ### The transformation as a whole

`to_cnf` runs `Encoder::new`, encodes, and asserts the root literal. Everything the
correctness proofs need about the starting state is what `Encoder.new.spec` gives:
clauses empty, no constant gate, counter above every variable of `e`. -/

/- `Conj` and `Disj` share one proof script (they differ only in the clauses they
emit), as do the `Ok`/`Err` and iterator branches. Lean's linters flag the simp
arguments and alternatives that a given instantiation does not use; the other one
uses them. -/
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
@[step]
theorem cnf_transform_tseitin.to_cnf.spec (e : expr.Expr)
    (hbound : 3 * exprSize e + 1 ≤ Usize.max) :
    cnf_transform_tseitin.to_cnf e ⦃ (r : core.result.Result cnf.Cnf Unit) =>
      match r with
      | core.result.Result.Ok c =>
        ∃ s s' root, Tseitin.State.Pinned s ∧ Tseitin.State.Wf s ∧
          (∀ k ∈ varsOf e, k.val < s.next) ∧ s.clauses = [] ∧
          Tseitin.encode s e = some (root, s') ∧
          absClauses c = s'.clauses ++ [[root]]
      | core.result.Result.Err _ => True ⦄ := by
  unfold cnf_transform_tseitin.to_cnf
  step*
  · cases r
    · /- Encoded: assert the root literal as a unit clause. -/
      rename_i root
      simp only at r_post
      have hpin : Tseitin.State.Pinned (absEncoder encoder) := by
        intro v hv; simp [absEncoder, encoder_post2] at hv
      have hb : encoder1.clauses.val.length ≤ 3 * exprSize e := by
        have hle := Tseitin.encode_clauses_length_le r_post
        simp only [absEncoder_clauses, absClauses_length, encoder_post1] at hle
        simpa using hle
      simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
      unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
        rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
      step*
      · refine ⟨absEncoder encoder, absEncoder encoder1, root, hpin, ⟨hpin, ?_, ?_⟩,
          ?_, ?_, r_post, ?_⟩
        · intro k hk; simp [absEncoder, absClauses, cnfVars, encoder_post1] at hk
        · intro v hv; simp [absEncoder, encoder_post2] at hv
        · simpa using encoder_post3
        · simp [absEncoder, absClauses, encoder_post1]
        · simp [absClauses, v_post, y_post, Array.to_slice, Array.make]
    · /- The encoder ran out of variable space; nothing to say. -/
      simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket, core.convert.From.Blanket.from]
      step*


/-! ### Correctness of the extracted transformation

These are the statements `Tseitin.lean` proves about the model, transported across the
extraction: they mention `cnf_transform_tseitin.to_cnf`, the function hax generated from
`src/cnf_transform_tseitin.rs`, and nothing else. -/

/-- **Soundness**: every model of the CNF that the extracted `to_cnf` returns satisfies
    `e`. The gate variables `w` also assigns are never consulted -- `evalPure` reads
    only `e`'s own. -/
theorem cnf_transform_tseitin.to_cnf.sound (e : expr.Expr) (w : Std.U16 → Bool)
    (hbound : 3 * exprSize e + 1 ≤ Usize.max) :
    cnf_transform_tseitin.to_cnf e ⦃ (r : core.result.Result cnf.Cnf Unit) =>
      ∀ c, r = core.result.Result.Ok c →
        Cnf.eval w (absClauses c) = true → evalPure w e = true ⦄ := by
  step*
  rw [r_post2] at r_post1
  simp only at r_post1
  obtain ⟨s, s', root, hpin, hwf, hvars, hcl, henc, habs⟩ := r_post1
  rw [habs, Cnf.eval_append] at r_post3
  obtain ⟨hbody, hroot⟩ := Bool.and_eq_true _ _ |>.mp r_post3
  have hsound := Tseitin.encode_sound hpin henc hbody
  simp only [Cnf.eval, List.all_cons, List.all_nil, Bool.and_true, Clause.eval,
    List.any_cons, List.any_nil, Bool.or_false] at hroot
  rw [← hsound]; exact hroot

/-- **Completeness**: every model of `e` extends to a model of the CNF that the
    extracted `to_cnf` returns, agreeing with it on all of `e`'s own variables. -/
theorem cnf_transform_tseitin.to_cnf.complete (e : expr.Expr) (w : Std.U16 → Bool)
    (hbound : 3 * exprSize e + 1 ≤ Usize.max) (hsat : evalPure w e = true) :
    cnf_transform_tseitin.to_cnf e ⦃ (r : core.result.Result cnf.Cnf Unit) =>
      ∀ c, r = core.result.Result.Ok c →
        ∃ w', (∀ k ∈ varsOf e, w' k = w k) ∧ Cnf.eval w' (absClauses c) = true ⦄ := by
  step*
  rw [r_post2] at r_post1
  simp only at r_post1
  obtain ⟨s, s', root, hpin, hwf, hvars, hcl, henc, habs⟩ := r_post1
  obtain ⟨w', hag, hev⟩ :=
    Tseitin.encode_complete hwf hvars henc w (by rw [hcl]; simp [Cnf.eval])
  have hagree : ∀ k ∈ varsOf e, w' k = w k := fun k hk => hag k (hvars k hk)
  refine ⟨w', hagree, ?_⟩
  rw [habs, Cnf.eval_append]
  refine Bool.and_eq_true _ _ |>.mpr ⟨hev, ?_⟩
  have hsound := Tseitin.encode_sound hpin henc hev
  simp only [Cnf.eval, List.all_cons, List.all_nil, Bool.and_true, Clause.eval,
    List.any_cons, List.any_nil, Bool.or_false]
  rw [hsound, evalPure_congr e hagree, hsat]


end sat_solver
