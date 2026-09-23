/- Pure reference semantics for `expr::collect_vars`, and the spec connecting it to
the extracted `expr.collect_vars`. -/
import SatSolver.Extraction
import SatSolver.Verification.Prelude

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

/-- The set of variables occurring in `e` (as a list; duplicates/order don't
    matter, only membership is ever used). -/
def varsOf : expr.Expr → List Std.U16
  | .True => []
  | .False => []
  | .Variable v => [v]
  | .Conj e1 e2 => varsOf e1 ++ varsOf e2
  | .Disj e1 e2 => varsOf e1 ++ varsOf e2
  | .Neg e => varsOf e

/-- Structural size of `e` (number of AST nodes), used only to bound
    `Vec`/`Usize.max` overflow side-conditions in `collect_vars`'s proof. -/
def exprSize : expr.Expr → Nat
  | .True => 1
  | .False => 1
  | .Variable _ => 1
  | .Conj e1 e2 => exprSize e1 + exprSize e2 + 1
  | .Disj e1 e2 => exprSize e1 + exprSize e2 + 1
  | .Neg e => exprSize e + 1

/-- **Spec theorem for `sat_solver::expr::contains_var`'s loop.** -/
@[step]
theorem expr.contains_var_loop.spec (iter : core.slice.iter.Iter Std.U16) (v : Std.U16) :
    expr.contains_var_loop iter v ⦃ (b : Bool) => b = true ↔ v ∈ iter.val ⦄ := by
  unfold expr.contains_var_loop
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

/-- **Spec theorem for `sat_solver::expr::contains_var`** -/
@[step]
theorem expr.contains_var.spec (vars : Slice Std.U16) (v : Std.U16) :
    expr.contains_var vars v ⦃ (b : Bool) => b = true ↔ v ∈ vars.val ⦄ := by
  unfold expr.contains_var
  step*

/-- **Spec theorem for `sat_solver::expr::merge_vars`'s loop.**
`dst`'s length never grows beyond `dst.length + iter.length` (it only grows on a
genuinely new key), so that sum bounds `Vec.push`'s `Usize.max` side-condition
throughout the recursion. -/
@[step]
theorem expr.merge_vars_loop.spec (iter : core.slice.iter.Iter Std.U16)
    (dst : alloc.vec.Vec Std.U16) (hlen : dst.val.length + iter.val.length ≤ Usize.max)
    (hnodup : dst.val.Nodup) :
    expr.merge_vars_loop iter dst ⦃ (result : alloc.vec.Vec Std.U16) =>
      (∀ k, k ∈ result.val ↔ k ∈ dst.val ∨ k ∈ iter.val) ∧
      result.val.length ≤ dst.val.length + iter.val.length ∧
      result.val.Nodup ⦄ := by
  unfold expr.merge_vars_loop
  step*
  · -- o = none: final result
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
  · -- hlen for the skip-branch recursive call
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · -- skip branch: final result
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      rename_i b_post
      refine ⟨?_, ?_, ?_⟩
      · simp_all
        intro k
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inl (h ▸ b_post)
          · exact Or.inr h
      · simp_all; scalar_tac
      · simp_all
  · -- hlen for the final push (o = none inside is unreachable here; this is
    -- the "not found" push precondition dst.length < Usize.max)
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · -- hlen for the push+recurse recursive call
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => scalar_tac
  · -- Nodup for the push+recurse recursive call
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      rename_i b_post
      simp_all [List.nodup_append]
      intro a ha he
      exact b_post (by rw [show a = e from by scalar_tac] at ha; exact ha)
  · -- push+recurse: final result
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      rename_i b_post
      refine ⟨?_, ?_, ?_⟩
      · simp_all; tauto
      · simp_all; scalar_tac
      · simp_all
termination_by iter.val.length
decreasing_by
  all_goals (obtain ⟨l, hl⟩ := iter; cases l with
    | nil => simp_all
    | cons e es => simp_all)

/-- **Spec theorem for `sat_solver::expr::merge_vars`** -/
@[step]
theorem expr.merge_vars.spec (dst : alloc.vec.Vec Std.U16) (src : Slice Std.U16)
    (hlen : dst.val.length + src.val.length ≤ Usize.max) (hnodup : dst.val.Nodup) :
    expr.merge_vars dst src ⦃ (result : alloc.vec.Vec Std.U16) =>
      (∀ k, k ∈ result.val ↔ k ∈ dst.val ∨ k ∈ src.val) ∧
      result.val.length ≤ dst.val.length + src.val.length ∧
      result.val.Nodup ⦄ := by
  unfold expr.merge_vars
  step*

/-- **Spec theorem for `sat_solver::expr::collect_vars_aux`**
`vs.val.length ≤ exprSize e` is carried along purely to discharge `merge_vars`'s
`Usize.max` side-condition in the `Conj`/`Disj` cases -- it isn't otherwise
meaningful (the real bound, after dedup, is `≤ 65536`, but this coarser one is
enough and needs no extra machinery). -/
@[step]
theorem expr.collect_vars_aux.spec (e : expr.Expr) (hbound : exprSize e ≤ Usize.max) :
    expr.collect_vars_aux e ⦃ (vs : alloc.vec.Vec Std.U16) =>
      (∀ k, k ∈ vs.val ↔ k ∈ varsOf e) ∧ vs.val.length ≤ exprSize e ∧ vs.val.Nodup ⦄ := by
  induction e with
  | True => unfold expr.collect_vars_aux; step*; simp_all [varsOf, exprSize]
  | False => unfold expr.collect_vars_aux; step*; simp_all [varsOf, exprSize]
  | Variable v => unfold expr.collect_vars_aux; step*; simp_all [varsOf, exprSize]
  | Conj e1 e2 ih1 ih2 =>
    unfold expr.collect_vars_aux
    replace ih1 := ih1 (by simp only [exprSize] at hbound; scalar_tac)
    replace ih2 := ih2 (by simp only [exprSize] at hbound; scalar_tac)
    step*
    · simp only [exprSize] at hbound; scalar_tac
    · refine ⟨?_, ?_, ?_⟩
      · simp_all [varsOf, exprSize]
      · simp_all [exprSize]; scalar_tac
      · simp_all
  | Disj e1 e2 ih1 ih2 =>
    unfold expr.collect_vars_aux
    replace ih1 := ih1 (by simp only [exprSize] at hbound; scalar_tac)
    replace ih2 := ih2 (by simp only [exprSize] at hbound; scalar_tac)
    step*
    · simp only [exprSize] at hbound; scalar_tac
    · refine ⟨?_, ?_, ?_⟩
      · simp_all [varsOf, exprSize]
      · simp_all [exprSize]; scalar_tac
      · simp_all
  | Neg e ih =>
    unfold expr.collect_vars_aux
    replace ih := ih (by simp only [exprSize] at hbound; scalar_tac)
    step*
    simp_all [varsOf, exprSize]
    scalar_tac

/-- **Spec theorem for `sat_solver::expr::collect_vars`**
The returned vector contains exactly the variables of `e` (as a set), with no
duplicates. -/
@[step]
theorem expr.collect_vars.spec (e : expr.Expr) (hbound : exprSize e ≤ Usize.max) :
    expr.collect_vars e ⦃ (vs : alloc.vec.Vec Std.U16) =>
      (∀ k, k ∈ vs.val ↔ k ∈ varsOf e) ∧ vs.val.Nodup ∧ vs.val.length ≤ exprSize e ⦄ := by
  unfold expr.collect_vars
  step*

end sat_solver
