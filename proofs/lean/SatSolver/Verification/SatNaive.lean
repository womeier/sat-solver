/- Soundness + completeness for `sat_naive::solve_sat` (recursive backtracking
search that threads one mutable `Map` through the recursion). -/
import SatSolver.Extraction
import SatSolver.Verification.MapLemmas
import SatSolver.Verification.Semantics
import SatSolver.Verification.CollectVars

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

/-- Loop invariant for `check_possible_valuations`, generalized over an arbitrary
    accumulator `val0` and the total valuation `w0` it represents *outside* `vars`.

    **Non-obvious subtlety** (see `PLAN.md`): the same `Map` is reused/mutated across
    the false- and true-branch recursive calls, so on entering the true branch, keys
    in `vars` may hold stale leftovers from the failed false branch. The invariant
    therefore says nothing about `val0`'s content *on* `vars` — only outside it.

    `vars.val` is required to be a `Nodup` subset of `varsOf e` (true at every call
    site: the top level calls with `vars = collect_vars e`, and the recursive calls
    only ever shrink `vars` by dropping its head) -- needed so the induction can tell
    a freshly-branched-on variable apart from ones handled at outer recursion levels. -/
@[step]
theorem sat_naive.check_possible_valuations.spec
    (e : expr.Expr) (vars : Slice Std.U16) (val0 : expr.Map) (w0 : Std.U16 → Bool)
    (hsub : ∀ k ∈ vars.val, k ∈ varsOf e) (hnodup : vars.val.Nodup)
    (hlen : (∀ k ∈ vars.val, Map.lookupList val0.val k ≠ none) ∨
      val0.val.length + vars.val.length < Usize.max)
    (hagree : ∀ k, k ∈ varsOf e → k ∉ vars.val → Map.lookupList val0.val k = some (w0 k)) :
    sat_naive.check_possible_valuations e vars val0 ⦃ (b : Bool) (val1 : expr.Map) =>
      -- val1 is unchanged outside `vars`, regardless of the outcome
      (∀ k, k ∈ varsOf e → k ∉ vars.val → Map.lookupList val1.val k = some (w0 k)) ∧
      -- every variable in `vars` has been visited (inserted at least once) by the
      -- time the call returns, regardless of the outcome -- this is what lets a
      -- second insert/recursive-call of the *same* keys at an outer level avoid
      -- needing fresh `Usize.max` growth room (it's known to be a pure overwrite)
      (∀ k ∈ vars.val, Map.lookupList val1.val k ≠ none) ∧
      -- soundness: a `true` result comes with an actual satisfying valuation, and
      -- val1 *is* that valuation on `vars` (val1 is the witness returned by solve_sat)
      (b = true → ∃ w : Std.U16 → Bool,
        (∀ k, k ∈ varsOf e → k ∉ vars.val → w k = w0 k) ∧
        (∀ k ∈ vars.val, Map.lookupList val1.val k = some (w k)) ∧
        evalPure w e = true) ∧
      -- completeness: if some valuation extending w0 satisfies e, a `true` result
      -- is found
      ((∃ w : Std.U16 → Bool,
          (∀ k, k ∈ varsOf e → k ∉ vars.val → w k = w0 k) ∧ evalPure w e = true) →
        b = true) ⦄ := by
  unfold sat_naive.check_possible_valuations
  step*
  · -- witness for evaluate.spec_of_represents in the base (vars = []) case
    exact w0
  · -- witness for the recursive call's own w0 parameter: w0 updated at the
    -- branch variable to `false`
    exact fun k => if k = vars.val[0]'v then false else w0 k
  · -- hrepr: val0 represents w0 on all of varsOf e, since vars.val = []
    intro k hk
    exact hagree k hk (by simp_all)
  · -- base case final result
    unfold core.result.Result.unwrap
    simp only [r_post]
    refine ⟨hagree, by simp_all, ?_, ?_⟩
    · intro hb
      exact ⟨w0, fun k _ _ => rfl, fun k hk => absurd hk (by simp_all), hb⟩
    · intro x hx1 hx2
      have : evalPure w0 e = evalPure x e := evalPure_congr e (fun k hk => (hx1 k hk (by simp_all)).symm)
      rw [← this] at hx2
      exact hx2
  · -- h_fail: vars is nonempty
    obtain ⟨l, hl⟩ := vars
    cases l with
    | nil => simp_all
    | cons e es => simp_all
  · -- hlen precondition for the first insert (val0.insert vars[0] false):
    -- either vars[0] is already present in val0 (no growth room needed), or
    -- there's genuine growth room since val0.length + vars.length < Usize.max
    rcases hlen with hpresent | hlen'
    · left
      apply hpresent
      rw [v_post2]
      exact List.getElem_mem v
    · right
      scalar_tac
  · -- hsub for the recursive call
    intro k hk
    apply hsub
    rw [vs_post] at hk
    exact List.mem_of_mem_tail hk
  · -- hnodup for the recursive call
    obtain ⟨l, hl⟩ := vars
    cases l with
    | nil => simp_all
    | cons e es =>
      rw [vs_post]
      simp_all
  · -- hlen for the recursive call (val1, vs)
    obtain ⟨l, hl⟩ := vars
    cases l with
    | nil => simp_all
    | cons e es =>
      rw [vs_post]
      rcases hlen with hpresent | hlen'
      · left
        intro k hk
        rw [__post2, v_post2]
        simp only [List.getElem_cons_zero]
        have hke : k ≠ e := fun hc => (List.nodup_cons.mp hnodup).1 (hc ▸ hk)
        rw [Map.lookupList_upsertList_other _ _ _ _ hke]
        exact hpresent k (List.mem_cons_of_mem e hk)
      · right
        rw [__post2]
        simp only [Map.upsertList_length, List.tail_cons]
        split_ifs <;> scalar_tac
  · -- hagree for the recursive call
    rw [v_post2] at __post2
    intro k hk hknotin
    by_cases hkx : k = vars.val[0]'v
    · rw [hkx, if_pos rfl, __post2]
      exact Map.lookupList_upsertList_self _ _ _
    · rw [if_neg hkx, __post2, Map.lookupList_upsertList_other _ _ _ _ hkx]
      apply hagree k hk
      rw [vs_post] at hknotin
      obtain ⟨l, hl⟩ := vars
      cases l with
      | nil => simp_all
      | cons e es =>
        simp only [List.getElem_cons_zero] at hkx
        simp only [List.mem_cons]
        rintro (rfl | hcontra)
        · exact hkx rfl
        · exact hknotin hcontra
  · -- final assembly using the recursive result b1/val2
    obtain ⟨l, hl⟩ := vars
    cases l with
    | nil => simp_all
    | cons e es =>
      simp only [List.getElem_cons_zero] at v_post2
      by_cases hb1 : b1 = true
      · simp only [if_pos hb1]
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- frame: val2 unchanged outside vars, matches w0
          intro k hk hknotin
          have hkne : k ≠ e := fun hc => hknotin (by simp [hc])
          have hknotes : k ∉ es := fun hc => hknotin (by simp [hc])
          rw [b1_post1 k hk (by rw [vs_post]; exact hknotes)]
          simp [hkne]
        · -- hpresent: every var in e :: es has been visited
          intro k hk
          simp only [List.mem_cons] at hk
          rcases hk with rfl | hk
          · rw [b1_post1 k (hsub k (by simp)) (by rw [vs_post]; exact (List.nodup_cons.mp hnodup).1)]
            simp
          · exact b1_post2 k (by rw [vs_post]; exact hk)
        · -- soundness: witness from the recursive call, bridged back to w0
          intro _
          obtain ⟨w, hw1, hw2, hw3⟩ := b1_post3 hb1
          refine ⟨w, ?_, ?_, hw3⟩
          · intro k hk hknotin
            have hkne : k ≠ e := fun hc => hknotin (by simp [hc])
            have hknotes : k ∉ es := fun hc => hknotin (by simp [hc])
            rw [hw1 k hk (by rw [vs_post]; exact hknotes)]
            simp [hkne]
          · intro k hk
            simp only [List.mem_cons] at hk
            rcases hk with rfl | hk
            · have hke := hsub k (by simp)
              have hknotes : k ∉ es := (List.nodup_cons.mp hnodup).1
              rw [b1_post1 k hke (by rw [vs_post]; exact hknotes),
                  hw1 k hke (by rw [vs_post]; exact hknotes)]
            · apply hw2
              rw [vs_post]
              exact hk
        · intros
          rfl
      · simp only [if_neg hb1]
        step*
        · -- witness for the second recursive call's own w0 parameter: w0 updated
          -- at the branch variable to `true`
          exact fun k => if k = e then true else w0 k
        · -- hlen precondition for the second insert (val2.insert e true): e is
          -- already present in val2 (frame, since e ∉ vs), no growth needed
          left
          rw [v_post2, b1_post1 e (hsub e (by simp)) (by rw [vs_post]; exact (List.nodup_cons.mp hnodup).1)]
          simp
        · -- hsub for the second recursive call
          intro k hk
          apply hsub
          rw [vs_post] at hk
          exact List.mem_of_mem_tail hk
        · -- hnodup for the second recursive call
          rw [vs_post]
          simp_all
        · -- hlen for the second recursive call (val3, vs): every key in vs is
          -- already present in val3 (it was already present in val2, from
          -- `b1_post2`, and the second insert only touches e ∉ vs)
          left
          intro k hk
          have hk' : k ∈ es := by rw [vs_post] at hk; exact hk
          have hke : k ≠ e := fun hc => (List.nodup_cons.mp hnodup).1 (hc ▸ hk')
          rw [__post2, v_post2, Map.lookupList_upsertList_other _ _ _ _ hke]
          exact b1_post2 k hk
        · -- hagree for the second recursive call
          rw [v_post2] at __post2
          intro k hk hknotin
          by_cases hkx : k = e
          · rw [hkx, if_pos rfl, __post2]
            exact Map.lookupList_upsertList_self _ _ _
          · rw [if_neg hkx, __post2, Map.lookupList_upsertList_other _ _ _ _ hkx,
                b1_post1 k hk hknotin]
            simp [hkx]
        · -- final assembly using the second recursive result b2/val4
          by_cases hb2 : b2 = true
          · simp only [if_pos hb2]
            refine ⟨?_, ?_, ?_, ?_⟩
            · -- frame: val4 unchanged outside vars, matches w0
              intro k hk hknotin
              have hkne : k ≠ e := fun hc => hknotin (by simp [hc])
              have hknotes : k ∉ es := fun hc => hknotin (by simp [hc])
              rw [b2_post1 k hk (by rw [vs_post]; exact hknotes)]
              simp [hkne]
            · -- hpresent: every var in e :: es has been visited
              intro k hk
              simp only [List.mem_cons] at hk
              rcases hk with rfl | hk
              · rw [b2_post1 k (hsub k (by simp)) (by rw [vs_post]; exact (List.nodup_cons.mp hnodup).1)]
                simp
              · exact b2_post2 k (by rw [vs_post]; exact hk)
            · -- soundness: witness from the second recursive call
              intro _
              obtain ⟨w, hw1, hw2, hw3⟩ := b2_post3 hb2
              refine ⟨w, ?_, ?_, hw3⟩
              · intro k hk hknotin
                have hkne : k ≠ e := fun hc => hknotin (by simp [hc])
                have hknotes : k ∉ es := fun hc => hknotin (by simp [hc])
                rw [hw1 k hk (by rw [vs_post]; exact hknotes)]
                simp [hkne]
              · intro k hk
                simp only [List.mem_cons] at hk
                rcases hk with rfl | hk
                · have hke := hsub k (by simp)
                  have hknotes : k ∉ es := (List.nodup_cons.mp hnodup).1
                  rw [b2_post1 k hke (by rw [vs_post]; exact hknotes),
                      hw1 k hke (by rw [vs_post]; exact hknotes)]
                · apply hw2
                  rw [vs_post]
                  exact hk
            · intros
              rfl
          · simp only [if_neg hb2]
            refine ⟨?_, ?_, by simp, ?_⟩
            · -- frame: neither branch ever touches keys outside vars
              intro k hk hknotin
              have hkne : k ≠ e := fun hc => hknotin (by simp [hc])
              have hknotes : k ∉ es := fun hc => hknotin (by simp [hc])
              rw [b2_post1 k hk (by rw [vs_post]; exact hknotes)]
              simp [hkne]
            · -- hpresent: every var in e :: es has been visited
              intro k hk
              simp only [List.mem_cons] at hk
              rcases hk with rfl | hk
              · rw [b2_post1 k (hsub k (by simp)) (by rw [vs_post]; exact (List.nodup_cons.mp hnodup).1)]
                simp
              · exact b2_post2 k (by rw [vs_post]; exact hk)
            · -- completeness: if b1 and b2 both failed, no `w` extending `w0`
              -- outside `e :: es` can satisfy `e✝` -- case on `w e`, and use
              -- whichever recursive call's own completeness this contradicts
              intro w hw hsat
              by_cases hwe : w e = true
              · exact absurd (b2_post4 w (fun k hk hknotin => by
                  rw [vs_post] at hknotin
                  by_cases hke : k = e
                  · simp [hke, hwe]
                  · have hkout : k ∉ (e :: es) := fun hc => (List.mem_cons.mp hc).elim hke hknotin
                    rw [hw k hk hkout]
                    simp [hke]) hsat) hb2
              · exact absurd (b1_post4 w (fun k hk hknotin => by
                  rw [vs_post] at hknotin
                  by_cases hke : k = e
                  · simp only [hke]
                    simp_all
                  · have hkout : k ∉ (e :: es) := fun hc => (List.mem_cons.mp hc).elim hke hknotin
                    rw [hw k hk hkout]
                    simp [hke]) hsat) hb1
termination_by vars.val.length
decreasing_by
  all_goals (obtain ⟨l, hl⟩ := vars; cases l with
    | nil => simp_all
    | cons e es => (rw [vs_post]; simp))

/-- **Spec theorem for `sat_naive::initial_valuation`'s loop.**
Every key visited along the way gets set to `false`; keys never visited are left
untouched. Mirrors `check_possible_valuations.spec`'s disjunctive `hlen`: a key
that's already present needs no fresh growth room to be overwritten. -/
@[step]
theorem sat_naive.initial_valuation_loop.spec
    (iter : core.slice.iter.Iter Std.U16) (map : expr.Map)
    (hlen : (∀ k ∈ iter.val, Map.lookupList map.val k ≠ none) ∨
      map.val.length + iter.val.length < Usize.max) :
    sat_naive.initial_valuation_loop iter map ⦃ (m : expr.Map) =>
      (∀ k, k ∉ iter.val → Map.lookupList m.val k = Map.lookupList map.val k) ∧
      (∀ k ∈ iter.val, Map.lookupList m.val k = some false) ⦄ := by
  unfold sat_naive.initial_valuation_loop
  step*
  · -- o = none: final result
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es => simp_all
  · -- hlen for Map.insert (v false)
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      obtain ⟨ho, hiter1⟩ := o_post
      have hve : v = e := by simp_all
      rcases hlen with hpresent | hlen'
      · left
        rw [hve]
        exact hpresent e (by simp)
      · right
        scalar_tac
  · -- hlen for the recursive call
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      obtain ⟨ho, hiter1⟩ := o_post
      have hve : v = e := by simp_all
      rcases hlen with hpresent | hlen'
      · left
        intro k hk
        rw [hiter1] at hk
        rw [__post2, hve]
        by_cases hke : k = e
        · rw [hke, Map.lookupList_upsertList_self]
          simp
        · rw [Map.lookupList_upsertList_other _ _ _ _ hke]
          exact hpresent k (by simp [hk])
      · right
        rw [hiter1, __post2, hve]
        simp only [Map.upsertList_length]
        split_ifs <;> scalar_tac
  · -- final result
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e es =>
      obtain ⟨ho, hiter1⟩ := o_post
      have hve : v = e := by simp_all
      refine ⟨?_, ?_⟩
      · intro k hk
        simp only [List.mem_cons, not_or] at hk
        obtain ⟨hke, hknotrest⟩ := hk
        rw [m_post1 k (by rw [hiter1]; exact hknotrest), __post2, hve,
            Map.lookupList_upsertList_other _ _ _ _ hke]
      · intro k hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | hk'
        · by_cases hv : k ∈ es
          · exact m_post2 k (by rw [hiter1]; exact hv)
          · rw [m_post1 k (by rw [hiter1]; exact hv), __post2, hve]
            exact Map.lookupList_upsertList_self _ _ _
        · exact m_post2 k (by rw [hiter1]; exact hk')
termination_by iter.val.length
decreasing_by
  obtain ⟨l, hl⟩ := iter
  cases l with
  | nil => simp_all
  | cons e es => simp_all

/-- **Spec theorem for `sat_naive::initial_valuation`**
Sets every variable in `vars` to `false` in a fresh map. -/
@[step]
theorem sat_naive.initial_valuation.spec (vars : Slice Std.U16) (hlen : vars.val.length < Usize.max) :
    sat_naive.initial_valuation vars ⦃ (m : expr.Map) =>
      ∀ k ∈ vars.val, Map.lookupList m.val k = some false ⦄ := by
  unfold sat_naive.initial_valuation expr.Map.new
    core.SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
  step*

/-- **Soundness**: if `sat_naive::solve_sat` returns a valuation, it satisfies `e`. -/
theorem sat_naive.solve_sat_sound (e : expr.Expr) (hbound : exprSize e < Usize.max) :
    sat_naive.solve_sat e ⦃ (result : core.option.Option expr.Map) =>
      ∀ v, result = some v →
        expr.evaluate e v ⦃ (r : core.result.Result Bool Unit) =>
          r = core.result.Result.Ok true ⦄ ⦄ := by
  unfold sat_naive.solve_sat
  step*
  · -- witness for check_possible_valuations' own w0 parameter: irrelevant, since
    -- s.val = varsOf e as a set, so `hagree`'s premise is always vacuous
    exact fun _ => false
  · -- hlen: every key in s is already present in val (initial_valuation.spec)
    left
    intro k hk
    rw [val_post k hk]
    simp
  · -- hagree: vacuous, since k ∈ varsOf e → k ∈ s.val always
    intro k hk hknotin
    exact absurd (by rw [s_post]; exact (vars_post1 k).mpr hk) hknotin
  · by_cases hb : b = true
    · simp only [if_pos hb]
      intro v hv
      have hv' : val1 = v := by injection hv
      subst hv'
      obtain ⟨w, _, hw2, hw3⟩ := b_post3 hb
      have hrepr : Map.represents val1 (varsOf e) w := by
        intro k hk
        apply hw2
        rw [s_post]
        exact (vars_post1 k).mpr hk
      have hev := expr.evaluate.spec_of_represents e val1 w hrepr
      rwa [hw3] at hev
    · simp [hb]

/-- **Completeness**: if some total valuation `w` satisfies `e`, `sat_naive::solve_sat`
    finds a satisfying valuation. -/
theorem sat_naive.solve_sat_complete (e : expr.Expr) (w : Std.U16 → Bool)
    (hbound : exprSize e < Usize.max) (hsat : evalPure w e = true) :
    sat_naive.solve_sat e ⦃ (result : core.option.Option expr.Map) => result ≠ none ⦄ := by
  unfold sat_naive.solve_sat
  step*
  · -- witness for check_possible_valuations' own w0 parameter: the given
    -- satisfying valuation
    exact w
  · -- hlen: every key in s is already present in val (initial_valuation.spec)
    left
    intro k hk
    rw [val_post k hk]
    simp
  · -- hagree: vacuous, since k ∈ varsOf e → k ∈ s.val always
    intro k hk hknotin
    exact absurd (by rw [s_post]; exact (vars_post1 k).mpr hk) hknotin
  · have hb : b = true := b_post4 w (fun k _ _ => rfl) hsat
    simp [hb]

end sat_solver
