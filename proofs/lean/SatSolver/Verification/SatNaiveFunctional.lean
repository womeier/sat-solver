/- Soundness + completeness for `sat_naive_functional::solve_sat` (builds the full
list of all `2^n` valuations up front, then linearly scans it with `evaluate`). -/
import SatSolver.Extraction
import SatSolver.Verification.MapLemmas
import SatSolver.Verification.Semantics
import SatSolver.Verification.CollectVars

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

set_option maxHeartbeats 1000000 in
/-- Loop invariant for `naive_create_possible_valuations`'s loop, generalized over
    an arbitrary already-processed prefix `pre` of `iter`: `result` starts out
    covering every valuation witnessed by some element of `pre` (extended to `v`),
    and by the end it covers every valuation witnessed by an element of the *whole*
    original iterator (`pre ++ iter.val`). Every map ever produced only grows by
    exactly one entry per recursion level, so its size stays bounded by the
    variable-set it represents -- this is what bounds every `Vec.push`/`Map.insert`
    `Usize.max` side-condition below, with no need to reason about key presence. -/
@[step]
theorem sat_naive_functional.naive_create_possible_valuations_loop.spec
    (iter : core.slice.iter.Iter expr.Map) (v : Std.U8) (result : alloc.vec.Vec expr.Map)
    (vs : List Std.U8) (pre : List expr.Map)
    (hiter : ∀ m ∈ iter.val, (∃ w, Map.represents m vs w) ∧ m.val.length ≤ vs.length)
    (hresult : ∀ m ∈ result.val, (∃ w, Map.represents m (v :: vs) w) ∧ m.val.length ≤ vs.length + 1)
    (hcov : ∀ w : Std.U8 → Bool, (∃ m ∈ pre, Map.represents m vs w) →
      ∃ m' ∈ result.val, Map.represents m' (v :: vs) w)
    (hbound : vs.length < Usize.max)
    (hlen : result.val.length + 2 * iter.val.length ≤ Usize.max) :
    sat_naive_functional.naive_create_possible_valuations_loop iter v result ⦃
      (result' : alloc.vec.Vec expr.Map) =>
        (∀ m ∈ result'.val, (∃ w, Map.represents m (v :: vs) w) ∧ m.val.length ≤ vs.length + 1) ∧
        (∀ w : Std.U8 → Bool, (∃ m ∈ pre ++ iter.val, Map.represents m vs w) →
          ∃ m' ∈ result'.val, Map.represents m' (v :: vs) w) ∧
        result'.val.length = result.val.length + 2 * iter.val.length ⦄ := by
  unfold sat_naive_functional.naive_create_possible_valuations_loop
  step*
  · -- pre for the recursive call: extend by the just-processed e
    exact pre ++ [e]
  · -- o = none: final result
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil =>
      refine ⟨hresult, by simpa using hcov, by simp⟩
    | cons e es => simp_all
  · -- hlen for the first Map.insert (e_true.insert v true)
    have he : e ∈ iter.val := by
      obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e2 es => simp_all
    right
    rw [e_true_post]
    exact lt_of_le_of_lt (hiter e he).2 hbound
  · -- hlen for the first Vec.push (result.push e_true1)
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e2 es => scalar_tac
  · -- hlen for the second Map.insert (e_true.insert v false)
    have he : e ∈ iter.val := by
      obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e2 es => simp_all
    right
    rw [e_true_post]
    exact lt_of_le_of_lt (hiter e he).2 hbound
  · -- hlen for the second Vec.push (result1.push e_false)
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e2 es => scalar_tac
  · -- hiter for the recursive call
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e2 es =>
      obtain ⟨ho, hiter1⟩ := o_post
      intro m hm
      apply hiter m
      rw [hiter1] at hm
      exact List.mem_cons_of_mem e2 hm
  · -- hresult for the recursive call
    have he : e ∈ iter.val := by
      obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e2 es => simp_all
    obtain ⟨w0, hw0⟩ := (hiter e he).1
    have hlen0 := (hiter e he).2
    intro m hm
    rw [result2_post, result1_post] at hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | hm
    · exact hresult m hm
    · subst hm
      refine ⟨⟨fun k => if k = v then true else w0 k, ?_⟩, ?_⟩
      · intro k hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · simp_all
        · by_cases hkv : k = v
          · simp_all
          · simp only [if_neg hkv]
            have hwk := hw0 k hk
            simp_all [Map.lookupList_upsertList_other]
      · have hpost2 : (m : expr.Map).val = Map.upsertList e_true.val v true := ‹_›
        rw [hpost2, e_true_post, Map.upsertList_length]
        split_ifs
        · exact Nat.add_le_add_right hlen0 1
        · exact hlen0.trans (Nat.le_succ _)
    · subst hm
      refine ⟨⟨fun k => if k = v then false else w0 k, ?_⟩, ?_⟩
      · intro k hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · simp_all
        · by_cases hkv : k = v
          · simp_all
          · simp only [if_neg hkv]
            have hwk := hw0 k hk
            simp_all [Map.lookupList_upsertList_other]
      · have hpost2 : (m : expr.Map).val = Map.upsertList e_true.val v false := ‹_›
        rw [hpost2, e_true_post, Map.upsertList_length]
        split_ifs
        · exact Nat.add_le_add_right hlen0 1
        · exact hlen0.trans (Nat.le_succ _)
  · -- hcov for the recursive call
    intro w hw
    obtain ⟨m, hm, hrepr⟩ := hw
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · obtain ⟨m', hm', hrepr'⟩ := hcov w ⟨m, hm, hrepr⟩
      exact ⟨m', by rw [result2_post, result1_post]; simp [hm'], hrepr'⟩
    · subst hm
      by_cases hwv : w v = true
      · refine ⟨e_true1, by rw [result2_post, result1_post]; simp, ?_⟩
        intro k hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · simp_all
        · by_cases hkv : k = v
          · simp_all
          · have hpost2 : (e_true1 : expr.Map).val = Map.upsertList e_true.val v true := ‹_›
            rw [hpost2, Map.lookupList_upsertList_other _ _ _ _ hkv, e_true_post]
            exact hrepr k hk
      · refine ⟨e_false, by rw [result2_post]; simp, ?_⟩
        have hwvf : w v = false := by
          cases hv : w v <;> simp_all
        intro k hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · simp_all
        · by_cases hkv : k = v
          · simp_all
          · have hpost2 : (e_false : expr.Map).val = Map.upsertList e_true.val v false := ‹_›
            rw [hpost2, Map.lookupList_upsertList_other _ _ _ _ hkv, e_true_post]
            exact hrepr k hk
  · -- hlen for the recursive call
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e2 es => scalar_tac
  · -- final result: assemble from the recursive result
    obtain ⟨l, hl⟩ := iter
    cases l with
    | nil => simp_all
    | cons e2 es =>
      obtain ⟨ho, hiter1⟩ := o_post
      have he2 : e2 = e := by simp_all
      refine ⟨result'_post1, ?_, ?_⟩
      · intro w x hx hxrepr
        have heq : pre ++ [e] ++ iter1.val = pre ++ (e2 :: es) := by
          rw [hiter1, ← he2, List.append_assoc]
          simp
        exact result'_post2 w x (by rw [heq]; exact hx) hxrepr
      · rw [result'_post3, result2_post, result1_post, hiter1]
        simp only [List.length_append, List.length_cons, List.length_nil]
        scalar_tac
termination_by iter.val.length
decreasing_by
  rcases hiv : (iter.val : List expr.Map) with _ | ⟨e2, es2⟩
  · rw [hiv] at o_post
    have h2 : _ = some e := ‹_›
    rw [o_post.1] at h2
    exact absurd h2 (by simp)
  · rw [hiv] at o_post
    rw [o_post.2]
    simp

set_option maxHeartbeats 1000000 in
/-- **Exhaustiveness**: `naive_create_possible_valuations` builds every possible
    total-on-`vars` valuation (as a set — order/multiplicity don't matter, only
    that *some* matching map is present for every `w`); every map it produces is
    no larger than `vars` (needed to bound `Usize.max` side-conditions); and it
    produces *exactly* `2 ^ vars.length` maps -- this algorithm is genuinely
    exponential, so `2 ^ vars.length ≤ Usize.max` is the real headroom hypothesis
    needed throughout, not just `vars.length ≤ Usize.max`. -/
@[step]
theorem sat_naive_functional.naive_create_possible_valuations.spec
    (vars : Slice Std.U8) (hbound : 2 ^ vars.val.length ≤ Usize.max) :
    sat_naive_functional.naive_create_possible_valuations vars ⦃
      (result : alloc.vec.Vec expr.Map) =>
        (∀ w : Std.U8 → Bool, ∃ m ∈ result.val, Map.represents m vars.val w) ∧
        (∀ m ∈ result.val, (∃ w, Map.represents m vars.val w) ∧ m.val.length ≤ vars.val.length) ∧
        result.val.length = 2 ^ vars.val.length ⦄ := by
  unfold sat_naive_functional.naive_create_possible_valuations
  step*
  · -- vs for the loop call: the loop needs vs.val, since that's what the
    -- recursive `rest` was built over
    exact vs.val
  · -- pre for the loop call: nothing processed yet
    exact []
  · -- base case (vars = []): the single empty map represents everything vacuously
    unfold expr.Map.new
    step*
    have hres : (result : alloc.vec.Vec expr.Map).val = [x] := by
      rw [result_post, base_post]; simp
    have hv : vars.val = [] := b_post.mp ‹b = true›
    rw [hv]
    refine ⟨?_, ?_, ?_⟩
    · intro w
      refine ⟨(x : expr.Map), ?_, ?_⟩
      · rw [hres]; simp
      · intro k hk; exact absurd hk (by simp)
    · intro m hm
      rw [hres] at hm
      simp only [List.mem_singleton] at hm
      rw [hm]
      refine ⟨⟨fun _ => false, ?_⟩, ?_⟩
      · intro k hk; exact absurd hk (by simp)
      · show (x : expr.Map).val.length ≤ 0
        rw [x_post]
        simp
    · rw [hres]
      simp
  · -- h_fail: vars is nonempty
    obtain ⟨l, hl⟩ := vars
    cases l with
    | nil => simp_all
    | cons e es => simp_all
  · -- hbound for the recursive call (vs)
    calc 2 ^ vs.val.length ≤ 2 ^ vars.val.length :=
          Nat.pow_le_pow_right (by norm_num)
            (by rw [vs_post]; cases vars.val with | nil => simp | cons e es => simp)
      _ ≤ Usize.max := hbound
  · -- hiter for the loop call: rest's elements are exactly what the loop needs
    intro m hm
    apply rest_post2
    rw [iter_post, s_post] at hm
    exact hm
  · -- hresult for the loop call: nothing processed yet, vacuous
    intro m hm
    simp_all
  · -- hcov for the loop call: nothing processed yet, vacuous
    intro w hw
    obtain ⟨m, hm, _⟩ := hw
    simp_all
  · -- hbound for the loop call
    have h1 : vs.val.length < 2 ^ vs.val.length := Nat.lt_two_pow_self
    have h2 : 2 ^ vs.val.length ≤ Usize.max :=
      calc 2 ^ vs.val.length ≤ 2 ^ vars.val.length :=
            Nat.pow_le_pow_right (by norm_num)
            (by rw [vs_post]; cases vars.val with | nil => simp | cons e es => simp)
        _ ≤ Usize.max := hbound
    exact lt_of_lt_of_le h1 h2
  · -- hlen for the loop call
    obtain ⟨l, hl⟩ := vars
    cases l with
    | nil => simp_all
    | cons e es =>
      simp only [List.tail_cons] at vs_post
      rw [result_post, iter_post, s_post, rest_post3, vs_post]
      have heq : 2 * 2 ^ es.length = 2 ^ (e :: es).length := by
        simp [pow_succ, mul_comm]
      simp only [List.length_nil, Nat.zero_add]
      rw [heq]
      exact hbound
  · -- final result: assemble from the loop's postcondition
    obtain ⟨l, hl⟩ := vars
    cases l with
    | nil => simp_all
    | cons e es =>
      simp only [List.tail_cons] at vs_post
      simp only [List.getElem_cons_zero] at v_post2
      rw [vs_post, v_post2] at result_post1 result_post2
      refine ⟨?_, result_post1, ?_⟩
      · intro w
        obtain ⟨m, hm, hrepr⟩ := rest_post1 w
        rw [vs_post] at hrepr
        exact result_post2 w m (by rw [iter_post, s_post]; simp [hm]) hrepr
      · rw [result_post3, iter_post, s_post, rest_post3, result_post, vs_post]
        have heq : 2 * 2 ^ es.length = 2 ^ (e :: es).length := by
          simp [pow_succ, mul_comm]
        simp only [List.length_nil, Nat.zero_add]
        rw [heq]
termination_by vars.val.length
decreasing_by
  obtain ⟨l, hl⟩ := vars
  cases l with
  | nil => simp_all
  | cons e es => simp_all

/-- **Spec theorem for `sat_naive_functional::solve_sat`'s loop.**
Scans `iter` for the first map that makes `e` evaluate to `true`. Needs every
candidate in `iter` to be well-formed over `e`'s variables (true of any `iter`
built by `naive_create_possible_valuations`) so `expr.evaluate` has a witness to
run against -- otherwise it could simply fail (`Err`) on an incomplete map. -/
@[step]
theorem sat_naive_functional.solve_sat_loop.spec
    (iter : alloc.vec.into_iter.IntoIter expr.Map) (e : expr.Expr)
    (hwf : ∀ m ∈ iter.val, ∃ w, Map.represents m (varsOf e) w) :
    sat_naive_functional.solve_sat_loop iter e ⦃ (result : core.option.Option expr.Map) =>
      (∀ v, result = some v → expr.evaluate e v ⦃ (r : core.result.Result Bool Unit) =>
        r = core.result.Result.Ok true ⦄) ∧
      (∀ m ∈ iter.val, expr.evaluate e m ⦃ (r : core.result.Result Bool Unit) =>
        r = core.result.Result.Ok true ⦄ → result ≠ none) ⦄ := by
  unfold sat_naive_functional.solve_sat_loop core.result.Result.is_ok_and
    sat_naive_functional.solve_sat.closure.Insts.CoreOpsFunctionFnOnceTupleBoolBool
    sat_naive_functional.solve_sat.closure.Insts.CoreOpsFunctionFnOnceTupleBoolBool.call_once
  dsimp only
  step*
  · -- witness (case w): the value `v` is well-formed, thanks to `hwf`
    have hv : v ∈ iter.val := by
      obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e2 es => simp_all
    exact (hwf v hv).choose
  · -- o = none: vacuous
    refine ⟨?_, ?_⟩
    · intro v hv; simp at hv
    · intro m hm hev
      obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e2 es => simp_all
  · -- hrepr
    have hv : v ∈ iter.val := by
      obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e2 es => simp_all
    exact (hwf v hv).choose_spec
  · -- main result: case on evalPure
    have hv : v ∈ iter.val := by
      obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => exact absurd (‹o = some v›.symm.trans o_post.1) (by simp)
      | cons e2 es =>
        have he2 : v = e2 := by
          have heq := ‹o = some v›.symm.trans o_post.1
          injection heq
        simp [he2]
    by_cases hev : evalPure (hwf v hv).choose e = true
    · simp only [result_post, hev]
      refine ⟨?_, ?_⟩
      · intro v' hv'
        injection hv' with hv''
        rw [← hv'']
        have hthis := expr.evaluate.spec_of_represents e v (hwf v hv).choose (hwf v hv).choose_spec
        rw [hev] at hthis
        exact hthis
      · intro m hm hev'
        simp
    · simp [result_post, hev]
      have hwf' : ∀ m ∈ iter1.val, ∃ w, Map.represents m (varsOf e) w := by
        intro m hm
        apply hwf
        obtain ⟨l, hl⟩ := iter
        cases l with
        | nil =>
          obtain ⟨ho, hiter1⟩ := o_post
          rw [hiter1] at hm
          exact absurd hm (by simp)
        | cons e2 es =>
          obtain ⟨ho, hiter1⟩ := o_post
          rw [hiter1] at hm
          exact List.mem_cons_of_mem e2 hm
      have hrec := sat_naive_functional.solve_sat_loop.spec iter1 e hwf'
      apply Aeneas.Std.WP.spec_mono hrec
      rintro r ⟨hA, hB⟩
      refine ⟨hA, ?_⟩
      intro m hm hm_ev
      obtain ⟨l, hl⟩ := iter
      cases l with
      | nil => simp_all
      | cons e2 es =>
        obtain ⟨ho, hiter1⟩ := o_post
        have hve2 : v = e2 := by
          have heq := ‹o = some v›.symm.trans ho
          injection heq
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · exfalso
          have hthis := expr.evaluate.spec_of_represents e v (hwf v hv).choose (hwf v hv).choose_spec
          rw [← hve2] at hm_ev
          cases hcase : expr.evaluate e v with
          | ok x => rw [hcase] at hthis hm_ev; simp_all
          | fail er => rw [hcase] at hthis; simp at hthis
          | div => rw [hcase] at hthis; simp at hthis
        · exact hB m (by rw [hiter1]; exact hm) hm_ev
termination_by iter.val.length
decreasing_by
  rcases hiv : (iter.val : List expr.Map) with _ | ⟨e2, es2⟩
  · rw [hiv] at o_post
    have h2 : _ = some v := ‹_›
    rw [o_post.1] at h2
    exact absurd h2 (by simp)
  · rw [hiv] at o_post
    rw [o_post.2]
    simp

/-- **Soundness**: if `sat_naive_functional::solve_sat` returns a valuation, it
    satisfies `e`. -/
theorem sat_naive_functional.solve_sat_sound (e : expr.Expr) (hbound : 2 ^ exprSize e ≤ Usize.max) :
    sat_naive_functional.solve_sat e ⦃ (result : core.option.Option expr.Map) =>
      ∀ v, result = some v →
        expr.evaluate e v ⦃ (r : core.result.Result Bool Unit) =>
          r = core.result.Result.Ok true ⦄ ⦄ := by
  unfold sat_naive_functional.solve_sat
  step*
  · -- hbound for collect_vars
    exact le_trans Nat.lt_two_pow_self.le hbound
  · -- hbound for naive_create_possible_valuations
    rw [s_post]
    calc 2 ^ vars.val.length ≤ 2 ^ exprSize e := Nat.pow_le_pow_right (by norm_num) vars_post3
      _ ≤ Usize.max := hbound
  · -- main result
    unfold alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    have hwf : ∀ m ∈ valuations.val, ∃ w, Map.represents m (varsOf e) w := by
      intro m hm
      obtain ⟨w0, hw0⟩ := (valuations_post2 m hm).1
      refine ⟨w0, fun k hk => ?_⟩
      apply hw0
      rw [s_post]
      exact (vars_post1 k).mpr hk
    exact Aeneas.Std.WP.spec_mono (sat_naive_functional.solve_sat_loop.spec valuations e hwf)
      (fun r hr => hr.1)

/-- **Completeness**: if some total valuation `w` satisfies `e`,
    `sat_naive_functional::solve_sat` finds a satisfying valuation. -/
theorem sat_naive_functional.solve_sat_complete (e : expr.Expr) (w : Std.U8 → Bool)
    (hbound : 2 ^ exprSize e ≤ Usize.max) (hsat : evalPure w e = true) :
    sat_naive_functional.solve_sat e ⦃ (result : core.option.Option expr.Map) =>
      result ≠ none ⦄ := by
  unfold sat_naive_functional.solve_sat
  step*
  · exact le_trans Nat.lt_two_pow_self.le hbound
  · rw [s_post]
    calc 2 ^ vars.val.length ≤ 2 ^ exprSize e := Nat.pow_le_pow_right (by norm_num) vars_post3
      _ ≤ Usize.max := hbound
  · unfold alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    have hwf : ∀ m ∈ valuations.val, ∃ w, Map.represents m (varsOf e) w := by
      intro m hm
      obtain ⟨w0, hw0⟩ := (valuations_post2 m hm).1
      refine ⟨w0, fun k hk => ?_⟩
      apply hw0
      rw [s_post]
      exact (vars_post1 k).mpr hk
    obtain ⟨m, hm, hrepr⟩ := valuations_post1 w
    have hrepr' : Map.represents m (varsOf e) w := by
      intro k hk
      apply hrepr
      rw [s_post]
      exact (vars_post1 k).mpr hk
    have hev := expr.evaluate.spec_of_represents e m w hrepr'
    rw [hsat] at hev
    exact Aeneas.Std.WP.spec_mono (sat_naive_functional.solve_sat_loop.spec valuations e hwf)
      (fun r hr => hr.2 m hm hev)

end sat_solver
