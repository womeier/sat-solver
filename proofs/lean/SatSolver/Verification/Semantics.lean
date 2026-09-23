/- Pure reference semantics for `expr::evaluate`, and the spec connecting it to the
extracted `expr.evaluate`. Working against a *total* valuation `Std.U16 → Bool` rather
than a partial `expr.Map` sidesteps the partiality of `Map.get` entirely: locality
(two maps agreeing on `varsOf e` evaluate the same) falls out for free, since both
sides just reduce to `evalPure w e` for the same `w`. -/
import SatSolver.Extraction
import SatSolver.Verification.MapLemmas
import SatSolver.Verification.CollectVars

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace sat_solver

/-- Pure reference semantics for `expr::evaluate`, over a total valuation. -/
def evalPure (w : Std.U16 → Bool) : expr.Expr → Bool
  | .True => true
  | .False => false
  | .Variable v => w v
  | .Conj e1 e2 => evalPure w e1 && evalPure w e2
  | .Disj e1 e2 => evalPure w e1 || evalPure w e2
  | .Neg e => ! evalPure w e

/-- A map `m` *represents* `w` on a set of keys `ks` if every key in `ks` is
    present in `m` with the value `w` assigns it. -/
def Map.represents (m : expr.Map) (ks : List Std.U16) (w : Std.U16 → Bool) : Prop :=
  ∀ k ∈ ks, Map.lookupList m.val k = some (w k)

theorem Map.represents_of_subset {m : expr.Map} {ks1 ks2 : List Std.U16} {w : Std.U16 → Bool}
    (hsub : ∀ k ∈ ks1, k ∈ ks2) (h : Map.represents m ks2 w) : Map.represents m ks1 w :=
  fun k hk => h k (hsub k hk)

/-- `evalPure` only depends on `w`'s values on `varsOf e`. -/
theorem evalPure_congr {w1 w2 : Std.U16 → Bool} (e : expr.Expr)
    (hagree : ∀ k ∈ varsOf e, w1 k = w2 k) : evalPure w1 e = evalPure w2 e := by
  induction e with
  | True => simp [evalPure]
  | False => simp [evalPure]
  | Variable v => simp [evalPure]; exact hagree v (by simp [varsOf])
  | Conj e1 e2 ih1 ih2 =>
    simp only [evalPure]
    rw [ih1 (fun k hk => hagree k (by simp [varsOf]; tauto)),
        ih2 (fun k hk => hagree k (by simp [varsOf]; tauto))]
  | Disj e1 e2 ih1 ih2 =>
    simp only [evalPure]
    rw [ih1 (fun k hk => hagree k (by simp [varsOf]; tauto)),
        ih2 (fun k hk => hagree k (by simp [varsOf]; tauto))]
  | Neg e ih =>
    simp only [evalPure]
    rw [ih (by simpa [varsOf] using hagree)]

/-- **Spec theorem for `sat_solver::expr::evaluate`** (totality + correctness).
If `m` represents some total valuation `w` on all of `e`'s variables, `evaluate`
succeeds and returns exactly `evalPure w e`. This also gives locality for free:
two maps representing the *same* `w` on `varsOf e` evaluate identically, since both
sides of this lemma only depend on `w`. -/
@[step]
theorem expr.evaluate.spec_of_represents (e : expr.Expr) (m : expr.Map) (w : Std.U16 → Bool)
    (hrepr : Map.represents m (varsOf e) w) :
    expr.evaluate e m ⦃ (r : core.result.Result Bool Unit) =>
      r = core.result.Result.Ok (evalPure w e) ⦄ := by
  induction e with
  | True => unfold expr.evaluate; step*; simp [evalPure]
  | False => unfold expr.evaluate; step*; simp [evalPure]
  | Variable v =>
    unfold expr.evaluate
    have hv : Map.lookupList m.val v = some (w v) := hrepr v (by simp [varsOf])
    step*
    simp_all [evalPure]
  | Conj e1 e2 ih1 ih2 =>
    unfold expr.evaluate
    have h1 : Map.represents m (varsOf e1) w :=
      Map.represents_of_subset (by intro k hk; simp [varsOf]; tauto) hrepr
    have h2 : Map.represents m (varsOf e2) w :=
      Map.represents_of_subset (by intro k hk; simp [varsOf]; tauto) hrepr
    replace ih1 := ih1 h1
    replace ih2 := ih2 h2
    step*
    simp only [r_post, core.result.Result.Insts.CoreOpsTry_traitTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
    step*
    · rename_i h1e
      simp only [r1_post]
      step*
      simp_all [evalPure]
    · rename_i h1e
      simp_all [evalPure]
  | Disj e1 e2 ih1 ih2 =>
    unfold expr.evaluate
    have h1 : Map.represents m (varsOf e1) w :=
      Map.represents_of_subset (by intro k hk; simp [varsOf]; tauto) hrepr
    have h2 : Map.represents m (varsOf e2) w :=
      Map.represents_of_subset (by intro k hk; simp [varsOf]; tauto) hrepr
    replace ih1 := ih1 h1
    replace ih2 := ih2 h2
    step*
    simp only [r_post, core.result.Result.Insts.CoreOpsTry_traitTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
    step*
    · rename_i h1e
      simp_all [evalPure]
    · rename_i h1e
      simp only [r1_post]
      step*
      simp_all [evalPure]
  | Neg e ih =>
    unfold expr.evaluate
    replace ih := ih (by simpa [varsOf] using hrepr)
    step*
    simp_all [evalPure, core.result.Result.map,
      expr.evaluate.closure.Insts.CoreOpsFunctionFnOnceTupleBoolBool.call_once]

end sat_solver
