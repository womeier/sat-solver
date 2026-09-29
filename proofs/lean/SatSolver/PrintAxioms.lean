/- Prints the axioms each top-level soundness/completeness theorem depends on, so CI
(and anyone running `lake build` locally) can see at a glance whether any of them
pull in more than the standard `propext`/`Classical.choice`/`Quot.sound` trio — in
particular, that none of them accidentally depend on `sorryAx` or on one of the
`axiom`-declared `Debug`/`Display` stubs hax seeds in `SatSolver/Assumptions/`. -/
import SatSolver.Verification.ProofObligations
import Mathlib.Util.AssertNoSorry

open sat_solver

#print axioms sat_naive.solve_sat_sound
#print axioms sat_naive.solve_sat_complete
#print axioms sat_dpll.solve_sat_sound
#print axioms sat_dpll.solve_sat_complete

/- `sat_cdcl`'s one proved theorem. Its axiom set is *expected* to hold two more than
the trio: Aeneas's `toStr` discharges "this string literal is at most `u32::MAX` bytes"
with `decide +native`, and `analyze_loop0` has two `.expect` messages. Those ride in
with the extraction, not with the proof; nothing else under `Verification/` has any. -/
#print axioms sat_cdcl.Solver.analyze.spec

/- The two `sat_cdcl` roots, which are now proved -- so these print the same trio as
`sat_dpll`'s pair plus the two `_native.decide` axioms the extraction brings in. Those
ride along wherever a statement so much as *mentions* an extracted function holding a
`panic!` message; they are a property of the definition, not of any proof. -/
#print axioms sat_cdcl.solve_sat_sound
#print axioms sat_cdcl.solve_sat_complete

/- `#print axioms` above is informational -- it prints, it does not fail. These lines
do fail the build, so "no `sorry`" is machine-checked rather than grep-checked, per
theorem: everything listed here is proved outright. -/
assert_no_sorry sat_naive.solve_sat_sound
assert_no_sorry sat_naive.solve_sat_complete
assert_no_sorry sat_dpll.solve_sat_sound
assert_no_sorry sat_dpll.solve_sat_complete
assert_no_sorry sat_cdcl.Solver.analyze.spec
assert_no_sorry sat_cdcl.Solver.new.spec
assert_no_sorry sat_cdcl.Solver.assign.spec
assert_no_sorry sat_cdcl.Solver.backtrack.spec
assert_no_sorry sat_cdcl.Solver.propagate.spec
assert_no_sorry sat_cdcl.Solver.pick_branch_var.spec
assert_no_sorry sat_cdcl.Solver.decay.spec
assert_no_sorry sat_cdcl.Solver.search_loop.spec
assert_no_sorry sat_cdcl.Solver.search.spec
assert_no_sorry sat_cdcl.solve_cnf_sound
assert_no_sorry sat_cdcl.solve_cnf_complete
assert_no_sorry sat_cdcl.solve_sat_sound
assert_no_sorry sat_cdcl.solve_sat_complete
assert_no_sorry cnf_transform_tseitin.to_cnf.sound
assert_no_sorry cnf_transform_tseitin.to_cnf.complete
assert_no_sorry cnf_transform_hybrid.to_cnf.sound
assert_no_sorry cnf_transform_hybrid.to_cnf.complete
