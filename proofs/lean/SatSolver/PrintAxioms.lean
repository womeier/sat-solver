/- Prints the axioms each top-level soundness/completeness theorem depends on, so CI
(and anyone running `lake build` locally) can see at a glance whether any of them
pull in more than the standard `propext`/`Classical.choice`/`Quot.sound` trio — in
particular, that none of them accidentally depend on `sorryAx` or on one of the
`axiom`-declared `Debug`/`Display` stubs hax seeds in `SatSolver/Assumptions/`. -/
import SatSolver.Verification.ProofObligations

open sat_solver

#print axioms sat_naive.solve_sat_sound
#print axioms sat_naive.solve_sat_complete
#print axioms sat_dpll.solve_sat_sound
#print axioms sat_dpll.solve_sat_complete
