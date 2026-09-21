/- Handwritten proofs about the extracted definitions.

hax creates this file once and never modifies anything under
`Verification/`. Import the extraction modules to prove properties
about, e.g. `import SatSolver.Extraction`.

The soundness + completeness theorems live in `SatNaive.lean` (for
`sat_naive::solve_sat`) and `SatNaiveFunctional.lean` (for
`sat_naive_functional::solve_sat`). See `PLAN.md` for the overall proof plan. -/
import SatSolver.Verification.Prelude
import SatSolver.Verification.MapLemmas
import SatSolver.Verification.CollectVars
import SatSolver.Verification.Semantics
import SatSolver.Verification.SatNaive
import SatSolver.Verification.SatNaiveFunctional
