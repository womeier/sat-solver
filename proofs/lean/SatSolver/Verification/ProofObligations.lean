/- Handwritten proofs about the extracted definitions.

hax creates this file once and never modifies anything under
`Verification/`. Import the extraction modules to prove properties
about, e.g. `import SatSolver.Extraction`.

The soundness + completeness theorems live in `SatNaive.lean` (for
`sat_naive::solve_sat`) and `SatDpll.lean` (for `sat_dpll::solve_sat`).

`Tseitin.lean` and `Hybrid.lean` prove the other two CNF transformations
equisatisfiability-preserving, against pure models of them built on
`Encoding.lean`'s shared framework; `TseitinExtraction.lean` and
`HybridExtraction.lean` then join those models to the extracted Rust with
`@[step]` specs, so `cnf_transform_{tseitin,hybrid}.to_cnf.{sound,complete}`
are statements about the generated code itself. -/
import SatSolver.Verification.Prelude
import SatSolver.Verification.MapLemmas
import SatSolver.Verification.CollectVars
import SatSolver.Verification.Semantics
import SatSolver.Verification.Cnf
import SatSolver.Verification.Encoding
import SatSolver.Verification.Tseitin
import SatSolver.Verification.Hybrid
import SatSolver.Verification.TseitinExtraction
import SatSolver.Verification.HybridExtraction
import SatSolver.Verification.SatNaive
import SatSolver.Verification.SatDpll
