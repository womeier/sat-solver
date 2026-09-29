/- Handwritten proofs about the extracted definitions.

hax creates this file once and never modifies anything under
`Verification/`. Import the extraction modules to prove properties
about, e.g. `import SatSolver.Extraction`.

The soundness + completeness theorems live in `SatNaive.lean` (for
`sat_naive::solve_sat`), `SatDpll.lean` (for `sat_dpll::solve_sat`) and
`SatCdcl.lean` (for `sat_cdcl::solve_sat`).

`Tseitin.lean` and `Hybrid.lean` prove the other two CNF transformations
equisatisfiability-preserving, against pure models of them built on
`Encoding.lean`'s shared framework; `TseitinExtraction.lean` and
`HybridExtraction.lean` then join those models to the extracted Rust with
`@[step]` specs, so `cnf_transform_{tseitin,hybrid}.to_cnf.{sound,complete}`
are statements about the generated code itself. `sat_dpll::solve_sat` encodes with
the hybrid, so `SatDpll.lean`'s two theorems consume `HybridExtraction.lean`'s
`Encodes.sound`/`.complete` on their main arm and `Cnf.lean` only on the fallback
arm `encode` takes when the hybrid runs out of gate variables.

`SatCdcl.lean` does the same for `sat_cdcl::solve_sat`, through a tree of nine
statements: `analyze.spec` (what 1-UIP conflict analysis computes, given a well-formed
state), the four obligations that establish and preserve that state (`new`, `assign`,
`propagate`, `backtrack`), `Solver.search.spec` (the CDCL loop -- soundness,
completeness *and* termination, the last by a base-3 trail numeral paired with the room
left in the conflict counter), the `solve_cnf` pair, and the two roots. All nine are
proved.

Its roots carry the same size bound `sat_dpll`'s do and none of their own, because
`sat_cdcl` checks its conflict counter (`checked_add`) rather than assuming it cannot
overflow. What that costs is a third answer: `sat_cdcl::solve_sat` can return
`SatResult::Unknown`, so its completeness theorem reads "never answers `Unsat` for a
satisfiable formula" where the other two read "returns a model".
`SatSolver/PrintAxioms.lean` is where the per-theorem claims are checked. -/
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
import SatSolver.Verification.SatCdcl
