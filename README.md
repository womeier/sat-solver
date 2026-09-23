# sat-solver

WIP verification of a simplistic SAT solver in Rust, extracted to Lean 4 with
[hax](https://github.com/hacspec/hax) (`just extract`).

The specification — soundness and completeness for all three solvers — lives in
[`proofs/lean/SatSolver/Verification/ProofObligations.lean`](proofs/lean/SatSolver/Verification/ProofObligations.lean),
which collects the theorems proved in
[`SatNaive.lean`](proofs/lean/SatSolver/Verification/SatNaive.lean),
[`SatNaiveFunctional.lean`](proofs/lean/SatSolver/Verification/SatNaiveFunctional.lean) and
[`SatDpll.lean`](proofs/lean/SatSolver/Verification/SatDpll.lean), the last of which
rests on the CNF transformation proved correct in
[`Cnf.lean`](proofs/lean/SatSolver/Verification/Cnf.lean).
