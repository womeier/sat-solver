# sat-solver

Implementation of various SAT solving algorithms in Rust,
extracted to and verified in Lean 4 with [hax](https://github.com/hacspec/hax).

The specification — soundness and completeness for all three solvers — lives in
[`proofs/lean/SatSolver/Verification/ProofObligations.lean`](proofs/lean/SatSolver/Verification/ProofObligations.lean),
which collects the theorems proved in
[`SatNaive.lean`](proofs/lean/SatSolver/Verification/SatNaive.lean),
[`SatNaiveFunctional.lean`](proofs/lean/SatSolver/Verification/SatNaiveFunctional.lean) and
[`SatDpll.lean`](proofs/lean/SatSolver/Verification/SatDpll.lean), the last of which
rests on the CNF transformation proved correct in
[`Cnf.lean`](proofs/lean/SatSolver/Verification/Cnf.lean).

## Benchmarks

`just satlib` downloads the [SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html)
uniform-random-3-SAT sets into `benchmarks/`; `just satlib-test` runs the solvers over them.

Measured over all 3000 instances (release build, mean per instance):

| solver             | `uf20-91` (SAT) | `uf50-218` (SAT) | `uuf50-218` (UNSAT) |
|--------------------|-----------------|------------------|---------------------|
| `dpll`             | 0.18 ms         | 6.0 ms           | 15.7 ms             |
| `naive`            | 154 ms          | out of reach     | out of reach        |
| `naive functional` | 480 ms          | out of reach     | out of reach        |

The naive solvers enumerate all `2^n` valuations, so they only ever see the
20-variable set — 50 variables is about ten orders of magnitude beyond them.
DPLL is ~1000x faster on the instances all three can attempt.

## Todo

- [ ] **CLI front end** — read a `.cnf` from a path or stdin, print the standard
      `s SATISFIABLE` / `v <model>` lines, exit 10/20/0. Unlocks `hyperfine` and
      any third-party harness.
- [ ] **Differential + property testing** — random formulas checked against the
      (proved-correct) naive solver, plus `proptest`/`cargo fuzz` over the
      parser and `to_cnf`. `sat_dpll.rs` has a small hand-written version of
      this; it should be generative and run on many more instances.
- [ ] **Scaling curve** — `criterion` benchmark sweeping the clause/variable
      ratio through the 4.26 phase transition, naive vs DPLL. This is the plot
      that shows why DPLL exists.
- [ ] **Resolution-hard families** — pigeonhole (`hole-n`) and friends, with a
      timeout. These are exponential for any DPLL-style solver, so they document
      the limit that motivates CDCL. [CNFgen](https://massimolauria.net/cnfgen/)
      generates them (also Tseitin, ordering principle, k-colourability) without
      downloading anything.
- [ ] **DIMACS 1993 challenge suite** — `aim`, `dubois`, `pret`, `ssa`, `bf`,
      `jnh`: small, structured, still cited. A useful second tier beyond random
      3-SAT.

Known limits worth fixing (or at least documenting) alongside the above:

- [ ] **255-variable ceiling.** `Expr::Variable(u8)` and `Map`'s keys are `u8`,
      so `uf250` only just fits and nothing larger does. Widening to `u16` would
      ripple through the extraction and every `Std.U8` in the proofs.
- [ ] **`Map` is a linear-scan assoc list**, so every lookup is O(vars).
- [ ] **DPLL allocates a fresh residual CNF per node.** That is what makes the
      correctness proof clean (each recursive call is self-contained), and it is
      also the performance ceiling. Watched literals would fix it at a
      substantial cost in proof effort.
- [ ] **The verified guarantee doesn't cover benchmark-sized inputs.** The
      soundness/completeness theorems carry `2 ^ exprSize e ≤ Usize.max`, i.e.
      formulas of at most ~63 AST nodes, inherited from the worst-case CNF blowup
      bound in `Cnf.lean`. The code runs fine on a 218-clause instance; the
      theorems say nothing about it. Benchmarking is therefore complementary to
      the proofs, not redundant with them.
- [ ] **No UNSAT proof output.** Competitions require DRAT proofs checked by
      `drat-trim`, because an `UNSAT` answer is otherwise unverifiable. The
      machine-checked completeness theorem is the substitute here — but only
      inside the bound above.
