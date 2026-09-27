# sat-solver

Implementation of various SAT solving algorithms in Rust,
extracted to and verified in Lean 4 with [hax](https://github.com/hacspec/hax).

Three solvers: `sat_naive` (backtracking search over `Expr`), `sat_dpll` (DPLL
on the CNF: unit propagation plus splitting) and `sat_cdcl` (DPLL plus
conflict-driven clause learning). The first two are verified; CDCL is not, yet.

The specification — soundness and completeness for the two verified solvers — lives in
[`proofs/lean/SatSolver/Verification/ProofObligations.lean`](proofs/lean/SatSolver/Verification/ProofObligations.lean),
which collects the theorems proved in
[`SatNaive.lean`](proofs/lean/SatSolver/Verification/SatNaive.lean) and
[`SatDpll.lean`](proofs/lean/SatSolver/Verification/SatDpll.lean), the latter of which
rests on the CNF transformations proved correct in
[`Cnf.lean`](proofs/lean/SatSolver/Verification/Cnf.lean) (naive distribution) and
[`Hybrid.lean`](proofs/lean/SatSolver/Verification/Hybrid.lean) (the Boy de la Tour
hybrid, which is what `solve_sat` encodes with by default — `Cnf.lean`'s transformation
is its fallback when gate variables run out).

## Benchmarks

`just satlib` downloads the [SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html)
uniform-random-3-SAT sets into `benchmarks/`; `just satlib-test` runs the solvers over them.

Every `SAT` answer is model-checked with `expr::evaluate`, the way SAT
competitions check solver output — all 3000 verdicts are correct for each solver
that can attempt the set.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="docs/benchmarks-dark.svg">
  <img src="docs/benchmarks.svg" width="780"
       alt="Mean solve time per instance, log scale, 100 instances per set. On uf20-91 (20 variables, satisfiable) cdcl averages 0.056 ms (worst 0.085 ms), dpll 0.147 ms (worst 0.446 ms) and naive 138 ms (worst 422 ms). On uf50-218 cdcl averages 0.322 ms (worst 1.19 ms) and dpll 4.66 ms (worst 19.0 ms); on the unsatisfiable uuf50-218 cdcl averages 0.589 ms (worst 1.52 ms) and dpll 12.0 ms (worst 42.8 ms). Naive is out of reach on the 50-variable sets because it enumerates all 2^50 valuations.">
</picture>

`just satlib-figure` re-measures and prints the dataset as CSV;
[`docs/make_benchmarks_svg.py`](docs/make_benchmarks_svg.py) (stdlib only)
redraws the two SVGs from it.

DPLL and CDCL search the *same* CNF (`sat_dpll::encode` under
`Transform::Hybrid`), so the gap between them is the value of clause learning and
nothing else: 2.6x on the 20-variable set, 14x on uf50-218, and 20x on the
unsatisfiable uuf50-218 — most where refuting the formula means exhausting the
search space, which is exactly what learned clauses prune. CDCL manages that
while *rescanning every clause* to propagate; with watched literals the gap would
be wider still.

## Todo

- [ ] **CLI front end** — read a `.cnf` from a path or stdin, print the standard
      `s SATISFIABLE` / `v <model>` lines, exit 10/20/0. Unlocks `hyperfine` and
      any third-party harness.
- [ ] **Differential + property testing** — random formulas checked against the
      (proved-correct) naive solver, plus `proptest`/`cargo fuzz` over the
      parser and `to_cnf`. `sat_dpll.rs` has a small hand-written version of
      this; it should be generative and run on many more instances.
- [ ] **Scaling curve** — `criterion` benchmark sweeping the clause/variable
      ratio through the 4.26 phase transition, naive vs DPLL vs CDCL. This is the
      plot that shows why each of them exists.
- [ ] **Resolution-hard families** — pigeonhole (`hole-n`) and friends, with a
      timeout. These are exponential for any DPLL-style solver, so they document
      the limit that motivates CDCL. [CNFgen](https://massimolauria.net/cnfgen/)
      generates them (also Tseitin, ordering principle, k-colourability) without
      downloading anything.
- [ ] **DIMACS 1993 challenge suite** — `aim`, `dubois`, `pret`, `ssa`, `bf`,
      `jnh`: small, structured, still cited. A useful second tier beyond random
      3-SAT.

Known limits worth fixing (or at least documenting) alongside the above:

- [x] **`Map` is a linear-scan assoc list.** ~~Every lookup is O(vars).~~ Now a
      slot array indexed by the variable itself (`Vec<Option<bool>>`, grown on
      demand), so `get` and `insert` are both O(1). This is *not* measurable at
      SATLIB sizes — 20–50 slots fit in a cache line either way, and `evaluate`
      short-circuits before doing many lookups — so it was worth doing for the
      asymptotics and for the proofs, not for the benchmark. It removed
      `Map.insert`'s `&mut`-iterator encoding (three nested backward
      continuations) and every `Usize.max` headroom hypothesis in `SatNaive.lean`
      and `SatDpll.lean`: indexing by the key bounds the array by the key type.
- [ ] **DPLL allocates a fresh residual CNF per node.** That is what makes the
      correctness proof clean (each recursive call is self-contained), and it is
      also the performance ceiling. Watched literals would fix it at a
      substantial cost in proof effort.
- [ ] **CDCL propagates by rescanning every clause.** Same trade one level up:
      `sat_cdcl::Solver::propagate` is O(clauses) per round where a production
      solver visits only the clauses that could have become unit. It also never
      deletes a learned clause (indices into the clause vector are used as
      `reason` handles) and does not minimize learned clauses. All three are
      engineering, not algorithm — the numbers above are what the algorithm alone
      buys.
- [ ] **CDCL is unverified.** `sat_naive` and `sat_dpll` have machine-checked
      soundness and completeness; `sat_cdcl` has tests only — including a
      300-instance random 3-SAT differential check against the proved-correct
      naive solver, and all 3000 SATLIB verdicts. Learning makes the proof a
      different animal: the invariant is that every learned clause is implied by
      the original ones (resolution soundness), on top of DPLL's trail
      invariants.
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
