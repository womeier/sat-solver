# sat-solver

Implementation of various SAT solving algorithms in Rust,
extracted to and verified in Lean 4 with [hax](https://github.com/hacspec/hax).

Three solvers: `sat_naive` (backtracking search over `Expr`), `sat_dpll` (DPLL
on the CNF: unit propagation plus splitting) and `sat_cdcl` (DPLL plus
conflict-driven clause learning). All three are verified end to end — soundness and
completeness, machine-checked, `sorry`-free.

The specification — soundness and completeness for all three solvers — lives in
[`proofs/lean/SatSolver/Verification/ProofObligations.lean`](proofs/lean/SatSolver/Verification/ProofObligations.lean),
which collects the theorems proved in
[`SatNaive.lean`](proofs/lean/SatSolver/Verification/SatNaive.lean) and
[`SatDpll.lean`](proofs/lean/SatSolver/Verification/SatDpll.lean), the latter of which
rests on the CNF transformations proved correct in
[`Cnf.lean`](proofs/lean/SatSolver/Verification/Cnf.lean) (naive distribution) and
[`Hybrid.lean`](proofs/lean/SatSolver/Verification/Hybrid.lean).
[`SatCdcl.lean`](proofs/lean/SatSolver/Verification/SatCdcl.lean) does the same for
`sat_cdcl`.

## Benchmarks
`just satlib` downloads the three 50-variable [SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html)
uniform-random-3-SAT sets into `benchmarks/` and `just satlib-test` runs the solvers over them;
`just satlib-fetch uf100-430 …` adds the larger ones, up to 250 variables.

Every `SAT` answer is model-checked with `expr::evaluate`, the way SAT
competitions check solver output — all 3000 verdicts are correct for each solver
that can attempt the set.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="docs/scaling-dark.svg">
  <img src="docs/scaling.svg" width="780"
       alt="Median solve time per instance against the number of variables, on a logarithmic time axis, over SATLIB uniform random 3-SAT at the phase transition (clause to variable ratio 4.26). Satisfiable sets are drawn solid, unsatisfiable dashed. Each instance had a ten-second budget; a curve stops where fewer than half the set fits in it. cdcl on sat sets runs from 57 µs at 20 variables to 1.69 s at 200, about 4.2 times per 25 variables, and at 225 variables solves only 7/25 in the budget. cdcl on unsat sets runs from 604 µs at 50 variables to 1.09 s at 175, about 4.5 times per 25 variables, and at 200 variables solves only 10/25 in the budget. dpll on sat sets runs from 210 µs at 20 variables to 2.89 s at 125, about 9.7 times per 25 variables, and at 150 variables solves only 7/25 in the budget. dpll on unsat sets runs from 12.2 ms at 50 variables to 1.44 s at 100, about 10.8 times per 25 variables, and at 125 variables solves only 7/25 in the budget. naive manages only the 20-variable sat set, at 94.0 ms, and at 50 variables solves only 0/25 in the budget.">
</picture>

`just satlib-scaling` re-measures the ladder, writes
[`docs/scaling.csv`](docs/scaling.csv) and redraws both SVGs from it with
[`docs/make_scaling_svg.py`](docs/make_scaling_svg.py) (stdlib only).

Why the censoring rule matters: `dpll` at 150 variables *looks* faster than at 125
(1.46 s against 2.89 s) purely because only the 7 easiest of 25 instances
finished. Those points are in `docs/scaling.csv`, marked, and not drawn.

## Todo

- [ ] **Resolution-hard families** — pigeonhole (`hole-n`) and friends, with a
      timeout. These are exponential for any DPLL-style solver, so they document
      the limit that motivates CDCL. [CNFgen](https://massimolauria.net/cnfgen/)
      generates them (also Tseitin, ordering principle, k-colourability) without
      downloading anything.

Known limits worth fixing (or at least documenting) alongside the above:

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
- [ ] **The verified guarantee doesn't cover benchmark-sized inputs.** Every
      soundness/completeness theorem here carries a size hypothesis, and they are
      the honest limit of what is proved. `sat_naive`/`sat_dpll` carry
      `2 ^ exprSize e ≤ Usize.max` — formulas of at most ~63 AST nodes, inherited
      from the worst-case CNF blowup bound in `Cnf.lean`. `sat_cdcl` carries
      `searchRoom (varBound e) ≤ u32::MAX`, which is much tighter, and is worth
      explaining because it is not slack in the *algorithm*:

      `⦃ ⦄` is total correctness and rules out failure, so proving anything about
      `search` means proving `self.conflicts += 1` — *checked* `u32` arithmetic in
      the extraction — never overflows. That needs a bound on the conflicts still
      to come, and the only such bound available is the termination measure itself,
      which is exponential in the variable count. `searchRoom n = 9^n + 2·3^n` is
      that bound, and `searchRoom n ≤ u32::MAX` holds exactly for `n ≤ 10`. So
      `solve_cnf_{sound,complete}` speak about CNFs of at most ten variables, and at
      the `Expr` layer `varBound e` is (largest variable index + 1) + `exprSize e`,
      which is tighter still. It is the only one of the new hypotheses that binds:
      the clause-count one has a 64-bit `usize` to spend and the clause-length one
      an `i32`, and neither is anywhere near either.

      Some of that is crudeness rather than necessity — `searchRoom` over-approximates
      via `restartsLeft bound budget ≤ bound`, so sharpening it would widen the
      theorem without touching a line of the termination proof. The exponential
      underneath is real, though: a `u32` genuinely cannot count the conflicts of a
      50-variable run.

      Checking the size at *runtime* and bailing out would not help — the bound is a
      predicate on the input alone, so a check relocates it rather than removing it,
      and `None` already means UNSAT, so aborting into it would have the solver call
      a satisfiable formula unsatisfiable. What would help is checking the *counter*:
      `checked_add` at the three increment sites plus a third outcome (`Unknown`).
      Then soundness and "never answers UNSAT for a satisfiable formula" become
      unconditional and cover the benchmarks, "satisfiable ⟹ returns a model" weakens
      to "⟹ a model or `Unknown`", and — the reason it is a genuine trade — the
      base-3 termination argument collapses into counting a `u32` down. Not done.

      So: the code runs fine on a 218-clause instance; the theorems say nothing about
      it. Benchmarking is complementary to the proofs, not redundant with them.
- [ ] **No UNSAT proof output.** Competitions require DRAT proofs checked by
      `drat-trim`, because an `UNSAT` answer is otherwise unverifiable. The
      machine-checked completeness theorem is the substitute here — but only
      inside the bound above.
