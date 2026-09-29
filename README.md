# sat-solver

Implementation of various SAT solving algorithms in Rust,
extracted to and verified in Lean 4 with [hax](https://github.com/hacspec/hax).
All three are verified end to end - soundness and completeness, machine-checked, `sorry`-free.
- `sat_naive` (backtracking search over `Expr`)
- `sat_dpll` (DPLL on the CNF: unit propagation plus splitting)
- `sat_cdcl` (DPLL plus conflict-driven clause learning).

`sat_cdcl` has a third answer, `SatResult::Unknown`, which it gives when the `u32`
conflict counter is exhausted; its completeness theorem is correspondingly "never answers
`Unsat` for a satisfiable formula" where the other two say "returns a model". That is what
lets it be verified with no bound on the search; the trade is spelled out under Todo below.

The specification — soundness and completeness for all three solvers — lives in
[`proofs/lean/SatSolver/Verification/ProofObligations.lean`](proofs/lean/SatSolver/Verification/ProofObligations.lean),
which collects the theorems proved in
[`SatNaive.lean`](proofs/lean/SatSolver/Verification/SatNaive.lean),
[`SatDpll.lean`](proofs/lean/SatSolver/Verification/SatDpll.lean) and
[`SatCdcl.lean`](proofs/lean/SatSolver/Verification/SatCdcl.lean).

## Benchmarks

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="docs/scaling-dark.svg">
  <img src="docs/scaling.svg" width="780"
       alt="Median solve time per instance against the number of variables, on a logarithmic time axis, over SATLIB uniform random 3-SAT at the phase transition (clause to variable ratio 4.26). Satisfiable sets are drawn solid, unsatisfiable dashed. Each instance had a ten-second budget; a curve stops where fewer than half the set fits in it. cdcl on sat sets runs from 57 µs at 20 variables to 1.69 s at 200, about 4.2 times per 25 variables, and at 225 variables solves only 7/25 in the budget. cdcl on unsat sets runs from 604 µs at 50 variables to 1.09 s at 175, about 4.5 times per 25 variables, and at 200 variables solves only 10/25 in the budget. dpll on sat sets runs from 210 µs at 20 variables to 2.89 s at 125, about 9.7 times per 25 variables, and at 150 variables solves only 7/25 in the budget. dpll on unsat sets runs from 12.2 ms at 50 variables to 1.44 s at 100, about 10.8 times per 25 variables, and at 125 variables solves only 7/25 in the budget. naive manages only the 20-variable sat set, at 94.0 ms, and at 50 variables solves only 0/25 in the budget.">
</picture>

`just satlib` downloads the three 50-variable [SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html)
uniform-random-3-SAT sets into `benchmarks/` and `just satlib-test` runs the solvers over them;
`just satlib-fetch uf100-430 …` adds the larger ones, up to 250 variables.

`just satlib-scaling` re-measures the ladder, writes
[`docs/scaling.csv`](docs/scaling.csv) and redraws both SVGs from it with
[`docs/make_scaling_svg.py`](docs/make_scaling_svg.py) (stdlib only).

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
- [ ] **The verified guarantee doesn't cover benchmark-sized `Expr`s.** Every
      soundness/completeness theorem here carries a size hypothesis. `sat_naive`,
      `sat_dpll` and `sat_cdcl` all carry `2 ^ exprSize e ≤ Usize.max` — formulas
      of at most ~63 AST nodes — inherited from the worst-case CNF blowup bound in
      `Cnf.lean`, which `encode`'s naive-transform fallback arm can hit. That is
      now the *only* binding one, and it is an artifact of the `Expr` layer, not
      of any solver: `sat_cdcl::solve_cnf`, the entry point a DIMACS front end
      calls, is verified with no bound on the CNF at all. So `solve_cnf_sound` and
      `solve_cnf_complete` do cover `uf250-1065`.

      Getting there cost one thing, and it is worth spelling out because it is a
      real trade rather than bookkeeping. `⦃ ⦄` is total correctness and rules out
      failure, so proving anything about `search` means proving the extraction's
      *checked* `self.conflicts += 1` never overflows. The only bound available on
      the conflicts still to come is the termination measure, which is exponential
      in the variable count — so as a hypothesis it read
      `9^n + 2·3^n ≤ u32::MAX`, true for `n ≤ 10`, and the theorems spoke about
      ten-variable formulas. `sat_cdcl` now *checks* the counter instead:
      `self.conflicts.checked_add(1)` and a third answer,
      `SatResult::Unknown`, when it is exhausted. Two instructions per conflict
      (`cmp eax, -1` and a never-taken `je`) against ~85 µs of work, so the cost
      is not measurable.

      What it buys: soundness and "never answers `Unsat` for a satisfiable CNF"
      become unconditional. What it costs: completeness weakens from "a
      satisfiable formula gets a model" to "a satisfiable formula does not get
      `Unsat`" — it gets a model or `Unknown`, and `Unknown` only with
      `conflicts = u32::MAX`, which `search.spec` records, so the weaker statement
      cannot hide a cheap give-up. And the termination argument's outer half is now
      "at most `2^32` conflicts, because the code counts them" rather than "the
      restart budget grows geometrically, so restarts run out". The geometric
      growth is still in the code and still what makes the solver fast; it is just
      no longer what the proof leans on.

      That weakening is forced, not chosen. The clause database grows by one
      learned clause per conflict and never shrinks (clause indices are `reason`
      handles — see above), `Vec::push` needs the length to fit a `usize`, and the
      only provable bound on the conflicts of a 250-variable run is exponential. So
      some finite cap exists whatever the counter's width, and a cap that can be
      reached is an outcome that has to be reported.

- [ ] **No UNSAT proof output.** Competitions require DRAT proofs checked by
      `drat-trim`, because an `UNSAT` answer is otherwise unverifiable. The
      machine-checked soundness theorem is the substitute here, and for
      `sat_cdcl::solve_cnf` it is now unconditional — an `Unsat` from it is a
      refutation of the CNF as given, not of a CNF small enough to reason about.
