# Plan: Lean soundness + completeness proof for the naive SAT solvers

> **AI-generated.** This document was written and is maintained by Claude (Anthropic's
> coding agent), working in this repository. It records what the proof effort found as it
> went, so it is a log of an agent's reasoning rather than a hand-written design note.
> The claims in it are checked to the extent the tree is: `lake build` and
> `SatSolver/PrintAxioms.lean` verify the Lean, `cargo test` the Rust; the prose around
> them has not been independently reviewed.

> **Historical record.** This plan was completed (see "Progress" at the bottom); it is kept for
> the extraction findings and proof techniques it documents, which still apply to the later
> `Cnf.lean`/`SatDpll.lean` work that this plan predates and does not cover.
>
> One thing below no longer matches the tree: `sat_naive_functional` — the solver that
> materializes all `2^n` valuations up front — has since been **removed** (`src/sat_naive_functional.rs`
> and `Verification/SatNaiveFunctional.lean`, both proved sound and complete at the time). It was
> strictly dominated: same `2^n` asymptotics as `sat_naive` but ~2.5x slower on `uf20-91` and far
> hungrier for memory, and it proved nothing `sat_naive` doesn't already prove. Mentions of it
> below, including its two top-level theorems, describe the state of the repo when the plan was
> written.
>
> Two smaller drifts, same story: the variable type is now `u16`/`Std.U16`, not the `u8`/`Std.U8`
> the `char`→`u8` note under "Progress" landed on (the ceiling moved from 255 to 65535 variables;
> the substitution was mechanical and needed no proof restructuring), and `Map` grew a `Cnf.lean`
> sibling plus `SatDpll.lean` that this plan never mentions.
>
> Most recently, `src/cnf.rs` was split: it keeps the `Literal`/`Clause`/`Cnf` types and
> `eval_cnf`, while the transformation moved to `src/cnf_transform_naive.rs` and gained two
> siblings, `cnf_transform_tseitin.rs` and `cnf_transform_hybrid.rs`. `sat_dpll::solve_sat` now
> goes through `solve_sat_with(e, Transform::Hybrid)`, so `Verification/Cnf.lean` refers to
> `cnf_transform_naive.*` throughout and the two top-level `SatDpll.lean` theorems open with
> `simp only [solve_sat, solve_sat_with, encode]` where they used to `unfold solve_sat`, then
> split on the hybrid's `Result` — see "The default encoding is the hybrid one" below.

## Where the Tseitin and hybrid proofs stand

`Verification/{Encoding,Tseitin,Hybrid}.lean` prove both new transformations **sound and
complete** — `toCnf_sound` (every model of the CNF satisfies `e`) and `toCnf_complete` (every
model of `e` extends to a model of the CNF, agreeing on `varsOf e`), which together is
equisatisfiability. No `sorry`; all four rest only on propext/Classical.choice/Quot.sound.

Two things are worth recording about the *shape* of these proofs, because neither applies to
`Cnf.lean`:

- **Soundness needs no freshness.** Tseitin's defining clauses are biconditionals, so any
  valuation satisfying them already pins each gate to the subformula it names
  (`Tseitin.encode_sound` is an *equality*, `Literal.eval w l = evalPure w e`). The only
  invariant it needs is `State.Pinned`: if the shared constant gate was allocated, its unit
  clause was emitted. The hybrid's definitions are one-directional (`g → c`, not `g ↔ c`), so
  there the corresponding statement weakens to an implication — a gate may be false where the
  clause list it names is true.
- **Completeness is where freshness is spent.** Both `encode_complete`/`cnfRec_complete`
  extend the witness gate by gate, and that is only harmless because the new gate sits at
  `next`, strictly above every variable mentioned so far (`State.Wf`). `Cnf.eval_upd_of_lt` is
  the lemma that cashes this in. For the hybrid the gate is given the value its clause list
  actually takes, which makes the substitution value-preserving — so the body comes out with
  exactly the truth value the naive transform would have given it.

**The extraction-matching layer is done too.** `TseitinExtraction.lean` and
`HybridExtraction.lean` carry an `@[step]` spec per extracted function, each saying it agrees
with its model counterpart under an abstraction (`absEncoder` / `absRenamer`) that reads the
`Vec`-of-`Vec` clause store as a plain list and the `u32` counter as a `Nat`. The payoff is
`cnf_transform_{tseitin,hybrid}.to_cnf.{sound,complete}`: four theorems that mention the
generated code and nothing else. So all three transformations are now verified *as Rust*, not
merely as algorithms.

Three things cost more here than in `Cnf.lean`, and are worth knowing before touching these
files:

- **State threading.** Every spec has to say what came out *and* what the state became. The
  naive transform is a pure function and needs none of this.
- **`?` desugaring.** Each `?` becomes `Try.branch` on a `Result` plus a `ControlFlow` match,
  so every spec carries an explicit `Ok`/`Err` split, and the `Err` path goes through
  `from_residual` and the blanket `From T T` instance (the identity) — which has to be
  unfolded by name before `step*` can see through it.
- **Overflow preconditions are real.** The hybrid's `disjoin` computes `n * m` in `usize`
  *before* deciding whether to distribute, so `cnfRec_length_le` (one clause per AST node),
  `cnfRec_defs_length_le` (one definition per pair of nodes) and `cnfRec_clause_length_le`
  (one literal per node) exist purely to discharge it. Tseitin needs only the linear
  `encode_clauses_length_le`. These are honest properties of the Rust, not proof bookkeeping:
  without them the extracted code really could overflow.

One small addition outside these files: `Prelude.lean` gained an `alloc.vec.Vec.append` spec,
which `Renamer::rename` needs and nothing in the repo previously called.

## The default encoding is the hybrid one

`solve_sat` is `solve_sat_with(e, Transform::Hybrid)`, and both top-level `SatDpll.lean`
theorems are stated about that. The hybrid dominates the other two: it distributes only where
distributing is cheaper (`disjoin` compares the real clause counts, `n * m <= n + m`, of the
operand CNFs it already has in hand), so on the clausal input SATLIB consists of it reproduces
the naive CNF exactly, and on formulas where distribution would blow up it names subformulas
instead. That local, exact decision is also why no size/depth heuristic for *choosing* between
the three transformations would be an improvement — the choice is already made per node, on
better information than any whole-formula proxy has.

Two things had to change to keep the proofs on the default:

- **`seed_cnf_vars`.** `dpll.spec`'s `hpresent` precondition wants a map that already holds
  every variable of the CNF it is handed, and `initial_valuation (collect_vars e)` does not
  cover gate variables. `sat_dpll::seed_cnf_vars` inserts `false` for every variable the CNF
  mentions, right after `initial_valuation`; on `Transform::Naive` it is a no-op (that CNF
  mentions nothing outside `e`, and those keys are already `false`). Its three specs mirror
  `initial_valuation_loop.spec` — frame, all-set, and presence-monotone, the last being what
  composes with the seed the search must not lose.
- **Both arms of `encode`.** The hybrid `to_cnf` returns `Err` when gate variables exhaust
  `u16`, and `encode` falls back to the naive transformation, so each theorem splits on that
  `Result`. The arms differ only in why a model of the CNF is a model of `e`
  (`cnf_transform_hybrid.Encodes.sound`/`.complete` versus `Cnf.eval_cnfPure`); the rest of
  the argument is shared, in `sound_tail` for the soundness direction. This fallback is also
  why `solve_sat_sound`/`solve_sat_complete` still carry the exponential `hbound` alongside
  the hybrid's quadratic `hquad`.

`HybridExtraction.lean` grew a `cnf_transform_hybrid.Encodes` predicate for this: it packages
what `to_cnf.spec`'s `Ok` arm returns (a well-formed final state, a body, and the definitions
appended to it) so `SatDpll.lean` consumes the transformation as two plain implications and
never mentions `Hybrid.cnfRec`.

`Transform::Naive` remains reachable through `solve_sat_naive`/`SAT_SOLVER_DPLL_NAIVE`, which
is what `tests/satlib.rs` uses to check the two encodings agree on real instances.

## Where CDCL stands (partly specified, not yet verified)

`src/sat_cdcl.rs` is now a real solver rather than the stub this plan refers to: the classic
CDCL loop — 1-UIP conflict analysis, non-chronological backjumping, VSIDS-style decisions with
periodic activity decay, phase saving, geometric restarts. It encodes through
`sat_dpll::encode` (made `pub` for it), so DPLL and CDCL search the identical CNF and the
benchmark gap between them is the value of clause learning alone: 2.5x on `uf20-91`, 14x on
`uf50-218`, 20x on `uuf50-218`.

**The solver as a whole is not proved.** What stands in for it is tests: unit tests for each
piece (including that
`analyze` returns the asserting clause and the backjump level a worked example demands, and
that it leaves no scratch state behind), a 300-instance random 3-SAT differential check at the
phase transition against the proved-correct `sat_naive`, and all 3000 SATLIB verdicts with
every model model-checked. The Lean side has begun: see below.

It is **no longer excluded from extraction**: `just extract` now translates every function in
`sat_cdcl`, and `proofs/lean/SatSolver/Verification/SatCdcl.lean` states the specification of
conflict analysis. Two Rust-side reshapes were needed to get there, both behaviour-preserving
and both forced by aeneas rather than by the proof:

- `propagate` was nested loops with a `return` out of the inner one ("Returns inside of nested
  loops are not supported yet"). It is now one flat loop over a cursor that wraps back to 0
  whenever the pass it finished assigned something -- the same passes in the same order.
- `status` iterated `self.clauses[clause].0.iter()` and returned early out of it ("Not
  implemented yet"). It now indexes by position, like `analyze` already did.

Neither could be skipped instead: charon's `--exclude` name patterns do not match inherent-impl
methods (`crate::sat_cdcl::{impl crate::sat_cdcl::Solver}::status` and three other spellings all
fail to match), so an untranslatable method lands in `Funs.lean` as a generated `sorry`.

`analyze.spec` is proved, `sorry`-free and non-vacuously. It proves that 1-UIP conflict analysis returns a
clause entailed by the database, false under the current assignment, asserting at the backjump
level it also returns, with that level strictly below the conflict level -- and that it leaves
every field of the solver but `activity` as it found it, the `seen` scratch array included.
`conflictState.hypotheses` exhibits a state satisfying every hypothesis of it, so a
contradictory `Solver.WF` is ruled out and the theorem is not vacuous.

**The whole correctness statement is written down and proved**, in `SatCdcl.lean`'s "The whole
correctness statement" section: `sat_cdcl.solve_sat_sound` and `solve_sat_complete` (stated
exactly as `SatDpll.lean`'s proved pair, so CDCL is a drop-in replacement on the identical CNF),
the `solve_cnf` pair they factor through, `Solver.search.spec` — where the learning-soundness
invariant "every clause the database holds is entailed by the problem" is carried across the
loop — and the four state-invariant obligations `Solver.new.spec`/`assign.spec`/`propagate.spec`/
`backtrack.spec` that establish and preserve `Solver.WF`.

**All nine are proved, `sorry`-free**, checked per theorem by `assert_no_sorry` in
`SatSolver/PrintAxioms.lean`; the roots report the standard trio plus the two
`native_decide` axioms the extraction brings in for `analyze_loop0`'s two `.expect`
messages. The order was leaves-up, and each layer sent one requirement down to the one
below — which is the real argument for stating the tree before proving it: the corrections
below were all found by a proof that could not close.
`Solver.new.spec` went first because it is the cheap leaf: five loop specs for the three passes
`new` makes (variable count, seven-array initialisation, `occurs` marking), then
`Solver.wf_of_fresh`, where every field of `Solver.WF` that says anything is vacuous over the
empty trail — the one exception being `db_len`, which comes from the input via `CnfShort`.
`Solver.assign.spec` followed, via `Solver.wf_assign`, and is where `decision_first` and
`reason_wf`'s strict trail inequality (the acyclicity of the implication graph) are earned.

Proving those two **corrected `Solver.WF` itself**, which is the main thing writing the statements
down bought: (1) it had no `phase_length` field, because `analyze` never reads `phase` — but
`assign` writes it and `search` reads it, so the state `assign` produces could not be shown
well-formed without it; (2) `decision_of_level` said *every* level from 1 to `decisionLevel` has
a decision, which the code does not maintain — `search` pushes `trail_lim` and only then calls
`assign`, so between the two the top level exists and is empty. It now quantifies over trail
entries instead, which is what `assign` can preserve and still all `analyze` needs. (3) A third
hypothesis, `hopen`, had to be added to `assign.spec`: a propagation at a level above 0 does not
open that level, so it preserves "every level with an entry has a decision" only if the level
already has one. (4) `Solver.WF` said nothing about `trail_lim`'s *contents* — only that
`decisionLevel` is its length — because nothing `analyze` does reads them. But "`backtrack level`
undoes exactly the assignments above `level`" is a claim about `trail_lim[level]`, so without a
field tying it to the trail, the stated `backtrack.spec` is not a statement about levels at all.
`trail_lim_spec` says `trail_lim[j]` is where level `j + 1` begins; `new` and `assign` preserve it.
(5) Nothing said a `reason` implies its variable is assigned, so a variable off the trail could
carry a stale reason into the region `backtrack` unassigns, and `reason_wf` could not be shown
preserved for it. `reason_assigned` closes that. (6) `occurs` had no length field either — it is
the other array `analyze` never reads — but `pick_branch_var` indexes it by a value slot, so
`occurs_length` is what makes the decision heuristic's scan in-bounds.

`Solver.backtrack.spec` is proved on top of those: `Solver.wf_backtrack` plus
`backtrack_loop.spec` for the pop-and-clear loop, and `Solver.mem_take_iff_level_le`, which is
`trail_lim_spec` read through `idxOf` and is where "undoes exactly the levels above" actually
becomes a statement about the trail prefix. `pop`, `truncate` and `unwrap` needed `@[step]` specs
of their own — the toolchain ships none, and `backtrack` is the first function here to call them.

`Solver.propagate.spec` came next, and needed specs for `lit_value`, `status` (the per-clause scan,
deliberately not `@[step]` since the clause is not determined by the call) and `Option::is_some`.
Three invariants ride through its loop: the pass invariant behind the `None` answer ("while
`progress` is false nothing has been assigned this pass, so the clauses behind the cursor are still
not falsified"), the one that makes a *conflict* answer usable by `analyze` ("a falsified clause
mentions the current level" — preserved because only this pass's own assignments, all at that level,
can falsify anything), and `assign`'s `hopen`. **Termination is lexicographic** on
`(unassigned slots, progress, clauses left)`: the wrap-around back to clause 0 is why one measure
does not do, and the first component needs `Solver.trail_length_lt` (the trail is strictly shorter
than the slot arrays while anything is unassigned). It also added the fourth missing `WF` field,
`db_vars` (every variable a clause mentions has a slot): `analyze` only ever reads literals the
assignment already falsified, which are in range for that reason, but `propagate` scans every clause
including ones nothing is assigned in. It also means `SatCdcl.lean` is no longer `sorry`-free as a file —
`analyze.spec` and everything it rests on is, and `SatSolver/PrintAxioms.lean` is where that is
checked, per theorem, with `assert_no_sorry`. None of the nine carries `@[step]` or any other
attribute, so none can leak into a proof that looks finished. Discharge order is at the end of
the section.

Then the two functions `search` calls that are not about the implication graph at all, and the
frame conditions it needs from the four that are. `pick_branch_var.spec` is where the `true`
answer comes from — `None` means every variable the problem mentions is assigned — and it needed
a hypothesis the statements did not have: `value.len() ≤ 2 ^ 16`, since the scan counts in
`usize` and casts the index down to the `u16` a variable is, so without the bound the variable
`search` decides on need not be the one the heuristic chose. That hypothesis is now on
`search.spec` too. `decay.spec` is one line on top of `Solver.wf_activity` ("only `activity`
changed"), which is also what carries the invariant across `analyze`. The frames are the other
half: `assign` and `propagate` now say they leave `occurs` and the conflict counter alone (and
`propagate` that it keeps the slot count), because the search loop has to carry
"every variable of the problem has a slot and is marked" and the counter's headroom across every
call it makes, and `Solver.db s' = Solver.db s` does not say that.

Then **`search`'s termination measure**, which is the one part of the CDCL proof with no
analogue anywhere else in this repo: every other loop here terminates because a counter runs
down, and `search` goes backwards — a backjump undoes assignments, a restart undoes all of
them. The measure reads the trail as a base-3 numeral with one digit per slot, most
significant first: `0` where the trail has run out, `1` for a decision, `2` for a
propagation. Decisions and propagations append a digit where there was a `0`; a *backjump*
replaces `P, d, …` (with `d` the decision it jumps over) by `P, ℓ` with `ℓ` propagated by the
clause just learned, so the digit at that position goes `1 → 2` and everything the backjump
threw away was worth strictly less, being the lower-order digits. That is Nieuwenhuis,
Oliveras and Tinelli's ordering on DPLL states, in the form a `termination_by` can consume:
`3 ^ n` minus the numeral. Restarts are the second component: a restart needs `budget`
conflicts since the last one and grows the budget by half of itself, so `restartsLeft` (how
many times it can still grow before passing the step bound) drops. `Solver.searchMeasure` is
the pair, lexicographic.

`propagate.spec` and `backtrack.spec` then had to say more. `propagate`'s hypothesis was
"nothing is falsified yet", which `search` cannot supply — the assignment that follows a
backjump can falsify a clause, so the next call has one. The weaker statement that *is*
inductive is "everything falsified mentions the level the search is on", which is all the
proof ever used the stronger one for, and `propagate` now hands it back for the state it
returns as well as consuming it. It also frames the levels and reasons of the trail entries it
was given. `backtrack.spec` gained the two conjuncts the measure reads: *which* prefix of the
trail it leaves (`trail_lim[level]`'s, spelled without a dependent index by quantifying over
the entry), and that the entries it kept kept their reasons — the measure's digit for an entry
is whether it has one.

Then what learning needs. The database *grows*, and `Solver.wf_push` is not free because of
`db_len`: the invariant needs every clause short, so a *learned* clause has to be short too.
That is why `analyze.spec` now also reports the length of what it returns — its literals sit
on distinct marked variables, which are distinct entries of the trail, so there are at most
`2 ^ 16` of them plus the UIP. `Solver.Marking.bounds` had the bound already; nothing had
asked it for it. Alongside: `Entails.trans` (entailment composes through a database every
clause of which the problem entails), `Solver.unsat_of_conflict_level_zero'` (a conflict with
no decision above it is a refutation, since at level 0 the assignment is forced by the
database itself) and `Solver.model_of_fixpoint` (a propagation fixpoint with every variable
assigned is a model) — the two answers `search` returns, each stated over the problem rather
than over the clauses the search happens to hold.

The loop's invariant is then a structure, `Solver.Searching`, like `Solver.Marking` and
`Solver.Analyzing` above and for the same reason: eleven clauses, each of which every step has
to re-establish. Three are about the `u32` counters rather than about the search; one —
`levels`, "every open level was opened by a decision" — is a fact `Solver.WF` *cannot* state,
since `search` pushes `trail_lim` and only then assigns, so the state in between has an empty
top level, and `assign.spec` is applied to exactly that state. `Searching.propagate`,
`.restart` and `.decide` are the three easy steps: each takes the specs' postconditions and
gives back the invariant plus what the measure did (`≤` for propagation, `<` for the other
two). Stating them over two states related by hypotheses keeps the semantic work out of the
thirteen-component state the extraction threads around.

`Searching.learn` is the fourth and hardest step: bump the counter, analyse, backjump, push
the clause, assert its first literal. Two facts carry it. The first is
`Solver.decision_at_trail_lim`: the trail entry a backjump lands on *is* a decision —
everything before it is at or below the level jumped to, so the decision its own level must
have (`decision_of_level`) can only be this entry, since `decision_first` puts that decision
before every entry at its level and there is nothing before this one. That is the `1 → 2`
digit the measure needs. The second is that **nothing is falsified right after a backjump**: a
clause false then was false before, and `falsified` says it had a literal at the level the
backjump just threw away, so it cannot still be false. Without that, the state after the
assertion could have a clause falsified at some lower level, and `falsified` — hence
`analyze`'s precondition on the next conflict — would not be inductive.

**`Solver.search.spec` is proved.** The loop's proof is four branch lemmas and the IH: the
restart (`backtrack 0`, a bigger budget, a fresh window), the `true` answer (propagation at a
fixpoint and no unassigned variable the problem mentions — `Solver.model_of_fixpoint`), the
decision, the `false` answer (a conflict at level 0 —
`Solver.unsat_of_conflict_level_zero'`), and the conflict above level 0 (`Searching.learn`).
`termination_by Solver.searchMeasure s budget` closes it; the decrease in each branch is a
`have` the default `decreasing_by` picks up. Two things were needed on the way that nothing had
asked for: `analyze.spec` now reports that the **activity array keeps its length** (without it a
*second* `analyze` call is not well-formed, since `Solver.WF`'s `activity_length` is gone after
the first), and `sat_cdcl.Solver.decay_if.spec` gives the `if i1 = 0 then decay else ok` of the
extraction a spec of its own, so the conflict branch is proved once rather than twice.

Stating the measure is also what **fixed `search.spec`, which was not a true statement**.
`self.conflicts += 1` and `budget += budget / 2` are *checked* `u32` arithmetic in the
extraction, so a state whose counter is near `u32::MAX` makes the call fail, and a `⦃ ⦄`
triple rules failure out. The measure bounds the conflicts still to come, so `hroom`
(`conflicts + searchMeasure ≤ u32::MAX`) is exactly the room the counter needs — an
exponential bound in the number of variables, which is the honest shape, since a `u32` cannot
count the conflicts of a run on 50 variables either. And `hbudget` became `2 ≤ first_restart`
rather than `0 <`: with a budget of 1, `budget += budget / 2` is a no-op, so the solver
restarts after every single conflict forever and nothing in the measure decreases across
those restarts. Termination *there* needs "a learned clause is not one the database already
has", a different and much harder argument, so the statement excludes the case instead of
pretending otherwise (`Solver::solve` passes `FIRST_RESTART = 100`). Three more hypotheses
arrived with the proof: `hdbroom` (the clause vector has room for the clauses still to be
learned — the same accounting as `hroom`, one index wider), `hfits` (the budget can grow to
`3 ^ n` and still fit twice over), and `hlevels` — the one that is not about machine
integers. "Every open level was opened by a decision" is what `propagate`'s `hopen` needs and
what the backjump measure counts on, `Solver.WF` cannot state it (the state between
`trail_lim.push` and `assign` has an empty top level), and `Solver::new` satisfies it
vacuously.

**`solve_cnf_sound` is proved**, and it is where those bounds come home: they are bounds on the
*input*, and they sit next to `CnfShort` in the way `2 ^ exprSize e ≤ Usize.max` does in
`SatDpll.lean`. The statement takes any `n` bounding the CNF's variables and asks
`searchRoom n ≤ u32::MAX`, where `searchRoom n = 3 ^ n * 3 ^ n + 2 * 3 ^ n` bounds
`Solver.searchMeasure` from above (`restartsLeft bound budget ≤ bound`, each restart worth at
most one full trail). Making that bound *usable* needed a new conclusion on `new.spec`: the slot
count is the **least** bound on the CNF's variables, not merely some bound. Without it the only
bound available is `2 ^ 16`, `searchRoom (2 ^ 16)` exceeds `u32::MAX`, and the theorem would be
vacuous rather than narrow. Narrow it is — about nine variables — and that is `self.conflicts`
being a `u32`, not slack in the argument.

Two further corrections came out of it. `search.spec`'s `hfix` **weakened**: "no clause of the
database is falsified" is false of a CNF holding the *empty* clause, and `solve_cnf` has to
answer for that CNF too (it answers `None`), so the hypothesis is now the loop invariant's
`falsified` — a falsified clause mentions the current level — which is all the proof ever spent
it on, and which is vacuous at level 0. And `new.spec` now reports `s.conflicts = 0`, which
nothing had asked for and `hroom` needs. The model-reading loop
(`solve_cnf_loop.spec`) claims two things, both needed: the pairs already pushed stay, and every
assigned variable in the window is recorded — the second is what makes a `true` answer a
*model*, since `search.spec` talks about `Solver.valueOf` and the caller only sees the vector.
It spends `value.len() ≤ 2 ^ 16` on the `v as u16` cast, exactly as `pick_branch_var` does.

`solve_cnf_complete` came free: the same prelude, and then `search.spec`'s `false` clause says
the CNF has no model while `hsat` says it has one, so the arm that would return `None` is
unreachable and `step*` closes it. It carries the same three input bounds, because neither
direction can be stated without them.

**The two roots are proved, and the tree is closed.** They split on the same `Result` as
`SatDpll.lean`'s pair — the hybrid arm and the naive fallback `encode` takes when gate
variables run out — and the three new bounds have to be pulled back through `encode` to reach
them. Clause lengths and clause counts were already available from `Hybrid.lean`
(`cnfRec_clause_length_le`, `cnfRec_defs_length_le`) and `Cnf.lean` (`cnfPure_*`); the
*variable* bound was not, and getting it took three additions. `Hybrid.cnfRec_next_le_add`
says the encoding allocates at most one gate per AST node (only `disjoin` allocates).
`cnf_transform_hybrid.Renamer.new.spec` grew a least-upper-bound conclusion — the same shape
`Solver.new.spec` grew, for the same reason — and `Encodes` grew the field that carries it:
it knew the gate counter started *above* `e`'s variables, and sizing an array needs that it
starts no higher than it has to. `varBound e` is the result: `e`'s own variables plus one gate
per node.

The one piece with no DPLL counterpart is `solve_sat_with`'s insertion loop. DPLL searches the
map it returns; CDCL copies a `Vec<(u16, bool)>` into a map seeded only from `collect_vars e`.
Saying the pairs read back out of that map needs the model to name each variable at most once
— which is `solve_cnf_sound`'s third conjunct, true because the vector holds nothing but slot
reads. The loop spec states that consequence as an *implication* rather than taking the
hypothesis, so `solve_sat_complete`, which has no model to be functional, can use the same
spec. The coverage conjunct, interestingly, turned out not to be needed at the `Expr` layer at
all: `evaluate` reads only `e`'s own variables, so `Map.represents` on `varsOf e` suffices, and
that holds because insertion only adds keys.

The shape of the proof: `analyze_loop0_loop0.spec` says the clause scan computes the pure model
`Solver.scan`, and `Solver.scan_marking` says what that model *means* -- it preserves
`Solver.Marking` (the bookkeeping half of the loop invariant) and folds the scanned clause into
the resolvent. `analyze_loop0.spec` then runs the resolution loop: the trail walk returns the
latest pending conflict-level variable, `Solver.pendingVars_split` turns that into
"`pending` drops by exactly one", and the two branches are the learned clause (`pending == 0`)
and one application of `Entails.resolution` against that variable's reason (otherwise), with
`Entails.drop_level_zero` licensing the level-0 literals the scan skipped.

Three `step` specs the toolchain does not ship were needed: `Iterator::next` on a `usize` range
(`CoreModels` gives it an `mvcgen`-style `@[spec]`, which Aeneas's `step` does not see),
`PartialEq` on `Option<u16>`, and a rewrite for `Option::expect` -- the last deliberately *not*
a `step` spec, since `step` would have to guess the value the Rust asserts is there, and that
value is exactly what the invariant supplies. The range spec is stated over an arbitrary
`Range`, not over `{ start := i, end := e }`, because destructuring the iterator in the proof
detaches it from the `termination_by` measure.

`Solver.Analyzing` is the resolution loop's invariant: the clause derived so far is
`Solver.resolvent`, which lives in `lower` plus the `seen` flags of the conflict-level variables
still behind the cursor, and is never materialized by the Rust. What a full proof of the solver
still needs, beyond everything `SatDpll.lean` already has:

- **`Solver.WF` itself.** `analyze.spec` assumes it; `assign`, `propagate` and `backtrack` have
  to establish it. That is the next piece of work, and it is where the two fields the Rust
  relies on silently have to be earned: `decision_first` (a level's decision is its earliest
  trail entry, which is what makes `.expect("a propagated literal has a reason")` safe) and
  `db_len` (clauses are shorter than `2 ^ 31 - 65537` literals, the one assumption about the
  *input* rather than the solver).
- **Resolution soundness of learning** — every clause `analyze` appends is implied by the
  clauses it started from, because each step of the loop is one resolution step. This is the
  invariant the whole file rests on, and the one that makes CDCL's proof qualitatively
  different from DPLL's: the clause database changes as the search runs. Done:
  `analyze.spec`'s first conjunct. What is left is carrying it across `search`'s calls, so the
  database the *next* conflict is analysed against is sound too.
- **Trail invariants** — every propagated literal's `reason` is a clause all of whose other
  literals are false and which was already in the database; levels along the trail are
  monotone; `backtrack` restores a prefix. These are `Solver.WF` in `SatCdcl.lean`. Its
  `reason_wf` field is also the implication graph: there is no graph data structure to model,
  because `trail` is a topological order of it by construction -- when `propagate` assigns `v`
  from a unit clause every other literal of that clause is already assigned, hence already
  earlier on the trail. That is the whole acyclicity argument, and it is why conflict analysis
  reasons by induction on trail position rather than over reachability. `Solver.WF` also has to
  make explicit what the Rust leaves implicit: `backtrack` does not clear `level` or `phase`, so
  "`level[v]` is meaningful only while `v` is assigned" becomes a precondition on every lemma
  that reads it.
- **No `Usize` underflow in the trail walk** — `analyze`'s inner `index -= 1` has no bounds
  test. In Rust a broken invariant is a panic; in Lean it is a subtraction that must be proved
  safe, from "while `pending > 0` there is still a marked conflict-level variable behind the
  cursor". This is the one place where the counting view (`pending`) and the graph view have to
  be reconciled, and since `index` is never reset between resolution steps the invariant has to
  hold across them. Done: `analyze_loop0_loop1.spec`, with its witness supplied from
  `Analyzing.pending_eq` and, on the first iteration, from a conflict-level literal of the
  conflicting clause.
- **No `i32` overflow in `pending`** — Rust infers `i32` for it, so the count of pending
  conflict-level literals has to be bounded. `Solver.trail_length_le` does it: trail entries are
  distinct `u16` variables, so there are at most `2 ^ 16` of them. `Solver.Marking.bounds`
  extends that to `marked` and `lower`, which is what makes the two `Vec` pushes safe. Done.
- **Termination** — DPLL's "one variable fewer per level" argument does not apply. The standard
  argument is that the learned clause is asserting at the backjump level, so the state
  immediately after a conflict is one the search has not been in before. Not started for the
  search; `analyze`'s own termination, on the other hand, is already proved, because `⦃ ⦄` is
  `Aeneas.Std.WP.spec` and `spec div p ↔ False` — a `⦃ ⦄` statement about a `partial_fixpoint`
  definition rules out divergence, so `analyze.spec` says `analyze` returns. Where a measure is
  needed it sits on the spec theorem (`analyze_loop0_loop1.spec`'s `termination_by index.val`),
  not on the extracted definition. `⦃ ⦄div` (`dspec`) is what a partial-correctness statement
  would use; nothing under `Verification/` does.
- **Two `native_decide` axioms** ride in with the extraction, not with the proof: Aeneas's
  `toStr` discharges "this string literal is at most `u32::MAX` bytes" with `decide +native`,
  so every extracted function holding a `panic!` message carries one axiom per message.
  `analyze_loop0` has two `.expect`s, so `analyze.spec` depends on
  `analyze_loop0._native.decide.ax_1` and `_2` on top of `propext`, `Classical.choice` and
  `Quot.sound`. Nothing else under `Verification/` does.
- **Extraction shape** — the loops are `while`/`for` over indices with a mutable struct, which
  `-loops-to-rec` turns into `partial_fixpoint` definitions over the whole `Solver` state. That
  is a much larger state to thread through specs than `dpll`'s `(cnf, val)`.

## Context

The repo has two "naive" SAT solvers:

- `src/sat_naive.rs` — recursive backtracking search (`check_possible_valuations`) that
  threads one mutable `Map` through the recursion, flipping each variable false-then-true.
- `src/sat_naive_functional.rs` — builds the full list of all `2^n` valuations up front
  (`naive_create_possible_valuations`), then linearly scans it with `evaluate`.

Both are decision procedures for propositional SAT over `Expr` (`src/expr.rs`). We want a
machine-checked proof, in Lean 4, that each is **sound** (a returned valuation really
satisfies the formula) and **complete** (if a satisfying valuation exists, one is found).

`flake.nix` already documents the intended path: `cargo hax into lean` extracts Rust into a
buildable Lean package at `proofs/lean` (verified via `lake build`). `hax-lib = "0.4.0"` is
already a Cargo dependency (currently unused). Confirmed via web search that hax 0.4.0's
`cargo hax into lean` (aeneas backend) is current and matches this pin. This means the proof
target is the *actual extracted Rust code*, not a hand-transliterated model — consistent with
the project's prior history of extracting to Coq and F* before hand-proofs were ever written.

Earlier design review (via a Plan sub-agent) validated the theorem shapes and lemma structure
below and flagged the risks captured in "Known risks" and "Edge cases".

## Target solvers and statements

Prove, for **both** `sat_naive::solve_sat` and `sat_naive_functional::solve_sat`:

- **Soundness**: `solve_sat e = some v → evaluate e v = Ok true`
- **Completeness**: `collect_vars e ⊆ dom(w) ∧ evaluate e w = Ok true → ∃ v, solve_sat e = some v`
  (stated with `dom(w) ⊇ collect_vars e`, not `=` — the weaker hypothesis is what the locality
  lemma actually supports, and is the more general/useful statement: a witness may carry
  irrelevant extra keys.)

Both statements are phrased purely in terms of `Ok true` / `Ok false` — never pattern-matched
against `Err` — by routing through a `evaluate_total` lemma (below) that shows `evaluate`
never errors once the valuation covers `collect_vars e`.

## Steps

### 1. Scope the hax extraction

**Done:** `Map` in `src/expr.rs` has been swapped from `BTreeMap<char, bool>` to a
`Vec<(char, bool)>`-backed newtype (same `get`/`insert` API, no call-site changes needed in
either solver) — done up front rather than as a reactive fallback, since `BTreeMap` has no
confirmed support in hax's core-models library while `Vec`/slices are its best-supported
territory. This is asymptotically free here: the parser only accepts single-character lowercase
variables (`expr.rs`'s `parse_var`), so `Map` never holds more than 26 entries regardless of
input size — `O(log 26)` vs `O(26)` is noise next to the solvers' `2^n` branching. `cargo build`
and `cargo test` pass unchanged. `Cargo.lock` also got re-resolved to match the already-pinned
`hax-lib = "0.4.0"` in `Cargo.toml` (it was stale at 0.3.6) as a side effect of the first build.

Only these items matter for the proof; everything else in the crate (the `nom` parser,
`fmt::Display`, the `SatSolver` struct/fn-pointer wrapper, and the
still-stub `sat_dpll.rs`/`sat_cdcl.rs`) must be excluded so extraction isn't blocked by code hax
can't/shouldn't handle:

- `src/expr.rs`: `Map`, `Expr`, `evaluate`, `collect_vars_aux`, `collect_vars`
- `src/sat_naive.rs`: `initial_valuation`, `check_possible_valuations`, `solve_sat`
- `src/sat_naive_functional.rs`: `naive_create_possible_valuations`, `solve_sat`

Use hax's item-selection query syntax on the CLI (e.g.
`cargo hax into lean -i '-** +sat_solver::expr::** +sat_solver::sat_naive::** +sat_solver::sat_naive_functional::**'`)
and then trim further if the parser/Display code still gets pulled in transitively.

### 2. Run extraction, resolve fallout

Enter the nix dev shell (`nix develop`) so `elan`/`cargo-hax` are available, run the scoped
extraction, and inspect the generated Lean before writing any proofs — the generated
signatures determine the proof shape, not the other way around. Specific things to check:

- **`Map`**: already swapped to `Vec<(char, bool)>` (step 1). If extraction of even that shape
  still fails, isolate all get/insert reasoning behind one lemma file (`MapLemmas`) so any
  further representation change only ever touches one place.
- **`&mut Map` in `check_possible_valuations`**: aeneas has no Lean mutable references, so this
  almost certainly extracts to a function returning `(Bool × Map)` (state-threading) rather than
  `Bool` with a side effect. Confirm the real generated signature before finalizing the
  induction lemma in step 4.
- **`.unwrap()` on `evaluate(...)`**: confirm how aeneas models `Result::unwrap` (does it
  produce a genuine panic/proof-obligation, or silently default on `Err`?). This affects whether
  we need an explicit "never hits the error path" corollary for trustworthiness.

### 3. Lean project layout

**Superseded by what `cargo hax into lean` actually generates** (confirmed by running it —
see "Progress" below). hax itself enforces the separation: it creates
`SatSolver/Extraction/*.lean` fresh on every run (not hand-edited), and creates
`SatSolver/Verification/ProofObligations.lean` exactly once, never touching it again on
re-extraction. So hand-written proof files live under `Verification/`, not a `Proofs/`
directory we invent ourselves:

```
proofs/lean/
  SatSolver/
    Extraction/                    # generated by `just extract`, never hand-edited
      Types.lean                   # Map, Expr
      Funs.lean                    # evaluate, collect_vars, both solve_sat, etc.
    Verification/                  # ours; hax creates ProofObligations.lean once and
      ProofObligations.lean        # never touches this directory again
      MapLemmas.lean                # get/insert/domain lemmas
      CollectVars.lean               # membership / (optional) no-dup lemmas
      Semantics.lean                 # locality + totality lemmas about `evaluate`
      SatNaive.lean                  # invariant + soundness/completeness for solver #1
      SatNaiveFunctional.lean        # exhaustiveness + soundness/completeness for solver #2
```
`ProofObligations.lean` imports `SatSolver.Extraction` plus the files above and states the
final top-level soundness/completeness theorems for both solvers.

### 4. Core lemmas (in dependency order)

1. **Locality** (`Semantics.lean`): if `w1`, `w2` agree on `collect_vars e`, then
   `evaluate e w1 = evaluate e w2`. Plain structural induction on `Expr`; everything else
   reduces to this.
2. **Totality** (`Semantics.lean`): `collect_vars e ⊆ dom(w) → ∃ b, evaluate e w = Ok b`.
   Discharges every `.unwrap()` site and the `Err`-avoidance corollary from step 2.
3. **`sat_naive` invariant** (`Proofs/SatNaive.lean`): by induction on the variable list `vs`,
   generalized over an **arbitrary** accumulator `val0` with `collect_vars e \ vs ⊆ dom(val0)`
   (see "mutation reuse" risk below — do *not* fix `val0` to all-false):
   `check_possible_valuations e vs val0 = (b, val1)` where `val1` agrees with `val0` outside
   `vs`, and `b = true ↔ ∃ ext : vs → Bool, evaluate e (val0 updated by ext on vs) = Ok true`.
   The `true` direction of soundness falls out directly (`val1` is itself the witness). Base
   case (`vs = []`) reduces to `evaluate e val0` via the totality lemma.
4. **`sat_naive_functional` exhaustiveness** (`Proofs/SatNaiveFunctional.lean`): induction on
   `vs` shows `naive_create_possible_valuations vs` is exactly the set of total maps with domain
   `vs` (as a set — order/multiplicity don't matter). The `evals1`/`evals2`
   duplicate-then-overwrite construction just needs unfolding; no mutation subtlety here since
   this version never threads a shared mutable accumulator.
5. **Top-level soundness/completeness** (`Proofs/Main.lean`): assemble 3+4 with `collect_vars`
   into the two theorem statements per solver.

### 5. Known risks / edge cases to handle explicitly

- **Mutation-reuse subtlety (sat_naive only)**: the same `Map` is reused across the false- and
  true-branch recursive calls, so on entering the true branch, keys in `vs` may hold stale
  leftovers from the failed false branch. The invariant in lemma 3 must be proved for arbitrary
  accumulator content on `vs` — an invariant fixed to "false-everywhere" will not carry through
  the induction. This is the one genuinely non-obvious step in the whole proof; call it out
  explicitly in the proof's comments when written.
- **`Expr::True` / `Expr::False`** (empty `collect_vars`): the base case of every induction.
  Neither existing example (`example_expr_sat`/`example_expr_unsat`) exercises a
  variable-free expression — add one as a sanity check once solvers are extracted.
- **`collect_vars` via `HashSet`**: iteration order is unspecified but irrelevant (proofs only
  use membership). `List.Nodup` isn't strictly required (`BTreeMap::insert` is idempotent) but
  is cheap to prove and simplifies the induction in lemma 3 if needed.

### 6. Verification

- `cargo hax into lean` succeeds and `lake build` (or `lake exe cache get && lake build`)
  compiles the generated package with zero `sorry`s in `Proofs/`.
- Grep `proofs/lean/Proofs/` for `sorry`/`admit` post-hoc as a completeness gate.
- Sanity-check the extracted definitions actually match intent by adding a couple of concrete
  `#eval`/`example` checks in Lean against `example_expr_sat`/`example_expr_unsat`-equivalent
  formulas (including the empty-variable edge case from step 5) before trusting the abstract
  proofs.
- `cargo test` / `cargo build` in the Rust crate must still pass unchanged — this work only
  adds proofs and (possibly) the `Map` representation swap from step 2, not new solver logic.

## Progress

- [x] `Map` swapped from `BTreeMap<char, bool>` to `Vec<(char, bool)>` in `src/expr.rs`;
      `cargo build`/`cargo test` pass.
- [x] Steps 1–2 (scoped extraction) done: `just extract` runs a clean `cargo hax into lean`
      with zero `sorry`s and zero errors in the two target functions' dependency closure.
      Findings that shaped the final recipe, differing from the original plan:
      - The Lean backend's `-i` CLI flag and `#[hax_lib::exclude]` attribute are both inert —
        neither is honored by the charon+aeneas pipeline (confirmed via a CLI warning and by
        testing). Scoping instead goes through `charon`'s own `--exclude`/`--start-from`
        flags, passed via `cargo hax into lean --charon-args="..."`. `--start-from` proved
        unreliable (path-resolution quirks, silent no-ops); `--exclude` on the specific
        unwanted items (the `nom` parser functions, `example_expr_sat`/`example_expr_unsat`,
        and the `sat`/`sat_dpll`/`sat_cdcl` modules) is what actually works.
      - **Critical, non-obvious finding**: when the package has both a `lib` and a `bin`
        target (main.rs), charon treats whichever target it's compiling as "primary" and
        gives it full bodies — the *other* target's items become opaque external references
        with no body, regardless of `--exclude`/`--start-from` scoping. Since neither the CLI
        nor `[package.metadata.charon]` expose a way to select just the `lib` target, `just
        extract` works around this by moving `src/main.rs` aside for the duration of the
        extraction (restored via a shell `trap`, so it survives even if extraction fails).
      - `Iterator::find`, `HashSet`, `.iter().map(...).collect()` chains, and the `vec!` macro
        all failed to translate (unsupported lifetime patterns / internal `aeneas` errors) —
        `Map::get`, `collect_vars`/`collect_vars_aux`, and
        `naive_create_possible_valuations` were rewritten to explicit loops/recursion and
        `Vec` construction, per the `BTreeMap`→`Vec` reasoning above (still O(1) in practice,
        capped at 26 variables). `collect_vars`/`collect_vars_aux` also switched from owned
        `Expr` to `&Expr` — owned recursive moves out of `Box<Expr>` hit a "no bottoms in the
        value" `aeneas` interpreter error that borrowing avoids (matching `evaluate`'s existing
        convention). Both `solve_sat` functions were made `pub` (needed for an earlier
        `--start-from` attempt; harmless either way).
      - `flake.nix` gained `hax.url = "github:cryspen/hax"` as a flake input, providing
        `cargo-hax`/`elan`/`lake` declaratively instead of the old `cargo install` fallback.
      - Extracted output lives at `proofs/lean/SatSolver/Extraction/{Types,Funs}.lean`
        (auto-generated, not hand-edited) — `Map`, `Expr`, `evaluate`, `collect_vars`,
        `collect_vars_aux`, `check_possible_valuations`, `initial_valuation`,
        `naive_create_possible_valuations`, and both `solve_sat`s are all present with real
        (non-`sorry`) bodies.
      - `&mut Map` extracts as `(Bool × Map)` return-threading, confirmed in
        `sat_naive.solve_sat`'s generated body:
        `let (b, val1) ← sat_naive.check_possible_valuations expr1 s val`.
- [x] `lake build` verified end-to-end (fresh `proofs/lean/SatSolver/` wiped, `just extract`
      run with no manual intervention, then `lake build`: 1736 jobs, zero errors). Getting
      here required three more `aeneas`/`CoreModels` compatibility fixes, all captured
      durably in the `just extract` recipe (not one-off manual patches):
      - `CoreModels` has **no `Char` support at all** (no `Clone`/`PartialEq`/`Debug`/
        `String::from`) — `char` is essentially unused in `aeneas`'s primary crypto-code
        domain. `Expr::Variable`/`Map`'s key switched from `char` to `u8` throughout
        `expr.rs`/`sat_naive.rs`/`sat_naive_functional.rs`; the parser (excluded from
        extraction anyway) converts `char ↔ u8` at its boundary; `Display` casts back
        (`*v as char`) for printing.
      - `evaluate`'s error type switched from `String` to `()` — `format!`/`String::from`
        don't translate (unsupported `alloc::fmt`/`String::from` machinery), and the error
        branch is provably unreachable once a valuation covers `collect_vars e` anyway, so
        the string content was never meaningful.
      - `CoreModels` has no `Clone` instance for raw tuples `(A × B)` — `aeneas`'s fallback
        (`BuiltinClone`) produces an instance from the wrong internal typeclass hierarchy
        (`Aeneas.Std.core.clone.Clone` instead of `CoreModels`'s `core.clone.Clone`), a
        genuine cross-namespace codegen bug. Fixed by giving `Map` a named `Entry { key,
        value }` struct instead of a raw `(u8, bool)` tuple — named structs get a normal
        derived-struct `Clone` instance and sidestep the gap entirely.
      - Two more `hax` quirks, both worked around durably in `just extract` itself (not just
        this one run): (a) the `Debug`/`Display` `fmt` axiom templates it seeds declare a
        spurious extra tuple component that doesn't match what call sites expect — stripped
        via a `sed -z` (multi-line) substitution right after seeding; (b) hax sometimes skips
        writing the root integration files (`SatSolver.lean`, `SatSolver/Extraction.lean`)
        that the `lean_lib`'s default target needs — recreated if missing, same as the
        `*External.lean` forwarder fix from before.
      - Also fixed: the recipe's `main.rs`-restore `trap` used a relative path, which broke
        when the recipe later `cd`s into `proofs/lean` (the trap fired with the wrong cwd at
        script exit) — now captures `root=$(pwd)` up front and uses absolute paths throughout.
- [x] Switched loop extraction from `aeneas`'s default fixed-point-combinator translation to
      `-loops-to-rec` (recursive functions), per an explicit recommendation in `aeneas`'s own
      agent-facing skill docs (vendored at
      `proofs/lean/.lake/packages/aeneas/documentation/skills/`): the combinator path's proof
      infra (`loop.spec_decr_nat`) is described as less mature/battle-tested than the
      recursive-function path (`unfold`/`step`/`termination_by`, "Pattern 4"). Passed via
      `cargo hax into lean --aeneas-args="-loops-to-rec"` (added to the `just extract` recipe).
      Confirmed in the regenerated `Funs.lean`: every former `loop`-combinator helper
      (`Map.insert`/`get`, `contains_var`, `merge_vars`, `initial_valuation`,
      `naive_create_possible_valuations`, both `solve_sat`s) now has a plain `@[rust_loop] def
      ..._loop` recursive definition instead. Re-verified `lake build`: 1736 jobs, zero errors
      (only `justfile` and the regenerated `Funs.lean` changed — `Types.lean` is untouched, as
      expected since loop translation doesn't affect type declarations).
- [x] Step 3 (Lean proof file layout) done: `Verification/{Prelude,MapLemmas,CollectVars,
      Semantics,SatNaive,SatNaiveFunctional}.lean`, aggregated by `ProofObligations.lean`.
      Whole soundness/completeness theorem tree stated top-down first (all `sorry`d), then
      filled in bottom-up. `lean-lsp-mcp` set up (via `uv`, see `AGENTS.md`) and used
      throughout instead of `lake build` loops, per the aeneas skill docs.
  - [x] `Prelude.lean`: `CoreModels` registers almost no `@[step]` lemmas for its own
        container/iterator primitives (only 2 in the whole package) — had to write generic
        reusable ones by hand: shared `Iter.next`, `Vec.deref`, `Slice.iter`, `Vec.new`,
        `Vec.push`. `Vec`/`Slice`/`Iter`/`IterMut` are all definitionally the same
        `{val : List T // val.length ≤ Usize.max}` in `CoreModels` (confirmed by reading
        `rust_primitives.sequence.Seq`'s definition), which made `deref`/`iter` trivial
        identity lemmas.
  - [x] `MapLemmas.lean`: `Map.get`/`insert` characterized against plain `List`-level
        `lookupList`/`upsertList` helpers. `get.spec` proved (structural induction via the
        `unfold`+`step*`+`termination_by` pattern, reusing `Prelude`'s shared-`Iter.next`
        spec). `insert.spec` is stated but still `sorry` — it goes through `IterMut`'s
        backward-continuation encoding (mutable borrow), which is harder; not yet attempted.
  - [x] `CollectVars.lean`: pure `varsOf`/`exprSize` (`exprSize` only exists to bound
        `Vec.push`'s `Usize.max` side-condition through the `merge_vars`/`Conj`/`Disj`
        recursion — real bound after dedup is ≤ 256, this coarser structural one needs no
        extra machinery). `contains_var`/`merge_vars`/`collect_vars_aux`/`collect_vars` all
        proved, no `sorry`.
  - [x] `Semantics.lean`: `evalPure` over a *total* valuation `Std.U8 → Bool` (sidesteps
        `Map`'s partiality entirely) + `Map.represents`. `evaluate.spec_of_represents` proved
        by structural induction on `Expr`; this single lemma gives totality *and* locality at
        once, since both sides only depend on the valuation. Conj/Disj needed hand-unfolding
        the `?`-operator's `Try`/`branch`/`from_residual` plumbing (no `@[step]` lemmas exist
        for it either). No `sorry`.
  - [x] `MapLemmas.lean`: `insert.spec`/`insert_loop.spec` proved (the `IterMut`
        backward-continuation encoding, generalized over an arbitrary already-consumed
        prefix `pre`). `hlen` is a *disjunction* — `lookupList self.val key ≠ none ∨
        self.val.length < Usize.max` — rather than a bare length bound: the strict bound is
        only ever actually needed on the genuine `Vec.push` path (key absent); when the key
        is already present, insertion is a pure overwrite needing no length headroom at all.
        This is what lets `check_possible_valuations` avoid re-deriving `Usize.max` headroom
        for its second insert per level (trying `value = true` after `value = false`
        failed), and lets `initial_valuation`/`naive_create_possible_valuations` do the same
        for keys visited more than once. Also added: `expr.Entry`/`expr.Map` clone specs
        (value-preserving, since `Entry`'s fields are `Copy` scalars).
  - [x] `Prelude.lean` gained two more generic specs needed by the top-level proofs:
        `Vec::clone` (via `Aeneas.Std.WP.spec_decr_nat`/`loop.spec_decr_nat` — a *different*
        proof technique than every other loop in this project, since `CoreModels`'s generic
        `Vec` clone is built from `Aeneas.Std`'s raw `loop` combinator rather than
        `partial_fixpoint` recursion) and `Vec::into_iter`'s `IntoIter::next`.
  - [x] `SatNaive.lean`: `check_possible_valuations.spec` proved — the loop invariant tracks,
        alongside soundness/completeness, an `hpresent` postcondition ("every variable in
        `vars` has been visited by the time the call returns") that lets a second
        insert/recursive-call of the same keys at an outer level avoid needing fresh
        `Usize.max` growth room, mirroring the `Map.insert.spec` disjunction one level up.
        `initial_valuation.spec` and the top-level `solve_sat_sound`/`solve_sat_complete`
        proved on top of it. File is fully `sorry`-free.
  - [x] `SatNaiveFunctional.lean`: `naive_create_possible_valuations_loop.spec` and
        `naive_create_possible_valuations.spec` proved — this algorithm is genuinely
        exponential, so the real headroom hypothesis threaded throughout is
        `2 ^ vars.length ≤ Usize.max` (not just `vars.length ≤ Usize.max`), with an exact
        `result.length = 2 ^ vars.length` output-count postcondition to make that bound
        composable across recursion levels. `solve_sat_loop.spec` needed an extra
        well-formedness hypothesis (`∀ m ∈ iter.val, ∃ w, Map.represents m (varsOf e) w`)
        since `expr.evaluate` can genuinely fail (`Err`) on an incomplete map — proved by
        combining two Hoare triples about the same deterministic computation via casing on
        its own `ok`/`fail`/`div` outcome (`Aeneas.Std.WP.spec_mono` for the
        postcondition-weakening step). Both top-level theorems proved on top of it. File is
        fully `sorry`-free.
      The well-founded-recursion `decreasing_by` obligations for these two files'
      self-referential lemmas needed a different technique than everywhere else in the
      project: the auto-generated termination goal bundles every explicit hypothesis
      (`hiter`/`hresult`/`hcov`/`hwf`/...) into one large dependent sigma type, and blind
      `simp_all` on it either times out or fails outright. Fixed by `rcases` on the
      iterator's underlying list plus anonymous-hypothesis (`‹_›`) lookups instead of naming
      the (often dagger'd/inaccessible) hypotheses `simp_all` would otherwise need by name.
- [x] **Done.** All four top-level theorems — `sat_naive::solve_sat_sound`/`_complete` and
      `sat_naive_functional::solve_sat_sound`/`_complete` — are proved, `sorry`-free, and
      verified end-to-end via a clean `lake build` (1742 jobs, zero errors/warnings).
