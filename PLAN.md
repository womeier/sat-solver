# Plan: Lean soundness + completeness proof for the naive SAT solvers

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
