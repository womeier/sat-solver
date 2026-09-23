//! Runs the solvers against the SATLIB benchmark suite.
//!
//! The instances live in `benchmarks/satlib/` and are not in the repository;
//! `just satlib` downloads them. Every test here degrades to a no-op (with a
//! note on stderr) when they are missing, so `cargo test` works on a fresh
//! clone.
//!
//! The sets are uniform random 3-SAT at the phase transition (clause/variable
//! ratio ≈ 4.26), which is where random instances are hardest:
//!
//! | set         | vars | clauses | instances | verdict |
//! |-------------|------|---------|-----------|---------|
//! | `uf20-91`   |   20 |      91 |      1000 | SAT     |
//! | `uf50-218`  |   50 |     218 |      1000 | SAT     |
//! | `uuf50-218` |   50 |     218 |      1000 | UNSAT   |
//!
//! Only DPLL can attempt the 50-variable sets: both naive solvers enumerate all
//! `2^n` valuations, so 50 variables is out of reach by roughly ten orders of
//! magnitude. They are exercised on `uf20-91` instead.
//!
//! Run the heavy sets (they are `#[ignore]`d) with `just satlib-test`, which
//! builds in release mode -- a debug build is ~20x slower and makes even the
//! 20-variable set tedious.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use sat_solver::dimacs::parse_dimacs;
use sat_solver::expr::{Expr, Map, evaluate};
use sat_solver::sat::SatSolver;
use sat_solver::sat_dpll::SAT_SOLVER_DPLL;
use sat_solver::sat_naive::SAT_SOLVER_NAIVE;
use sat_solver::sat_naive_functional::SAT_SOLVER_NAIVE_FUNCTIONAL;

const SATLIB: &str = "benchmarks/satlib";

/// Collects the `.cnf` files under `benchmarks/satlib/<set>`, sorted by name so
/// runs are reproducible. Returns `None` when the set hasn't been downloaded.
fn instances(set: &str) -> Option<Vec<PathBuf>> {
    let root = Path::new(SATLIB).join(set);
    if !root.is_dir() {
        eprintln!(
            "skipping: {} not found -- run `just satlib`",
            root.display()
        );
        return None;
    }
    let mut out = Vec::new();
    collect_cnf(&root, &mut out);
    out.sort();
    if out.is_empty() {
        eprintln!("skipping: no .cnf files under {}", root.display());
        return None;
    }
    Some(out)
}

/// The archives differ in layout -- `uf20-91` extracts its files flat, while
/// `uuf50-218` nests them one directory deeper -- so recurse.
fn collect_cnf(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_cnf(&path, out);
        } else if path.extension().is_some_and(|e| e == "cnf") {
            out.push(path);
        }
    }
}

fn read_instance(path: &Path) -> Expr {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    parse_dimacs(&text).unwrap_or_else(|e| panic!("cannot parse {}: {e}", path.display()))
}

/// Solves one instance and checks the verdict. A `SAT` answer is only accepted
/// if the returned valuation really satisfies the formula -- the same
/// model-checking that SAT competitions apply to solver output, and here it also
/// exercises the claim the Lean soundness theorem makes about `solve_sat`.
fn check(solver: &SatSolver, expr: &Expr, path: &Path, expect_sat: bool) -> Duration {
    let start = Instant::now();
    let result: Option<Map> = (solver.solve)(expr);
    let elapsed = start.elapsed();

    match (&result, expect_sat) {
        (Some(model), true) => assert_eq!(
            evaluate(expr, model),
            Ok(true),
            "[{}] {} reported SAT with a model that does not satisfy the formula",
            solver.description,
            path.display()
        ),
        (None, false) => {}
        (Some(_), false) => panic!(
            "[{}] {} is unsatisfiable but a model was returned",
            solver.description,
            path.display()
        ),
        (None, true) => panic!(
            "[{}] {} is satisfiable but no model was found",
            solver.description,
            path.display()
        ),
    }
    elapsed
}

/// Runs `solver` over (a prefix of) a set and reports timings.
fn run_set(solver: &SatSolver, set: &str, expect_sat: bool, limit: Option<usize>) {
    let Some((n, mean, worst)) = measure(solver, set, expect_sat, limit) else {
        return;
    };
    println!(
        "[{}] {}: {} instances, mean {:.2?}, worst {:.2?}",
        solver.description, set, n, mean, worst
    );
}

/// Solves every instance and returns `(count, mean, worst)`, or `None` when the
/// set hasn't been downloaded.
fn measure(
    solver: &SatSolver,
    set: &str,
    expect_sat: bool,
    limit: Option<usize>,
) -> Option<(usize, Duration, Duration)> {
    let mut paths = instances(set)?;
    if let Some(n) = limit {
        paths.truncate(n);
    }

    let mut total = Duration::ZERO;
    let mut worst = Duration::ZERO;
    for path in &paths {
        let expr = read_instance(path);
        let elapsed = check(solver, &expr, path, expect_sat);
        total += elapsed;
        worst = worst.max(elapsed);
    }
    Some((paths.len(), total / paths.len() as u32, worst))
}

#[test]
fn dimacs_reads_a_satlib_instance() {
    let Some(paths) = instances("uf20-91") else {
        return;
    };
    let expr = read_instance(&paths[0]);
    // 91 clauses of 3 literals: 91 * 3 variable nodes, 91 * 2 + 90 connectives,
    // plus one negation per negative literal -- just check it is non-trivial.
    assert!(!matches!(expr, Expr::True | Expr::False));
}

/* Everything below is `#[ignore]`d: these are benchmarks, and running them in a
default `cargo test` (a debug build, ~20x slower) would cost minutes. Use
`just satlib-test`. */

/// The headline check: DPLL against all 1000 satisfiable 20-variable instances,
/// with every model verified.
#[test]
#[ignore = "benchmark: use `just satlib-test`"]
fn dpll_solves_uf20() {
    run_set(&SAT_SOLVER_DPLL, "uf20-91", true, None);
}

#[test]
#[ignore = "benchmark: use `just satlib-test`"]
fn dpll_solves_uf50() {
    run_set(&SAT_SOLVER_DPLL, "uf50-218", true, None);
}

#[test]
#[ignore = "benchmark: use `just satlib-test`"]
fn dpll_refutes_uuf50() {
    run_set(&SAT_SOLVER_DPLL, "uuf50-218", false, None);
}

/// All three solvers on the same prefix of `uf20-91`, for a like-for-like
/// comparison. The sample is small because the naive solvers are `2^20`-bound:
/// they cost ~0.2 s and ~0.6 s per instance where DPLL costs ~0.2 ms.
#[test]
#[ignore = "benchmark: use `just satlib-test`"]
fn all_solvers_on_uf20_sample() {
    let sample = Some(25);
    run_set(&SAT_SOLVER_NAIVE, "uf20-91", true, sample);
    run_set(&SAT_SOLVER_NAIVE_FUNCTIONAL, "uf20-91", true, sample);
    run_set(&SAT_SOLVER_DPLL, "uf20-91", true, sample);
}

/// The naive solvers over a larger slice of `uf20-91`, as a check that the
/// sample above isn't hiding a disagreement on some instance.
#[test]
#[ignore = "benchmark: use `just satlib-test`"]
fn naive_solvers_on_uf20_slice() {
    let slice = Some(100);
    run_set(&SAT_SOLVER_NAIVE, "uf20-91", true, slice);
    run_set(&SAT_SOLVER_NAIVE_FUNCTIONAL, "uf20-91", true, slice);
}

/// Emits the dataset behind `docs/benchmarks.svg` in one pass, as CSV on stdout.
///
/// Every cell is measured over the *same* number of instances so the figure
/// compares like with like; `FIGURE_INSTANCES` is deliberately small enough that
/// the naive solvers finish. Cells the naive solvers cannot attempt at all are
/// emitted as `infeasible` rather than left out, so the figure can say so
/// explicitly instead of showing a missing bar.
///
/// Regenerate with `just satlib-figure`.
#[test]
#[ignore = "figure data: use `just satlib-figure`"]
fn figure_data() {
    const FIGURE_INSTANCES: usize = 100;
    let limit = Some(FIGURE_INSTANCES);

    println!("solver,set,verdict,instances,mean_us,worst_us");
    let mut row = |solver: &SatSolver, set: &str, expect_sat: bool, feasible: bool| {
        let verdict = if expect_sat { "SAT" } else { "UNSAT" };
        if !feasible {
            println!(
                "{},{},{},{},infeasible,infeasible",
                solver.description, set, verdict, FIGURE_INSTANCES
            );
            return;
        }
        if let Some((n, mean, worst)) = measure(solver, set, expect_sat, limit) {
            println!(
                "{},{},{},{},{},{}",
                solver.description,
                set,
                verdict,
                n,
                mean.as_secs_f64() * 1e6,
                worst.as_secs_f64() * 1e6
            );
        }
    };

    for (set, expect_sat) in [("uf20-91", true), ("uf50-218", true), ("uuf50-218", false)] {
        // 2^50 valuations is out of reach for the enumerating solvers.
        let naive_feasible = set == "uf20-91";
        row(&SAT_SOLVER_NAIVE, set, expect_sat, naive_feasible);
        row(
            &SAT_SOLVER_NAIVE_FUNCTIONAL,
            set,
            expect_sat,
            naive_feasible,
        );
        row(&SAT_SOLVER_DPLL, set, expect_sat, true);
    }
}
