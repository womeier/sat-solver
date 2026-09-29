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
//! Only DPLL and CDCL can attempt the 50-variable sets: `naive` enumerates all
//! `2^n` valuations, so 50 variables is out of reach by roughly ten orders of
//! magnitude. It is exercised on `uf20-91` instead.
//!
//! Run the heavy sets (they are `#[ignore]`d) with `just satlib-test`, which
//! builds in release mode -- a debug build is ~20x slower and makes even the
//! 20-variable set tedious.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use sat_solver::dimacs::parse_dimacs;
use sat_solver::expr::{Expr, Map, evaluate};
use sat_solver::sat::SatSolver;
use sat_solver::sat_cdcl::SAT_SOLVER_CDCL;
use sat_solver::sat_dpll::{SAT_SOLVER_DPLL, SAT_SOLVER_DPLL_NAIVE};
use sat_solver::sat_naive::SAT_SOLVER_NAIVE;

const SATLIB: &str = "benchmarks/satlib";

/// Per-instance budget for the env-driven ladder runs, in seconds; `SATLIB_CAP=0`
/// removes it. Ten seconds is chosen to be far above the mean of any set the
/// solver handles comfortably and far below the tail of the first set it does
/// not, so a capped run reads as "how far up the ladder does this get".
const DEFAULT_CAP_S: u64 = 10;

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

/// The naive CNF transformation over all three sets. SATLIB instances arrive
/// already in CNF, where the hybrid's rule never names anything -- so the
/// non-default arm should reproduce the default encoding clause for clause and
/// land on the same timings. That is what made swapping the default free here,
/// and it is what would break first if the decision rule ever changed. (The
/// third arm, `Transform::Tseitin`, is ~30x slower on these sets, because it
/// names every node of an input that needed no naming.)
#[test]
#[ignore = "benchmark: use `just satlib-test`"]
fn dpll_naive_arm_matches_the_default_encoding() {
    run_set(&SAT_SOLVER_DPLL_NAIVE, "uf20-91", true, None);
    run_set(&SAT_SOLVER_DPLL_NAIVE, "uf50-218", true, None);
    run_set(&SAT_SOLVER_DPLL_NAIVE, "uuf50-218", false, None);
}

/// CDCL over the same three sets DPLL is measured on. Both search the same CNF
/// (`sat_dpll::encode` under `Transform::Hybrid`), so these numbers compare the
/// two *searches*: clause learning against chronological backtracking.
#[test]
#[ignore = "benchmark: use `just satlib-test`"]
fn cdcl_solves_uf20() {
    run_set(&SAT_SOLVER_CDCL, "uf20-91", true, None);
}

#[test]
#[ignore = "benchmark: use `just satlib-test`"]
fn cdcl_solves_uf50() {
    run_set(&SAT_SOLVER_CDCL, "uf50-218", true, None);
}

/// The set where learning should show: refuting an instance means exhausting the
/// search space, and a learned clause prunes every branch that would have failed
/// for the same reason.
#[test]
#[ignore = "benchmark: use `just satlib-test`"]
fn cdcl_refutes_uuf50() {
    run_set(&SAT_SOLVER_CDCL, "uuf50-218", false, None);
}

/// Every solver on the same prefix of `uf20-91`, for a like-for-like comparison.
/// The sample is small because `naive` is `2^20`-bound: it costs ~0.2 s per
/// instance where the other two cost well under a millisecond.
#[test]
#[ignore = "benchmark: use `just satlib-test`"]
fn all_solvers_on_uf20_sample() {
    let sample = Some(25);
    run_set(&SAT_SOLVER_NAIVE, "uf20-91", true, sample);
    run_set(&SAT_SOLVER_DPLL, "uf20-91", true, sample);
    run_set(&SAT_SOLVER_CDCL, "uf20-91", true, sample);
}

/// `naive` over a larger slice of `uf20-91`, as a check that the sample above
/// isn't hiding a disagreement on some instance.
#[test]
#[ignore = "benchmark: use `just satlib-test`"]
fn naive_solver_on_uf20_slice() {
    run_set(&SAT_SOLVER_NAIVE, "uf20-91", true, Some(100));
}

/* Per-instance timeouts, and why they need a second process.

A solver call here is a plain function with no interruption point, so a worker
*thread* that runs past its budget cannot be reclaimed -- it keeps a core busy
for the rest of the process and quietly inflates every measurement after it. A
worker *process* can simply be killed. So one child per instance, which also
keeps the timing honest: the child times its own solve and prints it, so the
parent's ~2 ms of spawn overhead never enters a measurement, only the wall clock
of the run.

The child is this same test binary re-executed with `SATLIB_SOLVE_ONE` set, not a
separate `[[bin]]`: `just extract` moves `src/main.rs` aside because charon treats
whichever cargo target it compiles as primary and starves the others of their
bodies, and a second binary would silently break that. */

/// Resolves a solver by the name `SATLIB_SOLVER` uses. `SatSolver` carries a
/// lifetime for its description, so both have to be spelled `'static` -- eliding
/// the inner one ties the result to the name that was looked up.
fn solver_by_name(name: &str) -> &'static SatSolver<'static> {
    match name {
        "cdcl" => &SAT_SOLVER_CDCL,
        "dpll" => &SAT_SOLVER_DPLL,
        "dpll-naive" => &SAT_SOLVER_DPLL_NAIVE,
        "naive" => &SAT_SOLVER_NAIVE,
        other => panic!("unknown solver {other:?}: want cdcl, dpll, dpll-naive or naive"),
    }
}

/// How long a solve has to take before one measurement of it is trustworthy. A
/// fresh process has cold caches, a cold allocator and an untrained branch
/// predictor, which costs a fixed few hundred microseconds -- nothing next to a
/// ten-second instance, but a factor of three on a 57 µs one. Below this, the
/// worker repeats the solve and divides, the way any microbenchmark has to.
const REPEAT_BELOW: Duration = Duration::from_millis(5);

/// The worker half: solve the one instance named by `SATLIB_SOLVE_ONE` and print
/// its solve time in nanoseconds. Exits non-zero if the model does not check out,
/// which is how the parent learns about it.
#[test]
#[ignore = "internal: the worker half of `from_env`'s per-instance cap"]
fn solve_one() {
    let Ok(path) = std::env::var("SATLIB_SOLVE_ONE") else {
        eprintln!("skipping: SATLIB_SOLVE_ONE is not set -- this is not a standalone test");
        return;
    };
    let solver = solver_by_name(&std::env::var("SATLIB_SOLVER").unwrap_or("cdcl".into()));
    let expect_sat = std::env::var("SATLIB_EXPECT").as_deref() != Ok("unsat");
    let path = PathBuf::from(path);
    let expr = read_instance(&path);

    // The first solve is the one that gets its model checked; the repetitions,
    // if any, only have to be timed.
    let mut elapsed = check(solver, &expr, &path, expect_sat);
    if elapsed < REPEAT_BELOW && !elapsed.is_zero() {
        let reps = (REPEAT_BELOW.as_nanos() / elapsed.as_nanos()).clamp(1, 200) as u32;
        let start = Instant::now();
        for _ in 0..reps {
            std::hint::black_box((solver.solve)(&expr));
        }
        elapsed = start.elapsed() / reps;
    }
    println!("SOLVED {}", elapsed.as_nanos());
}

/// Solves one instance in a child, or `None` if it outran `cap`.
fn solve_capped(
    solver: &str,
    path: &Path,
    expect_sat: bool,
    cap: Duration,
) -> Option<Duration> {
    let exe = std::env::current_exe().expect("current_exe");
    let mut child = Command::new(exe)
        .args(["solve_one", "--exact", "--ignored", "--nocapture"])
        .env("SATLIB_SOLVE_ONE", path)
        .env("SATLIB_SOLVER", solver)
        .env("SATLIB_EXPECT", if expect_sat { "sat" } else { "unsat" })
        .env_remove("SATLIB_SET")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("cannot spawn the worker");

    let deadline = Instant::now() + cap;
    let status = loop {
        match child.try_wait().expect("try_wait on the worker") {
            Some(status) => break status,
            None if Instant::now() >= deadline => {
                let _ = child.kill();
                let _ = child.wait();
                return None;
            }
            // The worker writes one short line, well under a pipe buffer, so
            // polling without draining stdout cannot deadlock.
            None => std::thread::sleep(Duration::from_millis(2)),
        }
    };

    let mut out = String::new();
    child
        .stdout
        .take()
        .expect("worker stdout")
        .read_to_string(&mut out)
        .expect("read worker stdout");
    assert!(
        status.success(),
        "[{solver}] {} failed in the worker:\n{out}",
        path.display()
    );
    let nanos = out
        .lines()
        .find_map(|l| l.strip_prefix("SOLVED "))
        .unwrap_or_else(|| panic!("worker printed no SOLVED line for {}", path.display()))
        .trim()
        .parse::<u64>()
        .expect("SOLVED is not a number");
    Some(Duration::from_nanos(nanos))
}

/// What a capped run of one set produced.
struct Capped {
    attempted: usize,
    solved: Vec<Duration>,
}

impl Capped {
    /// The median over the solved instances, which is the statistic the figure
    /// plots: a cap censors the slow tail, so a mean is biased by exactly the
    /// instances it cannot see, while the median stays exact as long as more than
    /// half the set came in under the cap.
    fn median(&self) -> Duration {
        self.solved[self.solved.len() / 2]
    }

    fn mean(&self) -> Duration {
        self.solved.iter().sum::<Duration>() / self.solved.len() as u32
    }

    fn worst(&self) -> Duration {
        *self.solved.last().expect("no solved instances")
    }
}

/// Runs a set under a per-instance cap. Instances that outrun it are counted, not
/// fatal: where a solver starts missing instances is the interesting part of the
/// curve, and stopping at the first one would throw that away.
fn measure_capped(solver: &str, set: &str, expect_sat: bool, limit: Option<usize>, cap: Duration)
    -> Option<Capped>
{
    let mut paths = instances(set)?;
    if let Some(n) = limit {
        paths.truncate(n);
    }
    let attempted = paths.len();
    let mut solved: Vec<Duration> = paths
        .iter()
        .filter_map(|p| solve_capped(solver, p, expect_sat, cap))
        .collect();
    solved.sort();
    Some(Capped { attempted, solved })
}

/* The scaling ladder.

SATLIB's RND3SAT family goes on well past 50 variables -- 75, 100, 125, 150,
175, 200, 225, 250, all at the same 4.26 ratio -- and that is where the gap
between chronological backtracking and clause learning stops being a constant
factor. Those sets are not measured by the tests above because they are not all
feasible for every solver, and because "not feasible" here means *hours*, not
seconds: one process per set, killed from outside, is the only way to explore
the ladder without a run that never ends.

Hence this one env-driven test rather than a test per set:

    SATLIB_SOLVER=cdcl SATLIB_SET=uf100-430 SATLIB_LIMIT=20 SATLIB_CAP=10 \
      cargo test --release --test satlib from_env -- --ignored --nocapture

`just satlib-ladder` drives it, and `just satlib-scaling` turns it into the
dataset behind `docs/scaling.svg`. The expected verdict comes from the set name --
SATLIB spells unsatisfiable sets `uuf*` -- so there is nothing to keep in sync.

Two lines per set: one for a person, and one CSV row for the figure. */
#[test]
#[ignore = "benchmark: env-driven, use `just satlib-ladder`"]
fn from_env() {
    let Ok(set) = std::env::var("SATLIB_SET") else {
        eprintln!("skipping: set SATLIB_SET (also SATLIB_SOLVER, SATLIB_LIMIT, SATLIB_CAP)");
        return;
    };
    let name = std::env::var("SATLIB_SOLVER").unwrap_or("cdcl".into());
    let solver = solver_by_name(&name);
    let limit = std::env::var("SATLIB_LIMIT")
        .ok()
        .map(|s| s.parse().expect("SATLIB_LIMIT is not a number"));
    let cap_s: u64 = std::env::var("SATLIB_CAP")
        .ok()
        .map(|s| s.parse().expect("SATLIB_CAP is not a number"))
        .unwrap_or(DEFAULT_CAP_S);
    let expect_sat = !set.starts_with("uuf");
    let vars: u32 = set
        .trim_start_matches('u')
        .trim_start_matches('f')
        .split('-')
        .next()
        .and_then(|d| d.parse().ok())
        .expect("cannot read a variable count out of the set name");
    let verdict = if expect_sat { "SAT" } else { "UNSAT" };

    // No cap: the old uncapped path, which is still what the named tests use.
    if cap_s == 0 {
        run_set(solver, &set, expect_sat, limit);
        return;
    }

    let cap = Duration::from_secs(cap_s);
    let Some(r) = measure_capped(&name, &set, expect_sat, limit, cap) else {
        return;
    };
    if r.solved.is_empty() {
        println!(
            "[{name}] {set}: solved 0/{} within {cap_s}s",
            r.attempted
        );
        println!("{name},{set},{vars},{verdict},0,{},,,", r.attempted);
        return;
    }
    println!(
        "[{name}] {set}: solved {}/{} within {cap_s}s, median {:.2?}, mean {:.2?}, worst {:.2?}",
        r.solved.len(),
        r.attempted,
        r.median(),
        r.mean(),
        r.worst()
    );
    let ms = |d: Duration| d.as_secs_f64() * 1e3;
    println!(
        "{name},{set},{vars},{verdict},{},{},{:.4},{:.4},{:.4}",
        r.solved.len(),
        r.attempted,
        ms(r.median()),
        ms(r.mean()),
        ms(r.worst())
    );
}
