//! The DIMACS front end, end to end: what it prints and what it exits with.
//!
//! The exit codes are the SAT competitions' -- 10 satisfiable, 20 unsatisfiable,
//! 0 undecided -- so a harness can read the verdict without parsing stdout.

use std::io::Write;
use std::process::{Command, Output, Stdio};

fn run(args: &[&str], stdin: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_sat-solver"))
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("cannot run sat-solver");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).to_string()
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).to_string()
}

#[test]
fn satisfiable_prints_a_model_and_exits_10() {
    let o = run(&[], "p cnf 3 3\n1 -2 0\n2 3 0\n-1 -3 0\n");
    assert_eq!(o.status.code(), Some(10));
    let out = stdout(&o);
    assert!(out.starts_with("s SATISFIABLE\n"), "{out}");

    // the `v` line names every variable once, signed by its value, and ends in 0
    let v = out.lines().nth(1).expect("a v line");
    let lits: Vec<i32> = v
        .strip_prefix("v ")
        .expect("v line")
        .split_whitespace()
        .map(|t| t.parse().unwrap())
        .collect();
    assert_eq!(lits.last(), Some(&0));
    let mut vars: Vec<i32> = lits[..lits.len() - 1].iter().map(|l| l.abs()).collect();
    vars.sort();
    assert_eq!(vars, vec![1, 2, 3]);
}

#[test]
fn a_formula_over_no_variables_prints_a_bare_v_line() {
    let o = run(&[], "p cnf 0 0\n");
    assert_eq!(o.status.code(), Some(10));
    assert_eq!(stdout(&o), "s SATISFIABLE\nv 0\n");
}

#[test]
fn unsatisfiable_exits_20() {
    let o = run(&[], "p cnf 1 2\n1 0\n-1 0\n");
    assert_eq!(o.status.code(), Some(20));
    assert_eq!(stdout(&o), "s UNSATISFIABLE\n");
}

#[test]
fn an_empty_clause_is_unsatisfiable() {
    // DIMACS `0` alone is the empty clause. Worth its own test: it is the CNF that
    // makes `search.spec`'s "no clause is falsified" hypothesis unstatable, and
    // `solve_cnf` has to answer for it like any other.
    let o = run(&[], "p cnf 1 2\n1 0\n0\n");
    assert_eq!(o.status.code(), Some(20));
    assert_eq!(stdout(&o), "s UNSATISFIABLE\n");
}

#[test]
fn no_limit_checks_warns_that_the_guarantee_is_gone() {
    let o = run(&["--no-limit-checks"], "p cnf 1 1\n1 0\n");
    assert_eq!(o.status.code(), Some(10));
    assert!(stdout(&o).starts_with("s SATISFIABLE\n"));
    let err = stderr(&o);
    assert!(err.contains("--no-limit-checks"), "{err}");
    assert!(
        err.contains("not covered by the correctness theorems"),
        "{err}"
    );
}

#[test]
fn the_default_run_warns_about_nothing() {
    let o = run(&[], "p cnf 1 1\n1 0\n");
    assert_eq!(o.status.code(), Some(10));
    assert_eq!(stderr(&o), "");
}

#[test]
fn a_malformed_formula_exits_1() {
    // no `p cnf` header
    let o = run(&[], "1 -2 0\n");
    assert_eq!(o.status.code(), Some(1));
    assert!(stderr(&o).contains("missing `p cnf` header"));
}

#[test]
fn a_missing_file_exits_1() {
    let o = run(&["/nonexistent-instance.cnf"], "");
    assert_eq!(o.status.code(), Some(1));
    assert!(stderr(&o).contains("/nonexistent-instance.cnf"));
}

#[test]
fn an_unknown_option_exits_1() {
    let o = run(&["--bogus"], "");
    assert_eq!(o.status.code(), Some(1));
    assert!(stderr(&o).contains("unknown option"));
}

#[test]
fn help_exits_0() {
    let o = run(&["--help"], "");
    assert_eq!(o.status.code(), Some(0));
    assert!(stdout(&o).starts_with("usage: sat-solver"));
}
