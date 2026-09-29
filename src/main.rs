//! A DIMACS CNF front end for `sat_cdcl`.
//!
//! Reads a `.cnf` file (or stdin), solves it, and reports in the SAT
//! competition's output format: an `s` line, and on a satisfiable instance a
//! `v` line holding the model. Exit status follows the same convention --
//! 10 for satisfiable, 20 for unsatisfiable, 0 for an undecided run.
//!
//! The formula goes to [`solve_cnf`] as the `Cnf` the parser built, not as an
//! `Expr` re-encoded back to CNF. That is deliberate: `solve_cnf`'s soundness
//! and completeness theorems assume nothing at all about their input, whereas
//! the `Expr` entry point inherits the naive transformation's worst-case blowup
//! bound. Parsing straight to `Cnf` is what puts this program's answers inside
//! the verified statement.

use sat_solver::cnf::{Cnf, eval_cnf};
use sat_solver::dimacs::parse_dimacs_cnf;
use sat_solver::expr::Map;
use sat_solver::sat_cdcl::{solve_cnf, solve_cnf_unchecked};
use sat_solver::sat_result::SatResult;
use std::io::Read;
use std::process::ExitCode;

const USAGE: &str = "\
usage: sat-solver [--no-limit-checks] [FILE]

  Solves a DIMACS CNF formula, read from FILE or from stdin.

  --no-limit-checks   Skip the clause-length check on the input. THIS VOIDS THE
                      VERIFIED GUARANTEE: conflict analysis counts a clause's
                      literals in an i32, and the check is what rules out the
                      overflow. Nothing short of a two-billion-literal clause
                      triggers it, and skipping the check saves one pass over
                      the input.

  Exit status: 10 satisfiable, 20 unsatisfiable, 0 undecided, 1 error.
";

fn main() -> ExitCode {
    let mut path: Option<String> = None;
    let mut checks = true;

    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--no-limit-checks" => checks = false,
            "-h" | "--help" => {
                print!("{USAGE}");
                return ExitCode::SUCCESS;
            }
            other if other.starts_with('-') => {
                eprintln!("sat-solver: unknown option {other:?}\n");
                eprint!("{USAGE}");
                return ExitCode::FAILURE;
            }
            other => {
                if path.is_some() {
                    eprintln!("sat-solver: more than one input file\n");
                    eprint!("{USAGE}");
                    return ExitCode::FAILURE;
                }
                path = Some(other.to_string());
            }
        }
    }

    let input = match read_input(path.as_deref()) {
        Ok(text) => text,
        Err(e) => {
            eprintln!("sat-solver: {e}");
            return ExitCode::FAILURE;
        }
    };

    let cnf = match parse_dimacs_cnf(&input) {
        Ok(cnf) => cnf,
        Err(e) => {
            eprintln!("sat-solver: {e}");
            return ExitCode::FAILURE;
        }
    };

    let result = if checks {
        solve_cnf(&cnf)
    } else {
        eprintln!(
            "sat-solver: warning: --no-limit-checks is set, so this run is not \
             covered by the correctness theorems"
        );
        solve_cnf_unchecked(&cnf)
    };

    match result {
        SatResult::Unsat => {
            println!("s UNSATISFIABLE");
            ExitCode::from(20)
        }
        SatResult::Unknown => {
            println!("s UNKNOWN");
            ExitCode::SUCCESS
        }
        SatResult::Sat(model) => {
            // The solver is verified; the parsing and printing around it are
            // not, so the model is checked against the CNF as parsed before it
            // is reported. A failure here is a bug in this file or in
            // `dimacs.rs`, never in `sat_cdcl`.
            if let Err(e) = check_model(&cnf, &model) {
                eprintln!("sat-solver: internal error: {e}");
                return ExitCode::FAILURE;
            }
            println!("s SATISFIABLE");
            println!("{}", render_model(&model));
            ExitCode::from(10)
        }
    }
}

fn read_input(path: Option<&str>) -> Result<String, String> {
    match path {
        Some(p) => std::fs::read_to_string(p).map_err(|e| format!("{p}: {e}")),
        None => {
            let mut text = String::new();
            std::io::stdin()
                .read_to_string(&mut text)
                .map_err(|e| format!("stdin: {e}"))?;
            Ok(text)
        }
    }
}

fn check_model(cnf: &Cnf, model: &[(u16, bool)]) -> Result<(), String> {
    let mut val = Map::new();
    for (var, value) in model {
        val.insert(*var, *value);
    }
    match eval_cnf(cnf, &val) {
        Ok(true) => Ok(()),
        Ok(false) => Err("the returned model does not satisfy the formula".to_string()),
        Err(()) => Err("the returned model leaves a variable unassigned".to_string()),
    }
}

/// The `v` line: the model as DIMACS literals, `v` for a variable assigned
/// `true` and `-v` for one assigned `false`, terminated by `0`. A CNF over no
/// variables at all has an empty model, and then the line is just `v 0`.
fn render_model(model: &[(u16, bool)]) -> String {
    let mut line = String::from("v");
    for (var, value) in model {
        if *value {
            line.push_str(&format!(" {var}"));
        } else {
            line.push_str(&format!(" -{var}"));
        }
    }
    line.push_str(" 0");
    line
}
