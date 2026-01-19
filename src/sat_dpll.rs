#![allow(dead_code)]
use crate::expr::*;
use crate::sat::SatSolver;

pub fn solve_sat(expr: &Expr) -> Option<Map> {
    let _vars = collect_vars(expr.clone());

    None
}

pub static SAT_SOLVER_DPLL: SatSolver = SatSolver {
    solve: solve_sat,
    description: "dpll",
};
