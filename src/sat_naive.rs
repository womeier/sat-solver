#![allow(dead_code)]
use crate::expr::*;
use crate::sat::SatSolver;

fn initial_valuation(vars: &[char]) -> Map {
    let mut map = Map::new();

    for v in vars {
        map.insert(*v, false);
    }

    map
}

fn check_possible_valuations(expr: &Expr, vars: &[char], val: &mut Map) -> bool {
    if vars.is_empty() {
        return evaluate(expr, val).unwrap();
    }

    let v = &vars[0];
    let vs = &vars[1..];

    val.insert(*v, false);
    if check_possible_valuations(expr, vs, val) {
        return true;
    }

    val.insert(*v, true);
    if check_possible_valuations(expr, vs, val) {
        return true;
    }

    false
}

fn solve_sat(expr: &Expr) -> Option<Map> {
    let vars = collect_vars(expr.clone());
    let mut val = initial_valuation(&vars);

    if check_possible_valuations(expr, &vars, &mut val) {
        Some(val)
    } else {
        None
    }
}

pub static SAT_SOLVER_NAIVE: SatSolver = SatSolver {
    solve: solve_sat,
    description: "naive",
};
