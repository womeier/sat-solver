use crate::expr::*;
use crate::sat::SatSolver;

// TODO improve performance (reduce cloning)
fn naive_create_possible_valuations(vars: &[u8]) -> Vec<Map> {
    if vars.is_empty() {
        let mut base = Vec::new();
        base.push(Map::new());
        return base;
    }

    let v = vars[0];
    let vs = &vars[1..];

    let rest = naive_create_possible_valuations(vs);

    let mut result: Vec<Map> = Vec::new();

    for e in rest.iter() {
        let mut e_true = e.clone();
        e_true.insert(v, true);
        result.push(e_true);

        let mut e_false = e.clone();
        e_false.insert(v, false);
        result.push(e_false);
    }

    result
}

pub fn solve_sat(expr: &Expr) -> Option<Map> {
    let vars = collect_vars(expr);
    let valuations = naive_create_possible_valuations(&vars);

    for v in valuations {
        let result = evaluate(expr, &v);
        if result.is_ok_and(|r| r) {
            return Some(v);
        }
    }
    None
}

pub static SAT_SOLVER_NAIVE_FUNCTIONAL: SatSolver = SatSolver {
    solve: solve_sat,
    description: "naive functional",
};
