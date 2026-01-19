use crate::expr::*;
use crate::sat::SatSolver;

// TODO improve performance (reduce cloning)
fn naive_create_possible_valuations(vars: &[char]) -> Vec<Map> {
    if vars.is_empty() {
        return vec![Map::new()];
    }

    let v = &vars[0];
    let vs = &vars[1..];

    let evals1 = naive_create_possible_valuations(vs);

    let mut evals1: Vec<Map> = evals1
        .iter()
        .map(|e| {
            let mut e_new = e.clone();
            e_new.insert(*v, true);
            e_new
        })
        .collect();

    let evals2: Vec<Map> = evals1
        .iter()
        .map(|e| {
            let mut e_new = e.clone();
            e_new.insert(*v, false);
            e_new
        })
        .collect();

    evals1.extend(evals2);
    evals1.to_vec()
}

fn solve_sat(expr: &Expr) -> Option<Map> {
    let vars = collect_vars(expr.clone());
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
