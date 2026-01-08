#![allow(dead_code)]
use crate::expr::*;

// TODO improve performance (reduce cloning)
fn naive_create_possible_valuations(vars: &[String]) -> Vec<Map> {
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
            e_new.insert(v.to_string(), true);
            e_new
        })
        .collect();

    let evals2: Vec<Map> = evals1
        .iter()
        .map(|e| {
            let mut e_new = e.clone();
            e_new.insert(v.to_string(), false);
            e_new
        })
        .collect();

    evals1.extend(evals2);
    evals1.to_vec()
}

pub fn naive_solve_sat(expr: Expr) -> Option<Map> {
    let vars = collect_vars(expr.clone());
    let valuations = naive_create_possible_valuations(&vars);

    for v in valuations {
        let result = evaluate(expr.clone(), &v);
        if result.is_ok_and(|r| r) {
            return Some(v);
        }
    }
    None
}

pub fn example_naive_solve_sat() {
    let expr = Expr::Neg(Box::new(Expr::Conj(
        Box::new(Expr::Variable("Y".to_string())),
        Box::new(Expr::Conj(
            Box::new(Expr::True),
            Box::new(Expr::Disj(
                Box::new(Expr::Variable("X".to_string())),
                Box::new(Expr::False),
            )),
        )),
    )));

    let res = naive_solve_sat(expr.clone());
    println!("{expr}: {res:?}");
}
