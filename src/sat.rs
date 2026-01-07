#![allow(dead_code)]
use crate::expr::*;

// TODO improve performance
fn naive_create_possible_valuations(vars: &[String]) -> Vec<Map> {
    match &vars {
        [] => vec![Map::new()],
        [v, vs @ ..] => {
            let mut evals1 = naive_create_possible_valuations(vs);
            let mut evals2 = evals1.clone();

            for eval in evals1.iter_mut() {
                eval.insert(v.to_string(), true);
            }

            for eval in evals2.iter_mut() {
                eval.insert(v.to_string(), false);
            }
            evals1.extend(evals2);
            evals1
        }
    }
}

fn naive_solve_sat(expr: Expr) -> Option<Map> {
    let vars = collect_vars(expr.clone());
    let valuations = naive_create_possible_valuations(&vars);

    for v in valuations {
        if let Ok(result) = evaluate(expr.clone(), &v)
            && result
        {
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
