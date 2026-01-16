#![allow(dead_code)]
use crate::expr::*;

pub fn solve_sat(expr: Expr) -> Option<Map> {
    let _vars = collect_vars(expr.clone());

    None
}

pub fn example_solve_sat_cdcl() {
    let expr = Expr::Neg(Box::new(Expr::Conj(
        Box::new(Expr::Variable('Y')),
        Box::new(Expr::Conj(
            Box::new(Expr::True),
            Box::new(Expr::Disj(
                Box::new(Expr::Variable('X')),
                Box::new(Expr::False),
            )),
        )),
    )));

    let res = solve_sat(expr.clone());
    println!("{expr}: {res:?}");
}
