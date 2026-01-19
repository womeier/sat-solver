use crate::expr::{Expr, Map};

pub struct SatSolver<'a> {
    pub solve: fn(&Expr) -> Option<Map>,
    pub description: &'a str,
}

impl SatSolver<'_> {
    pub fn test_solve(&self, expr: &Expr) {
        let res = (self.solve)(expr);

        println!("[{}]: {expr}: {res:?}", self.description);
    }
}

pub fn example_sat() -> Expr {
    Expr::Neg(Box::new(Expr::Conj(
        Box::new(Expr::Variable('Y')),
        Box::new(Expr::Conj(
            Box::new(Expr::True),
            Box::new(Expr::Disj(
                Box::new(Expr::Variable('X')),
                Box::new(Expr::False),
            )),
        )),
    )))
}

pub fn example_unsat() -> Expr {
    Expr::Conj(
        Box::new(Expr::Variable('X')),
        Box::new(Expr::Neg(Box::new(Expr::Variable('X')))),
    )
}
