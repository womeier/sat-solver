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
