use crate::expr::{Expr, Map};
use crate::sat_result::SatResult;

pub struct SatSolver<'a> {
    pub solve: fn(&Expr) -> SatResult<Map>,
    pub description: &'a str,
}

impl SatSolver<'_> {
    pub fn test_solve(&self, expr: &Expr) {
        let res = (self.solve)(expr);

        println!("[{}]: {expr}: {res:?}", self.description);
    }
}
