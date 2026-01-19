use sat_solver::sat::*;
// use sat_solver::sat_cdcl::SAT_SOLVER_CDCL;
// use sat_solver::sat_dpll::SAT_SOLVER_DPLL;
use sat_solver::sat_naive::SAT_SOLVER_NAIVE;
// use sat_solver::sat_naive_functional::SAT_SOLVER_NAIVE_FUNCTIONAL;

fn main() {
    let expr_sat = example_sat();
    let expr_unsat = example_unsat();

    SAT_SOLVER_NAIVE.test_solve(&expr_sat);
    SAT_SOLVER_NAIVE.test_solve(&expr_unsat);

    // SAT_SOLVER_NAIVE_FUNCTIONAL.test_solve(&expr);
    // SAT_SOLVER_DPLL.test_solve(&expr);
    // SAT_SOLVER_CDCL.test_solve(&expr);
}
