module Sat_solver
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let main (_: Prims.unit) : Prims.unit =
  let expr_sat:Sat_solver.Expr.t_Expr = Sat_solver.Sat.example_sat () in
  let expr_unsat:Sat_solver.Expr.t_Expr = Sat_solver.Sat.example_unsat () in
  let _:Prims.unit =
    Sat_solver.Sat.impl__test_solve Sat_solver.Sat_naive.v_SAT_SOLVER_NAIVE expr_sat
  in
  let _:Prims.unit =
    Sat_solver.Sat.impl__test_solve Sat_solver.Sat_naive.v_SAT_SOLVER_NAIVE expr_unsat
  in
  ()
