module Sat_solver
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Nom.Error in
  let open Nom.Internal in
  let open Sat_solver.Expr in
  ()

let main (_: Prims.unit) : Prims.unit =
  let expr_sat:Sat_solver.Expr.t_Expr = Sat_solver.Expr.example_expr_sat () in
  let expr_unsat:Sat_solver.Expr.t_Expr = Sat_solver.Expr.example_expr_unsat () in
  let _:Prims.unit =
    Sat_solver.Sat.impl__test_solve Sat_solver.Sat_naive.v_SAT_SOLVER_NAIVE expr_sat
  in
  let _:Prims.unit =
    Sat_solver.Sat.impl__test_solve Sat_solver.Sat_naive.v_SAT_SOLVER_NAIVE expr_unsat
  in
  let res:Core_models.Result.t_Result (string & Sat_solver.Expr.t_Expr)
    (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)) =
    Sat_solver.Expr.parse_expr "~(~x & ~(y | z))"
  in
  let args:Core_models.Result.t_Result (string & Sat_solver.Expr.t_Expr)
    (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)) =
    res
    <:
    Core_models.Result.t_Result (string & Sat_solver.Expr.t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
  in
  let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
    let list =
      [
        Core_models.Fmt.Rt.impl__new_debug #(Core_models.Result.t_Result
              (string & Sat_solver.Expr.t_Expr)
              (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
          args
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list
  in
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list = [""; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          args
        <:
        Core_models.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  ()
