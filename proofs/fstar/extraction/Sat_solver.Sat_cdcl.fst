module Sat_solver.Sat_cdcl
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Sat_solver.Expr in
  ()

let solve_sat (expr: Sat_solver.Expr.t_Expr)
    : Core_models.Option.t_Option
    (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global) =
  let e_vars:Alloc.Vec.t_Vec FStar.Char.char Alloc.Alloc.t_Global =
    Sat_solver.Expr.collect_vars (Core_models.Clone.f_clone #Sat_solver.Expr.t_Expr
          #FStar.Tactics.Typeclasses.solve
          expr
        <:
        Sat_solver.Expr.t_Expr)
  in
  Core_models.Option.Option_None
  <:
  Core_models.Option.t_Option
  (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)

let v_SAT_SOLVER_CDCL: Sat_solver.Sat.t_SatSolver =
  { Sat_solver.Sat.f_solve = solve_sat; Sat_solver.Sat.f_description = "cdcl" }
  <:
  Sat_solver.Sat.t_SatSolver
