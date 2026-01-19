module Sat_solver.Sat
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Sat_solver.Expr in
  ()

type t_SatSolver = {
  f_solve:Sat_solver.Expr.t_Expr
    -> Core_models.Option.t_Option
      (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global);
  f_description:string
}

let impl__test_solve (self: t_SatSolver) (expr: Sat_solver.Expr.t_Expr) : Prims.unit =
  let res:Core_models.Option.t_Option
  (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global) =
    self.f_solve expr
  in
  let args:(string & Sat_solver.Expr.t_Expr &
    Core_models.Option.t_Option
    (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)) =
    self.f_description, expr, res
    <:
    (string & Sat_solver.Expr.t_Expr &
      Core_models.Option.t_Option
      (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
  in
  let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 3) =
    let list =
      [
        Core_models.Fmt.Rt.impl__new_display #string args._1;
        Core_models.Fmt.Rt.impl__new_display #Sat_solver.Expr.t_Expr args._2;
        Core_models.Fmt.Rt.impl__new_debug #(Core_models.Option.t_Option
            (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
          args._3
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
    Rust_primitives.Hax.array_of_list 3 list
  in
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 4)
          (mk_usize 3)
          (let list = ["["; "]: "; ": "; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
            Rust_primitives.Hax.array_of_list 4 list)
          args
        <:
        Core_models.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  ()

let example_sat (_: Prims.unit) : Sat_solver.Expr.t_Expr =
  Sat_solver.Expr.Expr_Neg
  (Sat_solver.Expr.Expr_Conj
      (Sat_solver.Expr.Expr_Variable 'Y'
        <:
        Alloc.Boxed.t_Box Sat_solver.Expr.t_Expr Alloc.Alloc.t_Global)
      (Sat_solver.Expr.Expr_Conj
          (Sat_solver.Expr.Expr_True
            <:
            Alloc.Boxed.t_Box Sat_solver.Expr.t_Expr Alloc.Alloc.t_Global)
          (Sat_solver.Expr.Expr_Disj
              (Sat_solver.Expr.Expr_Variable 'X'
                <:
                Alloc.Boxed.t_Box Sat_solver.Expr.t_Expr Alloc.Alloc.t_Global)
              (Sat_solver.Expr.Expr_False
                <:
                Alloc.Boxed.t_Box Sat_solver.Expr.t_Expr Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box Sat_solver.Expr.t_Expr Alloc.Alloc.t_Global)
        <:
        Alloc.Boxed.t_Box Sat_solver.Expr.t_Expr Alloc.Alloc.t_Global)
    <:
    Alloc.Boxed.t_Box Sat_solver.Expr.t_Expr Alloc.Alloc.t_Global)
  <:
  Sat_solver.Expr.t_Expr

let example_unsat (_: Prims.unit) : Sat_solver.Expr.t_Expr =
  Sat_solver.Expr.Expr_Conj
    (Sat_solver.Expr.Expr_Variable 'X'
      <:
      Alloc.Boxed.t_Box Sat_solver.Expr.t_Expr Alloc.Alloc.t_Global)
    (Sat_solver.Expr.Expr_Neg
      (Sat_solver.Expr.Expr_Variable 'X'
        <:
        Alloc.Boxed.t_Box Sat_solver.Expr.t_Expr Alloc.Alloc.t_Global)
      <:
      Alloc.Boxed.t_Box Sat_solver.Expr.t_Expr Alloc.Alloc.t_Global)
  <:
  Sat_solver.Expr.t_Expr
