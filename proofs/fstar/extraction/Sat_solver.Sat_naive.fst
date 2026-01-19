module Sat_solver.Sat_naive
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Sat_solver.Expr in
  ()

let initial_valuation (vars: t_Slice FStar.Char.char)
    : Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
  let map:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
    Alloc.Collections.Btree.Map.impl_18__new #FStar.Char.char #bool ()
  in
  let map:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
    Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
            FStar.Char.char)
          #FStar.Tactics.Typeclasses.solve
          vars
        <:
        Core_models.Slice.Iter.t_Iter FStar.Char.char)
      map
      (fun map v ->
          let map:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
            map
          in
          let v:FStar.Char.char = v in
          let
          (tmp0: Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global),
          (out: Core_models.Option.t_Option bool) =
            Alloc.Collections.Btree.Map.impl_20__insert #FStar.Char.char
              #bool
              #Alloc.Alloc.t_Global
              map
              v
              false
          in
          let map:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
            tmp0
          in
          let _:Core_models.Option.t_Option bool = out in
          map)
  in
  map

let rec check_possible_valuations
      (expr: Sat_solver.Expr.t_Expr)
      (vars: t_Slice FStar.Char.char)
      (v_val: Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
    : (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global & bool) =
  if Core_models.Slice.impl__is_empty #FStar.Char.char vars
  then
    v_val,
    Core_models.Result.impl__unwrap #bool
      #Alloc.String.t_String
      (Sat_solver.Expr.evaluate expr v_val <: Core_models.Result.t_Result bool Alloc.String.t_String
      )
    <:
    (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global & bool)
  else
    let v:FStar.Char.char = vars.[ mk_usize 0 ] in
    let vs:t_Slice FStar.Char.char =
      vars.[ { Core_models.Ops.Range.f_start = mk_usize 1 }
        <:
        Core_models.Ops.Range.t_RangeFrom usize ]
    in
    let
    (tmp0: Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global),
    (out: Core_models.Option.t_Option bool) =
      Alloc.Collections.Btree.Map.impl_20__insert #FStar.Char.char
        #bool
        #Alloc.Alloc.t_Global
        v_val
        v
        false
    in
    let v_val:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
      tmp0
    in
    let _:Core_models.Option.t_Option bool = out in
    let
    (tmp0: Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global),
    (out: bool) =
      check_possible_valuations expr vs v_val
    in
    let v_val:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
      tmp0
    in
    if out
    then
      v_val, true
      <:
      (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global & bool)
    else
      let
      (tmp0: Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global),
      (out: Core_models.Option.t_Option bool) =
        Alloc.Collections.Btree.Map.impl_20__insert #FStar.Char.char
          #bool
          #Alloc.Alloc.t_Global
          v_val
          v
          true
      in
      let v_val:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
        tmp0
      in
      let _:Core_models.Option.t_Option bool = out in
      let
      (tmp0: Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global),
      (out: bool) =
        check_possible_valuations expr vs v_val
      in
      let v_val:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
        tmp0
      in
      if out
      then
        v_val, true
        <:
        (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global & bool)
      else
        let hax_temp_output:bool = false in
        v_val, hax_temp_output
        <:
        (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global & bool)

let solve_sat (expr: Sat_solver.Expr.t_Expr)
    : Core_models.Option.t_Option
    (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global) =
  let vars:Alloc.Vec.t_Vec FStar.Char.char Alloc.Alloc.t_Global =
    Sat_solver.Expr.collect_vars (Core_models.Clone.f_clone #Sat_solver.Expr.t_Expr
          #FStar.Tactics.Typeclasses.solve
          expr
        <:
        Sat_solver.Expr.t_Expr)
  in
  let v_val:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
    initial_valuation (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec FStar.Char.char
              Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          vars
        <:
        t_Slice FStar.Char.char)
  in
  let
  (tmp0: Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global),
  (out: bool) =
    check_possible_valuations expr
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec FStar.Char.char Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          vars
        <:
        t_Slice FStar.Char.char)
      v_val
  in
  let v_val:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
    tmp0
  in
  if out
  then
    Core_models.Option.Option_Some v_val
    <:
    Core_models.Option.t_Option
    (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
  else
    Core_models.Option.Option_None
    <:
    Core_models.Option.t_Option
    (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)

let v_SAT_SOLVER_NAIVE: Sat_solver.Sat.t_SatSolver =
  { Sat_solver.Sat.f_solve = solve_sat; Sat_solver.Sat.f_description = "naive" }
  <:
  Sat_solver.Sat.t_SatSolver
