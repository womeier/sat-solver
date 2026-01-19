module Sat_solver.Sat_naive_functional
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Sat_solver.Expr in
  ()

let rec naive_create_possible_valuations (vars: t_Slice FStar.Char.char)
    : Alloc.Vec.t_Vec
      (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
      Alloc.Alloc.t_Global =
  if Core_models.Slice.impl__is_empty #FStar.Char.char vars
  then
    Alloc.Slice.impl__into_vec #(Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
          bool
          Alloc.Alloc.t_Global)
      #Alloc.Alloc.t_Global
      (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                  [
                    Alloc.Collections.Btree.Map.impl_18__new #FStar.Char.char #bool ()
                    <:
                    Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global
                  ]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
            <:
            Alloc.Boxed.t_Box
              (t_Array
                  (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
                  (mk_usize 1)) Alloc.Alloc.t_Global)
        <:
        Alloc.Boxed.t_Box
          (t_Slice
            (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
          Alloc.Alloc.t_Global)
  else
    let v:FStar.Char.char = vars.[ mk_usize 0 ] in
    let vs:t_Slice FStar.Char.char =
      vars.[ { Core_models.Ops.Range.f_start = mk_usize 1 }
        <:
        Core_models.Ops.Range.t_RangeFrom usize ]
    in
    let evals1:Alloc.Vec.t_Vec
      (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
      Alloc.Alloc.t_Global =
      naive_create_possible_valuations vs
    in
    let
    (evals1:
      Alloc.Vec.t_Vec
        (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
        Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
      (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
      Alloc.Alloc.t_Global =
      Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
            (Core_models.Slice.Iter.t_Iter
              (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
            (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global
                -> Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
        )
        #FStar.Tactics.Typeclasses.solve
        #(Alloc.Vec.t_Vec
            (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
            Alloc.Alloc.t_Global)
        (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
              (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
            #FStar.Tactics.Typeclasses.solve
            #(Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
            (Core_models.Slice.impl__iter #(Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                    bool
                    Alloc.Alloc.t_Global)
                (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
                        (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                            bool
                            Alloc.Alloc.t_Global) Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    evals1
                  <:
                  t_Slice
                  (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
                )
              <:
              Core_models.Slice.Iter.t_Iter
              (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
            (fun e ->
                let e:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                  bool
                  Alloc.Alloc.t_Global =
                  e
                in
                let e_new:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                  bool
                  Alloc.Alloc.t_Global =
                  Core_models.Clone.f_clone #(Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                        bool
                        Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    e
                in
                let
                (tmp0:
                  Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global),
                (out: Core_models.Option.t_Option bool) =
                  Alloc.Collections.Btree.Map.impl_20__insert #FStar.Char.char
                    #bool
                    #Alloc.Alloc.t_Global
                    e_new
                    v
                    true
                in
                let e_new:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                  bool
                  Alloc.Alloc.t_Global =
                  tmp0
                in
                let _:Core_models.Option.t_Option bool = out in
                e_new)
          <:
          Core_models.Iter.Adapters.Map.t_Map
            (Core_models.Slice.Iter.t_Iter
              (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
            (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global
                -> Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
        )
    in
    let
    (evals2:
      Alloc.Vec.t_Vec
        (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
        Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
      (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
      Alloc.Alloc.t_Global =
      Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Map.t_Map
            (Core_models.Slice.Iter.t_Iter
              (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
            (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global
                -> Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
        )
        #FStar.Tactics.Typeclasses.solve
        #(Alloc.Vec.t_Vec
            (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
            Alloc.Alloc.t_Global)
        (Core_models.Iter.Traits.Iterator.f_map #(Core_models.Slice.Iter.t_Iter
              (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
            #FStar.Tactics.Typeclasses.solve
            #(Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
            (Core_models.Slice.impl__iter #(Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                    bool
                    Alloc.Alloc.t_Global)
                (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
                        (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                            bool
                            Alloc.Alloc.t_Global) Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    evals1
                  <:
                  t_Slice
                  (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
                )
              <:
              Core_models.Slice.Iter.t_Iter
              (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
            (fun e ->
                let e:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                  bool
                  Alloc.Alloc.t_Global =
                  e
                in
                let e_new:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                  bool
                  Alloc.Alloc.t_Global =
                  Core_models.Clone.f_clone #(Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                        bool
                        Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    e
                in
                let
                (tmp0:
                  Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global),
                (out: Core_models.Option.t_Option bool) =
                  Alloc.Collections.Btree.Map.impl_20__insert #FStar.Char.char
                    #bool
                    #Alloc.Alloc.t_Global
                    e_new
                    v
                    false
                in
                let e_new:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                  bool
                  Alloc.Alloc.t_Global =
                  tmp0
                in
                let _:Core_models.Option.t_Option bool = out in
                e_new)
          <:
          Core_models.Iter.Adapters.Map.t_Map
            (Core_models.Slice.Iter.t_Iter
              (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
            (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global
                -> Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
        )
    in
    let evals1:Alloc.Vec.t_Vec
      (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
      Alloc.Alloc.t_Global =
      Core_models.Iter.Traits.Collect.f_extend #(Alloc.Vec.t_Vec
            (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
            Alloc.Alloc.t_Global)
        #(Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        #(Alloc.Vec.t_Vec
            (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
            Alloc.Alloc.t_Global)
        evals1
        evals2
    in
    Alloc.Slice.impl__to_vec #(Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
          bool
          Alloc.Alloc.t_Global)
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
              (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
              Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          evals1
        <:
        t_Slice (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))

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
  let valuations:Alloc.Vec.t_Vec
    (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
    Alloc.Alloc.t_Global =
    naive_create_possible_valuations (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
              FStar.Char.char Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          vars
        <:
        t_Slice FStar.Char.char)
  in
  match
    Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec
              (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
              Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          valuations
        <:
        Alloc.Vec.Into_iter.t_IntoIter
          (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
          Alloc.Alloc.t_Global)
      ()
      (fun temp_0_ v ->
          let _:Prims.unit = temp_0_ in
          let v:Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global =
            v
          in
          let result:Core_models.Result.t_Result bool Alloc.String.t_String =
            Sat_solver.Expr.evaluate expr v
          in
          if Core_models.Result.impl__is_ok_and #bool #Alloc.String.t_String result (fun r -> r)
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Option.Option_Some v
                <:
                Core_models.Option.t_Option
                (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Option.t_Option
                  (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
                ) (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Option.t_Option
                    (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                        bool
                        Alloc.Alloc.t_Global)) (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Option.t_Option
                    (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char
                        bool
                        Alloc.Alloc.t_Global)) (Prims.unit & Prims.unit)) Prims.unit)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Option.t_Option
        (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global))
      Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    Core_models.Option.Option_None
    <:
    Core_models.Option.t_Option
    (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)

let v_SAT_SOLVER_NAIVE_FUNCTIONAL: Sat_solver.Sat.t_SatSolver =
  { Sat_solver.Sat.f_solve = solve_sat; Sat_solver.Sat.f_description = "naive functional" }
  <:
  Sat_solver.Sat.t_SatSolver
