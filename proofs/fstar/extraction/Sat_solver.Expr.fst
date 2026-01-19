module Sat_solver.Expr
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Std.Collections.Hash.Set in
  let open Std.Hash.Random in
  ()

type t_Expr =
  | Expr_True : t_Expr
  | Expr_False : t_Expr
  | Expr_Variable : FStar.Char.char -> t_Expr
  | Expr_Conj :
      Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global ->
      Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global
    -> t_Expr
  | Expr_Disj :
      Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global ->
      Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global
    -> t_Expr
  | Expr_Neg : Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global -> t_Expr

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core_models.Fmt.t_Debug t_Expr

unfold
let impl_1 = impl_1'

let impl_2: Core_models.Clone.t_Clone t_Expr =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Marker.t_StructuralPartialEq t_Expr

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core_models.Cmp.t_PartialEq t_Expr t_Expr

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core_models.Fmt.t_Display t_Expr =
  {
    f_fmt_pre = (fun (self: t_Expr) (f: Core_models.Fmt.t_Formatter) -> true);
    f_fmt_post
    =
    (fun
        (self: t_Expr)
        (f: Core_models.Fmt.t_Formatter)
        (out1:
          (Core_models.Fmt.t_Formatter &
            Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error))
        ->
        true);
    f_fmt
    =
    fun (self: t_Expr) (f: Core_models.Fmt.t_Formatter) ->
      let
      (f: Core_models.Fmt.t_Formatter),
      (hax_temp_output: Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error) =
        match self <: t_Expr with
        | Expr_Neg e ->
          let args:Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global =
            e <: Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global
          in
          let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
            let list =
              [
                Core_models.Fmt.Rt.impl__new_display #(Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global
                  )
                  args
              ]
            in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list
          in
          let
          (tmp0: Core_models.Fmt.t_Formatter),
          (out: Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error) =
            Core_models.Fmt.impl_11__write_fmt f
              (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                  (mk_usize 1)
                  (let list = ["¬"] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                  args
                <:
                Core_models.Fmt.t_Arguments)
          in
          let f:Core_models.Fmt.t_Formatter = tmp0 in
          f, out
          <:
          (Core_models.Fmt.t_Formatter &
            Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error)
        | Expr_True  ->
          let
          (tmp0: Core_models.Fmt.t_Formatter),
          (out: Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error) =
            Core_models.Fmt.impl_11__write_fmt f
              (Core_models.Fmt.Rt.impl_1__new_const (mk_usize 1)
                  (let list = ["⊤"] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                <:
                Core_models.Fmt.t_Arguments)
          in
          let f:Core_models.Fmt.t_Formatter = tmp0 in
          f, out
          <:
          (Core_models.Fmt.t_Formatter &
            Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error)
        | Expr_False  ->
          let
          (tmp0: Core_models.Fmt.t_Formatter),
          (out: Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error) =
            Core_models.Fmt.impl_11__write_fmt f
              (Core_models.Fmt.Rt.impl_1__new_const (mk_usize 1)
                  (let list = ["⊥"] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                <:
                Core_models.Fmt.t_Arguments)
          in
          let f:Core_models.Fmt.t_Formatter = tmp0 in
          f, out
          <:
          (Core_models.Fmt.t_Formatter &
            Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error)
        | Expr_Variable v ->
          let args:FStar.Char.char = v <: FStar.Char.char in
          let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
            let list = [Core_models.Fmt.Rt.impl__new_display #FStar.Char.char args] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list
          in
          let
          (tmp0: Core_models.Fmt.t_Formatter),
          (out: Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error) =
            Core_models.Fmt.impl_11__write_fmt f
              (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                  (mk_usize 1)
                  (let list = [""] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                  args
                <:
                Core_models.Fmt.t_Arguments)
          in
          let f:Core_models.Fmt.t_Formatter = tmp0 in
          f, out
          <:
          (Core_models.Fmt.t_Formatter &
            Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error)
        | Expr_Conj e1 e2 ->
          let args:(Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global &
            Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global) =
            e1, e2
            <:
            (Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global &
              Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global)
          in
          let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 2) =
            let list =
              [
                Core_models.Fmt.Rt.impl__new_display #(Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global
                  )
                  args._1;
                Core_models.Fmt.Rt.impl__new_display #(Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global
                  )
                  args._2
              ]
            in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list
          in
          let
          (tmp0: Core_models.Fmt.t_Formatter),
          (out: Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error) =
            Core_models.Fmt.impl_11__write_fmt f
              (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 3)
                  (mk_usize 2)
                  (let list = ["("; " ∧ "; ")"] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
                    Rust_primitives.Hax.array_of_list 3 list)
                  args
                <:
                Core_models.Fmt.t_Arguments)
          in
          let f:Core_models.Fmt.t_Formatter = tmp0 in
          f, out
          <:
          (Core_models.Fmt.t_Formatter &
            Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error)
        | Expr_Disj e1 e2 ->
          let args:(Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global &
            Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global) =
            e1, e2
            <:
            (Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global &
              Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global)
          in
          let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 2) =
            let list =
              [
                Core_models.Fmt.Rt.impl__new_display #(Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global
                  )
                  args._1;
                Core_models.Fmt.Rt.impl__new_display #(Alloc.Boxed.t_Box t_Expr Alloc.Alloc.t_Global
                  )
                  args._2
              ]
            in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list
          in
          let
          (tmp0: Core_models.Fmt.t_Formatter),
          (out: Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error) =
            Core_models.Fmt.impl_11__write_fmt f
              (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 3)
                  (mk_usize 2)
                  (let list = ["("; " ∨ "; ")"] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
                    Rust_primitives.Hax.array_of_list 3 list)
                  args
                <:
                Core_models.Fmt.t_Arguments)
          in
          let f:Core_models.Fmt.t_Formatter = tmp0 in
          f, out
          <:
          (Core_models.Fmt.t_Formatter &
            Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error)
      in
      f, hax_temp_output
      <:
      (Core_models.Fmt.t_Formatter & Core_models.Result.t_Result Prims.unit Core_models.Fmt.t_Error)
  }

let rec evaluate
      (expr: t_Expr)
      (valuation: Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
    : Core_models.Result.t_Result bool Alloc.String.t_String =
  match expr <: t_Expr with
  | Expr_True  ->
    Core_models.Result.Result_Ok true <: Core_models.Result.t_Result bool Alloc.String.t_String
  | Expr_False  ->
    Core_models.Result.Result_Ok false <: Core_models.Result.t_Result bool Alloc.String.t_String
  | Expr_Neg e ->
    Core_models.Result.impl__map #bool
      #Alloc.String.t_String
      #bool
      (evaluate e valuation <: Core_models.Result.t_Result bool Alloc.String.t_String)
      (fun x ->
          let x:bool = x in
          ~.x <: bool)
  | Expr_Conj e1 e2 ->
    (match evaluate e1 valuation <: Core_models.Result.t_Result bool Alloc.String.t_String with
      | Core_models.Result.Result_Ok hoist2 ->
        (match evaluate e2 valuation <: Core_models.Result.t_Result bool Alloc.String.t_String with
          | Core_models.Result.Result_Ok hoist1 ->
            Core_models.Result.Result_Ok (hoist2 && hoist1)
            <:
            Core_models.Result.t_Result bool Alloc.String.t_String
          | Core_models.Result.Result_Err err ->
            Core_models.Result.Result_Err err
            <:
            Core_models.Result.t_Result bool Alloc.String.t_String)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err <: Core_models.Result.t_Result bool Alloc.String.t_String)
  | Expr_Disj e1 e2 ->
    (match evaluate e1 valuation <: Core_models.Result.t_Result bool Alloc.String.t_String with
      | Core_models.Result.Result_Ok hoist5 ->
        (match evaluate e2 valuation <: Core_models.Result.t_Result bool Alloc.String.t_String with
          | Core_models.Result.Result_Ok hoist4 ->
            Core_models.Result.Result_Ok (hoist5 || hoist4)
            <:
            Core_models.Result.t_Result bool Alloc.String.t_String
          | Core_models.Result.Result_Err err ->
            Core_models.Result.Result_Err err
            <:
            Core_models.Result.t_Result bool Alloc.String.t_String)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err <: Core_models.Result.t_Result bool Alloc.String.t_String)
  | Expr_Variable s ->
    let args:FStar.Char.char = s <: FStar.Char.char in
    let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
      let list = [Core_models.Fmt.Rt.impl__new_display #FStar.Char.char args] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list
    in
    Core_models.Option.impl__ok_or #bool
      #Alloc.String.t_String
      (Core_models.Option.impl_2__copied #bool
          (Alloc.Collections.Btree.Map.impl_20__get #FStar.Char.char
              #bool
              #Alloc.Alloc.t_Global
              #FStar.Char.char
              valuation
              s
            <:
            Core_models.Option.t_Option bool)
        <:
        Core_models.Option.t_Option bool)
      (Core_models.Hint.must_use #Alloc.String.t_String
          (Alloc.Fmt.format (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                  (mk_usize 1)
                  (let list = ["Variable not found: "] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                  args
                <:
                Core_models.Fmt.t_Arguments)
            <:
            Alloc.String.t_String)
        <:
        Alloc.String.t_String)

let rec collect_vars_aux (expr: t_Expr)
    : Std.Collections.Hash.Set.t_HashSet FStar.Char.char Std.Hash.Random.t_RandomState =
  match expr <: t_Expr with
  | Expr_Variable v ->
    Core_models.Iter.Traits.Iterator.f_collect #(Alloc.Vec.Into_iter.t_IntoIter FStar.Char.char
          Alloc.Alloc.t_Global)
      #FStar.Tactics.Typeclasses.solve
      #(Std.Collections.Hash.Set.t_HashSet FStar.Char.char Std.Hash.Random.t_RandomState)
      (Core_models.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec FStar.Char.char
              Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          (Alloc.Slice.impl__into_vec #FStar.Char.char
              #Alloc.Alloc.t_Global
              (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list = [v] in
                        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                        Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    Alloc.Boxed.t_Box (t_Array FStar.Char.char (mk_usize 1)) Alloc.Alloc.t_Global)
                <:
                Alloc.Boxed.t_Box (t_Slice FStar.Char.char) Alloc.Alloc.t_Global)
            <:
            Alloc.Vec.t_Vec FStar.Char.char Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.Into_iter.t_IntoIter FStar.Char.char Alloc.Alloc.t_Global)
  | Expr_Neg e -> collect_vars_aux e
  | Expr_Disj e1 e2
  | Expr_Conj e1 e2 ->
    let vs1:Std.Collections.Hash.Set.t_HashSet FStar.Char.char Std.Hash.Random.t_RandomState =
      collect_vars_aux e1
    in
    let vs2:Std.Collections.Hash.Set.t_HashSet FStar.Char.char Std.Hash.Random.t_RandomState =
      collect_vars_aux e2
    in
    let vs1:Std.Collections.Hash.Set.t_HashSet FStar.Char.char Std.Hash.Random.t_RandomState =
      Core_models.Iter.Traits.Collect.f_extend #(Std.Collections.Hash.Set.t_HashSet FStar.Char.char
            Std.Hash.Random.t_RandomState)
        #FStar.Char.char
        #FStar.Tactics.Typeclasses.solve
        #(Std.Collections.Hash.Set.t_HashSet FStar.Char.char Std.Hash.Random.t_RandomState)
        vs1
        vs2
    in
    vs1
  | Expr_True  | Expr_False  -> Std.Collections.Hash.Set.impl__new #FStar.Char.char ()

let collect_vars (expr: t_Expr) : Alloc.Vec.t_Vec FStar.Char.char Alloc.Alloc.t_Global =
  let vars:Std.Collections.Hash.Set.t_HashSet FStar.Char.char Std.Hash.Random.t_RandomState =
    collect_vars_aux expr
  in
  Core_models.Iter.Traits.Iterator.f_collect #(Std.Collections.Hash.Set.t_IntoIter FStar.Char.char)
    #FStar.Tactics.Typeclasses.solve
    #(Alloc.Vec.t_Vec FStar.Char.char Alloc.Alloc.t_Global)
    (Core_models.Iter.Traits.Collect.f_into_iter #(Std.Collections.Hash.Set.t_HashSet
            FStar.Char.char Std.Hash.Random.t_RandomState)
        #FStar.Tactics.Typeclasses.solve
        vars
      <:
      Std.Collections.Hash.Set.t_IntoIter FStar.Char.char)
