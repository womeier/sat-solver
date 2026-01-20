module Sat_solver.Expr
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Nom.Branch in
  let open Nom.Error in
  let open Nom.Internal in
  let open Nom.Sequence in
  let open Nom.Traits in
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

let parse_bool (i: string)
    : Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)) =
  let
  (_:
    (string
        -> Core_models.Result.t_Result (string & FStar.Char.char)
            (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))),
  (out:
    Core_models.Result.t_Result (string & FStar.Char.char)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))) =
    Core_models.Ops.Function.f_call_mut #string
      #FStar.Tactics.Typeclasses.solve
      (Nom.Character.Complete.one_of #string #string #(Nom.Error.t_Error string) "⊤⊥TF"
        <:
        string
          -> Core_models.Result.t_Result (string & FStar.Char.char)
              (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
      (i <: string)
  in
  match
    out
    <:
    Core_models.Result.t_Result (string & FStar.Char.char)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
  with
  | Core_models.Result.Result_Ok (i, t) ->
    Core_models.Result.Result_Ok
    (i,
      (match t <: FStar.Char.char with
        | 'F' | 'â' -> Expr_False <: t_Expr
        | 'â' | 'T' -> Expr_True <: t_Expr
        | _ ->
          Rust_primitives.Hax.never_to_any (Core_models.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never))
      <:
      (string & t_Expr))
    <:
    Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))

let parse_var (i: string)
    : Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)) =
  let
  (_:
    Nom.Internal.t_Map
      (string
          -> Core_models.Result.t_Result (string & FStar.Char.char)
              (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
      (FStar.Char.char -> t_Expr)),
  (out:
    Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))) =
    Nom.Internal.f_parse #(Nom.Internal.t_Map
          (string
              -> Core_models.Result.t_Result (string & FStar.Char.char)
                  (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
          (FStar.Char.char -> t_Expr))
      #string
      #FStar.Tactics.Typeclasses.solve
      (Nom.Combinator.map #string
          #t_Expr
          #(Nom.Error.t_Error string)
          (Nom.Character.Complete.one_of #string
              #string
              #(Nom.Error.t_Error string)
              "abcdefghijklmnopqrstuvwxyz"
            <:
            string
              -> Core_models.Result.t_Result (string & FStar.Char.char)
                  (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
          Expr_Variable
        <:
        Nom.Internal.t_Map
          (string
              -> Core_models.Result.t_Result (string & FStar.Char.char)
                  (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
          (FStar.Char.char -> t_Expr))
      i
  in
  out

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

let rec parse_neg (i: string)
    : Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)) =
  let
  (_:
    Nom.Internal.t_Map
      (Nom.Sequence.t_Preceded
          (string
              -> Core_models.Result.t_Result (string & FStar.Char.char)
                  (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
          (string
              -> Core_models.Result.t_Result (string & t_Expr)
                  (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))))
      (t_Expr -> t_Expr)),
  (out:
    Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))) =
    Nom.Internal.f_parse #(Nom.Internal.t_Map
          (Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (string
                  -> Core_models.Result.t_Result (string & t_Expr)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))))
          (t_Expr -> t_Expr))
      #string
      #FStar.Tactics.Typeclasses.solve
      (Nom.Internal.f_map #(Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (string
                  -> Core_models.Result.t_Result (string & t_Expr)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))))
          #string
          #FStar.Tactics.Typeclasses.solve
          #t_Expr
          (Nom.Sequence.preceded #string
              #t_Expr
              #(Nom.Error.t_Error string)
              (Nom.Character.Complete.one_of #string #string #(Nom.Error.t_Error string) "~¬"
                <:
                string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              parse_expr
            <:
            Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (string
                  -> Core_models.Result.t_Result (string & t_Expr)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))))
          (fun e ->
              let e:t_Expr = e in
              Expr_Neg e <: t_Expr)
        <:
        Nom.Internal.t_Map
          (Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (string
                  -> Core_models.Result.t_Result (string & t_Expr)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))))
          (t_Expr -> t_Expr))
      i
  in
  out

and parse_expr (i: string)
    : Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)) =
  let
  (_:
    Nom.Sequence.t_Preceded
      (string
          -> Core_models.Result.t_Result (string & string)
              (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
      (Nom.Sequence.t_Terminated
          (Nom.Branch.t_Choice
            (t_Array
                (string
                    -> Core_models.Result.t_Result (string & t_Expr)
                        (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
                (mk_usize 5)))
          (string
              -> Core_models.Result.t_Result (string & string)
                  (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))))),
  (out:
    Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))) =
    Nom.Internal.f_parse #(Nom.Sequence.t_Preceded
          (string
              -> Core_models.Result.t_Result (string & string)
                  (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
          (Nom.Sequence.t_Terminated
              (Nom.Branch.t_Choice
                (t_Array
                    (string
                        -> Core_models.Result.t_Result (string & t_Expr)
                            (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                (Nom.Error.t_Error string))) (mk_usize 5)))
              (string
                  -> Core_models.Result.t_Result (string & string)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))))
      #string
      #FStar.Tactics.Typeclasses.solve
      (Nom.Sequence.delimited #string
          #t_Expr
          #(Nom.Error.t_Error string)
          #(Nom.Branch.t_Choice
            (t_Array
                (string
                    -> Core_models.Result.t_Result (string & t_Expr)
                        (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
                (mk_usize 5)))
          Nom.Character.Complete.multispace0
          (Nom.Branch.alt #(t_Array
                  (string
                      -> Core_models.Result.t_Result (string & t_Expr)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  ) (mk_usize 5))
              (let list = [parse_conj; parse_disj; parse_neg; parse_var; parse_bool] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
                Rust_primitives.Hax.array_of_list 5 list)
            <:
            Nom.Branch.t_Choice
            (t_Array
                (string
                    -> Core_models.Result.t_Result (string & t_Expr)
                        (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
                (mk_usize 5)))
          Nom.Character.Complete.multispace0
        <:
        Nom.Sequence.t_Preceded
          (string
              -> Core_models.Result.t_Result (string & string)
                  (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
          (Nom.Sequence.t_Terminated
              (Nom.Branch.t_Choice
                (t_Array
                    (string
                        -> Core_models.Result.t_Result (string & t_Expr)
                            (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                (Nom.Error.t_Error string))) (mk_usize 5)))
              (string
                  -> Core_models.Result.t_Result (string & string)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))))
      i
  in
  out

and parse_disj (i: string)
    : Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)) =
  let
  (_:
    Nom.Internal.t_Map
      (Nom.Sequence.t_Preceded
          (string
              -> Core_models.Result.t_Result (string & FStar.Char.char)
                  (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
          (Nom.Sequence.t_Terminated
              (Nom.Internal.t_And
                  (string
                      -> Core_models.Result.t_Result (string & t_Expr)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )
                  (Nom.Sequence.t_Preceded
                      (string
                          -> Core_models.Result.t_Result (string & FStar.Char.char)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))))
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))))
      ((t_Expr & t_Expr) -> t_Expr)),
  (out:
    Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))) =
    Nom.Internal.f_parse #(Nom.Internal.t_Map
          (Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (Nom.Sequence.t_Terminated
                  (Nom.Internal.t_And
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (Nom.Sequence.t_Preceded
                          (string
                              -> Core_models.Result.t_Result (string & FStar.Char.char)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))
                          (string
                              -> Core_models.Result.t_Result (string & t_Expr)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))))
                  (string
                      -> Core_models.Result.t_Result (string & FStar.Char.char)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  ))) ((t_Expr & t_Expr) -> t_Expr))
      #string
      #FStar.Tactics.Typeclasses.solve
      (Nom.Internal.f_map #(Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (Nom.Sequence.t_Terminated
                  (Nom.Internal.t_And
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (Nom.Sequence.t_Preceded
                          (string
                              -> Core_models.Result.t_Result (string & FStar.Char.char)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))
                          (string
                              -> Core_models.Result.t_Result (string & t_Expr)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))))
                  (string
                      -> Core_models.Result.t_Result (string & FStar.Char.char)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )))
          #string
          #FStar.Tactics.Typeclasses.solve
          #t_Expr
          (Nom.Sequence.delimited #string
              #(t_Expr & t_Expr)
              #(Nom.Error.t_Error string)
              #(Nom.Internal.t_And
                  (string
                      -> Core_models.Result.t_Result (string & t_Expr)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )
                  (Nom.Sequence.t_Preceded
                      (string
                          -> Core_models.Result.t_Result (string & FStar.Char.char)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))))
              (Nom.Character.Complete.one_of #string #string #(Nom.Error.t_Error string) "("
                <:
                string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (Nom.Sequence.separated_pair #string
                  #t_Expr
                  #t_Expr
                  #(Nom.Error.t_Error string)
                  parse_expr
                  (Nom.Character.Complete.one_of #string #string #(Nom.Error.t_Error string) "∨v|"
                    <:
                    string
                      -> Core_models.Result.t_Result (string & FStar.Char.char)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )
                  parse_expr
                <:
                Nom.Internal.t_And
                  (string
                      -> Core_models.Result.t_Result (string & t_Expr)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )
                  (Nom.Sequence.t_Preceded
                      (string
                          -> Core_models.Result.t_Result (string & FStar.Char.char)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))))
              (Nom.Character.Complete.one_of #string #string #(Nom.Error.t_Error string) ")"
                <:
                string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
            <:
            Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (Nom.Sequence.t_Terminated
                  (Nom.Internal.t_And
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (Nom.Sequence.t_Preceded
                          (string
                              -> Core_models.Result.t_Result (string & FStar.Char.char)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))
                          (string
                              -> Core_models.Result.t_Result (string & t_Expr)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))))
                  (string
                      -> Core_models.Result.t_Result (string & FStar.Char.char)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )))
          (fun temp_0_ ->
              let (e1: t_Expr), (e2: t_Expr) = temp_0_ in
              Expr_Disj e1 e2 <: t_Expr)
        <:
        Nom.Internal.t_Map
          (Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (Nom.Sequence.t_Terminated
                  (Nom.Internal.t_And
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (Nom.Sequence.t_Preceded
                          (string
                              -> Core_models.Result.t_Result (string & FStar.Char.char)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))
                          (string
                              -> Core_models.Result.t_Result (string & t_Expr)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))))
                  (string
                      -> Core_models.Result.t_Result (string & FStar.Char.char)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  ))) ((t_Expr & t_Expr) -> t_Expr))
      i
  in
  out

and parse_conj (i: string)
    : Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)) =
  let
  (_:
    Nom.Internal.t_Map
      (Nom.Sequence.t_Preceded
          (string
              -> Core_models.Result.t_Result (string & FStar.Char.char)
                  (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
          (Nom.Sequence.t_Terminated
              (Nom.Internal.t_And
                  (string
                      -> Core_models.Result.t_Result (string & t_Expr)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )
                  (Nom.Sequence.t_Preceded
                      (string
                          -> Core_models.Result.t_Result (string & FStar.Char.char)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))))
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))))
      ((t_Expr & t_Expr) -> t_Expr)),
  (out:
    Core_models.Result.t_Result (string & t_Expr)
      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))) =
    Nom.Internal.f_parse #(Nom.Internal.t_Map
          (Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (Nom.Sequence.t_Terminated
                  (Nom.Internal.t_And
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (Nom.Sequence.t_Preceded
                          (string
                              -> Core_models.Result.t_Result (string & FStar.Char.char)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))
                          (string
                              -> Core_models.Result.t_Result (string & t_Expr)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))))
                  (string
                      -> Core_models.Result.t_Result (string & FStar.Char.char)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  ))) ((t_Expr & t_Expr) -> t_Expr))
      #string
      #FStar.Tactics.Typeclasses.solve
      (Nom.Internal.f_map #(Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (Nom.Sequence.t_Terminated
                  (Nom.Internal.t_And
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (Nom.Sequence.t_Preceded
                          (string
                              -> Core_models.Result.t_Result (string & FStar.Char.char)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))
                          (string
                              -> Core_models.Result.t_Result (string & t_Expr)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))))
                  (string
                      -> Core_models.Result.t_Result (string & FStar.Char.char)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )))
          #string
          #FStar.Tactics.Typeclasses.solve
          #t_Expr
          (Nom.Sequence.delimited #string
              #(t_Expr & t_Expr)
              #(Nom.Error.t_Error string)
              #(Nom.Internal.t_And
                  (string
                      -> Core_models.Result.t_Result (string & t_Expr)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )
                  (Nom.Sequence.t_Preceded
                      (string
                          -> Core_models.Result.t_Result (string & FStar.Char.char)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))))
              (Nom.Character.Complete.one_of #string #string #(Nom.Error.t_Error string) "("
                <:
                string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (Nom.Sequence.separated_pair #string
                  #t_Expr
                  #t_Expr
                  #(Nom.Error.t_Error string)
                  parse_expr
                  (Nom.Character.Complete.one_of #string #string #(Nom.Error.t_Error string) "∧&"
                    <:
                    string
                      -> Core_models.Result.t_Result (string & FStar.Char.char)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )
                  parse_expr
                <:
                Nom.Internal.t_And
                  (string
                      -> Core_models.Result.t_Result (string & t_Expr)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )
                  (Nom.Sequence.t_Preceded
                      (string
                          -> Core_models.Result.t_Result (string & FStar.Char.char)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))))
              (Nom.Character.Complete.one_of #string #string #(Nom.Error.t_Error string) ")"
                <:
                string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
            <:
            Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (Nom.Sequence.t_Terminated
                  (Nom.Internal.t_And
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (Nom.Sequence.t_Preceded
                          (string
                              -> Core_models.Result.t_Result (string & FStar.Char.char)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))
                          (string
                              -> Core_models.Result.t_Result (string & t_Expr)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))))
                  (string
                      -> Core_models.Result.t_Result (string & FStar.Char.char)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  )))
          (fun temp_0_ ->
              let (e1: t_Expr), (e2: t_Expr) = temp_0_ in
              Expr_Conj e1 e2 <: t_Expr)
        <:
        Nom.Internal.t_Map
          (Nom.Sequence.t_Preceded
              (string
                  -> Core_models.Result.t_Result (string & FStar.Char.char)
                      (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string)))
              (Nom.Sequence.t_Terminated
                  (Nom.Internal.t_And
                      (string
                          -> Core_models.Result.t_Result (string & t_Expr)
                              (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                  (Nom.Error.t_Error string)))
                      (Nom.Sequence.t_Preceded
                          (string
                              -> Core_models.Result.t_Result (string & FStar.Char.char)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))
                          (string
                              -> Core_models.Result.t_Result (string & t_Expr)
                                  (Nom.Internal.t_Err (Nom.Error.t_Error string)
                                      (Nom.Error.t_Error string)))))
                  (string
                      -> Core_models.Result.t_Result (string & FStar.Char.char)
                          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
                  ))) ((t_Expr & t_Expr) -> t_Expr))
      i
  in
  out

let example_expr_sat (_: Prims.unit) : t_Expr =
  (Core_models.Result.impl__unwrap #(string & t_Expr)
      #(Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
      (parse_expr "((T & ~y) & (x | F))"
        <:
        Core_models.Result.t_Result (string & t_Expr)
          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))))
    ._2

let example_expr_unsat (_: Prims.unit) : t_Expr =
  (Core_models.Result.impl__unwrap #(string & t_Expr)
      #(Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))
      (parse_expr "(T & (~x & x))"
        <:
        Core_models.Result.t_Result (string & t_Expr)
          (Nom.Internal.t_Err (Nom.Error.t_Error string) (Nom.Error.t_Error string))))
    ._2

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
