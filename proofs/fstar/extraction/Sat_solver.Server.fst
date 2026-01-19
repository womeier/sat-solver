module Sat_solver.Server
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_State =
  | State_Idle : t_State
  | State_AcceptingExpr : t_State
  | State_Ready : Sat_solver.Expr.t_Expr -> t_State
  | State_Done :
      Core_models.Option.t_Option
        (Alloc.Collections.Btree.Map.t_BTreeMap FStar.Char.char bool Alloc.Alloc.t_Global)
    -> t_State

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core_models.Fmt.t_Debug t_State

unfold
let impl = impl'

let impl_1: Core_models.Clone.t_Clone t_State =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Marker.t_StructuralPartialEq t_State

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Cmp.t_PartialEq t_State t_State

unfold
let impl_3 = impl_3'

type t_Command =
  | Command_Begin : t_Command
  | Command_GotExpr : Sat_solver.Expr.t_Expr -> t_Command
  | Command_Compute : t_Command
  | Command_End : t_Command

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core_models.Fmt.t_Debug t_Command

unfold
let impl_4 = impl_4'

let impl_5: Core_models.Clone.t_Clone t_Command =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

let process_command (state: t_State) (com: t_Command) : Core_models.Option.t_Option t_State =
  match state, com <: (t_State & t_Command) with
  | State_Idle , Command_Begin  ->
    Core_models.Option.Option_Some (State_AcceptingExpr <: t_State)
    <:
    Core_models.Option.t_Option t_State
  | State_AcceptingExpr , Command_GotExpr e ->
    Core_models.Option.Option_Some (State_Ready e <: t_State) <: Core_models.Option.t_Option t_State
  | State_Ready e, Command_Compute  ->
    Core_models.Option.Option_Some
    (State_Done (Sat_solver.Sat_naive.v_SAT_SOLVER_NAIVE.Sat_solver.Sat.f_solve e) <: t_State)
    <:
    Core_models.Option.t_Option t_State
  | _, Command_End  ->
    Core_models.Option.Option_Some (State_Idle <: t_State) <: Core_models.Option.t_Option t_State
  | _, _ -> Core_models.Option.Option_None <: Core_models.Option.t_Option t_State

let rec process_commands (state: t_State) (coms: t_Slice t_Command)
    : Core_models.Option.t_Option t_State =
  if Core_models.Slice.impl__is_empty #t_Command coms
  then Core_models.Option.Option_Some state <: Core_models.Option.t_Option t_State
  else
    let c:t_Command = coms.[ mk_usize 0 ] in
    let cs:t_Slice t_Command =
      coms.[ { Core_models.Ops.Range.f_start = mk_usize 1 }
        <:
        Core_models.Ops.Range.t_RangeFrom usize ]
    in
    match
      process_command state
        (Core_models.Clone.f_clone #t_Command #FStar.Tactics.Typeclasses.solve c <: t_Command)
      <:
      Core_models.Option.t_Option t_State
    with
    | Core_models.Option.Option_Some new_state -> process_commands new_state cs
    | Core_models.Option.Option_None  ->
      Core_models.Option.Option_None <: Core_models.Option.t_Option t_State
