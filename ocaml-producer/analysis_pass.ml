(* statement_analysis.ml types statement actions and supplies their semantic callbacks to the graph solver. *)
(* expression_typing.ml dispatches every expression constructor and associates its type with the execution point. *)
(* binding_analysis.ml interprets parameter and pattern binding schedules with recursive expression inference. *)
(* analysis_state.ml allocates the pass state shared by its mutually recursive expression, binding and body analyses. *)
open Source
open Proposal_types
let infer diagnostics flows offered declarations module_functions arities bounds assumed f =
  let state = Analysis_state.create diagnostics flows offered declarations module_functions arities bounds assumed f in
  let module Owner = Analysis_state.Access(struct let state = state end) in
  let module Context = Analysis_context.Make(Owner) in
  let module S = struct include Owner include Context end in
  let module E = Expression_typing.Make(S) in
  let module B = Binding_analysis.Make(S) in
  let module T = Statement_analysis.Make(S) in
  let rec expr ?expected env e = E.infer expr bindings body ?expected env e
  and bindings env plan = B.infer expr env plan
  and body owner_span result env ss =
    Owner.with_block_context result
      (fun () -> T.statements expr bindings owner_span env ss) in
  let run () =
  let owner_span = if f.name_pos=Json.Null then Json.Array [Json.int 0;Json.int 0] else f.name_pos in
  ignore (T.statements expr bindings owner_span Owner.initial_environment f.body);
  (* An expression the lowering reaches on two paths (the fields the arms of a
     constructor's last `if` share) is claimed once when both claims agree;
     two different claims at one span stay, and Lean refuses them. *)
  let output = Owner.output () in
  let seen = Hashtbl.create 64 in
  let expressions = List.filter (fun x ->
    not (Hashtbl.mem seen x) && (Hashtbl.add seen x (); true)) (List.rev output.Analysis_capabilities.expressions) in
  let expressions = List.map (fun (x:expression) -> match List.assoc_opt (x.point,x.pos) output.Analysis_capabilities.instances with
    | Some instance -> {x with type_=instance}
    | None -> x) expressions in
  (* Likewise an entry, the closure body a guard's arm types twice. *)
  let seen = Hashtbl.create 64 in
  let entries = List.filter (fun x ->
    not (Hashtbl.mem seen x) && (Hashtbl.add seen x (); true)) (List.rev output.Analysis_capabilities.entries) in
  {contracts=List.rev output.Analysis_capabilities.contracts;source=f;entries;expressions;arrows=List.sort_uniq compare (List.rev output.Analysis_capabilities.arrows)},List.sort_uniq compare output.Analysis_capabilities.requests
  in
  let result = try Ok (run ()) with Json.Error m -> Error m in
  result,Owner.writes (),Owner.uses ()
