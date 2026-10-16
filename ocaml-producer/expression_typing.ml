(* expression_values.ml infers value operations, assignments, conditionals and assertion expressions. *)
(* expression_support.ml supplies assignment-target contracts, constant assertions and failure explanations to expression families. *)
(* expression_properties.ml infers property reads and writes against storage contracts and current facts. *)
(* expression_objects.ml infers object and array construction and copying from contextual contracts. *)
(* expression_closures.ml infers constructors and closures and checks their bodies under scoped bounds. *)
(* expression_calls.ml infers calls and method invocations with overload and generic-instance proposals. *)
(* analysis_context.ml assembles the per-pass operations used by expression inference and its operation families. *)
open Source
module type Inputs = sig
  include Expression_values.Inputs
  include Expression_objects.Inputs
  include Expression_properties.Inputs
  include Expression_closures.Inputs
  include Expression_calls.Inputs
  include Analysis_capabilities.Typing_scope
end
module Make (S : Inputs) = struct
open S
module Values = Expression_values.Make(S)
module Objects = Expression_objects.Make(S)
module Properties = Expression_properties.Make(S)
module Closures = Expression_closures.Make(S)
module Calls = Expression_calls.Make(S)
  let infer expr execute_bindings body ?expected env (e:Source.expr) =
    let saved_roots = typing_roots () in
    let root=if speculative_typing () then None else match saved_roots with
      | ((point,plan,_) as root) :: _ when point = current_point () && Execution.contains e.pos plan -> Some root
      | _ -> Option.map (fun plan -> current_point (),plan,env)
          (execution_at e.pos) in
    let roots = match root with None -> saved_roots | Some root -> root :: saved_roots in
    with_typing_roots roots (fun () ->
    let env=match root,e.node with
      | _,BlockBody _ | None,_ -> env
      | Some root,_ -> expression_entry root e.pos env in
    let t = match e.node with
    | Id _ | Literal _ | Not _ | TypeofTest _ | HasKey _ | InstanceTest _
    | Arith _ | Comma _ | Update _ | LogicalAssign _ | NullishAssign _ | Unary _
    | ArrayAssign _ | Equality _ | Apply _ | WithFields _ | Bind _ | Conditional _
    | Coalesce _ | Optional _ | Logical _ | Cast _ | BlockBody _ ->
      Values.infer expr execute_bindings body ?expected env e
    | Alloc _ | Build _ | ObjectAssign _ | ArrayLiteral _ ->
      Objects.infer expr execute_bindings body ?expected env e
    | Read _ | Index _ | IndexWrite _ | Write _ | Assign _ ->
      Properties.infer expr execute_bindings body ?expected env e
    | Ctor _ | New _ | Lambda _ ->
      Closures.infer expr execute_bindings body ?expected env e
    | Call _ | Invoke _ -> Calls.infer expr execute_bindings body ?expected env e in
    (* Block wrappers correspond to statement entries, not expression sites. *)
    (match e.node with
      | BlockBody _ -> ()
      | _ -> publish_expression e.pos t (instantiation_at e.pos)); t)

end
