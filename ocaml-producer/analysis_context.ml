(* refinement.ml supplies branch refinement through the execution interpreter's input interface. *)
(* execution_analysis.ml interprets expression schedules to provide effect states and operand-entry environments. *)
(* closure_offers.ml tracks named closures and class constructors and records signatures offered by their uses. *)
(* claim_collection.ml collects entry claims and instances through point-specific publication operations. *)
open Environment
open Source
open Type_queries
module type Inputs = sig
  include Closure_offers.Inputs
  include Analysis_capabilities.Entry_publication
  include Analysis_capabilities.Instance_publication
  val branch_for_execution : Analysis_capabilities.env -> Source.expr -> bool -> Analysis_capabilities.env
  val speculate : (unit -> 'a) -> 'a option
  val mark_exact_allocations : Json.t list -> unit
end
module Make (S : Inputs) = struct
open S
include Closure_offers.Make(S)
module Execution_inputs : Execution_analysis.Inputs = struct
  let declarations = declarations
  let current_point = S.current_point
  let execution_at = S.execution_at
  let expression_hint = S.expression_hint
  let claimed_type = S.claimed_type
  let grew name = List.mem name (path_facts ()).Proposal_flow.grown_locals
  let branch = S.branch_for_execution
end
include Execution_analysis.Make(Execution_inputs)
module Claim_inputs : Claim_collection.Inputs = struct
  let declarations = declarations
  let is_local = S.is_local
  let module_type = S.module_type
  let publish_instance = S.publish_instance
  let publish_entry = S.publish_entry
  let speculate = S.speculate
end
include Claim_collection.Make(Claim_inputs)
  let resolve env n = match List.assoc_opt n env with
    | Some b -> binding_type b
    | None -> (match module_type n with
      | Some t -> t | None -> Json.fail ("unbound name " ^ n))

  let rec mark_exact (e:expr) = match e.node with
    | Alloc _ -> mark_exact_allocations [e.pos]
    | Logical (_,_,b) | Coalesce (_,b) | Comma (_,b) -> mark_exact b
    | Conditional (_,a,b) -> mark_exact a; mark_exact b
    | Cast (("nonNull" | "satisfies"),_,e) -> mark_exact e
    | _ -> ()

  let rec reads n (e:expr) =
    (match e.node with Id m -> m = n | _ -> false) || List.exists (reads n) (Source.children e)

  let evolving_array (receiver:expr) = match receiver.node with
    | Id n -> (match List.assoc_opt n (path_facts ()).Proposal_flow.evolving with Some (key,true) -> Some key | _ -> None)
    | _ -> None

  let adds env (receiver:expr) t name = match receiver.node with
    | Id n -> (match List.assoc_opt n env with
      | Some (Value _) -> may_lack declarations t name
      | _ -> false)
    | _ -> false

end
