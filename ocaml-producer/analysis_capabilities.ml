(* Component inputs describe query and publication authority over one analysis
   pass. Their records contain immutable values; no capability carries its owner. *)
open Semantic

type env = (string * Environment.binding) list
type root = string * Execution.plan * env
type class_info = Json.t * ty list * ty * (Semantic.key * string) list

type observations = {
  for_in_keys: string list;
  method_callees: Json.t list;
  shape_tests: (string * string) list;
  unknown_instance_tests: string list;
}

type node_output = {
  entries: Proposal_types.entry list;
  expressions: Proposal_types.expression list;
  contracts: Proposal_types.contract list;
  arrows: (Json.t * Proposal_types.overlay list) list;
  requests: (Json.t * Semantic.signature) list;
  instances: ((string * Json.t) * ty) list;
  instantiations: ((string * Json.t) * (string * type_argument) list) list;
}
let empty_output = { entries=[]; expressions=[]; contracts=[]; arrows=[];
  requests=[]; instances=[]; instantiations=[] }

module type Queries = sig
  val declarations : Source.declaration list
  val offered : (Json.t * Semantic.signature list) list
  val current_point : unit -> string
  val rigid_bounds : unit -> (Semantic.rigid * ty) list
  val rigid_bound : Semantic.rigid -> ty option
  val owned_resolution : Semantic.rigid -> (Semantic.rigid * Semantic.rigid option) option
  (* The resolvable binder whose observation a rigid is, with its result. *)
  val observation_owner : Semantic.rigid -> (Semantic.rigid * Semantic.rigid) option
  val field_type : Source.declaration list -> string list -> ty -> Semantic.key -> ty
  val index_type : Source.declaration list -> string list -> ty -> ty -> ty
  val is_local : string -> bool
  val module_names : string list
  (* What a module function declared in the source does with the actuals
     past its parameters; none for an imported value. *)
  val module_arity : string -> Module_contract.arity option
  val module_type : string -> ty option
  val execution_at : Json.t -> Execution.plan option
  val expression_hint : Json.t -> Source.expr option
  val claimed_type : Json.t -> ty option
  val latest_claim : Json.t -> ty option
  val instantiation_at : Json.t -> (string * type_argument) list option
  val evolved : Json.t -> ty
  val expected_result : unit -> ty option
end

module type Observations = sig
  val observations : unit -> observations
  val explain : Json.t -> string -> unit
end

module type Path_queries = sig
  val path_facts : unit -> Proposal_flow.metadata
end

module type Environment_queries = sig
  val resolve : env -> string -> ty
  val effects : env -> Source.expr -> env
  val branch : env -> Source.expr -> bool -> env
  val expression_entry : root -> Json.t -> env -> env
  val reads : string -> Source.expr -> bool
  val evolving_array : Source.expr -> Json.t option
  val adds : env -> Source.expr -> ty -> Semantic.key -> bool
end

module type Execution_operations = sig
  val run_execution : ?observe:(Json.t -> env -> unit) -> env -> Execution.plan -> env
  val join : env -> env -> env -> env
end

module type Speculation = sig
  val quietly : (unit -> 'a) -> 'a option
end

module type Expression_publication = sig
  val publish_expression : Json.t -> ty -> (string * type_argument) list option -> unit
end
module type Instance_publication = sig
  val publish_instance : Json.t -> ty -> unit
  val publish_substitution : Json.t -> (string * type_argument) list -> unit
end
module type Entry_publication = sig
  val publish_entry : Json.t -> env -> unit
end
module type Claim_operations = sig
  val entry : env -> Json.t -> unit
  val instance_of : ?declared:ty -> Source.expr -> Inference.substitution -> unit
  val method_read : Source.expr -> bool
end

module type Offer_operations = sig
  val closure_offer : string -> Semantic.signature -> (unit -> unit) option
  val offer_class : class_info -> ty -> unit
end
module type Closure_registry = sig
  val register_closure : string -> Json.t -> ty list -> unit
  val register_object : string -> (Semantic.key * Source.expr) list -> unit
  val register_class : string -> class_info -> unit
  val publish_request : Json.t -> Semantic.signature -> unit
end
module type Named_closures = sig
  val named_closure : string -> ty option -> Source.expr -> unit
end
module type Exact_allocations = sig
  val mark_exact : Source.expr -> unit
end
module type Evolution = sig
  val evolve : Json.t -> ty -> unit
end

module type Typing_scope = sig
  val speculative_typing : unit -> bool
  val typing_roots : unit -> root list
  val with_typing_roots : root list -> (unit -> 'a) -> 'a
end
module type Closure_scope = sig
  val held_in_cell : string -> Json.t -> bool
  val closure_entry : Json.t -> (string * Execution.binding_plan option) option
  val with_current_point : string -> (unit -> 'a) -> 'a
  val with_rigid_bounds : (Semantic.rigid * ty) list -> (unit -> 'a) -> 'a
  val collect_overload_row_claims : (unit -> unit) -> Proposal_types.overlay
  val prepare_constructor : Json.t list -> bool
  val publish_arrow : Json.t -> Proposal_types.overlay list -> unit
end
module type Statement_operations = sig
  val propose_use : Json.t -> ty -> unit
  val held_in_cell : string -> Json.t -> bool
  val following_statements : Json.t -> Source.stmt list
  val forget_exact_local : string -> unit
  val mark_fresh_constructor : unit -> unit
  val clear_evolving_binding : string -> unit
  val register_evolving_binding : string -> Json.t -> bool -> unit
  val mark_exact_allocations : Json.t list -> unit
  val mark_exact_local : string -> unit
  val record_growth : string -> unit
  val forget_holder : string -> unit
  val record_holder : string -> string -> unit
  val holders_of : string -> string list
  val publish_contract : Proposal_types.contract -> unit
  val record_return : ty -> unit
  val observe_for_in : string -> unit
end
module type Node_scope = sig
  val flow_graph : Json.t -> Flow.graph option
  val with_path_metadata : Proposal_flow.metadata -> Proposal_flow.metadata -> (unit -> 'a) -> 'a
  val with_output : string -> (unit -> 'a) -> 'a * node_output
  val publish_output : node_output -> unit
end
