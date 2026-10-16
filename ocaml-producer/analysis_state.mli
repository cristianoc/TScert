(* The state owner exports operations and immutable observations. Its candidate
   storage, context references and indexing tables are private. *)
type env = Analysis_capabilities.env
type expression_infer = ?expected:Semantic.ty -> env -> Source.expr -> Semantic.ty
type body_infer = Json.t -> Semantic.ty option -> env -> Source.stmt list -> env * Semantic.ty list

type t
val create : Proposal_diagnostics.state -> Flow.graph list ->
  (Json.t * Semantic.signature list) list -> Source.declaration list ->
  (string * Semantic.ty Lazy.t) list -> (string * Module_contract.arity) list -> (Semantic.rigid * Semantic.ty) list ->
  (Json.t * Semantic.ty) list -> Source.fn -> t


type candidate_snapshot = {
  point: string;
  speculative: bool;
  output: Analysis_capabilities.node_output;
  metadata: Proposal_flow.metadata;
}

module Access (_ : sig val state : t end) : sig
  include Analysis_capabilities.Queries
  include Analysis_capabilities.Observations
  include Analysis_capabilities.Path_queries
  include Analysis_capabilities.Expression_publication
  include Analysis_capabilities.Instance_publication
  include Analysis_capabilities.Entry_publication
  include Analysis_capabilities.Closure_registry
  include Analysis_capabilities.Evolution
  include Analysis_capabilities.Typing_scope
  include Analysis_capabilities.Closure_scope
  include Analysis_capabilities.Statement_operations
  include Analysis_capabilities.Node_scope
  val initial_environment : env
  val observe_method_call : Json.t -> unit
  val branch_for_execution : env -> Source.expr -> bool -> env
  val register_following : Json.t -> Source.stmt list -> unit
  val speculate : (unit -> 'a) -> 'a option
  val with_block_context : Semantic.ty option -> (unit -> 'a) -> 'a * Semantic.ty list
  val output : unit -> Analysis_capabilities.node_output
  val snapshot : unit -> candidate_snapshot
  val block_returns : unit -> Semantic.ty list
  val writes : unit -> (Json.t * Semantic.ty) list
  val uses : unit -> (Json.t * Semantic.ty) list
  val explanations : unit -> (Json.t * string) list
end
