(* analysis_state.mli seals candidate storage and context ownership. *)
(* analysis_capabilities.ml describes the operation domains supplied to component functors. *)
(* One inference pass owns its candidate output, lexical metadata and active
   typing scope. The diagnostic observations belong to the enclosing run. *)
open Semantic
open Environment
open Source
open Type_queries
open Proposal_types
open Analysis_capabilities
type env = (string * Environment.binding) list
type expression_infer = ?expected:ty -> env -> Source.expr -> ty
type body_infer = Json.t -> ty option -> env -> Source.stmt list -> env * ty list

(* A speculation copies this record and restores its pointer as a whole.
   Consumers always dereference local at access time; no field stores a ref. *)
type local = {
  mutable closures: (string * (Json.t * ty list)) list;
  mutable requests: (Json.t * Semantic.signature) list;
  mutable classes: (string * (Json.t * ty list * ty * (Semantic.key * string) list)) list;
  mutable entries: entry list;
  mutable expressions: expression list;
  mutable instantiations: ((string * Json.t) * (string * type_argument) list) list;
  mutable instances: ((string * Json.t) * ty) list;
  mutable arrows: (Json.t * overlay list) list;
  mutable evolving: (string * (Json.t * bool)) list;
  mutable grown_locals: string list;
  mutable exact_locals: string list;
  mutable objects: (string * (Semantic.key * Source.expr) list) list;
  mutable fresh_constructor: bool;
  mutable exact_allocs: Json.t list;
  mutable holders: (string * string) list;
  mutable contracts: contract list;
  mutable current_point: string;
  speculative_typing: bool;
 }

type t = {
  local: local ref;
  diagnostics: Proposal_diagnostics.state;
  flows: Flow.graph list;
  offered: (Json.t * Semantic.signature list) list;
  declarations: Source.declaration list;
  module_functions: (string * ty Lazy.t) list;
  (* What each module function declared in the source does with the actuals
     past its parameters. *)
  arities: (string * Module_contract.arity) list;
  assumed: (Json.t * ty) list;
  env0: env;
  rigid_bounds: (Semantic.rigid * ty) list ref;
  resolution_parameters: Semantic.quantifier list;
  writes: (Json.t * ty) list ref;
  (* What an evolving binding's uses expect it to hold, by its initializer. *)
  uses: (Json.t * ty) list ref;
  typing_roots: (string * Execution.plan * env) list ref;
  executions: (string * Json.t, Execution.plan) Hashtbl.t;
  expression_hints: (Json.t, Source.expr) Hashtbl.t;
  block_result: ty option ref;
  block_returned: ty list ref ref;
  following: (Json.t, Source.stmt list) Hashtbl.t;
}

let create diagnostics flows offered declarations module_functions arities bounds assumed (f:Source.fn) =
  let flows=List.map (fun (g:Flow.graph) -> {g with Flow.nodes=Array.copy g.Flow.nodes}) flows in
  let executions = Hashtbl.create 128 and expression_hints = Hashtbl.create 128 in
  let resolution_parameters = ref f.quantified in
  List.iter (fun (graph:Flow.graph) -> Array.iter (fun (node:Flow.node) ->
    List.iter (fun (source,plan) -> Hashtbl.replace executions (node.Flow.point,source) plan)
      node.Flow.executions) graph.Flow.nodes) flows;
  let rec register_expression (e:Source.expr) =
    Hashtbl.replace expression_hints e.pos e;
    (match e.node with
     | Lambda (_,quantified,_,_,_,_,_) -> resolution_parameters := quantified @ !resolution_parameters
     | NullishAssign (name,source,_) ->
       Hashtbl.replace expression_hints source {pos=source;node=Id name}
     | _ -> ());
    List.iter register_expression (Source.children e) in
  List.iter (fun s -> List.iter register_expression (Source.statement_children s)) f.body;
  (* An assigned parameter is a cell where the flow graph says so, and a
     slot of the activation otherwise. *)
  let in_cell n = List.exists (fun (g:Flow.graph) -> g.Flow.owner=f.name_pos &&
    List.exists (fun (b:Flow.binding) -> b.Flow.name=n && b.Flow.source=f.name_pos) g.Flow.cells) flows in
  let env0 = List.map (fun (n,t) ->
    n,if List.exists (assigns n) f.body then (if in_cell n then cell t else Local (t,arms declarations t))
      else Value (arms declarations t)) f.params in
  { diagnostics; flows; offered; declarations; module_functions; arities; assumed; env0;
    executions; expression_hints; rigid_bounds=ref bounds;
    resolution_parameters = !resolution_parameters; writes=ref []; uses=ref [];
    typing_roots=ref []; block_result=ref (Some f.result);
    block_returned=ref (ref []); following=Hashtbl.create 64;
    local=ref { entries=[]; expressions=[]; instantiations=[]; current_point="";
      contracts=[]; evolving=[]; grown_locals=[]; exact_locals=[]; closures=[];
      requests=[]; classes=[]; fresh_constructor=false; objects=[]; exact_allocs=[]; holders=[];
      instances=[]; arrows=[]; speculative_typing=false } }

(* Writes and diagnostic observations belong to the pass and run respectively;
   they survive speculation. Proposal output and path metadata belong to local. *)
let speculate state f =
  let saved = !(state.local) in
  state.local := { saved with speculative_typing=true };
  Fun.protect ~finally:(fun () -> state.local := saved)
    (fun () -> try Some (f ()) with Json.Error _ -> None)

(* Typing contexts are dynamically scoped around recursive inference. *)
let with_current_point state point f =
  let saved = (!(state.local)).current_point in
  (!(state.local)).current_point <- point;
  Fun.protect ~finally:(fun () -> (!(state.local)).current_point <- saved) f

let with_rigid_bounds state bounds f =
  let saved = !(state.rigid_bounds) in
  state.rigid_bounds := bounds;
  Fun.protect ~finally:(fun () -> state.rigid_bounds := saved) f

let with_typing_roots state roots f =
  let saved = !(state.typing_roots) in
  state.typing_roots := roots;
  Fun.protect ~finally:(fun () -> state.typing_roots := saved) f

let with_block_context state result f =
  let saved_result = !(state.block_result) in
  let saved_returned = !(state.block_returned) in
  let returned = ref [] in
  state.block_result := result;
  state.block_returned := returned;
  Fun.protect ~finally:(fun () ->
    state.block_result := saved_result;
    state.block_returned := saved_returned) (fun () -> let result = f () in result,!returned)

type candidate_snapshot = {
  point: string;
  speculative: bool;
  output: node_output;
  metadata: Proposal_flow.metadata;
}

(* The owner builds operation capabilities. Functor consumers receive restricted
   Inputs signatures and cannot recover this owner or its mutable storage. *)
module Access (S : sig val state : t end) = struct
  let state = S.state
  let local = state.local
  let declarations = state.declarations
  let offered = state.offered
  let initial_environment = state.env0
  let current_point () = (!local).current_point
  let rigid_bounds () = !(state.rigid_bounds)
  let rigid_bound r = List.assoc_opt r (rigid_bounds ())
  let owned_resolution r = List.find_map (fun (q:Semantic.quantifier) ->
    if q.identity=r then q.resolution else None) state.resolution_parameters
  let observation_owner r = List.find_map (fun (q:Semantic.quantifier) ->
    match q.resolution with
    | Some (observation,Some result) when observation=r -> Some (q.identity,result)
    | _ -> None) state.resolution_parameters
  let field_type declarations seen t key = Type_queries.field_type (rigid_bounds ()) declarations seen t key
  let index_type declarations seen t key = Type_queries.index_type (rigid_bounds ()) declarations seen t key
  let module_names = List.map fst state.module_functions
  let module_arity name = List.assoc_opt name state.arities
  let is_local name = List.mem_assoc name state.env0
  let module_type name = Option.map Lazy.force (List.assoc_opt name state.module_functions)
  let execution_at source = Hashtbl.find_opt state.executions (current_point (),source)
  let expression_hint source = Hashtbl.find_opt state.expression_hints source
  let claimed_type source = List.find_map (fun (x:expression) ->
    if x.point=current_point () && x.pos=source then Some x.type_ else None) (!local).expressions
  let latest_claim source = List.find_map (fun (x:expression) ->
    if x.pos=source then Some x.type_ else None) (!local).expressions
  let instantiation_at source = List.assoc_opt (current_point (),source) (!local).instantiations
  let evolved key = Option.value (List.assoc_opt key state.assumed) ~default:(Atoms [])
  let expected_result () = !(state.block_result)
  let speculative_typing () = (!local).speculative_typing
  let typing_roots () = !(state.typing_roots)
  let block_returns () = !(!(state.block_returned))
  let writes () = !(state.writes)
  let uses () = !(state.uses)
  let explanations () = !(state.diagnostics.Proposal_diagnostics.explanations)
  let observations () : observations = {
    for_in_keys= !(state.diagnostics.Proposal_diagnostics.for_in_keys);
    method_callees= !(state.diagnostics.Proposal_diagnostics.method_callees);
    shape_tests= !(state.diagnostics.Proposal_diagnostics.shape_tests);
    unknown_instance_tests= !(state.diagnostics.Proposal_diagnostics.unknown_instance_tests) }
  let explain = Proposal_diagnostics.explain state.diagnostics
  let observe_method_call pos =
    let observations=state.diagnostics.Proposal_diagnostics.method_callees in
    observations := pos :: !observations
  let observe_for_in name =
    let observations=state.diagnostics.Proposal_diagnostics.for_in_keys in
    observations := name :: !observations
  let branch_for_execution env cond truth = Refinement.branch_with state.diagnostics
    (rigid_bounds ()) declarations ~modules:(fun name ->
      try module_type name with Json.Error _ -> None) ~claimed:claimed_type env cond truth
  let path_facts () : Proposal_flow.metadata = {
    Proposal_flow.evolving=(!local).evolving; grown_locals=(!local).grown_locals;
    exact_locals=(!local).exact_locals; closures=(!local).closures;
    classes=(!local).classes; objects=(!local).objects;
    fresh_constructor=(!local).fresh_constructor; exact_allocs=(!local).exact_allocs;
    holders=(!local).holders }
  let restore_metadata (m:Proposal_flow.metadata) =
    (!local).evolving <- m.Proposal_flow.evolving; (!local).grown_locals <- m.Proposal_flow.grown_locals;
    (!local).exact_locals <- m.Proposal_flow.exact_locals; (!local).closures <- m.Proposal_flow.closures;
    (!local).classes <- m.Proposal_flow.classes; (!local).objects <- m.Proposal_flow.objects;
    (!local).fresh_constructor <- m.Proposal_flow.fresh_constructor; (!local).exact_allocs <- m.Proposal_flow.exact_allocs;
    (!local).holders <- m.Proposal_flow.holders
  let with_path_metadata enclosing incoming f =
    Fun.protect ~finally:(fun () -> restore_metadata enclosing)
      (fun () -> restore_metadata incoming; f ())
  let output () : node_output = {
    entries=(!local).entries; expressions=(!local).expressions;
    contracts=(!local).contracts; arrows=(!local).arrows;
    requests=(!local).requests; instances=(!local).instances;
    instantiations=(!local).instantiations }
  let restore_output (o:node_output) =
    (!local).entries <- o.entries; (!local).expressions <- o.expressions;
    (!local).contracts <- o.contracts; (!local).arrows <- o.arrows;
    (!local).requests <- o.requests; (!local).instances <- o.instances;
    (!local).instantiations <- o.instantiations
  let snapshot () = {point=current_point ();speculative=speculative_typing ();
    output=output ();metadata=path_facts ()}
  let with_output point action =
    let enclosing_point=current_point () and enclosing_output=output () in
    Fun.protect ~finally:(fun () -> restore_output enclosing_output;
      (!local).current_point <- enclosing_point) (fun () ->
        restore_output empty_output; (!local).current_point <- point;
        let result=action () in result,output ())
  let publish_expression pos type_ instantiation =
    (!local).expressions <- {point=current_point ();pos;type_;instantiation} :: (!local).expressions
  let publish_entry start bindings =
    (!local).entries <- {point=current_point ();start;bindings} :: (!local).entries
  let publish_instance source type_ =
    (!local).instances <- ((current_point (),source),type_) :: (!local).instances
  let publish_substitution source substitution =
    (!local).instantiations <- ((current_point (),source),substitution) :: (!local).instantiations
  let publish_request pos signature = (!local).requests <- (pos,signature) :: (!local).requests
  let publish_arrow pos rows = (!local).arrows <- (pos,rows) :: (!local).arrows
  let publish_contract (c:contract) =
    match List.find_opt (fun (other:contract) -> other.pos=c.pos && other.name=c.name) (!local).contracts with
    | None -> (!local).contracts <- c :: (!local).contracts
    | Some other when other.type_=c.type_ -> ()
    | Some _ -> Proposal_diagnostics.unsupported "a storage contract differs across executions of its declaration"
  let publish_output (o:node_output) =
    (!local).entries <- o.entries @ (!local).entries;
    (!local).expressions <- o.expressions @ (!local).expressions;
    (!local).arrows <- o.arrows @ (!local).arrows;
    (!local).requests <- o.requests @ (!local).requests;
    (!local).instances <- o.instances @ (!local).instances;
    (!local).instantiations <- o.instantiations @ (!local).instantiations;
    List.iter publish_contract o.contracts
  let collect_overload_row_claims action =
    let enclosing=output () in
    Fun.protect ~finally:(fun () ->
      (!local).entries <- enclosing.entries; (!local).expressions <- enclosing.expressions;
      (!local).contracts <- enclosing.contracts) (fun () ->
        (!local).entries <- []; (!local).expressions <- []; (!local).contracts <- [];
        action ();
        {row_contracts=List.rev (!local).contracts;row_entries=List.rev (!local).entries;
          row_expressions=List.rev (!local).expressions})
  let forget_exact_local name = (!local).exact_locals <- List.filter ((<>) name) (!local).exact_locals
  let mark_fresh_constructor () = (!local).fresh_constructor <- true
  let clear_evolving_binding name = (!local).evolving <- List.remove_assoc name (!local).evolving
  let register_evolving_binding name pos array = (!local).evolving <- (name,(pos,array)) :: (!local).evolving
  let mark_exact_allocations positions = (!local).exact_allocs <- positions @ (!local).exact_allocs
  let mark_exact_local name = (!local).exact_locals <- name :: (!local).exact_locals
  let record_growth name = (!local).grown_locals <- name :: (!local).grown_locals
  (* A binding of [n] ends every holding [n] took part in; a constant bound
     to the local [m] holds [m]'s object. *)
  let forget_holder n = (!local).holders <- List.filter (fun (a,b) -> a <> n && b <> n) (!local).holders
  let record_holder n m = (!local).holders <- (n,m) :: (!local).holders
  (* The locals holding [n]'s object: [n], and every local a chain of
     constants bound to one another links to it. *)
  let holders_of n =
    let rec close seen =
      let next = List.concat_map (fun (a,b) ->
        (if List.mem a seen && not (List.mem b seen) then [b] else [])
        @ (if List.mem b seen && not (List.mem a seen) then [a] else [])) (!local).holders in
      if next = [] then seen else close (List.sort_uniq compare (seen @ next)) in
    close [n]
  let prepare_constructor tails =
    let fresh=(!local).fresh_constructor in
    (!local).fresh_constructor <- false;
    if fresh then mark_exact_allocations tails;
    fresh
  let register_closure name pos params = (!local).closures <- (name,(pos,params)) :: (!local).closures
  let register_object name fields = (!local).objects <- (name,fields) :: (!local).objects
  let register_class name info = (!local).classes <- (name,info) :: (!local).classes
  let propose_use key t = state.uses := (key,t) :: List.remove_assoc key !(state.uses)
  let evolve key t = state.writes :=
    (key,union (Option.value (List.assoc_opt key !(state.writes)) ~default:(Atoms [])) (widen t))
    :: List.remove_assoc key !(state.writes)
  let record_return t = !(state.block_returned) := t :: !(!(state.block_returned))
  let following_statements span = Option.value (Hashtbl.find_opt state.following span) ~default:[]
  let register_following span following = Hashtbl.replace state.following span following
  (* A statement solver owns the returned node array. Closure inference reads
     only its entry description, so it receives no alias to a graph array. *)
  (* Whether the flow graphs hold a mutable binding, named with its declaring
     statement (a parameter: with its body's owner), in a cell. *)
  let held_in_cell name source = List.exists (fun (g:Flow.graph) ->
    List.exists (fun (b:Flow.binding) -> b.Flow.name=name && b.Flow.source=source) g.Flow.cells) state.flows
  let flow_graph owner = Option.map (fun (g:Flow.graph) -> {g with Flow.nodes=Array.copy g.Flow.nodes})
    (List.find_opt (fun (g:Flow.graph) -> g.Flow.owner=owner) state.flows)
  let closure_entry owner = Option.map (fun (g:Flow.graph) ->
    g.Flow.nodes.(g.Flow.entry).Flow.point,g.Flow.prologue)
    (List.find_opt (fun (g:Flow.graph) -> g.Flow.owner=owner) state.flows)
  let speculate action = speculate state action
  let with_current_point point action = with_current_point state point action
  let with_rigid_bounds bounds action = with_rigid_bounds state bounds action
  let with_typing_roots roots action = with_typing_roots state roots action
  let with_block_context result action = with_block_context state result action
end
