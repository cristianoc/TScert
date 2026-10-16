open Semantic
open Environment
open Source

(* Metadata accompanying an environment at a flow point. Every successor gets
   its own snapshot; join intersects facts and unions accumulated growth. *)
type environment = (string * Environment.binding) list
type metadata = {
  evolving: (string * (Json.t * bool)) list;
  grown_locals: string list;
  exact_locals: string list;
  closures: (string * (Json.t * ty list)) list;
  classes: (string * (Json.t * ty list * ty * (Semantic.key * string) list)) list;
  objects: (string * (Semantic.key * Source.expr) list) list;
  fresh_constructor: bool;
  exact_allocs: Json.t list;
  (* Each constant bound to a local, with that local: the two hold one object. *)
  holders: (string * string) list;
}
type state = { env: environment; metadata: metadata }

(* Statement semantics propose environments. Output isolation retains only the
   last visit's claims at a graph node, then publishes them after solving. The
   output payload is owned by the analysis and may contain nested body claims. *)
type 'output callbacks = {
  snapshot_metadata: unit -> metadata;
  with_path_metadata: 'result. metadata -> metadata -> (unit -> 'result) -> 'result;
  empty_output: 'output;
  with_output: 'result. string -> (unit -> 'result) -> 'result * 'output;
  publish_output: 'output -> unit;
  statement: environment -> Source.stmt -> environment;
  execute_bindings: environment -> Execution.binding_plan -> environment;
  expression: environment -> Source.expr -> ty;
  expression_effects: Source.expr -> environment -> environment;
  branch: environment -> Source.expr -> bool -> environment;
  return_expression: environment -> Source.expr -> ty;
  returned: ty -> unit;
  entry: environment -> Json.t -> unit;
  iterator_start: Flow.node -> Source.stmt -> environment -> Flow.binding -> environment;
  iterator_step: Flow.node -> Source.stmt -> environment -> Flow.binding -> Flow.binding -> environment * environment;
  (* A loop's widening of a slot: what its contract admits, at its arms. *)
  widen_slot: ty -> ty;
}

let unsupported s = Json.fail ("unsupported: " ^ s)

let statements callbacks flow_graph register_following owner_span env0 ss =
    let open Flow in
    let spans = List.map (fun (s:Source.stmt) -> s.span) ss in
    let graph = match flow_graph owner_span with
      | Some g -> g
      | None -> Json.fail "Lean supplied no control-flow graph for a body" in
    if graph.body_spans <> spans then Json.fail "Lean control-flow body disagrees with source statements";
    let syntax = Hashtbl.create 64 in
    let rec register ss =
      let rec following_statements = function
        | [] -> ()
        | s :: rest -> register_following s.span rest; following_statements rest in
      following_statements ss;
      List.iter (fun (s:Source.stmt) ->
        Hashtbl.replace syntax s.span s;
        (match s.statement with
         | If (_,a,b) -> register a; register b
         | While (_,body,update) -> register body; register update
         | Block (_,body) | ForOf (_,_,_,_,body) -> register body
         | Try (body,handler,finalizer) -> register body;
           Option.iter (fun (_,body) -> register body) handler; Option.iter register finalizer
         | Closing (close,body) -> register close; register body
         | Declare _ | Destructure _ | Return _ | Effect _ | Throw _ | Break _ | Continue -> ())) ss in
    register ss;
    let source span = match Hashtbl.find_opt syntax span with
      | Some s -> s | None -> Json.fail "flow operation names missing source syntax" in
    let scope bindings env =
      let live n = List.mem_assoc n env0 || List.exists (fun (b:Flow.binding) -> b.name=n) bindings in
      List.filter (fun (n,_) -> live n || (is_field n && live (owner n))) env in
    let capture env =
      let bound n = List.mem_assoc n env in
      let m = callbacks.snapshot_metadata () in
      {env; metadata={
        evolving=List.filter (fun (n,_) -> bound n) m.evolving;
        grown_locals=List.filter bound m.grown_locals;
        exact_locals=List.filter bound m.exact_locals;
        closures=List.filter (fun (n,_) -> bound n) m.closures;
        classes=List.filter (fun (n,_) -> bound n) m.classes;
        objects=List.filter (fun (n,_) -> bound n) m.objects;
        fresh_constructor=m.fresh_constructor; exact_allocs=m.exact_allocs;
        holders=List.filter (fun (n,m) -> bound n && bound m) m.holders}} in
    let join_env (node:Flow.node) left right =
      let left=scope node.scope left and right=scope node.scope right in
      let impossible env=List.exists (fun (n,b) -> not (is_field n) && binding_type b=Atoms []) env in
      if impossible left then right else if impossible right then left else
      List.filter_map (fun (n,b) -> match List.assoc_opt n right with
        | None -> None
        | Some c -> (match b,c with
          | Storage (contract,l),Storage (other,r) ->
            if contract <> other then unsupported "incoming paths disagree on a fixed storage contract";
            Some (n,holding contract (union l r))
          | Local (contract,l),Local (_,r) -> Some (n,Local (contract,union l r))
          | Value l,Value r -> Some (n,Value (union l r))
          | _ -> unsupported "incoming paths disagree on a binding's storage identity")) left in
    let common left right = List.filter (fun x -> List.mem x right) left in
    let combined left right = List.sort_uniq compare (left @ right) in
    let join node left_state right_state =
      let left=left_state.env and right=right_state.env in
      let impossible env=List.exists (fun (n,b) -> not (is_field n) && binding_type b=Atoms []) env in
      if impossible left then right_state else if impossible right then left_state else
      let l=left_state.metadata and r=right_state.metadata in
      {env=join_env node left right; metadata={
        evolving=common l.evolving r.evolving;
        grown_locals=combined l.grown_locals r.grown_locals;
        exact_locals=common l.exact_locals r.exact_locals;
        closures=common l.closures r.closures;
        classes=common l.classes r.classes;
        objects=common l.objects r.objects;
        fresh_constructor=l.fresh_constructor && r.fresh_constructor;
        exact_allocs=combined l.exact_allocs r.exact_allocs;
        holders=common l.holders r.holders}} in
    let publications=Array.make (Array.length graph.nodes) callbacks.empty_output in
    let transfer (node:Flow.node) state =
      let saved_metadata=capture env0 in
      let edges,output=callbacks.with_path_metadata saved_metadata.metadata state.metadata (fun () ->
        callbacks.with_output node.Flow.point (fun () ->
      let env=state.env in
      let env=if node.Flow.id=graph.Flow.entry then
        match graph.Flow.prologue with None -> env | Some plan -> callbacks.execute_bindings env plan
        else env in
      callbacks.entry env node.source;
      let next id env = id,capture (scope graph.nodes.(id).scope env) in
      let infer_return span = match (source span).statement with
        | Return e -> callbacks.return_expression env e
        | _ -> Json.fail "a return flow operation names another statement" in
      let edges = match node.action with
        | Flow.End -> []
        | Flow.Jump id -> [next id env]
        | Flow.Declaration (span,name,initial_source,mutable_,id) ->
          let s=source span in
          let selected=match s.statement with
            | Declare (source_mutable,bindings) ->
              if source_mutable <> mutable_ then Json.fail "flow declaration changes binding mutability";
              let bindings=List.filter (fun (binding,_,(init:Source.expr)) -> binding=name && init.pos=initial_source) bindings in
              if List.length bindings <> 1 then Json.fail "flow declaration names a missing or ambiguous binding";
              {s with statement=Declare (mutable_,bindings)}
            | _ -> Json.fail "flow declaration names another statement" in
          [next id (callbacks.statement env selected)]
        | Flow.Statement (span,id) ->
          let s=source span in
          let after=match node.Flow.binding_plan with
            | Some plan -> callbacks.execute_bindings env plan
            | None -> callbacks.statement env s in
          (match s.statement with Throw _ -> [] | _ -> [next id after])
        | Flow.Branch (span,yes,no) ->
          let s=source span in
          let cond=match s.statement with If (c,_,_) | While (c,_,_) -> c
            | _ -> Json.fail "a branch flow operation names another statement" in
          ignore (callbacks.expression env cond);
          let after=callbacks.expression_effects cond env in
          [next yes (callbacks.branch after cond true);next no (callbacks.branch after cond false)]
        | Flow.Return span ->

          callbacks.returned (infer_return span); []
        | Flow.ReturnSave (span,b,id) ->

          let t=infer_return span in
          let after=match (source span).statement with Return e -> callbacks.expression_effects e env | _ -> env in
          [next id (extend after b.name (Value t))]
        | Flow.ReturnHeld b ->
          callbacks.returned (binding_type (lookup env b.name)); []
        | Flow.Rethrow _ -> []
        | Flow.DiscardThrow (_,id) -> [next id env]
        | Flow.IteratorStart (span,b,id) ->
          [next id (callbacks.iterator_start node (source span) env b)]
        | Flow.IteratorStep (span,b,element,yes,no) ->
          let yielded,finished=callbacks.iterator_step node (source span) env b element in
          [next yes yielded;next no finished] in
      (* Lean names a handler only on a node whose expression may throw: a
         node of a statement that reads and writes slots and constants alone
         has none, so no edge carries this statement's states to it. *)
      let rec quiet (e:Source.expr) = match e.node with
        | Id n -> (match List.assoc_opt n env with Some (Storage _) -> false | _ -> true)
        | Literal _ -> true
        | Assign (n,rhs) -> (match List.assoc_opt n env with Some (Local _) -> quiet rhs | _ -> false)
        | _ -> false in
      let silent = match node.action with
        | Flow.Jump _ | Flow.End -> true
        | Flow.Statement (span,_) ->
          (match (source span).statement with Effect e -> quiet e | _ -> false)
        | Flow.Declaration (span,name,_,mutable_,_) ->
          (not mutable_ || not (List.exists (fun (b:Flow.binding) -> b.name=name && b.source=span) graph.cells))
          && (match (source span).statement with
              | Declare (_,bindings) -> List.for_all (fun (b,_,init) -> b <> name || quiet init) bindings
              | _ -> false)
        | _ -> false in
      let edges=match node.handler with
        | None -> edges
        | Some h ->
          (* A silent statement's edge carries no throw: its caught value is
             of the empty type, which a join with any other edge drops, and
             which marks a handler no edge reaches as unreachable. *)
          let caught=if silent then Atoms [] else top in
          let exceptional=scope h.scope (forget env) in
          let exceptional=if List.mem_assoc h.binding.name exceptional then
              List.map (fun (n,b) -> if n=h.binding.name then n,Value caught else n,b) exceptional
            else extend exceptional h.binding.name (Value caught) in
          next h.target exceptional :: edges in
      edges)) in
      publications.(node.id) <- output;
      edges in
    let states=Flow.solve ~join ~transfer
      ~widen:(fun _ previous state ->
        (* A slot still changing here is widened to its contract; one that
           settled keeps what it holds, a branch's narrowing included. *)
        let settled n b = List.assoc_opt n previous.env = Some b in
        {state with env=List.map (fun (n,b) -> match b with
          | Local (contract,_) when not (settled n b) -> n,Local (contract,callbacks.widen_slot contract)
          | _ -> n,b) (forget state.env)}) graph (capture env0) in
    Array.iter callbacks.publish_output publications;
    let completed=Array.to_list (Array.mapi (fun id state -> match graph.nodes.(id).action,state with
      | Flow.End,Some state -> Some (scope [] state.env) | _ -> None) states) |> List.filter_map Fun.id in
    match completed with [] -> env0 | first::rest ->
      List.fold_left (join_env {graph.nodes.(graph.entry) with scope=[]}) first rest
