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
  (* Whether the statement just transferred is an expression whose claimed
     type is empty: its normal edge carries every value and local slot at the
     empty type, with storage bindings unchanged. *)
  cannot_return_normally: Source.stmt -> bool;
  (* Whether a binding's declared type is an array, whose length Lean reads
     from its store (`Linear_facts.comparison_bounds`). *)
  array_binding: environment -> string -> string list -> bool;
  (* Whether the iterator loop claim retains separation from this binding. *)
  iterator_separated: string -> bool;
  execute_bindings: environment -> Execution.binding_plan -> environment;
  expression: environment -> Source.expr -> ty;
  expression_effects: Source.expr -> environment -> environment;
  condition: environment -> Source.expr -> environment * environment;
  return_expression: environment -> Source.expr -> ty;
  returned: ty -> unit;
  entry: environment -> Json.t -> unit;
  iterator_start: Flow.node -> Source.stmt -> environment -> Flow.binding -> environment;
  iterator_step: Flow.node -> Source.stmt -> environment -> Flow.binding -> Flow.binding -> environment * environment;
  (* An early binding where its statement list is entered (SOURCE-ELABORATION.md,
     "Lexical bindings before initialization"): its cell, at its stated
     type, from there on; the declaration later initializes it. *)
  early: environment -> Source.stmt -> string -> environment;
  (* A loop's widening of a slot: what its contract admits, at its arms. *)
  widen_slot: ty -> ty;
}

let unsupported = Json.unsupported

(* What a condition's false branch states of names (PROGRAM-TYPING.md,
   "Writes at a checked index"): `a || b` false, both false; `(k & m) !== k`
   false, with `m` a number literal on either side of `&` and either operand
   of `!==` the other, `k` an index; `k > xs.length` or `k >= xs.length`
   false, or `xs.length < k` or `xs.length <= k`, `k` at most the length. *)
type false_fact = IsIndex of string | AtMost of string * string
let rec false_facts (cond:Source.expr) = match cond.node with
  | Logical (false,a,b) -> false_facts a @ false_facts b
  | Equality (StrictUnequal,a,b) ->
    let masked (m:Source.expr) (k:Source.expr) = match m.node,k.node with
      | Arith (BitAnd,{node=Id k';_},{node=Literal (LNumber _);_}),Id k
      | Arith (BitAnd,{node=Literal (LNumber _);_},{node=Id k';_}),Id k when k = k' -> [IsIndex k]
      | _ -> [] in
    masked a b @ masked b a
  | Arith ((Gt | Ge),{node=Id k;_},{node=Read ({node=Id xs;_},Name "length");_})
  | Arith ((Lt | Le),{node=Read ({node=Id xs;_},Name "length");_},{node=Id k;_}) -> [AtMost (xs,k)]
  | _ -> []
(* The array and index pairs a guard's false branch bounds: `k` an index at
   most `xs.length`, its comparison evaluated after the test making `k` an
   index, as Lean's `bound-compare` reads the index fact the comparison's
   operand already has. *)
let guard_bounds (cond:Source.expr) =
  let rec scan seen = function
    | [] -> []
    | IsIndex k :: rest -> scan (k :: seen) rest
    | AtMost (xs,k) :: rest when List.mem k seen -> (xs,k) :: scan seen rest
    | AtMost _ :: rest -> scan seen rest in
  scan [] (false_facts cond)
let statements callbacks flow_graph register_following owner_span env0 ss =
    let open Flow in
    (* A closure's body holds its own bindings, not those it captures: only
       an outermost body's inputs are slots of its unit. *)
    let outermost = !Linear_facts.body_depth = 0 in
    let spans = List.map (fun (s:Source.stmt) -> s.span) ss in
    let graph = match flow_graph owner_span with
      | Some g -> g
      | None -> Json.fail "Lean supplied no control-flow graph for a body" in
    if graph.body_spans <> spans then Json.fail "Lean control-flow body disagrees with source statements";
    (* The constants holding an array literal's object: Lean states each
       one's store field apart from the store fields of the arrays of the
       older slots in its scope no write replaces (`Observations.separationFacts`), whatever
       the heap holds, so a push into one keeps the other's length. *)
    let array_constants =
      let rec collect ss = List.concat_map (fun (s:Source.stmt) -> match s.statement with
        | Source.Declare (false,bindings) -> List.filter_map (fun (n,_,(init:Source.expr)) ->
            match init.node with Source.ArrayLiteral (_,[]) -> Some n | _ -> None) bindings
        | Source.If (_,a,b) -> collect a @ collect b
        | Source.While (_,b,u) -> collect (b @ u)
        | Source.Block (_,b) | Source.ForOf (_,_,_,_,b) -> collect b
        | Source.Try (b,h,f) -> collect (b @ (match h with Some (_,hs) -> hs | None -> []) @ Option.value f ~default:[])
        | Source.Closing (c,b) -> collect (b @ c)
        | _ -> []) ss in
      collect ss in
    let separated env (scope:Flow.binding list) =
      let names = List.map (fun (b:Flow.binding) -> b.name) scope in
      let rec pairs = function
        | [] -> []
        | x :: older ->
          (if List.mem x array_constants then
             List.filter_map (fun m -> if m <> x && Linear_facts.slot_binding env m && callbacks.array_binding env m []
               && not (List.exists (Source.assigns m) ss)
               then Some (x,m) else None) older
           else []) @ pairs older in
      pairs names in
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
      (* A binding leaving scope is eliminated from the linear facts
         (`Linear_facts.forget`), as Lean eliminates a dropped slot. *)
      let dead = List.sort_uniq compare (List.concat_map (fun ((t,_) : Linear_facts.fact) ->
        List.filter_map (fun (x,_) -> let b = Linear_facts.term_binding x in if live b then None else Some b) t)
        (Linear_facts.facts env)) in
      let env = if dead = [] then env
        else Linear_facts.add env (List.fold_left (fun fs x -> Linear_facts.forget x fs) (Linear_facts.facts env) dead) in
      List.filter (fun (n,_) -> live n || (is_field n && live (owner n)) ||
        (match Linear_facts.dfact_parts n with Some d -> List.for_all live (Linear_facts.dbindings d) | None -> false) ||
        (match Linear_facts.gfact_parts n with Some g -> List.for_all live (Linear_facts.gbindings g) | None -> false) ||
        (match Linear_facts.efact_parts n with Some e -> List.for_all live (Linear_facts.ebindings e) | None -> false) ||
        (match Linear_facts.rfact_parts n with Some (x,y) -> live x && live y | None -> false) ||
        (match Linear_facts.sfact_parts n with Some f -> List.for_all live (Linear_facts.sbindings f) | None -> false) ||
        (match bound_parts n with Some (a,i,_) -> live a && live i | None -> false) ||
        (match fact_parts n with Some (t,_) -> List.for_all (fun (x,_) -> live (Linear_facts.term_binding x)) t | None -> false)) env in
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
      let joined_facts=Linear_facts.join (Linear_facts.facts left) (Linear_facts.facts right) in
      let joined_bounds=Linear_facts.join_bounds (Linear_facts.bounds left) (Linear_facts.bounds right) in
      let joined_guarded=let r=Linear_facts.gfacts right in List.filter (fun g -> List.mem g r) (Linear_facts.gfacts left) in
      let joined_disjunctions=let r=Linear_facts.dfacts right in List.filter (fun d -> List.mem d r) (Linear_facts.dfacts left) in
      let joined_every=let r=Linear_facts.efacts right in List.filter (fun e -> List.mem e r) (Linear_facts.efacts left) in
      let joined_regions=let r=Linear_facts.rfacts right in List.filter (fun e -> List.mem e r) (Linear_facts.rfacts left) in
      let joined_stores=let r=Linear_facts.sfacts right in List.filter (fun e -> List.mem e r) (Linear_facts.sfacts left) in
      let left=Linear_facts.strip_bounds (Linear_facts.strip left)
      and right=Linear_facts.strip_bounds (Linear_facts.strip right) in
      Fun.flip Linear_facts.dadd joined_disjunctions @@
      Fun.flip Linear_facts.radd joined_regions @@
      Fun.flip Linear_facts.sadd joined_stores @@
      Fun.flip Linear_facts.eadd joined_every @@
      Fun.flip Linear_facts.gadd joined_guarded @@
      Fun.flip Linear_facts.add_bounds joined_bounds @@
      Fun.flip Linear_facts.add joined_facts @@
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
      (* Where both are, the earlier state stays, so a loop no path reaches
         settles. *)
      if impossible right then left_state else if impossible left then right_state else
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
    let early_bindings=Array.fold_left (fun acc (node:Flow.node) -> match node.action with
      | Flow.Early (bs,_) -> List.map (fun (span,name,_,_) -> span,name) bs @ acc
      | _ -> acc) [] graph.nodes in
    (* The array bindings in scope where each iterator starts, by the
       iterator's binding, but the constants bound to a literal: Lean's
       array iterator is allocated apart from their stores, which its
       separation states of every older slot but an allocated constant
       (`ScopeBinding.fresh`), and its step changes only its own locations
       (`call-own`), so the step preserves their lengths' facts. *)
    let iterator_arrays : (string, string list) Hashtbl.t = Hashtbl.create 4 in
    let transfer (node:Flow.node) state =
      let saved_metadata=capture env0 in
      let edges,output=callbacks.with_path_metadata saved_metadata.metadata state.metadata (fun () ->
        callbacks.with_output node.Flow.point (fun () ->
      let env=state.env in
      let env=if node.Flow.id=graph.Flow.entry then
        match graph.Flow.prologue with None -> env | Some plan -> callbacks.execute_bindings env plan
        else env in
      (* A loop's invariant (ARITHMETIC.md, "Loop invariants"): its facts
         hold at the head, which every edge into it establishes (Lean's
         head assertion), over the bindings its positions name. *)
      let env = match node.action with
        | Flow.Branch (span,_,_) ->
          (match (source span).statement, Hashtbl.find_opt Source.loop_invariants (source span).span with
           | While _, Some (names,facts) ->
             let name p = List.nth_opt names p in
             let linear = Linear_facts.of_index_facts name facts in
             let every = List.filter_map (Linear_facts.of_every_fact name) facts in
             Linear_facts.eadd (Linear_facts.add env (Linear_facts.facts env @ linear)) (Linear_facts.efacts env @ every)
           | _ -> env)
        | _ -> env in
      callbacks.entry env node.source;
      (* The linear facts and the bounds flow beside the environment
         (`Linear_facts`); the statement callbacks see none, and a call
         stating a precondition reads those where its statement starts. *)
      let facts0 = Linear_facts.facts env in
      let bounds0 = Linear_facts.bounds env in
      let guarded0 = Linear_facts.gfacts env in
      let disjunctions0 = Linear_facts.dfacts env in
      let every0 = Linear_facts.efacts env in
      let regions0 = Linear_facts.rfacts env in
      let stores0 = Linear_facts.sfacts env in
      let env = Linear_facts.strip_bounds (Linear_facts.strip env) in
      (* A call stating a precondition is offered the bounds and facts of its
         statement's start: a proposal, which Lean refuses where an earlier
         part of the statement changed what they read. *)
      let typed_with_bounds = match node.action with
        | Flow.Statement _ | Flow.Declaration _ | Flow.Branch _ | Flow.Return _ | Flow.ReturnSave _ -> true
        | _ -> false in
      (* An update of a cell inside the statement (`xs[at++]!`) is read
         against the facts after it (`Linear_facts.linear`), as Lean reads
         the call's operands after the update's write. *)
      let updating = match node.action with
        | Flow.Statement (span,_) | Flow.Branch (span,_,_) | Flow.Return span | Flow.ReturnSave (span,_,_) ->
          (match (source span).statement with
           | Effect e | Return e | If (e,_,_) | While (e,_,_) -> Some e
           | _ -> None)
        | Flow.Declaration (span,name,initial_source,_,_) ->
          (match (source span).statement with
           | Declare (_,bindings) -> Option.map (fun (_,_,init) -> init)
               (List.find_opt (fun (b,_,(init:Source.expr)) -> b=name && init.pos=initial_source) bindings)
           | _ -> None)
        | _ -> None in
      let facts_at_calls = match updating with
        | Some e -> Linear_facts.after_cell_updates env e facts0
        | None -> facts0 in
      Linear_facts.current_bounds := (if typed_with_bounds then bounds0 else []);
      (* Element reads and bounded bitwise expressions have local names
         while calls in the statement are typed (`Linear_facts.with_reads`). *)
      let read_facts, reads = match updating with
        | Some e when typed_with_bounds ->
          Linear_facts.with_cells true (fun () ->
            Linear_facts.current_efacts := every0;
            Linear_facts.element_facts ~array:(callbacks.array_binding env) env facts_at_calls e)
        | _ -> [], [] in
      Linear_facts.element_reads := reads;
      Linear_facts.current_facts := (if typed_with_bounds then facts_at_calls @ read_facts else []);
      Linear_facts.current_dfacts := (if typed_with_bounds then disjunctions0 else []);
      Linear_facts.current_gfacts := (if typed_with_bounds then guarded0 else []);
      Linear_facts.current_efacts := every0;
      let next id env = id,capture (scope graph.nodes.(id).scope env) in
      let infer_return span = match (source span).statement with
        | Return e -> callbacks.return_expression env e
        | _ -> Json.fail "a return flow operation names another statement" in
      let edges = match node.action with
        | Flow.End -> []
        | Flow.Jump id -> [next id env]
        | Flow.Early (bindings,id) ->
          [next id (List.fold_left (fun env (span,name,_,_) -> callbacks.early env (source span) name) env bindings)]
        | Flow.Declaration (span,name,_,_,id) when List.mem (span,name) early_bindings ->
          (* The declaration initializes the early binding's cell: its
             initializer is typed and claimed as any declaration's, and the
             binding stays the cell every mention reads through a check. *)
          let s=source span in
          let selected=match s.statement with
            | Declare (mutable_,bindings) -> {s with statement=Declare (mutable_,
                List.filter (fun (binding,_,_) -> binding=name) bindings)}
            | _ -> Json.fail "flow declaration names another statement" in
          let after=callbacks.statement (List.remove_assoc name env) selected in
          [next id (List.map (fun (n,b) -> if n = name then n,lookup ~at:span env name else n,b) after)]
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
          (* A statement that cannot return normally leaves its successor an
             environment no value meets (`unreachable`). *)
          (match s.statement with
           | Throw _ -> []
           | _ when callbacks.cannot_return_normally s -> [next id (unreachable after)]
           | _ -> [next id after])
        | Flow.Branch (span,yes,no) ->
          let s=source span in
          let cond=match s.statement with If (c,_,_) | While (c,_,_) -> c
            | _ -> Json.fail "a branch flow operation names another statement" in
          ignore (callbacks.expression env cond);
          let held,failed=callbacks.condition env cond in
          (* `(k & m) !== k || k > xs.length` fails only where `k` is an
             index at most `xs.length`: the statement after it is claimed
             with that bound, which Lean checks on every edge into it. *)
          let failed=List.fold_left (fun failed (array,index) ->
            if List.mem_assoc array failed && List.mem_assoc index failed
               && not (List.mem_assoc (bound_key array index) failed)
            then failed @ [bound_key array index,Value top] else failed) failed (guard_bounds cond) in
          Linear_facts.current_bounds := [];
          Linear_facts.current_facts := [];
          Linear_facts.current_gfacts := [];
          [next yes held;next no failed]
        | Flow.Return span ->

          callbacks.returned (infer_return span); []
        | Flow.ReturnSave (span,b,id) ->

          let t=infer_return span in
          let after=match (source span).statement with Return e -> callbacks.expression_effects e env | _ -> env in
          [next id (extend after b.name (Value t))]
        | Flow.ReturnHeld b ->
          callbacks.returned (binding_type (lookup ~at:b.source env b.name)); []
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
        | Assign (n,_,rhs) -> (match List.assoc_opt n env with Some (Local _) -> quiet rhs | _ -> false)
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
      Linear_facts.current_bounds := [];
      Linear_facts.current_facts := [];
      Linear_facts.current_gfacts := [];
      Linear_facts.element_reads := [];
      (* Each normal edge's linear facts and bounds, by the node's action;
         the element reads read the quantified facts of the node's start. *)
      let edges =
        (* A cell (a binding a closure assigns, or an early one) holds no
           value slot a fact could name. *)
        let cell n = List.exists (fun (b:Flow.binding) -> b.name=n) graph.cells in
        (* A cell a fact names is one of the body's own (`cell_terms`); an
           early one names none. *)
        let unnamed n = cell n && not (!Linear_facts.cell_terms n) in
        (* A statement writing a slot inside an expression forgets its
           facts of the bindings it writes (`nested_slot_writes`). *)
        let rewritten (s:Source.stmt) = match Linear_facts.nested_slot_writes env s with
          | [] -> []
          | ns -> ns @ Linear_facts.names_assigned s env in
        let with_facts ?(ds=[]) ?(gs=[]) ?(es=[]) ?(rs=[]) ?(ss=[]) ?(dropped=[]) (id,state) fs bs =
          let unnamed n = unnamed n || List.mem n dropped in
          let cell n = cell n || List.mem n dropped in
          let fs = Linear_facts.close fs in
          let fs = List.filter (fun ((t,_) : Linear_facts.fact) -> not (List.exists (fun (n,_) -> unnamed (Linear_facts.term_binding n)) t)) fs in
          let ds = List.filter (fun d -> not (List.exists unnamed (Linear_facts.dbindings d))) ds in
          let gs = List.filter (fun g -> not (List.exists unnamed (Linear_facts.gbindings g))) gs in
          let es = List.filter (fun e -> not (List.exists unnamed (Linear_facts.ebindings e))) es in
          let rs = List.filter (fun (x,y) -> not (cell x) && not (cell y)) rs in
          let ss = List.filter (fun f -> not (List.exists cell (Linear_facts.sbindings f))) ss in
          let bs = List.filter (fun (a,i,_) -> not (cell a) && not (cell i)) (Linear_facts.bounds state.env @ bs) in
          id,{state with env=scope graph.nodes.(id).scope
            (Linear_facts.sadd (Linear_facts.radd (Linear_facts.dadd (Linear_facts.eadd (Linear_facts.gadd (Linear_facts.add_bounds (Linear_facts.add state.env (Linear_facts.deliminate fs ds)) bs) gs) es) ds) rs) ss)} in
        match node.action, edges with
        | Flow.Jump _, [e] -> [with_facts ~ds:disjunctions0 ~gs:guarded0 ~es:every0 ~rs:regions0 ~ss:stores0 e facts0 bounds0]
        | Flow.Declaration (span,name,initial_source,_,_), [e] when not (List.mem (span,name) early_bindings) ->
          let fs = match (source span).statement with
            | Declare (_,bindings) ->
              (match List.find_opt (fun (b,_,(init:Source.expr)) -> b=name && init.pos=initial_source) bindings with
               | Some (_,_,init) ->
                 Linear_facts.with_separations ~regions:(regions0 @ separated env node.scope) ~stores:stores0 (fun () ->
                   Linear_facts.declaration ~array:(callbacks.array_binding env) env facts0 name init)
               | None -> [])
            | _ -> [] in
          let gs = match (source span).statement with
            | Declare (_,bindings) ->
              (match List.find_opt (fun (b,_,(init:Source.expr)) -> b=name && init.pos=initial_source) bindings with
               | Some (_,_,init) -> Linear_facts.gdeclaration env guarded0 facts0 name init
               | None -> [])
            | _ -> [] in
          let declared = let s = source span in match s.statement with
            | Declare (m,bindings) -> {s with statement=Declare (m,
                List.filter (fun (b,_,(init:Source.expr)) -> b=name && init.pos=initial_source) bindings)}
            | _ -> s in
          let visible m = List.exists (fun (b:Flow.binding) -> b.name=m) node.scope || (outermost && List.mem_assoc m env0) in
          let rs = Linear_facts.rstatement ~array:(callbacks.array_binding env) ~visible env regions0 declared in
          [with_facts ~dropped:(rewritten (source span)) ~ds:(Linear_facts.dstatement env disjunctions0 declared) ~gs ~es:(Linear_facts.estatement ~array:(callbacks.array_binding env) ~facts:facts0 ~regions:regions0 env every0 declared) ~rs
             ~ss:(Linear_facts.sstatement ~array:(callbacks.array_binding env) ~visible env stores0 declared) e fs
             (Linear_facts.statement_bounds env bounds0 (source span))]
        | Flow.Statement (span,_), [e] ->
          let s = source span in
          [with_facts ~dropped:(rewritten s) ~ds:(Linear_facts.dstatement env disjunctions0 s) ~gs:(Linear_facts.gstatement ~bounds:bounds0 env facts0 guarded0 s)
            ~es:(Linear_facts.estatement ~array:(callbacks.array_binding env) ~facts:facts0 ~regions:regions0 env every0 s)
            ~rs:(Linear_facts.rstatement ~array:(callbacks.array_binding env) env regions0 s)
            ~ss:(Linear_facts.sstatement env stores0 s) e
            (Linear_facts.statement ~array:(callbacks.array_binding env) ~bounds:bounds0
               ~regions:(regions0 @ separated env node.scope) ~stores:stores0 env facts0 s)
            (Linear_facts.statement_bounds ~facts:facts0 ~regions:regions0 ~stores:stores0 env bounds0 s)]
        | Flow.IteratorStart (span,b,_), [e] ->
          (* `%Iterate%` of an array binding allocates its iterator and keeps
             the heap (`call-fresh`); any other iterable preserves the facts
             reading no heap. *)
          let array_iterable = match (source span).statement with
            | ForOf (_,_,_,{node=Id x;_},_) -> Linear_facts.value_binding env x && callbacks.array_binding env x []
            | _ -> false in
          let arrays = List.filter_map (fun (n,b) -> match b with
            | Value _ | Local _ when not (is_fact n) && not (is_bound n) && callbacks.array_binding env n [] && callbacks.iterator_separated n -> Some n
            | _ -> None) env in
          if array_iterable then Hashtbl.replace iterator_arrays b.name arrays else Hashtbl.remove iterator_arrays b.name;
          let fs = if array_iterable then facts0 else Linear_facts.keep_stable env facts0 in
          [with_facts ~es:(if array_iterable then every0 else []) e (Linear_facts.forget b.name fs)
             (if array_iterable then bounds0 else [])]
        | Flow.IteratorStep (_,b,element,_,_), [y;n] ->
          (* The step of an array's iterator changes only the iterator's own
             locations: lengths are kept for older arrays whose separation
             the loop claim retains. Fresh literal bindings are excluded
             by the same rule as the statement analysis's field frame. *)
          let arrays = Option.value ~default:[] (Hashtbl.find_opt iterator_arrays b.name) in
          let kept_term t = let r,path,kind = Linear_facts.term_parts t in
            Linear_facts.stable_term env t || (kind = Linear_facts.Length_term && path = [] && List.mem r arrays) in
          let fs = List.filter (fun ((t,_) : Linear_facts.fact) -> List.for_all (fun (n,_) -> kept_term n) t) facts0 in
          let fs = Linear_facts.forget element.name fs in
          let bs = List.filter (fun (a,i,_) -> List.mem a arrays && i <> element.name) bounds0 in
          [with_facts y fs bs; with_facts n fs bs]
        | Flow.Branch (span,_,_), [y;n] ->
          let s = source span in
          (match s.statement with
           | If (c,_,_) | While (c,_,_) ->
             (* A test updating a cell (`++i >= n`): the update's facts,
                then the test as one writing no other location
                (`after_cell_updates`). *)
             let updated = Linear_facts.after_cell_updates env c facts0 in
             Linear_facts.with_cells (updated != facts0) @@ fun () ->
             let facts0 = updated in
             let (t,bt),(f,bf) = Linear_facts.test ~array:(callbacks.array_binding env) env facts0 c in
             let kept = Linear_facts.statement_bounds env bounds0 s in
             (* A test that may write the heap, a call of a function changing
                it, preserves the facts its footprint preserves, as Lean preserves
                them past the call, and every other test none reading the heap:
                its own branches' included, and no bound. *)
             let heap_free = Linear_facts.statement_heap_free env s in
             (* A test that calls a function stating facts at its returns
                gains them, as Lean's `call-ensures` states them after the
                call. *)
             let reading fs = if heap_free then fs
               else
                 let changes,regional = Linear_facts.with_regional ~regions:(regions0 @ separated env node.scope) ~stores:stores0
                   (fun () -> Linear_facts.write_changes ~facts:facts0 ~bounds:bounds0 env c) in
                 let kept = match changes with
                 (* A test whose one write is a call's: the facts its
                    footprint keeps (`fact-kept`), as at a statement. *)
                 | Some ch -> List.filter (fun f -> (Linear_facts.fact_kept ch f || Linear_facts.stable_fact env f) &&
                     Linear_facts.region_keeps env regional f) fs
                 | None -> Linear_facts.keep_stable env fs in
                 Linear_facts.record_loss env c.pos [c] changes fs kept;
                 Linear_facts.kept_or_all fs kept @ Linear_facts.test_call_facts ~held:facts0 env c in
             let bounds bs = if heap_free then bs else [] in
             (* Each answer's guard eliminations (`unguardIndices`): what its
                test excludes of a path frees the facts guarded by it. *)
             let guarded answer =
               let gs = if heap_free then guarded0 else Linear_facts.gkept env guarded0 in
               let introduced = if heap_free then Linear_facts.gtest ~array:(callbacks.array_binding env) env facts0 c answer else [] in
               Linear_facts.geliminate (Linear_facts.excluded env c answer) (gs @ introduced) in
             let ty,gy = guarded true and tn,gn = guarded false in
             let es = if heap_free then every0 else [] in
             let rs = if heap_free then regions0 else [] in
             let ss = if heap_free then stores0 else List.filter (Linear_facts.skept env s) stores0 in
             let dropped = rewritten s in
             [with_facts ~dropped ~ds:(if heap_free then disjunctions0 else []) ~gs:gy ~es ~rs ~ss y (reading (facts0 @ t @ ty) @ Linear_facts.test_conditional_facts env c true) (kept @ bounds bt);
              with_facts ~dropped ~ds:(if heap_free then disjunctions0 else []) ~gs:gn ~es ~rs ~ss n (reading (facts0 @ f @ tn) @ Linear_facts.test_conditional_facts env c false) (kept @ bounds bf)]
           | _ -> edges)
        | _ -> edges in
      let edges=match node.handler with
        | None -> edges
        | Some h ->
          (* A silent statement's edge carries no throw: its caught value is
             of the empty type, which a join with any other edge drops, and
             which marks a handler no edge reaches as unreachable. *)
          let caught=if silent then Atoms [] else top in
          (* A throw may follow a write the statement makes inside an
             expression: a slot it writes holds a value of its contract. *)
          let written=match node.action with
            | Flow.Statement (span,_) | Flow.Declaration (span,_,_,_,_) | Flow.Branch (span,_,_)
            | Flow.Return span | Flow.ReturnSave (span,_,_) -> Some (source span)
            | _ -> None in
          let exceptional=List.map (fun (n,b) -> match b,written with
            | Local (contract,_),Some s when Source.assigns n s -> n,Local (contract,contract)
            | _ -> n,b) (scope h.scope (forget env)) in
          let exceptional=if List.mem_assoc h.binding.name exceptional then
              List.map (fun (n,b) -> if n=h.binding.name then n,Value caught else n,b) exceptional
            else extend exceptional h.binding.name (Value caught) in
          next h.target exceptional :: edges in
      edges)) in
      publications.(node.id) <- output;
      edges in
    (* The body's cells a fact may name: its own, early ones aside. *)
    let saved_cells = !Linear_facts.cell_terms in
    let own_cells n = List.exists (fun (b:Flow.binding) -> b.name=n) graph.cells &&
      not (List.exists (fun (_,m) -> m = n) early_bindings) in
    let saved_parameters = !Linear_facts.parameter_binding in
    let own_parameters n = List.mem_assoc n env0 && not (own_cells n) in
    let saved_depth = !Linear_facts.body_depth in
    let states=Fun.protect ~finally:(fun () -> Linear_facts.cell_terms := saved_cells;
        Linear_facts.parameter_binding := saved_parameters; Linear_facts.body_depth := saved_depth) @@ fun () ->
      Linear_facts.body_depth := saved_depth + 1;
      Linear_facts.cell_terms := own_cells;
      Linear_facts.parameter_binding := own_parameters;
      Flow.solve ~join ~transfer
      ~widen:(fun _ previous state ->
        (* A slot still changing here is widened to its contract; one that
           settled keeps what it holds, a branch's narrowing included. *)
        let settled n b = List.assoc_opt n previous.env = Some b in
        let keep_field n = List.assoc_opt n previous.env = List.assoc_opt n state.env in
        let kept=Linear_facts.widen (Linear_facts.facts previous.env) (Linear_facts.facts state.env) in
        let kept_bounds=Linear_facts.join_bounds (Linear_facts.bounds previous.env) (Linear_facts.bounds state.env) in
        let kept_guarded=let p=Linear_facts.gfacts previous.env in
          List.filter (fun g -> List.mem g p) (Linear_facts.gfacts state.env) in
        let kept_disjunctions=let p=Linear_facts.dfacts previous.env in
          List.filter (fun d -> List.mem d p) (Linear_facts.dfacts state.env) in
        let kept_every=let p=Linear_facts.efacts previous.env in
          List.filter (fun e -> List.mem e p) (Linear_facts.efacts state.env) in
        let kept_regions=let p=Linear_facts.rfacts previous.env in
          List.filter (fun e -> List.mem e p) (Linear_facts.rfacts state.env) in
        let kept_stores=let p=Linear_facts.sfacts previous.env in
          List.filter (fun e -> List.mem e p) (Linear_facts.sfacts state.env) in
        {state with env=Fun.flip Linear_facts.sadd kept_stores @@ Fun.flip Linear_facts.radd kept_regions @@ Fun.flip Linear_facts.dadd kept_disjunctions @@ Fun.flip Linear_facts.eadd kept_every @@ Fun.flip Linear_facts.gadd kept_guarded @@ Fun.flip Linear_facts.add_bounds kept_bounds @@
          Linear_facts.add (List.map (fun (n,b) -> match b with
          | Local (contract,_) when not (settled n b) -> n,Local (contract,callbacks.widen_slot contract)
          | _ -> n,b) (forget ~keep:keep_field (Linear_facts.strip_bounds (Linear_facts.strip state.env)))) kept}) graph (capture env0) in
    Array.iter callbacks.publish_output publications;
    let completed=Array.to_list (Array.mapi (fun id state -> match graph.nodes.(id).action,state with
      | Flow.End,Some state -> Some (scope [] state.env) | _ -> None) states) |> List.filter_map Fun.id in
    match completed with [] -> env0 | first::rest ->
      List.fold_left (join_env {graph.nodes.(graph.entry) with scope=[]}) first rest
