(* proposal_flow.ml solves the shared statement graph while preserving scopes, exception edges and node publications. *)
open Semantic
open Environment
open Source
open Inference
open Type_queries
open Proposal_types
open Proposal_diagnostics
module type Inputs = sig
  include Analysis_capabilities.Queries
  include Analysis_capabilities.Observations
  include Analysis_capabilities.Path_queries
  include Analysis_capabilities.Environment_queries
  include Analysis_capabilities.Named_closures
  include Analysis_capabilities.Claim_operations
  include Analysis_capabilities.Statement_operations
  include Analysis_capabilities.Node_scope
  include Analysis_capabilities.Expression_publication
  val register_following : Json.t -> Source.stmt list -> unit
end
module Make (S : Inputs) = struct
open S
let transfer (expr:Analysis_state.expression_infer) =
  let after e env = effects env e in
  (* The statements following each statement of a block, by its span. *)
  let rec mentions n (e:expr) =
    (match e.node with Id m -> m = n | _ -> false) || List.exists (mentions n) (Source.children e) in
  let rec stmt_mentions n (s:stmt) = match s.statement with
    | Declare (_,bs) -> List.exists (fun (_,_,e) -> mentions n e) bs
    | Destructure (p,d,e) -> List.exists (mentions n) (e :: Option.to_list d @ pattern_defaults p)
    | Return e | Effect e | Throw e -> mentions n e
    | If (c,a,b) -> mentions n c || List.exists (stmt_mentions n) (a @ b)
    | While (c,b,u) -> mentions n c || List.exists (stmt_mentions n) (b @ u)
    | Block (_,b) -> List.exists (stmt_mentions n) b
    | ForOf (_,_,_,e,b) -> mentions n e || List.exists (stmt_mentions n) b
    | Try (b,h,f) -> List.exists (stmt_mentions n)
      (b @ (match h with Some (_,h) -> h | None -> []) @ Option.value f ~default:[])
    | Closing (c,b) -> List.exists (stmt_mentions n) (b @ c)
    | Break _ | Continue -> false in
  (* Whether [n] may reach a place other than the receiver of its own member
     reads and writes, as Lean's `escapesExpr` reads it: a binding, a field,
     an argument or the receiver of a call, a result, a closure. *)
  let rec escapes n (e:expr) = match e.node with
    | Id m -> m = n
    | Read ({node=Id _;_},_) -> false
    | Index ({node=Id _;_},key) -> escapes n key
    | Write ({node=Id _;_},_,rhs) -> escapes n rhs
    | IndexWrite ({node=Id _;_},key,rhs) -> escapes n key || escapes n rhs
    | Invoke ({node=Read ({node=Id m;_},_);_},args,_,_) -> m = n || List.exists (escapes n) args
    | ObjectAssign ({node=Id _;_},sources) -> List.exists (escapes n) sources
    | Lambda _ | Ctor _ -> mentions n e
    | _ -> List.exists (escapes n) (Source.children e) in
  (* Whether a statement among [ss] adds a key other than [keys] to the
     object [n] names: `n.k = e`, `n["k"] = e`, `n[s] = e` of a symbol, or a
     write at a key known only at run time. *)
  let rec grows_later n keys ss = List.exists (fun (s:stmt) -> match s.statement with
    | Effect {node=Write ({node=Id m;_},k,_);_} -> m = n && not (List.mem k keys)
    | Effect {node=IndexWrite ({node=Id m;_},{node=Literal (LString k);_},_);_} ->
      m = n && not (List.mem (Name k) keys)
    | Effect {node=IndexWrite ({node=Id m;_},_,_);_} -> m = n
    | Effect {node=ObjectAssign ({node=Id m;_},_::_);_} -> m = n
    | If (_,a,b) -> grows_later n keys a || grows_later n keys b
    | Block (_,b) -> grows_later n keys b
    | Try (b,h,f) -> grows_later n keys (b @ (match h with Some (_,h) -> h | None -> [])
        @ Option.value f ~default:[])
    | _ -> false) ss in
  (* The first use of an unannotated constant's fresh array, in the
     statements after its declaration: where it is the whole value expected
     at a type (an annotated constant's initializer, a returned value, an
     argument of a call to a function of one plain signature), that type;
     any other first use, none. `None` where it is not used. *)
  let rec first_use env n rest = Option.join (List.find_map Fun.id (uses env n rest))
  (* Each statement's use of the constant: `Some` of where its first
     mention in the statement is the whole value expected at a type, as
     [first_use] reads it. *)
  and uses env n rest =
    let rec sink expected (e:expr) = match e.node with
      | Id m when m = n -> Some expected
      | Call ({node=Id g;_},None,args,[],[]) when g <> n ->
        let params = match (try declared_head declarations [] (resolve env g) with Json.Error _ -> Atoms []) with
          | Atoms [Shape {calls=[s];_}] when s.quantified=[] && s.variadic=None && s.rest_pack=None -> s.params
          (* A generic callee's parameters at the instance the call's own
             expected type fixes, every actual left unconstrained: each
             binder must have received a bound from relating the callee's
             result to the expected type; where one received none (it occurs
             only in the parameters, or the expected type says nothing of
             it) and would take a default, none. *)
          | Atoms [Shape {calls=[s];_}] when s.variadic=None && s.rest_pack=None
                && List.length s.params = List.length args && expected <> None ->
            let from_expected = ref [] in
            (match Inference.infer ~expand:(expand_named declarations) ~receiver:(Atoms [Undef]) ?expected
                     ~expected_bounds:from_expected s (List.map (fun _ -> Atoms []) args) with
             | inferred ->
               let fixed (q:Semantic.quantifier) = List.mem q.identity !from_expected &&
                 (match List.assoc_opt q.identity inferred.substitution with
                  | Some (ValueArgument t) -> t <> Atoms [] | _ -> false) in
               if List.for_all fixed s.quantified then
                 let solution = inferred.substitution in
                 List.map (Inference.substitute solution) s.params
               else []
             | exception Json.Error _ -> [])
          | _ -> [] in
        List.find_map Fun.id (List.mapi (fun i a -> sink (List.nth_opt params i) a) args)
      | _ -> List.find_map (sink None) (Source.children e) in
    let at (s:stmt) = match s.statement with
      | Declare (_,bs) -> List.find_map (fun (_,written,e) -> sink written e) bs
      | Return e -> sink (expected_result ()) e
      | Effect e -> sink None e
      | _ -> if stmt_mentions n s then Some None else None in
    List.map at rest in
  let transfer_statement env s =
    (* A grown local's exact keys are claimed only where nothing else can
       reach its object: from the first statement that may let it escape on
       (but a `return` of it, after which the body runs nothing), it is its
       record, so no other reference, and no callee that may add a key to a
       writable dictionary, learns which keys it lacks. An annotated constant
       of the object itself learns only what its annotation states: the
       object is its record from the next statement on. *)
    let loosen env n =
      forget_exact_local n;
      List.map (fun (m,b) -> match b with
        | Value (Atoms atoms) when m = n -> m,Value (Atoms (List.map (function
            | Exact fields -> Shape {fields;indexes=[];calls=[];elements=None}
            | a -> a) atoms))
        | Value (Union ts) when m = n -> m,Value (Union (List.map (function
            | Atoms atoms -> Atoms (List.map (function
                | Exact fields -> Shape {fields;indexes=[];calls=[];elements=None}
                | a -> a) atoms)
            | t -> t) ts))
        | _ -> m,b) env in
    let aliased = List.filter (fun n -> match s.statement with
      | Declare (false,[(_,Some _,{node=Id m;_})]) -> m = n
      | _ -> false) (path_facts ()).Proposal_flow.exact_locals in
    let env = List.fold_left (fun env n ->
      let escaping = match s.statement with
        | Return {node=Id _;_} -> false
        | _ -> not (List.mem n aliased) && List.exists (escapes n) (Source.statement_children s) in
      if not escaping then env else loosen env n) env (path_facts ()).Proposal_flow.exact_locals in
    let result = match s.statement with
    | Declare (mutable_,[(n,written,init)]) ->
      (* A `let` the flow graph does not hold in a cell is a slot of the
         activation: every point claims what it holds there. *)
      let slot = mutable_ && not (held_in_cell n s.span) in
      if String.ends_with ~suffix:".[[class]]" n then mark_fresh_constructor ();
      (* An unannotated constant's fresh array is built at the array type its
         first use expects it at, where that use is one (TypeScript widens it
         at the declaration, and refuses the use when that differs). A
         proposal: Lean checks the elements against it and every use against
         the binding. *)
      let committed = match mutable_,written,init.node with
        | false,None,ArrayLiteral (_::_,_) ->
          (match first_use env n (following_statements s.span) with
           | Some t -> (match (try declared_head declarations [] t with Json.Error _ -> t) with
             | Atoms atoms when atoms <> [] && List.for_all (function
                 | Shape {elements=Some _;_} -> true | _ -> false) atoms -> Some t
             | _ -> None)
           | None -> None)
        | _ -> None in
      (* An evolving binding (TypeScript's evolving `any`): an unannotated
         `let` of `null` or `undefined` holds what is assigned to it, an
         unannotated `[]` the elements written into it. Its contract is the
         union of those, TypeScript's evolved type: a proposal, which Lean
         checks at every write. *)
      clear_evolving_binding n;
      let committed = match written,init.node with
        | None,ArrayLiteral ([],_) ->
          register_evolving_binding n init.pos true;
          Some (array {required=[];optional_elements=[];rest=Some (evolved init.pos);readonly=false;presence=Readable})
        | None,Literal (LNull | LUndefined) when mutable_ ->
          register_evolving_binding n init.pos false;
          (* The one type the binding's whole-value uses expect, where its
             written types never settle: a returned value, an annotated
             initializer, a call's argument. *)
          (match List.sort_uniq compare (List.filter_map Fun.id
                   (List.filter_map Fun.id (uses env n (following_statements s.span)))) with
           | [t] -> propose_use init.pos t
           | _ -> ());
          committed
        | _ -> committed in
      (* A constant's object literal to which a later statement of its
         block adds a key is claimed with its exact keys: the bound says
         which keys it lacks, so a key added on one path only is optional
         where the paths join. *)
      forget_exact_local n;
      (* A constant bound to a local holds that local's object. *)
      forget_holder n;
      (match mutable_,init.node with
       | false,Id m when List.mem_assoc m env -> record_holder n m
       | _ -> ());
      (match mutable_,written,init.node with
       | false,None,Alloc fs when grows_later n (List.map fst fs)
             (following_statements s.span) ->
         mark_exact_allocations [init.pos];
         mark_exact_local n
       (* A constant's object literal used whole where a type with an
          optional field it leaves out is expected is claimed with its exact
          keys, as a literal written there would be: the bound is what says
          it lacks the key. Not where it is also used as a writable
          dictionary. A proposal: Lean checks the bound at the allocation
          and every use against it. *)
       | false,None,Alloc fs ->
         let lacks_optional t = match object_hint declarations [] t with
           | Some {fields;indexes=[];_} -> List.exists (fun (f:Semantic.field) ->
               f.optional && not f.host && not (List.mem_assoc f.name fs)) fields
           | _ -> false in
         (* A holder of a writable dictionary some value meets may add
            keys, so no view learns from the bound which it lacks. *)
         let writable_dictionary t = match object_hint declarations [] t with
           | Some {indexes;_} -> List.exists (fun (i:Semantic.index_signature) ->
               match i.writable with Some (Atoms []) | None -> false | Some _ -> true) indexes
           | None -> false in
         let used = uses env n (following_statements s.span) in
         if List.exists (function Some (Some t) -> lacks_optional t | _ -> false) used
            && not (List.exists (function Some (Some t) -> writable_dictionary t | _ -> false) used) then
           mark_exact_allocations [init.pos]
       | _ -> ());
      let initial = expr ?expected:(if committed <> None then committed else written) env init in
      if not mutable_ then named_closure n written init;
      let binding = match mutable_,written with
        (* TypeScript's declared type for an unannotated `let`: its
           initializer's type, widened, or an evolving one's evolved type.
           Lean checks the initializer and every assignment against it. *)
        | true,None ->
          (match init.node with
           | Literal (LNull | LUndefined) -> cell (union (widen initial) (evolved init.pos))
           | _ -> cell (widen initial))
        (* An annotated `let` is its cell's first assignment: TypeScript
           narrows the declared type to what was assigned, and the cell
           holds the initializer's value, as after an assignment statement. *)
        | true,Some contract -> holding contract initial
        (* A class's annotation is its own construct signature, which the
           parser writes; the class value's claim may offer more. *)
        | false,Some _ when (match init.node with Ctor _ -> true | _ -> false) -> Value initial
        (* A closure offered further signatures holds them beside its
           annotation's: the binding is the closure, claimed at all of them,
           which Lean checks against the annotation. *)
        | false,Some _ when List.mem_assoc init.pos offered -> Value initial
        | false,Some contract -> Value (retain_call_effects
            (assigned_arms declarations (arms declarations contract) init) initial)
        (* An unannotated constant of a named union is held at its arms, as
           an annotated one is: a guard then keeps or drops each. *)
        | false,None -> Value (arms declarations initial) in
      (* A `let` the flow graph does not hold in a cell is a slot of the
         activation: it holds the initializer's value, a primitive at its
         type and any other at the contract's arms it may be of, under the
         same contract. *)
      let binding = match binding with
        | Storage (contract,_) when slot -> Local (contract,slot_holds declarations contract initial (Some init))
        | b -> b in
      (match binding with
       | Storage (contract,_) | Local (contract,_) ->
         let candidate = { pos = init.pos; name = n; type_ = contract } in
         publish_contract candidate
       | Value _ -> ());
      extend (after init env) n binding
    | Declare _ -> Json.fail "a declaration flow operation requires one binding"
    (* The initializer, then each binding in pattern order: a property at its
       field's read, an element at its position's, a rest at the tuple of the
       positions from its index on, claimed at its span; a default, which
       sees the earlier bindings, replaces the read's undefined slice. *)
    | Destructure _ -> Json.fail "destructuring requires its shared binding schedule"
    | Return e -> record_return (expr ?expected:(expected_result ()) env e); env
    (* An assignment statement leaves the cell holding the value written;
       `n ??= rhs`, the value it yields. *)
    (* `Object.assign(o, …)` on a local: the local holds the copies. *)
    | Effect ({node=ObjectAssign ({node=Id n;_},_);_} as e)
      when (match List.assoc_opt n env with Some (Value _) -> true | _ -> false) ->
      let t = expr env e in
      let env = after e env in
      record_growth n;
      List.map (fun (m,b) -> if m=n then m,Value t else m,b) env
    | Effect ({node=Write ({node=Id n;_},_,_) | IndexWrite ({node=Id n;_},_,_);_} as e)
      when (match List.assoc_opt n env with Some (Value _) -> true | _ -> false) ->
      let t = binding_type (lookup env n) in
      (* A key the write adds is added at the type the object's first later
         use whole expects for it, where that use states one: the field is
         writable, so its contract is what the use reads it at. A proposal:
         Lean checks the value against it. *)
      let added = match e.node with
        | Write (_,name,_) -> Some name
        | IndexWrite (_,{node=Literal (LString k);_},_) -> Some (Name k)
        | _ -> None in
      let hint = match added,first_use env n (following_statements s.span) with
        | Some name,Some use -> Option.bind (object_hint declarations [] use) (fun shape ->
            List.find_map (fun (f:Semantic.field) ->
              if f.name = name && not f.host then f.write else None) shape.fields)
        | _ -> None in
      let c = expr ?expected:hint env e in
      let claimed (x:expr) = latest_claim x.pos in
      (* A key of one of several singletons gives one copy per key: the
         object is one of them. *)
      let receiver,names = match e.node with
        | Write (r,name,_) -> r,[name]
        | IndexWrite (r,key,_) -> r,(match claimed key with
          | Some (Atoms [StrLit k]) -> [Name k]
          | Some t -> literal_keys declarations t
          | None -> [])
        | _ -> e,[] in
      let before = env in
      let env = after e env in
      if List.exists (adds before receiver t) names then begin
        record_growth n;
        let t' = combine (List.map (fun name -> grown declarations t name c) names) in
        (* Every constant holding the object holds the copy, and so does a
           `let` held in a slot, which the lowering rebinds; a `let`'s cell
           keeps its contract. *)
        let holders = holders_of n in
        List.map (fun (m,b) -> match b with
          | Value _ when List.mem m holders -> m,Value t'
          | Local (contract,_) when List.mem m holders -> m,Local (contract,t')
          | _ -> m,b) env
      end else env
    | Effect e -> ignore (expr env e);
      (* An assertion function's call leaves its actual at the promise's type. *)
      Refinement.promise_refine ~claimed:latest_claim
        (fun name -> try Some (resolve env name) with Json.Error _ -> None)
        declarations (after e env) e true
    | If _ | While _ | Block _ | ForOf _ | Try _ | Closing _ | Break _ | Continue ->
      Json.fail "a structured statement occurs as an atomic flow operation"
    | Throw e -> ignore (expr env e); after e env in
    List.fold_left loosen result aliased in
  transfer_statement

let statements (expr:Analysis_state.expression_infer) execute_bindings owner_span env ss =
  let transfer_statement = transfer expr in
  let after e env = effects env e in
  let flow_callbacks = {
    widen_slot=arms declarations;
    Proposal_flow.snapshot_metadata=path_facts;
    with_path_metadata;
    empty_output=Analysis_capabilities.empty_output;
    with_output;
    publish_output;
    statement=transfer_statement;
    execute_bindings;
    expression=(fun env e -> expr env e);
    expression_effects=after;
    branch;
    return_expression=(fun env e -> expr ?expected:(expected_result ()) env e);
    returned=record_return;
    entry;
    iterator_start=(fun (_node:Flow.node) (s:Source.stmt) env (b:Flow.binding) ->
      let span=s.span in
          let iterate,iterable=match s.statement with ForOf (_,_,i,e,_) -> i,e
            | _ -> Json.fail "an iterator flow operation names another statement" in
          (match iterable.node,s.statement with
           | Call ({node=Id "%ForIn%";_},_,_,_,_),ForOf (name,_,_,_,_) ->
             observe_for_in name
           | _ -> ());
          let actual=expr env iterable in
          if iterate="%Iterate%" then Option.iter (fun arm ->
            S.explain s.span ("a for...of loop over " ^ arm ^ ": " ^ iteration_reason))
            (non_array_arm declarations [] actual);
          let signature=match declared_head declarations [] (resolve env iterate) with
            | Atoms [Shape {calls=[s];_}] -> s
            | _ -> Proposal_diagnostics.unsupported ("a for...of loop needs the " ^ iterate ^ " intrinsic") in
          let result,substitution=if signature.quantified=[] then signature.result,[] else
            let inferred=Inference.infer ~receiver:(Atoms [Undef]) signature [actual] in
            inferred.result,inferred.substitution in
          publish_expression span result (if substitution=[] then None else
              Some (List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t) substitution));
          extend (forget env) b.Flow.name (Value result));
    iterator_step=(fun (_node:Flow.node) (s:Source.stmt) env (b:Flow.binding) (element:Flow.binding) ->
          let name,name_pos=match s.statement with ForOf (n,p,_,_,_) -> n,p
            | _ -> Json.fail "an iterator step names another statement" in
          let t=match declared_head declarations [] (binding_type (lookup env b.Flow.name)) with
            | Atoms [Shape {calls=[{params=[];result;_}];_}] ->
              let yielded=match result with Union ts -> ts | t -> [t] in
              let values=List.concat_map (fun t -> match declared_head declarations [] t with
                | Atoms atoms -> List.filter_map (function
                  | Shape {fields;_} -> List.find_map (fun (f:Semantic.field) ->
                    if f.name=Name "value" then Some f.read else None) fields
                  | _ -> None) atoms
                | _ -> []) yielded in
              (match values with [t] -> t | _ -> Proposal_diagnostics.unsupported "an iterator step yields no one value")
            | _ -> Proposal_diagnostics.unsupported "an iterator gives no step" in
          ignore name;
          publish_expression name_pos t None;
          extend (forget env) element.Flow.name (Value t),forget env);
  } in
  let statements = Proposal_flow.statements flow_callbacks flow_graph register_following in
  statements owner_span env ss

end
