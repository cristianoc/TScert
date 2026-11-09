open Semantic
open Environment
open Source
open Type_queries
(* The interpreter reads point-specific proposals and refines branch states.
   Its inputs expose no pass-state record, mutable reference or table. *)
module type Inputs = sig
  val declarations : Source.declaration list
  val current_point : unit -> string
  val execution_at : Json.t -> Execution.plan option
  val expression_hint : Json.t -> Source.expr option
  val claimed_type : Json.t -> Semantic.ty option
  (* The instance a call published of its callee read at a source. *)
  val latest_instance : Json.t -> Semantic.ty option
  val grew : string -> bool
  val cache_entries : bool
  val rigid_bounds : unit -> (Semantic.rigid * Semantic.ty) list
  val branch : claimed:(Json.t -> Semantic.ty option) -> (string * Environment.binding) list -> Source.expr -> bool ->
    (string * Environment.binding) list
end

module Make (S : Inputs) = struct
open S
  (* A replay records the queries it actually reads, including refinement's
     claims. Later typings may publish a claim or a call instance. *)
  let dependencies = ref None
  let track ?(equal = ( = )) read key =
    let value = read key in
    (match !dependencies with
     | None -> ()
     | Some checks -> checks := (fun () -> let current = read key in current == value || equal current value) :: !checks);
    value
  let same_type a b = match a,b with
    | Some a,Some b -> a == b || a = b
    | None,None -> true | _ -> false
  let claimed_type source = track ~equal:same_type S.claimed_type source
  let latest_instance source = track ~equal:same_type S.latest_instance source
  let grew name = track S.grew name
  let branch env cond truth = S.branch ~claimed:claimed_type env cond truth
  let execution (e:Source.expr) = match execution_at e.pos with
    | Some plan -> plan
    | None -> Json.fail ("missing expression execution plan at " ^ current_point () ^
        " for " ^ Json.encode e.pos)

  (* An environment's lookup, answering for each name what `List.assoc_opt`
     answers, the first binding of the name, in time independent of the
     environment's length: a join looks up every binding of one state in the
     others. *)
  let index env =
    let table = Hashtbl.create (2 * List.length env + 1) in
    List.iter (fun (n,b) -> if not (Hashtbl.mem table n) then Hashtbl.add table n b) env;
    Hashtbl.find_opt table

  let join_indexed before left in_left in_right =
    List.filter_map (fun (n,b) -> match b,in_left n,in_right n with
      | Storage (contract,_),Some (Storage (_,l)),Some (Storage (_,r)) -> Some (n,holding contract (union l r))
      | Local (contract,_),Some (Local (_,l)),Some (Local (_,r)) -> Some (n,Local (contract,union l r))
      (* A local an arm added a key to holds the object either arm left. *)
      | Value _,Some (Value l),Some (Value r) when grew n && l <> r ->
        Some (n,Value (union l r))
      | _ when is_field n -> None
      | _ -> Some (n,b)) before
    (* A field's contents are known after both arms where each knows them. *)
    @ List.filter_map (fun (n,b) -> match b,in_right n with
      | Value l,Some (Value r) when is_field n && List.mem_assoc (owner n) before ->
        Some (n,Value (union l r))
      | _ -> None) left
  let join before left right = join_indexed before left (index left) (index right)

  let refine_test env condition test truth =
    match expression_hint condition with
    | None -> env
    | Some cond -> (match test with
      | Execution.Truthy -> branch env cond truth
      | Execution.Nullish | Execution.Defined ->
        let refine t = match test,truth with
          | Execution.Nullish,true -> union (restrict Nul true t) (restrict Undef true t)
          | Execution.Nullish,false -> restrict Undef false (restrict Nul false t)
          | Execution.Defined,true -> restrict Undef false t
          | Execution.Defined,false -> restrict Undef true t
          | Execution.Truthy,_ -> t in
        (match cond.node with Id name -> refine_value env name refine | _ -> env))

  (* The hidden names a plan binds: an optional chain's saved receiver and
     an optional method call's saved object. *)
  let hidden name = name = "?." || name = "?.object"
  let restore_optional ?(name = "?.") original env =
    let env=List.remove_assoc name env in
    match List.assoc_opt name original with None -> env | Some binding -> env @ [name,binding]

  (* Two paths' states from `base`: as `join` leaves them, and where the
     paths are a condition's (`refine`), an immutable value holds what either
     path refined it to. *)
  let merge ~refine base left right =
    let in_base = index base and in_left = index left and in_right = index right in
    let joined = join_indexed (List.map (fun (n,b) -> n,Option.value (in_base n) ~default:b) left) left in_left in_right in
    if not refine then joined else List.map (fun (n,b) -> match b,in_left n,in_right n with
      | Value _,Some (Value l),Some (Value r) when not (is_field n) -> n,Value (if l = r then l else union l r)
      | _ -> n,b) joined
  let either ~refine base a b = match a,b with
    | Some l,Some r -> Some (merge ~refine base l r) | Some l,None -> Some l | None,r -> r
  (* The state a plan leaves, its paths joined. *)
  let rec run_execution ?(observe = fun _ _ -> ()) env plan =
    let _,_,all=outcomes ~observe ~refine:false env plan in
    Option.value all ~default:env
  (* What a plan leaves where its value is truthy, where it is falsy, and on
     every path (`run_execution`): each path refined by a test where the
     test runs, every later step acting on what it found, so a call past a
     test forgets the fields the test knew. None where no path gets there. A
     plan whose value is read for its effects alone (`refine` false)
     refines only by the tests it dispatches on. *)
  and outcomes ?(observe = fun _ _ -> ()) ~refine env = function
    | Execution.Observe (source,evaluate) -> observe source env; outcomes ~observe ~refine env evaluate
    | Execution.Atom (source,operation) ->
      let env=step env operation in
      (match operation.Execution.result,refine,expression_hint source with
       | Execution.Boolean true,_,_ -> Some env,None,Some env
       | Execution.Boolean false,_,_ -> None,Some env,Some env
       | _,true,Some e -> Some (branch env e true),Some (branch env e false),Some env
       | _ -> Some env,Some env,Some env)
    | Execution.Sequence (_,binding,evaluate,Execution.Atom (_,operation))
      when (match operation.Execution.result with
        | Execution.Saved (name,_) -> name = binding.Execution.name
        | _ -> false) ->
      let t,f,all=outcomes ~observe ~refine env evaluate in
      let apply=Option.map (fun env -> step env operation) in
      let t,f=match operation.Execution.result with
        | Execution.Saved (_,true) -> f,t | _ -> t,f in
      apply t,apply f,apply all
    | Execution.Sequence (_,binding,evaluate,next) ->
      let env=run_execution ~observe env evaluate in
      let name=binding.Execution.name in
      let optional=hidden name in
      let original=env in
      let env=if optional then
        let t=Option.value (claimed_type (Execution.source evaluate)) ~default:top in
        List.remove_assoc name env @ [name,Value t] else env in
      let t,f,all=outcomes ~observe ~refine env next in
      let restore = if optional then Option.map (restore_optional ~name original) else Fun.id in
      restore t,restore f,restore all
    | Execution.Choose (_source,condition,test,binding,evaluate,yes,no) ->
      let optional=binding.Execution.name="?." in
      let truthy,falsy,after=match test with
        | Execution.Truthy -> outcomes ~observe ~refine:true env evaluate
        | Execution.Nullish | Execution.Defined ->
          let after=run_execution ~observe env evaluate in
          Some (refine_test after condition test true),Some (refine_test after condition test false),Some after in
      let original=Option.value after ~default:env in
      let with_optional env = if optional then
          let t=Option.value (claimed_type (Execution.source evaluate)) ~default:top in
          List.remove_assoc "?." env @ ["?.",Value t] else env in
      let base=with_optional original in
      let path truth state = Option.map (fun env ->
        let env=with_optional env in
        if optional then refine_value env "?." (fun t ->
          if truth then union (restrict Nul true t) (restrict Undef true t)
          else without_nullish t) else env) state in
      (* An arm keeping the tested value (`a && b` where `a` is falsy) has
         that value's answer. *)
      let arm truth state plan = match state,plan with
        | None,_ -> None,None,None
        | Some env,Execution.Atom (_,operation) when
            operation.Execution.result = Execution.Saved (binding.Execution.name,false)
            && test = Execution.Truthy ->
          if truth then Some env,None,Some env else None,Some env,Some env
        | Some env,_ -> outcomes ~observe ~refine env plan in
      let yt,yf,yall=arm true (path true truthy) yes
      and nt,nf,nall=arm false (path false falsy) no in
      let restore = Option.map (fun env -> if optional then restore_optional original env else env) in
      restore (either ~refine base yt nt),restore (either ~refine base yf nf),
      restore (either ~refine:false base yall nall)
  (* A call or a construction whose callee's every signature keeps the
     heap (its footprint within the empty one, its receiver's store
     included): Lean's `call-keep` keeps every heap fact across it, so the
     step keeps the cells, fields and paths a test found. The signatures are
     those the call's instance projects from its callee's overloads, as a
     closure's footprint reads them, else all of the callee's type's: its
     call signatures for a call, its construct signatures for a
     construction. *)
  and keeps_heap source =
    let keeps calls = List.for_all (fun (s:Semantic.signature) ->
      footprint_le (Semantic.coarse_footprint s.call_effect) empty_footprint && not s.call_effect.receiver_store &&
      not s.call_effect.receiver_own) calls in
    let callee_head (callee:expr) =
      match (match latest_instance callee.pos with Some t -> Some t | None -> claimed_type callee.pos) with
      | Some t -> (try Some (declared_head declarations [] t) with Json.Error _ -> None)
      | None -> None in
    match expression_hint source with
    | Some {node=(Call (callee,_,_,_,_) | Invoke (callee,_,_,_));_} ->
      (match callee_head callee with
       | Some (Atoms [Shape {calls=(_ :: _ as calls);_}]) -> keeps calls
       | _ -> false)
    | Some {node=New (callee,_,_,_);_} ->
      (match callee_head callee with
       | Some (Atoms [Ctors ((_ :: _ as constructs),_)]) -> keeps constructs
       | _ -> false)
    | _ -> false
  (* A write of a cell's contents may be a write of any location the unit
     does not know apart from it, another cell's or a field's: Lean's
     `writeOutput` keeps an observation only of a location known apart, and
     the read links through stable members. A cell the unit declares is
     apart from every older location; after a write of any other cell, the
     other cells are known by their contracts, as after a step that may
     write cells. *)
  and cell_written env name =
    if List.mem name !unit_cells then env
    else if List.mem_assoc name !module_cells then
      (* Two module cells are two locations (Lean's entry separation of a
         unit's module cells), so another module cell keeps its contents. *)
      List.filter_map (fun (n,b) -> match b with
        | _ when is_field n -> if Refinement.stable_path declarations env n then Some (n,b) else None
        | Storage (contract,_) when n = name || not (List.mem_assoc n !module_cells) -> Some (n,cell contract)
        | _ -> Some (n,b)) env
    else forget ~keep:(Refinement.stable_path declarations env) env
  (* A write of field [f] of an immutable binding's object keeps what is
     known of the object's other fields where every arm states [f] an
     invariant field (Lean's `write-sibling`); any other write may write any
     location. *)
  and field_written env written =
    let stable = Refinement.stable_path declarations env in
    match written with
    | Some (n,f) ->
      (match List.assoc_opt n env with
       | Some (Value t) when Refinement.owned_field declarations t f ->
         forget ~keep:(fun k -> stable k ||
           (is_field k && not (is_path k) && owner k = n && field_of k <> f)) env
       | _ -> forget ~keep:stable env)
    | None -> forget ~keep:stable env
  (* The binding and field a write expression, or a written reference, names. *)
  and written_field ~target source = match expression_hint source with
    | Some {node=Write ({node=Id n;_},Name f,_);_} when not target -> Some (n,f)
    | Some {node=Read ({node=Id n;_},Name f);_} when target -> Some (n,f)
    | _ -> None
  and step env operation = match operation.Execution.impact with
      (* A completed member read narrows its receiver: reading a member of
         `null` or `undefined` throws, so past it the constant or owned local
         it names holds an object or primitive (Lean's `readNarrowing`). *)
      | Execution.None_ -> (match expression_hint operation.Execution.source with
        | Some {node=Read ({node=Id n;_},_);_} ->
          (match List.assoc_opt n env with
           | Some (Value _ | Local _) -> refine_value env n without_nullish
           | _ -> env)
        | _ -> env)
      (* A step that may write cells keeps the path entries through stable
         members, as Lean keeps their read links. *)
      | Execution.Havoc when keeps_heap operation.Execution.source -> env
      | Execution.Havoc -> field_written env (written_field ~target:false operation.Execution.source)
      | Execution.FieldWrite target -> field_written env (written_field ~target:true target)
      | Execution.CellWrite (name,value) ->
        (match List.assoc_opt name env,claimed_type value with
         | Some (Storage _),Some t -> assign (cell_written env name) name t
         (* A slot holds the value at its declared arms, as a constant does:
            a guard then keeps or drops each. *)
         | Some (Local (contract,_)),Some t ->
           assign env name (slot_holds declarations contract t (expression_hint value))
         | Some (Storage _),None -> forget ~only:(( = ) name) (cell_written env name)
         | Some (Local (contract,_)),None -> assign env name contract
         | _ -> env)
      | Execution.CellUpdate (name,source) ->
        (match List.assoc_opt name env,expression_hint source with
         | Some (Storage (contract,_)),Some {node=Update (op,_,rhs,_);_} ->
           let right=match rhs with None -> contract | Some rhs ->
             Option.value (claimed_type rhs.pos) ~default:contract in
           assign (cell_written env name) name (operation_result declarations op contract right)
         | Some (Local (contract,current)),Some {node=Update (op,_,rhs,_);_} ->
           let right=match rhs with None -> contract | Some rhs ->
             Option.value (claimed_type rhs.pos) ~default:contract in
           assign env name (operation_result declarations op current right)
         | Some (Storage _),_ -> forget ~only:(( = ) name) (cell_written env name)
         | Some (Local (contract,_)),_ -> assign env name contract
         | _ -> env)

  let effects env (e:expr) = run_execution env (execution e)
  (* What a condition leaves where it holds and where it fails, each path
     refined in evaluation order; an answer no path reaches is `unreachable`. *)
  let condition env (e:expr) =
    let t,f,all=outcomes ~refine:true env (execution e) in
    let after=Option.value all ~default:env in
    (match t with Some t -> t | None -> unreachable after),
    (match f with Some f -> f | None -> unreachable after)

  module Roots = Hashtbl.Make(struct
    type t = Analysis_capabilities.root
    let equal a b = a == b
    let hash = Hashtbl.hash
  end)
  (* Each observation retains the dependency-list prefix that produced its
     environment. Claims read later in the statement cannot invalidate that
     entry. A repeated observation joins its environments, an immutable
     value at what either path refined it to (`merge`), and retains all
     dependencies read up to that join. The root owns the plan and initial
     environment; a pass owns the cache and its immutable source hints. *)
  let entry_cache = Roots.create 16

  let expression_entry root source fallback =
    let (_,plan,initial)=root in
    let bounds = rigid_bounds () in
    let cached = if cache_entries then Roots.find_opt entry_cache root else None in
    let valid (entries,previous,checks) =
      previous = bounds &&
      let checks = match Hashtbl.find_opt entries source with
        | Some (_,checks) -> checks | None -> checks in
      List.for_all (fun check -> check ()) checks in
    let entries = match cached with
    | Some cached when valid cached -> let entries,_,_ = cached in entries
    | _ ->
      let entries=Hashtbl.create 16 in
      let checks = ref [] in
      let observe span env =
        let env = match Hashtbl.find_opt entries span with
          | None -> env
          | Some (previous,_) ->
            let impossible env=List.exists (fun (n,b) -> not (is_field n) && binding_type b=Atoms []) env in
            if impossible previous then env else if impossible env then previous else
              merge ~refine:true previous previous env in
        Hashtbl.replace entries span (env,!checks) in
      let saved = !dependencies in
      dependencies := Some checks;
      Fun.protect ~finally:(fun () -> dependencies := saved)
        (fun () -> ignore (run_execution ~observe initial plan));
      if cache_entries then Roots.replace entry_cache root (entries,bounds,!checks);
      entries in
    match Hashtbl.find_opt entries source with
    | Some (env,_) -> env | None -> fallback

end
