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
  val grew : string -> bool
  val branch : (string * Environment.binding) list -> Source.expr -> bool ->
    (string * Environment.binding) list
end

module Make (S : Inputs) = struct
open S
  let branch = S.branch
  let claimed_type = S.claimed_type
  let execution (e:Source.expr) = match execution_at e.pos with
    | Some plan -> plan
    | None -> Json.fail ("missing expression execution plan at " ^ current_point () ^
        " for " ^ Json.encode e.pos)

  let join before left right =
    List.filter_map (fun (n,b) -> match b,List.assoc_opt n left,List.assoc_opt n right with
      | Storage (contract,_),Some (Storage (_,l)),Some (Storage (_,r)) -> Some (n,holding contract (union l r))
      | Local (contract,_),Some (Local (_,l)),Some (Local (_,r)) -> Some (n,Local (contract,union l r))
      (* A local an arm added a key to holds the object either arm left. *)
      | Value _,Some (Value l),Some (Value r) when grew n && l <> r ->
        Some (n,Value (union l r))
      | _ when is_field n -> None
      | _ -> Some (n,b)) before
    (* A field's contents are known after both arms where each knows them. *)
    @ List.filter_map (fun (n,b) -> match b,List.assoc_opt n right with
      | Value l,Some (Value r) when is_field n && List.mem_assoc (owner n) before ->
        Some (n,Value (union l r))
      | _ -> None) left

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

  let restore_optional original env =
    let env=List.remove_assoc "?." env in
    match List.assoc_opt "?." original with None -> env | Some binding -> env @ ["?.",binding]

  (* Two paths' states from `base`: as `join` leaves them, and where the
     paths are a condition's (`refine`), an immutable value holds what either
     path refined it to. *)
  let merge ~refine base left right =
    let joined = join (List.map (fun (n,b) -> n,Option.value (List.assoc_opt n base) ~default:b) left) left right in
    if not refine then joined else List.map (fun (n,b) -> match b,List.assoc_opt n left,List.assoc_opt n right with
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
      let optional=binding.Execution.name="?." in
      let original=env in
      let env=if optional then
        let t=Option.value (claimed_type (Execution.source evaluate)) ~default:top in
        List.remove_assoc "?." env @ ["?.",Value t] else env in
      let t,f,all=outcomes ~observe ~refine env next in
      let restore = if optional then Option.map (restore_optional original) else Fun.id in
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
  (* A call whose callee's every signature keeps the heap (its footprint
     within the empty one, its receiver's store included): Lean's
     `call-keep` keeps every heap fact across it, so the step keeps the
     fields and paths a test found. *)
  and keeps_heap source = match expression_hint source with
    | Some {node=(Call (callee,_,_,_,_) | Invoke (callee,_,_,_));_} ->
      (match claimed_type callee.pos with
       | Some t ->
         (match (try Some (declared_head declarations [] t) with Json.Error _ -> None) with
          | Some (Atoms [Shape {calls=(_ :: _ as calls);_}]) ->
            List.for_all (fun (s:Semantic.signature) ->
              footprint_le s.call_effect.footprint empty_footprint && not s.call_effect.receiver_store) calls
          | _ -> false)
       | None -> false)
    | _ -> false
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
      | Execution.Havoc -> forget ~keep:(Refinement.stable_path declarations env) env
      | Execution.CellWrite (name,value) ->
        (match List.assoc_opt name env,claimed_type value with
         | Some (Storage _),Some t -> assign env name t
         (* A slot holds the value at its declared arms, as a constant does:
            a guard then keeps or drops each. *)
         | Some (Local (contract,_)),Some t ->
           assign env name (slot_holds declarations contract t (expression_hint value))
         | Some (Storage _),None -> forget ~only:(( = ) name) env
         | Some (Local (contract,_)),None -> assign env name contract
         | _ -> env)
      | Execution.CellUpdate (name,source) ->
        (match List.assoc_opt name env,expression_hint source with
         | Some (Storage (contract,_)),Some {node=Update (op,_,rhs,_);_} ->
           let right=match rhs with None -> contract | Some rhs ->
             Option.value (claimed_type rhs.pos) ~default:contract in
           assign env name (operation_result declarations op contract right)
         | Some (Local (contract,current)),Some {node=Update (op,_,rhs,_);_} ->
           let right=match rhs with None -> contract | Some rhs ->
             Option.value (claimed_type rhs.pos) ~default:contract in
           assign env name (operation_result declarations op current right)
         | Some (Storage _),_ -> forget ~only:(( = ) name) env
         | Some (Local (contract,_)),_ -> assign env name contract
         | _ -> env)

  let effects env (e:expr) = run_execution env (execution e)
  (* What a condition leaves where it holds and where it fails, each path
     refined in evaluation order; where no path reaches an answer, its
     syntactic refinement. *)
  let condition env (e:expr) =
    let t,f,all=outcomes ~refine:true env (execution e) in
    let after=Option.value all ~default:env in
    (match t with Some t -> t | None -> branch after e true),
    (match f with Some f -> f | None -> branch after e false)

  let expression_entry root source fallback =
    let (_,plan,initial)=root in
    let entries=Hashtbl.create 16 in
    let observe span env=match Hashtbl.find_opt entries span with
      | None -> Hashtbl.add entries span env
      | Some previous ->
        let impossible env=List.exists (fun (n,b) -> not (is_field n) && binding_type b=Atoms []) env in
        let env=if impossible previous then env else if impossible env then previous else
          join previous previous env in
        Hashtbl.replace entries span env in
    ignore (run_execution ~observe initial plan);
    Option.value (Hashtbl.find_opt entries source) ~default:fallback

end
