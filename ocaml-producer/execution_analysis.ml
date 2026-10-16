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

  let rec run_execution ?(observe = fun _ _ -> ()) env = function
    | Execution.Observe (source,evaluate) -> observe source env; run_execution ~observe env evaluate
    | Execution.Atom (_,operation) -> (match operation.Execution.impact with
      | Execution.None_ -> env
      | Execution.Havoc -> forget env
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
         | _ -> env))
    | Execution.Sequence (_,binding,evaluate,next) ->
      let env=run_execution ~observe env evaluate in
      let optional=binding.Execution.name="?." in
      let original=env in
      let env=if optional then
        let t=Option.value (claimed_type (Execution.source evaluate)) ~default:top in
        List.remove_assoc "?." env @ ["?.",Value t] else env in
      let env=run_execution ~observe env next in
      if optional then restore_optional original env else env
    | Execution.Choose (_,condition,test,binding,evaluate,yes,no) ->
      let env=run_execution ~observe env evaluate in
      let original=env in
      let optional=binding.Execution.name="?." in
      let env=if optional then
        let t=Option.value (claimed_type (Execution.source evaluate)) ~default:top in
        List.remove_assoc "?." env @ ["?.",Value t] else env in
      let path truth =
        let env=refine_test env condition test truth in
        if optional then refine_value env "?." (fun t ->
          if truth then union (restrict Nul true t) (restrict Undef true t)
          else without_nullish t) else env in
      let left=run_execution ~observe (path true) yes
      and right=run_execution ~observe (path false) no in
      let result=join env left right in
      if optional then restore_optional original result else result

  let effects env (e:expr) = run_execution env (execution e)

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
