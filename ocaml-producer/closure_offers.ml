open Semantic
open Source
open Type_queries
module type Inputs = sig
  include Analysis_capabilities.Queries
  include Analysis_capabilities.Path_queries
  include Analysis_capabilities.Closure_registry
end
module Make (S : Inputs) = struct
open S
  let rec allocated (body:expr) = match body.node with
    | Alloc fs -> Some fs
    | BlockBody ss -> allocated_in ss
    | _ -> None
  and allocated_in ss = match List.rev ss with
    | {statement=Return e;_} :: _ -> allocated e
    | {statement=If (_,a,_);_} :: _ -> allocated_in a
    | _ -> None

  let rec tails (body:expr) = match body.node with
    | Alloc _ | Build _ -> [body.pos]
    | BlockBody ss -> tails_in ss
    | _ -> []
  and tails_in ss = match List.rev ss with
    | {statement=Return e;_} :: _ -> tails e
    | {statement=If (_,a,b);_} :: _ -> tails_in a @ tails_in b
    | _ -> []

  let named_closure n written (init:expr) = match written,init.node with
    | (None | Some (Atoms [Shape {calls=[_];fields=[];indexes=[];elements=None}])),Lambda (_,[],ps,_,false,_,_) ->
      register_closure n init.pos (List.map snd ps)
    | None,Alloc fs -> register_object n fs
    | Some _,Ctor ({node=Lambda (None,[],ps,[],false,Some instance,body);_},_) when allocated body <> None ->
      let fs = Option.get (allocated body) in
      (* An instance's methods are its prototype chain's, the nearer first. *)
      let rec chain seen fs = match List.assoc_opt (Name proto_key) fs with
        | Some {node=Id p;_} when not (List.mem p seen) ->
          let own = Option.value (List.assoc_opt p (path_facts ()).Proposal_flow.objects) ~default:[] in
          List.filter (fun (k,_) -> k <> Name proto_key) own
          @ List.filter (fun (k,_) -> not (List.mem_assoc k own)) (chain (p::seen) own)
        | _ -> [] in
      let fs = if List.mem_assoc (Name proto_key) fs then chain [] fs else fs in
      let methods = List.filter_map (fun (key,(e:expr)) -> match e.node with
        | Id m when List.mem_assoc m (path_facts ()).Proposal_flow.closures -> Some (key,m)
        | _ -> None) fs in
      register_class n (init.pos,List.map snd ps,instance,methods)
    | _ -> ()

  let closure_offer n (offered:Semantic.signature) =
    let pos,own = List.assoc n (path_facts ()).Proposal_flow.closures in
    let arity = List.length own in
    if offered.quantified=[] && offered.rest_pack=None
       && (match offered.variadic with
           | None -> List.length offered.params > arity
           | Some _ -> List.length offered.params >= arity)
       && List.for_all2 plausible_subtype
            (List.filteri (fun i _ -> i < arity) offered.params) own
    then Some (fun () -> publish_request pos offered) else None

  let offer_class (pos,params,instance,methods) expected =
    match declared_head declarations [] expected with
    | Atoms [Ctors (signatures,_)] ->
      List.iter (fun (s:Semantic.signature) ->
        let member key = match (try Some (declared_head declarations []
            (S.field_type declarations [] s.result key)) with Json.Error _ -> None) with
          | Some (Atoms [Shape {calls=[m];fields=[];indexes=[];elements=None}]) -> Some m
          | _ -> None in
        let widened = List.filter (fun (key,m) -> match member key with
          | Some offered -> (match closure_offer m {offered with receiver=instance} with
            | Some state -> state (); true
            | None -> false)
          | None -> false) methods in
        let arity = List.length params in
        let longer = s.variadic=None && s.rest_pack=None && List.length s.params > arity
          && List.for_all2 plausible_subtype (List.filteri (fun i _ -> i < arity) s.params) params in
        (* A variadic signature with an element rest: Lean checks the code
           at its fixed parameters, then each further position it binds at
           the element or `undefined`. *)
        let variadic = s.variadic=None && (match s.rest_pack with
            | Some (Pack {required=[];optional_elements=[];rest=Some _;_}) -> true | _ -> false)
          && List.length s.params <= arity
          && List.for_all2 plausible_subtype s.params (List.filteri (fun i _ -> i < List.length s.params) params) in
        if variadic then publish_request pos s
        else if widened <> [] || longer then
          publish_request pos {call_effect=s.call_effect;quantified=[];receiver=top;params=if longer then s.params else params;
                            variadic=None;rest_pack=None;result=s.result})
        (List.filter (fun (s:Semantic.signature) -> s.quantified=[]) signatures)
    | _ -> ()

end
