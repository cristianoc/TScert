open Semantic
open Environment
open Source
open Inference
open Type_queries
module type Inputs = sig
  include Expression_support.Inputs
  include Analysis_capabilities.Path_queries
  include Analysis_capabilities.Instance_publication
  include Analysis_capabilities.Claim_operations
  include Analysis_capabilities.Closure_scope
  val tails : Source.expr -> Json.t list
end
module Make (S : Inputs) = struct
open S
module Support = Expression_support.Make(S)
let infer (expr:Analysis_state.expression_infer) execute_bindings (infer_body:Analysis_state.body_infer) ?expected env (e:Source.expr) =
  (* A class value's static fields, each the binding its initializer bound,
     at the contract the class's annotation states for it. *)
  let static_fields expected env statics =
    let declared = match expected with
      | Some t -> (match declared_head declarations [] t with
        | Atoms [Ctors (_,fs)] -> fs
        | _ -> [])
      | None -> [] in
    List.map (fun (name,(value:Source.expr)) ->
      match List.find_opt (fun (f:Semantic.field) -> f.name = name) declared with
      | Some f -> ignore (expr ~expected:f.read env value); f
      | None ->
        (* A static method's binding may carry an effect its annotation
           does not state; the field holds it at its annotation. *)
        let t = match expr env value with
          | Atoms [Shape ({calls;_} as s)] ->
            Atoms [Shape {s with calls=List.map (fun (c:Semantic.signature) -> {c with call_effect=Unrestricted}) calls}]
          | t -> t in
        {name;optional=false;read=t;write=Some t;host=false;receivers=[]}) statics in
  match e.node with
    | Ctor ({node=Lambda (None,[],ps,[],false,Some result,body);_},statics) ->
      (* The constructor's body under its parameters; `new` passes it no
         receiver it reads, and runs it later, when a cell it captures holds
         what its contract admits. The class value's type is its construct
         signature. *)
      let inner = List.fold_left (fun env (n,t) -> extend env n (Value t)) (forget env) ps in
      let fresh = prepare_constructor (tails body) in
      let allocated_type = match body.node with
        | BlockBody ss ->
          let _,returned = infer_body body.pos (Some result) inner ss in
          combine (List.rev returned)
        | _ -> expr ~expected:result inner body in
      (* A class offered construct signatures giving other instances is
         claimed at them too, beside its own; Lean checks the body at each. *)
      let own = {call_effect=Unrestricted;quantified=[];receiver=Semantic.top;params=List.map snd ps;variadic=None;rest_pack=None;result} in
      let extra = Option.value (List.assoc_opt e.pos offered) ~default:[] in
      (* A fresh constructor gives, first, the instance it allocates. *)
      let fresh_sig = if fresh then [{own with result=allocated_type}] else [] in
      Atoms [Ctors (fresh_sig @ own :: List.filter (fun s -> s <> own) (List.sort_uniq compare extra),
        static_fields expected env statics)]
    (* A class value whose code is that of the class value named, bound
       before its static initializers, which construct the class through it:
       that one's construct signatures, with the class's static fields. *)
    | Ctor ({node=Id h;_},statics) ->
      (match declared_head declarations [] (binding_type (lookup env h)) with
       | Atoms [Ctors (signatures,[])] ->
         (* The signatures it is offered, as a constructor's own are. *)
         let extra = Option.value (List.assoc_opt e.pos offered) ~default:[] in
         Atoms [Ctors (signatures @ List.filter (fun s -> not (List.mem s signatures)) (List.sort_uniq compare extra),
           static_fields expected env statics)]
       | _ -> Proposal_diagnostics.unsupported ("a class value's code names no class value: " ^ h))
    | Ctor _ -> Proposal_diagnostics.unsupported "a class value is a constructor lambda with plain parameters"
    | New (callee,types,args,spreads) ->
      let constructor = declared_head declarations [] (expr env callee) in
      (* A spread of an array of no fixed length goes to a variadic construct
         signature taking at most the actuals before it as fixed parameters:
         `new` reads the array's elements as a call's spread into a rest. *)
      let first_spread = List.fold_left min (List.length args) spreads in
      let variadic = match constructor with
        | Atoms [Ctors (signatures,_)] when List.exists (fun i ->
            Semantic.tuple_positions ~readonly:true
              (declared_head declarations [] (expr env (List.nth args i))) = None) spreads
            || (spreads = [] && not (List.exists (fun (s:Semantic.signature) -> s.rest_pack = None
              && List.length s.params >= List.length args) signatures)) ->
          List.find_opt (fun (s:Semantic.signature) -> s.quantified = [] && s.rest_pack <> None
            && List.length s.params <= first_spread) signatures
        | _ -> None in
      (match variadic with
      | Some s ->
        List.iteri (fun i a ->
          if i < List.length s.params then ignore (expr ~expected:(List.nth s.params i) env a)
          else ignore (expr env a)) args;
        s.result
      | None ->
      (* A spread's tuple annotation supplies its element contracts. Ordinary
         calls retain contextual inference for their written arguments. Lean
         checks every expanded actual against the chosen signature. *)
      let expanded = if spreads = [] then None else
        Some (List.concat (List.mapi (fun i arg ->
          let t = expr env arg in
          if List.mem i spreads then
            match Semantic.tuple_positions ~readonly:true (declared_head declarations [] t) with
            | Some ps -> ps
            | None -> Proposal_diagnostics.unsupported "a constructor spread needs a tuple of required positions"
          else [t]) args)) in
      let count = match expanded with Some ts -> List.length ts | None -> List.length args in
      let actual_types () = match expanded with Some ts -> ts | None -> List.map (expr env) args in
      let contextual_actuals ps = match expanded with
        | Some _ -> ()
        | None -> List.iter2 (fun p a -> ignore (expr ~expected:p env a)) ps args in
      (* `new` may omit trailing actuals, as a call may: the machine binds
         `undefined` there, and Lean checks each omitted position admits it. *)
      let written (s:Semantic.signature) = List.filteri (fun i _ -> i < count) s.params in
      (match constructor with
       | Atoms [Ctors ([signature],_)] when signature.quantified <> [] ->
         (* A generic class: its instance is the one the explicit type
            arguments name, or is inferred from the actuals, as a generic
            call's is. *)
         if count > List.length signature.params then
           Proposal_diagnostics.unsupported "no construct signature takes this many arguments";
         let substitution,result =
           if types <> [] then begin
             if List.length types <> List.length signature.quantified then
               Proposal_diagnostics.unsupported "explicit type arguments must name every class type parameter";
             let substitution = List.map2 (fun (q:Semantic.quantifier) t -> q.identity,ValueArgument t)
               signature.quantified types in
             let instance = Inference.substitute_signature substitution {signature with quantified=[]} in
             contextual_actuals (written instance);
             substitution,instance.result
           end else
             let missing = List.length signature.params - count in
             let inferred = Inference.infer ~expand:(expand_named declarations) ~receiver:Semantic.top ?expected signature
               (actual_types () @ List.init missing (fun _ -> Atoms [Undef])) in
             inferred.substitution,inferred.result in
         instance_of callee substitution;
         publish_substitution e.pos (List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t) substitution);
         result
       | Atoms [Ctors (signatures,_)] ->
         if types <> [] then Proposal_diagnostics.unsupported "explicit type arguments to a class that takes none";
         let exact,short = List.partition (fun (s:Semantic.signature) ->
           List.length s.params = count) (List.filter (fun (s:Semantic.signature) ->
             s.quantified = [] && List.length s.params >= count) signatures) in
         (match exact @ short with
          | s :: _ ->
            contextual_actuals (written s);
            s.result
          | [] -> Proposal_diagnostics.unsupported "no construct signature takes this many arguments")
       | _ -> Proposal_diagnostics.unsupported "`new` needs a value with construct signatures"))
    | Lambda (receiver,quantified,ps,defaults,rest,written,body) ->
      (* An ordinary function binds its own `this`, replacing an enclosing
         one; an arrow keeps the enclosing binding, as a capture. *)
      (* The body runs later, when any cell it captures holds whatever its
         contract admits. *)
      let env = forget env in
      let env = match receiver with
        | Some t -> List.remove_assoc "this" env @ ["this",Value t]
        | None -> env in
      let receiver = Option.value receiver ~default:Semantic.top in
      (* Executing defaults see only earlier bindings. A literal closure may
         capture later parameters; this is a proposal about its eventual body,
         not permission to invoke it during initialization. Lean independently
         schedules acyclic captures and rejects pending closure exposure. *)
      let inner = List.fold_left (fun env (i,(n,t)) ->
        let assigned = match body.node with
          | BlockBody ss -> List.exists (assigns n) ss
          | _ -> false in
        let input=if List.mem_assoc i defaults then union t (Atoms [Undef]) else t in
        extend env n (if assigned then holding t input else Value input)) env (List.mapi (fun i p -> i,p) ps) in
      (* A closure literal without a result annotation expected at one
         signature taking at least its parameters has that signature's result
         as its contextual return type, as in TypeScript. *)
      let contextual = match written,expected with
        | None,Some t when quantified = [] ->
          (match (try declared_head declarations [] t with Json.Error _ -> t) with
           | Atoms [Shape {calls=[s];fields=[];indexes=[];elements=None}]
             when s.quantified=[] && s.rest_pack=None && s.variadic=None
                  && List.length s.params >= List.length ps -> Some s.result
           | _ -> None)
        | _ -> None in
      (* A generic closure's own value bounds hold in its body, as a generic
         function's do: a member read through a bounded binder reads the
         bound's member. *)
      let closure_bounds = List.filter_map (fun (q:Semantic.quantifier) -> match q.bound with
        | Some (ValueArgument b) when b <> Rigid q.identity -> Some (q.identity,b)
        | _ -> None) quantified @ rigid_bounds () in
      let infer_closure_body ?expected env = match body.node with
        | BlockBody _ -> expr ?expected env body
        | _ ->
          let point,prologue=match closure_entry body.pos with
            | Some entry -> entry | None -> Json.fail "Lean supplied no graph for a closure expression body" in
          with_current_point point (fun () ->
            let env=match prologue with None -> env | Some plan -> execute_bindings env plan in
            entry env body.pos;
            expr ?expected env body) in
      let body_type = with_rigid_bounds closure_bounds (fun () ->
        infer_closure_body ?expected:(if written <> None then written else contextual) inner) in
      (* Without a result annotation the result is the body's, widened as
         TypeScript widens an inferred return type, or the contextual return
         type where the body's fits it: a literal result the context asks for
         (`() => "hello"` at `() => "hello"`) is kept, and an async body's
         promise is the one the context names. It is a claim: Lean checks the
         body against it. *)
      let rec fits a b = plausible_subtype a b || match a,b with
        | Atoms [Named (i,xs)],Atoms [Named (j,ys)] ->
          i=j && List.length xs = List.length ys && List.for_all2 fits xs ys
        | _ -> false in
      let result = match written,contextual with
        | Some result,_ -> result
        | None,Some r when fits body_type r -> r
        | None,_ -> widen body_type in
      let params = List.mapi (fun i (_,t) ->
        if List.mem_assoc i defaults then union t (Atoms [Undef]) else t) ps in
      (* A tuple rest is one binding and several positions: the signature
         carries the elements, the body reads the tuple. An array rest is one
         binding and any number of positions, each at its element type. *)
      let params,element = if not rest then params,None else
        match List.rev params with
        | last :: fixed ->
          (match Semantic.tuple_positions ~readonly:true last,Semantic.array_element ~readonly:true last with
           | Some elements,_ -> List.rev fixed @ elements,None
           | None,Some element -> List.rev fixed,Some element
           | _ -> Proposal_diagnostics.unsupported "a rest parameter needs a tuple of required positions or an array")
        | [] -> Proposal_diagnostics.unsupported "a rest parameter needs a parameter" in
      let values = List.filter_map (fun (name,b) -> match b with
        | Value _ | Local _ -> Some name | Storage _ -> None) inner @ module_names in
      let readable (a:expr) key =
        match latest_claim a.pos with
        | Some t -> (match declared_head declarations [] t with
          | Atoms [Shape shape] ->
            (shape.elements <> None && key=Name "length") ||
            List.exists (fun (f:field) -> f.name=key && not f.optional && not f.host) shape.fields
          | Atoms [Exact fields] -> List.exists (fun (f:field) -> f.name=key && not f.optional) fields
          | _ -> false)
        | None -> false in
      let callable (callee:expr) =
        match latest_claim callee.pos with
        | Some t -> (match declared_head declarations [] t with
          | Atoms [Shape {calls;fields=[];indexes=[];elements=None}] -> calls <> [] &&
            List.for_all (fun (s:signature) -> s.call_effect=PreservesInputHeap &&
              s.variadic=None && s.rest_pack=None) calls
          | _ -> false)
        | None -> false in
      (* Rest entries have a separate wrapper; its signature transport remains
         conservative until that lowering carries the inferred effect too. *)
      let call_effect = if not rest && heap_preserving_expr ~readable ~callable values body &&
        List.for_all (fun (_,d) -> heap_preserving_expr ~readable ~callable values d) defaults
        then PreservesInputHeap else Unrestricted in
      let own = match element with
        | Some element -> variadic_arrow ~call_effect ~quantified ~receiver params element result
        | None -> quantified_arrow ~call_effect ~receiver quantified params result in
      (* A named closure passed where more parameters are offered is claimed
         at those signatures too, beside its own: calls through it discard
         the actuals past its parameters, and Lean checks its body at each. *)
      (* A closure literal expected at one signature binding more parameters
         than it does, whose leading positions its own take, is offered it
         where it is created, as a named one is offered by its uses. *)
      (* Expected at several signatures (a method whose rest is a union of
         tuples, `next(...[value]: [] | [TNext])`), it is offered each that
         binds more, beside its own, which takes the others. *)
      let implements_arity (s:Semantic.signature) =
        s.quantified=[] && s.variadic=None && List.length s.params = List.length ps in
      let longer (s:Semantic.signature) = s.quantified=[] && s.rest_pack=None
        && (match s.variadic with
            | None -> List.length s.params > List.length ps
            | Some _ -> List.length s.params >= List.length ps)
        && List.for_all2 plausible_subtype
             (List.filteri (fun i _ -> i < List.length ps) s.params) (List.map snd ps) in
      let from_context = match expected with
        | Some t -> (match (try declared_head declarations [] t with Json.Error _ -> t) with
          | Atoms [Shape {calls=[s];fields=[];indexes=[];elements=None}] when longer s -> [s]
          | Atoms [Shape {calls=(_::_::_ as calls);fields=[];indexes=[];elements=None}]
            when not (List.for_all implements_arity calls) -> List.filter longer calls
          | _ -> [])
        | None -> [] in
      let offered_here = match List.assoc_opt e.pos offered, from_context with
        | None,[] -> None
        | extra,context -> Some (Option.value extra ~default:[] @ context) in
      let own = match offered_here, own with
        | Some extra, Atoms [Shape ({calls=[call];_} as shape)] when quantified=[] && element=None ->
          Atoms [Shape {shape with calls=call :: List.filter (fun s -> s <> call)
            (List.sort_uniq compare (List.map (fun s -> {s with call_effect}) extra))}]
        | _ -> own in
      (* A contract advertising several signatures is implemented by this one
         closure. Propose that contract and state what the body claims under
         each signature; Lean checks every one of them. *)
      let implements (s:Semantic.signature) =
        s.quantified=[] && s.variadic=None && element=None && List.length s.params=List.length ps in
      (match expected with
       | Some (Atoms [Shape {calls=(_::_::_ as calls);fields=[];indexes=[];elements=None}] as contract)
         when quantified=[] && defaults=[] && List.for_all implements calls ->
         let row (s:Semantic.signature) =
           (* An entry environment replaces the context it is checked against,
              so a body's entries are stated per signature like its
              expressions. *)
           collect_overload_row_claims (fun () ->
             let env_row = List.fold_left2 (fun env (n,_) t -> extend env n (Value t))
               env ps s.params in
             ignore (infer_closure_body ~expected:s.result env_row)) in
         let rows = List.map row calls in
         publish_arrow e.pos rows;
         contract
       | _ -> own)
    | _ -> Json.fail "expression dispatched to the wrong typing family"
end
