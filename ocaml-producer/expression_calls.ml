open Semantic
open Source
open Inference
open Type_queries
open Proposal_diagnostics
module type Inputs = sig
  include Expression_support.Inputs
  include Analysis_capabilities.Path_queries
  include Analysis_capabilities.Exact_allocations
  include Analysis_capabilities.Offer_operations
  include Analysis_capabilities.Evolution
  include Analysis_capabilities.Instance_publication
  include Analysis_capabilities.Claim_operations
  val observe_method_call : Json.t -> unit
end
module Make (S : Inputs) = struct
open S
module Support = Expression_support.Make(S)
open Support
let infer (expr:Analysis_state.expression_infer) _execute_bindings (_body:Analysis_state.body_infer) ?expected env (e:Source.expr) =
  let site = e.pos in
  match e.node with
    | Call _ | Invoke _ ->
      (* A method call types its callee, the read of the method, and so its
         object; the receiver Lean checks is that object. *)
      let callee,receiver,args,spreads,type_args = match e.node with
        | Call (c,r,a,s,t) -> c,r,a,s,t
        | Invoke (c,a,s,t) -> c,None,a,s,t
        | _ -> assert false in
      (* An evolving array's `push` and `unshift` add their arguments. *)
      (match callee.node with
       | Read (o,Name ("push" | "unshift")) when spreads = [] ->
         Option.iter (fun k -> List.iter (fun a ->
           Option.iter (evolve k) (quietly (fun () -> expr env a))) args) (evolving_array o)
       | _ -> ());
      (* Explicit type arguments fix the callee's leading binders; the others
         are inferred from the receiver and the actuals. Lean checks that the
         claimed instance agrees with them. *)
      let infer_explicit ~receiver ?expected (signature:Semantic.signature) actuals =
        let native id = List.exists (fun (d:Source.declaration) -> d.id=id && d.native_promise) declarations in
        let expand = expand_named declarations in
        if List.length type_args > List.length signature.quantified then
          Proposal_diagnostics.unsupported "more explicit type arguments than the callee has binders";
        let fixed = List.mapi (fun i t ->
          (List.nth signature.quantified i).identity,ValueArgument t) type_args in
        let fixed = Inference.qualify_substitution ~native ~expand ~owned:owned_resolution
          ~observed:observation_owner signature.quantified fixed in
        let partial = Inference.substitute_signature fixed
          {signature with quantified=List.filteri (fun i _ -> i >= List.length type_args)
             signature.quantified} in
        if partial.quantified = [] then fixed,partial.result
        else
          let inferred = Inference.infer ~expand ~native ~owned:owned_resolution ~observed:observation_owner ~receiver ?expected partial actuals in
          fixed @ inferred.substitution,inferred.result in
      let no_type_arguments () = if type_args <> [] then
        Proposal_diagnostics.unsupported "explicit type arguments on a callee without binders" in
      let target = callee in
      observe_method_call callee.pos;
      (* A binder's value is called at its bound, as it is read there. *)
      let callee = match declared_head declarations [] (expr env callee) with
        | Rigid r -> (match rigid_bound r with
          | Some b -> declared_head declarations [] b
          | None -> Rigid r)
        | t -> t in
      (* The receiver the call passes: the `.call` operand, the object a
         method is read from, or `undefined`. A scheme infers from it too. *)
      let receiver_type = match receiver, target.node with
        | Some r, _ -> expr env r
        | None, (Read (o,_) | Index (o,_)) when (match e.node with Invoke _ -> true | _ -> false) ->
          (match latest_claim o.pos with
           | Some t -> t
           | None -> Atoms [Undef])
        | None, _ -> Atoms [Undef] in
      (* A closure passed where a callback is offered more parameters than it
         binds — a fixed signature taking more, or a variadic one whose fixed
         parameters cover them — is claimed at the offered signature: calls
         through it discard the actuals past its parameters, and Lean checks
         its body at the offered receiver, parameters and result. A literal is
         claimed there; a named closure, where it is created, beside its own
         signature, and only at a signature whose positions its parameters
         take: another is not one its body could be checked at. The result is
         the action stating the offer. *)
      let offer_to (arg:expr) param =
        (* Arity adaptation may retain a guarantee already inferred for the
           value; adding ignored parameters cannot manufacture an effect.
           Overload selection uses this type, never the callback's body. *)
        let supplies_effect (offered:Semantic.signature) =
          offered.call_effect=Unrestricted ||
          let known = match arg.node with
            | Id name -> quietly (fun () -> resolve env name)
            | _ -> latest_claim arg.pos in
          match known with
          | Some (Atoms [Shape {calls;_}]) -> List.exists (fun (s:Semantic.signature) ->
              s.call_effect=offered.call_effect) calls
          | _ -> false in
        let offered arity = match param with
          | Atoms [Shape {calls=[offered];fields=[];indexes=[];elements=None}] as t
              when offered.quantified=[] && offered.rest_pack=None && supplies_effect offered
                && (match offered.variadic with
                    | None -> List.length offered.params > arity
                    | Some _ -> List.length offered.params >= arity) -> Some (t,offered)
          | _ -> None in
        match arg.node with
        | Lambda (_,[],ps,_,false,_,_) ->
          Option.map (fun (t,_) () -> publish_instance arg.pos t)
            (offered (List.length ps))
        | Id n when List.mem_assoc n (path_facts ()).Proposal_flow.closures ->
          (match param with
           | Atoms [Shape {calls=[o];fields=[];indexes=[];elements=None}]
               when supplies_effect o -> closure_offer n o
           | _ -> None)
        (* A class value at a generic call's construct parameter, known only
           once the call's instance is: offered as where the parameter's type
           is expected. *)
        | Id n when List.mem_assoc n (path_facts ()).Proposal_flow.classes ->
          Some (fun () -> offer_class (List.assoc n (path_facts ()).Proposal_flow.classes) param)
        (* Any other named function is not offered a signature binding more
           parameters: a module function that discards the actuals past its
           parameters meets it from its slot, and any other is refused. *)
        | Id n ->
          explain_builtin_array arg.pos env n (Some param);
          explain_record_at_index arg.pos env n (Some param);
          (match param, (try Some (resolve env n) with Json.Error _ -> None) with
           | Atoms [Shape {calls=[o];_}], Some (Atoms [Shape {calls=[own];fields=[];indexes=[];elements=None}])
               when List.length o.params > List.length own.params || (o.variadic <> None && own.variadic = None) ->
             Option.iter (S.explain arg.pos) (Module_contract.longer_refusal
               (if List.mem_assoc n env then None else module_arity n))
           | _ -> ());
          None
        | _ -> None in
      let param_at (s:Semantic.signature) i = match List.nth_opt s.params i with
        | Some p -> Some p
        | None -> s.variadic in
      (* Several candidate signatures (overloads, or a union's arms): an
         actual is built at a parameter every candidate states alike, as a
         single signature's actuals are, and typed on its own otherwise. *)
      let shared_actuals (candidates:Semantic.signature list) =
        List.mapi (fun i arg ->
          match List.map (fun s -> param_at s i) candidates with
          | Some p :: rest when List.for_all (fun q -> q = Some p) rest ->
            expr ~expected:p env arg,Some p
          | _ -> expr env arg,None) args in
      let offer ?(substitute=Fun.id) (s:Semantic.signature) =
        List.iteri (fun i arg -> Option.iter (fun p ->
          Option.iter (fun state -> state ()) (offer_to arg (substitute p))) (param_at s i)) args in
      (match callee with
       | Atoms [Shape {calls=[{quantified=[];variadic=None;rest_pack=Some (PackParameter _);params;result;_}];_}]
           when spreads = [List.length args - 1] && List.length params = List.length args - 1 ->
         (* A rest that is a packed binder's argument lists, after the fixed
            actuals: one spread of a value of that binder, whose elements are
            one of its lists (Lean's `callPacked`). *)
         no_type_arguments ();
         List.iteri (fun i e -> match List.nth_opt params i with
           | Some p -> ignore (expr ~expected:p env e)
           | None -> ignore (expr env e)) args;
         result
       | Atoms [Shape {calls=[{quantified=[];variadic=Some element;params;result;_} as signature];_}] ->
         no_type_arguments ();
         offer signature;
         (* A variadic callee: the fixed actuals at its parameters, every
            further actual at its element type, and a spread at its own array
            contract, whose elements Lean checks against the element type. *)
         (* A shorter call omits trailing fixed positions, each admitting
            `undefined`, and writes nothing further. *)
         if List.length args < List.length params
            && not (List.for_all Semantic.admits_undefined
                      (List.filteri (fun i _ -> i >= List.length args) params))
         then Proposal_diagnostics.unsupported "a variadic call omits a fixed parameter that does not admit undefined";
         List.iteri (fun i e ->
           if List.mem i spreads then
             Option.iter (fun arm ->
               S.explain (e:expr).pos ("a spread argument of " ^ arm ^ ": " ^ iteration_reason))
               (non_array_arm declarations [] (expr env e))
           else match List.nth_opt params i with
             | Some p -> ignore (expr ~expected:p env e)
             | None -> ignore (expr ~expected:element env e)) args;
         result
       | Atoms [Shape {calls=[signature];_}]
           when signature.quantified<>[] && signature.rest_pack<>None ->
         (* A rest typed by a pack parameter: the actuals past the fixed ones,
            widened as TypeScript infers them, are its instance, a tuple; the
            other binders are inferred from the fixed actuals. Lean checks the
            instance against the bound, position by position. *)
         if type_args <> [] then Proposal_diagnostics.unsupported "explicit type arguments beside a pack parameter";
         let fixed = List.length signature.params in
         if List.length args < fixed then
           Proposal_diagnostics.unsupported "a call omits a fixed parameter before a pack parameter";
         let actuals = List.map (expr env) args in
         (* A spread past the fixed actuals is a tuple's required positions,
            which the call reads as actuals (Lean's lowering). *)
         let extras = List.concat (List.filteri (fun i _ -> i >= fixed) (List.mapi (fun i t ->
           if not (List.mem i spreads) then [t]
           else match Option.value (expand_named declarations t) ~default:t with
             | Atoms [Shape {elements=Some {required;optional_elements=[];rest=None;_};_}] -> required
             | _ -> Proposal_diagnostics.unsupported "a spread into a pack parameter of what is no tuple of required positions")
           actuals)) in
         if List.exists (fun i -> i < fixed) spreads then
           Proposal_diagnostics.unsupported "a spread into a pack parameter's fixed parameters";
         let pack = Pack {required=List.map Semantic.widen extras;
           optional_elements=[];rest=None;readonly=false;presence=Dense} in
         let solution = match signature.rest_pack with
           | Some (PackParameter p) when List.exists (fun (q:Semantic.quantifier) -> q.identity=p &&
               (match q.bound with Some (PackArgument _) -> true | _ -> false)) signature.quantified ->
             [p,PackArgument pack]
           (* A binder typing a value too: its instance is the tuple of the
              collected actuals, whose argument lists the rest's are. *)
           | Some (PackParameter p) when List.exists (fun (q:Semantic.quantifier) -> q.identity=p)
               signature.quantified ->
             [p,ValueArgument (Semantic.array {required=List.map Semantic.widen extras;
               optional_elements=[];rest=None;readonly=false;presence=Dense})]
           | _ -> Proposal_diagnostics.unsupported "a pack rest that is not the method's own parameter" in
         let rest_quantified = List.filter (fun (q:Semantic.quantifier) ->
           not (List.mem_assoc q.identity solution)) signature.quantified in
         let partial = Inference.substitute_signature solution
           {signature with quantified=rest_quantified} in
         let substitution,result =
           if rest_quantified = [] then solution,partial.result
           else
             let inferred = Inference.infer ~expand:(expand_named declarations) ~receiver:receiver_type
               {partial with rest_pack=None}
               (List.filteri (fun i _ -> i < fixed) actuals) in
             solution @ inferred.substitution,inferred.result in
         instance_of ~declared:callee target substitution;
         offer ~substitute:(Inference.substitute substitution) signature;
         if not (method_read target) then
           publish_substitution e.pos (List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t) substitution);
         result
       | Atoms [Shape {calls=[signature];_}]
           when signature.quantified<>[] && signature.variadic<>None ->
         (* The binders the receiver fixes alone (`push` of a `T[]`, the
            array's `T`): a fresh literal at a parameter they instantiate is
            built at it, as TypeScript's contextual type of it is. A hint:
            Lean checks the actual at the instance. *)
         let fixed = lazy (if not (Semantic.mentions_rigid signature.receiver) then None else
           try Some (Inference.infer ~expand:(expand_named declarations) ~receiver:receiver_type
                  {signature with params=[];variadic=None} []).substitution
           with Json.Error _ -> None) in
         let built (arg:expr) i = match arg.node,Lazy.force fixed,param_at signature i with
           | (Alloc _ | ArrayLiteral _),Some solution,Some p
             when not (List.exists (fun (_,a) -> a = ValueArgument top) solution) ->
             let t = Inference.substitute solution p in
             if Semantic.mentions_rigid t then None else Some t
           | _ -> None in
         let actuals = List.concat (List.mapi (fun i arg ->
           let actual = expr ?expected:(if List.mem i spreads then None else built arg i) env arg in
           if not (List.mem i spreads) then [actual]
           else if i < List.length signature.params then
             Proposal_diagnostics.unsupported "a spread cannot fill fixed parameters of a variadic signature"
           else match Semantic.tuple_positions ~readonly:true actual, Semantic.array_element ~readonly:true actual with
             | Some positions,_ -> positions
             | None,Some element -> [union element (Atoms [Undef])]
             | _ -> Proposal_diagnostics.unsupported "generic spread requires an array or a tuple of required positions") args) in
         let missing = max 0 (List.length signature.params - List.length actuals) in
         let substitution,result = infer_explicit ~receiver:receiver_type signature
           (actuals @ List.init missing (fun _ -> Atoms [Undef])) in
         instance_of ~declared:callee target substitution;
         if not (method_read target) then
         publish_substitution e.pos (List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t) substitution);
         result
       | _ ->
      let spread = spreads <> [] in
      (* Into fixed parameters, each spread's elements are read once every
         actual is evaluated, where the call reads them: so no actual after
         the first spread may run code. *)
      let last_only = spreads = [List.length args - 1] in
      if spread && not last_only then
        List.iteri (fun i (a:expr) ->
          if i > List.fold_left min max_int spreads then match a.node with
            | Id _ | Literal _ -> ()
            | _ -> Proposal_diagnostics.unsupported "a spread into fixed parameters followed by an actual that runs code") args;
      (* A call writes a prefix of the declared positions. The rest are omitted,
         which is admissible exactly when each of their contracts admits
         `undefined`; Lean checks that premise for itself. *)
      (* A spread argument stands for the required elements of its operand's
         tuple contract: the call writes those positions. *)
      (* Counting the positions must not state the operand's claim twice, so a
         name is read from the environment and anything else is typed once,
         here, and not again below. *)
      let spread_types = List.map (fun i -> i,lazy (match List.nth args i with
        | { node = Id name; _ } -> resolve env name
        | operand -> expr env operand)) spreads in
      let spread_positions i =
        match Semantic.tuple_positions (Lazy.force (List.assoc i spread_types)) with
        | Some elements -> List.length elements
        | None -> Proposal_diagnostics.unsupported "a spread argument needs a tuple of required positions" in
      (* The position each actual starts at: a spread writes as many as its
         tuple has. *)
      let offsets = List.rev (snd (List.fold_left (fun (at,acc) i ->
        (at + (if List.mem i spreads then spread_positions i else 1)),at :: acc)
        (0,[]) (List.init (List.length args) Fun.id))) in
      let written_positions =
        List.fold_left (+) 0 (List.mapi (fun i _ ->
          if List.mem i spreads then spread_positions i else 1) args) in
      let callable (signature:Semantic.signature) =
        let declared = List.length signature.params and written = written_positions in
        (signature.variadic <> None && written >= declared)
        || (written <= declared
            && List.for_all Semantic.admits_undefined
                 (List.filteri (fun i _ -> i >= written) signature.params)) in
      (* Of several advertised signatures, the only one taking this many
         arguments is the one the call uses: its parameters guide the
         actuals' construction, as a single signature's do. *)
      let callee = match callee with
        | Atoms [Shape ({calls=(_::_::_ as calls);_} as shape)]
            when List.for_all (fun (s:Semantic.signature) -> s.quantified=[]) calls ->
          (match List.filter callable calls with
           | [s] -> Atoms [Shape {shape with calls=[s]}]
           | _ -> callee)
        | _ -> callee in
      (match callee with Atoms [Shape {calls=[signature];_}]
          when signature.quantified=[] && callable signature ->
        no_type_arguments ();
        (* A spread operand is checked at its own tuple contract; Lean reads
           the positions from that contract and checks each of them. *)
        List.iteri (fun i (e:expr) ->
          if List.mem i spreads then
            (match e.node with Id _ -> ignore (expr env e) | _ -> ())
          else let expected = match List.nth_opt signature.params (List.nth offsets i) with
            | Some t -> t
            | None -> (match signature.variadic with
              | Some t -> t
              | None -> Proposal_diagnostics.unsupported "call has too many arguments") in
            ignore (expr ~expected env e)) args;
        offer signature;
        signature.result
      | Atoms [Shape {calls=[signature];_}]
          when signature.quantified<>[] && callable signature && (last_only || not spread) ->
        (* Omission contributes undefined to inference, but no expression or
           claim is inserted into the source's argument list. An actual at a
           parameter mentioning no type parameter is built at it, as at a
           call without binders: TypeScript types it contextually, and a
           fresh literal leaving out an optional field is claimed at its
           exact keys there. Explicit type arguments naming every binder give
           every parameter its type, and each actual is built at it. *)
        let stated = if List.length type_args <> List.length signature.quantified then None
          else Some (List.map2 (fun (q:Semantic.quantifier) t -> q.identity,ValueArgument t)
            signature.quantified type_args) in
        (* An array literal at a parameter typed by a binder bounded by a
           tuple is built at that tuple, as TypeScript types it by the
           constraint: `exact<K extends [0, 1]>(x: K)` called with `[0, 1]`
           instantiates `K` at the tuple, not at `number[]`. A bound with one
           tuple arm of the literal's length among others, through its
           declarations (`S extends [number, number] | string`), is that arm,
           as TypeScript's contextual type makes the literal a tuple. *)
        let tuple_bound (arg:expr) = function
          | Rigid r -> (match List.find_opt (fun (q:Semantic.quantifier) -> q.identity = r)
                          signature.quantified with
            | Some {bound=Some (ValueArgument (Atoms [Shape {elements=Some {rest=None;_};fields=[];
                calls=[];indexes=[]}] as t));_} -> Some t
            | Some {bound=Some (ValueArgument t);_} ->
              let length = match arg.node with ArrayLiteral (es,[]) -> List.length es | _ -> -1 in
              (match List.filter (function
                 | Shape {elements=Some {rest=None;required;optional_elements;_};fields=[];calls=[];indexes=[]} ->
                   List.length required <= length
                   && length <= List.length required + List.length optional_elements
                 | _ -> false) (flat_atoms declarations t) with
               | [arm] -> Some (Atoms [arm])
               | _ -> None)
            | _ -> None)
          | _ -> None in
        (* A fresh array literal at a parameter whose every binder is
           bounded by literal types is built at the parameter read at those
           bounds, as TypeScript keeps a fresh literal's literal type where a
           binder's constraint names literals: `pick<K extends 0 | 1>(e:
           Array<[K, number]>)` called with `[[0, 1]]` builds a pair whose
           first position is `0 | 1`, and `K` is inferred from it. *)
        let literal_bounds p =
          let literal = function
            | Nul | Undef | True | False | NumLit _ | StrLit _ | BigintLit _ -> true
            | _ -> false in
          let solution = List.filter_map (fun (q:Semantic.quantifier) -> match q.bound with
            | Some (ValueArgument (Atoms (_::_ as atoms) as t)) when List.for_all literal atoms ->
              Some (q.identity,ValueArgument t)
            | _ -> None) signature.quantified in
          if solution = [] then None
          else
            let t = Inference.substitute solution p in
            if Semantic.mentions_rigid t then None else Some t in
        let dictionary_bound = function
          | Rigid r -> (match List.find_opt (fun (q:Semantic.quantifier) -> q.identity = r)
                          signature.quantified with
            | Some {bound=Some (ValueArgument t);_} ->
              (match object_hint declarations [] t with
               | Some sh when List.exists (fun (i:Semantic.index_signature) -> i.keys = Semantic.Strings) sh.indexes -> Some t
               | _ -> None)
            | _ -> None)
          | _ -> None in
        (* A spread's actuals are its tuple's positions, which Lean reads
           and checks each at its parameter. *)
        let actuals=List.concat (List.mapi (fun i (arg:expr) ->
          if List.mem i spreads then begin
            (match arg.node with Id _ -> ignore (expr env arg) | _ -> ());
            match Semantic.tuple_positions (Lazy.force (List.assoc i spread_types)) with
            | Some positions -> positions
            | None -> Proposal_diagnostics.unsupported "a spread argument needs a tuple of required positions"
          end else [match param_at signature (List.nth offsets i),stated with
          | Some p,_ when not (Semantic.mentions_rigid p) -> expr ~expected:p env arg
          | Some p,Some solution -> expr ~expected:(Inference.substitute solution p) env arg
          | Some p,None when (match arg.node with ArrayLiteral _ -> true | _ -> false)
                              && tuple_bound arg p <> None ->
            expr ?expected:(tuple_bound arg p) env arg
          | Some p,None when (match arg.node with ArrayLiteral _ -> true | _ -> false)
                              && literal_bounds p <> None ->
            expr ?expected:(literal_bounds p) env arg
          (* A dictionary bound guides a fresh literal's construction.
             Readonly bounds admit precise field contracts; writable bounds
             supply the index's storage contract. *)
          | Some p,None when (match arg.node with Alloc _ -> true | _ -> false)
                              && dictionary_bound p <> None ->
            (match dictionary_bound p with
             | Some bound ->
               (match object_hint declarations [] bound with
                | Some shape when shape.fields = [] && List.for_all (fun (i:Semantic.index_signature) -> i.writable = None) shape.indexes ->
                  (* A read-only bound constrains the argument's view. Infer
                     fresh literal storage from its values, retaining exact
                     keys so Lean can check the bound independently. *)
                  let rec exact_literals (e:expr) = match e.node with
                    | Alloc fs -> mark_exact e; List.iter (fun (_,v) -> exact_literals v) fs
                    | ArrayLiteral (es,_) -> List.iter exact_literals es
                    | _ -> () in
                  exact_literals arg;
                  expr env arg
                | _ -> expr ~expected:bound env arg)
             | None -> expr env arg)
          | p,_ ->
            (match arg.node with Id n -> explain_builtin_array arg.pos env n p | _ -> ());
            expr env arg]) args) @
          List.init (max 0 (List.length signature.params - written_positions)) (fun _ -> Atoms [Undef]) in
        explain_thenable e target actuals;
        let substitution,result = infer_explicit ~receiver:receiver_type ?expected signature actuals in
        instance_of ~declared:callee target substitution;
        offer ~substitute:(Inference.substitute substitution) signature;
        if not (method_read target) then
        publish_substitution e.pos (List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t) substitution);
        result
      (* Quantified overloads use the same proposal/validation split as one
         quantified signature. Type the actuals once, infer an instance for
         each arity-compatible signature, then offer one matching contract.
         Only that signature is projected from the scheme; Lean independently
         checks both the projection and the call, including its receiver.
         A nonmatching proposal may still be emitted to locate the failed
         obligation; it is never acceptance. *)
      | Atoms [Shape ({calls=(_::_::_ as calls);_} as shape)]
          when not spread && List.for_all (fun (s:Semantic.signature) ->
            s.quantified<>[] && s.variadic=None && s.rest_pack=None) calls ->
        let usable = List.filter callable calls in
        let actuals = shared_actuals usable in
        let proposals = List.filter_map (fun (s:Semantic.signature) ->
          Option.map (fun (substitution,result) -> s,substitution,result)
            (quietly (fun () -> infer_explicit ~receiver:receiver_type ?expected s
              (List.map fst actuals @ List.init (max 0 (List.length s.params - List.length args))
                (fun _ -> Atoms [Undef]))))) usable in
        let matches_actuals ((s:Semantic.signature),substitution,_) =
          let at = Inference.substitute substitution in
          List.for_all Fun.id (List.mapi (fun i (arg,(t,_)) ->
            match List.nth_opt s.params i with
            | Some p -> plausible_subtype t (at p) || offer_to arg (at p) <> None
            | None -> false) (List.combine args actuals)) in
        let matching = List.filter matches_actuals proposals in
        let receiver_matches ((s:Semantic.signature),substitution,_) =
          plausible_subtype_with
            (fun t -> excludes_undefined (declared_head declarations [] t))
            receiver_type (Inference.substitute substitution s.receiver) in
        let preferred = match List.find_opt receiver_matches matching with
          | Some p -> Some p
          | None -> (match matching with
            | p::_ -> Some p
            | [] -> List.find_opt receiver_matches proposals) in
        (match preferred,proposals with
         | Some (s,substitution,result),_ | None,((s,substitution,result)::_) ->
           instance_of ~declared:(Atoms [Shape {shape with calls=[s]}]) target substitution;
           offer ~substitute:(Inference.substitute substitution) s;
           if not (method_read target) then
             publish_substitution e.pos (List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t) substitution);
           result
         | None,[] -> Proposal_diagnostics.unsupported "quantified overloads have no inferable arity-compatible instance")
      (* Several advertised signatures on one value. The actuals are built
         as the usable signatures agree (`shared_actuals`), and the signature
         whose domains they match is proposed. Lean selects the row it checks
         and re-checks every argument obligation. *)
      | Atoms [Shape {calls=(_::_::_ as calls);_}]
          when List.for_all (fun (s:Semantic.signature) -> s.quantified=[]) calls
               && (last_only || not spread) ->
        no_type_arguments ();
        let usable = List.filter callable calls in
        let actuals = shared_actuals usable in
        (* A closure an offer would claim at the parameter matches it, as
           does an actual built at it. *)
        let matching = List.filter (fun (s:Semantic.signature) ->
          List.for_all Fun.id (List.mapi (fun i (arg,(t,built)) -> match param_at s i with
            | Some p -> built = Some p || plausible_subtype t p || offer_to arg p <> None
            | None -> false) (List.combine args actuals))) usable in
        (match matching,usable with
         | s :: _,_ -> offer s; s.result
         | [],(first :: rest) when List.for_all (fun (s:Semantic.signature) ->
             s.result = first.result) rest -> first.result
         | _ -> Proposal_diagnostics.unsupported "overloaded call needs a signature its arguments match")
      (* A union of callables: the call is one of its arms' calls, whichever
         the value is, so it is valid when every arm takes the actuals, and
         its value is the union of the arms' results. The actuals are built
         as the arms agree (`shared_actuals`); Lean splits the saved callee
         and checks the call once per arm. *)
      | Atoms (_::_::_ as arms) when not spread && List.for_all (function
          | Semantic.Shape {calls=[s];_} -> s.quantified=[] && s.variadic=None
              && s.rest_pack=None && callable s
          | _ -> false) arms ->
        no_type_arguments ();
        let signatures = List.filter_map (function
          | Semantic.Shape {calls=[s];_} -> Some s | _ -> None) arms in
        ignore (shared_actuals signatures);
        List.fold_left (fun acc (s:Semantic.signature) -> union acc s.result)
          (Atoms []) signatures
      (* JavaScript drops actuals past the parameters, but the calculus's call
         takes no more actuals than its signature's positions. *)
      | Atoms [Shape {calls=[{variadic=None;rest_pack=None;params;_}];_}]
          when written_positions > List.length params ->
        Proposal_diagnostics.unsupported "a call writes more positions than its callee's parameters, which TypeScript rejects"
      (* `(() => R) & { a: T }` is a function carrying fields, the model's
         callable object; the meet of an arrow and a record forms none. *)
      | Meet _ -> Proposal_diagnostics.unsupported "a call of an intersection of a function type and a record, a callable with fields, which an annotation's meet does not form"
      | Atoms kinds when List.mem Callable kinds && List.for_all (function
          | Callable | Ctors ([],_) -> true | _ -> false) kinds ->
        let location = match site with
          | Json.Array [Json.Number first;Json.Number last] -> "[" ^ first ^ "," ^ last ^ ")"
          | _ -> Proposal_diagnostics.unsupported "call has an invalid source span" in
        Proposal_diagnostics.unsupported ("call at " ^ location ^ ": value has no admitted call signature")
      | _ -> Proposal_diagnostics.unsupported "call requires a single arrow the arguments can call"))
    | _ -> Json.fail "expression dispatched to the wrong typing family"
end
