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
  include Analysis_capabilities.Expression_publication
  val observe_method_call : Json.t -> unit
end
module Make (S : Inputs) = struct
open S
module Support = Expression_support.Make(S)
open Support
(* A callback's parameter against a closure literal's written one, asked
   for the same pair at every call of a native at the elements fact: once
   per pair and declarations. *)
module Pairs = Hashtbl.Make (struct
  type t = Semantic.ty * Semantic.ty
  let equal (a, b) (c, d) = (a == c || a = c) && (b == d || b = d)
  let hash = Hashtbl.hash_param 256 1024
end)
let takes_memo : bool Pairs.t = Pairs.create 64
let takes_declarations = ref None
let takes_at declarations passed own =
  (match !takes_declarations with
   | Some d when d == declarations -> ()
   | _ -> Pairs.reset takes_memo; takes_declarations := Some declarations);
  match Pairs.find_opt takes_memo (passed, own) with
  | Some r -> r
  | None ->
    let r = plausible_subtype_declared declarations passed own in
    Pairs.replace takes_memo (passed, own) r; r
let infer (expr:Analysis_state.expression_infer) _execute_bindings (_body:Analysis_state.body_infer) ?expected env (e:Source.expr) =
  let site = e.pos in
  (* A type mentioning a hole (`contextual_actual`) guides a callback's
     result alone (`result_bound`); the call's instance is inferred from its
     actuals. *)
  let contextual = expected in
  let expected = match expected with Some t when mentions_hole t -> None | _ -> expected in
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
      (* A promise signature states what a call promises of an actual, not
         its result: the call is typed at the plain ones, and a condition
         narrows by the promise (`Refinement.promise_refine`). *)
      let callee = match callee with
        | Atoms [Shape ({calls;_} as shape)]
          when List.exists (fun (s:Semantic.signature) -> not (Semantic.plain_effect s.call_effect)) calls ->
          Atoms [Shape {shape with calls=List.filter (fun (s:Semantic.signature) ->
            Semantic.plain_effect s.call_effect) calls}]
        | t -> t in
      (* A signature stating a precondition on the call's values (`pre`,
         Lean's `call-requires`) is the call's where the bounds holding at
         its statement's start establish each fact of it, its positions the
         receiver and the actuals; the others are then dropped. Elsewhere the
         call is typed at the signatures stating none, or, where every
         signature states one, at them all. A proposal: Lean checks the
         precondition against its own knowledge at the call. *)
      let callee = match callee with
        | Atoms [Shape ({calls;_} as shape)]
          when List.exists (fun (s:Semantic.signature) -> s.call_effect.pre <> []) calls ->
          let name p = match (if p = 0 then receiver else List.nth_opt args (p - 1)) with
            | Some {node=Id x;_} -> Some x
            | _ -> None in
          (* Each position's actual as a linear expression over safe-integer
             bindings, as Lean reads an operand (`Linear_facts.linear`). *)
          let form p = Option.bind (if p = 0 then receiver else List.nth_opt args (p - 1))
            (Linear_facts.linear env !Linear_facts.current_facts) in
          let holds = function
            | Semantic.Bound_by (x,k,strict) -> (match name x, name k with
              | Some a, Some i -> List.exists (fun (a',i',s) -> a' = a && i' = i && (s || not strict))
                  !Linear_facts.current_bounds
              | _ -> false)
            | Semantic.Int_at k -> Option.is_some (form k)
            | Semantic.Linear_le (fact,d) ->
              let parts = List.map (fun (x,c) -> Option.map (fun (t,k) -> Linear_facts.scale c t, c * k) (form x)) fact in
              List.for_all Option.is_some parts &&
              (let parts = List.filter_map Fun.id parts in
               let terms = Linear_facts.norm (List.concat_map fst parts) in
               let constant = List.fold_left (fun acc (_,k) -> acc + k) 0 parts in
               terms = [] && constant <= d ||
               Linear_facts.entails !Linear_facts.current_facts (terms, d - constant))
            | _ -> false in
          let established = List.filter (fun (s:Semantic.signature) ->
            s.call_effect.pre <> [] && List.for_all holds s.call_effect.pre) calls in
          let plain = List.filter (fun (s:Semantic.signature) -> s.call_effect.pre = []) calls in
          Atoms [Shape {shape with calls=if established <> [] then established else if plain <> [] then plain
            else calls}]
        | t -> t in
      (* A statement's method call on a value the flow types at several
         declarations, whose signatures all state one declared receiver (a
         host family's method, which each arm holding it inherits from one
         base), reads the member off that receiver: the object is claimed at
         it, one label, so Lean reads and invokes the member in one node
         (`Type_queries.dispatches_call`). A proposal: Lean checks the object at
         the receiver. *)
      (match e.node, target.node, callee with
       | Invoke _, Read (o,_), Atoms [Shape {calls=(first :: _ as calls);_}] ->
         (match first.receiver, latest_claim o.pos with
          | (Atoms [Named (_,[])] as receiver), Some claimed
              when Hashtbl.mem Source.statement_calls e.pos
                && List.length (List.sort_uniq compare (Type_queries.unfolded_arms declarations [] claimed)) > 1
                && List.for_all (fun (s:Semantic.signature) -> s.receiver = receiver) calls ->
            restate_expression o.pos receiver
          | _ -> ())
       | _ -> ());
      (* The receiver the call passes: the `.call` operand, the object a
         method is read from, or `undefined`. A scheme infers from it too. *)
      let receiver_type = match receiver, target.node with
        | Some r, _ -> expr env r
        | None, (Read (o,_) | Index (o,_)) when (match e.node with Invoke _ -> true | _ -> false) ->
          (* The object past the member read's guard: values other than
             `null` and `undefined`, at which the read throws. *)
          (match latest_claim o.pos with
           | Some t -> (match Semantic.without_nullish t with Atoms [] -> t | p -> p)
           | None -> Atoms [Undef])
        | None, _ -> Atoms [Undef] in
      (* A method called on a union of hosts each holding it: Lean binds each
         host's member to it before the actuals run (`memberHead`), as for
         `o.m.bind(o)`, so the head is claimed as that bound function, one
         signature at any receiver ([Semantic.bound_union]). Arms with no
         common signature keep their own. Overloaded arms keep every row: an
         arity-compatible first row need not accept the actuals. *)
      let union_member_hosts key =
        match flat_atoms declarations receiver_type with
        | Some (_::_::_ as hosts) -> List.for_all (function
            | Shape {fields;_} -> List.exists (fun (f:Semantic.field) ->
                f.name=key && f.host) fields
            | _ -> false) hosts
        | _ -> false in
      let callee = match e.node, target.node, callee with
        | Invoke _, Read (_,key), Atoms (_::_::_ as arms)
            when union_member_hosts key && List.for_all (function
              | Shape {calls=[_];_} -> true
              | _ -> false) arms ->
          let fits (s:Semantic.signature) = Semantic.plain_effect s.call_effect && s.quantified=[]
            && s.rest_pack=None && (s.variadic<>None || List.length args<=List.length s.params) in
          (match Semantic.bound_union fits arms with
           | Some t -> restate_expression target.pos t; t
           | None -> callee)
        | _ -> callee in
      (* A guard passed by name whose value states its promise signature
         extended by a rest of the actuals it discards: a module function
         without a rest parameter, whose slot states it, or an import whose
         type states it (a compiler-API guard's entry). Its fixed promise
         signature. A value known only by its type states no extension. *)
      let value_promise (arg:expr) = match arg.node with
        | Id n when not (List.mem_assoc n env) ->
          (match quietly (fun () -> resolve env n) with
           | Some t ->
             (match (try declared_head declarations [] t with Json.Error _ -> t) with
              | Atoms [Shape {calls;_}] ->
                let promising = List.filter (fun (c:Semantic.signature) ->
                  c.call_effect.promise <> None && c.quantified=[] && c.rest_pack=None) calls in
                let fixed,extended = List.partition (fun (c:Semantic.signature) -> c.variadic=None) promising in
                (match fixed with
                 | [c] when List.for_all (fun (d:Semantic.signature) ->
                       d.call_effect.promise = c.call_effect.promise) extended
                     && (module_arity n = Some Module_contract.Discards || extended <> []) -> Some c
                 | _ -> None)
              | _ -> None)
           | None -> None)
        | _ -> None in
      (* A guard passed by name meets a callback parameter stating its
         promise at as many parameters or more, each within the guard's own
         parameter, at a promised type within the guard's: its slot, or its
         host entry, states that promise extended by a rest of `unknown`
         elements, the further actuals it discards, which Lean checks the
         argument at. *)
      let guard_meets (arg:expr) = function
        | Atoms [Shape {calls=[c];_}] ->
          (match value_promise arg with
           | Some own ->
             own.call_effect.promise = c.call_effect.promise && own.variadic=None && own.rest_pack=None
             && c.variadic=None && c.rest_pack=None
             && List.length own.params <= List.length c.params
             && List.for_all2 (fun mine theirs -> plausible_subtype_declared declarations theirs mine)
                  own.params (List.filteri (fun i _ -> i < List.length own.params) c.params)
             && plausible_subtype_declared declarations own.result c.result
           | None -> false)
        | _ -> false in
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
          offered.call_effect=Semantic.ordinary_effect ||
          let known = match arg.node with
            | Id name -> quietly (fun () -> resolve env name)
            | _ -> latest_claim arg.pos in
          match known with
          | Some (Atoms [Shape {calls;_}]) -> List.exists (fun (s:Semantic.signature) ->
              (* A fresh result, or a footprint on a throw, the offer does
                 not state is not asked for. *)
              {s.call_effect with fresh=s.call_effect.fresh && offered.call_effect.fresh;
                 on_throw=s.call_effect.on_throw && offered.call_effect.on_throw}=offered.call_effect) calls
          | _ -> false in
        let offered arity = match param with
          | Atoms [Shape {calls=[offered];fields=[];indexes=[];elements=None}] as t
              when offered.quantified=[] && offered.rest_pack=None && supplies_effect offered
                && (match offered.variadic with
                    | None -> List.length offered.params > arity
                    | Some _ -> List.length offered.params >= arity) -> Some (t,offered)
          | _ -> None in
        match arg.node with
        (* A guard closure is claimed at its own signatures, the promise and
           the ones it is offered among them (`Closures`). *)
        | Lambda (_,[],ps,_,false,_,None,_) ->
          Option.map (fun (t,offered) () ->
            (* Closed contextual inference may already offer this signature beside
               the closure's own, with interior claims for both. Keep that
               claim when it meets the parameter: replacing its signatures
               alone would detach those claims from their signatures. *)
            match latest_claim arg.pos with
            | Some (Atoms [Shape {calls;_}] as own)
                when has_arrow_claims arg.pos && not (Semantic.mentions_rigid own)
                  && List.exists (fun (s:Semantic.signature) ->
                  s.quantified=[] && s.variadic=offered.variadic && s.rest_pack=offered.rest_pack
                  && List.length s.params=List.length offered.params) calls
                  && plausible_subtype_declared declarations own t -> ()
            | _ -> publish_instance arg.pos t)
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
        (* A guard passed by name is claimed at a callback parameter stating
           its promise that it meets (`guard_meets`), as TypeScript resolves
           `filter`'s guard overload at it. *)
        | Id _ when guard_meets arg param -> Some (fun () -> publish_instance arg.pos param)
        (* Any other named function is not offered a signature binding more
           parameters: a module function that discards the actuals past its
           parameters meets it from its slot, and any other is refused. *)
        | Id n ->
          explain_builtin_array arg.pos env n (Some param);
          explain_record_at_index arg.pos env n (Some param);
          (match param, (try Some (declared_head declarations [] (resolve env n)) with Json.Error _ -> None) with
           | Atoms [Shape {calls=[o];_}], Some (Atoms [Shape {calls=[own];fields=[];indexes=[];elements=None}])
               when List.length o.params > List.length own.params || (o.variadic <> None && own.variadic = None) ->
             Option.iter (S.explain arg.pos) (Module_contract.longer_refusal own
               (if List.mem_assoc n env then None else module_arity n))
           | _ -> ());
          None
        (* A function a field holds is known only by the field's type. *)
        | Read _ ->
          (match param, Option.bind (quietly (fun () -> expr env arg))
                   (fun t -> try Some (declared_head declarations [] t) with Json.Error _ -> None) with
           | Atoms [Shape {calls=[o];_}], Some (Atoms [Shape {calls=[own];fields=[];indexes=[];elements=None}])
               when own.variadic = None
                 && (List.length o.params > List.length own.params || o.variadic <> None) ->
             Option.iter (S.explain arg.pos) (Module_contract.longer_refusal own None)
           | _ -> ());
          None
        | _ -> None in
      let param_at (s:Semantic.signature) i = match List.nth_opt s.params i with
        | Some p -> Some p
        | None -> s.variadic in
      (* Several candidate signatures (overloads, or a union's arms): an
         actual is built at a parameter every candidate states alike, as a
         single signature's actuals are, and typed on its own otherwise. *)
      (* An object or array literal where the candidates differ is built at
         the first candidate's parameter it fits, as TypeScript reads a
         literal against each overload in turn. *)
      let shared_actuals (candidates:Semantic.signature list) =
        List.mapi (fun i arg ->
          match List.map (fun s -> param_at s i) candidates with
          | Some p :: rest when List.for_all (fun q -> q = Some p) rest ->
            expr ~expected:p env arg,Some p
          | params ->
            let literal = match arg.node with Alloc _ | ArrayLiteral _ -> true | _ -> false in
            (* A record literal fits where each field it writes is a field of
               the parameter's at a plausible type, and it writes each field
               the parameter requires. *)
            let head t = try declared_head declarations [] t with Json.Error _ -> t in
            let written = function
              | Atoms [Exact fields] -> Some fields
              | Atoms [Shape {fields;elements=None;calls=[];_}] -> Some fields
              | _ -> None in
            let fits p = match Option.map head (quietly (fun () -> expr ~expected:p env arg)) with
              | Some t -> (match written t,head p with
                | Some fs,Atoms [Shape {fields=gs;elements=None;_}] ->
                  List.for_all (fun (f:Semantic.field) -> List.exists (fun (g:Semantic.field) ->
                    g.name=f.name && plausible_subtype f.read g.read) gs) fs &&
                  List.for_all (fun (g:Semantic.field) -> g.optional ||
                    List.exists (fun (f:Semantic.field) -> f.name=g.name) fs) gs
                | _ -> plausible_subtype t p)
              | None -> false in
            match (if literal then List.find_opt fits (List.filter_map Fun.id params) else None) with
            | Some p -> expr ~expected:p env arg,Some p
            | None -> expr env arg,None) args in
      (* The binders a pattern (a signature's receiver or result) places
         where a type places a type: a binder itself, or an array's
         element, which a tuple's is the union of its required positions' and
         its rest's, and a union of arrays' the union of its arms' elements,
         as TypeScript reads a method of `A[] | B[]` at `(A | B)[]`. *)
      let rec bind (pattern:ty) (actual:ty) = match pattern,declared_head declarations [] actual with
        | Rigid r,_ -> [r,actual]
        (* An array pattern at a union with one array arm, `readonly T[] |
           undefined`: at that arm, as the other arms hold no array. *)
        | Atoms [Shape {elements=Some _;calls=[];_}],Atoms (_::_::_ as atoms)
            when List.length (List.filter (function Shape {elements=Some _;_} -> true | _ -> false) atoms) = 1 ->
          bind pattern (Atoms (List.filter (function Shape {elements=Some _;_} -> true | _ -> false) atoms))
        | Atoms [Shape {elements=Some p;calls=[];_}],Atoms (_::_ as arms)
            when p.required=[] && p.optional_elements=[] ->
          let arm_elements = List.map (function
            | Semantic.Shape {elements=Some a;_} when a.optional_elements = [] ->
              Some (a.required @ Option.to_list a.rest)
            | _ -> None) arms in
          (match p.rest with
           | Some p when List.for_all Option.is_some arm_elements ->
             (match List.concat_map (Option.value ~default:[]) arm_elements with
              | _::_ as elements -> bind p (Semantic.unions elements)
              | [] -> [])
           | _ -> [])
        | _ -> [] in
      (* Quantified overloads whose receiver or result places a binder where
         the call's receiver or expected type places a type: the binder is that
         type for typing the actuals, as TypeScript infers from the return
         position first. A
         callback actual is typed at the parameter the candidates share once
         their call effects are set aside: the overloads of a callback member
         differ only in the footprint they state, and the actual's own is
         inferred from its body. The proposal is untrusted; Lean checks the
         instance and every actual. *)
      (* A closure literal is offered a callback signature only where its
         parameters take what the signature passes, and its written
         promise is within the one the signature asks for: Lean checks the
         claim within the closure's annotation (`map` at the elements
         fact passes a `string`, `every` at it asks for a guard promising
         one). *)
      let literal_takes (arg:expr) p = match arg.node,p with
        | Lambda (_,_,ps,_,_,_,guard,_),Atoms [Shape {calls=[c];_}] ->
          List.for_all2 (fun passed (_,own) -> takes_at declarations passed own)
            (List.filteri (fun i _ -> i < List.length ps) c.params)
            (List.filteri (fun i _ -> i < List.length c.params) ps)
          && (match guard with
              | Some (_,written) when c.call_effect.promise <> None ->
                plausible_subtype_declared declarations written c.result
              | _ -> true)
        | _ -> true in
      let seeded_actuals (candidates:Semantic.signature list) =
        (* A guard closure's written promise is the type a callback
           parameter stating that promise promises: its result operand, as
           TypeScript infers `filter<S>`'s `S` from the predicate. So is a
           guard passed by name: its promise signature's result. *)
        let promised (s:Semantic.signature) = List.concat (List.mapi (fun i (arg:expr) ->
          match arg.node,param_at s i,value_promise arg with
          | Lambda (_,_,_,_,_,_,Some (stated,written),_),Some (Atoms [Shape {calls=[c];_}]),_
              when c.call_effect.promise <> None && c.call_effect.promise = stated.promise ->
            bind c.result written
          | _,Some (Atoms [Shape {calls=[c];_}]),Some own
              when c.call_effect.promise = own.call_effect.promise ->
            bind c.result own.result
          | _ -> []) args) in
        (* A closure literal at a parameter that is a binder, which an
           earlier parameter's method takes at one of its positions: the
           binder is the callback type the earlier actual's method takes
           there, where exactly one of its signatures of that arity takes a
           callable, as TypeScript infers it from the earlier argument
           (`String.prototype.replace` dispatching to a native regex's
           `[Symbol.replace]`, whose replacer overload takes the callback). *)
        let from_actuals (s:Semantic.signature) =
          let own = List.map (fun (q:Semantic.quantifier) -> q.identity) s.quantified in
          let binders = List.concat (List.mapi (fun i (arg:expr) ->
            match arg.node,param_at s i with
            | Lambda _,Some (Rigid r) when List.mem r own -> [r]
            | _ -> []) args) in
          if binders = [] then [] else
          List.concat (List.mapi (fun i (arg:expr) -> match arg.node,param_at s i with
            | Lambda _,_ -> []
            | _,Some (Atoms [Shape {fields=(_::_ as fields);_}]) ->
              (match Option.bind (quietly (fun () -> expr env arg))
                       (fun t -> try Some (declared_head declarations [] t) with Json.Error _ -> None) with
               | Some (Atoms [Shape {fields=actuals;_}]) ->
                 List.concat_map (fun (f:Semantic.field) ->
                   match f.read,List.find_opt (fun (g:Semantic.field) -> g.name = f.name) actuals with
                   | Atoms [Shape {calls=[c];_}],Some {read=Atoms [Shape {calls;_}];_} ->
                     List.concat (List.mapi (fun j p -> match p with
                       | Rigid r when List.mem r binders ->
                         (match List.filter_map (fun (a:Semantic.signature) ->
                            match List.nth_opt a.params j with
                            | Some (Atoms [Shape {calls=_::_;_}] as t)
                                when List.length a.params = List.length c.params -> Some t
                            | _ -> None) calls with
                          | [t] -> [r,t]
                          | _ -> [])
                       | _ -> []) c.params)
                   | _ -> []) fields
               | _ -> [])
            | _ -> []) args) in
        let seed (s:Semantic.signature) =
          let own = List.map (fun (q:Semantic.quantifier) -> q.identity) s.quantified in
          let found = bind s.receiver receiver_type @ promised s @ from_actuals s @ (match contextual with
            | Some t -> bind s.result t
            | None -> []) in
          let seeds = List.filter_map (fun (r,t) ->
            if List.mem r own then Some (r,ValueArgument t) else None) found in
          {s with receiver=Inference.substitute seeds s.receiver;
            params=List.map (Inference.substitute seeds) s.params} in
        (* A callback parameter with its footprint set aside; its promise
           stays, since a promise signature's result is the promised type. *)
        let plain = function
          | Atoms [Shape ({calls=_::_;_} as sh)] -> Atoms [Shape {sh with calls=List.map (fun (c:Semantic.signature) ->
              {c with call_effect={Semantic.ordinary_effect with promise=c.call_effect.promise}}) sh.calls}]
          | t -> t in
        let candidates = List.map seed candidates in
        (* Contextual callbacks share the first receiver contract the
           actual meets. A readable receiver and a sparse one offer
           different third callback arguments; combining those groups
           would lose the contextual signature even for a guard. All
           advertised overloads remain candidates for the checked call. *)
        let candidates = match List.find_opt (fun (s:Semantic.signature) ->
            plausible_subtype_declared declarations receiver_type s.receiver) candidates with
          | Some first -> List.filter (fun (s:Semantic.signature) -> s.receiver=first.receiver) candidates
          | None -> candidates in
        (* A parameter still naming a candidate's own binder, one neither
           the receiver nor the expected result fixes, is no type to check a
           callback at. *)
        let unbound p = List.for_all (fun (c:Semantic.signature) ->
          let own = List.map (fun (q:Semantic.quantifier) -> q.identity,ValueArgument (Atoms [])) c.quantified in
          Inference.substitute own p = p) candidates in
        (* A module function discarding the actuals past its parameters,
           passed by name, is typed at the shared parameter at its own
           effect: its slot meets that signature, which binds more
           parameters, and the overload stating its effect is the call's. *)
        let own_signature (arg:expr) = match arg.node with
          | Id n when not (List.mem_assoc n env) && module_arity n = Some Module_contract.Discards ->
            (match (try module_type n with Json.Error _ -> None) with
             | Some (Atoms [Shape {calls=[own];_}]) when own.quantified=[] && own.variadic=None
                 && own.rest_pack=None -> Some own
             | _ -> None)
          | _ -> None in
        (* The parameter at the function's own effect; where it still names
           a binder, the function's own signature extended to its
           positions, whose result fixes it. *)
        let at_own (own:Semantic.signature) = function
          | Atoms [Shape ({calls=[c];_} as sh)] as t when not (unbound t)
              && List.length own.params <= List.length c.params ->
            Atoms [Shape {sh with calls=[{c with call_effect=own.call_effect;receiver=own.receiver;
              params=own.params @ List.filteri (fun i _ -> i >= List.length own.params) c.params;
              result=own.result}]}]
          | Atoms [Shape ({calls=_::_;_} as sh)] -> Atoms [Shape {sh with calls=List.map (fun (c:Semantic.signature) ->
              {c with call_effect=own.call_effect}) sh.calls}]
          | t -> t in
        let promise_of (arg:expr) = match arg.node with
          | Lambda (_,_,_,_,_,_,Some (stated,_),_) -> stated.promise
          | _ -> None in
        (* The candidates a closure literal is typed at: for a guard closure,
           those whose callback states its written promise where any does,
           else those whose callback states no promise. *)
        let states promise = function
          | Some (Atoms [Shape {calls=_::_ as calls;_}]) ->
            List.for_all (fun (c:Semantic.signature) -> c.call_effect.promise = promise) calls
          | _ -> promise = None in
        List.mapi (fun i arg ->
          (* Signatures stating a precondition are alternatives for a
             closure literal no other signature's callback takes. *)
          let plain_candidates = List.filter (fun (s:Semantic.signature) ->
            s.call_effect.requires = None) candidates in
          let takes = function Some p -> literal_takes arg p | None -> false in
          let params = match arg.node with
            | Lambda _ when plain_candidates <> []
                && not (List.exists takes (List.map (fun s -> param_at s i) plain_candidates)) ->
              (match List.filter takes (List.map (fun s -> param_at s i) candidates) with
               | [] -> List.map (fun s -> param_at s i) plain_candidates
               | kept -> kept)
            | _ -> List.map (fun s -> param_at s i)
                (if plain_candidates = [] then candidates else plain_candidates) in
          let params = match arg.node with
            | Lambda (_,_,_,_,_,_,guard,_) ->
              (* Of the callbacks stating the written promise, those promising
                 a type the written one is within, where any does (`every`
                 at a guard promising `string`). *)
              let within_written = function
                | Some (Atoms [Shape {calls=_::_ as calls;_}]) ->
                  (match guard with
                   | Some (_,written) -> List.for_all (fun (c:Semantic.signature) ->
                       plausible_subtype_declared declarations written c.result) calls
                   | None -> true)
                | _ -> true in
              (match List.filter (states (promise_of arg)) params, List.filter (states None) params with
               | [],[] -> params
               | [],plain -> plain
               | promised,_ ->
                 (match List.filter within_written promised with
                  | [] -> promised
                  | kept -> kept))
            (* A function passed by name, at those stating the promise its
               type states, or none. *)
            | Id _ ->
              let promise = Option.bind (value_promise arg) (fun (c:Semantic.signature) -> c.call_effect.promise) in
              (match List.filter (states promise) params with
               | [] -> params
               | kept -> kept)
            | _ -> params in
          match params with
          | Some p :: rest when unbound p && List.for_all (fun q -> q = Some p) rest ->
            expr ~expected:p env arg,Some p
          | Some p :: rest when own_signature arg <> None
              && List.for_all (fun q -> Option.map plain q = Some (plain p)) rest ->
            expr ~expected:(at_own (Option.get (own_signature arg)) (plain p)) env arg,None
          | Some p :: rest when (match arg.node with Lambda _ -> true | _ -> false)
              && unbound (plain p)
              && List.for_all (fun q -> Option.map plain q = Some (plain p)) rest ->
            expr ~expected:(plain p) env arg,None
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
         (* A literal, or a choice one of whose values is one
            (`fallback ?? { k: "break" }`). *)
         let rec literal (arg:expr) = match arg.node with
           | Alloc _ | ArrayLiteral _ -> true
           | Conditional (_,a,b) | Coalesce (a,b) | Logical (_,a,b) -> literal a || literal b
           | _ -> false in
         let built (arg:expr) i = match Lazy.force fixed,param_at signature i with
           | Some solution,Some p
             when literal arg && not (List.exists (fun (_,a) -> a = ValueArgument top) solution) ->
             let t = Inference.substitute solution p in
             if Semantic.mentions_rigid t then None else Some t
           | _ -> None in
         let actuals = List.concat (List.mapi (fun i arg ->
           let actual = expr ?expected:(if List.mem i spreads then None else built arg i) env arg in
           if not (List.mem i spreads) then [actual]
           else if i < List.length signature.params then
             Proposal_diagnostics.unsupported "a spread cannot fill fixed parameters of a variadic signature"
           else match Semantic.tuple_positions ~readonly:true actual, Semantic.spread_element ~readonly:true actual with
             | Some positions,_ -> positions
             | None,Some element -> [element]
             | _ -> Proposal_diagnostics.unsupported "generic spread requires an array, a union of arrays, or a tuple of required positions") args) in
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
        | { node = Id name; pos } -> resolve ~at:pos env name
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
                 | _ -> false) (Option.value ~default:[] (flat_atoms declarations t)) with
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
        (* A closure literal at a parameter whose binders the call's expected
           result fixes is built at the parameter read at them, as TypeScript
           infers from the return position first and types the callback's
           body at that contextual return type: `xs.map(n => ({ k: "atom", n
           }))` expected at `Array<Term>` builds the literal at the arm of
           `Term` it fits. A proposal: the instance is inferred from the
           actuals afterwards, and Lean checks it and the closure. *)
        let result_bound p = match contextual with
          | None -> None
          | Some t ->
            let own = List.map (fun (q:Semantic.quantifier) -> q.identity) signature.quantified in
            let solution = List.filter_map (fun (r,t) ->
              if List.mem r own then Some (r,ValueArgument t) else None) (bind signature.result t) in
            if solution = [] then None
            else
              let p = Inference.substitute solution p in
              (* Holes stand in the callback's result alone: its parameters
                 are types. *)
              let holed = mentions_hole p && (match p with
                | Atoms [Shape {calls=[s];fields=[];indexes=[];elements=None}] ->
                  not (List.exists mentions_hole (s.receiver :: s.params @ Option.to_list s.variadic))
                | _ -> false) in
              let hidden = Inference.substitute (List.map (fun r -> r,ValueArgument (Atoms [])) (holes ())) p in
              if Semantic.mentions_rigid hidden || (mentions_hole p && not holed) then None else Some p in
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
        (* An object literal an async body returns is claimed with its exact
           keys: the resolution reads its `then` when it returns, and the
           own-key bound states the literal owns none, which the stable
           descriptor requires (SOURCE-CONTRACTS.md, "Async functions and
           await"). A proposal: Lean checks the bound at the allocation. *)
        (match target.node,args with
         | Id "%AsyncReturn%",[arg] -> mark_exact arg
         | _ -> ());
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
          | Some p,None when (match arg.node with Lambda _ -> true | _ -> false)
                              && result_bound p <> None ->
            expr ?expected:(result_bound p) env arg
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
            match Option.bind p (fun p -> contextual_actual expr signature.quantified env p arg) with
            | Some t -> t
            | None ->
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
        (* A signature stating a precondition on the receiver's elements is
           tried only where the receiver's claimed elements admit a string,
           a number or a boolean: elsewhere an elements atom at those kinds
           holds only of an empty array. *)
        let elements_known = match target.node with
          | Read (o,_) | Index (o,_) ->
            (match Option.bind (latest_claim o.pos) (Semantic.spread_element ~readonly:true) with
             | Some (Atoms atoms) -> List.exists (function
                 | True | False | Num | Str | NumLit _ | StrLit _ -> true
                 | _ -> false) atoms
             | Some (Union arms) -> List.exists (function
                 | Atoms atoms -> List.exists (function
                     | True | False | Num | Str | NumLit _ | StrLit _ -> true
                     | _ -> false) atoms
                 | _ -> true) arms
             | Some _ -> true
             | None -> false)
          | _ -> false in
        let usable = List.filter (fun (s:Semantic.signature) ->
          callable s && (elements_known || s.call_effect.requires = None)) calls in
        let actuals = seeded_actuals usable in
        let proposals = List.filter_map (fun (s:Semantic.signature) ->
          Option.map (fun (substitution,result) -> s,substitution,result)
            (quietly (fun () -> infer_explicit ~receiver:receiver_type ?expected s
              (List.map fst actuals @ List.init (max 0 (List.length s.params - List.length args))
                (fun _ -> Atoms [Undef]))))) usable in
        (* Where some signature is about the receiver's elements, a closure
           literal is matched only at a callback it takes. *)
        let about_elements = List.exists (fun ((s:Semantic.signature),_,_) ->
          s.call_effect.requires <> None || s.call_effect.elements <> None) proposals in
        let matches_actuals ((s:Semantic.signature),substitution,_) =
          let at = Inference.substitute substitution in
          (* An instance a binder's bound excludes is not the call's, as
             TypeScript skips an overload whose inferred type argument fails
             its constraint. *)
          let rec within bound (t:ty) = match t with
            | Union ts -> List.for_all (within bound) ts
            | Meet (t,ts) -> List.exists (within bound) (t :: ts)
            | Rigid r -> (match rigid_bound r with Some b -> within bound b | None -> false)
            | Atoms _ -> plausible_subtype_declared declarations t bound in
          List.for_all (fun (q:Semantic.quantifier) -> match q.bound,List.assoc_opt q.identity substitution with
            | Some (ValueArgument bound),Some (ValueArgument t) -> within (at bound) t
            | _ -> true) s.quantified &&
          List.for_all Fun.id (List.mapi (fun i (arg,(t,_)) ->
            match List.nth_opt s.params i with
            | Some p -> plausible_subtype_declared declarations t (at p)
                || (offer_to arg (at p) <> None && (not about_elements || literal_takes arg (at p)))
            | None -> false) (List.combine args actuals)) in
        (* A signature requiring an actual's member to state an effect is not
           the call's where that member, as the actual's type states it, has a
           signature whose effect it does not cover (`%Dispatch:m%` at a regex
           whose member may change anything). *)
        let member_effects ((s:Semantic.signature),substitution,_) =
          let calls_of (t:ty) = match declared_head declarations [] t with
            | Atoms [Shape {calls;_}] -> calls
            | _ -> [] in
          List.for_all Fun.id (List.mapi (fun i (_,(t,_)) ->
            match List.nth_opt s.params i,declared_head declarations [] t with
            | Some p,Atoms [Shape actual] ->
              (match declared_head declarations [] (Inference.substitute substitution p) with
               | Atoms [Shape wanted] -> List.for_all (fun (w:Semantic.field) ->
                   List.for_all (fun (c:Semantic.signature) ->
                     match List.find_opt (fun (a:Semantic.field) -> a.name=w.name) actual.fields with
                     | Some a ->
                       (* Of an overloaded member, the signatures taking
                          what the wanted one passes are those a call may
                          meet it by (a regex's `[Symbol.replace]` at a
                          string, not its callback overload). *)
                       let covers (d:Semantic.signature) = Semantic.effect_covers d.call_effect c.call_effect in
                       let takes (d:Semantic.signature) = List.length d.params = List.length c.params
                         && List.for_all2 (plausible_subtype_declared declarations) c.params d.params in
                       (match List.filter takes (calls_of a.read) with
                        | [] -> List.for_all covers (calls_of a.read)
                        | relevant -> List.exists covers relevant)
                     | None -> true) (calls_of w.read)) wanted.fields
               | _ -> true)
            | _ -> true) (List.combine args actuals)) in
        let proposals = List.filter member_effects proposals in
        (* Of the matching signatures, those whose parameter states the
           promise a guard closure passed there writes come first, as
           TypeScript resolves `filter`'s guard overload at a type
           predicate. *)
        let states_written ((s:Semantic.signature),_,_) = List.for_all Fun.id (List.mapi (fun i (arg:expr) ->
          match arg.node,param_at s i,value_promise arg with
          | Lambda (_,_,_,_,_,_,Some (stated,_),_),Some (Atoms [Shape {calls=_::_ as calls;_}]),_ ->
            List.for_all (fun (c:Semantic.signature) -> c.call_effect.promise = stated.promise) calls
          | Lambda (_,_,_,_,_,_,Some _,_),_,_ -> false
          (* A guard passed by name, as TypeScript resolves the guard
             overload at a function whose type is a predicate. *)
          | _,Some (Atoms [Shape {calls=_::_ as calls;_}]),Some own ->
            List.for_all (fun (c:Semantic.signature) -> c.call_effect.promise = own.call_effect.promise) calls
          | _,_,Some _ -> false
          | _ -> true) args) in
        let matching = List.filter matches_actuals proposals in
        let matching = List.filter states_written matching @
          List.filter (fun p -> not (states_written p)) matching in
        let receiver_matches ((s:Semantic.signature),substitution,_) =
          let expected = Inference.substitute substitution s.receiver in
          plausible_subtype_with (excludes_undefined_declared declarations) receiver_type expected ||
          plausible_subtype_declared declarations receiver_type expected in
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
      | Atoms [Shape ({calls=(_::_::_ as calls);_} as overloaded)]
          when List.for_all (fun (s:Semantic.signature) -> s.quantified=[]) calls
               && (last_only || not spread) ->
        no_type_arguments ();
        let usable = List.filter callable calls in
        let actuals = shared_actuals usable in
        (* A closure an offer would claim at the parameter matches it, as
           does an actual built at it. *)
        let matching = List.filter (fun (s:Semantic.signature) ->
          List.for_all Fun.id (List.mapi (fun i (arg,(t,built)) -> match param_at s i with
            | Some p -> built = Some p || plausible_subtype_declared declarations t p || offer_to arg p <> None
            | None -> false) (List.combine args actuals))) usable in
        (* A result with required positions forbids a removal from it: it is
           proposed only where nothing shrinks the array (`Source.unshrunk`). *)
        let required (s:Semantic.signature) = match s.result with
          | Atoms [Shape {elements=Some {required=_::_;_};_}] -> true
          | _ -> false in
        let matching = if List.mem site !Source.unshrunk then matching
          else match List.filter (fun s -> not (required s)) matching with
            | [] -> matching
            | kept -> kept in
        (match matching,usable with
         (* The callee is claimed at the signature selected, which the
            overloads' intersection meets: a call's effect is its own. A
            guard's callee keeps its promise signatures, which a condition
            reads. *)
         | s :: _,_ ->
           offer s;
           let promises = match latest_claim target.pos with
             | Some (Atoms [Shape {calls;_}]) ->
               List.exists (fun (c:Semantic.signature) -> not (Semantic.plain_effect c.call_effect)) calls
             | _ -> true in
           if not (method_read target) && not promises then
             publish_instance target.pos (Atoms [Shape {overloaded with calls=[s]}]);
           s.result
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
        unions (List.map (fun (s:Semantic.signature) -> s.result) signatures)
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
      (* A callee of no value, as an optional call's on a receiver a pass
         finds only nullish: the call is never reached, and gives no value.
         A loop's later pass, where the receiver may be present, types it;
         Lean checks the claims of the last. *)
      | Atoms [] when spreads = [] -> List.iter (fun a -> ignore (expr env a)) args; Atoms []
      | _ ->
        let location = match site with
          | Json.Array [Json.Number first;Json.Number last] -> " (call at [" ^ first ^ "," ^ last ^ "))"
          | _ -> "" in
        Proposal_diagnostics.unsupported ("call requires a single arrow the arguments can call" ^ location)))
    | _ -> Json.fail "expression dispatched to the wrong typing family"
end
