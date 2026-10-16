open Semantic
open Environment
open Source
open Type_queries
open Proposal_diagnostics
open Refinement
module type Inputs = sig
  include Expression_support.Inputs
  include Analysis_capabilities.Path_queries
  include Analysis_capabilities.Offer_operations
  include Analysis_capabilities.Evolution
  include Analysis_capabilities.Expression_publication
  include Analysis_capabilities.Instance_publication
end
module Make (S : Inputs) = struct
open S
module Support = Expression_support.Make(S)
open Support
let infer (expr:Analysis_state.expression_infer) _execute_bindings (body:Analysis_state.body_infer) ?expected env (e:Source.expr) =
  let target_contract = Support.target_contract expr in
  let const_type = Support.const_type expr in
  let site = e.pos in
  (* A function's own signature, and what it does with the actuals past its
     parameters: a module function declared in the source by its arity, any
     other value (a parameter, a local, an import) known only by its type. *)
  let own_signature n =
    let own = if not (List.mem_assoc n env) && List.mem n module_names
      then (try module_type n with Json.Error _ -> None)
      else (try Some (resolve env n) with Json.Error _ -> None) in
    match own with
    | Some (Atoms [Shape {calls=[own];fields=[];indexes=[];elements=None}]) -> Some own
    | _ -> None in
  let arity n = if List.mem_assoc n env then None else module_arity n in
  let rec calls t = match t with
    | Meet (t,ts) -> List.concat_map calls (t::ts)
    | t -> List.concat_map (function Shape s -> s.calls | _ -> [])
             (flat_atoms declarations t) in
  (* Whether `x` states a signature binding more parameters than `own`. *)
  let longer (own:Semantic.signature) x = List.exists (fun (c:Semantic.signature) ->
    List.length c.params > List.length own.params
    || (c.variadic <> None && own.variadic = None)) (calls x) in
  (* A module function that discards the actuals past its parameters, read
     where a signature binding more parameters is expected: its slot holds its
     signature extended by a rest of `unknown`, so it is claimed at what is
     expected, and Lean derives that from the slot. *)
  let discarded n = match expected, own_signature n with
    | Some x, Some own when arity n = Some Module_contract.Discards && longer own x -> Some x
    | _ -> None in
  match e.node with
    | Id n when discarded n <> None -> Option.get (discarded n)
    | Id n ->
      Option.iter (fun expected -> Option.iter (fun c -> offer_class c expected)
        (List.assoc_opt n (path_facts ()).Proposal_flow.classes)) expected;
      (* A named closure expected at a signature binding more parameters
         than it does is offered it, wherever it flows: an argument, an annotated binding, a return, a field. *)
      (match expected with
       | Some (Atoms [Shape {calls=[o];fields=[];indexes=[];elements=None}])
         when List.mem_assoc n (path_facts ()).Proposal_flow.closures && List.mem_assoc n env ->
         Option.iter (fun state -> state ()) (closure_offer n o)
       | _ -> ());
      (* A named function value, a module function or a parameter, where a
         signature binding more parameters than it does, or indifferent to
         the receiver it requires, is expected (a closure literal is offered
         such a signature instead). *)
      (match expected with
       | Some x when not (List.mem_assoc n (path_facts ()).Proposal_flow.closures) ->
         (match own_signature n with
          | Some own ->
            if longer own x
            then Option.iter (S.explain site) (Module_contract.longer_refusal (arity n))
            else if own.receiver <> top && List.exists (fun (c:Semantic.signature) -> c.receiver = top) (calls x)
            then S.explain site ("a function whose `this` is typed where a callback indifferent to its receiver is \
              expected: " ^ receiver_reason)
          | _ -> ())
       | _ -> ());
      (* A mutable array, or an instance with a writable field, at one whose
         element or field is wider. *)
      (match expected with
       | Some x ->
         let mutable_rest = function
           | Shape {elements=Some {required=[];optional_elements=[];rest=Some r;readonly=false;presence=_};_} -> Some r
           | _ -> None in
         let actual = flat_atoms declarations (resolve env n) and wanted = flat_atoms declarations x in
         let rests = List.filter_map mutable_rest actual and wanted_rests = List.filter_map mutable_rest wanted in
         if rests <> [] && List.length rests = List.length actual && wanted_rests <> []
            && List.for_all (fun r -> not (List.mem r wanted_rests)
                 && List.exists (fun w -> plausible_subtype r w) wanted_rests) rests
            && not (List.exists (function
                 | Shape {elements=Some {readonly=true;_};_} -> true | _ -> false) wanted) then
           S.explain site ("a mutable array at one of a wider element: " ^ invariance_reason);
         (match resolve env n, x with
          | Atoms [Named (a,xs)], Atoms [Named (b,ys)] when a = b && xs <> ys ->
            (match definition declarations a xs, definition declarations b ys with
             | Atoms [Shape s1], Atoms [Shape s2] ->
               if List.exists (fun (f:Semantic.field) -> f.write <> None && not f.host && List.exists (fun (g:Semantic.field) ->
                   g.name = f.name && g.read <> f.read) s2.fields) s1.fields then
                 S.explain site ("an instance at another whose writable field differs: " ^ invariance_reason)
             | _ -> ()
             | exception Json.Error _ -> ())
          | _ -> ())
       | None -> ());
      (* A value a type test found of a shape, where its type is a type
         parameter or `unknown`. *)
      (match expected, List.assoc_opt n (observations ()).Analysis_capabilities.shape_tests with
       | Some x, Some shape when primitive_shape shape ->
         if rigid_arm x then
           S.explain site ("a `typeof x === \"" ^ shape ^ "\"` test on a value of a type parameter or `unknown`: "
             ^ family_test_reason)
       | _ -> ());
      (* A cell read at its contract where the use asks for less. *)
      (match expected, List.assoc_opt n env with
       | Some x, Some (Storage (contract,current)) when current = contract
           && not (plausible_subtype contract x) ->
         let atoms = flat_atoms declarations contract in
         if List.mem Undef atoms && List.exists (function
             | Shape _ | Exact _ | Named _ | Callable | Ctors _ -> true | _ -> false) atoms
            && plausible_subtype (Semantic.without_nullish contract) x
         then S.explain site ("a `let` holding an object read where it must be assigned: " ^ object_cell_reason)
         else S.explain site ("a cell read at its contract: " ^ forgotten_cell_reason)
       | _ -> ());
      (* An instance of a declaration with generic methods at an instance of
         another, `Promise<A>` at `PromiseLike<B>`: refused by name. Two
         instances of one declaration relate through their methods. *)
      (match expected with
       | Some x ->
         let generic_methods id args =
           match definition declarations id args with
           | Atoms [Shape sh] -> List.exists (fun (f:Semantic.field) -> match f.read with
               | Atoms [Shape {calls;_}] ->
                 List.exists (fun (c:Semantic.signature) -> c.quantified <> []) calls
               | _ -> false) sh.fields
           | _ -> false
           | exception Json.Error _ -> false in
         let apps t = match t with
           | Atoms atoms -> List.filter_map (function Named (id,args) -> Some (id,args) | _ -> None) atoms
           | _ -> [] in
         (match apps (resolve env n), apps x with
          | [a,xs], (_::_ as wanted) when not (List.mem (a,xs) wanted)
              && List.for_all (fun (b,ys) -> b <> a && generic_methods b ys
                   (* Instances that are one type, their arguments unused. *)
                   && (try
                         (* A method's receiver names the instance itself. *)
                         let unreceived = function
                           | Atoms [Shape sh] -> Atoms [Shape {sh with fields=List.map (fun (f:Semantic.field) ->
                               match f.read with
                               | Atoms [Shape m] -> {f with read=Atoms [Shape {m with calls=List.map
                                   (fun (c:Semantic.signature) -> {c with receiver=top}) m.calls}]}
                               | _ -> f) sh.fields}]
                           | t -> t in
                         unreceived (definition declarations b ys) <> unreceived (definition declarations a xs)
                       with Json.Error _ -> true)) wanted
              && generic_methods a xs ->
            S.explain site ("an instance of a declaration with generic methods at an instance of another: "
              ^ generic_instances_reason)
          | _ -> ())
       | None -> ());
      explain_record_at_index site env n expected;
      (* A tuple expected at an iterable other than an array is read as the
         readonly array of its positions, whose prototype's iterator yields
         them: Lean checks the tuple within that view, and the view within
         the iterable. *)
      (match resolve env n, expected with
       | Atoms [Shape {elements=Some s;fields=[];indexes=[];calls=[]}],Some x
         when (s.required <> [] || s.optional_elements <> []) && s.rest = None
              && (match x with Atoms [Shape {elements=Some _;_}] -> false | _ -> true)
              && iterated_hint declarations x <> None ->
         array {required=[];optional_elements=[];
           rest=Some (combine (s.required @ s.optional_elements));readonly=true;presence=(match s.presence with Dense | Readable -> Readable | Sparse -> Sparse)}
       | t,_ -> t)
    | Literal l -> literal_type l
    | Not e -> ignore (expr env e); bool
    | TypeofTest (_,_,e) -> ignore (expr env e); bool
    (* A string literal key is part of the test, not a claim site. *)
    | HasKey ({node=Literal (LString _);_},e) -> ignore (expr env e); bool
    | HasKey (k,e) -> ignore (expr env k); ignore (expr env e); bool
    | InstanceTest (_,e,proto) -> ignore (expr env e); ignore (expr env proto); bool
    (* A comparison is a Boolean; `+` with a string operand is a string;
       other arithmetic is of its operands' numeric family, bigint where the
       left one is all bigints, else number. *)
    | Arith (op,l,r) ->
      let left = expr env l in let right = expr env r in
      if relational op then begin
        (* Two strings compare by code units; two operands among numbers,
           bigints, Booleans, `null` and `undefined` by `ToNumeric`, which runs
           no code. Any other pair may be converted through code. *)
        let all_atoms ok t = match (try declared_head declarations [] t with Json.Error _ -> t) with
          | Atoms atoms -> List.for_all ok atoms
          | Rigid _ | Union _ | Meet _ -> true in
        let numeric = function
          | Num | NumLit _ | Bigint | BigintLit _ | True | False | Nul | Undef -> true
          | _ -> false in
        let stringy = function Str | StrLit _ -> true | _ -> false in
        let primitive = function
          | Shape _ | Exact _ | Ctors _ | Callable | Top -> false
          | _ -> true in
        if not (all_atoms numeric left && all_atoms numeric right
                || all_atoms stringy left && all_atoms stringy right) then
          S.explain e.pos (if all_atoms primitive left && all_atoms primitive right
            then "a relational comparison of operands that may not both be numeric primitives or \
              both strings: " ^ relational_reason
            else "a relational comparison with an operand that may be an object: " ^ relational_object_reason);
        bool
      end else operation_result declarations op left right
    | Comma (a,b) -> ignore (expr env a); expr ?expected env b
    (* The target is read at its storage contract and written back: a local's
       contract, or the field's type. An increment adds one of that family;
       the old value is the contract's, the new one the operation's. *)
    | Update (op,target,rhs,post) ->
      let contract = target_contract env target in
      let right = match rhs with Some r -> expr env r | None -> contract in
      if post then contract else operation_result declarations op contract right
    (* The kept value is the target's, where the test keeps it: present for
       `??=`, `true` for `||=`, `false` for `&&=`; the other arm's is the right
       side's, written at the contract. *)
    | LogicalAssign (op,target,rhs) ->
      let contract = target_contract env target in
      let right = expr ~expected:contract env rhs in
      union (match op with
        | Nullish -> without_nullish contract | OrElse -> Atoms [True] | AndAlso -> Atoms [False]) right
    | NullishAssign (n,name_pos,rhs) ->
      let current = resolve env n in
      publish_expression name_pos current None;
      let contract = match lookup env n with
        | Storage (contract,_) | Local (contract,_) -> contract
        | Value _ -> Proposal_diagnostics.unsupported "assignment to immutable binding" in
      let right = expr ~expected:contract env rhs in
      (match List.assoc_opt n (path_facts ()).Proposal_flow.evolving with
       | Some (key,false) -> evolve key right
       | _ -> ());
      union (without_nullish current) right
    (* `typeof e` names one of eight shapes: a string. *)
    | Unary (Typeof,e) -> ignore (expr env e); Atoms [Str]
    | Unary (_,e) -> numeric_family declarations (expr env e)
    (* The right side is built at the tuple of the local targets' contracts,
       as TypeScript types it from the targets; then each target in turn,
       a field's reference first, takes its position's read, or its default,
       at its storage contract. The value is the right side's. *)
    | ArrayAssign (targets,rest,rhs) ->
      let local (t:expr) = match t.node with
        | Id n -> (match lookup env n with
          | Storage (contract,_) | Local (contract,_) -> Some contract
          | Value _ -> Proposal_diagnostics.unsupported "assignment to immutable binding")
        | _ -> None in
      (* A field's reference is evaluated after the right side: its contract
         is read here quietly, as a hint for the right side's literal, and
         claimed where the reference is evaluated. *)
      let contract t = match local t with
        | Some c -> c
        | None -> Option.value (quietly (fun () -> target_contract env t)) ~default:Semantic.top in
      (* A literal's positions past the rest's index are the rest's: its
         tuple's positions or its array's element. *)
      let width = match rhs.node,rest with
        | ArrayLiteral (es,[]),_ -> List.length es
        | _,Some (i,_,_,_) -> i
        | _,None -> 1 + List.fold_left (fun m (i,_,_) -> max m i) (-1) targets in
      let required = List.init width (fun i -> match List.find_opt (fun (j,_,_) -> j=i) targets,rest with
        | Some (_,n,Some _),_ -> union (contract n) (Atoms [Undef])
        | Some (_,n,None),_ -> contract n
        | None,Some (start,_,n,_) when i >= start ->
          (match declared_head declarations [] (contract n) with
           | Atoms [Shape {elements=Some s;_}] ->
             (match List.nth_opt s.required (i-start) with
              | Some t -> t | None -> Option.value s.rest ~default:Semantic.top)
           | _ -> Semantic.top)
        | None,_ -> Semantic.top) in
      let actual = expr ~expected:(array {required;optional_elements=[];rest=None;readonly=false;presence=Dense}) env rhs in
      let evaluated t = match local t with Some c -> c | None -> target_contract env t in
      List.iter (fun (_,t,d) ->
        let c = evaluated t in Option.iter (fun d -> ignore (expr ~expected:c env d)) d) targets;
      let rest = Option.map (fun (start,span,t,slice) -> (start,span,evaluated t,slice)) rest in
      (* The rest's fresh array is claimed at its local's contract where that
         is an array, which a fresh array meets, else at the positions it
         takes. *)
      Option.iter (fun (start,span,n,slice) ->
        if slice then
          (* A slice: its `%RestFrom:k%`'s fresh array, at the instance of
             the elements from the rest's index on. *)
          let element = slice_element declarations start actual in
          publish_expression span (array {required=[];optional_elements=[];rest=Some element;readonly=false;presence=Readable})
            (Some ["T",ValueArgument element])
        else
        let claim = match Semantic.array_element n,declared_head declarations [] actual with
          | Some _,_ -> n
          | None,Atoms [Shape {elements=Some s;_}] when s.optional_elements=[] && s.rest=None ->
            array {required=List.filteri (fun i _ -> i >= start) s.required;
                   optional_elements=[];rest=None;readonly=false;presence=Dense}
          | _ -> Proposal_diagnostics.unsupported "an array rest needs one tuple of required positions: the rest of an array of unknown length is a slice" in
        publish_expression span claim None) rest;
      actual
    | Equality (op,l,r) ->
      let lt = expr env l and rt = expr env r in
      let undecided t = rigid_arm t || t = top in
      if (op = StrictEqual || op = StrictUnequal) && undecided lt && undecided rt
         && (rigid_arm lt || rigid_arm rt) then
        S.explain site ("strict equality with a value of a type parameter: " ^ equality_reason);
      bool
    | Apply (callee,receiver,list) ->
      (* The list is typed at its own contract; Lean reads each element's
         type from it and checks the call against the target's signature. *)
      let callee = declared_head declarations [] (expr env callee) in
      ignore (expr env receiver);
      Option.iter (fun l -> ignore (expr env l)) list;
      (match callee with
       | Atoms [Shape {calls=[{quantified=[];result;_}];_}] -> result
       | _ -> Proposal_diagnostics.unsupported ".apply requires a single arrow")
    | WithFields (fn,initial,ft,bag) ->
      ignore (expr ~expected:ft env fn); ignore (expr ~expected:bag env initial);
      (match ft,bag with
        | Atoms [Shape f],Atoms [Shape b] when f.fields=[] && f.elements=None && b.calls=[] && b.elements=None ->
          Atoms [Shape {b with calls=f.calls}]
        | _ -> Proposal_diagnostics.unsupported "function field construction requires a callable and a record contract")
    | Bind (callee,receiver,args) ->
      let callee=declared_head declarations [] (expr env callee) in ignore (expr env receiver);
      (* A target of several signatures, `next(...[value]: [] | [TNext])`, is
         bound at the first that takes the prefix: the bound function's claim
         is one signature, which Lean selects among the target's. *)
      let fits (s:Semantic.signature) = s.quantified=[] && s.rest_pack=None && (s.variadic<>None
        || List.length args<=List.length s.params) in
      let callee = match callee with
        | Atoms [Shape ({calls=_::_::_ as calls;_} as shape)] when List.exists fits calls ->
          Atoms [Shape {shape with calls=[List.find fits calls]}]
        | t -> t in
      (match callee with Atoms [Shape {calls=[signature];_}]
          when signature.quantified=[] && (signature.variadic<>None
            || List.length args<=List.length signature.params) ->
        (* The prefix takes the first positions; past a variadic signature's
           fixed ones, each is at its element contract. What is left is the
           bound function's signature, at any receiver. *)
        let rec prefix ps args = match ps,args with
          | rest,[] -> rest
          | p::ps,e::es -> ignore (expr ~expected:p env e); prefix ps es
          | [],e::es -> (match signature.variadic with
              | Some element -> ignore (expr ~expected:element env e); prefix [] es
              | None -> Proposal_diagnostics.unsupported "bind argument prefix exceeds arity") in
        let rest = prefix signature.params args in
        (match signature.variadic with
         | Some element -> variadic_arrow ~call_effect:signature.call_effect rest element signature.result
         | None -> arrow ~call_effect:signature.call_effect rest signature.result)
      | _ -> Proposal_diagnostics.unsupported "bind requires a single arrow and a valid argument prefix")
    | Conditional (c,a,b) -> ignore (expr env c);
      let left = expr ?expected env a in
      let right = expr ?expected env b in union left right
    (* The left operand's values other than null and undefined, a type
       parameter's the meet of it with its bound's, `T ⊓ number` for
       `T extends number | null`, where the bound states them. *)
    | Coalesce (a,b) -> let left=expr env a in let right=expr ?expected env b in
      let present = narrow_rigid (S.rigid_bounds ()) without_nullish left in
      if expected <> None && rigid_arm present then
        S.explain site ("`??` on a value of a type parameter whose bound states no values other than null \
          and undefined: those are the meet `T & {}`, which no clause row states");
      union present right
    (* The body runs where the receiver is present, and reads it so; a
       nullish receiver gives `undefined`. An inner chain's receiver hides
       an outer one's. *)
    | Optional (r,b) -> let receiver=expr env r in
      let present=without_nullish receiver in
      let body=expr ?expected env b in
      if present = receiver then body else union (Atoms [Undef]) body
    (* The left operand's value where it decides, the right's elsewhere; the
       right operand runs where the left answered the other way. *)
    | Logical (conjunction,a,b) -> let left=expr env a in
      let right=expr ?expected env b in
      union (truthy_slice (not conjunction) left) right
    (* The operand is built at its const type, which is the cast's. *)
    | Cast ("const",None,e) ->
      (match const_type env e with
       | Some t -> ignore (expr ~expected:t env e); t
       | None -> Proposal_diagnostics.unsupported "`as const` on an operand other than a literal, an array or object literal, or a name")
    | Cast (kind,annot,e) ->
      (match kind,e.node with
       | "nonNull",Index (_,{node=Id k;_}) when List.mem k (observations ()).Analysis_capabilities.for_in_keys ->
         S.explain site ("a non-null assertion on a read at a for...in key: " ^ for_in_key_reason)
       | _ -> ());
      let actual=expr ?expected:annot env e in
      (match kind,annot with
        | "nonNull",None -> without_nullish actual
        | "satisfies",Some _ -> actual
        | "as",Some target -> target
        | _ -> Proposal_diagnostics.unsupported "cast form")
    (* A closure's statements: the union of what its `return`s give, each
       checked at the closure's result where it has one. *)
    | BlockBody ss ->
      let _,returned = body e.pos expected env ss in
      combine (List.rev returned)
    | _ -> Json.fail "expression dispatched to the wrong typing family"
end
