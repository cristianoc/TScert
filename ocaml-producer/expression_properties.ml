open Semantic
open Environment
open Source
open Type_queries
open Proposal_diagnostics
module type Inputs = sig
  include Expression_support.Inputs
  include Analysis_capabilities.Path_queries
  include Analysis_capabilities.Evolution
  include Analysis_capabilities.Claim_operations
  include Analysis_capabilities.Instance_publication
end
module Make (S : Inputs) = struct
open S
module Support = Expression_support.Make(S)
open Support
let infer (expr:Analysis_state.expression_infer) _execute_bindings (_body:Analysis_state.body_infer) ?expected env (e:Source.expr) =
  let site = e.pos in
  match e.node with
    | Read (({node=Id name;_} as o),Name field) when List.mem_assoc (field_key name field) env ->
      let known = binding_type (List.assoc (field_key name field) env) in
      ignore (expr env o); known
    | Read ({node=Id name;_} as e,n) when List.mem name (observations ()).Analysis_capabilities.unknown_instance_tests ->
      (match expr env e with
       | Atoms xs as t when List.mem Top xs ->
         (try S.field_type declarations [] t n with Json.Error _ -> Proposal_diagnostics.unsupported unknown_instance_reason)
       | t -> S.field_type declarations [] t n)
    (* A `let` holding a union of objects is not narrowed by a test of its
       object: what a cell is known to hold is a union of primitives
       (`holding`), and an object's fields may change through an alias. A
       member only some arms have is refused by that reason. *)
    | Read (({node=Id name;_} as e),n)
      when (match List.assoc_opt name env with Some (Storage _) -> true | _ -> false) ->
      let t = expr env e in
      (try S.field_type declarations [] t n with Json.Error m
        when String.length m >= 27 && String.sub m 0 27 = "unsupported: missing field " ->
        Proposal_diagnostics.unsupported ("a read of " ^ key_text n ^ " on a `let` holding a union of objects, some without it: \
          a test does not narrow a cell holding an object, whose known contents are primitive values")
        | Json.Error m when m = "unsupported: field read on non-object" ->
          Proposal_diagnostics.unsupported ("a cell read at its contract: a read of " ^ key_text n ^ " on a `let` or an assigned \
            parameter holding a primitive beside an object, which a test does not narrow: what a cell is known \
            to hold is primitive values or merely no `undefined`"))
    (* A static field read off a generic class value: its bag names none
       of the class's binders, so the value is read at an instance, each
       binder at its bound. *)
    | Read (({node=Id name;_} as o),n) when not (is_local name) &&
        (match module_type name with Some (Atoms [Ctors ([s],_::_)]) -> s.quantified <> [] | _ -> false) ->
      (match module_type name with
       | Some (Atoms [Ctors ([s],statics)]) ->
         ignore (expr env o);
         let substitution = List.map (fun (q:quantifier) -> q.identity,
           (match q.bound with Some b -> b | None -> ValueArgument Semantic.top)) s.quantified in
         instance_of o substitution;
         publish_substitution site (List.map (fun ((r:rigid),t) -> r.spelling,t) substitution);
         S.field_type declarations [] (Atoms [Ctors ([],statics)]) n
       | _ -> Proposal_diagnostics.unsupported "a generic class value")
    | Read (e,n) ->
      let receiver = expr env e in
      if not (List.mem site (observations ()).Analysis_capabilities.method_callees) && method_member declarations receiver n then
        S.explain site ("a method '" ^ key_text n ^ "' read off its object is not a function value: " ^ extraction_reason);
      (match expected with
       | Some x when n = Name "length"
           && List.exists (function
               | Shape {elements=Some {rest=None;readonly=false;_};_} -> true
               | _ -> false) (flat_atoms declarations receiver)
           && (match flat_atoms declarations x with
               | [] -> false
               | wanted -> List.for_all (function NumLit _ -> true | _ -> false) wanted) ->
         S.explain site ("the `length` of a mutable tuple read at its arity: " ^ mutable_tuple_length_reason)
       | _ -> ());
      (
         (try S.field_type declarations [] receiver n with Json.Error m
           when String.length m >= 27 && String.sub m 0 27 = "unsupported: missing field "
                && (match receiver with
                    | Atoms atoms -> List.exists (function Shape {elements=Some _;_} -> true | _ -> false) atoms
                    | _ -> false) ->
           (* `Array.isArray` keeps a record arm on both outcomes: a value of
              the record's type may be an array carrying its keys. *)
           Proposal_diagnostics.unsupported ("a read of " ^ key_text n ^ " on a union of an array and a record that does not state it: \
             a test that the value is an array keeps the record, a value of which may be an array carrying its keys")
           (* A field holding an object or `null` (`undefined`), which a
              guard found an object: what a field is known to hold is a union
              of primitives, and an object's contents may change through an
              alias, so the guard leaves it at its type. *)
           | Json.Error m when m = "unsupported: field read on non-object"
               && (match e.node with Read ({node=Id _;_},_) -> true | _ -> false) ->
             Proposal_diagnostics.unsupported ("a field read at its contract: a read of " ^ key_text n ^ " through a field holding \
               an object beside null or undefined, which a test does not narrow: what a field is known to hold \
               is a union of primitive values (DESIGN.md, \"Current-content assertions\")")))
    | Index (e,key) -> let receiver=expr env e in let key=expr env key in
      S.index_type declarations [] receiver key
    (* The right side runs after the receiver and the key: it sees what they
       assigned. *)
    | IndexWrite (receiver,key,rhs) ->
      Option.iter (fun k -> Option.iter (evolve k) (quietly (fun () -> expr env rhs))) (evolving_array receiver);
      let t = expr env receiver in
      let key_type = expr env key in
      (match key_type with
       | Atoms [StrLit k] -> dictionary_growth site t (Name k)
       | Atoms [NumLit bits] -> Option.iter (fun k -> dictionary_growth site t (Name k)) (number_key bits)
       | _ -> ());
      (* A key of one of several singletons adds the one it holds, each at the
         contract a named write would add it at. *)
      let names = match key_type with
        | Atoms [StrLit k] -> [Name k]
        | _ -> literal_keys declarations key_type in
      let value = expr env rhs in
      (match List.find_opt (adds env receiver t) names with
       | Some name -> added_contract declarations t name rhs value
       | None -> value)
    | Write (receiver,field,rhs) ->
      let t = expr env receiver in
      dictionary_growth site t field;
      let value = expr env rhs in
      if adds env receiver t field then
        (match expected with Some c -> c | None -> added_contract declarations t field rhs value)
      else value
    | Assign (n,rhs) ->
      if not (List.mem_assoc n env) && List.mem n module_names then
        Proposal_diagnostics.unsupported ("assignment to module function " ^ n);
      (match lookup env n with
      | Storage (contract,_) | Local (contract,_) ->
        let t = expr ~expected:contract env rhs in
        (* A value that reads the binding is what it may be for anything the
           binding may hold: its contract. *)
        let written () = if reads n rhs
          then (match quietly (fun () -> expr (widen_locals ~only:(( = ) n) (forget env)) rhs) with None -> Some t | s -> s)
          else Some t in
        (match List.assoc_opt n (path_facts ()).Proposal_flow.evolving with
         | Some (key,false) -> Option.iter (evolve key) (written ())
         | Some (key,true) -> Option.iter (evolve key) (Option.bind (written ()) (fun t -> Semantic.array_element t))
         | None -> ());
        t
      | Value _ -> Proposal_diagnostics.unsupported "assignment to immutable binding")
    | _ -> Json.fail "expression dispatched to the wrong typing family"
end
