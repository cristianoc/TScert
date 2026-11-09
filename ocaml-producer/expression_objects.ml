(* object_spread.ml computes candidate alternatives for object copying, preserving field presence and key bounds. *)
open Semantic
open Source
open Type_queries
open Proposal_diagnostics
open Object_spread
module type Inputs = sig
  include Expression_support.Inputs
  include Analysis_capabilities.Path_queries
  include Analysis_capabilities.Offer_operations
  include Analysis_capabilities.Exact_allocations
  include Analysis_capabilities.Expression_publication
end
module Make (S : Inputs) = struct
open S
module Support = Expression_support.Make(S)
let infer (expr:Analysis_state.expression_infer) _execute_bindings (_body:Analysis_state.body_infer) ?expected env (e:Source.expr) =
  let site = e.pos in
  match e.node with
    | Alloc fs ->
      let contract = match Option.bind expected (object_hint declarations []) with
        | Some shape -> Some shape
        | None -> Option.bind expected (fun t -> discriminated_record declarations t fs) in
      let fields = List.map (fun (name,e) ->
        let hint = Option.bind contract (fun s -> List.find_opt (fun (f:Semantic.field) -> f.name=name) s.fields) in
        (* A key the contract names is built at its member's type; any other
           at the index. *)
        let expected = match hint,contract with
          (* An instance's prototype link is built at what it holds: the
             contract's view of the chain (an `Error`-derived instance's
             message) states less than its methods, which the instance's
             own-key bound sends reads on to. *)
          | _ when name = Name proto_key -> None
          | Some (f:Semantic.field),_ -> Some f.read
          | None,Some shape -> Option.map (fun (i:Semantic.index_signature) -> i.value)
              (index_for shape name)
          | None,_ -> None in
        (match hint,e.node with
         | Some f,Literal LUndefined when f.optional && not (Semantic.admits_undefined f.read) ->
           S.explain site ("an optional field given `undefined`: " ^ exact_optional_reason)
         | _ -> ());
        let inferred=expr ?expected env e in
        (* A method's closure offered further signatures is held at its own
           claim: a construct signature offering them reads them there. *)
        let widened = match e.node with
          | Id m -> (match List.assoc_opt m (path_facts ()).Proposal_flow.closures with
            | Some (pos,_) -> List.mem_assoc pos offered | None -> false)
          | _ -> false in
        (* A literal's type widens in a mutable field, as TypeScript's fresh
           literal types do; a name's or a read's declared type does not,
           nor does a const assertion's, whose type is not fresh. *)
        let fresh = match e.node with Id _ | Read _ | Cast ("const",None,_) -> false | _ -> true in
        let t=if widened || name = Name proto_key || (expected = None && not fresh) then inferred
          else Option.value expected ~default:(widen inferred) in
        (* A field a program record's contract states stable is allocated at
           its initial value alone, a view of the literal (POSITIVE-TYPES.md,
           "Records"). A host family's marked shape states its stable keys of
           objects no allocation of the program makes. *)
        let program_record = match contract with
          | Some s -> not (List.exists (fun (f:Semantic.field) -> f.name = Semantic.host_key) s.fields)
          | None -> false in
        let stable = match hint with
          | Some (f:Semantic.field) -> program_record && f.stable && f.write = None
          | None -> false in
        {name;optional=false;read=t;write=(if stable then None else Some t);host=false;receivers=[];stable;generic=false}) fs in
      (* Where the contract is a dictionary, or has optional fields, the
         literal is claimed with its exact keys: that own-key bound is what
         lets it meet an index, or an optional field it leaves out. A class
         instance, which holds its prototype, is claimed with its exact keys
         too: the bound is what says a method is not its own, so a read of it
         continues at the prototype. A writable index is never met through an
         own-key bound, since code holding it may add keys: a literal meant
         for one is allocated at the dictionary itself, each field at its
         index's type. *)
      (match contract with
       | _ when List.mem_assoc (Name proto_key) fs -> Atoms [Exact fields]
       | Some {indexes=(_::_ as indexes);fields=contract_fields;_}
         when List.exists (fun (i:Semantic.index_signature) -> i.writable <> None) indexes ->
         (* The contract's optional fields it leaves out, which it lacks. *)
         let absent = List.filter (fun (f:Semantic.field) -> f.optional && not f.host &&
           not (List.mem_assoc f.name fs)) contract_fields in
         Atoms [Shape {fields=fields @ absent;indexes;calls=[];elements=None}]
       | _ when List.mem e.pos (path_facts ()).Proposal_flow.exact_allocs -> Atoms [Exact fields]
       | Some {indexes=_::_;_} -> Atoms [Exact fields]
       | Some {fields=contract_fields;_}
         when List.exists (fun (f:Semantic.field) -> f.optional) contract_fields -> Atoms [Exact fields]
       (* Expected at a union of records no field selects one arm of, the
          literal leaving out an optional field of an arm is claimed with its
          exact keys too: that bound is what lets it meet that arm. *)
       | None when (match expected with
           | Some t ->
             List.exists (fun (s:shape) -> List.exists (fun (f:Semantic.field) ->
                 f.optional && not f.host && not (List.mem_assoc f.name fs)) s.fields)
               (try record_arms declarations [] t with Json.Error _ -> [])
           | None -> false) -> Atoms [Exact fields]
       | _ -> record fields)
    | Build parts ->
      List.iter (fun (name,(e:expr)) -> if name = None then
        match (match quietly (fun () -> expr env e) with
               | Some t -> (try Option.value ~default:[] (flat_atoms declarations t) with Json.Error _ -> [])
               | None -> []) with
        | atoms when List.exists (function Shape {indexes=_::_;_} -> true | _ -> false) atoms ->
          S.explain site ("a spread of a dictionary: " ^ dictionary_spread_reason)
        | atoms when List.exists (function
            | Shape {fields;_} | Exact fields ->
              List.exists (fun (f:Semantic.field) -> not (string_key f) && not f.host) fields
            | _ -> false) atoms ->
          S.explain site ("a spread of an object with a symbol-keyed property: " ^ symbol_copy_reason)
        | _ -> ()) parts;
      let contract = Option.bind expected (object_hint declarations []) in
      (* A field is built at the type the contract names for it, else at its
         own, widened, as a literal's field is. *)
      (* Expected at a union of records, a field is built at the type every
         arm stating it gives it, where they agree, as TypeScript types it
         from the contextual union. *)
      let arms = match expected,contract with
        | Some t,None -> (try record_arms declarations [] t with Json.Error _ -> [])
        | _ -> [] in
      (* The arms are those the written literal-valued fields admit, as
         TypeScript discriminates a contextual union by a literal's
         properties ([discriminated_record]): `{ k: "alloc", ...s }` is
         built at the arms whose `k` admits `"alloc"`, so its `k` holds that
         literal type. A construction hint only: Lean checks the literal's
         claim against the expected type. *)
      let arms = match List.filter (fun (s:shape) ->
          List.for_all (fun (name,(e:expr)) -> match name,e.node with
            | Some name,Literal _ ->
              (match List.find_opt (fun (f:Semantic.field) -> f.name = Name name && not f.host) s.fields with
               | Some f -> literal_admitted declarations e f.read
               | None -> index_for s (Name name) <> None)
            | _ -> true) parts) arms with
        | [] -> arms
        | admitted -> admitted in
      let field_of (name,e) =
        let hint = Option.bind contract (fun s ->
          List.find_opt (fun (f:Semantic.field) -> f.name=Name name) s.fields) in
        (* The prototype link at what it holds, as in an allocation. *)
        let expected = if name = proto_key then None else match Option.map (fun (f:Semantic.field) -> f.read) hint with
          | Some t -> Some t
          | None ->
            (match List.sort_uniq compare (List.filter_map (fun (s:shape) ->
                Option.map (fun (f:Semantic.field) -> f.read)
                  (List.find_opt (fun (f:Semantic.field) -> f.name=Name name) s.fields)) arms) with
             | [t] -> Some t
             | _ -> None) in
        let inferred = expr ?expected env e in
        let t = match e.node with
          | _ when name = proto_key -> inferred
          | Cast ("const",None,_) when expected = None -> inferred
          | _ -> Option.value expected ~default:(widen inferred) in
        ({name=Name name;optional=false;read=t;write=Some t;host=false;receivers=[];stable=false;generic=false} : Semantic.field) in
      let group fs = {empty_alternative with afields=fs} in
      let merge alts b = List.concat_map (fun a -> List.map (merge_alternative a) b) alts in
      (* A spread operand written as a record literal, or a conditional
         between record literals (`...(c ? { f: [a, b] } : {})`), is built at
         the fields the contract, or every admitted arm, gives a type, each
         optional, as TypeScript types the operand from the contextual type:
         a tuple field there is a tuple. A construction hint only: Lean
         checks the copy against the expected type. *)
      let rec literal (e:expr) = match e.node with
        | Alloc _ -> true
        | Conditional (_,a,b) -> literal a && literal b
        | _ -> false in
      let spread_expected =
        let shapes = match contract with Some s -> [s] | None -> arms in
        let names = List.sort_uniq compare (List.concat_map (fun (s:shape) ->
          List.filter_map (fun (f:Semantic.field) -> if f.host then None else Some f.name) s.fields) shapes) in
        let field name = match List.sort_uniq compare (List.filter_map (fun (s:shape) ->
            Option.map (fun (f:Semantic.field) -> f.read)
              (List.find_opt (fun (f:Semantic.field) -> f.name = name) s.fields)) shapes) with
          | [t] when name <> Name proto_key ->
            Some ({name;optional=true;read=t;write=Some t;host=false;receivers=[];stable=false;generic=false} : Semantic.field)
          | _ -> None in
        match List.filter_map field names with
        | [] -> None
        | fields -> Some (Atoms [Shape {fields;indexes=[];calls=[];elements=None}]) in
      let operand (e:expr) = match spread_expected with
        | Some expected when literal e -> expr ~expected env e
        | _ -> expr env e in
      let alts,fields = List.fold_left (fun (alts,fields) (name,e) -> match name with
        | Some name -> alts,fields @ [field_of (name,e)]
        | None ->
          let alts = match alts with
            | None -> [group fields]
            | Some alts -> if fields = [] then alts else merge alts [group fields] in
          mark_exact e;
          Some (merge alts (source_alternatives ~bound:S.rigid_bound ~site:e.pos declarations [] (operand e))),[]) (None,[]) parts in
      let alts = match alts with
        | None -> [group fields]
        | Some alts -> if fields = [] then alts else merge alts [group fields] in
      (* Expected at a union of records, an alternative whose keys are one
         arm's has each written field at that arm's type: the last merge
         allocates the copy per pair of its operands' clauses, each field at
         the type of the record that pair gives, so each arm is met with its
         own, as TypeScript types the literal per arm of the contextual
         union. An alternative whose keys several arms have, typing a written
         field apart, is refused by name. *)
      let alts = match expected,contract with
        | Some t,None when List.exists (fun (n,_) -> n = None) parts ->
          let arms = record_arms declarations [] t in
          let names fs = List.sort compare (List.map (fun (f:Semantic.field) -> f.name) fs) in
          let written = List.filter_map (fun (n,_) -> Option.map (fun n -> Name n) n) parts in
          let arms_of (a:alternative) = List.filter (fun (s:shape) -> s.indexes = [] && names s.fields = names a.afields
            && List.for_all (fun (f:Semantic.field) -> not f.optional) s.fields) arms in
          let alts = List.map (fun (a:alternative) -> match arms_of a with
            | [arm] -> {a with afields=List.map (fun (f:Semantic.field) ->
                match List.find_opt (fun (g:Semantic.field) -> g.name = f.name) arm.fields with
                | Some g when List.mem f.name written -> {f with read=g.read; write=Some g.read}
                | _ -> f) a.afields}
            | _ -> a) alts in
          let typed (s:shape) k = List.find_map (fun (g:Semantic.field) ->
            if g.name = k then Some g.read else None) s.fields in
          if List.exists (fun (a:alternative) -> match arms_of a with
              | first :: (_ :: _ as others) -> List.exists (fun k ->
                  List.exists (fun s -> typed s k <> typed first k) others) written
              | _ -> false) alts
          then S.explain site ("a spread with a written field that the arms of the expected union type \
            differently: " ^ copy_field_reason);
          alts
        | _ -> alts in
      unions (List.map alternative_type alts)
    (* `Object.assign(t, ...sources)`: each source copied over what the
       target and the sources before it give, as a spread is; a literal
       source is claimed with its exact keys, which says it owns no
       `__proto__`, a key the copy would set through a setter. *)
    | ObjectAssign (target,sources) ->
      mark_exact target;
      let merge alts b = List.concat_map (fun a -> List.map (merge_alternative a) b) alts in
      let alts = List.fold_left (fun alts (s:expr) ->
        mark_exact s;
        merge alts (source_alternatives ~bound:S.rigid_bound ~site:s.pos declarations [] (expr env s)))
        (source_alternatives ~target:true ~bound:S.rigid_bound ~site:target.pos declarations [] (expr env target)) sources in
      unions (List.map alternative_type alts)
    | ArrayLiteral (es,spreads) ->
      (* One array arm of the expected type is the literal's contract: an
         optional array parameter, `readonly T[] | undefined`, is its array;
         a declaration's, such as a tuple alias at arguments, its equation's.
         A spread stands for its operand's elements: their union is what it
         adds, and the expected element type is what its operand's array
         holds. *)
      let arrays = match expected with
        | Some (Atoms atoms) -> List.concat_map (fun atom -> match atom with
          | Shape {elements=Some s;_} -> [s]
          | Named _ ->
            (match (try Some (declared_head declarations [] (Atoms [atom])) with Json.Error _ -> None) with
             | Some (Atoms heads) -> List.filter_map (function Shape {elements=Some s;_} -> Some s | _ -> None) heads
             | _ -> [])
          | _ -> []) atoms
        | _ -> [] in
      let contract = match expected,arrays with
        | _,[s] -> Some s
        | _,_::_::_ when spreads = [] && discriminated_array declarations arrays es <> None ->
          discriminated_array declarations arrays es
        | Some expected,_ ->
          Option.map (fun t -> {required=[];optional_elements=[];rest=Some t;readonly=true;presence=Readable})
            (iterated_hint declarations expected)
        | None,_ -> None in
      let rec elements t = match (try declared_head declarations [] t with Json.Error _ -> t) with
        | Atoms [Shape {elements=Some s;_}] ->
          let held = unions (s.required @ s.optional_elements @ Option.to_list s.rest) in
          Some (if s.presence = Sparse then union held (Atoms [Undef]) else held)
        (* A union of arrays, `xs ?? []`: the elements of each. *)
        | Union (_ :: _ :: _ as parts) -> elements_of parts
        | Atoms (_ :: _ :: _ as atoms) -> elements_of (List.map (fun a -> Atoms [a]) atoms)
        | t -> iterated_hint declarations t
      and elements_of parts =
        let each = List.map elements parts in
        if List.for_all Option.is_some each then Some (unions (List.filter_map Fun.id each)) else None in
      (* A position holding a hole (`contextual_actual`) is its element's own
         type: the element is built at no type there. *)
      let hole = function Rigid r -> List.mem r (holes ()) | _ -> false in
      let types = List.mapi (fun i e ->
        let expected = Option.bind contract (fun s -> match List.nth_opt (s.required @ s.optional_elements) i with
          | Some t -> Some t | None -> s.rest) in
        let expected = match expected with Some t when hole t -> None | _ -> expected in
        if List.mem i spreads then
          let expected = Option.map (fun t ->
            array {required=[];optional_elements=[];rest=Some t;readonly=true;presence=Readable}) expected in
          let actual = expr ?expected env e in
          (* Keep an operand's own claim where its elements already fit.
             Only arrays can acquire a readonly array view; an iterable
             keeps its iterator contract. Lean checks every proposed view,
             including the operand's presence mode. *)
          let actual = match expected,Option.bind expected (array_element ~readonly:true),
              (try spread_element ~readonly:true (declared_head declarations [] actual)
               with Json.Error _ -> None) with
            | Some target,Some element,Some held when not (Support.mentions_hole target) &&
                not (plausible_subtype held element) ->
              restate_expression e.pos target;
              target
            | _ -> actual in
          match elements actual with
          | Some t -> t
          | None -> Proposal_diagnostics.unsupported "an array literal spread needs an array operand"
        else expr ?expected env e) es in
      (match contract with
        | Some s when Support.mentions_hole (array s) && spreads = [] ->
          (* Each position mentioning a hole is its element's type, widened
             as TypeScript widens an unconstrained binder's candidate. *)
          let fixed = List.length (s.required @ s.optional_elements) in
          let at i q = if Support.mentions_hole q then widen (List.nth types i) else q in
          let rest = List.filteri (fun i _ -> i >= fixed) types in
          array {s with required=List.mapi at s.required;
            optional_elements=List.mapi (fun i q -> at (i + List.length s.required) q) s.optional_elements;
            rest=Option.map (fun q -> if Support.mentions_hole q then widen (unions rest) else q) s.rest}
        | Some s -> array s
        | None -> array {required=[];optional_elements=[];rest=Some (absorb declarations (widen (unions types)));
            readonly=false;presence=Readable})
    (* A field a guard found holding less than its type is read at that. *)
    | _ -> Json.fail "expression dispatched to the wrong typing family"
end
