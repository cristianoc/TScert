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
           literal types do; a name's or a read's declared type does not. *)
        let fresh = match e.node with Id _ | Read _ -> false | _ -> true in
        let t=if widened || (expected = None && not fresh) then inferred
          else Option.value expected ~default:(widen inferred) in
        {name;optional=false;read=t;write=Some t;host=false;receivers=[]}) fs in
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
       | _ when List.mem_assoc (Name proto_key) fs || List.mem e.pos (path_facts ()).Proposal_flow.exact_allocs -> Atoms [Exact fields]
       | Some {indexes=(_::_ as indexes);fields=contract_fields;_}
         when List.exists (fun (i:Semantic.index_signature) -> i.writable <> None) indexes ->
         (* The contract's optional fields it leaves out, which it lacks. *)
         let absent = List.filter (fun (f:Semantic.field) -> f.optional && not f.host &&
           not (List.mem_assoc f.name fs)) contract_fields in
         Atoms [Shape {fields=fields @ absent;indexes;calls=[];elements=None}]
       | Some {indexes=_::_;_} -> Atoms [Exact fields]
       | Some {fields=contract_fields;_}
         when List.exists (fun (f:Semantic.field) -> f.optional) contract_fields -> Atoms [Exact fields]
       | _ -> record fields)
    | Build parts ->
      List.iter (fun (name,(e:expr)) -> if name = None then
        match (match quietly (fun () -> expr env e) with
               | Some t -> (try flat_atoms declarations t with Json.Error _ -> [])
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
      let field_of (name,e) =
        let hint = Option.bind contract (fun s ->
          List.find_opt (fun (f:Semantic.field) -> f.name=Name name) s.fields) in
        let expected = Option.map (fun (f:Semantic.field) -> f.read) hint in
        let inferred = expr ?expected env e in
        let t = Option.value expected ~default:(widen inferred) in
        ({name=Name name;optional=false;read=t;write=Some t;host=false;receivers=[]} : Semantic.field) in
      let group fs = {empty_alternative with afields=fs} in
      let merge alts b = List.concat_map (fun a -> List.map (merge_alternative a) b) alts in
      let alts,fields = List.fold_left (fun (alts,fields) (name,e) -> match name with
        | Some name -> alts,fields @ [field_of (name,e)]
        | None ->
          let alts = match alts with
            | None -> [group fields]
            | Some alts -> if fields = [] then alts else merge alts [group fields] in
          mark_exact e;
          Some (merge alts (source_alternatives declarations [] (expr env e))),[]) (None,[]) parts in
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
      combine (List.map alternative_type alts)
    (* `Object.assign(t, ...sources)`: each source copied over what the
       target and the sources before it give, as a spread is; a literal
       source is claimed with its exact keys, which says it owns no
       `__proto__`, a key the copy would set through a setter. *)
    | ObjectAssign (target,sources) ->
      mark_exact target;
      let merge alts b = List.concat_map (fun a -> List.map (merge_alternative a) b) alts in
      let alts = List.fold_left (fun alts (s:expr) ->
        mark_exact s;
        merge alts (source_alternatives declarations [] (expr env s)))
        (source_alternatives ~target:true declarations [] (expr env target)) sources in
      combine (List.map alternative_type alts)
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
      let elements t = match (try declared_head declarations [] t with Json.Error _ -> t) with
        | Atoms [Shape {elements=Some s;_}] ->
          let held = combine (s.required @ s.optional_elements @ Option.to_list s.rest) in
          Some (if s.presence = Sparse then union held (Atoms [Undef]) else held)
        | t -> iterated_hint declarations t in
      let types = List.mapi (fun i e ->
        let expected = Option.bind contract (fun s -> match List.nth_opt (s.required @ s.optional_elements) i with
          | Some t -> Some t | None -> s.rest) in
        if List.mem i spreads then
          let expected = Option.map (fun t ->
            array {required=[];optional_elements=[];rest=Some t;readonly=true;presence=Readable}) expected in
          match elements (expr ?expected env e) with
          | Some t -> t
          | None -> Proposal_diagnostics.unsupported "an array literal spread needs an array operand"
        else expr ?expected env e) es in
      (match contract with
        | Some s -> array s
        | None -> array {required=[];optional_elements=[];rest=Some (widen (combine types));readonly=false;presence=Readable})
    (* A field a guard found holding less than its type is read at that. *)
    | _ -> Json.fail "expression dispatched to the wrong typing family"
end
