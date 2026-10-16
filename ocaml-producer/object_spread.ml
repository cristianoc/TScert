open Semantic
open Type_queries


(* An object literal with spreads, as a merge reads it: each alternative of
   what is built so far is its fields and whether its own keys are exactly
   theirs; a source's alternative may also state an index, the type of every
   own string key it does not name, and a symbol index, the type of every own
   symbol-keyed property, which JavaScript's copy takes where it is
   enumerable. *)
type alternative = { afields : Semantic.field list; exact : bool; index : ty option; symbols : ty option;
  numeric : ty option }

(* No fields, and exactly them. *)
let empty_alternative = { afields=[]; exact=true; index=None; symbols=None; numeric=None }

(* A method member is host-relative: its object may hold it on its
   prototype, which a spread does not copy. *)
let method_field (f:Semantic.field) = f.host

(* A key some number spells. *)
let numeric_name = function Name s -> canonical_numeric s | Key _ -> false

(* The alternatives a spread's operand gives: nothing from a primitive other
   than a string, a record's fields otherwise, a class value's static fields,
   and no key a string's copy gives. *)
let string_key (f:Semantic.field) = match f.name with Name _ -> true | Key _ -> false
let rec source_alternatives ?(target=false) declarations seen t = match t with
  | Atoms atoms -> List.concat_map (function
      | Nul | Undef | True | False | Num | NumLit _ | Bigint | BigintLit _ | Symbol ->
        [empty_alternative]
      (* A copy takes no symbol-keyed property, a private slot's included
         (DESIGN.md, "Object literals"). *)
      | Exact fs -> [{afields=List.filter (fun (f:Semantic.field) -> f.name <> Name proto_key && string_key f) fs;
                      exact=true;index=None;symbols=None;numeric=None}]
      | Shape {fields;indexes;calls=[];elements=None} ->
        (* The string index states every own string key's type; a number
           index states only the canonical numeric ones', so a key it covers
           is left unstated, as an open record's is. *)
        [{afields=List.filter (fun (f:Semantic.field) ->
            not (method_field f) && f.name <> Name proto_key && string_key f) fields;exact=false;
          index=Option.map (fun (i:index_signature) -> i.value)
            (List.find_opt (fun (i:index_signature) -> i.keys=Strings) indexes);
          symbols=Option.map (fun (i:index_signature) -> i.value)
            (List.find_opt (fun (i:index_signature) -> i.keys=Symbols) indexes);numeric=None}]
      | Named (id,args) ->
        if List.mem id seen then Proposal_diagnostics.unsupported "unguarded spread cycle";
        source_alternatives ~target declarations (id::seen) (definition declarations id args)
      (* A string's own enumerable properties are its code units at its
         index keys, which no record states, and a `Function`'s whatever was
         assigned to it: the copy's type states none of their keys. *)
      | Str | StrLit _ | Callable -> [{empty_alternative with exact=false}]
      (* A class value's are its static fields, of which its type states its
         own, and no bound: it may own any other. *)
      | Ctors (_,statics) ->
        [{empty_alternative with afields=List.filter (fun (f:Semantic.field) ->
            not (method_field f) && f.name <> Name proto_key && string_key f) statics;exact=false}]
      (* An array's own enumerable properties are its elements, at its index
         keys, and whatever keys it carries, which its type does not state;
         at a canonical numeric key, its own field holds an element's type. *)
      | Shape {elements=Some _;_} when target -> Proposal_diagnostics.unsupported "a copy onto an array: \
          the copy is a new object, which holds no array store"
      | Shape {elements=Some s;_} ->
        [{empty_alternative with exact=false;
          numeric=Some (combine (s.required @ s.optional_elements @ Option.to_list s.rest))}]
      (* A function's own enumerable properties are whatever was assigned to
         it: its type states its fields, and no other key. *)
      | Shape {fields;indexes=[];calls=_::_;elements=None} ->
        [{afields=List.filter (fun (f:Semantic.field) ->
            not (method_field f) && f.name <> Name proto_key && string_key f) fields;exact=false;index=None;
          symbols=None;numeric=None}]
      | Shape _ -> Proposal_diagnostics.unsupported "a spread copies the own enumerable properties of a plain object; \
          a function with an index signature owns what its type does not state"
      | _ -> Proposal_diagnostics.unsupported "a spread copies the own enumerable properties of a plain object; one of a string, an array, a function or a class value is outside the fragment") atoms
  | Union ts -> List.concat_map (source_alternatives ~target declarations seen) ts
  | Meet _ | Rigid _ -> Proposal_diagnostics.unsupported "a spread of an intersection or a type parameter is outside the fragment"

(* A source's properties defined over an alternative's: a key the source
   surely has takes its type; one the alternative has keeps its own where the
   source never has it, or with the source's optional or index type where it
   may; a key only the source may have is optional where the alternative's
   keys are exact. A key either side may hold at an unknown type is not
   stated. *)
let merge_alternative (a:alternative) (b:alternative) : alternative =
  let find fs k = List.find_opt (fun (f:Semantic.field) -> f.name = k) fs in
  let index_at (x:alternative) k = match k with Name _ -> x.index | Key _ -> x.symbols in
  let names = List.fold_left (fun ns (f:Semantic.field) ->
    if List.mem f.name ns then ns else ns @ [f.name]) [] (a.afields @ b.afields) in
  let field name optional t = ({name;optional;read=t;write=Some t;host=false;receivers=[]} : Semantic.field) in
  let fields = List.filter_map (fun k ->
    match find b.afields k with
    | Some f when not f.optional -> Some (field k false f.read)
    | bf ->
      let b_maybe = match bf,index_at b k with
        | Some f,_ -> Some f.read
        | None,Some t -> Some t
        | None,None -> None in
      let b_never = bf = None && b.exact in
      match find a.afields k with
      | Some f when not f.optional ->
        if b_never then Some (field k false f.read)
        else Option.map (fun t -> field k false (union f.read t)) b_maybe
      | Some f ->
        if b_never then Some (field k true f.read)
        else Option.map (fun t -> field k true (union f.read t)) b_maybe
      (* A key the alternative may hold at its index: a dictionary owns no
         prototype, so the key is optional at either side's type. *)
      | None -> (match index_at a k with
        | Some ta -> Option.map (fun t -> field k true (union ta t)) b_maybe
        | None -> if a.exact then Option.map (field k true) b_maybe else None)) names in
  (* Where a side states an index and each side says what it gives under
     every key of its class, by an index or by its exact keys, the result
     states the index, at what either side and the fields of that class hold,
     and so does every such field: Lean's merge of a dictionary. The string
     and the symbol keys are apart, each index at its own type. *)
  let resolve get keyed =
    match get a,get b with
    | (Some _,_ | _,Some _) when (get a <> None || a.exact) && (get b <> None || b.exact) ->
      Some (List.fold_left union (Atoms [])
        (Option.to_list (get a) @ Option.to_list (get b)
         @ List.map (fun (f:Semantic.field) -> f.read) (List.filter keyed fields)))
    | _ -> None in
  let index = resolve (fun x -> x.index) (fun f -> string_key f) in
  let symbols = resolve (fun x -> x.symbols) (fun f -> not (string_key f)) in
  let numeric = match index with
    | Some _ -> None
    | None -> resolve (fun x -> x.numeric) (fun f -> numeric_name f.name) in
  { afields=List.map (fun (f:Semantic.field) -> match f.name,index,symbols with
      | Name _,Some v,_ | Key _,_,Some v -> {f with read=v; write=Some v}
      | _ -> f) fields;
    exact=a.exact && b.exact; index; symbols; numeric }

let alternative_type (a:alternative) =
  let index keys = Option.map (fun v : index_signature -> {keys;value=v;writable=Some v}) in
  match Option.to_list (index Strings a.index) @ Option.to_list (index Numeric a.numeric)
        @ Option.to_list (index Symbols a.symbols) with
  | _::_ as indexes -> Atoms [Shape {fields=a.afields;indexes;calls=[];elements=None}]
  | [] ->
    if a.exact && List.for_all (fun (f:Semantic.field) -> not f.optional) a.afields
    then Atoms [Exact a.afields] else record a.afields

