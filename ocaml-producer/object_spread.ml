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

(* A spread of a value of an intersection (SOURCE-MODEL.md, "Object
   literals"): the value is of every operand, so it is of the meet of one arm
   of each, `(A | B) & C` being `(A & C) | (B & C)`. These arms are a
   proposal: Lean normalizes the operand's claim into its own clauses
   (`sourceMeetLists`) and checks the copy against them (`MergeOk`). *)
exception Refused of string
let unsupported s = raise (Refused s)
let meet_refused s = unsupported ("a spread of an intersection " ^ s)
(* Definition queries report unlocated unsupported errors. Convert those
   at this boundary; all spread refusals then share structured control flow. *)
let spread_definition declarations id args =
  try definition declarations id args with
  | Json.Error (Json.Message message) when String.starts_with ~prefix:"unsupported: " message ->
    unsupported (String.sub message 13 (String.length message - 13))
  | Json.Error (Json.Unbound { name; at }) -> unsupported (Json.unbound_text name at)
let primitive_atom = function
  | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Bigint | BigintLit _
  | Symbol | SymbolLit _ -> true
  | _ -> false
(* Two primitive atoms' common values: one of them, or none. *)
let atom_meet x y = match x,y with
  | _ when x = y -> [x]
  | (NumLit _,Num | StrLit _,Str | BigintLit _,Bigint | SymbolLit _,Symbol) -> [x]
  | (Num,NumLit _ | Str,StrLit _ | Bigint,BigintLit _ | Symbol,SymbolLit _) -> [y]
  | _ -> []
(* Select a field from all constraints on the key, with its own required
   presence. The heuristic only proposes: Lean checks the copy's field. *)
let field_meet fs =
  let f = List.hd fs in
  let optional = List.for_all (fun (f:Semantic.field) -> f.optional) fs in
  let host = List.exists (fun (f:Semantic.field) -> f.host) fs in
  let combined (c:Semantic.field) = {c with optional;
    write=(if List.for_all (fun (f:Semantic.field) -> f.write <> None) fs then c.write else None);
    host; receivers=List.sort_uniq compare (List.concat_map (fun (f:Semantic.field) -> f.receivers) fs);
    stable=List.exists (fun (f:Semantic.field) -> f.stable) fs} in
  if host then combined f
  else match List.find_opt (fun (c:Semantic.field) -> (optional || not c.optional) &&
    List.for_all (fun (d:Semantic.field) -> Type_queries.plausible_subtype c.read d.read) fs) fs with
    | Some c -> combined c
    | None -> meet_refused ("states the key " ^ key_text f.name ^
        " in several operands, and the proposal heuristic finds no field covering every constraint at the required presence")

let meet_records records =
  if List.exists (fun (r:shape) -> r.elements <> None) records then
    meet_refused "with an array operand is outside the fragment";
  if List.length (List.filter (fun (r:shape) -> r.indexes <> []) records) > 1 then
    meet_refused "of two operands with index signatures is outside the fragment";
  let rec callable_pairs = function
    | [] -> true
    | x::xs -> List.for_all (callable_record_supported x) xs && callable_pairs xs in
  if not (callable_pairs records) then
    meet_refused "of a callable and a record with readonly or optional fields, methods or an index is outside \
      the fragment: no clause states that callable";
  let fields = List.concat_map (fun (r:shape) -> r.fields) records in
  let names = List.sort_uniq compare (List.map (fun (f:Semantic.field) -> f.name) fields) in
  Atoms [Shape {fields=List.map (fun name -> field_meet
      (List.filter (fun (f:Semantic.field) -> f.name = name) fields)) names;
    indexes=List.concat_map (fun (r:shape) -> r.indexes) records;
    (* Both function and callable clause meets retain every signature. *)
    calls=List.concat_map (fun (r:shape) -> r.calls) records;elements=None}]

(* Expand whole products before selecting fields. Nested intersections and
   declarations retain all constraints until that selection. *)
let rec arm_products declarations seen t = match t with
  | Atoms [Named (id,args)] ->
    if List.mem (id,args) seen then meet_refused "through a cyclic declaration is outside the fragment";
    arm_products declarations ((id,args)::seen) (spread_definition declarations id args)
  | Atoms atoms when List.length atoms <> 1 ->
    List.concat_map (fun a -> arm_products declarations seen (Atoms [a])) atoms
  | Atoms _ | Rigid _ -> [[t]]
  | Union ts -> List.concat_map (arm_products declarations seen) ts
  | Meet (t,ts) ->
    List.fold_left (fun acc part ->
      let parts = arm_products declarations seen part in
      List.concat_map (fun a -> List.map (fun b -> a @ b) parts) acc)
      (arm_products declarations seen t) ts

let meet_product parts =
  let parts = List.filter (fun t -> t <> Atoms [Top]) parts in
  let primitives = List.filter_map (function Atoms [p] when primitive_atom p -> Some p | _ -> None) parts in
  let records = List.filter_map (function Atoms [Shape r] -> Some r | _ -> None) parts in
  let primitive = List.fold_left (fun acc p -> List.concat_map (fun q -> atom_meet p q) acc)
    (match primitives with [] -> [] | p::_ -> [p]) primitives in
  (* Only emptiness recognized by Lean's arm meet drops a product. An
     unsupported field meet, including disjoint literals, is a refusal. *)
  if (primitives <> [] && records <> []) || (primitives <> [] && primitive = []) then None
  else if List.exists (function Rigid _ -> true | _ -> false) parts then
    meet_refused "with a type parameter operand is outside the fragment"
  else if List.length primitives + List.length records <> List.length parts then
    meet_refused "with an operand other than a record, a primitive or a union of them is outside the fragment"
  else match records,primitives with
    | _::_,_ -> Some (meet_records records)
    | [],_::_ -> Some (Atoms primitive)
    | [],[] -> Some (Atoms [Top])

let meet_arms declarations seen t =
  List.filter_map meet_product (arm_products declarations seen t)

let rec alternatives_of ~target ~bound declarations seen t =
  let recur = alternatives_of ~target ~bound declarations in
  match t with
  | Atoms atoms -> List.concat_map (function
      | Nul | Undef | True | False | Num | NumLit _ | Bigint | BigintLit _ | Symbol ->
        [empty_alternative]
      (* A copy takes no symbol-keyed property, a private slot's included
         (SOURCE-MODEL.md, "Object literals"). *)
      | Exact fs -> [{afields=List.filter (fun (f:Semantic.field) -> (target || f.name <> Name proto_key) && string_key f) fs;
                      exact=true;index=None;symbols=None;numeric=None}]
      | Shape {fields;indexes;calls=[];elements=None} ->
        (* The string index states every own string key's type; a number
           index states only the canonical numeric ones', so a key it covers
           is left unstated, as an open record's is. *)
        [{afields=List.filter (fun (f:Semantic.field) ->
            not (method_field f) && (target || f.name <> Name proto_key) && string_key f) fields;exact=false;
          index=Option.map (fun (i:index_signature) -> i.value)
            (List.find_opt (fun (i:index_signature) -> i.keys=Strings) indexes);
          symbols=Option.map (fun (i:index_signature) -> i.value)
            (List.find_opt (fun (i:index_signature) -> i.keys=Symbols) indexes);numeric=None}]
      | Named (id,args) ->
        if List.mem (id,args) seen then unsupported "unguarded spread cycle";
        recur ((id,args)::seen) (spread_definition declarations id args)
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
      | Shape {elements=Some _;_} when target -> unsupported "a copy onto an array: \
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
      | Shape _ -> unsupported "a spread copies the own enumerable properties of a plain object; \
          a function with an index signature owns what its type does not state"
      | _ -> unsupported "a spread copies the own enumerable properties of a plain object; one of a string, an array, a function or a class value is outside the fragment") atoms
  | Union ts -> List.concat_map (recur seen) ts
  (* A value of an intersection is of one of its arms, each the one object
     an arm of every operand describes. *)
  | Meet _ ->
    List.concat_map (recur seen) (meet_arms declarations seen t)
  (* A value of a type parameter is one of its bound, whose own enumerable
     properties it copies: the copy is typed at the bound's fields. *)
  | Rigid r -> (match bound r with
    | Some b -> recur seen b
    | None -> unsupported "a spread of a type parameter without an object bound is outside the fragment")

(* The alternatives of the copy's source, written at [site]: a refusal names
   that span. *)
let source_alternatives ?(target=false) ?(bound=fun _ -> None) ~site declarations seen t =
  try
    let alternatives = alternatives_of ~target ~bound declarations seen t in
    if alternatives = [] then
      meet_refused "with no value is refused: its operands have no value in common";
    alternatives
  with Refused reason ->
    Proposal_diagnostics.unsupported (reason ^ " at " ^ Json.span_text site)

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
  let field name optional t = ({name;optional;read=t;write=Some t;host=false;receivers=[];stable=false} : Semantic.field) in
  let fields = List.filter_map (fun k ->
    (* The accumulator's prototype value is retained by merge in a fresh
       location; a source never copies its prototype link. *)
    if k = Name proto_key then Option.map (fun (f:Semantic.field) ->
        {f with write=Some f.read}) (find a.afields k) else
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

