(* Read-only queries used to propose types. Declarations and rigid bounds
   are explicit inputs; successful queries are hints for Lean to check. *)
open Semantic
open Source

let unsupported s = Json.fail ("unsupported: " ^ s)
let combine = List.fold_left union (Atoms [])
(* A conservative proposal-side test. In particular a rigid parameter is
   not known to exclude undefined. Lean's CoversPresence proves the conversion. *)
let rec excludes_undefined = function
  | Atoms atoms -> List.for_all (function Undef | Top | Named _ -> false | _ -> true) atoms
  | Union ts -> List.for_all excludes_undefined ts
  | Meet (t,ts) -> List.exists excludes_undefined (t::ts)
  | Rigid _ -> false
let plausible_elements excludes a b = match a,b with
  | None,None -> true
  | Some p,Some q ->
    let elements = p.required @ p.optional_elements @ Option.to_list p.rest in
    let presence = p.presence=q.presence || p.presence=Dense || q.presence=Sparse ||
      (p.presence=Readable && q.presence=Dense && List.for_all excludes elements) in
    presence && (q.readonly || not p.readonly) &&
      p.required=q.required && p.optional_elements=q.optional_elements && p.rest=q.rest
  | _ -> false
(* Clause kinds from Claims: non-callable records lower to refs or dict;
   signatures alone to arrs; signatures with fields to callable. CoversWith
   compares callable to callable or arrs, and arrs to arrs. Record width
   applies within refs/dict (the index check below restricts their pairs).
   Arrays lower through their store and are compared only with arrays. *)
let plausible_shape_kinds a b = match a,b with
  | {elements=None;calls=[];_}, {elements=None;calls=[];_} -> true
  | {elements=None;indexes=[];calls=_::_;fields},
    {elements=None;indexes=[];calls=_::_;fields=target} ->
    target=[] || fields<>[]
  | {elements=Some _;calls=[];_}, {elements=Some _;calls=[];_} -> true
  | _ -> false
(* A proposal heuristic for choosing an advertised arrow. It does not
   establish subtyping: Lean checks the selected call and its arguments. *)
let rec plausible_subtype_with excludes actual expected =
  if actual=expected then true else match actual,expected with
  | Atoms _,Atoms [Top] -> true
  | Atoms xs,Atoms ys -> List.for_all (fun x -> List.exists (fun y ->
      x=y || match x,y with
      | NumLit _,Num | StrLit _,Str | BigintLit _,Bigint | SymbolLit _,Symbol -> true
      (* The host-marked record: an object whose type excludes host values,
         as Lean's `hostFree` decides. *)
      | Exact _,Shape {fields=[m];indexes=[];calls=[];elements=None} when m=host_mark -> true
      | Shape a,Shape {fields=[m];indexes=[];calls=[];elements=None} when m=host_mark ->
        List.mem host_mark a.fields || a.indexes <> [] || a.calls <> [] ||
        List.exists (fun (f:Semantic.field) -> f.write <> None && not f.optional && not f.host) a.fields ||
        (match a.elements with Some s -> not s.readonly | None -> false)
      (* A value with call signatures is never within a record without
         any; members are equal, or within by width and depth inside one
         clause kind. *)
      | Shape a,Shape b when plausible_elements excludes a.elements b.elements
                             && (a.calls=[] || b.calls<>[])
                             && ((a.fields=b.fields && a.indexes=b.indexes)
                                 || (plausible_shape_kinds a b
                                     && plausible_fields excludes a.fields b.fields
                                     && (a.indexes=b.indexes || b.indexes=[])
                                     && plausible_index_writes excludes a b.indexes)) ->
        List.for_all (fun (q:Semantic.signature) -> List.exists (fun (p:Semantic.signature) ->
          Semantic.effect_covers p.call_effect q.call_effect &&
          ({p with call_effect=q.call_effect}=q ||
           (* A promise signature promising a larger type is met by one
              promising a smaller type: its `true` leaves the actual in the
              larger type too. *)
           (not (Semantic.plain_effect q.call_effect) &&
            {p with call_effect=q.call_effect;result=q.result}=q &&
            plausible_subtype_with excludes p.result q.result) ||
           (* A function taking fewer parameters meets a signature passing
              more: a call discards the actuals past its parameters. A
              promise at the longer signature is met only by code checked
              there, a closure claimed at it (`Closures`). *)
           (p.variadic=None && p.rest_pack=None && q.variadic=None && q.rest_pack=None &&
            Semantic.plain_effect q.call_effect &&
            List.length p.params < List.length q.params &&
            {p with call_effect=q.call_effect}
              = {q with params=List.filteri (fun i _ -> i < List.length p.params) q.params}))) a.calls) b.calls
      | _ -> false) ys) xs
  | Union parts,_ -> List.for_all (fun part -> plausible_subtype_with excludes part expected) parts
  | _,Union parts -> List.exists (plausible_subtype_with excludes actual) parts
  (* A value of an intersection is a value of each operand. *)
  | Meet (t,ts),_ -> List.exists (fun part -> plausible_subtype_with excludes part expected) (t::ts)
  | Rigid _,_ | _,(Rigid _ | Meet _) -> false
(* Record width and depth, as Lean's record rule reads them
   (POSITIVE-TYPES.md, "Records"): each expected member is met by the
   actual's member of its key, which the actual may hold beside others. An
   invariant field by an equal invariant field; a view by a required member
   within it; an optional member by a slot within it, excluding required
   readonly length views as Lean's optionalSources does, a writable one by
   an equal writable slot; a method by a method within it, with contravariant receiver requirements;
   every stable target key must be stable in the source. Writable target
   indexes additionally preserve source index and optional-field contracts
   through plausible_index_writes, including optional readonly views. *)
and plausible_fields excludes actual expected =
  actual=expected || List.for_all (fun (q:Semantic.field) ->
    List.exists (fun (p:Semantic.field) -> p=q || (p.name=q.name && p.host=q.host &&
      (not q.stable || p.stable) &&
      List.for_all (fun receiver -> List.exists (fun target ->
        plausible_subtype_with excludes target receiver) q.receivers) p.receivers &&
      match q.optional,q.write with
      | false,Some _ -> not p.optional && p.read=q.read && p.write=q.write
      | false,None -> not p.optional && plausible_subtype_with excludes p.read q.read
      | true,Some _ -> p.write<>None && p.read=q.read && p.write=q.write
      | true,None -> (p.optional || p.write<>None || p.name<>Name "length") &&
        plausible_subtype_with excludes p.read q.read)) actual) expected
and plausible_index_writes excludes actual expected =
  let overlaps a b = match a,b with
    | Symbols,Symbols -> true
    | Symbols,_ | _,Symbols -> false
    | _ -> true in
  (* Conservatively let a numeric index reach every string key: a failure
     to recognize a numeric spelling must not drop its field obligation. *)
  let may keys name = match keys,name with
    | (Strings | Numeric),Name _ | Symbols,Key _ -> true
    | _ -> false in
  List.for_all (fun (q:Semantic.index_signature) -> match q.writable with
    | None -> true
    | Some write ->
      List.for_all (fun (p:Semantic.index_signature) ->
        not (overlaps q.keys p.keys) || plausible_subtype_with excludes write p.value) actual.indexes &&
      List.for_all (fun (p:Semantic.field) ->
        not p.optional || not (may q.keys p.name) ||
        plausible_subtype_with excludes write p.read) actual.fields) expected
let plausible_subtype = plausible_subtype_with excludes_undefined
let literal_type = function
  | LNull -> Atoms [Nul] | LUndefined -> Atoms [Undef]
  | LBool true -> Atoms [True] | LBool false -> Atoms [False]
  | LNumber s -> number_literal s | LString s -> Atoms [StrLit s]
  | LBigint s -> Atoms [BigintLit s]

(* Read permissions do not imply write permissions. All candidates still pass
   through reconstructed obligations, including readonly view conversion. *)
let definition_of declarations id args =
  (* An interface and its base as one object: disjoint fields, and the one
     index signature either states. A hint only: Lean's `inheritRows` gives
     the declaration's meaning. *)
  let merge base own = match meet_objects base own with
    | Some t -> t
    | None -> (match base,own with
      (* A base that holds every record, `{}` or `object`, adds nothing to
         the interface's own record: their meet is that record. *)
      | Atoms atoms,Atoms [Shape _] when List.mem Top atoms ||
          List.mem (Shape {fields=[];indexes=[];calls=[];elements=None}) atoms -> own
      | Atoms [Shape inherited],Atoms [Shape local]
        when inherited.calls=[] && local.calls=[] && inherited.elements=None && local.elements=None
             && (inherited.indexes=[] || local.indexes=[] || inherited.indexes=local.indexes) ->
        (* A member both declare, as a derived class's override: the
           declaration's own is the hint; Lean's meaning is both, and a value
           must meet each. *)
        let own_names = List.map (fun (f:Semantic.field) -> f.name) local.fields in
        Atoms [Shape {local with fields=local.fields @ List.filter
          (fun (f:Semantic.field) -> not (List.mem f.name own_names)) inherited.fields;
          indexes=(if local.indexes=[] then inherited.indexes else local.indexes)}]
      | _ -> unsupported "inheritance needs plain object contracts") in
  let rec instantiate seen id args =
  if List.mem id seen then unsupported "cyclic inheritance";
  match List.find_opt (fun (d:Source.declaration) -> d.id=id) declarations with
  | Some d ->
    (* A reference carries every argument. *)
    if List.length args <> List.length d.parameters then
      unsupported "type application has wrong arity";
    let solution = List.map2 (fun parameter value -> parameter,ValueArgument value) d.parameters args in
    (* An intersection of the equation, its arguments substituted, is the one
       object its operands describe where they are records, a declared one
       read through its equation (`Serializable<Todo>`); otherwise it stays
       their intersection, including over type parameters. Keeping only the
       principal operand would lose receiver restrictions when the equation
       is later instantiated. Lean fills the claim's meet row independently. *)
    let meet t ts =
      let expand t = match t with
        | Atoms [Named (named,named_args)] when not (List.mem named (id::seen)) ->
          (try instantiate (id::seen) named named_args with Json.Error _ -> t)
        | t -> t in
      match List.fold_left (fun acc part -> Option.bind acc (fun a -> meet_objects a (expand part)))
              (Some (expand t)) ts with
      | Some merged -> merged
      | None -> Meet (t,ts) in
    let expression = match d.expression with
      | Some e -> e
      | None -> unsupported ("a computed alias has no equation: " ^ id) in
    let body = Inference.substitute ~meet solution expression in
    (* A base named through an alias of another declaration is that
       declaration, instantiated: its members are inherited by structure. *)
    let rec base_of seen t = match t with
      | Atoms [Named (named,named_args)] ->
        if List.mem named seen then unsupported "cyclic inheritance";
        base_of (named::seen) (instantiate seen named named_args)
      | t -> t in
    List.fold_left (fun own base ->
      match Inference.substitute ~meet solution base with
      | Atoms [Named _] as named -> merge (base_of (id::seen) named) own
      (* A base written as its record: `Error`'s instance contract, which a
         class extending it inherits (SOURCE-ELABORATION.md). *)
      | Atoms [Shape _] as record -> merge record own
      | _ -> unsupported "heritage is not a named base")
      body d.bases
  | None -> unsupported ("missing declaration " ^ id) in
  instantiate [] id args
(* A declaration's instance, computed once for each application and the
   declarations it is read in: a family's root is its arms' union, each an
   interface merged with its bases, read at every refinement of a node. *)
let definitions : (string * ty list, Source.declaration list * ty) Hashtbl.t = Hashtbl.create 256
let definition declarations id args =
  match Hashtbl.find_opt definitions (id, args) with
  | Some (read, t) when read == declarations -> t
  | _ ->
    let t = definition_of declarations id args in
    Hashtbl.replace definitions (id, args) (declarations, t);
    t
(* A declaration's equation, for inference to look inside an application. *)
let expand_named declarations = function
  | Atoms [Named (id,args)] ->
    (try Some (definition declarations id args) with Json.Error _ -> None)
  | _ -> None
(* Inspect a declared callable's source equation for proposal purposes only.
   The point claim remains the named type; Lean independently fills and checks
   that graph row from the same declaration. *)
let rec declared_head declarations seen = function
  | Atoms [Named (id,args)] ->
    if List.mem id seen then unsupported "unguarded callable alias cycle";
    declared_head declarations (id::seen) (definition declarations id args)
  | t -> t
(* Whether a type excludes `undefined`, each declared atom unfolded to what
   it names, through unions (a host family's declaration read as the union
   of its arms); a cycle or an unreadable equation is taken to admit it. A
   proposal heuristic; Lean decides presence. *)
let excludes_undefined_declared declarations t =
  let rec go seen = function
    | Atoms atoms -> List.for_all (function
        | Undef | Top -> false
        | Named (id,args) -> not (List.mem id seen) &&
          (try go (id::seen) (definition declarations id args) with Json.Error _ -> false)
        | _ -> true) atoms
    | Union ts -> List.for_all (go seen) ts
    | Meet (t,ts) -> List.exists (go seen) (t::ts)
    | Rigid _ -> false in
  go [] t
(* `plausible_subtype` up to the declarations: each side is read as
   written or with its declared atoms unfolded, through unions, to what they
   name (the compiler API's `Statement`, which TypeScript reads as
   `StatementBase`; `type T = A | F`, which holds `F` written inline), and a
   readonly array's elements likewise, covariantly (`readonly Identifier[]`
   within `readonly Node[]`). A proposal heuristic; Lean decides inclusion.
   Where both sides are unfolded, a host method whose receiver is the
   declaration it unfolds (`Set<T>`'s members, `NativeSetView<T>`'s) is
   compared at one receiver for both, as the declaration's own `this`. *)
let rec plausible_subtype_declared declarations actual expected =
  let unfold ~own t =
    (* Each declared atom contributes once to the union; the path retains
       the named atom at a cycle. Equations are read only as needed. *)
    let expanded = Hashtbl.create 32 in
    let own_receivers self = function
      | Atoms atoms when own -> Atoms (List.map (function
          | Shape sh ->
            let method_ t = match t with
              | Atoms [Shape ({calls;_} as m)] -> Atoms [Shape { m with calls = List.map (fun (c:Semantic.signature) ->
                  match c.receiver with
                  | Atoms [Named (r,_)] when r = self -> { c with receiver = Atoms [Top] }
                  | _ -> c) calls }]
              | t -> t in
            Shape { sh with fields = List.map (fun (f:Semantic.field) ->
              if f.host then { f with read = method_ f.read; write = Option.map method_ f.write } else f) sh.fields }
          | a -> a) atoms)
      | t -> t in
    let rec walk seen = function
      | Atoms atoms -> combine (List.map (function
          | Named (id,args) as a when not (List.mem id seen) ->
            if Hashtbl.mem expanded (id,args) then Atoms [] else begin
              Hashtbl.add expanded (id,args) ();
              try walk (id::seen) (own_receivers id (definition declarations id args)) with Json.Error _ -> Atoms [a]
            end
          | a -> Atoms [a]) atoms)
      | Union ts -> combine (List.map (walk seen) ts)
      | t -> t in
    walk [] t in
  let unfolded_actual = lazy (unfold ~own:false actual) in
  let unfolded_expected = lazy (unfold ~own:false expected) in
  let readonly_elements () = match actual,expected with
    | Atoms [Shape ({elements=Some p;_} as a)],Atoms [Shape ({elements=Some q;_} as b)] ->
      q.readonly && a.fields=b.fields && a.indexes=b.indexes && a.calls=[] && b.calls=[] &&
      p.required=[] && q.required=[] && p.optional_elements=[] && q.optional_elements=[] &&
      (p.presence=q.presence || p.presence=Dense || q.presence=Sparse) &&
      (match p.rest,q.rest with
       | Some x,Some y -> plausible_subtype_declared declarations x y
       | _ -> false)
    | _ -> false in
  plausible_subtype actual expected ||
  plausible_subtype actual (Lazy.force unfolded_expected) ||
  plausible_subtype (Lazy.force unfolded_actual) expected ||
  plausible_subtype (Lazy.force unfolded_actual) (Lazy.force unfolded_expected) ||
  plausible_subtype (unfold ~own:true actual) (unfold ~own:true expected) ||
  readonly_elements ()
(* The first operand of an intersection a read succeeds on; where none has
   it, the principal operand's reason. *)
let first_part read parts =
  match List.find_map (fun t -> try Some (read t) with Json.Error _ -> None) parts with
  | Some t -> t
  | None -> (match parts with
    | principal :: _ -> read principal
    | [] -> unsupported "read on an empty intersection")
(* `ArrayProto`, the declaration of `Array.prototype`'s members, by identity. *)
(* The key an object keeps its prototype under: no source property spells it. *)
let proto_key = "[[proto]]"
let array_prototype = "tscert/array-prototype#ArrayProto#0:0"
let key_text = function Name n -> n | Key i -> "[symbol " ^ string_of_int i ^ "]"
(* The contract of the prototype a primitive's members are read through:
   `StringProto` for a string, and so on. *)
let primitive_prototype = function
  | Str | StrLit _ -> Some "tscert/string-prototype#StringProto#0:0"
  | Num | NumLit _ -> Some "tscert/number-prototype#NumberProto#0:0"
  | Bigint | BigintLit _ -> Some "tscert/bigint-prototype#BigIntProto#0:0"
  | True | False -> Some "tscert/boolean-prototype#BooleanProto#0:0"
  | _ -> None
(* The property key a number spells (`ToString`), for integers below 1e21
   and decimals `%g` writes as JavaScript does; none otherwise. *)
let number_key bits =
  let n = Int64.float_of_bits bits in
  if Float.is_integer n && Float.abs n < 1e21 then Some (Printf.sprintf "%.0f" (Float.abs n) |> fun s ->
    if n < 0. then "-" ^ s else s)
  else if Float.is_finite n then
    let rec shortest p = if p > 17 then None else
      let s = Printf.sprintf "%.*g" p n in
      if float_of_string s = n then (if String.contains s 'e' then None else Some s) else shortest (p+1) in
    shortest 1
  else None
(* Whether a key is canonical numeric: the spelling of the number it reads
   as, which is the key `o[n]` reaches for that number. *)
let canonical_numeric s =
  s = "NaN" || s = "Infinity" || s = "-Infinity" ||
  (match float_of_string_opt s with
   | Some n -> number_key (Int64.bits_of_float n) = Some s
   | None -> false)
(* The index of a shape whose class surely admits a key: the canonical
   numeric keys' first, which is the narrowest, then every string key's; a
   symbol key's. *)
let index_for (shape:shape) name =
  let find keys = List.find_opt (fun (i:Semantic.index_signature) -> i.keys=keys) shape.indexes in
  match name with
  | Name s ->
    (match (if canonical_numeric s then find Numeric else None) with
     | Some i -> Some i | None -> find Strings)
  | Key _ -> find Symbols
let rec field_type bounds declarations seen t name = match t with
  | Atoms atoms -> combine (List.map (function
      | Shape {elements=Some _;_} when name=Name "length" -> Atoms [Num]
      (* An array's own field (a regex match's `index`, a node list's
         `pos`); any other key of an array is read from its prototype. *)
      | Shape {elements=Some _;fields;_} when List.exists (fun (f:Semantic.field) -> f.name=name) fields ->
        let f = List.find (fun (f:Semantic.field) -> f.name=name) fields in
        if f.optional then union f.read (Atoms [Undef]) else f.read
      | Shape {elements=Some _;_} ->
        field_type bounds declarations seen (Atoms [Named (array_prototype,[])]) name
      | Shape shape -> (match List.find_opt (fun (f:Semantic.field) -> f.name=name) shape.fields with
          | Some f -> if f.optional then union f.read (Atoms [Undef]) else f.read
          | None -> (match index_for shape name with
            | Some index -> union index.value (Atoms [Undef])
            | None -> (match List.find_opt (fun (f:Semantic.field) -> f.name=Name proto_key) shape.fields with
              (* A member the object holds on its prototype. *)
              | Some p -> field_type bounds declarations seen p.read name
              | None -> unsupported ("missing field " ^ key_text name))))
      | Exact fields -> (match List.find_opt (fun (f:Semantic.field) -> f.name=name) fields with
          | Some f -> f.read
          | None -> (match List.find_opt (fun (f:Semantic.field) -> f.name=Name proto_key) fields with
            (* A fresh object's member its prototype holds: an
               `Error`-derived instance's message, on its first link. *)
            | Some p -> field_type bounds declarations seen p.read name
            | None -> unsupported ("missing field " ^ key_text name)))
      (* A class value's static field. *)
      | Ctors (_,statics) -> (match List.find_opt (fun (f:Semantic.field) -> f.name=name) statics with
          | Some f -> f.read
          | None -> unsupported ("missing field " ^ key_text name))
      | Named (id,args) ->
        if List.mem id seen then unsupported "unguarded field cycle";
        field_type bounds declarations (id::seen) (definition declarations id args) name
      (* A string owns its `length`; any other member of a primitive is its
         wrapper prototype's. *)
      | Str | StrLit _ when name=Name "length" -> Atoms [Num]
      | atom when primitive_prototype atom <> None ->
        let id = Option.get (primitive_prototype atom) in
        (* The parser reads a wrapper prototype where TypeScript types a
           member's receiver as that primitive. *)
        if not (List.exists (fun (d:Source.declaration) -> d.id=id) declarations) then begin
          let kind = String.sub id 5 (String.index id '-' - 5) in
          unsupported ("a member read on a " ^ kind ^ " where the type TypeScript gives the receiver holds no " ^
            kind ^ ": the producer and TypeScript disagree on the receiver")
        end;
        field_type bounds declarations seen (Atoms [Named (id,[])]) name
      | _ -> unsupported "field read on non-object") atoms)
  | Union ts -> combine (List.map (fun t -> field_type bounds declarations seen t name) ts)
  (* A value of an intersection is one of each operand: read as the first
     operand that has the field, a hint Lean checks. *)
  | Meet (t,ts) -> first_part (fun t -> field_type bounds declarations seen t name) (t::ts)
  | Rigid r -> (match List.assoc_opt r bounds with
    | Some b -> field_type bounds declarations seen b name
    | None -> unsupported "field read on rigid parameter")
(* A key-adding write (PROGRAM-TYPING.md, "Key-adding writes"): a write of a key
   some plain-object arm of the receiver's type states neither as a required
   field nor as a method may add the key. Lean lowers it on an owned local as
   the copy of the object with the key, and refuses it on any other object;
   the producer proposes the grown type and the new field's contract. *)
let plain_arms declarations t =
  match (try declared_head declarations [] t with Json.Error _ -> t) with
  | Atoms (_::_ as atoms) when List.for_all (function
      | Shape {elements=None;calls=[];_} | Exact _ -> true | _ -> false) atoms -> Some atoms
  | _ -> None
let arm_fields = function Shape {fields;_} | Exact fields -> fields | _ -> []
(* Prototype-backed records exclude their prototype's own keys. A proposal
   for key growth must retain that bound, just as the exported row does. *)
let excludes_key arm name =
  match List.find_opt (fun (f:Semantic.field) -> f.name = Name "[[proto]]") (arm_fields arm) with
  | Some {read=Atoms [Shape proto];_} ->
    List.exists (fun (f:Semantic.field) -> f.name=name) proto.fields
  | _ -> false
let may_lack declarations t name =
  match plain_arms declarations t with
  | Some atoms ->
    List.exists (fun a -> not (List.exists (fun (f:Semantic.field) ->
      f.name=name && not f.optional) (arm_fields a))) atoms
    && not (List.exists (fun a -> excludes_key a name) atoms)
    && not (List.exists (fun a -> List.exists (fun (f:Semantic.field) ->
      f.name=name && f.optional && f.write=None) (arm_fields a)) atoms)
  | None -> false
(* The contract the new field is added at: an optional field's own where an
   arm states one, else the value's type, a literal's widened as a fresh
   literal's field is. *)
let added_contract declarations t name (rhs:Source.expr) value =
  let declared = Option.bind (plain_arms declarations t) (List.find_map (fun a ->
    List.find_map (fun (f:Semantic.field) ->
      if f.name=name && f.optional then f.write else None) (arm_fields a))) in
  (* A binding's or a read's type is the contract as it stands, without the
     exact keys a fresh literal has, as TypeScript's declared type is. *)
  let loosen = function
    | Atoms atoms -> Atoms (List.map (function
        | Exact fields -> Shape {fields;indexes=[];calls=[];elements=None}
        | a -> a) atoms)
    | t -> t in
  match declared,rhs.node with
  | Some c,_ -> c
  | None,(Id _ | Read _) -> loosen value
  | None,_ -> loosen (widen value)
(* The object's type once the key is added at [c]: every arm owns it. *)
let grown declarations t name c =
  match plain_arms declarations t with
  | Some atoms ->
    let field = {name;optional=false;read=c;write=Some c;host=false;receivers=[];stable=false} in
    let add fs = List.filter (fun (f:Semantic.field) -> f.name<>name) fs @ [field] in
    Atoms (List.map (function
      | Shape s -> Shape {s with fields=add s.fields}
      | Exact fs -> Exact (add fs)
      | a -> a) atoms)
  | None -> t
(* What a fresh array literal expected at an iterable type holds, found as
   TypeScript finds it: the expected type's member under the key
   `Array.prototype` iterates by (its one symbol key, `[Symbol.iterator]`),
   the `next` results of that member's result other than a finished one, and
   their `value`. A construction hint only: Lean proves the literal, a
   `readonly T[]`, below the expected type. *)
let iterated_hint declarations expected =
  let expand = function Atoms [Named (id,args)] -> definition declarations id args | t -> t in
  let shape t = match expand t with Atoms [Shape s] -> Some s | _ -> None in
  let member key t = Option.bind (shape t) (fun s ->
    Option.map (fun (f:Semantic.field) -> f.read)
      (List.find_opt (fun (f:Semantic.field) -> f.name=key) s.fields)) in
  let result t = Option.bind (shape t) (fun s -> match s.calls with
    | c :: _ -> Some c.result | [] -> None) in
  (* A union's alternatives, through the aliases that name it. *)
  let rec parts seen t = match t with
    | Union ts -> List.concat_map (parts seen) ts
    | Atoms [Named (id,args)] when not (List.mem id seen) ->
      (match definition declarations id args with
       | Atoms [Shape _] -> [t]
       | body -> parts (id::seen) body)
    | Atoms (_::_::_ as atoms) -> List.concat_map (fun a -> parts seen (Atoms [a])) atoms
    | t -> [t] in
  let ( let* ) = Option.bind in
  let* key = Option.bind (shape (Atoms [Named (array_prototype,[])])) (fun s ->
    List.find_map (fun (f:Semantic.field) -> match f.name with
      | Key _ -> Some f.name | Name _ -> None) s.fields) in
  let* iterator = Option.bind (member key expected) result in
  let* results = Option.bind (member (Name "next") iterator) result in
  match List.filter_map (fun r -> match member (Name "done") r with
      | Some (Atoms [True]) -> None
      | _ -> member (Name "value") r) (parts [] results) with
  | [] -> None
  | values -> Some (combine values)
(* The first arm of an iterated value that is not an array, named for the
   refusal where the loop or spread steps `%Iterate%` or copies an array:
   the parser picks the intrinsic of a string, a `Set`, a `Map` or a host
   collection iterator only where TypeScript types the whole iterable as one
   such kind, and lowers a program's iterable, or a union with one, to the
   iterator protocol (SOURCE-ELABORATION.md "Loops and spreads over iterables").
   A type parameter is left to Lean. *)
let rec non_array_arm declarations seen t = match t with
  | Rigid _ -> None
  | Union ts -> List.find_map (non_array_arm declarations seen) ts
  | Meet (t,_) -> non_array_arm declarations seen t
  | Atoms atoms -> List.find_map (function
      | Shape {elements=Some _;_} -> None
      | Named (id,args) when not (List.mem id seen) ->
        (match definition declarations id args with
         | body -> non_array_arm declarations (id::seen) body
         | exception Json.Error _ -> None)
      | Named _ -> None
      | Str | StrLit _ -> Some "a string"
      (* An object naming a symbol-keyed member, as `[Symbol.iterator]` is:
         an iterable to TypeScript. Any other is left to Lean, which finds
         no iterator, as TypeScript does not. *)
      | Shape {fields;_} when List.exists (fun (f:Semantic.field) ->
            match f.name with Key _ -> true | Name _ -> false) fields ->
        Some "an object that is not an array (a Set, a Map, an iterator or another iterable)"
      | _ -> None) atoms
(* The elements a slice rest from index [start] collects from an array of
   type [t]: every arm's positions from there on, an optional one with
   `undefined`, and its rest element. `%RestFrom:k%` is claimed at it. *)
let slice_element declarations start t =
  let rec arms seen t = match t with
    | Union ts -> List.concat_map (arms seen) ts
    | Atoms atoms -> List.concat_map (function
        | Named (id,_) as a when not (List.mem id seen) ->
          arms (id::seen) (declared_head declarations [] (Atoms [a]))
        | a -> [a]) atoms
    | Rigid _ | Meet _ -> unsupported "a slice rest over a type parameter or an intersection" in
  combine (List.concat_map (function
    | Shape {elements=Some s;_} ->
      let r = List.length s.required in
      List.filteri (fun i _ -> i >= start) s.required
      @ List.filteri (fun i _ -> i + r >= start) (List.map (fun t -> union t (Atoms [Undef])) s.optional_elements)
      @ Option.to_list s.rest
    | _ -> unsupported "an array pattern over a value that may not be an array: it would step that value's own \
        iterator, which is not modeled; only an array's positions are read") (arms [] t))
(* A type's atoms through the declarations and unions that name them. *)
(* The atoms a type's arms are, through the declarations that state them:
   `None` where some arm, at any depth of the definitions, is a type
   parameter or an intersection, whose values no atom list states. A caller
   cannot read such a type as the atoms of its other arms. *)
let flat_atoms declarations t =
  let rec go seen t = match t with
    | Union ts -> all (List.map (go seen) ts)
    | Atoms atoms -> all (List.map (function
        | Named (id,args) when not (List.mem id seen) ->
          (match definition declarations id args with
           | body -> go (id::seen) body
           | exception Json.Error _ -> Some [Named (id,args)])
        | a -> Some [a]) atoms)
    | Rigid _ | Meet _ -> None
  and all parts = List.fold_right (fun p acc -> match p,acc with
    | Some xs,Some ys -> Some (xs @ ys) | _ -> None) parts (Some []) in
  go [] t
(* A union naming a declaration beside atoms of that declaration's
   definition is the declaration's: the atoms add no value. `T | { kind:
   "a" }`, with `T = { kind: "a" } | { kind: "b" }`, is `T`. *)
let absorb declarations = function
  | Atoms xs as t when List.exists (function Named _ -> true | _ -> false) xs ->
    let covered = List.concat_map (function
      | Named _ as a -> (try Option.value ~default:[] (flat_atoms declarations (Atoms [a])) with Json.Error _ -> [])
      | _ -> []) xs in
    let kept = List.filter (fun a -> (match a with Named _ -> true | _ -> false) || not (List.mem a covered)) xs in
    if List.length kept = List.length xs then t else Atoms kept
  | t -> t
(* A key whose type names string or number singletons, through the
   declarations and unions that state them, is read as those singletons. *)
let literal_key declarations key =
  match (try Option.value ~default:[] (flat_atoms declarations key) with Json.Error _ -> []) with
  | _::_ as ks when List.for_all (function StrLit _ | NumLit _ -> true | _ -> false) ks -> Atoms ks
  | _ -> key
(* A key of several string or number singletons (NaN, which no equality
   test finds, is none): Lean reads, per singleton, the member its key names. *)
let key_singletons = function
  | Atoms (_::_::_ as ks) when List.for_all (function
      | StrLit _ -> true
      | NumLit bits -> not (Float.is_nan (Int64.float_of_bits bits)) && number_key bits <> None
      | _ -> false) ks -> Some ks
  | _ -> None
let rec index_type bounds declarations seen receiver key =
  let key = literal_key declarations key in
  match key_singletons key with
  | Some ks -> combine (List.map (fun k -> index_type bounds declarations seen receiver (Atoms [k])) ks)
  | None -> match receiver with
  | Atoms atoms -> combine (List.map (function
      | Shape {elements=Some sequence;_} ->
        let at i = if i < 0 then Atoms [Undef]
          else match List.nth_opt sequence.required i with
          | Some t -> t
          | None -> let offset=i-List.length sequence.required in
            union (Atoms [Undef]) (match List.nth_opt sequence.optional_elements offset with
              | Some t -> t | None -> Option.value sequence.rest ~default:(Atoms [])) in
        (match key with
          | Atoms [NumLit bits] -> let n=Int64.float_of_bits bits in
            if n >= 0. && n < float_of_int max_int && Float.floor n=n then at (int_of_float n)
            else Atoms [Undef]
          | _ -> combine (Atoms [Undef] :: sequence.required @ sequence.optional_elements @ Option.to_list sequence.rest))
      | Shape shape -> (match key with
          | Atoms [StrLit name] -> field_type bounds declarations seen (Atoms [Shape shape]) (Name name)
          (* A number names the property its `ToString` spells. *)
          | Atoms (NumLit bits :: rest) when List.for_all (fun a -> a = NumLit bits
              || (match a with NumLit b -> Int64.float_of_bits b = Int64.float_of_bits bits | _ -> false)) rest
              && Option.is_some (number_key bits) ->
            field_type bounds declarations seen (Atoms [Shape shape]) (Name (Option.get (number_key bits)))
          (* A dynamic key reads through an index over its keys: a string
             through a string index, a number through a number index or a
             string one, a symbol through a symbol index. *)
          | Atoms [(Str | Num | Symbol) as k] ->
            let within = match k with
              | Str -> [Strings] | Num -> [Numeric;Strings] | _ -> [Symbols] in
            (match List.find_map (fun keys -> List.find_opt
                (fun (i:Semantic.index_signature) -> i.keys=keys) shape.indexes) within with
              | Some index -> union index.value (Atoms [Undef])
              | None -> unsupported "dynamic index requires a dictionary over its keys")
          | _ -> unsupported "record index requires a string key")
      | Exact _ as atom -> (match key with
          | Atoms [StrLit name] -> field_type bounds declarations seen (Atoms [atom]) (Name name)
          | Atoms [NumLit bits] when number_key bits <> None ->
            field_type bounds declarations seen (Atoms [atom]) (Name (Option.get (number_key bits)))
          | _ -> unsupported "record index requires a string key")
      | Named (id,args) ->
        if List.mem id seen then unsupported "unguarded index cycle";
        index_type bounds declarations (id::seen) (definition declarations id args) key
      (* A string's index properties are its code units: a numeric key reads
         one, or `undefined` past the end. A string literal key is a named
         member's. *)
      | (Str | StrLit _) as atom -> (match key with
          | Atoms [StrLit name] -> field_type bounds declarations seen (Atoms [atom]) (Name name)
          | Atoms ks when ks <> [] && List.for_all (function Num | NumLit _ -> true | _ -> false) ks ->
            Atoms [Str;Undef]
          | _ -> unsupported "a string's index needs a numeric key")
      (* Another primitive's named member is its wrapper prototype's. *)
      | atom when primitive_prototype atom <> None -> (match key with
          | Atoms [StrLit name] -> field_type bounds declarations seen (Atoms [atom]) (Name name)
          | _ -> unsupported "a primitive's member needs a string literal key")
      | _ -> unsupported "indexed read on non-object") atoms)
  | Union ts -> combine (List.map (fun t -> index_type bounds declarations seen t key) ts)
  | Meet (t,ts) -> first_part (fun t -> index_type bounds declarations seen t key) (t::ts)
  | Rigid r -> (match List.assoc_opt r bounds with
    | Some b -> index_type bounds declarations seen b key
    | None -> unsupported "indexed read on rigid parameter")

(* A fresh literal is built at the one object contract its expected type
   names: a record or dictionary shape, possibly behind a declaration (a class
   instance, or the dictionary arm of a recursive type). This is a construction
   hint only: every field still has a source obligation against the contract.
   Existing objects never gain a dictionary guarantee by this lookup. *)
let rec object_hint declarations seen = function
  | Atoms atoms ->
    let choices = List.filter_map (function
      | Shape ({elements=None;_} as shape) -> Some shape
      | Named (id,args) when not (List.mem id seen) ->
        object_hint declarations (id::seen) (definition declarations id args)
      | _ -> None) atoms in
    (match choices with [shape] -> Some shape | _ -> None)
  | Union parts ->
    (match List.filter_map (object_hint declarations seen) parts with
    | [shape] -> Some shape | _ -> None)
  | Rigid _ | Meet _ -> None

(* Where the expected type is a union of several records or several arrays,
   a fresh literal is built at the one arm its own keys (or length) and its
   literal-valued members select, as TypeScript discriminates a contextual
   union by a literal's properties: `{ kind: "a", n: 1 }` at
   `{ kind: "a"; n: number } | { kind: "b"; s: string }` is built at the
   first arm, so its `kind` holds the literal type the arm fixes rather than
   the widened `string` no arm admits. A construction hint only, as
   [object_hint] is: Lean checks every member against the arm, and no other
   arm is ever assumed. *)
let literal_admitted declarations (e:expr) t = match e.node with
  | Literal l -> plausible_subtype (literal_type l) (declared_head declarations [] t)
  | _ -> true
let rec record_arms declarations seen = function
  | Atoms atoms -> List.concat_map (function
      | Shape ({elements=None;calls=[];_} as shape) -> [shape]
      | Named (id,args) when not (List.mem id seen) ->
        record_arms declarations (id::seen) (definition declarations id args)
      | _ -> []) atoms
  | Union parts -> List.concat_map (record_arms declarations seen) parts
  | Rigid _ | Meet _ -> []
let discriminated_record declarations expected (members:(key * expr) list) =
  let admits (s:shape) =
    List.for_all (fun (name,e) ->
      match List.find_opt (fun (f:field) -> f.name = name && not f.host) s.fields with
      | Some f -> literal_admitted declarations e f.read
      | None -> index_for s name <> None) members
    && List.for_all (fun (f:field) -> f.optional || f.host
      || List.mem_assoc f.name members) s.fields in
  match List.filter admits (record_arms declarations [] expected) with
  | [shape] -> Some shape
  | _ -> None
let discriminated_array declarations (arms:sequence list) (elements:expr list) =
  let n = List.length elements in
  let admits (s:sequence) =
    let fixed = s.required @ s.optional_elements in
    n >= List.length s.required && (s.rest <> None || n <= List.length fixed)
    && List.for_all Fun.id (List.mapi (fun i e -> match List.nth_opt fixed i with
      | Some t -> literal_admitted declarations e t
      | None -> Option.fold ~none:false ~some:(literal_admitted declarations e) s.rest) elements) in
  match List.filter admits arms with
  | [s] -> Some s
  | _ -> None

(* The numeric family of an operand: bigint where every atom is one. *)
let numeric_family declarations t =
  match declared_head declarations [] t with
  | Atoms (_::_ as atoms) when List.for_all (function Bigint | BigintLit _ -> true | _ -> false) atoms ->
    Atoms [Bigint]
  | _ -> Atoms [Num]

(* Whether every value of a type is a string. *)
let string_like declarations t =
  match declared_head declarations [] t with
  | Atoms (_::_ as atoms) -> List.for_all (function Str | StrLit _ -> true | _ -> false) atoms
  | _ -> false

(* What an arithmetic operator yields: a string for `+` with a string
   operand, which concatenates; a number for `&`, `|`, `<<`, `>>` and `>>>`,
   which take numbers alone; else the numeric family of the left operand.
   Lean checks the operands pair by pair. *)
let operation_result declarations op left right =
  if op = Add && (string_like declarations left || string_like declarations right) then Atoms [Str]
  else if List.mem op [BitAnd; BitOr; Shl; Shr; Ushr] then Atoms [Num]
  else numeric_family declarations left

(* The atoms of `t` that may be (`equal`) or may not be strictly equal to a
   singleton value. Unknown/rigid predicates conservatively retain their type;
   proof checking validates each narrower cut. *)
let rec restrict ?declarations singleton equal t = match t with
  (* `unknown` other than null: its other kinds (Lean's `sourceSlice`). *)
  | Atoms xs when List.mem Top xs && not equal && singleton = Nul ->
    union (restrict ?declarations singleton equal (Atoms (List.filter (fun a -> a <> Top) xs)))
      (unknown_slice (fun a -> a <> singleton))
  | Atoms xs -> ground (List.filter (fun atom ->
      let rec known atom = match atom,singleton with
        | Nul,Nul | Undef,Undef | True,True | False,False -> Some true
        (* Number::equal: NaN equals nothing, and the zeros each other. *)
        | NumLit a,NumLit b -> Some (Int64.float_of_bits a = Int64.float_of_bits b)
        | StrLit a,StrLit b -> Some (a=b)
        | BigintLit a,BigintLit b -> Some (a=b)
        | Num,NumLit _ | Str,StrLit _ | Bigint,BigintLit _ -> None
        (* A declaration answers as its atoms do, where they all agree, as
           Lean's slice of its row does; an intersection as its first
           part's, which holds every value of it. *)
        | Named _,_ ->
          let agree = function
            | Some r :: more when List.for_all (( = ) (Some r)) more -> Some r
            | _ -> None in
          let rec head_answer = function
            | Atoms (a::rest) when Atoms (a::rest) <> Atoms [atom] -> agree (List.map known (a::rest))
            | Meet (principal,_) -> head_answer principal
            | _ -> None in
          (match declarations with
           | None -> None
           | Some declarations ->
             (match (try Some (declared_head declarations [] (Atoms [atom])) with Json.Error _ -> None) with
              | Some head -> head_answer head
              | None -> None))
        (* Any other atom is of another kind than the singleton, or an
           object, never equal to it. *)
        | Top,_ -> None
        | _,_ -> Some false in
      match known atom with Some result -> result=equal | None -> true) xs
    (* Equal to one number other than a zero, or to one string: that value,
       whatever the operand was, `unknown` included (Lean's `observeAtom` and
       `tagMember`). *)
    |> List.map (fun atom -> match atom,singleton with
      | (Num | Top),NumLit b when equal && Int64.float_of_bits b <> 0.0 -> NumLit b
      | (Str | Top),StrLit s when equal -> StrLit s
      | _ -> atom))
  (* A union's arms each; an intersection's values are its principal's, so
     it goes where none of those can. *)
  | Union ts -> List.fold_left union (Atoms []) (List.map (restrict ?declarations singleton equal) ts)
  | Meet (principal,_) when restrict ?declarations singleton equal principal = Atoms [] -> Atoms []
  | Rigid _ | Meet _ -> t
(* The one value every member of a type is, as Lean selects a singleton
   operand: null, undefined, a Boolean, a string, a bigint, or one number
   (both zeros are one). *)
let singleton_atom = function
  | Atoms [(Nul | Undef | True | False | StrLit _ | BigintLit _ | NumLit _) as a] -> Some a
  | Atoms (NumLit b :: rest) when List.for_all (function
      | NumLit c -> Int64.float_of_bits c = Int64.float_of_bits b | _ -> false) rest -> Some (NumLit b)
  | _ -> None
(* The arms of an object's union that may remain once its field `key` was
   found (not) equal to something: an arm whose field, sliced by that outcome,
   holds nothing is dropped. The arm stays dropped whatever the field holds
   later: an object's arm is fixed where it is allocated. Lean checks the
   slice. *)
(* The arms an atom stands for: a declaration whose definition is a union of
   atoms, the arms of each of those atoms; an alias of one declaration
   (`Expression`, whose definition is `ExpressionBase`), the arms of that
   declaration; any other atom, itself. A test keeps or drops each arm,
   wherever its declaration occurs in a union: a join can leave a
   declaration beside arms of it a test already split. *)
let rec atom_arms declarations seen = function
  | Named (id,args) as a when not (List.mem id seen) ->
    (match (try Some (definition declarations id args) with Json.Error _ -> None) with
     | Some (Atoms (_::_::_ as atoms)) -> List.concat_map (atom_arms declarations (id::seen)) atoms
     | Some (Atoms [Named _ as inner]) -> atom_arms declarations (id::seen) inner
     | _ -> [a])
  | a -> [a]
let union_arms declarations atoms =
  List.sort_uniq compare (List.concat_map (atom_arms declarations []) atoms)
(* The alternatives a type stands for, each declaration it names unfolded,
   through unions, into its definition's: `Node` is a union of node kinds. *)
let rec unfolded_arms declarations seen t = match t with
  | Atoms atoms -> List.concat_map (fun a -> match a with
    | Named (id,args) when not (List.mem id seen) ->
      (match (try Some (definition declarations id args) with Json.Error _ -> None) with
       | Some d -> unfolded_arms declarations (id::seen) d
       | None -> [Atoms [a]])
    | a -> [Atoms [a]]) atoms
  | Union ts -> List.concat_map (unfolded_arms declarations seen) ts
  | Rigid _ | Meet _ -> [t]
(* Whether the lowering dispatches a method call on its object in one node
   (Lean's `Lowering.dispatchesCall`), which no bounded node rule admits:
   the object's claim, its declarations unfolded (`unfolded_arms`), has
   several alternatives, and every actual is a name or a literal. Lean
   dispatches only where the callee's claim has several labels too, or the
   object has no primitive arm, not every alternative is a host holding the
   member, and the alternatives do not all read the member at one row, so a
   call this answers true for but Lean does not dispatch is proposed
   unbounded, which Lean accepts. A union of arrays none of which owns the
   member, the callee claimed at one atom, is not dispatched: each
   alternative reads the member from the one array prototype, at one row
   (Lean's `Lowering.sharedFieldRow`). *)
let dispatches_call declarations (object_claim:ty) (k:key) (member_claim:ty option) args =
  let arms = List.sort_uniq compare (unfolded_arms declarations [] object_claim) in
  let prototype_read = function
    | Atoms [Shape {elements=Some _; fields; _}] -> not (List.exists (fun (f:field) -> f.name = k) fields)
    | _ -> false in
  plain_actuals args
  && List.length arms > 1
  && not ((match member_claim with Some (Atoms [_]) -> true | _ -> false) && List.for_all prototype_read arms)
(* `ToBoolean` of every value of an atom, through the declaration it names:
   a declaration all of whose arms settle it one way (a named union of
   records, always truthy) settles it so. *)
let rec atom_truthiness declarations seen = function
  | Named (id,args) when not (List.mem id seen) ->
    (match (try Some (definition declarations id args) with Json.Error _ -> None) with
     | Some (Atoms (_::_ as atoms)) ->
       (match List.sort_uniq compare (List.map (atom_truthiness declarations (id::seen)) atoms) with
        | [answer] -> answer
        | _ -> None)
     | _ -> None)
  | a -> truthiness a
(* The part of a type a truthiness test answering [truth] leaves, an atom
   naming a declaration dropped where all its values answer the other way. *)
let truthy_refine declarations truth t = match t with
  | Atoms xs -> truthy_slice truth (Atoms (List.filter (fun a ->
      atom_truthiness declarations [] a <> Some (not truth)) xs))
  | t -> truthy_slice truth t
let rec discriminate ?(seen = []) bounds declarations t key slice =
  match declared_head declarations [] t with
  | Atoms atoms ->
    let atoms = union_arms declarations atoms in
    (* A declaration whose definition is a union with intersection arms is
       its definition's arms, each discriminated. *)
    let unions = List.filter_map (fun atom -> match atom with
      | Named (id,args) when not (List.mem id seen) ->
        (match (try Some (definition declarations id args) with Json.Error _ -> None) with
         | Some (Union _ as u) -> Some (atom,id,u)
         | _ -> None)
      | _ -> None) atoms in
    let plain = List.filter (fun a -> not (List.exists (fun (b,_,_) -> b = a) unions)) atoms in
    let admits atom =
      match (try Some (field_type bounds declarations [] (Atoms [atom]) key) with Json.Error _ -> None) with
      | Some field -> slice field <> Atoms []
      | None -> true in
    let kept = List.filter admits plain in
    let parts = List.map (fun (_,id,u) -> discriminate ~seen:(id :: seen) bounds declarations u key slice) unions in
    if unions = [] then (if List.length kept = List.length atoms then t else Atoms kept)
    else if List.length kept = List.length plain && parts = List.map (fun (_,_,u) -> u) unions then t
    else List.fold_left union (Atoms kept) parts
  (* A union's arms each, an intersection arm dropped where its field holds
     nothing the slice keeps. *)
  | Union ts ->
    let parts = List.map (fun u -> discriminate ~seen bounds declarations u key slice) ts in
    if parts = ts then t else List.fold_left union (Atoms []) parts
  | Meet _ as m ->
    (match (try Some (field_type bounds declarations [] m key) with Json.Error _ -> None) with
     | Some field when slice field = Atoms [] -> Atoms []
     | _ -> t)
  | Rigid _ -> t
(* The arms of `t` whose object may still be of them once the value of its
   field `key` answered `slice`: an arm is dropped only where it fixes the
   field, required, at a type none of whose values does. *)
let discriminate_fixed bounds declarations t key slice =
  match declared_head declarations [] t with
  | Atoms atoms ->
    let atoms = union_arms declarations atoms in
    let fixed atom = match (try Some (declared_head declarations [] (Atoms [atom])) with Json.Error _ -> None) with
      | Some (Atoms [Shape {fields;_}]) | Some (Atoms [Exact fields]) ->
        List.exists (fun (f:Semantic.field) -> f.name = key && not f.optional) fields
      | _ -> false in
    let admits atom = not (fixed atom) ||
      (match (try Some (field_type bounds declarations [] (Atoms [atom]) key) with Json.Error _ -> None) with
       | Some field -> slice field <> Atoms []
       | None -> true) in
    let kept = List.filter admits atoms in
    if List.length kept = List.length atoms then t else Atoms kept
  | Rigid _ | Union _ | Meet _ -> t
(* An immutable binding declared at a named union is held at the union's
   arms, the same values: a guard then keeps or drops each arm, and a read
   splits on them. Lean checks the declared type below the arms on the edge
   from the declaration. *)
let arms declarations t = match t with
  | Atoms [Named _] ->
    (match (try Some (declared_head declarations [] t) with Json.Error _ -> None) with
     | Some (Atoms (_::_::_ as atoms)) -> Atoms atoms
     | _ -> t)
  | _ -> t
(* The arms an immutable binding's object literal may be of, as TypeScript
   narrows a declared union on its initialization (the assignment-reduced
   type): an arm the literal's keys or literal-valued members rule out is
   dropped, the arm the literal is built at stays. A proposal: Lean checks
   the initializer against what is kept. *)
let assigned_arms declarations t (init:expr) = match t,init.node with
  | Atoms (_::_::_ as atoms),Alloc members ->
    (match List.filter (fun a -> discriminated_record declarations (Atoms [a]) members <> None) atoms with
     | [] -> t
     | kept -> Atoms kept)
  | _ -> t
(* What a slot holds after a write of a value of type [t] under [contract],
   as TypeScript narrows a declared type on assignment: a primitive value at
   its own type; any other at the contract's arms, those the written literal
   [init] rules out dropped and a nullish arm dropped where the value's type
   excludes it. So a read sees the declared members, an optional field
   included, on every path. A proposal: Lean checks the written value below
   it on the edge out of the write. *)
let slot_holds declarations contract t (init:expr option) =
  if Environment.knowable t then t
  else
    let declared = arms declarations contract in
    let declared = match init with Some e -> assigned_arms declarations declared e | None -> declared in
    match (try flat_atoms declarations t with Json.Error _ -> None) with
    | Some (_::_ as atoms) -> Environment.observed_contents declared (Atoms atoms)
    | _ -> declared
(* The keys a key's type names, each a singleton: a string, a number's
   `ToString` or a symbol. Empty where it names a family (every string, every
   number, every symbol) or anything else. *)
let literal_keys declarations t =
  let atoms = try Option.value ~default:[] (flat_atoms declarations t) with Json.Error _ -> [] in
  let key = function
    | StrLit k -> Some (Name k)
    | NumLit bits -> Option.map (fun k -> Name k) (number_key bits)
    | SymbolLit i -> Some (Key i)
    | _ -> None in
  let keys = List.filter_map key atoms in
  if atoms <> [] && List.length keys = List.length atoms then List.sort_uniq compare keys else []
(* An open record: a plain object whose keys its type does not bound, which
   may be an array carrying other keys. *)
let open_record_atom = function
  | Shape {elements=None;calls=[];_} -> true
  | _ -> false
