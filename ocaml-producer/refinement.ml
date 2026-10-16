open Semantic
open Environment
open Source
open Type_queries
open Proposal_diagnostics

let primitive_shape shape = List.mem shape ["string";"number";"bigint";"symbol";"undefined";"boolean"]
let rec rigid_arm = function Rigid _ -> true | Union ts -> List.exists rigid_arm ts | _ -> false
(* Keep the atoms of a `typeof` test's shape where it holds, and the others
   where it fails. *)
let any_function = Atoms [Callable;Ctors ([],[])]
let rec typeof_slice shape holds = function
  | Atoms xs when not (List.mem Top xs) ->
    let has = function
      (* `Array.isArray`: an array owns its store; an open record may be an
         array carrying other keys, and stays on both arms. *)
      | Shape s when shape="array" ->
        if s.elements<>None then Some true else if s.calls<>[] then Some false else None
      | Top | Named _ when shape="array" -> None
      | _ when shape="array" -> Some false
      (* `"object"`: null, or an object without call code. *)
      | Nul when shape="object" -> Some true
      | Shape s when shape="object" -> Some (s.calls=[])
      | Exact _ when shape="object" -> Some true
      | Num | NumLit _ -> Some (shape="number") | Str | StrLit _ -> Some (shape="string")
      | True | False -> Some (shape="boolean") | Undef -> Some (shape="undefined")
      | Bigint | BigintLit _ -> Some (shape="bigint") | Symbol | SymbolLit _ -> Some (shape="symbol")
      | Shape s -> Some (shape="function" && s.calls<>[])
      | Exact _ -> Some false
      (* A class is a function to `typeof`. *)
      | Ctors _ | Callable -> Some (shape="function")
      | Nul -> Some false
      (* A declaration's shape is not known here: it stays on both arms. No
         value is an argument pack. *)
      | Top | Named _ -> None in
    Atoms (List.filter (fun a -> match has a with
      | Some result -> result = holds | None -> true) xs)
  (* `unknown`, where a test naming one primitive family holds: that
     family, whatever the value was (a caught value, say); where
     `typeof x === "function"` holds, a function: one invocable, or a class
     (`Function`, of no known signature). *)
  | Atoms _ when holds ->
    (match shape with
     | "string" -> Atoms [Str] | "number" -> Atoms [Num] | "bigint" -> Atoms [Bigint]
     | "symbol" -> Atoms [Symbol] | "undefined" -> Atoms [Undef] | "boolean" -> bool
     | "function" -> any_function
     | _ -> Atoms [Top])
  (* A type parameter's value, where a test naming one primitive family
     holds: that family, as for `unknown` (TypeScript's `T & number`, of
     which the model states the `number`). Where `typeof x === "function"`
     holds, the meet of the parameter with a function, `T & Function`. *)
  | Rigid _ when holds && primitive_shape shape ->
    typeof_slice shape holds (Atoms [Top])
  | Rigid _ as t when holds && shape = "function" -> Meet (t,[any_function])
  (* A union's arms each; an intersection's values are its principal's, so
     it goes where none of those can. *)
  | Union ts -> List.fold_left union (Atoms []) (List.map (typeof_slice shape holds) ts)
  | Meet (t,_) when typeof_slice shape holds t = Atoms [] -> Atoms []
  | t -> t
(* Where `Array.isArray` holds, an open record's arm and `unknown`'s are an
   array of the built-ins: record types and `unknown` are of values meeting the
   array invariant, so one owning an array's store holds a possibly sparse
   store of `unknown` and `Array.prototype` (Lean's `arraySlice`). Such arms
   become `sparse ReadonlyArray<unknown>`; an array arm stays; a type
   parameter's arm, of which the invariant says nothing, stays as it is. *)
let any_array = array {required=[];optional_elements=[];rest=Some top;readonly=true;presence=Sparse}
let array_slice declarations t =
  let sliced = typeof_slice "array" true t in
  let rec plain = function
    | Atoms _ -> true | Union ts -> List.for_all plain ts | Rigid _ | Meet _ -> false in
  if not (plain sliced) then sliced else
  let atoms = flat_atoms declarations sliced in
  if not (List.mem Top atoms || List.exists open_record_atom atoms) then sliced
  else match typeof_slice "array" true (Atoms atoms) with
    | Atoms kept -> union (ground (List.filter (fun a -> a <> Top && not (open_record_atom a)) kept)) any_array
    | _ -> sliced
(* Keep the atoms that may own the key where `key in o` held, and those that
   may lack it where it failed: a record's required field is owned, a fresh
   literal's keys are exactly its fields', and a primitive owns none. *)
(* A plain record whose optional key was found present: the key is a field
   of it from then on, since an object's keys are fixed at its allocation.
   A dictionary holds no prototype, so a key found on it is its own, a view
   at the index type. Lean checks the promoted record against the tested one
   (`promote`). *)
let present key =
  let promote = List.map (fun (f:Semantic.field) ->
    if f.name = Name key && f.optional then {f with optional=false} else f) in
  function
  | Shape ({calls=[];elements=None;indexes=[];_} as s) -> Shape {s with fields=promote s.fields}
  | Shape ({calls=[];elements=None;indexes=_::_;fields} as s)
    when not (List.exists (fun (f:Semantic.field) -> f.name = Name key) fields) ->
    (match index_for s (Name key) with
     | Some i -> Shape {s with fields=fields @ [{name=Name key;optional=false;read=i.value;write=None;
         host=false;receivers=[]}]}
     | None -> Shape s)
  | Exact fields -> Exact (promote fields)
  | a -> a
let key_slice key holds = function
  | Atoms xs when not (List.mem Top xs) ->
    let field_of fields = List.find_opt (fun (f:Semantic.field) -> f.name = Name key) fields in
    let has = function
      | Shape s -> (match field_of s.fields with
        | Some f when not f.optional -> Some true | _ -> None)
      | Exact fields -> (match field_of fields with
        | Some f -> if f.optional then None else Some true
        (* A class instance may inherit the key from its prototype. *)
        | None -> if List.exists (fun (f:Semantic.field) -> f.name = Name proto_key) fields
          then None else Some false)
      | Ctors _ | Callable | Named _ | Top -> None
      | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _
      | Bigint | Symbol | BigintLit _ | SymbolLit _ -> Some false in
    Atoms (List.filter_map (fun a -> match has a with
      | Some result -> if result = holds then Some a else None
      | None -> Some (if holds then present key a else a)) xs)
  | t -> t
(* Whether every record arm names the field. Read-result observations admit
   optional fields; presence-dependent refinement requires a required field. *)
let record_field ?(allow_optional=false) declarations t field =
  let rec has seen t = match (try Some (declared_head declarations seen t) with Json.Error _ -> None) with
    | Some (Atoms (_::_ as atoms)) -> List.for_all (function
        | Shape {fields;calls=[];elements=None;indexes=[]} | Exact fields ->
          List.exists (fun (f:Semantic.field) -> f.name = Name field && (allow_optional || not f.optional)) fields
        | Named (id,_) as atom when not (List.mem id seen) -> has (id::seen) (Atoms [atom])
        | _ -> false) atoms
    | _ -> false in
  has [] t
(* A guard on a field of an immutable binding's object: what the field holds
   is known until a step may write it. *)
let refine_field bounds declarations env name field refine =
  (* A read of an optional key that gave something other than `undefined`
     found the key present: the object's record arms have it from then on
     (Lean's `promote`, through the read's optional link). *)
  let env = match List.assoc_opt name env with
    | Some (Value t) when refine (Atoms [Undef]) = Atoms [] ->
      let rec arms seen t = match declared_head declarations seen t with
        | Atoms atoms -> List.concat_map (function
            | Named (id,_) as atom when not (List.mem id seen) -> arms (id::seen) (Atoms [atom])
            | a -> [a]) atoms
        | _ -> [] in
      let atoms = try arms [] t with Json.Error _ -> [] in
      let names = function
        | Shape {fields;calls=[];elements=None;indexes=[]} | Exact fields ->
          List.exists (fun (f:Semantic.field) -> f.name = Name field) fields
        | _ -> false in
      let optional = function
        | Shape {fields;_} | Exact fields ->
          List.exists (fun (f:Semantic.field) -> f.name = Name field && f.optional) fields
        | _ -> false in
      if atoms <> [] && List.for_all names atoms && List.exists optional atoms
      then refine_value env name (fun _ -> Atoms (List.map (present field) atoms))
      else env
    | _ -> env in
  match List.assoc_opt name env with
  | Some (Value t) when record_field ~allow_optional:true declarations t field ->
    let key = field_key name field in
    let current = match List.assoc_opt key env with
      | Some (Value c) -> Some c
      | _ -> (try Some (field_type bounds declarations [] t (Name field)) with Json.Error _ -> None) in
    (match current with
     | Some c -> fact env key (field_type bounds declarations [] t (Name field)) (refine c)
     | None -> env)
  | _ -> env
let rec branch_with state ?(modules = fun _ -> None) ?(claimed = fun _ -> None) bounds declarations env cond truth =
  let branch = branch_with state ~modules ~claimed bounds declarations in
  let refine_field = refine_field bounds declarations in
  match cond.node with
  | Not e -> branch env e (not truth)
  (* A name as a condition is tested for truthiness; a Boolean's slice is
     its literal. *)
  | Id name -> refine_value env name (truthy_slice truth)
  (* Where some arm leaves the field optional or unnamed, so that nothing is
     known of what it holds, the test keeps the arms whose field may answer
     so (Lean's `fieldSlice` through the read's link): `IteratorResult` by
     `done`. *)
  | Read ({node=Id name;_},Name field) ->
    let env = match List.assoc_opt name env with
      | Some (Value t) when not (record_field declarations t field) ->
        refine_value env name (fun t -> discriminate_fixed bounds declarations t (Name field) (truthy_slice truth))
      | _ -> env in
    refine_field env name field (truthy_slice truth)
  (* A true `&&` (a false `||`) established both operands so; the other
     answer came from either operand, the right one after the left answered
     the first way, and holds what either established. *)
  | Logical (conjunction,a,b) when truth = conjunction -> branch (branch env a truth) b truth
  | Logical (_,a,b) ->
    let either = branch env a truth and later = branch (branch env a (not truth)) b truth in
    (* A field's contents are known where both paths know them. *)
    List.filter_map (fun (n,x) -> match x,List.assoc_opt n later with
      | Value l,Some (Value r) -> Some (n,Value (union l r))
      | Storage (contract,l),Some (Storage (_,r)) -> Some (n,holding contract (union l r))
      | Local (contract,l),Some (Local (_,r)) -> Some (n,Local (contract,union l r))
      | _ when is_field n -> None
      | _ -> Some (n,x)) either
  | TypeofTest (shape,equal,{node=Id name;_}) ->
    (if truth = equal && shape <> "array" && shape <> "object" then match List.assoc_opt name env with
      | Some b when rigid_arm (binding_type b) || binding_type b = top ->
        state.shape_tests := (name,shape) :: !(state.shape_tests)
      | _ -> ());
    let env = refine_value env name (if shape = "array" && truth = equal then array_slice declarations
      else typeof_slice shape (truth = equal)) in
    env
  | HasKey ({node=Literal (LString key);_},{node=Id name;_}) ->
    refine_value env name (key_slice key truth)
  (* `x instanceof C` is the same test of the class's key: primitives and
     fresh literals lack it; any other arm may have it or not. *)
  | InstanceTest (key,{node=Id name;_},_) ->
    (match List.assoc_opt name env with
     | Some b when truth && (match binding_type b with Atoms xs -> List.mem Top xs | _ -> false) ->
       state.unknown_instance_tests := name :: !(state.unknown_instance_tests)
     | _ -> ());
    refine_value env name (key_slice key truth)
  | TypeofTest (shape,equal,{node=Read ({node=Id name;_},Name field);_}) ->
    refine_field env name field (typeof_slice shape (truth = equal))
  (* `x == null` holds of null and undefined alike. *)
  | Equality ((LooseEqual | LooseUnequal as op),{node=Id name;_},{node=Literal (LNull | LUndefined);_})
  | Equality ((LooseEqual | LooseUnequal as op),{node=Literal (LNull | LUndefined);_},{node=Id name;_}) ->
    let equal = truth=(op=LooseEqual) in
    refine_value env name (fun t ->
      if equal then union (restrict ~declarations Nul true t) (restrict ~declarations Undef true t)
      else restrict ~declarations Undef false (restrict ~declarations Nul false t))
  | Equality ((LooseEqual | LooseUnequal as op),{node=Read ({node=Id name;_},Name field);_},{node=Literal (LNull | LUndefined);_})
  | Equality ((LooseEqual | LooseUnequal as op),{node=Literal (LNull | LUndefined);_},{node=Read ({node=Id name;_},Name field);_}) ->
    let equal = truth=(op=LooseEqual) in
    refine_field env name field (fun t ->
      if equal then union (restrict ~declarations Nul true t) (restrict ~declarations Undef true t)
      else restrict ~declarations Undef false (restrict ~declarations Nul false t))
  (* A comparison with a singleton, a literal or a name or field holding one,
     narrows the other operand where it is a name, or a field of a name's
     object, and that object's arms, on both outcomes. Where it holds, one
     with a name or field holding one of several singletons narrows the
     other to the values that may equal one of them. *)
  | Equality ((StrictEqual | StrictUnequal as op),l,r) ->
    let equal = truth=(op=StrictEqual) in
    (* An immutable name, or a field of one: read again where Lean tests it
       against each singleton, which nothing between has changed. *)
    let immutable n = match List.assoc_opt n env with
      | Some (Value _ | Local _) -> true | Some (Storage _) -> false | None -> modules n <> None in
    let reread (e:expr) = match e.node with
      | Id n | Read ({node=Id n;_},_) -> immutable n
      | _ -> false in
    (* An operand evaluated once into a slot of its own, a call say: Lean
       splits it there, against an immutable name. *)
    let saved (e:expr) = match e.node with
      | Literal _ | Id _ | Read ({node=Id _;_},_) -> false
      | _ -> true in
    let values (e:expr) = Option.bind (match e.node with
      | Literal lit -> Some (literal_type lit)
      | Id n -> (match List.assoc_opt n env with Some b -> Some (binding_type b) | None -> modules n)
      | Read ({node=Id n;_},Name f) ->
        (match List.assoc_opt (field_key n f) env,List.assoc_opt n env with
         | Some b,_ -> Some (binding_type b)
         | None,Some b -> (try Some (field_type bounds declarations [] (binding_type b) (Name f)) with Json.Error _ -> None)
         (* A module value's field, an enum member: its declared type. *)
         | None,None -> Option.bind (modules n) (fun t ->
             try Some (field_type bounds declarations [] t (Name f)) with Json.Error _ -> None))
      | _ -> claimed e.pos) (fun t -> match singleton_atom t,t with
        | Some a,_ -> Some ((fun t -> restrict ~declarations a equal t),true)
        | None,Atoms (_::_ as atoms) when equal
            && List.for_all (fun a -> singleton_atom (Atoms [a]) <> None) atoms ->
          Some ((fun t -> combine (List.map (fun a -> restrict ~declarations a true t) atoms)),false)
        | _ -> None) in
    (* What a field holds is known from a test against one singleton, whose
       saved read Lean observes; against several, from Lean's test of each,
       one read at a time, where both operands are read again there or the
       other is saved and this one is an immutable name. *)
    let narrow env (operand:expr) other = match values other,operand.node with
      | None,_ -> env
      (* Against a singleton, this operand is the one Lean tests: it learns
         nothing of the other's several values. *)
      | Some (_,false),_ when (match values operand with Some (_,true) -> true | _ -> false) -> env
      | Some (_,false),Id name when not (immutable name && (reread other || saved other)) -> env
      | Some (_,false),Read _ when not (reread operand && reread other) -> env
      | Some (_,true),Read _ when saved other -> env
      | Some (slice,_),Id name -> refine_value env name slice
      | Some (slice,_),Read ({node=Id name;_},key) ->
        let env = refine_value env name (fun t -> discriminate bounds declarations t key slice) in
        (match key with
         | Name field -> refine_field env name field slice
         | _ -> env)
      | Some _,_ -> env in
    narrow (narrow env l r) r l
  | _ -> env

