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
        (* An indexed dictionary owns no prototype, which an array owns
           (Lean's `not_array_of_indexed`). *)
        if s.elements<>None then Some true else if s.calls<>[] || s.indexes<>[] then Some false else None
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
(* A declaration's arm stays on both arms of a `typeof` test, its shape not
   known there. Where the test decides some arm of its definition, the
   definition is sliced instead, arm by arm: `Key = string | { sym: number }`
   where `typeof k === "string"` fails is `{ sym: number }`. A type
   parameter's or an intersection's arm in a definition is sliced as
   `typeof_slice` slices it, so it stays where the test cannot decide it. *)
let typeof_refine declarations shape holds t =
  let sliced = typeof_slice shape holds t in
  let rec named = function
    | Atoms xs -> List.exists (function Named _ -> true | _ -> false) xs
    | Union ts -> List.exists named ts | Rigid _ | Meet _ -> false in
  if not (named sliced) then sliced else
  let rec unfold seen = function
    | Atoms xs -> List.fold_left union (Atoms []) (List.map (function
        | Named (id,args) as a when not (List.mem id seen) ->
          (match definition declarations id args with
           | body -> unfold (id::seen) body
           | exception Json.Error _ -> Atoms [a])
        | a -> Atoms [a]) xs)
    | Union ts -> List.fold_left union (Atoms []) (List.map (unfold seen) ts)
    | t -> t in
  let unfolded = unfold [] sliced in
  let resliced = typeof_slice shape holds unfolded in
  if resliced = unfolded then sliced else resliced
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
  match flat_atoms declarations sliced with
  | None -> sliced
  | Some atoms ->
  (* The definitions' arms are sliced first: an indexed dictionary's arm,
     which owns no array, leaves before an open record's adds the
     built-ins' array (Lean's `arrayRefine`). *)
  match typeof_slice "array" true (Atoms atoms) with
  | Atoms kept when List.mem Top kept || List.exists open_record_atom kept ->
    union (ground (List.filter (fun a -> a <> Top && not (open_record_atom a)) kept)) any_array
  | Atoms kept when List.length kept < List.length atoms -> ground kept
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
  (* A writable optional key becomes an invariant field only of a record whose
     objects are ordinary: one naming an invariant field already, or a fresh
     literal's. Otherwise a host object might hold it, and it is a view. *)
  let ordinary fields = List.exists (fun (f:Semantic.field) -> f.write <> None && not f.optional) fields in
  let as_view = List.map (fun (f:Semantic.field) ->
    if f.name = Name key && f.optional then {f with optional=false; write=None} else f) in
  (* A record holding a generic method has no claim but its declaration's
     (Lean allocates the method's scheme with the declaration): an arm of it
     stays as declared, and what a test found of its readonly optional key
     is known only as the field's contents. *)
  let generic (f:Semantic.field) = match f.read with
    | Atoms [Shape {calls=(_::_ as calls);_}] ->
      List.exists (fun (c:Semantic.signature) -> c.quantified <> []) calls
    | _ -> false in
  let declared_only fields = List.exists generic fields && List.exists (fun (f:Semantic.field) ->
    f.name = Name key && f.optional && f.write = None) fields in
  function
  | Shape ({calls=[];elements=None;indexes=[];_} as s) when declared_only s.fields -> Shape s
  | Shape ({calls=[];elements=None;indexes=[];_} as s) ->
    Shape {s with fields=(if ordinary s.fields then promote s.fields else as_view s.fields)}
  | Shape ({calls=[];elements=None;indexes=_::_;fields} as s)
    when not (List.exists (fun (f:Semantic.field) -> f.name = Name key) fields) ->
    (match index_for s (Name key) with
     | Some i -> Shape {s with fields=fields @ [{name=Name key;optional=false;read=i.value;write=None;
         host=false;receivers=[];stable=false}]}
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
        (* A dictionary's string index reaches every string key: a read of a
           key it lacks gives `undefined` (Lean's `optionalOperand`). *)
        | Shape ({calls=[];elements=None;indexes=_::_;_} as s) when allow_optional ->
          index_for s (Name field) <> None
        | Named (id,args) when not (List.mem id seen) ->
          (try has (id::seen) (definition declarations id args) with Json.Error _ -> false)
        | _ -> false) atoms
    | Some (Union ts) -> ts <> [] && List.for_all (has seen) ts
    | _ -> false in
  has [] t
(* Whether every record arm states the field a stable member (HOST-FAMILIES.md,
   "Stable keys"): a required member its declaration document states stable. *)
let stable_member declarations t field =
  let rec has seen t = match (try Some (declared_head declarations seen t) with Json.Error _ -> None) with
    | Some (Atoms (_::_ as atoms)) -> List.for_all (function
        | Shape {fields;calls=[];elements=None;indexes=[]} ->
          List.exists (fun (f:Semantic.field) -> f.name = Name field && f.stable && not f.optional) fields
        | Named (id,args) when not (List.mem id seen) ->
          (try has (id::seen) (definition declarations id args) with Json.Error _ -> false)
        | _ -> false) atoms
    | Some (Union ts) -> ts <> [] && List.for_all (has seen) ts
    | _ -> false in
  has [] t
(* Whether a path entry survives a step that may write cells: each member
   of the path stable in every arm of what its receiver holds, the root's
   type or the refinement its prefix's entry states (Lean's stable links,
   `HeapExpressionRules.withStable`). *)
let stable_path declarations env n =
  is_path n &&
  match String.split_on_char '\001' (field_of n) with
  | "" :: fields ->
    (match List.assoc_opt (owner n) env with
     | Some (Value root | Local (_,root)) ->
       let rec walk t prefix = function
         | [] -> true
         | f :: rest ->
           stable_member declarations t f &&
           let here = prefix @ [f] in
           let next = match List.assoc_opt (path_key (owner n) here) env with
             | Some (Value t') -> Some t'
             | _ -> (try Some (field_type [] declarations [] t (Name f)) with Json.Error _ -> None) in
           (match next with Some t' -> walk t' here rest | None -> rest = [])
       in walk root [] fields
     | _ -> false)
  | _ -> false
(* A guard on a field of an immutable binding's object: what the field holds
   is known until a step may write it. *)
(* The atoms of a field's type some of the known contents may be: a
   primitive atom meets a content atom equal to it, a singleton meets its
   family; any other atom, or contents not all primitive, is kept. *)
let contents_meet field known = match field,known with
  | Atoms fs,Atoms ks ->
    let primitive = function
      | Nul | Undef | True | False | Str | StrLit _ | Num | NumLit _ -> true | _ -> false in
    if not (List.for_all primitive ks) then field else
    let meets f k = f = k || (match f,k with
      | StrLit _,Str | Str,StrLit _ | NumLit _,Num | Num,NumLit _ -> true | _ -> false) in
    Atoms (List.filter (fun f -> not (primitive f) || List.exists (meets f) ks) fs)
  | _ -> field
let refine_field ?(answer = false) bounds declarations env name field refine =
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
      let promoted = List.map (present field) atoms in
      (* Where no arm changes (a readonly key stays optional), the binding
         keeps its declared type. *)
      if atoms <> [] && List.for_all names atoms && List.exists optional atoms && promoted <> atoms
      then refine_value env name (fun _ -> Atoms promoted)
      else env
    | _ -> env in
  match List.assoc_opt name env with
  | Some (Value t) when record_field ~allow_optional:true declarations t field ->
    let key = field_key name field in
    (* A field declared at a named union of primitives holds one of its
       atoms: the definition's, so that a test slices them. *)
    let flat f =
      let rec plain = function
        | Atoms _ -> true | Union ts -> List.for_all plain ts | Rigid _ | Meet _ -> false in
      let primitive = function
        | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _
        | Bigint | Symbol | BigintLit _ | SymbolLit _ -> true
        | _ -> false in
      if plain f then (try (match flat_atoms declarations f with
          | Some (_::_ as atoms) when List.for_all primitive atoms -> Atoms (List.sort_uniq compare atoms)
          | _ -> f)
        with Json.Error _ -> f) else f in
    let current = match List.assoc_opt key env with
      | Some (Value c) -> Some c
      | _ -> (try Some (flat (field_type bounds declarations [] t (Name field))) with Json.Error _ -> None) in
    (match current with
     | Some c ->
       let contents = refine c in
       (* A test leaving one of a declared union's primitive arms (`Json`
          at `=== "a"`): the arms the test keeps of the definition's, where
          they are all primitive, a fact Lean records of the field. *)
       let contents =
         let primitive = function
           | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _
           | Bigint | Symbol | BigintLit _ | SymbolLit _ -> true
           | _ -> false in
         let rec plain = function
           | Atoms _ -> true | Union ts -> List.for_all plain ts | Rigid _ | Meet _ -> false in
         if not (plain c) then contents else
         match (try flat_atoms declarations c with Json.Error _ -> None) with
         | Some (_::_ as atoms) ->
           (match refine (Atoms (List.sort_uniq compare atoms)) with
            | Atoms (_::_ as kept) as sliced when List.for_all primitive kept -> sliced
            | _ -> contents)
         | _ -> contents in
       let env = fact ~answer:(answer && contents <> c) env key (field_type bounds declarations [] t (Name field)) contents in
       (* The object's arms whose field the contents rule out are dropped
          (Lean's `factSlice`): a primitive arm none of whose atoms meets one
          of the contents. Successive tests narrow the contents, so their
          exclusions combine. *)
       (match List.assoc_opt key env with
        | Some (Value known) -> refine_value env name (fun t ->
            discriminate_fixed bounds declarations t (Name field) (fun f ->
              let rec plain = function
                | Atoms _ -> true | Union ts -> List.for_all plain ts | Rigid _ | Meet _ -> false in
              let f = if plain f then (try (match flat_atoms declarations f with Some atoms -> Atoms atoms | None -> f)
                with Json.Error _ -> f) else f in
              contents_meet f known))
        | _ -> env)
     | None -> env)
  | _ -> env
(* What a call of a guard promises of its actual, a name: where a type guard
   returned `true` (`asserts` false), or wherever an assertion function
   returned (`asserts` true), the name holds the promise's type, the result of
   a promise signature of the callee's type. The callee is any expression: a
   name (`resolve` gives its type), a member or namespace read, whose claimed
   type `claimed` gives. Of several promise signatures (overloads), those whose
   parameters admit the actuals' known types. Lean checks the signature at the
   call (`PromiseCalls.promiseCall_sound`). *)
let promise_refine ?(claimed = fun _ -> None) resolve declarations env (cond:expr) asserts =
  let call = match cond.node with
    | Call (callee,None,args,[],[]) -> Some (callee,args)
    | Invoke (callee,args,[],[]) -> Some (callee,args)
    | _ -> None in
  match call with
  | None -> env
  | Some (callee,args) ->
    let callee_type = match callee.node with
      | Id name -> (match resolve name with Some t -> Some t | None -> claimed callee.pos)
      | _ -> claimed callee.pos in
    let actual (a:expr) = match a.node with
      | Id name -> resolve name
      | _ -> claimed a.pos in
    let promises = match Option.map (fun t ->
        try Some (declared_head declarations [] t) with Json.Error _ -> None) callee_type with
      | Some (Some (Atoms [Shape {calls;_}])) -> List.filter_map (fun (s:Semantic.signature) ->
          match s.call_effect.promise,asserts with
          | Some (Guards p),false | Some (Asserts p),true -> Some (p,s)
          | _ -> None) calls
      | _ -> [] in
    let applicable (_,(s:Semantic.signature)) =
      List.length args <= List.length s.params &&
      List.for_all2 (fun (a:expr) param -> match actual a with
        | Some t -> plausible_subtype t param
        | None -> true) args (List.filteri (fun i _ -> i < List.length args) s.params) in
    let chosen = match promises with
      | [_] -> promises
      | _ -> List.filter applicable promises in
    (match chosen with
     | (p,s) :: _ -> (match List.nth_opt args p with
       | Some {node=Id name;_} -> refine_value env name (fun _ -> s.result)
       | _ -> env)
     | [] -> env)
let rec branch_with state ?(modules = fun _ -> None) ?(claimed = fun _ -> None) bounds declarations env cond truth =
  let branch = branch_with state ~modules ~claimed bounds declarations in
  let refine_field ?answer = refine_field ?answer bounds declarations in
  match cond.node with
  | Not e -> branch env e (not truth)
  (* `a, b` as a condition: `a` runs, then `b` is the test. *)
  | Comma (_,b) -> branch env b truth
  (* A name as a condition is tested for truthiness; a Boolean's slice is
     its literal. *)
  (* An immutable binding's falsy outcome drops a named union of records,
     all of whose values are truthy. A mutable local's or a cell's keeps it:
     its outcomes join other edges into it, a loop's exit those of the
     guards after it, along which Lean keeps the named union, so the join's
     proposal holds the named union where an incoming edge does. *)
  | Id name ->
    let refine = match List.assoc_opt name env with
      | Some (Storage _ | Local _) -> truthy_slice truth
      | _ -> truthy_refine declarations truth in
    refine_value env name refine
  (* Where some arm leaves the field optional or unnamed, so that nothing is
     known of what it holds, the test keeps the arms whose field may answer
     so (Lean's `fieldSlice` through the read's link): `IteratorResult` by
     `done`. *)
  (* A path of two members or more, tested for truthiness: what the test
     leaves of the read's value, which a read of the same path reads again. *)
  | Read ({node=Read _;_},Name _) when path_of env cond <> None ->
    refine_path env cond (claimed cond.pos) (truthy_refine declarations truth)
  | Read ({node=Id name;_},Name field) ->
    let current = claimed cond.pos in
    if path_of env cond <> None && (match current with Some t -> not (knowable t) | None -> false)
    then refine_path env cond current (truthy_refine declarations truth)
    else
    let env = match List.assoc_opt name env with
      | Some (Value t) when not (record_field declarations t field) ->
        refine_value env name (fun t -> discriminate_fixed bounds declarations t (Name field) (truthy_slice truth))
      | _ -> env in
    let env = refine_field ~answer:true env name field (truthy_slice truth) in
    refine_path env cond (claimed cond.pos) (truthy_refine declarations truth)
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
      else typeof_refine declarations shape (truth = equal)) in
    env
  (* A family guard's test of a name: its value, or its object's arms by
     their field, as Lean's slices leave them (`PromiseCalls.memberSlotSlice`,
     `memberFieldSlice`): where it answered `true`, each atom one of the tags
     may equal, kept as it is; where `false`, each atom less the tags'
     values, an arm whose field the tags' values cover dropped, and an arm of
     a generic declaration at its stable tag, partly covered, read at the
     rest of its tag (member-split). *)
  | TagMember (field,tags,tested) ->
    let atoms = List.filter_map (fun l -> singleton_atom (literal_type l)) tags in
    let rec passing t = match t with
      | Atoms xs -> Atoms (List.filter (fun x ->
          List.exists (fun a -> restrict ~declarations a true (Atoms [x]) <> Atoms []) atoms) xs)
      | Union ts -> List.fold_left union (Atoms []) (List.map passing ts)
      (* An intersection holds nothing where one operand holds nothing. *)
      | Meet (p,others) when List.exists (fun o -> passing o = Atoms []) (p :: others) -> Atoms []
      | Meet _ | Rigid _ -> t in
    (* A name's own value: each tag's values taken out in turn. An object's
       arm, by its field: dropped where one tag is every value the field
       holds, as Lean's field slice decides each tag in turn. *)
    let own t =
      if truth then passing t
      else List.fold_left (fun t a -> restrict ~declarations a false t) t atoms in
    let rest field = List.fold_left (fun t a -> restrict ~declarations a false t) field atoms in
    let through field =
      if truth then passing field
      else if rest field = Atoms [] then Atoms []
      else field in
    let field_of atom f = try Some (field_type bounds declarations [] (Atoms [atom]) (Name f)) with Json.Error _ -> None in
    let split f t =
      if truth then t else
      match (try Some (declared_head declarations [] t) with Json.Error _ -> None) with
      | Some (Atoms atoms) ->
        let arms = union_arms declarations atoms in
        (* An alias of one application is that application. *)
        let rec unalias seen atom = match atom with
          | Named (id,args) when not (List.mem id seen) ->
            (match (try Some (definition declarations id args) with Json.Error _ -> None) with
             | Some (Atoms [Named _ as inner]) -> unalias (id :: seen) inner
             | _ -> atom)
          | _ -> atom in
        let narrowed = List.map (fun arm -> match unalias [] arm with
          | Named (id,[_]) as applied when stable_member declarations (Atoms [applied]) f ->
            (match field_of applied f with
             | Some field ->
               let r = rest field in
               let candidate = Named (id,[r]) in
               if r <> field && r <> Atoms [] && field_of candidate f = Some r then candidate else arm
             | None -> arm)
          | _ -> arm) arms in
        if narrowed = arms then t else Atoms narrowed
      | _ -> t in
    let by_field f t = split f (discriminate bounds declarations t (Name f) through) in
    (* A name, where it is held; a path, through the read the test refined
       (HOST-FAMILIES.md, "A guard on any argument"). *)
    (match tested.node,field with
     | Id name,None -> refine_value env name own
     | Id name,Some f -> refine_value env name (by_field f)
     | _,None -> refine_path env tested (claimed tested.pos) own
     | _,Some f -> refine_path env tested (claimed tested.pos) (by_field f))
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
    refine_field ~answer:true env name field (if shape = "array" && truth = equal then array_slice declarations
      else typeof_refine declarations shape (truth = equal))
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
      (* A field of a path's value: the path's arms, as the read the test
         refined holds them. *)
      | Some (slice,_),Read (inner,key) when path_of env inner <> None ->
        refine_path env inner (claimed inner.pos) (fun t -> discriminate bounds declarations t key slice)
      | Some _,_ -> env in
    narrow (narrow env l r) r l
  | (Call _ | Invoke _) when truth ->
    promise_refine ~claimed (fun name -> match List.assoc_opt name env with
      | Some b -> Some (binding_type b)
      | None -> modules name) declarations env cond false
  | _ -> env

