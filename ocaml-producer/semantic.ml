(* Semantic types contain no solver state. More precise proposals do not mutate them.
   A rigid parameter remains distinct from any future inference/existential IDs. *)
(* How a footprint may change a location's contents (Lean's
   `Footprints.Change`): not at all, by an initialization of `null` or
   `undefined`, by a scalar's step (contents neither an object nor a store
   replaced by contents that are no store), as a store keeping every dense
   prefix, or arbitrarily; the chain `Keep < Init < Scalar < Grow < Any`. *)
type change = Keep | Init | Scalar | Grow | Any
(* A closed footprint (Lean's `Footprints.Closed`): the change a call may make,
   on normal return, to its entry heap's locations holding a value and to those
   holding an array store. On a value `Grow` is `Scalar`; on a store `Init`
   and `Scalar` are `Keep`. *)
type footprint = { on_value: change; on_store: change }
let top_footprint = {on_value=Any;on_store=Any}
let empty_footprint = {on_value=Keep;on_store=Keep}
let change_rank = function Keep -> 0 | Init -> 1 | Scalar -> 2 | Grow -> 3 | Any -> 4
let change_le a b = change_rank a <= change_rank b
let join_change a b = if change_le a b then b else a
let footprint_le a b =
  let on_value = function Grow -> Scalar | d -> d in
  let on_store = function Init | Scalar -> Keep | d -> d in
  change_le (on_value a.on_value) (on_value b.on_value) && change_le (on_store a.on_store) (on_store b.on_store)
(* A promise about the actual at a parameter. A promise signature's result is
   the promise's type, not the call's: a type guard's call is `true` or
   `false`, `true` leaving the actual at the result; an assertion function's
   returns `undefined`, leaving it there. *)
type promise = Guards of int | Asserts of int
(* What a signature guarantees beyond its contract (Lean's
   `CallEffects.Effect`): its footprint, an optional promise, whether a
   normal return's value has an array store the call allocated, and whether
   the footprint excepts the receiver's array store, which the call may
   change arbitrarily. *)
(* An index fact at a call's positions (Lean's `HeapKnowledge.IndexFact`, 0
   the receiver, i + 1 the i-th actual): an array index; the length of an
   array's store; an index at most that length, below it where strict; a safe
   integer; a linear fact `Σ c·t ≤ d` or `≠ d`, each term the value at a
   position or at the named data fields read from it in turn (its path), the
   length of the array store there, the length of the typed array
   there, or the length of the string there (Lean's `HeapKnowledge.Term`). *)
type term = Value_at of int * string list | Length_at of int * string list | View_at of int * string list
  | Str_length_at of int * string list
type index_fact = Index_at of int | Length_of of int * int | Bound_by of int * int * bool | Int_at of int
  | Linear_le of (term * int) list * int | Linear_ne of (term * int) list * int
  (* Where the named data fields read from the position do not give the
     value the tag names, `null` or `undefined`, the body holds
     (PROGRAM-TYPING.md, "Guarded clauses"). *)
  | Either of index_fact * index_fact
  | Guarded of int * string list * string * index_fact
  (* The value at the first position is what the array at the second holds
     at the index at the third, below its length (Lean's `IndexFact.element`). *)
  | Element of int * int * int
  (* For every index below the bound of the array the named data fields read
     from the position give, each body fact holds of the index, the element
     at it and its terms (PROGRAM-TYPING.md, "Quantified clauses"). *)
  | Every of int * string list * term * body_fact list
(* A variable of a quantified fact's body: the index, the element at it, or a term. *)
and body_var = Body_index | Body_elem | Body_project of string * string list | Body_term of term
and body_fact = Body_le of (body_var * int) list * int | Body_ne of (body_var * int) list * int
type call_effect = { footprint: footprint; promise: promise option; fresh: bool; receiver_store: bool; on_throw: bool;
  receiver_own: bool; fresh_object: bool;
  (* The kinds the receiver's present elements have where the call starts,
     and those a normal return of `true` leaves them with (Lean's
     `Effect.requires` and `Effect.elements`), in the wire's order. *)
  requires: string list option; elements: string list option;
  (* A precondition on the call's values (Lean's `Effect.pre`). *)
  pre: index_fact list;
  (* Facts a normal return states, at the return's positions: 0 the result,
     i + 1 the call's position i (Lean's `Effect.ensures`). Only a trusted
     signature states them. *)
  ensures: index_fact list;
  (* A normal return changed no old location but the receiver's store, which
     it grew (Lean's `Effect.receiverGrows`). Only a trusted signature states
     it. *)
  receiver_grows: bool;
  (* A normal return changed the heap as a typed array's element write may:
     no location holding no store, and no store's length; and, where
     "exact", the view's element at the index alone, to the value (Lean's
     `Effect.elementWrite`). Only a trusted signature states it. *)
  element_write: string option }
let footprint_effect footprint =
  {footprint;promise=None;fresh=false;receiver_store=false;on_throw=false;receiver_own=false;fresh_object=false;
   requires=None;elements=None;pre=[];ensures=[];receiver_grows=false;element_write=None}
(* An ordinary arrow's: every location may change. *)
let ordinary_effect = footprint_effect top_footprint
(* Heap preservation: no location may change. *)
let empty_effect = footprint_effect empty_footprint
let promise_effect promise = {(footprint_effect top_footprint) with promise=Some promise}

(* A bound function's effect (Lean's `Effect.drop`): the receiver it saved is
   not the receiver of a call of it, so an exception of the receiver's store
   is an exception of every location; its positions are not the target's, so
   it states no postcondition. *)
let bound_effect e = if e.receiver_store || e.receiver_own then
    {e with footprint=top_footprint; receiver_store=false; receiver_own=false; elements=None; ensures=[];
      receiver_grows=false}
  else {e with elements=None; ensures=[]; receiver_grows=false}
(* Whether a signature's result is the call's: one without a promise. *)
let plain_effect e = e.promise = None
(* A smaller footprint and the same promise, a fresh result where the other
   states one, and the receiver's store excepted only where the other excepts
   it or lets everything change, and a footprint on a throw where the other
   states one (Lean's `Effect.covers`). *)
let effect_covers a b = footprint_le a.footprint b.footprint && a.promise = b.promise &&
  (not b.fresh || a.fresh) &&
  (not a.receiver_store || (b.receiver_store && not b.receiver_own) || b.footprint = top_footprint) &&
  (not b.on_throw || a.on_throw) &&
  (not a.receiver_own || b.receiver_own || b.footprint = top_footprint) && (not b.fresh_object || a.fresh_object) &&
  (match a.requires, b.requires with
   | None, _ -> true | Some ka, Some kb -> List.for_all (fun k -> List.mem k ka) kb | Some _, None -> false) &&
  List.for_all (fun f -> List.mem f b.pre) a.pre &&
  List.for_all (fun f -> List.mem f a.ensures) b.ensures && (not b.receiver_grows || a.receiver_grows) &&
  (b.element_write = None || a.element_write = b.element_write) &&
  (match a.elements, b.elements with
   | _, None -> true | Some ka, Some kb -> List.for_all (fun k -> List.mem k kb) ka | None, Some _ -> false)

type array_presence = Dense | Readable | Sparse
let presence_name = function Dense -> "dense" | Readable -> "readable" | Sparse -> "sparse"
let presence_of_string = function
  | "dense" -> Dense | "readable" -> Readable | "sparse" -> Sparse
  | s -> invalid_arg ("invalid array presence: " ^ s)

type ty = Atoms of atom list | Rigid of rigid | Union of ty list
         (* An intersection whose operands are known only where it is
            applied or instantiated: in a declaration's equation one is a
            parameter of the declaration, `T & { readonly [k: string]: Json }`,
            or another declaration, and it is kept, its principal operand
            first, until the application: there it is the one object its
            operands describe where they are records (`Type_queries.definition`),
            and otherwise the whole intersection, with every operand retained. In a function's
            annotation, a binder met with other types (`T & U`, `T & "fixed"`)
            is claimed as the meet row of its operands (`Claims`). *)
         | Meet of ty * ty list
and rigid = { scope: int; index: int; spelling: string }
and atom = Nul | Undef | True | False | Num | Str | NumLit of int64 | StrLit of string | Top
         (* Every bigint; every symbol, an opaque value. *)
         | Bigint | Symbol
         (* One bigint: its canonical decimal integer. *)
         | BigintLit of string
         (* One symbol: the one the declaration document lists at this index,
            as a symbol key [Key] names it. *)
         | SymbolLit of int
         (* A class value: construct signatures, which `new` meets and no call
            does, and its static fields, own invariant fields of the class
            value. A signature's receiver is unused: `new` passes none. *)
         | Ctors of signature list * field list
         (* A value with call code of which no signature is known: nothing
            calls it. `Function` is it or a class value meeting no construct
            signature, `Ctors ([],[])`; `object` is those or an empty `Shape`. *)
         | Callable
         | Shape of shape
         (* A record whose own keys are exactly its fields' keys, as a fresh
            object literal's are: no other key, so no prototype. The bound is
            what lets it meet a dictionary, or a record whose optional fields
            it leaves out. *)
         | Exact of field list
         (* Declaration identity, with arguments retained for later generic
            instantiation. A recursive reference is never expanded into a
            finite approximation. *)
         | Named of string * ty list
(* A property key: a string, or the symbol the declaration document lists at
   this index. The two spaces never meet. *)
and key = Name of string | Key of int
(* A host-relative method (`host`) is read off its object and invoked on it:
   a member, not a field holding a function value, as Lean reads method
   syntax. `receivers` are the types its host must meet, which a `this`
   parameter states; none for any other field. A generic method (`generic`),
   a required member whose signatures form one scheme each taking the
   declaration as receiver, is a member too, as Lean reads it
   (`schemeMethod`): its host binds it before the actuals run. *)
and field = { name: key; optional: bool; read: ty; write: ty option; host: bool; receivers: ty list; stable: bool;
              generic: bool }
(* An index signature constrains the keys its class admits: every string key
   (`[k: string]`), the canonical numeric ones (`[k: number]`), or every symbol
   key (`[k: symbol]`); an index over a union of key types is one per member. *)
and index_keys = Strings | Numeric | Symbols
and index_signature = { keys: index_keys; value: ty; writable: ty option }
(* Argument lists are not value types. A pack parameter and its instances
   travel through their own substitution projection, never through [ty]. *)
and pack = PackParameter of rigid | Pack of sequence
and type_argument = ValueArgument of ty | PackArgument of pack
  (* A qualified binder's instance: its input, observation and, for a
     resolvable binder, result, with the certificate classifying the input. *)
  | ResolutionArgument of ty * (rigid * ty) * (rigid * ty) option * resolution_certificate
and resolution_certificate = StableResolution
  | NativeResolution of resolution_certificate
  (* A native promise observed at its payload, whatever that is. *)
  | PromiseObservation
  | UnionResolution of resolution_certificate list
  | BinderResolution of string
(* [default]: the value binder's declared default (`TResult2 = never`), the
   instance a call takes where nothing constrains the binder. It is inference
   input, not part of the signature's type: claims state the instance. *)
and quantifier = { identity: rigid; bound: type_argument option; default: ty option;
                   (* The owned observation, and result where resolvable. *)
                   resolution: (rigid * rigid option) option }
(* `receiver` is the `this` value a call may pass: `Top` for a signature
   indifferent to it. `variadic` is the contract of each actual after `params`,
   for a signature that takes any number of them; `rest_pack` the type of all
   of them as one argument list, for a rest typed by a pack parameter or a
   concrete pack instance. At most one is set. *)
and signature = { quantified: quantifier list; receiver: ty; params: ty list;
                  variadic: ty option; rest_pack: pack option; result: ty; call_effect: call_effect }
and sequence = { required: ty list; optional_elements: ty list; rest: ty option; readonly: bool; presence: array_presence }
and shape = { fields: field list; indexes: index_signature list; calls: signature list; elements: sequence option }
let quantifier_identities (q:quantifier) = q.identity ::
  (match q.resolution with None -> [] | Some (observation,result) -> observation :: Option.to_list result)
(* An immutable annotated binding may retain a separately inferred effect on
   exactly the same call signature. Every other annotation component remains
   unchanged; this never strengthens an ordinary input annotation by itself. *)
let retain_call_effects declared inferred = match declared,inferred with
  | Atoms [Shape expected],Atoms [Shape actual] ->
    let retain (s:signature) =
      match List.find_opt (fun (candidate:signature) ->
        {candidate.call_effect with on_throw=false}=empty_effect &&
        {candidate with call_effect=ordinary_effect} = {s with call_effect=ordinary_effect}) actual.calls with
      | Some candidate -> {s with call_effect=candidate.call_effect}
      | None -> s in
    Atoms [Shape {expected with calls=List.map retain expected.calls}]
  | _ -> declared

(* A callable's type with the footprint proposed for its call signatures, on
   a throw too where `on_throw`. *)
let with_footprint ?(on_throw=false) footprint t = match t with
  | Atoms [Shape ({calls;_} as shape)] when footprint <> top_footprint ->
    Atoms [Shape {shape with calls=List.map (fun (s:signature) ->
      {s with call_effect={s.call_effect with footprint;on_throw}}) calls}]
  | _ -> t

(* A function's precondition on every signature of its type: its code
   is checked assuming it, so each call establishes it (Lean's `moduleArrow`). *)
let with_pre pre t = match t with
  | Atoms [Shape ({calls;_} as shape)] when pre <> [] ->
    Atoms [Shape {shape with calls=List.map (fun (s:signature) ->
      {s with call_effect={s.call_effect with pre}}) calls}]
  | _ -> t

(* Every signature stating the postcondition a declaration's type
   invariants give (Lean's `moduleArrow`, `Fn.ensures`). *)
let with_ensures ensures t = match t with
  | Atoms [Shape ({calls;_} as shape)] when ensures <> [] ->
    Atoms [Shape {shape with calls=List.map (fun (s:signature) ->
      {s with call_effect={s.call_effect with ensures}}) calls}]
  | _ -> t

let record fields = Atoms [Shape {fields;indexes=[];calls=[];elements=None}]
(* Whether a type mentions a type parameter. *)
let rec mentions_rigid = function
  | Rigid _ -> true
  | Union ts -> List.exists mentions_rigid ts
  | Meet (t,ts) -> List.exists mentions_rigid (t::ts)
  | Atoms atoms -> List.exists (function
      | Named (_,args) -> List.exists mentions_rigid args
      | Shape s ->
        List.exists (fun (f:field) -> mentions_rigid f.read
          || Option.fold ~none:false ~some:mentions_rigid f.write
          || List.exists mentions_rigid f.receivers) s.fields
        || List.exists (fun (i:index_signature) -> mentions_rigid i.value
          || Option.fold ~none:false ~some:mentions_rigid i.writable) s.indexes
        || List.exists signature_mentions_rigid s.calls
        || Option.fold ~none:false ~some:sequence_mentions_rigid s.elements
      | Exact fs -> List.exists (fun (f:field) -> mentions_rigid f.read) fs
      | Ctors (signatures,statics) -> List.exists signature_mentions_rigid signatures
        || List.exists (fun (f:field) -> mentions_rigid f.read) statics
      | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Top
      | Bigint | Symbol | BigintLit _ | SymbolLit _ | Callable -> false) atoms
and sequence_mentions_rigid s = List.exists mentions_rigid
    (s.required @ s.optional_elements @ Option.to_list s.rest)
and signature_mentions_rigid (s:signature) =
  s.quantified <> [] || s.rest_pack <> None ||
  List.exists mentions_rigid (s.receiver :: s.result :: s.params @ Option.to_list s.variadic)
(* Record operands are one object; a function type met with a record is the
   function carrying the record's fields, a callable object, as Lean meets
   them (`sourceMeetLists`). *)
let callable_record_supported (x:shape) (y:shape) =
  let plain_fields (r:shape) = r.indexes = [] && List.for_all (fun (f:field) ->
    not f.optional && not f.host && f.write <> None) r.fields in
  (x.calls = [] || plain_fields y) && (y.calls = [] || plain_fields x)
let meet_objects a b = match a,b with
  | Atoms [Shape x],Atoms [Shape y]
    when (x.calls=[] || y.calls=[]) && x.elements=None && y.elements=None &&
         (x.indexes=[] || y.indexes=[]) && callable_record_supported x y ->
    let names = List.map (fun (f:field) -> f.name) (x.fields @ y.fields) in
    if List.length names <> List.length (List.sort_uniq compare names) then None
    else Some (Atoms [Shape {x with fields=x.fields @ y.fields;
      indexes=(match x.indexes with [] -> y.indexes | own -> own);
      calls=x.calls @ y.calls}])
  | Atoms [Shape ({elements=Some _;_} as x)],Atoms [Shape ({elements=None;_} as y)]
  | Atoms [Shape ({elements=None;_} as y)],Atoms [Shape ({elements=Some _;_} as x)]
    when x.calls=[] && y.calls=[] && x.indexes=[] && y.indexes=[] && y.fields <> [] ->
    let names = List.map (fun (f:field) -> f.name) (x.fields @ y.fields) in
    if List.length names <> List.length (List.sort_uniq compare names) then None
    else Some (Atoms [Shape {x with fields=x.fields @ y.fields}])
  | _ -> None
let top = Atoms [Top]
(* The key the model reserves for a host object (COMPILER-API.md, "Restricted
   values"). A record type marked by an optional field of it owns no such key:
   its objects are ordinary, which a claim states as an own-key bound
   excluding the key. *)
let host_key = Name "[[host]]"
let host_mark : field = {name=host_key;optional=true;read=Atoms [];write=None;host=false;receivers=[];stable=false;generic=false}
(* `nonHost`: every value but a host object. *)
let non_host = Atoms [Nul;Undef;True;False;Num;Str;Bigint;Symbol;
  Shape {fields=[host_mark];indexes=[];calls=[];elements=None};Callable;Ctors ([],[])]
let arrow ?(call_effect=ordinary_effect) params result =
  Atoms [Shape {fields=[];indexes=[];calls=[{quantified=[];receiver=top;params;variadic=None;rest_pack=None;result;call_effect}];elements=None}]
(* A longer callback signature keeps the parameters the code reads at its
   own contracts. The remaining actuals are discarded by fixed-arity code.
   Both the closure and its use are checked by Lean. *)
let discarded_signature (own:signature) (offered:signature) =
  {offered with call_effect=own.call_effect; params=own.params @
    List.filteri (fun i _ -> i >= List.length own.params) offered.params}
let quantified_arrow ?(call_effect=ordinary_effect) ?(receiver=top) quantified params result =
  Atoms [Shape {fields=[];indexes=[];calls=[{quantified;receiver;params;variadic=None;rest_pack=None;result;call_effect}];elements=None}]
let variadic_arrow ?(call_effect=ordinary_effect) ?(quantified=[]) ?(receiver=top) params element result =
  Atoms [Shape {fields=[];indexes=[];calls=[{quantified;receiver;params;variadic=Some element;rest_pack=None;result;call_effect}];elements=None}]
let ground xs = Atoms (List.sort_uniq compare xs)
let bool = ground [True;False]
(* `unknown` as the union of the kinds of a JavaScript value (Lean's
   `sourceKinds`): null, undefined, a Boolean, a number, a string, a bigint,
   a symbol, an object without call code, and one with call code, invocable
   or a class. *)
let unknown_kinds = [Nul;Undef;True;False;Num;Str;Bigint;Symbol;
  Shape {fields=[];indexes=[];calls=[];elements=None};Callable;Ctors ([],[])]
(* What a test keeps of `unknown`: the kinds [keeps] admits, the Boolean kind
   whole where it admits either value, as Lean slices `unknown` by kinds, and
   `unknown` itself where it admits every kind. *)
let unknown_slice keeps =
  let kept = List.filter keeps unknown_kinds in
  let kept = if List.mem True kept || List.mem False kept then True :: False :: kept else kept in
  if List.for_all (fun k -> List.mem k kept) unknown_kinds then Atoms [Top] else ground kept
(* Whether atoms are strictly increasing, as `ground` leaves them. *)
let rec strictly_increasing = function
  | a :: (b :: _ as rest) -> compare a b < 0 && strictly_increasing rest
  | _ -> true
(* Two strictly increasing lists of atoms merged in one pass: what `ground`
   makes of their concatenation, since atoms compare equal only when they
   are equal. *)
let rec merge_increasing xs ys = match xs,ys with
  | [],l | l,[] -> l
  | x :: xs',y :: ys' ->
    let c = compare x y in
    if c < 0 then x :: merge_increasing xs' ys
    else if c > 0 then y :: merge_increasing xs ys'
    else x :: merge_increasing xs' ys'
let union a b = match a,b with
  | Atoms [], t | t, Atoms [] -> t
  | Atoms xs, Atoms ys when strictly_increasing xs && strictly_increasing ys -> Atoms (merge_increasing xs ys)
  | Atoms xs, Atoms ys -> ground (xs @ ys)
  | _ when a=b -> a
  | _ -> let parts = function Union ts -> ts | t -> [t] in
    Union (List.sort_uniq compare (parts a @ parts b))
(* `unions`, with each run of atom lists met while
   the joined type is atoms grounded once: one non-empty list is kept as it
   is, as `union` keeps it beside an empty one, and several are what `ground`
   makes of their concatenation, as `union` makes of each pair. Joining one
   atom at a time costs a pass over the joined list per atom; one `ground`
   sorts the run once. *)
let unions ts =
  let joined lists = match List.filter (function [] -> false | _ -> true) (List.rev lists) with
    | [] -> Atoms [] | [l] -> Atoms l | ls -> ground (List.concat ls) in
  let rec run lists = function Atoms xs :: rest -> run (xs :: lists) rest | rest -> lists, rest in
  let rec go acc ts = match acc, ts with
    | _, [] -> acc
    | Atoms a, _ ->
      let lists, rest = run [a] ts in
      (match rest with [] -> joined lists | t :: rest -> go (union (joined lists) t) rest)
    | _, t :: rest -> go (union acc t) rest in
  go (Atoms []) ts
let rec widen = function
  | Atoms xs -> ground (List.concat_map (function
      | True | False -> [True;False] | NumLit _ -> [Num] | StrLit _ -> [Str]
      | BigintLit _ -> [Bigint] | SymbolLit _ -> [Symbol]
      | a -> [a]) xs)
  | Rigid _ as t -> t | Union ts -> unions (List.map widen ts)
  | Meet (t,ts) -> Meet (widen t,ts)
(* A member bound to its host where the host is a union of hosts, each arm
   given by its member's type: Lean splits the host's slot and binds each
   arm's member to it (`unionVar`, then `bindMember`), so the bound function
   is one signature, each arm's chosen by [fits], all at the same parameters
   and effect, its result their union, at any receiver. None where an arm has
   no such signature or two arms' differ. *)
let bound_union fits arms =
  let chosen = List.map (function
    | Shape {calls;_} -> List.find_opt fits calls
    | _ -> None) arms in
  match chosen with
  | Some (first:signature) :: rest
    when List.for_all (function
      | Some (s:signature) -> s.params = first.params && s.variadic = first.variadic
          && s.call_effect = first.call_effect
      | None -> false) rest ->
    let result = List.fold_left (fun r -> function
      | Some (s:signature) -> union r s.result | None -> r) (Atoms []) chosen in
    Some (match first.variadic with
      | Some element -> variadic_arrow ~call_effect:first.call_effect first.params element result
      | None -> arrow ~call_effect:first.call_effect first.params result)
  | _ -> None
let array elements = Atoms [Shape {fields=[];indexes=[];calls=[];elements=Some elements}]
(* A call may omit a trailing position exactly when its contract admits
   `undefined`: that is the value bound there. Optionality is a property of the
   declared type, not a separate arity record. *)
(* The positions a rest parameter stands for: the required elements of the
   tuple its arguments are collected into. A contract with optional or
   unbounded positions is not a fixed number of further arguments. Own fields
   are separate from the element sequence. *)
let tuple_positions ?(readonly=false) = function
  | Atoms [Shape {indexes=[];calls=[];elements=Some s;_}]
    when s.optional_elements=[] && s.rest=None && (readonly || not s.readonly) -> Some s.required
  | _ -> None

(* The contract of each further argument, where a rest parameter's contract is
   a mutable `T[]` (with [readonly], a `readonly T[]` too: the array a call
   collects is fresh, and a readonly view of it gives up only writes): it
   collects any number of them. *)
let array_element ?(readonly=false) = function
  | Atoms [Shape {fields=[];indexes=[];calls=[];elements=Some s}]
    when s.required=[] && s.optional_elements=[] && (readonly || not s.readonly) -> s.rest
  | _ -> None

(* The values a spread of such an array passes: every position's contract,
   and `undefined` for a hole where its presence is sparse; a dense or
   readable store's holes read at a position's contract (Lean's
   `SpreadsInto`). A union of arrays passes the values of each arm, an empty
   tuple's none. Own fields are separate from the element sequence. *)
let spread_element ?(readonly=false) = function
  | Atoms (_ :: _ as arms) ->
    let arm = function
      | Shape {indexes=[];calls=[];elements=Some s;_} when readonly || not s.readonly ->
        let positions = s.required @ s.optional_elements @ Option.to_list s.rest in
        Some (unions ((if s.presence = Sparse then [Atoms [Undef]] else []) @ positions))
      | _ -> None in
    List.fold_left (fun acc a -> match acc,arm a with
      | Some t,Some u -> Some (union t u) | _ -> None) (Some (Atoms [])) arms
  | _ -> None

let rec admits_undefined = function
  | Atoms xs -> List.exists (function Undef | Top -> true | _ -> false) xs
  | Rigid _ -> false
  | Union ts -> List.exists admits_undefined ts
  | Meet (t,ts) -> List.for_all admits_undefined (t::ts)

let rec without_nullish = function
  | Atoms xs -> ground (List.filter (function Nul | Undef -> false | _ -> true) xs)
  | Rigid _ as t -> t | Union ts -> unions (List.map without_nullish ts)
  | Meet (t,ts) -> Meet (without_nullish t,ts)
(* The values of `t` a test keeps, [slice] reading each arm: a type
   parameter's are the meet of it with what the test keeps of its bound,
   where the bound is of atoms other than `unknown`: none where it keeps
   none, the parameter itself where it keeps all. *)
let narrow_rigid bounds slice t =
  let rec arm = function
    | Rigid r as t -> (match List.assoc_opt r bounds with
      | Some (Atoms xs as bound) when not (List.mem Top xs) ->
        let kept = slice bound in
        if kept = bound then t else if kept = Atoms [] then Atoms [] else Meet (t,[kept])
      | _ -> t)
    | Union ts -> unions (List.map arm ts)
    | t -> slice t in
  arm t
(* JavaScript's `ToBoolean` of every value of an atom, where the atom settles
it: null, undefined, `false`, the two zeros, NaN, `""` and `0n` are falsy,
every object, function, class and symbol truthy. *)
let truthiness = function
  | Nul | Undef | False -> Some false
  | True | Symbol | SymbolLit _ | Shape _ | Exact _ | Ctors _ | Callable -> Some true
  | NumLit bits -> let x = Int64.float_of_bits bits in Some (not (x = 0. || Float.is_nan x))
  | StrLit s -> Some (s <> "")
  | BigintLit i -> Some (i <> "0")
  | Num | Str | Bigint | Top | Named _ -> None
(* The part of a type a truthiness test answering [truth] leaves: the atoms
   that may answer so. *)
let rec truthy_slice truth = function
  | Atoms xs when List.mem Top xs ->
    union (truthy_slice truth (Atoms (List.filter (fun a -> a <> Top) xs)))
      (unknown_slice (fun a -> truthiness a <> Some (not truth)))
  | Atoms xs -> ground (List.filter (fun a -> truthiness a <> Some (not truth)) xs)
  | Rigid _ | Meet _ as t -> t
  | Union ts -> unions (List.map (truthy_slice truth) ts)
let number_literal spelling = Atoms [NumLit (Int64.bits_of_float (float_of_string spelling))]
(* The literal *type* `0` (or `-0`) admits both runtime zeros: TypeScript
   gives `-0` the type `0`, and strict equality equates them. A literal value
   keeps its own bit pattern (`number_literal`); only the type names both, as
   Lean's annotation lowering does (`SourceTypes.numberLabels`). *)
let number_literal_type spelling =
  if float_of_string spelling = 0. then ground [NumLit 0L; NumLit (Int64.bits_of_float (-0.))]
  else number_literal spelling
