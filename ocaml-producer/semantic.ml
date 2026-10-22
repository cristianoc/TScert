(* Semantic types contain no solver state. More precise proposals do not mutate them.
   A rigid parameter remains distinct from any future inference/existential IDs. *)
(* How a footprint may change a location's contents (Lean's
   `Footprints.Change`): not at all, as a store keeping every dense prefix, or
   arbitrarily. *)
type change = Keep | Grow | Any
(* A closed footprint (Lean's `Footprints.Closed`): the change a call may make,
   on normal return, to its entry heap's locations holding a value and to those
   holding an array store. On a value `Grow` is `Keep`. *)
type footprint = { on_value: change; on_store: change }
let top_footprint = {on_value=Any;on_store=Any}
let empty_footprint = {on_value=Keep;on_store=Keep}
let change_le a b = match a,b with Keep,_ | Grow,(Grow|Any) | Any,Any -> true | _ -> false
let footprint_le a b =
  let on_value = function Grow -> Keep | d -> d in
  change_le (on_value a.on_value) (on_value b.on_value) && change_le a.on_store b.on_store
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
type call_effect = { footprint: footprint; promise: promise option; fresh: bool; receiver_store: bool; on_throw: bool }
let footprint_effect footprint = {footprint;promise=None;fresh=false;receiver_store=false;on_throw=false}
(* An ordinary arrow's: every location may change. *)
let ordinary_effect = footprint_effect top_footprint
(* Heap preservation: no location may change. *)
let empty_effect = footprint_effect empty_footprint
let promise_effect promise = {(footprint_effect top_footprint) with promise=Some promise}

(* A bound function's effect (Lean's `Effect.drop`): the receiver it saved is
   not the receiver of a call of it, so an exception of the receiver's store
   is an exception of every location. *)
let bound_effect e = if e.receiver_store then {e with footprint=top_footprint; receiver_store=false} else e
(* Whether a signature's result is the call's: one without a promise. *)
let plain_effect e = e.promise = None
(* A smaller footprint and the same promise, a fresh result where the other
   states one, and the receiver's store excepted only where the other excepts
   it or lets everything change, and a footprint on a throw where the other
   states one (Lean's `Effect.covers`). *)
let effect_covers a b = footprint_le a.footprint b.footprint && a.promise = b.promise &&
  (not b.fresh || a.fresh) && (not a.receiver_store || b.receiver_store || b.footprint = top_footprint) &&
  (not b.on_throw || a.on_throw)

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
   parameter states; none for any other field. *)
and field = { name: key; optional: bool; read: ty; write: ty option; host: bool; receivers: ty list; stable: bool }
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
let meet_objects a b = match a,b with
  | Atoms [Shape x],Atoms [Shape y]
    when (x.calls=[] || y.calls=[]) && x.elements=None && y.elements=None &&
         (x.indexes=[] || y.indexes=[]) ->
    let names = List.map (fun (f:field) -> f.name) (x.fields @ y.fields) in
    if List.length names <> List.length (List.sort_uniq compare names) then None
    else Some (Atoms [Shape {x with fields=x.fields @ y.fields;
      indexes=(match x.indexes with [] -> y.indexes | own -> own);
      calls=x.calls @ y.calls}])
  | _ -> None
let top = Atoms [Top]
(* The key the model reserves for a host object (COMPILER-API.md, "Restricted
   values"). A record type marked by an optional field of it owns no such key:
   its objects are ordinary, which a claim states as an own-key bound
   excluding the key. *)
let host_key = Name "[[host]]"
let host_mark : field = {name=host_key;optional=true;read=Atoms [];write=None;host=false;receivers=[];stable=false}
(* `nonHost`: every value but a host object. *)
let non_host = Atoms [Nul;Undef;True;False;Num;Str;Bigint;Symbol;
  Shape {fields=[host_mark];indexes=[];calls=[];elements=None};Callable;Ctors ([],[])]
let arrow ?(call_effect=ordinary_effect) params result =
  Atoms [Shape {fields=[];indexes=[];calls=[{quantified=[];receiver=top;params;variadic=None;rest_pack=None;result;call_effect}];elements=None}]
let quantified_arrow ?(call_effect=ordinary_effect) ?(receiver=top) quantified params result =
  Atoms [Shape {fields=[];indexes=[];calls=[{quantified;receiver;params;variadic=None;rest_pack=None;result;call_effect}];elements=None}]
let variadic_arrow ?(call_effect=ordinary_effect) ?(quantified=[]) ?(receiver=top) params element result =
  Atoms [Shape {fields=[];indexes=[];calls=[{quantified;receiver;params;variadic=Some element;rest_pack=None;result;call_effect}];elements=None}]
let ground xs = Atoms (List.sort_uniq compare xs)
let bool = ground [True;False]
let union a b = match a,b with
  | Atoms [], t | t, Atoms [] -> t
  | Atoms xs, Atoms ys -> ground (xs @ ys)
  | _ when a=b -> a
  | _ -> let parts = function Union ts -> ts | t -> [t] in
    Union (List.sort_uniq compare (parts a @ parts b))
let rec widen = function
  | Atoms xs -> ground (List.concat_map (function
      | True | False -> [True;False] | NumLit _ -> [Num] | StrLit _ -> [Str]
      | BigintLit _ -> [Bigint] | SymbolLit _ -> [Symbol]
      | a -> [a]) xs)
  | Rigid _ as t -> t | Union ts -> List.fold_left union (Atoms []) (List.map widen ts)
  | Meet (t,ts) -> Meet (widen t,ts)
let array elements = Atoms [Shape {fields=[];indexes=[];calls=[];elements=Some elements}]
(* A call may omit a trailing position exactly when its contract admits
   `undefined`: that is the value bound there. Optionality is a property of the
   declared type, not a separate arity record. *)
(* The positions a rest parameter stands for: the required elements of the
   tuple its arguments are collected into. A contract with optional or
   unbounded positions is not a fixed number of further arguments. *)
let tuple_positions ?(readonly=false) = function
  | Atoms [Shape {fields=[];indexes=[];calls=[];elements=Some s}]
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

let rec admits_undefined = function
  | Atoms xs -> List.exists (function Undef | Top -> true | _ -> false) xs
  | Rigid _ -> false
  | Union ts -> List.exists admits_undefined ts
  | Meet (t,ts) -> List.for_all admits_undefined (t::ts)

let rec without_nullish = function
  | Atoms xs -> ground (List.filter (function Nul | Undef -> false | _ -> true) xs)
  | Rigid _ as t -> t | Union ts -> List.fold_left union (Atoms []) (List.map without_nullish ts)
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
    | Union ts -> List.fold_left union (Atoms []) (List.map arm ts)
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
  | Atoms xs -> ground (List.filter (fun a -> truthiness a <> Some (not truth)) xs)
  | Rigid _ | Meet _ as t -> t
  | Union ts -> List.fold_left union (Atoms []) (List.map (truthy_slice truth) ts)
let number_literal spelling = Atoms [NumLit (Int64.bits_of_float (float_of_string spelling))]
(* The literal *type* `0` (or `-0`) admits both runtime zeros: TypeScript
   gives `-0` the type `0`, and strict equality equates them. A literal value
   keeps its own bit pattern (`number_literal`); only the type names both, as
   Lean's annotation lowering does (`SourceTypes.numberLabels`). *)
let number_literal_type spelling =
  if float_of_string spelling = 0. then ground [NumLit 0L; NumLit (Int64.bits_of_float (-0.))]
  else number_literal spelling
