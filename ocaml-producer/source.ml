open Json
open Semantic
let unsupported s = fail ("unsupported: " ^ s)
let text k j = str (field k j)
let items k j = list (field k j)
let natural j = match j with
  | Number n -> (match int_of_string_opt n with Some i when i >= 0 -> i | _ -> fail "expected a natural number")
  | _ -> fail "expected a natural number"
(* A closed footprint and a signature's effect, as the wire spells them. *)
let change_of allowed j =
  match List.assoc_opt (str j) ["keep",Keep;"grow",Grow;"any",Any] with
  | Some d when List.mem d allowed -> d
  | _ -> unsupported "unknown footprint change"
let footprint_of j = match j with
  | Object fields when List.sort String.compare (List.map fst fields) = ["store";"value"] ->
    {on_value=change_of [Keep;Any] (field "value" j);on_store=change_of [Keep;Grow;Any] (field "store" j)}
  | _ -> unsupported "invalid footprint"
let promise_of = function
  | Object [("guards",Object [("param",p)])] -> Guards (natural p)
  | Object [("asserts",Object [("param",p)])] -> Asserts (natural p)
  | _ -> unsupported "unknown callable promise"
let effect_of j = match j with
  | Object fields when List.sort String.compare (List.map fst fields) = ["footprint";"fresh";"promise";"receiverStore"] ->
    {footprint=footprint_of (field "footprint" j);
     promise=(match field "promise" j with Null -> None | p -> Some (promise_of p));
     fresh=boolean (field "fresh" j); receiver_store=boolean (field "receiverStore" j)}
  | _ -> unsupported "unknown callable effect"
let resolution_slots scope index j = match field "resolution" j with
  | Null -> None
  | Object fields as slots ->
    if List.sort String.compare (List.map fst fields) <> ["observation";"result"] then
      fail "invalid resolution slot fields";
    let slot offset key = {scope;index=3*index+offset;spelling=text key slots} in
    let observation=slot 1 "observation" in
    let result = match field "result" slots with
      | Null -> None
      | String _ -> Some (slot 2 "result")
      | _ -> fail "expected a nullable resolution result slot" in
    let owned = observation :: Option.to_list result in
    let spellings = List.map (fun (r:rigid) -> r.spelling) owned in
    if List.mem "" spellings || List.length (List.sort_uniq String.compare spellings) <> List.length spellings ||
       List.mem (text "name" j) spellings then
      fail "resolution slots must be distinct lexical names";
    Some (observation,result)
  | _ -> fail "expected nullable resolution slots"
(* Where a source type's names resolve. A function annotation reads its
   enclosing binders by spelling; a declaration body reads its own parameters
   by position and its method receiver as the declaration. A reference names
   its declaration by identity. *)
type type_context = { bindings: (string * type_argument) list;
                      owner: string option; positional: rigid list;
                      arity: (string * (int * int)) list;
                      symbolic: (string * (rigid * ty)) list;
                      (* The term read here is the declaration's own body:
                         a record there is the one its methods' receiver,
                         `self`, names. *)
                      own: bool;
                      (* `self` names the declaration: a method of its own
                         body. A nested type literal's method is received by
                         that literal, which the producer does not name. *)
                      self_owner: bool;
                      (* A declared value's binder typing both a value and a
                         rest's argument list: its rest is the argument lists
                         of the array type it is instantiated at. *)
                      value_packs: bool }
let identity declaration =
  let span = list (field "span" declaration) in
  match span with
  | [Number first;Number last] ->
    str (field "module" declaration) ^ "#" ^ first ^ ":" ^ last
  | _ -> fail "invalid declaration identity"
(* The source type terms function annotations and declaration bodies share.
   This is a candidate-only view: Lean independently derives the authoritative
   graph rows from the same terms. Named edges remain named here, including
   cycles; no recursive declaration is unfolded. *)
(* A field name: a string key, or `{"symbol": i}` for the declaration
   document's i-th symbol. *)
let property_key = function
  | String name -> Name name
  | Object ["symbol",Number i] -> Key (int_of_string i)
  | _ -> fail "expected a property key"
(* A rest term typed by a pack parameter, `{"k": "pack", "of": binder}`. *)
let is_pack = function
  | Object fields -> List.assoc_opt "k" fields = Some (String "pack")
  | _ -> false

(* Free uses by role, not occurrences in serialized JSON. Nested schemes
   shadow their own names, including in their bounds and signatures. *)
let rec binder_use name = function
  | Object fields as term ->
    let get key = List.assoc_opt key fields in
    if get "k" = Some (String "binder") then get "name" = Some (String name),false
    else if is_pack term then
      (match get "of" with
      | Some (Object operand) when List.assoc_opt "k" operand = Some (String "binder") ->
        false,List.assoc_opt "name" operand = Some (String name)
      | Some operand -> binder_use name operand
      | None -> false,false)
    else if get "k" = Some (String "scheme") &&
      (match get "binders" with
      | Some (Array binders) -> List.exists (function
          | Object binder -> List.assoc_opt "name" binder = Some (String name) ||
            (match List.assoc_opt "resolution" binder with
            | Some (Object slots) -> List.exists (fun key ->
              List.assoc_opt key slots = Some (String name)) ["observation";"result"]
            | _ -> false)
          | Null | Bool _ | Number _ | String _ | Array _ -> false) binders
      | Some (Null | Bool _ | Number _ | String _ | Object _) | None -> false)
    then false,false
    else binder_uses name (List.map snd fields)
  | Array terms -> binder_uses name terms
  | Null | Bool _ | Number _ | String _ -> false,false
and binder_uses name terms = List.fold_left (fun (values,packs) term ->
  let value,pack=binder_use name term in values || value,packs || pack) (false,false) terms

let rec source_type ctx j =
  let recur = source_type {ctx with own=false} in
  match text "k" j with
  | "atom" -> (match text "name" j with
    | "null" -> Atoms [Nul] | "undefined" -> Atoms [Undef]
    | "boolean" -> bool | "number" -> Atoms [Num]
    | "string" -> Atoms [Str] | "bigint" -> Atoms [Bigint] | "symbol" -> Atoms [Symbol]
    | "unknown" -> top
    | "void" -> top
    (* `object`, every object: an ordinary one, constraining no key, or one
       with call or construct code. *)
    | "object" -> Atoms [Shape {fields=[];indexes=[];calls=[];elements=None};Callable;Ctors ([],[])]
    | "never" -> Atoms [] | name -> unsupported ("atom " ^ name))
  (* The standard library's `Function`: callable or constructible, with no
     signature, as Lean lowers it. *)
  | "callable" -> Atoms [Callable;Ctors ([],[])]
  | "unique" -> (match field "symbol" j with Number i -> Atoms [SymbolLit (int_of_string i)] | _ -> unsupported "unique symbol identity")
  | "literal" -> (match text "name" j with
    | "true" -> Atoms [True] | "false" -> Atoms [False]
    | "number" -> number_literal_type (text "text" j)
    | "string" -> Atoms [StrLit (text "text" j)]
    | "bigint" -> Atoms [BigintLit (text "text" j)]
    | name -> unsupported ("literal type " ^ name))
  | "union" ->
    (* `unknown` absorbs the rest of its union: semantic top. *)
    (match List.fold_left union (Atoms []) (List.map recur (items "parts" j)) with
    | Atoms atoms when List.mem Top atoms -> top
    | t -> t)
  | "array" -> array {required=[];optional_elements=[];
      rest=Some (recur (field "element" j));readonly=boolean (field "readonly" j);presence=presence_of_string (text "presence" j)}
  | "tuple" -> array {required=List.map recur (items "required" j);
      optional_elements=List.map recur (items "optional" j);
      rest=(match field "rest" j with Null -> None | t -> Some (recur t));
      readonly=boolean (field "readonly" j);presence=presence_of_string (text "presence" j)}
  (* A generic method: its signatures quantify lexically scoped binders.
     A bound naming the method's own binders is not represented, and a
     binder typing a rest and anything else is refused on principle
     (SOURCE-FRAGMENT, Refused on principle), consistently with Lean's
     declaration lowering; a rest is a pack
     parameter or any number of actuals at an element, as Lean reads it. *)
  | "scheme" ->
    let binders = items "binders" j and signatures = items "signatures" j in
    let names = List.map (fun b -> text "name" b) binders in
    (* A bound naming the method's own binders, an F-bound, is not what a
       scheme's bounds mean: they are read where the method is declared. *)
    let mentions_own term = List.exists (fun name ->
      let value,pack=binder_use name term in value || pack) names in
    let uses=List.map (fun name -> name,binder_uses name signatures) names in
    let packs=List.filter_map (fun (name,(_,pack)) -> if pack then Some name else None) uses in
    if List.exists (fun (_, (value,pack)) -> value && pack) uses then
      unsupported ("generic contract at " ^ Json.encode (field "span" j) ^
        ": a type parameter typing a rest parameter and anything else is refused on principle: \
         TypeScript's instance gives the rest the element lists of the instance's members, \
         tagged arrays included, which no array a call collects is")
    else if List.exists (fun b -> mentions_own (field "bound" b)) binders then
      unsupported ("generic contract at " ^ Json.encode (field "span" j) ^
        ": a bound naming the method's own type parameters is not represented; the contract cannot be erased")
    else begin
      let start = match list (field "span" j) with
        | Number n :: _ -> int_of_string n
        | _ -> fail "empty source span" in
      let scope = -1_000_000_000 - start in
      let identities = List.mapi (fun index b -> {scope;index=3*index;spelling=text "name" b}) binders in
      let resolutions = List.mapi (resolution_slots scope) binders in
      let qualified = List.filter_map Fun.id resolutions in
      if qualified <> [] && List.length binders <> 1 then
        unsupported "a resolution-qualified scheme has exactly one source parameter";
      let inner = {ctx with bindings =
        List.map (fun (r:rigid) -> r.spelling,
          if List.mem r.spelling packs then PackArgument (PackParameter r)
          else ValueArgument (Rigid r)) identities @
        List.concat_map (fun (observation,result) -> List.map (fun (r:rigid) ->
          r.spelling,ValueArgument (Rigid r)) (observation :: Option.to_list result)) qualified @ ctx.bindings} in
      let pack_bound = pack_bound ctx in
      let quantified = List.map2 (fun (identity,resolution) b ->
        let pack = List.mem identity.spelling packs in
        {identity;resolution;bound=(match field "bound" b with
          | Null -> None
          | t when pack -> Some (PackArgument (pack_bound t))
          | t -> Some (ValueArgument (source_type ctx t)));
         (* A default sees the method's binders, as TypeScript reads it. A
            pack binder's instance is its argument list, never a default. *)
         default=(match field "default" b with
          | Null -> None
          | _ when pack -> None
          | t -> Some (source_type inner t))})
        (List.combine identities resolutions) binders in
      (* Call signatures, or construct signatures of a generic constructor
         type, `new <T>(x: T) => C<T>`. *)
      let parsed = List.map (source_type inner) signatures in
      if parsed <> [] && List.for_all (function Atoms [Ctors ([_],_)] -> true | _ -> false) parsed then
        Atoms [Ctors (List.map (function
          | Atoms [Ctors ([s],_)] -> {s with quantified}
          | _ -> unsupported "generic construct signature") parsed,
          List.concat_map (function Atoms [Ctors (_,statics)] -> statics | _ -> []) parsed)]
      else
      let calls = List.map (function
        | Atoms [Shape {fields=[];indexes=[];calls=[s];elements=None}] -> {s with quantified}
        | _ -> unsupported "generic method signature") parsed in
      Atoms [Shape {fields=[];indexes=[];calls;elements=None}]
    end
  | "constructor" ->
    (* A construct signature's rest, if any, is one argument list: a pack
       parameter, or any number at an element. *)
    let rest_pack = match field "rest" j with
      | Null -> None
      | t when is_pack t -> Some (source_pack ctx (field "of" t))
      | t -> Some (Pack {required=[];optional_elements=[];rest=Some (recur t);readonly=false;presence=Dense}) in
    (* A class value's static fields, listed when it has any: invariant, or
       a readonly one, a view. *)
    let statics = match List.assoc_opt "statics" (obj j) with
      | None -> []
      | Some fs -> List.map (fun f -> let t = recur (field "type" f) in
          let readonly = List.mem_assoc "readonly" (obj f) in
          {name=property_key (field "name" f);optional=false;read=t;write=(if readonly then None else Some t);
           host=false;receivers=[]}) (list fs) in
    Atoms [Ctors ([{call_effect=effect_of (field "effect" j);quantified=[];receiver=top;params=List.map recur (items "params" j);
      variadic=None;rest_pack;result=recur (field "result" j)}],statics)]
  | "function" ->
    let receiver = match field "receiver" j with Null -> top | source -> recur source in
    let variadic,rest_pack = match field "rest" j with
      | Null -> None,None
      | t when is_pack t -> None,Some (source_pack ctx (field "of" t))
      | t -> Some (recur t),None in
    let call_effect = effect_of (field "effect" j) in
    let signature = {call_effect;quantified=[];receiver;
      params=List.map recur (items "params" j);
      variadic;rest_pack;
      result=recur (field "result" j)} in
    Atoms [Shape {fields=[];indexes=[];calls=[signature];elements=None}]
  | "self" -> (match ctx.owner with
    | _ when not ctx.self_owner -> top
    | None -> fail "a method receiver outside a declaration"
    | Some owner ->
      (* A generic declaration's receiver is its application to its own
         parameters, which instantiation makes the instance. *)
      Atoms [Named (owner,List.map (fun r -> Rigid r) ctx.positional)])
  | "object" ->
    let recur = source_type {ctx with own=false;self_owner=ctx.own} in
    (* Method syntax: one signature or several, each received by the object,
       or by its meet with the types a `this` parameter states, which the
       host must meet, on a required member (as Lean's `methodForms`). *)
    let is_self = function
      | Object r -> List.assoc_opt "k" r = Some (String "self")
      | _ -> false in
    let stated f = match f with
      | Object fs when List.assoc_opt "k" fs = Some (String "function") ->
        (match List.assoc_opt "receiver" fs with
         | Some r when is_self r -> Some []
         | Some (Object r as receiver) when List.assoc_opt "k" r = Some (String "intersection") ->
           let parts = items "parts" receiver in
           let others = List.filter (fun p -> not (is_self p)) parts in
           if List.length parts - List.length others = 1 && others <> [] then Some others else None
         | _ -> None)
      | _ -> None in
    let forms t = match t with
      | Object fs when List.assoc_opt "k" fs = Some (String "intersection") ->
        (match List.assoc_opt "parts" fs with
         | Some (Array (_::_ as parts)) -> parts
         | _ -> [])
      | t -> [t] in
    let method_syntax t = forms t <> [] && List.for_all (fun f -> stated f <> None) (forms t) in
    let fields = List.map (fun f ->
      let optional = boolean (field "optional" f) in
      let host = not optional && method_syntax (field "type" f) in
      (* The stated receivers are read apart; the forms keep the host alone. *)
      let receivers,ty = if not host then [],field "type" f else
        let unstated form = match form with
          | Object fs -> Object (List.map (fun (k,v) -> if k = "receiver" && not (is_self v)
              then (k,List.find is_self (items "parts" v)) else (k,v)) fs)
          | form -> form in
        let receivers = match forms (field "type" f) with
          | form :: _ -> List.map recur (Option.get (stated form))
          | [] -> [] in
        receivers,(match field "type" f with
          | Object fs when List.assoc_opt "k" fs = Some (String "intersection") ->
            Object (List.map (fun (k,v) -> if k = "parts" then (k,Array (List.map unstated (list v))) else (k,v)) fs)
          | form -> unstated form) in
      let t = recur ty in
      {name=property_key (field "name" f);optional;
       read=t;write=(if boolean (field "readonly" f) then None else Some t);
       host;receivers})
      (items "fields" j) in
    (* The string index, and the number and symbol indexes a term states only
       when it has them. *)
    let indexes = List.filter_map (fun (name,keys) ->
      match List.assoc_opt name (Json.obj j) with
      | None | Some Null -> None
      | Some index -> let t = recur (field "value" index) in
        Some {keys;value=t;writable=(if boolean (field "readonly" index) then None else Some t)})
      ["stringIndex",Strings;"numberIndex",Numeric;"symbolIndex",Symbols] in
    let calls = List.map (fun c -> match recur c with
      | Atoms [Shape {fields=[];indexes=[];calls=[signature];elements=None}] -> signature
      | _ -> unsupported "call signature") (items "calls" j) in
    (* Members held as own properties that are not enumerable, on the
       prototype the model gives the object (the library overlay's). *)
    let fields = match List.assoc_opt "prototype" (obj j) with
      | Some p -> fields @ [{name=Name "[[proto]]";optional=false;read=recur p;write=None;host=false;receivers=[]}]
      | None -> fields in
    Atoms [Shape {fields;indexes;calls;elements=None}]
  | "reference" ->
    let id = identity (field "target" (field "reference" j)) in
    let args = List.map recur (items "args" j) in
    (match List.assoc_opt id ctx.arity with
    | Some (required,total) when List.length args < required || List.length args > total ->
      fail ("type application arity: " ^ id)
    | Some _ -> ()
    | None -> fail ("reference lacks a declaration " ^ id));
    (* An annotation applies a one-parameter cell or identity declaration
       directly: its body is the argument, substituted. *)
    (match ctx.owner,args,List.assoc_opt id ctx.symbolic with
    | None,[arg],Some (parameter,body) -> Inference.substitute [parameter,ValueArgument arg] body
    | _ -> Atoms [Named (id,args)])
  | "parameter" ->
    let index = match field "index" j with
      | Number n -> (match int_of_string_opt n with
        | Some i when i >= 0 -> i
        | _ -> fail "invalid declaration parameter index")
      | _ -> fail "invalid declaration parameter index" in
    (match List.nth_opt ctx.positional index with
    | Some identity -> Rigid identity
    | None -> fail "declaration parameter index outside declaration")
  | "binder" -> (match List.assoc_opt (text "name" j) ctx.bindings with
    | Some (ValueArgument t) -> t
    | Some (ResolutionArgument (input,_,_,_)) -> input
    | Some (PackArgument _) -> unsupported "a type parameter types both a rest parameter's argument list and a value: an argument list is not a runtime value"
    | None -> fail "unbound rigid parameter")
  | "intersection" ->
    (* Function operands are one overloaded callable. A type parameter's
       intersection with other types, `V & DepSafe`, `T & U`, is `Meet` with
       the parameter first: in a declaration's equation it is read once the
       parameter is known, at the application; in a function's annotation it
       is a meet row, which Lean fills from the operands' rows. Elsewhere,
       record operands are the one object they describe, and any other ground
       operands, such as an array with a record's members, are kept as
       `Meet`, whose row Lean fills with its own meet. *)
    let parts = List.map recur (items "parts" j) in
    let callable = function
      | Atoms [Shape {fields=[];indexes=[];calls;elements=None}] when calls <> [] -> Some calls
      | _ -> None in
    let constructible = function
      | Atoms [Ctors (signatures,[])] -> Some signatures
      | _ -> None in
    let rigid = List.find_opt (function Rigid _ -> true | _ -> false) parts in
    (match rigid,parts with
     | Some rigid,_ ->
       (match List.filter (fun part -> part <> rigid) parts with
        | [] -> rigid
        | others -> Meet (rigid,others))
     | None,_ when List.for_all (fun part -> callable part <> None) parts ->
       Atoms [Shape {fields=[];indexes=[];calls=List.concat (List.filter_map callable parts);elements=None}]
     (* Construct operands are one overloaded constructor, `new Date()` and
        `new Date(v)`, as call operands are one overloaded callable. *)
     | None,_::_ when List.for_all (fun part -> constructible part <> None) parts ->
       Atoms [Ctors (List.concat (List.filter_map constructible parts),[])]
     | None,first::rest when ctx.owner <> None -> Meet (first,rest)
     | None,first::rest ->
       (match List.fold_left (fun acc part -> Option.bind acc (fun a -> meet_objects a part))
                (Some first) rest with
        | Some merged -> merged
        | None -> Meet (first,rest))
     | None,[] -> fail "empty intersection")
  | k -> unsupported ("type term " ^ k)
(* A pack parameter's bound: the argument lists of any number of an array's
   element, or of a tuple's required positions. *)
and pack_bound ctx t = match text "k" t with
  | "array" -> Pack {required=[];optional_elements=[];
      rest=Some (source_type ctx (field "element" t));readonly=false;presence=Dense}
  | "tuple" when items "optional" t = [] && field "rest" t = Null ->
    Pack {required=List.map (source_type ctx) (items "required" t);
      optional_elements=[];rest=None;readonly=false;presence=Dense}
  | _ -> unsupported "a pack parameter's bound is an array or a tuple"
and source_pack ctx j =
  (* A declaration's own parameter typing a rest inside the declaration is a
     packed one: its instances are arrays or tuples, the lists their elements
     form. *)
  if text "k" j = "parameter" then (match source_type ctx j with
    | Rigid r -> PackParameter r
    | _ -> unsupported "a pack rest must name a type parameter") else
  if text "k" j <> "binder" then unsupported "a pack rest must name a type parameter" else
  match List.assoc_opt (text "name" j) ctx.bindings with
  | Some (PackArgument p) -> p
  | Some (ValueArgument (Rigid r)) when ctx.value_packs -> PackParameter r
  | Some (ValueArgument _ | ResolutionArgument _) -> unsupported "a type parameter types both a value and a rest parameter's argument list: an argument list is not a runtime value"
  | None -> fail "unbound pack parameter"

type literal = LNull | LUndefined | LBool of bool | LNumber of string | LString of string
             | LBigint of string

let literal j = match text "a" j with
  | "null" -> LNull | "undefined" -> LUndefined
  | "booleanlit" -> LBool (text "v" j = "true")
  | "numberlit" -> LNumber (text "v" j) | "stringlit" -> LString (text "v" j)
  | "bigintlit" -> LBigint (text "v" j)
  | k -> unsupported ("literal " ^ k)
let optional_type binders = function Null -> None | j -> Some (source_type binders j)
(* A guard's promise as the Fragment states it: the parameter it is about, by
   position among the actuals, and its type. *)
let guard_of binders = function
  | Null -> None
  | j ->
    let param = natural (field "param" j) in
    Some (promise_effect (if boolean (field "asserts" j) then Asserts param else Guards param),
      source_type binders (field "type" j))
let span_start j = match list j with
  | Number n :: _ -> int_of_string n
  | _ -> Json.fail "empty source span"

(* Decode binders in declaration order. A bound sees outer and preceding
   binders, while the signature and body see the complete local frame. An
   inner spelling shadows an outer one without identifying their rigid IDs. *)
let quantify binders scope parameters =
  let rec loop index binders accumulated = function
    | [] -> binders,List.rev accumulated
    | p::rest ->
      let spelling=text "name" p in
      if List.exists (fun (q:quantifier) -> q.identity.spelling=spelling) accumulated
      then Json.fail "duplicate type parameter";
      let identity={scope;index=3*index;spelling} in
      let resolution=resolution_slots scope index p in
      let quantified={identity;bound=Option.map (fun t -> ValueArgument t)
        (optional_type binders (field "bound" p));default=None;resolution} in
      let hidden = match resolution with None -> [] | Some (observation,result) ->
        List.map (fun (r:rigid) -> r.spelling,ValueArgument (Rigid r)) (observation :: Option.to_list result) in
      let binders={binders with bindings=(spelling,ValueArgument (Rigid identity))::hidden @ binders.bindings} in
      loop (index+1) binders (quantified::accumulated) rest in
  loop 0 binders [] parameters
(* A binary operator on primitive operands: arithmetic, or a comparison. *)
type arithmetic = Add | Sub | Mul | Div | Pow | Rem | BitAnd | BitOr | Xor | Shl | Shr | Ushr | Lt | Le | Gt | Ge
let relational = function
  | Lt | Le | Gt | Ge -> true
  | Add | Sub | Mul | Div | Pow | Rem | BitAnd | BitOr | Xor | Shl | Shr | Ushr -> false
(* `-e`, `+e` and `~e`; and `typeof e`, the string naming the operand's shape. *)
type unary = Neg | Plus | BitNot | Typeof
type equality = StrictEqual | StrictUnequal | LooseEqual | LooseUnequal
(* `??=`, `||=` and `&&=`. *)
type logical = Nullish | OrElse | AndAlso

(* This is a typed view of the shared Fragment, not a new source language.
   Unknown cases fail here; inference exhaustively matches implemented cases. *)
type expr = { pos: Json.t; node: expr_node }
and expr_node =
  | Id of string | Literal of literal | Not of expr | Arith of arithmetic * expr * expr
  (* `a && b` (true) or `a || b` (false): the left operand's value, or the
     right's where the left is truthy (`&&`) or falsy (`||`). *)
  | Logical of bool * expr * expr
  | Unary of unary * expr
  (* `typeof e === "shape"` (equal) or `!==`: a test of the operand's shape. *)
  | TypeofTest of string * bool * expr
  (* `key in e`: the key, then whether the operand has it. *)
  | HasKey of expr * expr
  (* `e instanceof C` of a class of the file: the operand, then a read of the
     class's prototype object, then whether the key only that object owns is
     along the operand's prototype chain. *)
  | InstanceTest of string * expr * expr
  | Equality of equality * expr * expr | Alloc of (key * expr) list
  (* An object literal with spreads of values: its parts in source order, a
     named field (`Some key`) or a spread (`None`). *)
  | Build of (string option * expr) list
  (* A named read: a string key, or the symbol key of `e[k]` with `k` a
     `unique symbol` constant. *)
  | Read of expr * key | Write of expr * key * expr
  | Assign of string * expr
  (* `target op= rhs`, or an increment where the right side is absent: the
     target (a local, a field or a named index) is read and written back. The
     flag makes the old value the expression's. *)
  | Update of arithmetic * expr * expr option * bool
  (* `target ??= rhs`, `||=` or `&&=` on a field or named index, or a Boolean
     local: the right side is evaluated and written only where the test on
     the target's value asks for it. *)
  | LogicalAssign of logical * expr * expr
  (* `name ??= rhs` on a local: the name's read is claimed at its own position. *)
  | NullishAssign of string * Json.t * expr
  (* `left, right`: the left operand for its effects, then the right one's
     value. `void e` is `e, undefined`. *)
  | Comma of expr * expr
  (* `[a, b = d, ...r] = rhs`: the right side once, then each mutable local,
     at its position, takes its read, or its default where the read is
     undefined, and the rest's, the fresh array of the positions from its
     index on, claimed at its span. The expression's value is the right
     side's. *)
  (* A rest's index, span, local and whether it is a slice, which
     `%RestFrom:k%` collects. *)
  (* Each target a local ([Id]) or a field ([Read], [Index]). *)
  | ArrayAssign of (int * expr * expr option) list * (int * Json.t * expr * bool) option * expr
  (* A parameter's type is what the body reads. A defaulted one also admits
     `undefined` where the closure is called; the default replaces it. A rest
     parameter reads the tuple its arguments are collected into, and the
     signature has one position per required element of that tuple. The
     receiver is the `this` annotation of an ordinary function, none for an
     arrow, whose `this` is the enclosing one. *)
  (* The result is none where the source states no result annotation: the
     producer proposes it, and Lean checks the body against that claim. *)
  (* A guard closure's promise, its result annotation `x is T` or `asserts x
     is T`: the promise signature's effect and type, beside the plain result. *)
  | Lambda of ty option * quantifier list * (string * ty) list * (int * expr) list * bool * ty option
      * (call_effect * ty) option * expr
  (* The positions of the arguments written with `...`: each stands for the
     elements of its operand, read where it is written. The types are the
     explicit type arguments written on the call, if any. *)
  | Call of expr * expr option * expr list * int list * ty list
  (* A call through a property reference: the callee is the read of the
     method, and the object it is read from is the receiver. The types are the
     explicit type arguments written on the call, if any. *)
  | Invoke of expr * expr list * int list * ty list
  (* `f.apply(r, list)`: the list's elements, read by index, are the actuals. *)
  | Apply of expr * expr * expr option
  (* A class value: its constructor, and its static fields, each the binding
     its initializer bound, in member order. *)
  | Ctor of expr * (Semantic.key * expr) list
  (* `new callee<types>(args)`: the explicit type arguments, if written,
     name the instantiation proposed for a generic class. *)
  | New of expr * ty list * expr list * int list
  | Conditional of expr * expr * expr | Coalesce of expr * expr
  (* An optional chain: the receiver once, `undefined` where it is nullish,
     else the body, which reads the receiver as `?.`. *)
  | Optional of expr * expr
  (* An array literal's elements, and the positions of those written with
     `...`, each standing for its operand's elements. *)
  | ArrayLiteral of expr list * int list | Index of expr * expr | IndexWrite of expr * expr * expr
  | Bind of expr * expr * expr list
  (* `Object.assign(target, ...sources)`, other than the callable form: the
     target, then each source copied onto it as it is evaluated. *)
  | ObjectAssign of expr * expr list
  | WithFields of expr * expr * ty * ty
  | Cast of string * ty option * expr
  (* A closure's body written as statements, a function body: its
     parameters written as patterns or with defaults are destructured by its
     first statements, and a body that can complete returns `undefined` at
     its closing brace. Only a lambda's body is one. *)
  | BlockBody of stmt list
and stmt = { span: Json.t; statement: stmt_node }
(* What a pattern binds at one place: a name, at its span, or a nested
   pattern over the value found there. An object pattern's properties read
   their fields; an array pattern's elements read their positions, and its
   rest, claimed at its span, collects the positions from its index on. Each
   element's default replaces a read that is undefined. *)
and pattern =
  | PName of string * Json.t
  (* An object pattern's rest, claimed at its span, is a fresh object holding
     the source's other own enumerable properties. *)
  | PObject of (string * pattern * expr option) list * (Json.t * pattern) option
  (* A rest's index, span, whether it is a slice (`%RestFrom:k%`), target. *)
  | PArray of (int * pattern * expr option) list * (int * Json.t * bool * pattern) option
and stmt_node =
  | Declare of bool * (string * ty option * expr) list
  (* `const target = init`, the default (a parameter's) replacing an
     undefined initializer. *)
  | Destructure of pattern * expr option * expr
  | Return of expr | Effect of expr | If of expr * stmt list * stmt list
  (* The condition, the body, and the update the body's end and every
     `continue` run: a `for`'s, none for a `while`. *)
  (* A `break` carries the label of the block it leaves, or none for a loop. *)
  | While of expr * stmt list * stmt list | Break of string option | Continue
  (* A block, labeled (a `break` may leave it) when it is part of a lowered
     `switch`. *)
  | Block of string option * stmt list
  (* `for (const name of iterable) body`: the name's position, the
     iteration intrinsic stepping the iterable (`%Iterate%` for an array),
     the iterable and the body. *)
  | ForOf of string * Json.t * string * expr * stmt list
  (* `throw e`. *)
  | Throw of expr
  (* `try body catch (param) handler finally finalizer`: the handler's
     parameter, with its position, if it names one. *)
  | Try of stmt list * ((string * Json.t) option * stmt list) option * stmt list option
  (* The body of a `for...of` over a program's iterable, the last statement
     of its loop: the close (IteratorClose), then the body. The close runs
     where the body is left by a `break` of the loop, a `return` or a throw. *)
  | Closing of stmt list * stmt list
and fn = { quantified: quantifier list; name: string; name_pos: Json.t; params: (string * ty) list;
           rest: bool;
           (* A rest typed by one of the function's own type parameters: that
              parameter, an argument pack each call instantiates. The rest's
              type in [params] is the parameter's bound, the array the body
              sees. *)
           rest_pack: rigid option; result: ty;
           (* A guard's promise, beside its plain result: the promise
              signature's effect and type. *)
           guard: (call_effect * ty) option; body: stmt list }
type declaration = { id: string; native_promise: bool; parameters: rigid list;
  bases: ty list; expression: ty option }
(* `init` is the module's top-level code, run once after its function
   declarations exist. *)
(* `values` are the client's value imports, at the types their declarations
   state: assumptions, not checked here. *)
type program = { file: Json.t; digest: Json.t; declarations: declaration list;
                 functions: fn list; init: stmt list; values: (string * ty) list;
                 (* The binders of the generic classes the top-level code
                    declares: the initialization unit's. *)
                 init_quantified: quantifier list }

(* A pattern's defaults, in evaluation order. *)
let rec pattern_defaults = function
  | PName _ -> []
  | PObject (props,rest) -> List.concat_map (fun (_,t,d) -> Option.to_list d @ pattern_defaults t) props @
    (match rest with Some (_,t) -> pattern_defaults t | None -> [])
  | PArray (elems,rest) -> List.concat_map (fun (_,t,d) -> Option.to_list d @ pattern_defaults t) elems
      @ (match rest with Some (_,_,_,t) -> pattern_defaults t | None -> [])

(* The names a pattern binds, and whether it only reads: no rest, which
   allocates. *)
let rec pattern_names = function
  | PName (n,_) -> [n]
  | PObject (props,rest) -> List.concat_map (fun (_,t,_) -> pattern_names t) props @
    (match rest with Some (_,t) -> pattern_names t | None -> [])
  | PArray (elems,rest) -> List.concat_map (fun (_,t,_) -> pattern_names t) elems @
    (match rest with Some (_,_,_,t) -> pattern_names t | None -> [])
let rec pattern_reads = function
  | PName _ -> true
  | PObject (props,rest) -> rest=None && List.for_all (fun (_,t,_) -> pattern_reads t) props
  | PArray (elems,rest) -> rest=None && List.for_all (fun (_,t,_) -> pattern_reads t) elems

(* The immediate subexpressions of a form, and those of a closure body's
   statements. *)
let rec children e = match e.node with
  | Id _ | Literal _ -> []
  | BlockBody ss -> List.concat_map statement_children ss
  | Not e | TypeofTest (_,_,e) | Read (e,_) | Cast (_,_,e) | Unary (_,e) -> [e]
  | Ctor (e,statics) -> e :: List.map snd statics
  | Assign (_,e) | NullishAssign (_,_,e) -> [e]
  | Update (_,t,r,_) -> t :: Option.to_list r
  | LogicalAssign (_,a,b) | Comma (a,b) | HasKey (a,b) | InstanceTest (_,a,b) -> [a;b]
  | ArrayAssign (targets,rest,rhs) ->
    rhs :: List.concat_map (fun (_,t,d) -> t :: Option.to_list d) targets
    @ (match rest with Some (_,_,t,_) -> [t] | None -> [])
  | Arith (_,a,b) | Equality (_,a,b) | Write (a,_,b) | Coalesce (a,b) | Optional (a,b) | Index (a,b) | Logical (_,a,b)
  | WithFields (a,b,_,_) -> [a;b]
  | Conditional (a,b,c) | IndexWrite (a,b,c) -> [a;b;c]
  | Alloc fs -> List.map snd fs
  | Build parts -> List.map snd parts
  | ArrayLiteral (es,_) -> es
  | Lambda (_,_,_,defaults,_,_,_,body) -> List.map snd defaults @ [body]
  | Call (f,r,args,_,_) -> f :: Option.to_list r @ args
  | Invoke (f,args,_,_) | New (f,_,args,_) -> f :: args
  | Apply (f,r,l) -> f :: r :: Option.to_list l
  | Bind (f,r,args) -> f :: r :: args
  | ObjectAssign (t,sources) -> t :: sources
and statement_children s = match s.statement with
  | Declare (_,bs) -> List.map (fun (_,_,e) -> e) bs
  | Destructure (t,d,init) -> init :: Option.to_list d @ pattern_defaults t
  | Return e | Effect e | Throw e -> [e]
  | If (c,a,b) -> c :: List.concat_map statement_children (a @ b)
  | While (c,b,u) -> c :: List.concat_map statement_children (b @ u)
  | Block (_,b) -> List.concat_map statement_children b
  | ForOf (_,_,_,i,b) -> i :: List.concat_map statement_children b
  | Try (b,h,f) -> List.concat_map statement_children
      (b @ (match h with Some (_,hs) -> hs | None -> []) @ Option.value f ~default:[])
  | Closing (c,b) -> List.concat_map statement_children (b @ c)
  | Break _ | Continue -> []
(* Whether a name is assigned anywhere in a form, nested closures included:
   such a binding is a cell. Lean decides storage the same way, from the
   source (`assignsStmt`); this only proposes consistently with it. *)
let rec assigns_expr name e = match e.node with
  | Assign (n,_) | NullishAssign (n,_,_) when n = name -> true
  | Update (_,{node=Id n;_},_,_) | LogicalAssign (_,{node=Id n;_},_) when n = name -> true
  | ArrayAssign (targets,rest,_) when List.exists (fun (_,t,_) -> t.node = Id name) targets
      || (match rest with Some (_,_,t,_) -> t.node = Id name | None -> false) -> true
  | _ -> List.exists (assigns_expr name) (children e)
let rec assigns name s = match s.statement with
  | Declare (_,bs) -> List.exists (fun (_,_,e) -> assigns_expr name e) bs
  | Destructure (target,d,init) ->
    List.exists (assigns_expr name) (init :: Option.to_list d @ pattern_defaults target)
  | Return e | Effect e -> assigns_expr name e
  | If (c,a,b) -> assigns_expr name c || List.exists (assigns name) (a @ b)
  | While (c,body,update) -> assigns_expr name c || List.exists (assigns name) (body @ update)
  | ForOf (_,_,_,c,body) -> assigns_expr name c || List.exists (assigns name) body
  | Block (_,body) -> List.exists (assigns name) body
  | Throw e -> assigns_expr name e
  | Try (body,handler,finalizer) -> List.exists (assigns name)
    (body @ (match handler with Some (_,h) -> h | None -> []) @ Option.value finalizer ~default:[])
  | Closing (close,body) -> List.exists (assigns name) (body @ close)
  | Break _ | Continue -> false
(* A definition-level proposal, never a call-site assumption: the closed
   footprint a body's runs stay within, or [None] where the analysis cannot
   bound them. Reads, tests, arithmetic and fresh allocations change nothing;
   an assignment to a variable changes at most a cell holding a value, which
   [cell_write] bounds; a call or a construction changes at most what every
   signature its callee may take states ([callable]: call signatures, or
   construct signatures). Creation does not execute a closure's code. Lean
   checks every node of the body against the proposed footprint, and each
   call at the signature it selects.
   Every constructor is listed so extensions require a decision here. *)
let join_change a b = match a,b with
  | Any,_ | _,Any -> Any | Grow,_ | _,Grow -> Grow | Keep,Keep -> Keep
let join_footprint a b =
  {on_value=join_change a.on_value b.on_value;on_store=join_change a.on_store b.on_store}
let join_bound a b = match a,b with Some a,Some b -> Some (join_footprint a b) | _ -> None
let cell_write = Some {on_value=Any;on_store=Keep}
(* The footprint a `for...of` runs its iteration within, read off the
   iteration intrinsic's type: its call, which creates the iterator, then
   each call of the step the iterator is. *)
let iteration_footprint (t:ty) : footprint option =
  let join_calls calls = List.fold_left (fun acc (s:signature) -> join_footprint acc s.call_effect.footprint)
    empty_footprint calls in
  match t with
  | Atoms [Shape {calls=(_ :: _ as calls);_}] ->
    List.fold_left (fun acc (s:signature) -> join_bound acc (match s.result with
      | Atoms [Shape {calls=(_ :: _ as steps);_}] -> Some (join_footprint s.call_effect.footprint (join_calls steps))
      | _ -> None)) (Some empty_footprint) calls
  | _ -> None
(* The footprint of a call at every signature its callee may take: each
   signature's, or, where it excepts its receiver's store and the receiver's
   store is not one the run allocated, the one letting everything change. *)
let effects_footprint ~receiver_fresh (effects:call_effect list) =
  List.fold_left (fun acc (e:call_effect) -> join_footprint acc
    (if e.receiver_store && not receiver_fresh then top_footprint else e.footprint)) empty_footprint effects
(* A value whose array store the run allocated: a constant holding one, or a
   call every signature of whose callee states a fresh result. Lean's facts
   follow slots of the graph, which a constant's binding is. *)
let fresh_expr ~callable ~fresh (e:expr) = match e.node with
  | Id name -> List.mem name fresh
  | Call (callee,_,_,_,_) | Invoke (callee,_,_,_) ->
    (match callable callee with
     | Some (_ :: _ as effects) -> List.for_all (fun (e:call_effect) -> e.fresh) effects
     | _ -> false)
  | _ -> false
let rec footprint_expr ?(fresh=[]) ~callable ~iteration ~readable (e:expr) : footprint option =
  let go = footprint_expr ~fresh ~callable ~iteration ~readable in
  let calls ?(receiver_fresh=false) callee =
    Option.map (effects_footprint ~receiver_fresh) (callable callee) in
  let all es = List.fold_left (fun acc e -> join_bound acc (go e)) (Some empty_footprint) es in
  match e.node with
  | Id name -> if List.mem name readable then Some empty_footprint else None
  | Literal _ -> Some empty_footprint
  | Not a | TypeofTest (_,_,a) | Cast (_,_,a) -> go a
  | Arith (_,a,b) | Comma (a,b) -> all [a;b]
  | Logical (_,a,b) | Coalesce (a,b) -> all [a;b]
  | Conditional (c,a,b) -> all [c;a;b]
  (* A read changes no location: Lean's inspection rule admits any read of a
     field or an element, ordinary safety supplying that it does not stick. *)
  | Read (a,_) -> go a
  | Index (a,b) | Equality (_,a,b) -> all [a;b]
  | Alloc fields -> all (List.map snd fields)
  (* A spread part reads its operand's store, an array; the parser writes a
     spread of any other iterable as its spread intrinsic's call, whose
     signature states its footprint. *)
  | ArrayLiteral (es,_) -> all es
  | Lambda _ -> Some empty_footprint
  (* A variable's new value goes to its slot, or to its cell, a location
     holding a value (Lean's typed write rule). *)
  | Assign (_,v) -> join_bound cell_write (go v)
  | Update (_,{node=Id _;_},r,_) -> join_bound cell_write (all (Option.to_list r))
  (* A spread argument reads its operand's store, as an array literal's
     spread part does. *)
  | Call (callee,receiver,args,_,_) ->
    join_bound (all (callee :: Option.to_list receiver @ args)) (calls callee)
  (* A method call reads the member off its receiver (through a primitive's
     prototype, for a primitive) and invokes it: a member excepting its
     receiver's store is within its footprint where the receiver is a
     constant holding a store the run allocated. *)
  | Invoke ({node=Read (o,_);_} as callee,args,_,_) ->
    let receiver_fresh = match o.node with Id name -> List.mem name fresh | _ -> false in
    join_bound (all (o :: args)) (calls ~receiver_fresh callee)
  (* A construction changes at most what every construct signature its
     callee may take states. *)
  | New (callee,_,args,spreads) ->
    if spreads<>[] then None else join_bound (all (callee :: args)) (calls callee)
  (* An optional chain runs its receiver once, then its body, which reads
     the receiver as `?.`, where the receiver is present. *)
  | Optional (r,b) -> join_bound (go r) (footprint_expr ~fresh ~callable ~iteration ~readable:("?." :: readable) b)
  | BlockBody body -> footprint_stmts ~fresh ~callable ~iteration ~readable body
  | Unary _ | HasKey _ | InstanceTest _ | Build _
  | Write _ | Update _ | LogicalAssign _ | NullishAssign _
  | ArrayAssign _ | Invoke _ | Apply _ | Ctor _
  | IndexWrite _ | Bind _ | ObjectAssign _
  | WithFields _ -> None
and footprint_stmts ?(fresh=[]) ~callable ~iteration ~readable = function
  | [] -> Some empty_footprint
  | s::rest ->
    let go = footprint_expr ~fresh ~callable ~iteration ~readable in
    let block ?(fresh=fresh) readable body = footprint_stmts ~fresh ~callable ~iteration ~readable body in
    let tail () = block readable rest in
    match s.statement with
    | Declare (mutable_,bindings) ->
      let rec add fresh readable acc = function
        | [] -> join_bound acc (block ~fresh readable rest)
        | (name,_,init)::more ->
          let fresh = if not mutable_ && fresh_expr ~callable ~fresh init then name :: fresh
            else List.filter ((<>) name) fresh in
          add fresh (name::readable) (join_bound acc (footprint_expr ~fresh ~callable ~iteration ~readable init)) more in
      add fresh readable (Some empty_footprint) bindings
    | Return e | Effect e | Throw e -> join_bound (go e) (tail ())
    | If (c,a,b) -> join_bound (go c) (join_bound (block readable a) (join_bound (block readable b) (tail ())))
    | Block (_,body) -> join_bound (block readable body) (tail ())
    | While (c,body,update) ->
      join_bound (go c) (join_bound (block readable (body @ update)) (tail ()))
    | Break _ | Continue -> tail ()
    (* A pattern without a rest reads fields and positions of its
       initializer's value and binds them. *)
    | Destructure (target,d,init) when pattern_reads target ->
      List.fold_left join_bound (go init)
        (Option.to_list (Option.map go d) @ List.map go (pattern_defaults target) @
         [footprint_stmts ~fresh:(List.filter (fun n -> not (List.mem n (pattern_names target))) fresh)
            ~callable ~iteration ~readable:(pattern_names target @ readable) rest])
    | ForOf (name,_,iterate,iterable,body) ->
      join_bound (go iterable) (join_bound (iteration iterate)
        (join_bound (block ~fresh:(List.filter ((<>) name) fresh) (name::readable) body) (tail ())))
    | Destructure _ | Try _ | Closing _ -> None

(* Whether every normal return of a body returns a value whose array store
   the run allocated: an expression body that is one, or a block of
   declarations and expression statements ending in a `return` of one. *)
let fresh_result ~callable (body:expr) =
  let rec returns fresh = function
    | [{statement=Return e;_}] -> fresh_expr ~callable ~fresh e
    | {statement=Declare (mutable_,bindings);_} :: rest ->
      returns (List.fold_left (fun fresh (name,_,init) ->
        if not mutable_ && fresh_expr ~callable ~fresh init then name :: fresh
        else List.filter ((<>) name) fresh) fresh bindings) rest
    | {statement=Effect _;_} :: rest -> returns fresh rest
    | _ -> false in
  match body.node with
  | BlockBody stmts -> returns [] stmts
  | _ -> fresh_expr ~callable ~fresh:[] body

let arithmetic = function
  | "add" -> Add | "sub" -> Sub | "mul" -> Mul | "div" -> Div | "pow" -> Pow | "rem" -> Rem
  | "bitAnd" -> BitAnd | "bitOr" -> BitOr | "xor" -> Xor | "shl" -> Shl | "shr" -> Shr | "ushr" -> Ushr
  | "lt" -> Lt | "le" -> Le | "gt" -> Gt | "ge" -> Ge
  | k -> unsupported ("arithmetic " ^ k)
let rec expr binders j =
  let sub k = expr binders (field k j) in
  let node = match text "k" j with
  | "id" -> Id (text "name" j) | "lit" -> Literal (literal (field "lit" j))
  | "this" -> Id "this"
  | "not" -> Not (sub "e")
  | "unary" -> Unary ((match text "op" j with
      | "neg" -> Neg | "plus" -> Plus | "bitNot" -> BitNot | "typeof" -> Typeof
      | k -> unsupported ("unary operator " ^ k)),sub "e")
  | "typeofTest" -> TypeofTest (text "shape" j,boolean (field "equal" j),sub "e")
  (* `Array.isArray(e)`: a test of the operand's shape, the array one. *)
  | "arrayTest" -> TypeofTest ("array",true,sub "e")
  | "inTest" -> HasKey (sub "key",sub "e")
  | "instanceTest" -> InstanceTest (text "key" j,sub "e",sub "proto")
  | "arith" -> Arith (arithmetic (text "op" j),sub "l",sub "r")
  | "update" -> Update (arithmetic (text "op" j),sub "target",
      (match field "rhs" j with Null -> None | r -> Some (expr binders r)),boolean (field "post" j))
  | "logicalAssign" -> LogicalAssign ((match text "op" j with
      | "nullish" -> Nullish | "or" -> OrElse | "and" -> AndAlso
      | k -> unsupported ("logical assignment " ^ k)),sub "target",sub "rhs")
  | "nullishAssign" -> NullishAssign (text "name" j,field "namePos" j,sub "rhs")
  | "comma" -> Comma (sub "left",sub "right")
  | "arrayAssign" ->
    let index q = int_of_string (match field "index" q with
      | Json.Number n -> n | _ -> Json.fail "an index is a number") in
    ArrayAssign (List.map (fun q -> index q,expr binders (field "target" q),
      (match field "default_" q with Null -> None | d -> Some (expr binders d))) (items "targets" j),
      (match field "rest" j with Null -> None
        | r -> Some (index r,field "pos" r,expr binders (field "target" r),Json.boolean (field "slice" r))),
      sub "rhs")
  | "bin" when text "op" j = "&&" || text "op" j = "||" ->
    Logical (text "op" j = "&&",sub "l",sub "r")
  | "bin" -> let op = match text "op" j with
      | "===" -> StrictEqual | "!==" -> StrictUnequal
      | "==" -> LooseEqual | "!=" -> LooseUnequal
      | k -> unsupported ("operator " ^ k) in Equality (op,sub "l",sub "r")
  | "alloc" ->
    (* A class instance's prototype, under the key no source property spells. *)
    let proto = match List.assoc_opt "proto" (Json.obj j) with
      | Some e -> [Name "[[proto]]",expr binders e] | None -> [] in
    (* A prototype `instanceof` tests owns its class's key, at `undefined`. *)
    let brand = match List.assoc_opt "brand" (Json.obj j) with
      | Some b -> [Name (text "key" b),{pos=field "pos" b;node=Literal LUndefined}] | None -> [] in
    Alloc (proto @ brand @ List.map (fun f -> property_key (field "name" f),expr binders (field "e" f)) (items "fields" j))
  | "build" ->
    let proto = match List.assoc_opt "proto" (Json.obj j) with
      | Some e -> [Some "[[proto]]",expr binders e] | None -> [] in
    Build (proto @ List.map (fun p -> match List.assoc_opt "spread" (Json.obj p) with
      | None -> Some (text "name" p),expr binders (field "e" p)
      | Some e -> None,expr binders e) (items "parts" j))
  | "read" -> Read (sub "e",property_key (field "field" j))
  | "write" -> Write (sub "receiver",property_key (field "field" j),sub "rhs")
  | "assign" -> Assign (text "name" j,sub "rhs")
  | "lambda" ->
      let inner,quantified = quantify binders (-1 - span_start (field "pos" j))
        (items "typeParams" j) in
      let parameters = items "params" j in
      let rest = List.exists (fun p -> List.mem_assoc "rest" (obj p)) parameters in
      let receiver = match field "receiver" j with
        | Null -> None
        | r ->
          (* The receiver is bound unchanged. Sloppy code converts a receiver
             that is not an object, observable only where the body reads
             `this`; Lean admits that only at a receiver type of objects,
             which the conversion leaves unchanged. *)
          Some (source_type inner (field "type" r)) in
      Lambda (receiver,quantified,
        List.map (fun p -> text "name" p,source_type inner (field "type" p)) parameters,
        List.filter_map (fun (i,p) -> match List.assoc_opt "default" (obj p) with
          | None -> None
          | Some d -> Some (i, expr inner d))
          (List.mapi (fun i p -> i,p) parameters),
        rest,
        optional_type inner (field "result" j),
        guard_of inner (field "guard" j),
        expr inner (field "body" j))
  | "ctor" -> Ctor (sub "lambda",match List.assoc_opt "statics" (obj j) with
      | None -> []
      | Some fs -> List.map (fun f -> property_key (field "name" f),expr binders (field "e" f)) (list fs))
  | "new" ->
    let types = match List.assoc_opt "typeArgs" (obj j) with
      | None -> [] | Some ts -> List.map (source_type binders) (list ts) in
    let spreads = match List.assoc_opt "spreads" (obj j) with
      | None -> [] | Some s -> List.map (fun n -> int_of_string (match n with
          | Json.Number n -> n | _ -> Json.fail "a spread position is a number")) (list s) in
    New (sub "callee",types,List.map (expr binders) (items "args" j),spreads)
  | "apply" ->
    let spreads = match List.assoc_opt "spreads" (obj j) with
      | None -> [] | Some s -> List.map (fun n -> int_of_string (match n with
          | Json.Number n -> n | _ -> Json.fail "a spread position is a number")) (list s) in
    let type_args = match List.assoc_opt "typeArgs" (obj j) with
      | None -> [] | Some ts -> List.map (source_type binders) (list ts) in
    Call (sub "callee",None,List.map (expr binders) (items "args" j),spreads,type_args)
  | "invoke" ->
    let spreads = match List.assoc_opt "spreads" (obj j) with
      | None -> [] | Some s -> List.map (fun n -> int_of_string (match n with
          | Json.Number n -> n | _ -> Json.fail "a spread position is a number")) (list s) in
    let type_args = match List.assoc_opt "typeArgs" (obj j) with
      | None -> [] | Some ts -> List.map (source_type binders) (list ts) in
    Invoke (sub "callee",List.map (expr binders) (items "args" j),spreads,type_args)
  | "applyWithReceiver" ->
    Apply (sub "callee",sub "receiver",(match field "list" j with Null -> None | l -> Some (expr binders l)))
  | "callWithReceiver" ->
    Call (sub "callee",Some (sub "receiver"),List.map (expr binders) (items "args" j),[],[])
  | "coalesce" -> Coalesce (sub "left",sub "right")
  | "optional" -> Optional (sub "receiver",sub "body")
  | "arrayLit" ->
    let spreads = match List.assoc_opt "spreads" (obj j) with
      | None -> [] | Some s -> List.map (fun n -> int_of_string (match n with
          | Json.Number n -> n | _ -> Json.fail "a spread position is a number")) (list s) in
    ArrayLiteral (List.map (expr binders) (items "elems" j),spreads)
  | "index" -> Index (sub "e",sub "key")
  | "indexWrite" -> IndexWrite (sub "receiver",sub "key",sub "rhs")
  | "withValue" -> WithFields (sub "fn",sub "initial",source_type binders (field "functionType" j),source_type binders (field "bagType" j))
  | "bindWithReceiver" -> Bind (sub "callee",sub "receiver",List.map (expr binders) (items "args" j))
  | "objectAssign" -> ObjectAssign (sub "target",List.map (expr binders) (items "sources" j))
  | "cast" -> Cast (text "cast" j,(match field "annot" j with Null -> None | a -> Some (source_type binders a)),sub "e")
  | "blockBody" -> BlockBody (List.map (stmt binders) (items "body" j))
  | "conditional" -> Conditional (sub "cond",sub "then",sub "else_")
  | k -> unsupported ("expression " ^ k) in {pos=field "pos" j;node}
and pattern binders j =
  let target q = pattern binders (field "target" q) and default q = match field "default_" q with
    | Null -> None | d -> Some (expr binders d) in
  let index q = int_of_string (match field "index" q with
    | Json.Number n -> n | _ -> Json.fail "an index is a number") in
  match text "k" j with
  | "name" -> PName (text "name" j,field "pos" j)
  | "object" -> PObject (List.map (fun q -> text "field" q,target q,default q) (items "props" j),
      match field "rest" j with Null -> None | r -> Some (field "pos" r,target r))
  | "array" -> PArray (List.map (fun q -> index q,target q,default q) (items "elems" j),
      match field "rest" j with Null -> None
        | r -> Some (index r,field "pos" r,Json.boolean (field "slice" r),target r))
  | k -> unsupported ("pattern " ^ k)
and stmt binders j =
  let statement = match text "k" j with
  | "destructure" -> Destructure (pattern binders (field "target" j),
      (match field "default_" j with Null -> None | d -> Some (expr binders d)),
      expr binders (field "init" j))
  | "const" | "let" -> Declare (text "k" j="let",List.map (fun b ->
      text "name" b,optional_type binders (field "annot" b),expr binders (field "init" b)) (items "bindings" j))
  | "return" -> Return (expr binders (field "e" j)) | "effect" -> Effect (expr binders (field "e" j))
  | "while" -> While (expr binders (field "cond" j),List.map (stmt binders) (items "body" j),
      List.map (stmt binders) (items "update" j))
  | "block" -> Block ((match field "label" j with Null -> None | l -> Some (Json.str l)),List.map (stmt binders) (items "body" j))
  | "forOf" -> ForOf (text "name" j,field "namePos" j,text "iterate" j,expr binders (field "iterable" j),
      List.map (stmt binders) (items "body" j))
  | "break" -> Break (match field "label" j with Null -> None | l -> Some (Json.str l))
  | "continue" -> Continue
  | "throw" -> Throw (expr binders (field "e" j))
  | "try" ->
    let block k = List.map (stmt binders) (items k j) in
    let handler = match field "handler" j with
      | Null -> None
      | h ->
        let param = match field "param" h with
          | Null -> None
          | p -> Some (text "name" p,field "namePos" p) in
        Some (param,List.map (stmt binders) (items "body" h)) in
    let finalizer = match field "finalizer" j with
      | Null -> None
      | xs -> Some (List.map (stmt binders) (list xs)) in
    Try (block "body",handler,finalizer)
  | "closing" -> Closing (List.map (stmt binders) (items "close" j),List.map (stmt binders) (items "body" j))
  | "if" -> If (expr binders (field "cond" j),List.map (stmt binders) (items "then" j),
      match field "else_" j with Null -> [] | xs -> List.map (stmt binders) (list xs))
  | k -> unsupported ("statement " ^ k) in {span=field "pos" j;statement}
(* The calls whose array result nothing shrinks: read by index at once, or
   bound to a constant every use of which reads it (an element, its length,
   a member that reads, an iteration). A signature whose result has required
   positions, `split`'s non-empty form, is proposed only there: such a store
   contract forbids a removal. A proposal; Lean checks every call. *)
let reading_members = ["map";"filter";"every";"some";"forEach";"join";"slice";"at";"indexOf";
  "lastIndexOf";"includes";"find";"findIndex";"flatMap";"reduce";"reduceRight";"entries";"keys";"values"]
let rec reads_only name (e:expr) = match e.node with
  | Id n -> n <> name
  | Index ({node=Id n;_},k) when n = name -> reads_only name k
  (* An element at a computed index, read through `%ElementAt%`. *)
  | Call ({node=Id "%ElementAt%";_},_,{node=Id n;_} :: rest,_,_) when n = name ->
    List.for_all (reads_only name) rest
  | Read ({node=Id n;_},Name "length") when n = name -> true
  | Invoke ({node=Read ({node=Id n;_},Name m);_},args,_,_) when n = name && List.mem m reading_members ->
    List.for_all (reads_only name) args
  | IndexWrite ({node=Id n;_},_,_) | Write ({node=Id n;_},_,_) when n = name -> false
  | _ -> List.for_all (reads_only name) (children e)
and stmts_read_only name ss = List.for_all (fun s -> match s.statement with
  | ForOf (_,_,_,{node=Id n;_},b) when n = name -> stmts_read_only name b
  | If (c,a,b) -> reads_only name c && stmts_read_only name (a @ b)
  | While (c,b,u) -> reads_only name c && stmts_read_only name (b @ u)
  | Block (_,b) -> stmts_read_only name b
  | ForOf (_,_,_,i,b) -> reads_only name i && stmts_read_only name b
  | Try (b,h,f) -> stmts_read_only name (b @ (match h with Some (_,hs) -> hs | None -> []) @ Option.value f ~default:[])
  | Closing (c,b) -> stmts_read_only name (b @ c)
  | _ -> List.for_all (reads_only name) (statement_children s)) ss
let unshrunk : Json.t list ref = ref []
let rec collect_unshrunk_expr (e:expr) =
  (match e.node with
   | Index (({node=(Call _ | Invoke _);_} as c),_)
   | Call ({node=Id "%ElementAt%";_},_,({node=(Call _ | Invoke _);_} as c) :: _,_,_) -> unshrunk := c.pos :: !unshrunk
   | _ -> ());
  List.iter collect_unshrunk_expr (children e);
  match e.node with
  | BlockBody ss -> collect_unshrunk_stmts ss
  | _ -> ()
and collect_unshrunk_stmts = function
  | [] -> ()
  | s :: rest ->
    (match s.statement with
     | Declare (false,[(name,None,({node=(Call _ | Invoke _);_} as init))]) when stmts_read_only name rest ->
       unshrunk := init.pos :: !unshrunk
     (* A conditional's call arm, the value the constant holds where it is
        taken. *)
     | Declare (false,[(name,None,{node=Conditional (_,a,b);_})]) when stmts_read_only name rest ->
       List.iter (fun (arm:expr) -> match arm.node with
         | Call _ | Invoke _ -> unshrunk := arm.pos :: !unshrunk
         | _ -> ()) [a;b]
     | _ -> ());
    (match s.statement with
     | If (_,a,b) -> collect_unshrunk_stmts a; collect_unshrunk_stmts b
     | While (_,b,u) -> collect_unshrunk_stmts b; collect_unshrunk_stmts u
     | Block (_,b) | ForOf (_,_,_,_,b) -> collect_unshrunk_stmts b
     | Try (b,h,f) -> collect_unshrunk_stmts b;
       Option.iter (fun (_,hs) -> collect_unshrunk_stmts hs) h; Option.iter collect_unshrunk_stmts f
     | Closing (c,b) -> collect_unshrunk_stmts b; collect_unshrunk_stmts c
     | _ -> ());
    List.iter collect_unshrunk_expr (match s.statement with
      | If (c,_,_) | While (c,_,_) -> [c]
      | ForOf (_,_,_,i,_) -> [i]
      | Block _ | Try _ | Closing _ -> []
      | _ -> statement_children s);
    collect_unshrunk_stmts rest

let rec decode ast =
  let program = decode_program ast in
  unshrunk := [];
  List.iter (fun (f:fn) -> collect_unshrunk_stmts f.body) program.functions;
  collect_unshrunk_stmts program.init;
  program
and decode_program ast =
  let document = field "declarations" ast in
  let arity = List.map (fun definition ->
    let parameters = items "parameters" definition in
    identity (field "declaration" definition),
      (* A reference carries every argument, the omitted ones completed
         where it is read. *)
      (List.length parameters, List.length parameters)) (items "definitions" document) in
  let definitions = List.mapi (fun index definition ->
    let id = identity (field "declaration" definition) in
    let parameters = List.mapi (fun i p -> {scope= -1-index;index=i;spelling=text "name" p})
      (items "parameters" definition) in
    let body = source_type {bindings=[];owner=Some id;positional=parameters;arity;symbolic=[];
      own=true;self_owner=true;value_packs=false} in
    {id;native_promise=(text "name" (field "declaration" definition)="Promise" &&
       String.starts_with ~prefix:"typescript/lib/" (text "module" (field "declaration" definition)));parameters;
     bases=List.map body (items "bases" definition);
     (* A definition stated for its bounds only has no equation. *)
     expression=(match field "expression" definition with Null -> None | e -> Some (body e))})
    (items "definitions" document) in
  let locals = List.map (fun root ->
    let id=identity (field "declaration" root) in
    if not (List.exists (fun d -> d.id=id) definitions) then
      fail ("import root lacks definition " ^ id);
    text "local" (field "binding" root)) (items "roots" document) in
  if List.length (List.sort_uniq compare locals) <> List.length locals then
    fail "duplicate declaration root name";
  let symbolic = List.filter_map (fun d ->
    match d.parameters,d.bases,d.expression with
    | [parameter],[],Some (Rigid identity as body) when identity=parameter ->
      Some (d.id,(parameter,body))
    | [parameter],[],Some (Atoms [Shape shape] as body) ->
      (match shape.fields,shape.indexes,shape.calls,shape.elements with
      | [{name=Name "value";optional=false;read=Rigid identity;
          write=Some (Rigid written);host=false;receivers=[]}],[],[],None
          when identity=parameter && written=parameter ->
        Some (d.id,(parameter,body))
      | _ -> None)
    | _ -> None) definitions in
  let top={bindings=[];owner=None;positional=[];arity;symbolic;own=false;self_owner=false;value_packs=false} in
  (* A generic class's binders are in scope in its members: one binder per
     spelling for the whole top-level code, as Lean reads them. *)
  let rec class_params = function
    | Object fields as j ->
      let here = if List.assoc_opt "k" fields = Some (String "ctor") then
          (match List.assoc_opt "typeParams" fields with Some (Array ps) -> ps | _ -> [])
        else [] in
      ignore j; here @ List.concat_map (fun (_,v) -> class_params v) fields
    | Array xs -> List.concat_map class_params xs
    | _ -> [] in
  let class_params = List.fold_left (fun acc p ->
    if List.exists (fun q -> text "name" q = text "name" p) acc then acc else acc @ [p])
    [] (class_params (field "init" ast)) in
  let init_binders,init_quantified = quantify top (-2000) class_params in
  { file=field "file" ast;digest=field "sourceSha256" ast;
    declarations=definitions;
    (* A class's binder typing a rest inside the class is a packed one: its
       rest is the argument lists of its instance's array. *)
    init=List.map (stmt {init_binders with value_packs=true}) (items "init" ast);
    init_quantified;
    values=List.mapi (fun index v ->
      (* A generic value's binders quantify each of its signatures. *)
      let binders,quantified = quantify top (-1000-index) (items "typeParams" v) in
      (* A binder only a rest's argument list uses is a pack parameter,
         bounded by its bound's pack; one typing a value as well stays a value
         binder whose rest is the argument lists of its instance's array. *)
      let pure_packs = List.filter_map (fun (q:quantifier) ->
        let value,pack = binder_use q.identity.spelling (field "type" v) in
        if pack && not value then Some q.identity else None) quantified in
      let bound_of (r:rigid) = List.find_map (fun tp ->
        if text "name" tp = r.spelling then Some (field "bound" tp) else None) (items "typeParams" v) in
      let binders = {binders with value_packs=true;
        bindings=List.map (fun (name,arg) -> match arg with
          | ValueArgument (Rigid r) when List.mem r pure_packs -> name,PackArgument (PackParameter r)
          | _ -> name,arg) binders.bindings} in
      let quantified = List.map (fun (q:quantifier) ->
        if List.mem q.identity pure_packs then
          {q with bound=(match bound_of q.identity with
            | Some Null | None -> unsupported "an argument pack needs its bound"
            | Some t -> Some (PackArgument (pack_bound binders t)))}
        else q) quantified in
      text "local" (field "binding" v),
      (match source_type binders (field "type" v),quantified with
       | t,[] -> t
       | Atoms [Shape ({calls=_ :: _ as calls;_} as shape)],_ ->
         Atoms [Shape {shape with calls=List.map (fun (call:signature) -> {call with quantified}) calls}]
       (* A generic class: every construct signature under its binders. *)
       | Atoms [Ctors ((_ :: _ as signatures),statics)],_ ->
         Atoms [Ctors (List.map (fun (signature:signature) -> {signature with quantified}) signatures,statics)]
       | _ -> unsupported "a generic imported value must be one callable"))
      (items "values" document);
    functions=List.mapi (fun scope f ->
      let parameters = items "typeParams" f in
      let initial={bindings=[];owner=None;positional=[];arity;symbolic;own=false;self_owner=false;value_packs=false} in
      let binders,quantified = quantify initial scope parameters in
      (* A rest typed by one of the function's own type parameters: the body
         sees the array at that parameter's bound; callers instantiate the
         parameter as an argument pack within it. *)
      let pack_rest = match List.rev (items "params" f) with
        | p :: _ when List.mem_assoc "rest" (obj p) && text "k" (field "type" p) = "pack" ->
          let name = text "name" (field "of" (field "type" p)) in
          (match List.find_opt (fun tp -> text "name" tp = name) parameters,
                 List.find_opt (fun (q:quantifier) -> q.identity.spelling = name) quantified with
           | Some tp,Some q when field "bound" tp <> Null -> Some (q.identity,field "bound" tp)
           | _ -> unsupported "a rest typed by a type parameter needs its bound")
        | _ -> None in
      let quantified = match pack_rest with
        | None -> quantified
        | Some (identity,bound) -> List.map (fun (q:quantifier) ->
            if q.identity = identity then {q with bound=Some (PackArgument (pack_bound binders bound))} else q)
            quantified in
      let param_type p = match pack_rest with
        | Some (_,bound) when List.mem_assoc "rest" (obj p) -> source_type binders bound
        | _ -> source_type binders (field "type" p) in
      {quantified;name=text "name" f; name_pos=field "namePos" f;
      params=List.map (fun p -> text "name" p,param_type p) (items "params" f);
      rest=List.exists (fun p -> List.mem_assoc "rest" (obj p)) (items "params" f);
      rest_pack=Option.map fst pack_rest;
      result=source_type binders (field "retType" f);guard=guard_of binders (field "guard" f);
      body=List.map (stmt binders) (items "body" f)}) (items "functions" ast) }
