(* Lean owns the order and conditional execution of expression operations. *)
type saved = { id: int; name: string; source: Json.t; role: string }
type impact = None_ | Havoc | CellWrite of string * Json.t | CellUpdate of string * Json.t
type operation = { source: Json.t; impact: impact }
type test = Truthy | Nullish | Defined
type plan =
  | Observe of Json.t * plan
  | Atom of Json.t * operation
  | Sequence of Json.t * saved * plan * plan
  | Choose of Json.t * Json.t * test * saved * plan * plan * plan

let saved j =
  let id=match Json.field "id" j with
    | Json.Number n -> (try int_of_string n with Failure _ -> Json.fail "invalid saved value identity")
    | _ -> Json.fail "a saved value identity is a number" in
  {id;name=Json.str (Json.field "name" j);source=Json.field "source" j;
   role=Json.str (Json.field "role" j)}
let impact j = match Json.str (Json.field "kind" j) with
  | "none" -> None_
  | "havoc" -> Havoc
  | "cellWrite" -> CellWrite (Json.str (Json.field "name" j),Json.field "value" j)
  | "cellUpdate" -> CellUpdate (Json.str (Json.field "name" j),Json.field "source" j)
  | kind -> Json.fail ("unknown expression effect " ^ kind)
let reference j = match Json.str (Json.field "kind" j) with
  | "local" -> ignore (Json.field "source" j); Some (Json.str (Json.field "name" j))
  | "field" ->
    ignore (Json.field "source" j); ignore (saved (Json.field "receiver" j));
    (match Json.field "key" j with Json.Null -> () | key -> ignore (saved key)); None
  | kind -> Json.fail ("unknown expression reference " ^ kind)
let operation j =
  let source=Json.field "source" j in
  let impact=match Json.str (Json.field "kind" j) with
   | "evaluate" -> impact (Json.field "effect" j)
   | "methodRead" ->
     ignore (saved (Json.field "receiver" j));
     (match Json.field "key" j with Json.Null -> () | key -> ignore (saved key));
     ignore (Json.field "call" j); None_
   | "invokeSaved" -> ignore (saved (Json.field "receiver" j)); ignore (saved (Json.field "method" j)); Havoc
   | "snapshotSpread" -> ignore (saved (Json.field "value" j)); ignore (Json.field "call" j); None_
   | "snapshotObject" -> ignore (saved (Json.field "value" j)); None_
   | "referenceRead" -> ignore (reference (Json.field "reference" j)); None_
   | "referenceWrite" ->
     let reference=reference (Json.field "reference" j) and value=saved (Json.field "value" j) in
     (match reference with Some name -> CellWrite (name,value.source) | None -> Havoc)
   | "updateSaved" ->
     let reference=reference (Json.field "reference" j) in
     ignore (saved (Json.field "previous" j));
     (match Json.field "rhs" j with Json.Null -> () | rhs -> ignore (saved rhs));
     (match reference with Some name -> CellUpdate (name,source) | None -> Havoc)
   | "positionRead" -> ignore (saved (Json.field "array" j)); ignore (Json.field "index" j); None_
   | "arrayRest" -> ignore (saved (Json.field "array" j)); ignore (Json.field "start" j);
     ignore (Json.boolean (Json.field "slice" j)); None_
   | "emptyObject" -> None_
   | "addField" -> ignore (saved (Json.field "base" j)); ignore (Json.field "key" j);
     ignore (saved (Json.field "value" j)); ignore (Json.boolean (Json.field "final" j)); None_
   | "mergeObjects" -> ignore (saved (Json.field "left" j)); ignore (saved (Json.field "right" j)); ignore (Json.boolean (Json.field "final" j)); ignore (Json.boolean (Json.field "assign" j)); None_
   | kind -> Json.fail ("unknown expression operation " ^ kind) in
  {source;impact}
let rec decode j =
  let source=Json.field "source" j in
  match Json.str (Json.field "kind" j) with
  | "observe" -> Observe (source,decode (Json.field "evaluate" j))
  | "atom" -> Atom (source,operation (Json.field "operation" j))
  | "sequence" -> Sequence (source,saved (Json.field "binding" j),
      decode (Json.field "evaluate" j),decode (Json.field "next" j))
  | "choose" ->
    let test=match Json.str (Json.field "test" j) with
      | "truthy" -> Truthy | "nullish" -> Nullish | "defined" -> Defined
      | kind -> Json.fail ("unknown expression branch " ^ kind) in
    Choose (source,Json.field "condition" j,test,saved (Json.field "binding" j),
      decode (Json.field "evaluate" j),decode (Json.field "yes" j),decode (Json.field "no" j))
  | kind -> Json.fail ("unknown expression execution plan " ^ kind)
let rec contains source = function
  | Observe (span,evaluate) -> span=source || contains source evaluate
  | Atom _ -> false
  | Sequence (_,_,evaluate,next) -> contains source evaluate || contains source next
  | Choose (_,_,_,_,evaluate,yes,no) -> contains source evaluate || contains source yes || contains source no

let source = function
  | Observe (source,_) | Atom (source,_) | Sequence (source,_,_,_)
  | Choose (source,_,_,_,_,_,_) -> source

(* Persistent lexical bindings and parameter defaults share a source-owned
   schedule with expression execution. *)
type binding_plan =
  | Finish
  | Evaluate of saved * plan * binding_plan
  | DefaultValue of saved * saved * plan * binding_plan
  | Bind of string * Json.t * saved * binding_plan
  | Input of string * int * saved * binding_plan
  | ReadField of Json.t * saved * string * saved * binding_plan
  | ReadPosition of Json.t * saved * int * saved * binding_plan
  | ObjectRest of Json.t * saved * string list * saved * binding_plan
  | ArrayRest of Json.t * saved * int * bool * saved * binding_plan
let natural j = match j with
  | Json.Number n -> (try let n=int_of_string n in if n<0 then Json.fail "negative binding index"; n
    with Failure _ -> Json.fail "invalid binding index")
  | _ -> Json.fail "binding index must be a number"
let rec decode_binding j =
  let get name=Json.field name j in
  let value ()=saved (get "value") and next ()=decode_binding (get "next") in
  match Json.str (get "kind") with
  | "finish" -> Finish
  | "evaluate" -> Evaluate (value (),decode (get "plan"),next ())
  | "defaultValue" -> DefaultValue (value (),saved (get "result"),decode (get "fallback"),next ())
  | "bind" -> Bind (Json.str (get "name"),get "origin",value (),next ())
  | "input" -> Input (Json.str (get "name"),natural (get "index"),value (),next ())
  | "readField" -> ReadField (get "source",saved (get "receiver"),Json.str (get "field"),value (),next ())
  | "readPosition" -> ReadPosition (get "source",saved (get "array"),natural (get "index"),value (),next ())
  | "objectRest" -> ObjectRest (get "source",saved (get "receiver"),List.map Json.str (Json.list (get "drop")),value (),next ())
  | "arrayRest" -> ArrayRest (get "source",saved (get "array"),natural (get "start"),Json.boolean (get "slice"),value (),next ())
  | kind -> Json.fail ("unknown binding operation " ^ kind)
let optional_binding = function Json.Null -> None | j -> Some (decode_binding j)
