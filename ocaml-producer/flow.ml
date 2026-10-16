(* Control flow supplied by Lean. Source references identify the syntax an
   operation elaborates; node identities distinguish executions of that syntax. *)
type binding = { name: string; source: Json.t }
type handler = { target: int; scope: binding list; binding: binding }
type action =
  | End
  | Jump of int
  | Statement of Json.t * int
  | Declaration of Json.t * string * Json.t * bool * int
  | Branch of Json.t * int * int
  | Return of Json.t
  | ReturnSave of Json.t * binding * int
  | ReturnHeld of binding
  | Rethrow of binding
  | DiscardThrow of binding * int
  | IteratorStart of Json.t * binding * int
  | IteratorStep of Json.t * binding * binding * int * int
type node = { id: int; point: string; source: Json.t; scope: binding list;
              handler: handler option; action: action; binding_plan: Execution.binding_plan option; executions: (Json.t * Execution.plan) list }
(* [cells]: the body's mutable bindings held in cells, a `let` named with its
   declaring statement, an assigned parameter with the owner; every other
   mutable binding is a slot of the body's activation. *)
type graph = { owner: Json.t; body_spans: Json.t list; entry: int; nodes: node array;
               prologue: Execution.binding_plan option; cells: binding list }

let number = function
  | Json.Number n -> (try int_of_string n with Failure _ -> Json.fail "invalid flow node identity")
  | _ -> Json.fail "a flow node identity is a number"
let binding j = {name=Json.str (Json.field "name" j);source=Json.field "source" j}
let bindings j = List.map binding (Json.list j)
let decode_action j =
  let get name = Json.field name j in
  let point name = number (get name) and bind name = binding (get name) in
  match Json.str (get "kind") with
  | "end" -> End
  | "jump" -> Jump (point "target")
  | "stmt" -> Statement (get "statement",point "next")
  | "declaration" -> Declaration (get "statement",Json.str (get "name"),get "initializer",Json.boolean (get "mutable"),point "next")
  | "branch" -> Branch (get "statement",point "yes",point "no")
  | "return" -> Return (get "statement")
  | "returnSave" -> ReturnSave (get "statement",bind "binding",point "next")
  | "returnHeld" -> ReturnHeld (bind "binding")
  | "rethrow" -> Rethrow (bind "binding")
  | "discardThrow" -> DiscardThrow (bind "binding",point "next")
  | "iteratorStart" -> IteratorStart (get "statement",bind "binding",point "next")
  | "iteratorStep" -> IteratorStep (get "statement",bind "binding",bind "element",point "yes",point "no")
  | kind -> Json.fail ("unknown flow action " ^ kind)
let decode_node j =
  let handler = match Json.field "handler" j with
    | Json.Null -> None
    | h -> Some {target=number (Json.field "target" h);
                 scope=bindings (Json.field "scope" h);binding=binding (Json.field "binding" h)} in
  {id=number (Json.field "id" j);point=Json.str (Json.field "point" j);source=Json.field "source" j;
   scope=bindings (Json.field "scope" j);handler;action=decode_action (Json.field "action" j);
   binding_plan=Execution.optional_binding (Json.field "bindingPlan" j);
   executions=List.map (fun execution -> Json.field "source" execution,
     Execution.decode (Json.field "plan" execution)) (Json.list (Json.field "executions" j))}
let successors node =
  let normal = match node.action with
    | End | Return _ | ReturnHeld _ -> []
    | Jump next | Statement (_,next) | Declaration (_,_,_,_,next) | ReturnSave (_,_,next)
    | DiscardThrow (_,next) | IteratorStart (_,_,next) -> [next]
    | Branch (_,yes,no) | IteratorStep (_,_,_,yes,no) -> [yes;no]
    | Rethrow _ -> [] in
  normal @ (match node.handler with None -> [] | Some h -> [h.target])
let decode j =
  let nodes=Array.of_list (List.map decode_node (Json.list (Json.field "nodes" j))) in
  Array.sort (fun a b -> compare a.id b.id) nodes;
  Array.iteri (fun id node -> if id <> node.id then
    Json.fail "flow nodes must have distinct contiguous identities") nodes;
  let valid id = id >= 0 && id < Array.length nodes in
  Array.iter (fun node -> List.iter (fun id -> if not (valid id) then
    Json.fail "flow edge names a missing node") (successors node)) nodes;
  let entry=number (Json.field "entry" j) in
  if not (valid entry) then Json.fail "flow entry names a missing node";
  {owner=Json.field "owner" j;body_spans=Json.list (Json.field "bodySpans" j);entry;nodes;prologue=Execution.optional_binding (Json.field "prologue" j);
   cells=bindings (Json.field "cells" j)}

(* Transfer proposes states on the graph's edges. Repeated visits compute a
   fixed point; callers publish claims only after the result settles. *)
let solve ~join ~transfer ~widen graph initial =
  let states=Array.make (Array.length graph.nodes) None in
  let queued=Array.make (Array.length graph.nodes) false in
  let visits=Array.make (Array.length graph.nodes) 0 in
  let work=Queue.create () in
  let enqueue id = if not queued.(id) then begin
    queued.(id) <- true; Queue.add id work
  end in
  states.(graph.entry) <- Some initial; enqueue graph.entry;
  while not (Queue.is_empty work) do
    let id=Queue.take work in
    queued.(id) <- false;
    match states.(id) with
    | None -> ()
    | Some state ->
      visits.(id) <- visits.(id) + 1;
      if visits.(id) > 64 then
        Json.fail ("unsupported: control-flow inference does not settle at " ^ graph.nodes.(id).point);
      let edges=transfer graph.nodes.(id) state in
      List.iter (fun (target,incoming) ->
        if not (List.mem target (successors graph.nodes.(id))) then
          Json.fail "flow transfer proposed an edge absent from the graph";
        let next=match states.(target) with
          | None -> incoming
          | Some previous ->
            let merged=join graph.nodes.(target) previous incoming in
            if visits.(target) >= 5 then widen graph.nodes.(target) previous merged else merged in
        if states.(target) <> Some next then begin
          states.(target) <- Some next; enqueue target
        end) edges
  done;
  states
