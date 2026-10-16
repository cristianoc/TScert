(* Source cases cannot inspect rollback or inject an unexpected OCaml exception.
   These checks exercise the state owner's protected operation boundaries. *)
open Semantic
open Source
open Proposal_types
open Analysis_capabilities

exception Unexpected
let require message condition = if not condition then failwith message

let fresh ?(flows=[]) () =
  let diagnostics = Proposal_diagnostics.create ~explaining:true () in
  let fn : Source.fn = {
    quantified=[]; name="scope-test"; name_pos=Json.Null; params=[];
    rest=false; rest_pack=None; result=Atoms []; body=[] } in
  Analysis_state.create diagnostics flows [] [] [] [] [] [] fn

let disturb state name =
  let module Owner = Analysis_state.Access(struct let state = state end) in
  Owner.record_growth name;
  Owner.publish_entry (Json.String name) [];
  Owner.evolve (Json.String name) (Atoms []);
  Owner.explain Json.Null name

let check_exit name action expected =
  let state = fresh () in
  let module Owner = Analysis_state.Access(struct let state = state end) in
  Owner.with_current_point "enclosing" (fun () ->
    Owner.record_growth "enclosing";
    let before=Owner.snapshot () in
    let result=Owner.speculate (fun () ->
      require "attempt must be marked speculative" (Owner.speculative_typing ());
      require "attempt starts with enclosing point" (Owner.current_point () = "enclosing");
      disturb state name;
      Owner.with_current_point name action) in
    require "attempt result" (result = expected);
    require "restore enclosing candidate contents" (Owner.snapshot () = before);
    require "retain write proposals" (Owner.writes () = [Json.String name, Atoms []]);
    require "retain diagnostic observations" (Owner.explanations () = [Json.Null,name]))

let () =
  check_exit "successful" (fun () -> 7) (Some 7);
  check_exit "refused" (fun () -> Json.fail "probe refused") None;
  let state = fresh () in
  let module Owner = Analysis_state.Access(struct let state = state end) in
  let enclosing=Owner.snapshot () in
  require "nested successful attempt" (Owner.speculate (fun () ->
    disturb state "parent";
    Owner.with_current_point "parent" (fun () ->
      let parent=Owner.snapshot () in
      require "nested refusal" (Owner.speculate (fun () ->
        disturb state "child"; Json.fail "nested refusal") = None);
      require "nested scope restores parent contents" (Owner.snapshot () = parent);
      require "nested scope preserves speculative mode" (Owner.speculative_typing ());
      9)) = Some 9);
  require "nested scope restores outer contents" (Owner.snapshot () = enclosing);
  require "nested writes survive both scopes" (List.map fst (Owner.writes ()) =
    [Json.String "child"; Json.String "parent"]);
  let caught = try ignore (Owner.speculate (fun () ->
    disturb state "unexpected"; raise Unexpected)); false
    with Unexpected -> true in
  require "unexpected exceptions propagate" caught;
  require "unexpected exception restores scope" (Owner.snapshot () = enclosing);
  require "unexpected exception retains shared effects" (List.length (Owner.writes ()) = 3);
  print_endline "speculative scopes: success, refusal, nesting and exception restoration passed"

(* Each node owns its publication buffers and runs under a path snapshot.
   Failures restore the enclosing node while shared observations survive. *)
let () =
  let state=fresh () in
  let module Owner = Analysis_state.Access(struct let state = state end) in
  let within_node point action =
    let enclosing=Owner.path_facts () in
    Owner.with_path_metadata enclosing enclosing (fun () -> Owner.with_output point action) in
  Owner.with_current_point "enclosing-node" (fun () ->
    disturb state "enclosing-node";
    let enclosing=Owner.snapshot () in
    let result,output=within_node "parent-node" (fun () ->
      require "node starts with empty output" (Owner.output () = empty_output);
      disturb state "parent-node";
      let parent=Owner.snapshot () in
      let child_result,child_output=within_node "child-node" (fun () ->
        disturb state "child-node"; 11) in
      require "nested node returns value" (child_result = 11);
      require "nested node returns only its claims"
        (List.map (fun (e:entry) -> e.point) child_output.entries = ["child-node"]);
      require "nested node restores parent output and path" (Owner.snapshot () = parent);
      let refused=try ignore (within_node "refused-node" (fun () ->
        disturb state "refused-node"; Json.fail "node refusal")); false
        with Json.Error _ -> true in
      require "node refusal propagates" refused;
      require "refused nested node restores parent output and path" (Owner.snapshot () = parent);
      17) in
    require "node result survives scope" (result = 17);
    require "parent owns only its output"
      (List.map (fun (e:entry) -> e.point) output.entries = ["parent-node"]);
    require "node restores enclosing scope" (Owner.snapshot () = enclosing);
    let caught=try ignore (within_node "exception-node" (fun () ->
      disturb state "exception-node"; raise Unexpected)); false
      with Unexpected -> true in
    require "node unexpected exceptions propagate" caught;
    require "exception restores enclosing node" (Owner.snapshot () = enclosing);
    require "node write proposals survive every exit" (List.map fst (Owner.writes ()) =
      List.map (fun name -> Json.String name)
        ["exception-node"; "refused-node"; "child-node"; "parent-node"; "enclosing-node"]);
    require "node diagnostics survive every exit" (List.map snd (Owner.explanations ()) =
      ["exception-node"; "refused-node"; "child-node"; "parent-node"; "enclosing-node"]));
  print_endline "node scopes: owned output, nested paths and exception restoration passed"

(* A row owns three claim collections; its other proposal effects belong to
   the enclosing inference. Publication order must survive this boundary. *)
let () =
  let state=fresh () in
  let module Owner = Analysis_state.Access(struct let state = state end) in
  let claims () = let o=Owner.output () in o.expressions,o.entries,o.contracts in
  let add_claims name = Owner.with_current_point name (fun () ->
    Owner.publish_expression Json.Null (Atoms []) None;
    Owner.publish_entry Json.Null [];
    Owner.publish_contract {pos=Json.Null;name;type_=Atoms []}) in
  add_claims "enclosing";
  let enclosing=claims () in
  let row=Owner.collect_overload_row_claims (fun () ->
    require "row starts with empty claim collections" (claims () = ([],[],[]));
    add_claims "first";
    let parent=claims () in
    let nested=Owner.collect_overload_row_claims (fun () -> add_claims "nested") in
    require "nested row collects its own claims"
      (List.map (fun (c:contract) -> c.name) nested.row_contracts = ["nested"]);
    require "nested row restores enclosing claims" (claims () = parent);
    require "row nested speculation refuses" (Owner.speculate (fun () ->
      add_claims "speculative"; Json.fail "row speculation") = None);
    require "row uses active state after speculation" (claims () = parent);
    add_claims "last";
    Owner.record_growth "row-effect";
    Owner.evolve Json.Null (Atoms [])) in
  require "row retains claim order"
    (List.map (fun (c:contract) -> c.name) row.row_contracts = ["first";"last"] &&
     List.map (fun (e:expression) -> e.point) row.row_expressions = ["first";"last"] &&
     List.map (fun (e:entry) -> e.point) row.row_entries = ["first";"last"]);
  require "row restores enclosing claims" (claims () = enclosing);
  require "row retains other proposal effects"
    (List.mem "row-effect" (Owner.path_facts ()).Proposal_flow.grown_locals &&
     Owner.writes () = [Json.Null,Atoms []]);
  List.iter (fun (name,action) ->
    let caught=try ignore (Owner.collect_overload_row_claims (fun () ->
      add_claims name; Owner.record_growth name; action ())); false
      with Json.Error _ | Unexpected -> true in
    require "row failure propagates" caught;
    require "failed row restores enclosing claims" (claims () = enclosing);
    require "failed row retains other effects"
      (List.hd (Owner.path_facts ()).Proposal_flow.grown_locals = name))
    ["refused-row",(fun () -> Json.fail "row refusal");
     "unexpected-row",(fun () -> raise Unexpected)];
  print_endline "overload row scopes: claim ownership, nesting and exception restoration passed"

(* Contexts have lexical lifetimes; each block owns its return accumulator. *)
let () =
  let state=fresh () in
  let module Owner = Analysis_state.Access(struct let state = state end) in
  let contexts () = Owner.current_point (),Owner.rigid_bounds (),
    Owner.typing_roots (),Owner.expected_result (),Owner.block_returns () in
  let within name action =
    let rigid={scope=0;index=0;spelling=name} in
    let bounds=[rigid,Atoms []] in
    let roots=[name,Execution.Atom (Json.Null,{Execution.source=Json.Null;impact=Execution.None_}),[]] in
    Owner.with_current_point name (fun () ->
      Owner.with_rigid_bounds bounds (fun () ->
        Owner.with_typing_roots roots (fun () ->
          let result,returned=Owner.with_block_context None (fun () ->
            Owner.record_return (Rigid rigid);
            require "typing scopes expose requested context"
              (contexts () = (name,bounds,roots,None,[Rigid rigid]));
            action ()) in
          require "block returns its own accumulated results" (returned = [Rigid rigid]);
          result))) in
  let enclosing=contexts () in
  let result=within "parent-context" (fun () ->
    let parent=contexts () in
    require "nested context returns result" (within "child-context" (fun () -> 23) = 23);
    require "nested context restores parent" (contexts () = parent);
    require "context nested speculation refuses" (Owner.speculate (fun () ->
      within "refused-context" (fun () -> Json.fail "context refusal")) = None);
    require "refused context restores active parent" (contexts () = parent);
    let caught=try ignore (within "unexpected-context" (fun () -> raise Unexpected)); false
      with Unexpected -> true in
    require "typing context unexpected exceptions propagate" caught;
    require "exception restores parent context" (contexts () = parent);
    29) in
  require "typing scopes return result and restore enclosing context"
    (result = 29 && contexts () = enclosing);
  print_endline "typing contexts: dynamic scope, nested refusal and exception restoration passed"

(* A caller cannot mutate the owner's graph through an input or returned
   array; point-sensitive claims differ from the latest claim at a source. *)
let () =
  let open Flow in
  let node : Flow.node = {id=0;point="entry";source=Json.Null;scope=[];
    handler=None;action=Flow.End;binding_plan=None;executions=[]} in
  let graph : Flow.graph = {owner=Json.Null;body_spans=[];entry=0;nodes=[|node|];prologue=None;cells=[]} in
  let state=fresh ~flows:[graph] () in
  let module Owner = Analysis_state.Access(struct let state = state end) in
  graph.nodes.(0) <- {node with point="input mutation"};
  let first=Option.get (Owner.flow_graph Json.Null) in
  require "owner copies input graph array" (first.nodes.(0).point = "entry");
  first.nodes.(0) <- {node with point="output mutation"};
  require "graph lookup returns owned arrays"
    ((Option.get (Owner.flow_graph Json.Null)).nodes.(0).point = "entry");
  require "closure entry has no mutable graph alias" (Owner.closure_entry Json.Null = Some ("entry",None));
  Owner.with_current_point "first" (fun () -> Owner.publish_expression Json.Null (Atoms [Num]) None);
  Owner.with_current_point "second" (fun () ->
    require "point lookup excludes another point's claims" (Owner.claimed_type Json.Null = None);
    require "latest lookup retains cross-point source lookup" (Owner.latest_claim Json.Null = Some (Atoms [Num]));
    Owner.publish_expression Json.Null (Atoms [Str]) None);
  Owner.with_current_point "first" (fun () ->
    require "point lookup selects its own claim" (Owner.claimed_type Json.Null = Some (Atoms [Num]));
    require "latest lookup selects latest source claim" (Owner.latest_claim Json.Null = Some (Atoms [Str])));
  print_endline "sealed ownership: graph isolation and distinct claim lookups passed"
