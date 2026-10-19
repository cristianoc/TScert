(* This executable emits proposals, never an acceptance decision. With
   `--explain`, it prints instead the known causes of failure it met, each at
   its source span (`Proposal_diagnostics.explain`), for naming a failed search. *)
let main () =
  match Array.to_list Sys.argv with
  | [_;"--explain";file;flow_file] ->
    let state = Proposal_diagnostics.create ~explaining:true () in
    (try ignore (file |> Json.read |> Source.decode |> Proposal.infer ~state (List.map Flow.decode (Json.list (Json.read flow_file)))) with Json.Error _ -> ());
    print_endline (Json.encode (Json.Array (List.rev_map (fun (pos,reason) ->
      Json.Object ["pos",pos;"reason",Json.String reason]) !(state.Proposal_diagnostics.explanations))))
  | _ ->
    let file,flow_file,qualified_file = match Array.to_list Sys.argv with
      | [_;file;flow_file] -> file,flow_file,None
      | [_;file;flow_file;qualified] -> file,flow_file,Some qualified
      | _ -> Json.fail "usage: producer [--explain] fragment.json flow.json [qualified.json]" in
    (* The imports the pipeline reads qualified: each by its name, its
       declaration identity, and its unit's certified footprint and on-throw
       flag. *)
    let qualified = match qualified_file with
      | None -> []
      | Some f -> List.map (fun q -> Json.str (Json.field "local" q),Json.field "declaration" q,
          Source.footprint_of (Json.field "footprint" q),Json.boolean (Json.field "onThrow" q)) (Json.list (Json.read f)) in
    let program = {(file |> Json.read |> Source.decode) with Source.qualified} in
    let result = program |> Proposal.infer (List.map Flow.decode (Json.list (Json.read flow_file))) |> Claims.encode in
    print_endline (Json.encode result)

(* A refusal exits 2 with its record: the reason, then the line that ends it,
   so a reader can tell a complete record from one cut short. Any other
   exception is an operational failure: exit 3, a first line `error: `. *)
let () =
  try main () with
  | Json.Error e -> prerr_endline e; prerr_endline "end of refusal"; exit 2
  | e -> prerr_endline ("error: " ^ Printexc.to_string e); exit 3
