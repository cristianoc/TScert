(* This executable emits proposals, never an acceptance decision. With
   `--explain`, it prints instead the known causes of failure it met, each at
   its source span (`Proposal_diagnostics.explain`), for naming a failed search. *)
let () =
  match Array.to_list Sys.argv with
  | [_;"--explain";file;flow_file] ->
    let state = Proposal_diagnostics.create ~explaining:true () in
    (try ignore (file |> Json.read |> Source.decode |> Proposal.infer ~state (List.map Flow.decode (Json.list (Json.read flow_file)))) with Json.Error _ -> ());
    print_endline (Json.encode (Json.Array (List.rev_map (fun (pos,reason) ->
      Json.Object ["pos",pos;"reason",Json.String reason]) !(state.Proposal_diagnostics.explanations))))
  | _ -> try
    let file,flow_file = match Array.to_list Sys.argv with
      | [_;file;flow_file] -> file,flow_file
      | _ -> Json.fail "usage: producer [--explain] fragment.json flow.json" in
    let result = file |> Json.read |> Source.decode |> Proposal.infer (List.map Flow.decode (Json.list (Json.read flow_file))) |> Claims.encode in
    print_endline (Json.encode result)
  with Json.Error e -> prerr_endline e; exit 2
