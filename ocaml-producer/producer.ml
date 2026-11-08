(* This executable emits proposals, never an acceptance decision. With
   `--explain`, it prints instead the known causes of failure it met, each at
   its source span (`Proposal_diagnostics.explain`), for naming a failed search. *)
(* The names a statement list mentions: every name its expressions read or
   assign, nested closures included, and every class an `instanceof` reads. *)
open Source
open Proposal_types

let mentioned stmts =
  let rec expr (e:Source.expr) = (match e.node with
    | Id n | Assign (n,_,_) | NullishAssign (n,_,_) | InstanceTest (n,_,_) -> [n]
    | _ -> []) @ List.concat_map expr (Source.children e) in
  List.sort_uniq compare (List.concat_map expr (List.concat_map Source.statement_children stmts))

(* The names the initialization declares. *)
let init_names (program:Source.program) = List.concat_map (fun (s:Source.stmt) -> match s.statement with
  | Declare (_,bindings) -> List.map (fun (n,_,_) -> n) bindings
  | Destructure (target,_,_) -> Source.pattern_names target
  | _ -> []) program.init

(* Potentially owned empty-object module bindings whose objects can escape,
   as SourceExtraction.moduleEscapes treats them. Slices carry these names through omittedMentions, so deleting
   another function cannot make a shared object appear exclusively owned. *)
let module_escapes name stmts =
  let rec mentions e = (match e.node with
    | Id n | Assign (n,_,_) | NullishAssign (n,_,_) -> n = name
    | _ -> false) || List.exists mentions (Source.children e) in
  let quiet e = match e.node with Id _ | Literal _ -> true | _ -> false in
  let rec escapes e = match e.node with
    | Id n -> n = name
    | Read ({node=Id _;_},_) -> false
    | Index ({node=Id n;_},k) -> (n = name && not (quiet k)) || escapes k
    | Write ({node=Id _;_},_,rhs) -> escapes rhs
    | IndexWrite ({node=Id n;_},k,rhs) ->
      (n = name && not (quiet k)) || escapes k || escapes rhs
    | Optional _ | WithObject _ | WithFields _ | ArrayAssign _
    | Update _ | LogicalAssign _ | ObjectAssign _ -> mentions e
    | Assign (n,_,rhs) | NullishAssign (n,_,rhs) -> n = name || escapes rhs
    | _ -> List.exists escapes (Source.children e) in
  List.exists escapes (List.concat_map Source.statement_children stmts)

(* `--units`: what a unit's proposal reads beyond its own code. For each
   function name, the module functions and whether a name of the
   initialization its code mentions, and every name it mentions; the
   initialization's mentions and names; and the constants of the
   initialization the file reads as values. *)
let units_facts (program:Source.program) =
  let names = List.sort_uniq compare (List.map (fun (g:Source.fn) -> g.name) program.functions) in
  let declared = init_names program in
  let of_body stmts = List.filter (fun n -> List.mem n names) (mentioned stmts),
    List.exists (fun n -> List.mem n declared) (mentioned stmts) in
  let strings ns = Json.Array (List.map (fun n -> Json.String n) ns) in
  let first_seen = List.fold_left (fun acc (g:Source.fn) -> if List.mem g.name acc then acc else acc @ [g.name]) []
    program.functions in
  let constants = List.concat_map (fun (s:Source.stmt) -> match s.statement with
    | Declare (false,bindings) -> List.map (fun (n,_,_) -> n) bindings
    | _ -> []) program.init in
  let read = Proposal.read_as_values program in
  Json.Object ["functions",Json.Array (List.map (fun name ->
      let bodies = List.concat_map (fun (g:Source.fn) -> if g.name = name then g.body else []) program.functions in
      let fs,init = of_body bodies in
      Json.Object ["name",Json.String name;"mentions",strings fs;"init",Json.Bool init;
        "names",strings (mentioned bodies)]) first_seen);
    "init",(match program.init with
      | [] -> Json.Null
      | stmts -> Json.Object ["mentions",strings (fst (of_body stmts));"names",strings (mentioned stmts)]);
    "escaped",strings (List.filter (fun n -> module_escapes n
      (program.init @ List.concat_map (fun (g:Source.fn) -> g.body) program.functions)) (List.concat_map (fun (s:Source.stmt) -> match s.statement with
      | Declare (true, bindings) -> List.filter_map (fun (n,_,e) -> match e.node with
        | Alloc [] -> Some n | _ -> None) bindings
      | _ -> []) program.init));
    "readAsValues",Json.Array (List.filter_map (fun n ->
      if List.mem n read then Some (Json.String n) else None) constants)]

let strings j = List.map Json.str (Json.list j)

(* The imports read qualified: each by its name, its declaration identity,
   its unit's certified footprint and on-throw flag, and the footprint the
   unit certifies for the function it returns. *)
let qualified_of j = List.map (fun q -> Json.str (Json.field "local" q),Json.field "declaration" q,
  Source.footprint_of (Json.field "footprint" q),Json.boolean (Json.field "onThrow" q),
  Source.footprint_of (Json.field "resultFootprint" q)) (Json.list j)

(* A unit's reads document: its members, whether the initialization is one,
   the settled footprint, flag and result footprint of each other function
   its slice holds,
   the constants read as values, and its qualified reads. *)
let unit_reads reads_file =
  let reads = Json.read reads_file in
  let spec : Proposal.unit_spec = {
    Proposal.members=strings (Json.field "members" reads);
    init_member=Json.boolean (Json.field "init" reads);
    pinned=List.map (fun p -> Json.str (Json.field "name" p),
      (match Json.field "footprint" p with Json.Null -> None | f -> Some (Source.footprint_of f)),
      Json.boolean (Json.field "thrown" p),
      (match Json.field "resultFootprint" p with Json.Null -> None | f -> Some (Source.footprint_of f)))
      (Json.list (Json.field "pinned" reads));
    read_as_values=strings (Json.field "readAsValues" reads)} in
  spec,qualified_of (Json.field "qualified" reads)

(* A position of a unit's slice at the document's: the slice leaves out the
   document's intervals `deletions` (sorted, disjoint), each at one point. *)
let to_document deletions y =
  let rec go removed = function
    | [] -> y + removed
    | (s,e) :: rest -> if y <= s - removed then y + removed else go (removed + (e - s)) rest in
  go 0 deletions

(* Symbols in a proposal are indices of its slice's symbol table. Assembly
   restores their document indices throughout complete semantic contracts. *)
let symbol_mapper symbols =
  let open Semantic in
  let symbol i = match List.nth_opt symbols i with
    | Some n -> n | None -> Json.fail "a proposal names an absent slice symbol" in
  let key = function Name n -> Name n | Key i -> Key (symbol i) in
  let rec ty = function
    | Rigid r -> Rigid r
    | Atoms xs -> Atoms (List.map atom xs)
    | Union xs -> Union (List.map ty xs)
    | Meet (x,xs) -> Meet (ty x,List.map ty xs)
  and atom = function
    | SymbolLit i -> SymbolLit (symbol i)
    | Shape s -> Shape {fields=List.map field s.fields;
        indexes=List.map (fun (i:index_signature) -> {i with value=ty i.value;writable=Option.map ty i.writable}) s.indexes;
        calls=List.map signature s.calls;elements=Option.map sequence s.elements}
    | Exact fs -> Exact (List.map field fs)
    | Ctors (ss,fs) -> Ctors (List.map signature ss,List.map field fs)
    | Named (id,args) -> Named (id,List.map ty args)
    | (Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Top
      | Bigint | Symbol | BigintLit _ | Callable) as a -> a
  and field (f:field) = {f with name=key f.name;read=ty f.read;write=Option.map ty f.write;
    receivers=List.map ty f.receivers}
  and sequence s = {s with required=List.map ty s.required;optional_elements=List.map ty s.optional_elements;
    rest=Option.map ty s.rest}
  and pack = function PackParameter r -> PackParameter r | Pack s -> Pack (sequence s)
  and argument = function
    | ValueArgument t -> ValueArgument (ty t)
    | PackArgument p -> PackArgument (pack p)
    | ResolutionArgument (t,(r,o),result,c) ->
      ResolutionArgument (ty t,(r,ty o),Option.map (fun (r,t) -> r,ty t) result,c)
  and signature s = {s with receiver=ty s.receiver;params=List.map ty s.params;
    variadic=Option.map ty s.variadic;rest_pack=Option.map pack s.rest_pack;result=ty s.result;
    quantified=List.map (fun q -> {q with bound=Option.map argument q.bound;default=Option.map ty q.default}) s.quantified} in
  ty,argument

let remap_claim m symbols (c:Proposal_types.function_claim) : Proposal_types.function_claim =
  let ty,argument = symbol_mapper symbols in
  let binding = function
    | Environment.Value t -> Environment.Value (ty t)
    | Environment.Storage (a,b) -> Environment.Storage (ty a,ty b)
    | Environment.Local (a,b) -> Environment.Local (ty a,ty b) in
  let num = function
    | Json.Number n as j -> (match int_of_string_opt n with Some i -> Json.Number (string_of_int (m i)) | None -> j)
    | j -> j in
  let pos = function Json.Array [a;b] -> Json.Array [num a;num b] | j -> j in
  let point p = match String.split_on_char ':' p with
    | a :: b :: rest -> (match int_of_string_opt a,int_of_string_opt b with
      | Some a,Some b -> String.concat ":" (string_of_int (m a) :: string_of_int (m b) :: rest)
      | _ -> p)
    | _ -> p in
  (* A name the lowering made at a position, `…@N…`. *)
  let name n = if not (String.contains n '%') then n else
    let b = Buffer.create (String.length n) in
    (* Within a generated name, from its `%` to the first character no
       name holds. *)
    let generated = ref false in
    let plain c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' || c = '$' in
    let len = String.length n in
    let digits i = let j = ref i in while !j < len && n.[!j] >= '0' && n.[!j] <= '9' do incr j done; !j in
    let number i j = string_of_int (m (int_of_string (String.sub n i (j - i)))) in
    let rec go i =
      if i >= len then () else
      if n.[i] = '%' then (generated := true; Buffer.add_char b '%'; go (i + 1)) else
      if n.[i] = '@' && !generated then begin
        let j = digits (i + 1) in
        Buffer.add_char b '@';
        if j = i + 1 then go j else begin
          Buffer.add_string b (number (i + 1) j);
          let k = if j < len && n.[j] = ':' then digits (j + 1) else j in
          if k > j + 1 then (Buffer.add_char b ':'; Buffer.add_string b (number (j + 1) k); go k) else go j
        end
      end else begin
        if not (plain n.[i] || n.[i] = '@' || n.[i] = ':' || n.[i] = '-') then generated := false;
        Buffer.add_char b n.[i]; go (i + 1)
      end in
    go 0; Buffer.contents b in
  let expression (e:Proposal_types.expression) = {pos=pos e.pos;point=point e.point;type_=ty e.type_;
    instantiation=Option.map (List.map (fun (n,a) -> n,argument a)) e.instantiation} in
  let entry (e:Proposal_types.entry) = {Proposal_types.start=num e.start;point=point e.point;
    bindings=List.map (fun (n,b) -> name n,binding b) e.bindings} in
  let contract (k:Proposal_types.contract) = {pos=pos k.pos;name=name k.name;type_=ty k.type_} in
  let overlay (o:Proposal_types.overlay) = {Proposal_types.row_contracts=List.map contract o.row_contracts;
    row_entries=List.map entry o.row_entries;row_expressions=List.map expression o.row_expressions} in
  {c with contracts=List.map contract c.contracts;entries=List.map entry c.entries;
    expressions=List.map expression c.expressions;
    arrows=List.map (fun (p,os) -> pos p,List.map overlay os) c.arrows;
    source={c.source with name_pos=pos c.source.name_pos;
      params=List.map (fun (n,t) -> n,ty t) c.source.params;result=ty c.source.result}}

let main () =
  match Array.to_list Sys.argv with
  | [_;"--units";file] ->
    print_endline (Json.encode (units_facts (file |> Json.read |> Source.decode)))
  | [_;"--unit";file;flow_file;reads_file;out;claims_out] ->
    let spec,qualified = unit_reads reads_file in
    let program = {(file |> Json.read |> Source.decode) with Source.qualified} in
    let flows = List.map Flow.decode (Json.list (Json.read flow_file)) in
    let interfaces = ref [] in
    let proposal = Proposal.infer ~unit:spec ~on_settled:(fun assumed thrown results ->
      interfaces := List.map (fun name -> Json.Object ["name",Json.String name;
        "footprint",(match List.assoc_opt name assumed with Some f -> Claims.footprint_json f | None -> Json.Null);
        "thrown",Json.Bool (List.mem name thrown);
        "resultFootprint",(match List.assoc_opt name results with Some f -> Claims.footprint_json f | None -> Json.Null)])
        spec.Proposal.members) flows program in
    let ch = open_out_bin out in
    Marshal.to_channel ch ((if spec.Proposal.init_member then proposal.init else None),proposal.functions) [];
    close_out ch;
    (* The slice's claims, what the unit's search reads: the members' claims,
       and each other function the slice holds, by its signature alone, at
       its settled footprint and flag. Where the producer refuses those, the
       claims are that refusal, and the unit's search refuses with it. *)
    let others = List.filter (fun n -> not (List.mem n spec.Proposal.members))
      (List.sort_uniq compare (List.map (fun (g:Source.fn) -> g.name) program.Source.functions)) in
    let slice_claims = try
        let stubs = if others = [] then [] else
          (Proposal.infer ~unit:{spec with Proposal.members=others;init_member=false} flows program).functions in
        let claims = proposal.functions @ stubs in
        let functions = List.map (fun (g:Source.fn) ->
          match List.find_opt (fun (c:Proposal_types.function_claim) ->
            c.source.name = g.name && c.source.name_pos = g.name_pos) claims with
          | Some c -> c
          | None -> Json.fail ("no claim of " ^ g.name)) program.Source.functions in
        Claims.encode {program;functions;init=proposal.init}
      with Json.Error e -> Json.Object ["refusal",Json.String (Json.message e)] in
    let ch = open_out_bin claims_out in
    output_string ch (Json.encode slice_claims);
    close_out ch;
    print_endline (Json.encode (Json.Array !interfaces))
  | _ :: "--assemble" :: file :: qualified_file :: assembly_file :: proposals ->
    let program = {(file |> Json.read |> Source.decode) with
      Source.qualified=qualified_of (Json.read qualified_file)} in
    let assembly = Json.list (Json.read assembly_file) in
    if List.length assembly <> List.length proposals then Json.fail "an assembly lists another number of proposals";
    let read path deletions symbols =
      let ch = open_in_bin path in
      let (init,functions) : Proposal_types.function_claim option * Proposal_types.function_claim list =
        Marshal.from_channel ch in
      close_in ch;
      let deletions = List.map (fun d -> match Json.list d with
        | [Json.Number s;Json.Number e] -> int_of_string s,int_of_string e
        | _ -> Json.fail "a deletion is two positions") (Json.list deletions) in
      let symbols = List.map (function Json.Number n -> int_of_string n
        | _ -> Json.fail "an assembly symbol is an index") (Json.list symbols) in
      let m = to_document deletions in
      Option.map (remap_claim m symbols) init,List.map (remap_claim m symbols) functions in
    let units = List.map2 (fun path a -> read path (Json.field "deletions" a) (Json.field "symbols" a)) proposals assembly in
    let claims = List.concat_map snd units in
    let functions = List.map (fun (g:Source.fn) ->
      match List.find_opt (fun (c:Proposal_types.function_claim) ->
        c.source.name = g.name && c.source.name_pos = g.name_pos) claims with
      | Some c -> c
      | None -> Json.fail ("no unit proposes " ^ g.name)) program.functions in
    let init = match program.init,List.filter_map fst units with
      | [],[] -> None
      | _ :: _,[c] -> Some c
      | _ -> Json.fail "the initialization is proposed by no unit or by several" in
    print_endline (Json.encode (Claims.encode {program;functions;init}))
  | [_;"--explain";file;flow_file;reads_file] ->
    let spec,qualified = unit_reads reads_file in
    let state = Proposal_diagnostics.create ~explaining:true () in
    let program = {(file |> Json.read |> Source.decode) with Source.qualified} in
    let flows = List.map Flow.decode (Json.list (Json.read flow_file)) in
    (try ignore (Proposal.infer ~unit:spec ~state flows program) with Json.Error _ -> ());
    print_endline (Json.encode (Json.Array (List.rev_map (fun (pos,reason) ->
      Json.Object ["pos",pos;"reason",Json.String reason]) !(state.Proposal_diagnostics.explanations))))
  | _ -> Json.fail ("usage: producer --units fragment.json | --unit slice.json flow.json reads.json proposal.bin claims.json"
      ^ " | --assemble fragment.json qualified.json assembly.json proposal.bin... | --explain slice.json flow.json reads.json")

(* Every `Json.Error` exits 2 with its message, then `end of refusal`: a refusal
   (`unsupported: …`), malformed input or a usage error, told apart by the
   prefix. Any other exception exits 3, with a first line `error: `. *)
let () =
  try main () with
  | Json.Error e -> prerr_endline (Json.message e); prerr_endline "end of refusal"; exit 2
  | e -> prerr_endline ("error: " ^ Printexc.to_string e); exit 3
