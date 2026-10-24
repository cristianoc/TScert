(* type_queries.ml expands declarations and queries candidate types used by function and module inference. *)
(* proposal_diagnostics.ml owns observations for one producer run so its CLI can explain unsuccessful proposals. *)
(* module_contract.ml constructs the source signatures offered when one module function refers to another. *)
(* analysis_pass.ml runs one inference pass and returns candidate claims and observed writes to function iteration. *)
open Semantic
open Source
open Proposal_types
open Module_contract

(* A named closure's claim is fixed where it is created, before the calls that
   offer it more parameters are reached: a first pass finds those offers, and
   the second states them at the creation. *)
let infer_function ?(offers=[]) state flows declarations arities module_functions (f:Source.fn) =
  (* A value bound retains its parameters: `T extends Ref<U>` reads a
     member through Ref<U>; `U extends T` reads through T's bound. *)
  let bounds = List.filter_map (fun (q:Semantic.quantifier) -> match q.bound with
    | Some (ValueArgument b) when b <> Rigid q.identity -> Some (q.identity,b)
    | _ -> None) f.quantified in
  (* An evolving binding's contract is what the body writes into it, which
     a pass finds under the contract the previous pass assumed: passes run
     until the contracts settle. A write whose value grows with the binding
     itself (a list consed onto it) never settles. *)
  let rec settled offered rounds assumed =
    let result,seen,uses = Analysis_pass.infer state flows offered declarations module_functions arities bounds assumed f in
    let evolved key = Option.value (List.assoc_opt key assumed) ~default:(Atoms []) in
    let grown = List.filter (fun (key,t) -> union (evolved key) t <> evolved key) seen in
    match result,grown with
    | Ok result,[] -> result,assumed
    | Error m,[] -> raise (Json.Error m)
    | _,_ when rounds = 0 ->
      (* A contract that does not settle is proposed from the binding's uses:
         the one type every read of its whole value is expected at. The
         contract is a claim: Lean checks every write against it and every
         read at it. Where no use fixes one, the refusal stays. *)
      let refused () = Proposal_diagnostics.unsupported "an evolving binding's contract does not settle: a value written into it grows with the binding itself" in
      if List.for_all (fun (key,_) -> List.mem_assoc key uses) grown then
        let assumed = List.fold_left (fun acc (key,_) ->
          (key,List.assoc key uses) :: List.remove_assoc key acc) assumed grown in
        (match Analysis_pass.infer state flows offered declarations module_functions arities bounds assumed f with
         | Ok result,_,_ -> result,assumed
         | Error _,_,_ -> refused ())
      else refused ()
    | _ ->
      let assumed = List.fold_left (fun acc (key,t) ->
        (key,union (evolved key) t) :: List.remove_assoc key acc) assumed grown in
      settled offered (rounds - 1) assumed in
  let (claim,requests),assumed = settled offers 4 [] in
  if requests = [] then claim else
  let requests = List.concat_map (fun (p,ss) -> List.map (fun s -> p,s) ss) offers @ requests in
  let offered = List.map (fun pos -> pos,List.sort_uniq compare (List.filter_map (fun (p,s) ->
    if p = pos then Some s else None) requests))
    (List.sort_uniq compare (List.map fst requests)) in
  let (claim,_),_ = settled offered 4 assumed in
  claim

(* A call of a signature the call applies: no quantified one, whose call is
   an elimination of a scheme, and no packed rest. *)
let applicable (s:signature) = s.quantified = [] && s.rest_pack = None

(* The declarations whose signatures may state the empty footprint: those
   without a rest or binders of their own. A guard's or an assertion
   function's promise signature states its footprint too. *)
let effect_candidate (g:Source.fn) = not g.rest && g.quantified = [] && not g.async

(* The footprint a declaration's body proposes for its signature, read off its
   claims as a closure's is (`Expression_closures`), else the one letting
   everything change. A proposal: Lean's check of the unit's graph
   establishes it. *)
let declaration_footprint declarations values names (claim:function_claim) =
  let g = claim.source in
  if not (effect_candidate g) then top_footprint,false else
  let callable (callee:expr) =
    match List.filter_map (fun (x:expression) -> if x.pos = callee.pos then Some x.type_ else None)
            claim.expressions with
    | [] -> None
    | types -> List.fold_left (fun acc t -> match acc,Type_queries.declared_head declarations [] t with
      | Some effects,(Atoms [Shape {calls;fields=[];indexes=[];elements=None}] | Atoms [Ctors (calls,_)])
        when calls <> [] && List.for_all applicable calls ->
        Some (effects @ List.map (fun (s:signature) -> s.call_effect) calls)
      | _ -> None) (Some []) types in
  (* A call the claim types at `never`, wherever it claims it, never returns
     normally. *)
  let no_return (e:expr) =
    match List.filter_map (fun (x:expression) -> if x.pos = e.pos then Some x.type_ else None) claim.expressions with
    | [] -> false
    | types -> List.for_all (fun t -> t = Atoms []) types in
  let readable = List.map fst g.params @ names in
  let iteration name = Option.bind (List.assoc_opt name values) iteration_footprint in
  Option.value (footprint_stmts ~callable ~no_return ~iteration ~readable g.body) ~default:top_footprint,
  throws_stmts ~callable g.body

let rec infer ?(state = Proposal_diagnostics.create ()) flows program =
  (* Footprints are proposed at the least fixpoint: every candidate is
     assumed to change nothing, and a round's claims raise each assumption to
     what its body then changes, until a round raises none. Larger callee
     footprints make no body's smaller, and the footprints are finitely
     many, so the rounds terminate. *)
  (* The module's functions, values and constants: reading one changes
     nothing. *)
  let constants = List.concat_map (fun (s:Source.stmt) -> match s.statement with
    | Declare (false,bindings) -> List.map (fun (n,_,_) -> n) bindings
    | _ -> []) program.Source.init in
  let names = List.map (fun (g:Source.fn) -> g.name) program.Source.functions @ List.map fst program.Source.values
    @ constants in
  let start = List.filter_map (fun (g:Source.fn) ->
    if effect_candidate g then Some (g.name,empty_footprint) else None) program.Source.functions in
  (* A footprint on a throw is proposed at the greatest fixpoint: every
     candidate is assumed to bound its throws, and a round withdraws the
     assumption from each whose body then does not. *)
  (* A recursive constant's closure reads its self entry at the footprint the
     round assumes of it, at first the empty one, bounding its throws
     (`Statement_analysis`); a round raises the assumption to what the
     closure's claim then proposes, and withdraws the bound on a throw where
     the claim does not state it. *)
  Hashtbl.reset Source.self_effects;
  let raise_selves (proposal : Proposal_types.t) =
    let claims = Option.to_list proposal.init @ proposal.functions in
    let claimed pos = List.concat_map (fun (c:function_claim) ->
      List.filter_map (fun (x:expression) -> if x.pos = pos then Some x.type_ else None) c.expressions) claims in
    let effect_of pos = match claimed pos with
      | [] -> top_footprint,false
      | types -> List.fold_left (fun (f,t) ty -> match ty with
        | Atoms [Shape {calls=(_ :: _ as calls);_}] ->
          List.fold_left (fun f (s:signature) -> join_footprint f s.call_effect.footprint) f calls,
          t && List.for_all (fun (s:signature) -> s.call_effect.on_throw) calls
        | _ -> top_footprint,false) (empty_footprint,true) types in
    List.fold_left (fun changed (pos,(f,t)) ->
      let f',t' = effect_of pos in
      let raised = join_footprint f f' in
      let kept = t && t' && raised <> top_footprint in
      if raised = f && kept = t then changed
      else (Hashtbl.replace Source.self_effects pos (raised,kept); true))
      false (List.of_seq (Hashtbl.to_seq Source.self_effects)) in
  let rec rounds assumed thrown =
    let proposal : Proposal_types.t = infer_assuming ~thrown ~state flows program assumed in
    let selves_raised = raise_selves proposal in
    let footprints = List.map (fun c -> c,declaration_footprint program.Source.declarations program.Source.values names c) proposal.functions in
    (* A stated declaration is assumed at most at its statement. *)
    let raised = List.filter_map (fun ((c:function_claim),(f,_)) ->
      match List.assoc_opt c.source.name assumed with
      | Some a -> Some (c.source.name,fst (within_statement (join_footprint a f,false)
          (Option.map (fun (s,_) -> s,false) c.source.stated)))
      | None -> None) footprints in
    let kept = List.filter (fun name -> List.exists (fun ((c:function_claim),(f,t)) ->
      c.source.name = name && t && f <> top_footprint) footprints) thrown in
    if raised = assumed && kept = thrown && not selves_raised then
      {proposal with functions=List.map (fun ((c:function_claim),(f,_)) ->
        let footprint = match List.assoc_opt c.source.name assumed with
          | Some a -> join_footprint a f | None -> top_footprint in
        let footprint,on_throw = within_statement
          (footprint,footprint <> top_footprint && List.mem c.source.name thrown) c.source.stated in
        {c with declared_footprint=footprint; declared_on_throw=on_throw}) footprints}
    else rounds raised kept in
  rounds start (List.map fst start)

and infer_assuming ?(thrown=[]) ~state flows program assumed =
  let module_functions = List.map (fun (g:Source.fn) -> g.name,lazy (with_footprint
      ~on_throw:(List.mem g.name thrown)
      (Option.value (List.assoc_opt g.name assumed) ~default:top_footprint) (module_type g)))
    program.Source.functions
    (* A qualified import is read as its unit's module reads the unit: at its
       certified footprint, its code discarding further actuals. *)
    @ List.map (fun (name,t) -> name,lazy (match List.find_opt (fun (n,_,_,_) -> n = name) program.Source.qualified with
        | Some (_,_,footprint,on_throw) -> with_footprint ~on_throw footprint t
        | None -> t)) program.Source.values in
  let arities = List.map (fun (g:Source.fn) -> g.name,arity g) program.Source.functions
    @ List.map (fun (n,_,_,_) -> n,Module_contract.Discards) program.Source.qualified in
  let infer_with = infer_function state flows program.Source.declarations arities in
  (* A class's instance members read the class as its own binding, `C.[[self]]`,
     at its construct signature: a module value of the initialization unit. *)
  let class_selves = List.concat_map (fun (s:Source.stmt) -> match s.statement with
    | Declare (false,bindings) ->
      let ctors = List.filter_map (fun (n,_,(e:expr)) -> match e.node with
        | Ctor _ -> Some n | _ -> None) bindings in
      List.filter_map (fun (n,written,_) -> match written with
        | Some t when List.mem n ctors || List.mem (n ^ ".[[class]]") ctors ->
          Some (n ^ ".[[self]]",lazy t)
        | _ -> None) bindings
    | _ -> []) program.Source.init in
  (* A module constant holding a closure without a rest, binders, defaults
     or a guard, whose result is written, and read as a value somewhere
     (called alone, it is called at its own arity), is claimed where it is created at its
     signature extended by a rest of `unknown` elements too, as a module
     function's slot is: its code discards the actuals past its parameters,
     and Lean checks its body at that signature. A unit passing it where a
     signature binding more parameters is expected meets that one. *)
  (* A name the source spells, not one the parser makes for a class's parts. *)
  let source_name n = n <> "" && String.for_all (fun c ->
    c = '_' || c = '$' || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')) n in
  (* The names the module reads as values: anywhere but as a called callee. *)
  let rec valued (e:expr) = match e.node with
    | Call ({node=Id _;_},r,args,_,_) -> List.concat_map valued (Option.to_list r @ args)
    | Id n -> [n]
    | _ -> List.concat_map valued (children e) in
  let read_as_values = List.concat_map valued (List.concat_map statement_children
    (program.Source.init @ List.concat_map (fun (g:Source.fn) -> g.body) program.Source.functions)) in
  let discarding = List.concat_map (fun (s:Source.stmt) -> match s.statement with
    | Declare (false,bindings) -> List.filter_map (fun (name,written,(e:expr)) -> match written,e.node with
        | None,Lambda (receiver,[],ps,[],false,Some result,None,_)
          when source_name name && List.mem name read_as_values ->
          Some (e.pos,[{quantified=[];receiver=Option.value receiver ~default:top;
            params=List.map snd ps;variadic=Some top;
            rest_pack=None;result;call_effect=ordinary_effect}])
        | _ -> None) bindings
    | _ -> []) program.Source.init in
  let init = match program.Source.init with
    | [] -> None
    | body -> Some (infer_function ~offers:discarding state flows program.Source.declarations arities
        (module_functions @ class_selves)
        {quantified=program.Source.init_quantified;name="";name_pos=Json.Null;params=[];rest=false;rest_pack=None;
         result=Atoms [Undef];guard=None;async=false;stated=None;body}) in
  (* The initialization unit checks both initializer and annotation. Use the
     annotation's offered signatures, retaining effects established by a matching
     initializer signature. Lean makes both checked contracts available. *)
  (* A generic class's constructor is quantified over the class's binders:
     a unit reading it names its instance, as for a generic function. *)
  let quantify_class t = match t with
    | Atoms [Ctors ([signature],statics)] when program.Source.init_quantified <> [] ->
      let mentioned = List.filter (fun (q:Semantic.quantifier) ->
        let rec mentions = function
          | Rigid r -> r = q.identity
          | Union ts -> List.exists mentions ts
          | Meet (t,ts) -> List.exists mentions (t::ts)
          | Atoms atoms -> List.exists (function
              | Named (_,args) -> List.exists mentions args
              | _ -> false) atoms in
        List.exists mentions (signature.result :: signature.params)) program.Source.init_quantified in
      if mentioned = [] then t else Atoms [Ctors ([{signature with quantified=mentioned}],statics)]
    | t -> t in
  let module_constants = List.concat_map (fun (s:Source.stmt) -> match s.statement with
    | Declare (false,bindings) -> List.map (fun (n,written,(e:expr)) -> n,lazy (
        match Option.bind init (fun c -> List.find_opt (fun (x:expression) -> x.pos = e.pos) c.expressions) with
        | Some x -> quantify_class (match written with
          | None -> x.type_
          | Some contract -> retain_call_effects contract x.type_)
        | None -> Proposal_diagnostics.unsupported ("module constant " ^ n ^ " has no claimed initializer")))
      bindings
    | _ -> []) program.Source.init in
  (* The module's cells, at the contracts the initialization unit claims. *)
  Environment.module_cells := List.concat_map (fun (s:Source.stmt) -> match s.statement with
    | Declare (true,bindings) -> List.filter_map (fun (n,_,(e:expr)) ->
        if not (Hashtbl.mem Source.early_bindings (n,e.pos)) then None else
        match Option.bind init (fun (c:function_claim) ->
          List.find_opt (fun (x:contract) -> x.pos = e.pos && x.name = n) c.contracts) with
        | Some x -> Some (n,x.type_)
        | None -> Proposal_diagnostics.unsupported ("module cell " ^ n ^ " has no claimed contract")) bindings
    | _ -> []) program.Source.init;
  {program;init;functions=List.map (infer_with (module_functions @ module_constants))
    program.Source.functions}
