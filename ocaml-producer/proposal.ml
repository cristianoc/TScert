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
let infer_function state flows declarations arities module_functions (f:Source.fn) =
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
  let (claim,requests),assumed = settled [] 4 [] in
  if requests = [] then claim else
  let offered = List.map (fun pos -> pos,List.filter_map (fun (p,s) ->
    if p = pos then Some s else None) requests)
    (List.sort_uniq compare (List.map fst requests)) in
  let (claim,_),_ = settled offered 4 assumed in
  claim

let infer ?(state = Proposal_diagnostics.create ()) flows program =
  let module_functions = List.map (fun (g:Source.fn) -> g.name,lazy (module_type g))
    program.Source.functions
    @ List.map (fun (name,t) -> name,lazy t) program.Source.values in
  let arities = List.map (fun (g:Source.fn) -> g.name,arity g) program.Source.functions in
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
  let init = match program.Source.init with
    | [] -> None
    | body -> Some (infer_with (module_functions @ class_selves)
        {quantified=program.Source.init_quantified;name="";name_pos=Json.Null;params=[];rest=false;rest_pack=None;
         result=Atoms [Undef];body}) in
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
  {program;init;functions=List.map (infer_with (module_functions @ module_constants))
    program.Source.functions}
