open Semantic
open Environment
open Source
open Type_queries
open Proposal_diagnostics
module type Inputs = sig
  include Analysis_capabilities.Queries
  include Analysis_capabilities.Observations
  include Analysis_capabilities.Environment_queries
  include Analysis_capabilities.Speculation
end
module Make (S : Inputs) = struct
open S
  let target_contract (expr:Analysis_state.expression_infer) env (target:expr) = match target.node with
    | Id n ->
      ignore (expr env target);
      (match lookup env n with
       | Storage (contract,_) | Local (contract,_) -> contract
       | Value _ -> Proposal_diagnostics.unsupported "assignment to immutable binding")
    | _ -> expr env target
  (* The type `e as const` gives its operand: a literal its own type, an
     array literal the readonly tuple of its elements', an object literal
     readonly fields of theirs; a name keeps its type. None for any other
     operand, which TypeScript refuses. An element or field of a literal
     that is none of these (`[x.f] as const`) keeps its own type, as
     TypeScript's const context does. *)
  let rec const_type (expr:Analysis_state.expression_infer) ?(nested = false) env (e:expr) = match e.node with
    | Literal l -> Some (literal_type l)
    | Id n -> Some (resolve env n)
    | Cast ("const",None,e) -> const_type expr ~nested env e
    | ArrayLiteral (es,[]) ->
      let elements = List.map (const_type expr ~nested:true env) es in
      if List.mem None elements then None
      else Some (array {required=List.filter_map Fun.id elements;optional_elements=[];rest=None;readonly=true;presence=Dense})
    | Alloc fs ->
      let fields = List.map (fun (name,e) -> name,const_type expr ~nested:true env e) fs in
      if List.exists (fun (_,t) -> t = None) fields then None
      else Some (record (List.map (fun (name,t) ->
        {name;optional=false;read=Option.get t;write=None;host=false;receivers=[]}) fields))
    | _ when nested -> quietly (fun () -> expr env e)
    | _ -> None
  (* Explain an unsupported resolution contract. Bounded parameters are
     classified through their declared bounds, qualified ones through their
     descriptors; this query supplies only a diagnostic, while Lean checks
     the actual instance and its bounds. A native promise's payload is
     observed whatever it is, and resolved again by async return. *)
  let explain_thenable (e:expr) (target:expr) actuals =
    match target.node,actuals with
    | Id ("%Await%" | "%AsyncReturn%" | "%PromiseResolve%" as n),[actual] ->
      let promises = List.filter_map (fun (d:Source.declaration) ->
        if d.native_promise then Some d.id else None) declarations in
      let rec settled allow_objects seen seen_rigids = function
        | Union ts -> List.for_all (settled allow_objects seen seen_rigids) ts
        | Meet (t,ts) -> List.exists (settled allow_objects seen seen_rigids) (t::ts)
        | Rigid r -> S.owned_resolution r <> None || S.observation_owner r <> None ||
          (not (List.mem r seen_rigids) && (match S.rigid_bound r with
            | Some bound -> settled allow_objects seen (r::seen_rigids) bound
            | None -> false))
        | Atoms xs -> List.for_all (function
            | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Bigint | BigintLit _ | Symbol | SymbolLit _ -> true
            | Named (id,args) when List.mem id promises ->
              n <> "%AsyncReturn%" || List.for_all (settled true seen seen_rigids) args
            | Named (id,args) when not (List.mem id seen) ->
              (try settled allow_objects (id::seen) seen_rigids (definition declarations id args)
               with Json.Error _ -> false)
            | Shape {elements=Some _;_} -> allow_objects
            | Shape shape when allow_objects ->
              (try settled false seen seen_rigids
                (Type_queries.field_type (S.rigid_bounds ()) declarations [] (Atoms [Shape shape]) (Name "then"))
               with Json.Error _ -> false)
            | _ -> false) xs in
      if not (settled true [] [] actual) then
        S.explain e.pos (if n = "%Await%"
          then "the modeled await requires a native promise or a stably non-thenable value: " ^ thenable_reason
          else if n = "%PromiseResolve%" then
            "Promise.resolve requires an ordinary native promise or a stably non-thenable value: " ^ thenable_reason
          else "fresh async resolution requires a stably non-thenable payload, also when adopting a native promise: "
            ^ thenable_reason ^ "; primitives, ordinary arrays and lifetime primitive `then` contracts establish this bound")
    | _ -> ()
  (* An array `Array.isArray` found in `unknown` or a record, the built-ins'
     `readonly unknown[]`, passed where a call wants a mutable array of a
     binder: the binder's instance would be the array's own element contract. *)
  let explain_builtin_array site env n expected =
    match expected with
    | Some x ->
      let at_binder = function
        | Shape {elements=Some {rest=Some (Rigid _);readonly=false;_};_} -> true
        | _ -> false in
      let actual = try resolve env n with Json.Error _ -> Atoms [] in
      if actual = Refinement.any_array && List.exists at_binder (Option.value ~default:[] (flat_atoms declarations x)) then
        S.explain site ("a built-in array at a generic call's mutable array of a binder: " ^ builtin_array_reason)
    | None -> ()
  (* A record at an index signature, which TypeScript admits through an
     implicit index signature. *)
  let explain_record_at_index site env n expected =
    match expected with
    | Some x ->
      let named = try resolve env n with Json.Error _ -> Atoms [] in
      let actual = Option.value ~default:[] (flat_atoms declarations named) and wanted = Option.value ~default:[] (flat_atoms declarations x) in
      let record = function Shape {elements=None;calls=[];indexes=[];_} -> true | _ -> false in
      let dictionary = function Shape {elements=None;calls=[];indexes=_::_;_} -> true | _ -> false in
      if actual <> [] && List.for_all record actual && List.exists dictionary wanted
         && not (List.exists (fun a -> record a || a = Top) wanted) then
        S.explain site ("a record at an index signature: " ^ implicit_index_reason)
    | None -> ()
  (* A write at a key a dictionary may lack adds it. *)
  let dictionary_growth site t field =
    match Option.value ~default:[] (flat_atoms declarations t) with
    | [] -> ()
    | atoms -> if List.for_all (function
        | Shape {indexes=_::_;elements=None;calls=[];fields;_} ->
          not (List.exists (fun (f:Semantic.field) -> f.name = field) fields)
        | _ -> false) atoms then
      S.explain site ("a write adds the property '" ^ key_text field ^ "' where a dictionary may lack it: \
        another reference may hold the dictionary, and would see its keys change")

end
