open Semantic
(* Value snapshots and storage contracts have different constructors. The
   environment is persistent; reads never expose a way to alter storage types.
   A cell carries its fixed contract and what it is proposed to hold here:
   the contract, or a primitive refinement or nullish exclusion after an assignment or a guard,
   which Lean checks as a fact about the cell's current contents on every
   edge into the point claiming it. A slot (`Local`) carries its contract
   and what it holds here, any type: Lean holds it in its activation's
   environment (the flow graph's `cells` omit it), where no call, closure or
   throw reaches it. *)
type binding = Value of ty | Storage of ty * ty | Local of ty * ty
let binding_type = function Value t | Storage (_,t) | Local (_,t) -> t
let cell contract = Storage (contract,contract)
let lookup env name = match List.assoc_opt name env with
  | Some b -> b | None -> Json.fail ("unbound name " ^ name)
let is_field n = String.contains n '\000'
let owner n = String.sub n 0 (String.index n '\000')
let extend env name binding =
  if List.mem_assoc name env then Json.fail ("unsupported: shadowing " ^ name);
  env @ [name,binding]

(* Primitive observations have a type independent of the storage contract. *)
let knowable = function
  | Atoms xs -> List.for_all (function
      | Nul | Undef | True | False | Num | NumLit _ | Str | StrLit _ -> true
      | _ -> false) xs
  | Rigid _ | Union _ | Meet _ -> false
(* Retain primitive observations or remove the nullish alternatives known
   absent from the current value. Every other part of the contract stays fixed;
   Lean checks the exclusion where the observation is consumed. *)
let observed_contents contract t =
  if knowable t then t
  else match contract,t with
    | Atoms xs,Atoms (_::_ as ys) when not (List.mem Top ys) ->
      Atoms (List.filter (function
        | Nul -> List.mem Nul ys
        | Undef -> List.mem Undef ys
        | _ -> true) xs)
    | _ -> contract
let holding contract t = Storage (contract,observed_contents contract t)

(* A branch refines an immutable value, and a cell's known contents where
   the refinement is a supported current-content predicate. *)
let refine_value env name refine = List.map (fun (n,b) ->
  if n=name then n,(match b with
    | Value t -> Value (refine t)
    | Storage (contract,current) -> holding contract (refine current)
    | Local (contract,current) -> Local (contract,refine current))
  else n,b) env
(* After an assignment, the cell holds the value written. *)
let assign env name t = List.map (fun (n,b) ->
  if n=name then n,(match b with
    | Storage (contract,_) -> holding contract t
    | Local (contract,_) -> Local (contract,t)
    | Value _ -> b)
  else n,b) env
(* What a field of an immutable binding's object currently holds, where a
   guard found it: an entry named by the object's name and the field joined
   by a NUL, which no name contains, holding a primitive refinement or nullish slice of the contract. Lean
   checks it on every edge into a point claiming it, as a current-content
   fact about the field. *)
let field_key name field = name ^ "\000" ^ field
let field_of n = let i = String.index n '\000' in String.sub n (i+1) (String.length n - i - 1)
let fact env key contract t =
  let current = observed_contents contract t in
  let rest = List.remove_assoc key env in
  if current <> Atoms [] && (knowable current || current <> contract)
  then rest @ [key,Value current] else rest
(* Where a step may write cells unseen (a call, a closure run later, a loop's
   other iterations), a cell is known only by its contract, and no field's
   contents are known. A step that assigns only locals keeps the fields. *)
(* A loop's widening: a slot holds what its contract admits. *)
let widen_locals ?(only = fun _ -> true) env = List.map (fun (n,b) -> match b with
  | Local (contract,_) when only n -> n,Local (contract,contract)
  | _ -> n,b) env
let forget ?only env = List.filter_map (fun (n,b) -> match b,only with
  | _,None when is_field n -> None
  | Storage (contract,_),None -> Some (n,cell contract)
  | Storage (contract,_),Some only when only n -> Some (n,cell contract)
  | _ -> Some (n,b)) env
