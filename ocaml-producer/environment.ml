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
(* The `let` cells a body analysed, or a body enclosing a closure of it,
   declares: each allocated by that body, at a location no older object
   has (Lean's separation of a fresh allocation). *)
let unit_cells : string list ref = ref []
(* The module's cells (SOURCE-ELABORATION.md, "Module cells"), each at the contract
   the initialization unit claims: a module function reads and writes one as
   the cell it captures. *)
let module_cells : (string * ty) list ref = ref []
(* A name no binding of the run binds: a refusal, at `at`, the span of the
   source identifier read, where there is one. *)
let unbound ?at name = raise (Json.Error (Json.Unbound { name; at }))
let lookup ?at env name = match List.assoc_opt name env with
  | Some b -> b | None -> unbound ?at name
let is_field n = String.contains n '\000'
let owner n = String.sub n 0 (String.index n '\000')
(* A bound a guard states for the statement after it (PROGRAM-TYPING.md,
   "Writes at a checked index"): the value of `index` is an array index at
   most the length of the array `array` holds. It is held from the guard's
   failing edge to the next statement's entry, which claims it, and no
   further. *)
let bound_key array index = "\002" ^ array ^ "\002" ^ index
let is_bound n = String.length n > 0 && n.[0] = '\002'
let bound_parts n = match String.split_on_char '\002' n with
  | [""; array; index] -> Some (array, index)
  | _ -> None
(* A linear fact the producer proposes at statement entries (PROGRAM-TYPING.md,
   "Linear facts"): the sum of [terms], each a value binding's name and an
   integer coefficient, is at most [bound]. Held as a pseudo-binding whose
   name encodes it, so it flows and joins with the environment. The terms are
   sorted by name with nonzero coefficients; a fact with one zero term states
   only that its binding holds a safe integer. *)
let fact_key (terms : (string * int) list) (bound : int) =
  "\003" ^ string_of_int bound ^ String.concat "" (List.map (fun (n,c) -> "\004" ^ n ^ "\005" ^ string_of_int c) terms)
let is_fact n = String.length n > 0 && n.[0] = '\003'
let fact_parts n =
  if not (is_fact n) then None else
  match String.split_on_char '\004' (String.sub n 1 (String.length n - 1)) with
  | bound :: terms ->
    (try Some (List.map (fun t -> match String.split_on_char '\005' t with
        | [name; c] -> name, int_of_string c
        | _ -> raise Exit) terms, int_of_string bound)
     with _ -> None)
  | [] -> None
let extend env name binding =
  if List.mem_assoc name env then Json.unsupported ("shadowing " ^ name);
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
(* The state of a point no run reaches: each binding at the empty type, a
   cell's contents included, and each field entry kept. A join drops a state
   with a binding at the empty type, so a cell's contents on such a path stay
   out of what follows; Lean checks the edge by `vacuous-edge`, which reads
   the unsatisfiable context of the edge's source (a tested Boolean refined
   to the answer it rules out, a call's result at the empty type), whatever
   the target's claims state. *)
let unreachable env = List.map (fun (n,b) -> if is_field n then n,b else match b with
  | Value _ -> n,Value (Atoms [])
  | Local (contract,_) -> n,Local (contract,Atoms [])
  | Storage (contract,_) -> n,Storage (contract,Atoms [])) env

(* A branch refines an immutable value, and a cell's known contents where
   the refinement is a supported current-content predicate. *)
let refine_value env name refine = List.map (fun (n,b) ->
  if n=name then n,(match b with
    | Value t -> Value (refine t)
    | Storage (contract,current) -> holding contract (refine current)
    | Local (contract,current) -> Local (contract,refine current))
  else n,b) env
(* After an assignment, the cell holds the value written. A slot's member
   paths were of the object it held before, so their entries go. *)
let assign env name t = List.filter_map (fun (n,b) ->
  if n=name then Some (n,(match b with
    | Storage (contract,_) -> holding contract t
    | Local (contract,_) -> Local (contract,t)
    | Value _ -> b))
  else if is_field n && owner n = name && (match List.assoc_opt name env with
      Some (Local _) -> true | _ -> false) then None
  else Some (n,b)) env
(* What a field of an immutable binding's object currently holds, where a
   guard found it: an entry named by the object's name and the field joined
   by a NUL, which no name contains, holding a primitive refinement or nullish slice of the contract. Lean
   checks it on every edge into a point claiming it, as a current-content
   fact about the field. *)
let field_key name field = name ^ "\000" ^ field
let field_of n = let i = String.index n '\000' in String.sub n (i+1) (String.length n - i - 1)
(* A test's answer that narrowed the field (`answer`) is itself a fact of
   it: what it leaves is kept whole, an array slice say (Lean's tag atom),
   where it is a list of atoms; a type parameter's arm has no current-content
   label. *)
let fact ?(answer = false) env key contract t =
  let ground = match t with Atoms _ -> true | Rigid _ | Union _ | Meet _ -> false in
  let current = if answer && ground && not (knowable t) then t else observed_contents contract t in
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
let forget ?only ?(keep = fun _ -> false) env = List.filter_map (fun (n,b) -> match b,only with
  | _,None when is_field n -> if keep n then Some (n,b) else None
  | Storage (contract,_),None -> Some (n,cell contract)
  | Storage (contract,_),Some only when only n -> Some (n,cell contract)
  | _ -> Some (n,b)) env

(* What a member path of an immutable binding's object currently holds, where
   a test of the path's value found it (HOST-FAMILIES.md, "Linked reads"): an
   entry named by the root and the path's fields, after a NUL and a SOH, so
   that it is a field entry of its root, which a step that may write cells
   forgets. Lean reads it through the read link from the path's last read to
   the slot the test refined. *)
let path_key root fields = root ^ "\000\001" ^ String.concat "\001" fields
let is_path n = is_field n && (let i = String.index n '\000' in
  i + 1 < String.length n && n.[i+1] = '\001')
let rec path_of env (e:Source.expr) = match e.Source.node with
  | Source.Read ({Source.node=Source.Id name;_},Name f) ->
    (match List.assoc_opt name env with Some (Value _ | Local _) -> Some (name,[f]) | _ -> None)
  | Source.Read (inner,Name f) -> Option.map (fun (r,fs) -> (r,fs @ [f])) (path_of env inner)
  | _ -> None
let path_entry env e = Option.bind (path_of env e) (fun (r,fs) ->
  match List.assoc_opt (path_key r fs) env with Some (Value t) -> Some t | _ -> None)
let refine_path env (e:Source.expr) current refine = match path_of env e with
  | None -> env
  | Some (r,fs) ->
    let key = path_key r fs in
    let current = match List.assoc_opt key env with Some (Value t) -> Some t | _ -> current in
    (match current with
     | None -> env
     | Some t -> List.remove_assoc key env @ [key,Value (refine t)])
