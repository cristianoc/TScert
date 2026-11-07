(* The linear facts the producer proposes at statement entries
   (PROGRAM-TYPING.md, "Linear facts"): a must-analysis over safe-integer
   bindings, carried in the environment as pseudo-bindings
   (`Environment.fact_key`). Lean checks every proposed fact on every edge
   into an entry, so a fact proposed here is a claim, never an assumption.
   The transfer mirrors what Lean's steps state: an integer literal, a copy,
   a sum or a difference of operands with known ranges, and a comparison's
   answers; every other assignment of a binding forgets its facts. *)
open Environment
open Source

type fact = (string * int) list * int

let max_safe = 9007199254740991
let max_index = 4294967294

let facts env : fact list = List.filter_map (fun (n,_) -> fact_parts n) env
let strip env = List.filter (fun (n,_) -> not (is_fact n)) env

let norm (terms : (string * int) list) =
  let names = List.sort_uniq compare (List.map fst terms) in
  List.filter_map (fun n ->
    let c = List.fold_left (fun acc (m,c) -> if m = n then acc + c else acc) 0 terms in
    if c = 0 then None else Some (n,c)) names

let int_fact x : fact = [x,0], 0
let is_int_fact ((t,_) : fact) = List.for_all (fun (_,c) -> c = 0) t
let mentions x ((t,_) : fact) = List.mem_assoc x t
let forget x fs = List.filter (fun f -> not (mentions x f)) fs

(* One fact per form, at its least bound. *)
let tighten (fs : fact list) : fact list =
  let forms = List.sort_uniq compare (List.map fst fs) in
  List.map (fun t -> t, List.fold_left (fun acc (t',d) -> if t' = t then min acc d else acc) max_int fs) forms

let add env (fs : fact list) =
  let fs = tighten fs in
  strip env @ List.map (fun (t,b) -> fact_key t b, Value Semantic.top) fs

(* A binding a fact may name: a value or a slot local, never a cell. *)
let value_binding env x = match List.assoc_opt x env with
  | Some (Value _) | Some (Local _) -> true
  | _ -> false

let is_int fs x = List.exists (fun f -> mentions x f) fs

(* The range single-variable facts state of a binding. *)
let range fs x =
  List.fold_left (fun (lo,hi) ((t,d) : fact) -> match t with
    | [y,1] when y = x -> lo, Some (match hi with Some h -> min h d | None -> d)
    | [y,-1] when y = x -> Some (match lo with Some l -> max l (-d) | None -> -d), hi
    | _ -> lo,hi) (None,None) fs

let scale k (t : (string * int) list) = List.map (fun (n,c) -> n,k*c) t

(* The range of `t + c`, where every term has a known range. *)
let range_of fs ((t,c) : (string * int) list * int) =
  List.fold_left (fun acc (x,k) -> match acc with
    | None -> None
    | Some (lo,hi) -> (match range fs x with
      | Some l,Some h -> let a = k*l and b = k*h in Some (lo + min a b, hi + max a b)
      | _ -> None)) (Some (c,c)) t

let in_safe = function Some (lo,hi) -> -max_safe <= lo && hi <= max_safe | None -> false

let literal_int s =
  match float_of_string_opt s with
  | Some f when Float.is_integer f && Float.abs f <= 9007199254740991. -> Some (int_of_float f)
  | _ -> None

(* An operand Lean reads as a safe integer: a literal, or a binding a fact
   states one; a sum or a difference of such, each step's result in range. *)
let rec linear env fs (e : expr) : ((string * int) list * int) option = match e.node with
  | Literal (LNumber s) -> Option.map (fun i -> [],i) (literal_int s)
  | Id x when value_binding env x && is_int fs x -> Some ([x,1],0)
  | Arith ((Add | Sub) as op,a,b) ->
    (match linear env fs a, linear env fs b with
     | Some (ta,ca),Some (tb,cb) ->
       let r = if op = Add then norm (ta @ tb),ca+cb else norm (ta @ scale (-1) tb),ca-cb in
       if in_safe (range_of fs r) then Some r else None
     | _ -> None)
  | _ -> None

(* `x = t + c`: x a safe integer equal to the sum. *)
let equal x (t,c) : fact list =
  [int_fact x; norm ((x,1) :: scale (-1) t), c; norm ((x,-1) :: t), -c]

let assign env fs x (e : expr) =
  if not (value_binding env x) then forget x fs else
  match linear env fs e with
  | Some ([y,1],c) when y = x ->
    (* `x = x + c`: each fact of the old value restated of the new one. *)
    List.map (fun ((t,d) as f) -> match List.assoc_opt x t with
      | Some a when not (is_int_fact f) -> t, d + a*c
      | _ -> f) fs
  | Some (t,c) when not (List.mem_assoc x t) -> forget x fs @ equal x (t,c)
  | _ -> forget x fs

let names_assigned (s : stmt) env =
  List.filter (fun (n,_) -> not (is_fact n) && Source.assigns n s) env |> List.map fst

(* A statement's effect on the facts: an assignment or update of a slot
   binding by a linear expression, and every other assigned binding
   forgotten. *)
let statement env fs (s : stmt) =
  match s.statement with
  | Effect {node=Assign (x,_,e);_} -> assign env fs x e
  | Effect {node=Update ((Add | Sub) as op,({node=Id x;_} as target),rhs,_);pos} ->
    let one = {node=Literal (LNumber "1"); pos} in
    let r = match rhs with Some r -> r | None -> one in
    assign env fs x {node=Arith (op,target,r); pos}
  | _ -> List.fold_left (fun fs x -> forget x fs) fs (names_assigned s env)

let declaration env fs name (init : expr) =
  let fs = forget name fs in
  match linear env fs init with
  | Some (t,c) when not (List.mem_assoc name t) -> fs @ equal name (t,c)
  | _ -> fs

(* What each answer of a comparison of two operands states. *)
let comparison env fs (cond : expr) : fact list * fact list =
  match cond.node with
  | Arith ((Lt | Le | Gt | Ge) as op,a,b) ->
    (match linear env fs a, linear env fs b with
     | Some (ta,ca),Some (tb,cb) ->
       let d = norm (ta @ scale (-1) tb) and c = ca - cb in
       let neg = scale (-1) d in
       (match op with
        | Lt -> [d,-1-c],[neg,c]
        | Le -> [d,-c],[neg,c-1]
        | Gt -> [neg,c-1],[d,-c]
        | _ -> [neg,c],[d,-1-c])
     | _ -> [],[])
  | _ -> [],[]

let rec writes_index xs j (s : stmt) =
  let rec in_expr (e : expr) = match e.node with
    | IndexWrite ({node=Id a;_},{node=Id k;_},_) when a = xs && k = j -> true
    | _ -> List.exists in_expr (Source.children e) in
  match s.statement with
  | Effect e | Return e | Throw e -> in_expr e
  | Declare (_,bs) -> List.exists (fun (_,_,e) -> in_expr e) bs
  | If (c,a,b) -> in_expr c || List.exists (writes_index xs j) (a @ b)
  | Block (_,b) -> List.exists (writes_index xs j) b
  | _ -> false

(* The true answer of `j < xs.length`, with `0 ≤ j` known, before a body
   writing `xs[j]`: `j` is an index at most the length (the bound atom) and at
   most `2^32 - 2`, which Lean derives from the length's range. *)
let length_test env fs (cond : expr) body =
  match cond.node with
  | Arith (Lt,{node=Id j;_},{node=Read ({node=Id xs;_},Semantic.Name "length");_})
    when value_binding env j && value_binding env xs && is_int fs j
         && (match range fs j with Some l,_ -> l >= 0 | _ -> false)
         && List.exists (writes_index xs j) body ->
    Some (xs,j), [[j,1],max_index]
  | _ -> None,[]

(* At a merge, a fact of one form holds at the larger bound where both
   paths state one. A bound larger than the one the earlier state (`l`, the
   state the flow solver joins into) held is raised at once to `2^32 - 1`, the
   largest length, where it is at most that, and forgotten otherwise, so each
   form changes at most twice and a loop settles as it would without facts. *)
let join (l : fact list) (r : fact list) : fact list =
  let l = tighten l and r = tighten r in
  List.filter_map (fun (t,d) ->
    match List.assoc_opt t r with
    | None -> None
    | Some d' when d' <= d -> Some (t,d)
    | Some d' when d' <= max_index + 1 && d < max_index + 1 -> Some (t, max_index + 1)
    | Some _ -> None) l
  |> List.sort_uniq compare

(* Widening keeps the facts that did not change. *)
let widen (previous : fact list) (current : fact list) =
  let previous = tighten previous in
  List.filter (fun (t,d) -> match List.assoc_opt t previous with
    | Some d' -> d <= d'
    | None -> false) (tighten current)
