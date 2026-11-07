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

(* A term of a fact (Lean's `HeapKnowledge.Term`): a value binding's name,
   then the named data fields read from what it holds in turn, each after a
   `.` (its path), then what the term reads of the value the path ends at:
   nothing for the value itself, `:length` for the length of its array store,
   `:view` for the element count of the typed array it is. A binding's name
   and a field name have no `.` or `:`, so the parts never meet. *)
type kind = Value_term | Length_term | View_term
let make_term ?(path=[]) kind b =
  String.concat "." (b :: path) ^ (match kind with Value_term -> "" | Length_term -> ":length" | View_term -> ":view")
let length_term ?path xs = make_term ?path Length_term xs
let view_term ?path b = make_term ?path View_term b
let path_term b path = make_term ~path Value_term b
let term_parts t : string * string list * kind =
  let base,kind = match String.index_opt t ':' with
    | Some i -> String.sub t 0 i, (if String.sub t (i + 1) (String.length t - i - 1) = "view" then View_term else Length_term)
    | None -> t, Value_term in
  match String.split_on_char '.' base with
  | root :: path -> root,path,kind
  | [] -> base,[],kind
let term_binding t = let b,_,_ = term_parts t in b
(* A path, a length or an element count reads the heap (Lean's
   `Term.envOnly`). *)
let reads_heap t = let _,path,kind = term_parts t in kind <> Value_term || path <> []
let has_heap_term ((t,_) : fact) = List.exists (fun (n,_) -> reads_heap n) t

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
let mentions x ((t,_) : fact) = List.exists (fun (n,_) -> term_binding n = x) t
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

let is_int fs x = List.exists (fun ((t,_) : fact) -> List.mem_assoc x t) fs

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

(* Whether the facts entail `Σ c·t ≤ d` by Fourier–Motzkin elimination: the
   goal's negation, `-Σ c·t ≤ -d - 1`, beside the facts, each variable
   eliminated by combining the rows of opposite signs on it, the variable
   combining the fewest pairs first, until a row `0 ≤ b` with `b < 0`
   appears. Lean searches the same way (`Linear.prove`) and checks what it
   finds; a fact proposed here is a claim Lean checks. *)
let fm_entails (fs : fact list) ((t,d) : fact) =
  let limit = 400 and large = 1 lsl 58 in
  let coeff x t = Option.value ~default:0 (List.assoc_opt x t) in
  let rows = (norm (scale (-1) t), -d-1) :: List.map (fun (t,b) -> norm t, b) fs in
  let rec go rows =
    if List.exists (fun (t,b) -> t = [] && b < 0) rows then true else
    match List.sort_uniq compare (List.concat_map (fun (t,_) -> List.map fst t) rows) with
    | [] -> false
    | vars ->
      let sign x k = List.length (List.filter (fun (t,_) -> k * coeff x t > 0) rows) in
      let cost x = sign x 1 * sign x (-1) in
      let x = List.fold_left (fun y z -> if cost z < cost y then z else y) (List.hd vars) vars in
      let pos = List.filter (fun (t,_) -> coeff x t > 0) rows
      and neg = List.filter (fun (t,_) -> coeff x t < 0) rows
      and zero = List.filter (fun (t,_) -> coeff x t = 0) rows in
      let combined = List.concat_map (fun (tp,bp) -> List.filter_map (fun (tn,bn) ->
        let a = coeff x tp and b = - (coeff x tn) in
        let bound = b * bp + a * bn in
        if abs bp > large / (b + 1) || abs bn > large / (a + 1) then None
        else Some (norm (scale b tp @ scale a tn), bound)) neg) pos in
      let rows = zero @ combined in
      if List.length rows > limit then false else go rows in
  go rows

(* Whether the facts state a linear fact `Σ c·x ≤ d` over terms: a fact of
   one term by its range, any other by a held fact of the same form at a
   bound at most `d`, or by elimination (`fm_entails`). Lean decides the same
   entailment by its own search. *)
let entails fs ((terms,d) : fact) =
  let terms = norm terms in
  (match terms with
   | [x,1] -> (match range fs x with _,Some h -> h <= d | _ -> false)
   | [x,-1] -> (match range fs x with Some l,_ -> -l <= d | _ -> false)
   | _ -> List.exists (fun ((t,b) : fact) -> norm t = terms && b <= d) fs)
  || fm_entails fs (terms,d)

(* The ranges Lean's knowledge states of each length and element count the
   facts name (`HeapKnowledge.lengthRange`, `viewRange`). *)
let term_ranges (fs : fact list) : fact list =
  List.concat_map (fun ((t,_) : fact) -> List.concat_map (fun (n,_) -> match (let _,_,k = term_parts n in k) with
    | Length_term -> [[n,-1],0; [n,1],max_index + 1]
    | View_term -> [[n,-1],0; [n,1],max_safe]
    | Value_term -> []) t) fs |> List.sort_uniq compare

(* Whether `t + c` is a safe integer: by the ranges of its terms, or as Lean
   decides it, by the facts with those ranges entailing
   `-(2^53 - 1) ≤ t + c ≤ 2^53 - 1` (`IndexWrites`, the sum's atoms). *)
let safe fs ((t,c) : (string * int) list * int) =
  in_safe (range_of fs (t,c)) ||
  (let fs = fs @ term_ranges fs in entails fs (t, max_safe - c) && entails fs (scale (-1) t, max_safe + c))

let literal_int s =
  match float_of_string_opt s with
  | Some f when Float.is_integer f && Float.abs f <= 9007199254740991. -> Some (int_of_float f)
  | _ -> None

(* The path an expression reads: a value binding and the named fields read
   from it in turn. *)
let rec path_of env (e : expr) = match e.node with
  | Id x when value_binding env x -> Some (x,[])
  | Read (o,Semantic.Name f) when not (String.contains f '.') && not (String.contains f ':') ->
    Option.map (fun (b,p) -> b,p @ [f]) (path_of env o)
  | _ -> None

(* An operand Lean reads as a safe integer: a literal, or a binding or a
   path a fact states one; a sum or a difference of such, each step's result
   in range. `array b path` tells whether the path from `b` holds an array,
   whose `length` is its store's. *)
let rec linear ?(array = fun _ _ -> false) env fs (e : expr) : ((string * int) list * int) option = match e.node with
  | Literal (LNumber s) -> Option.map (fun i -> [],i) (literal_int s)
  | Id x when value_binding env x && is_int fs x -> Some ([x,1],0)
  | Read (o,Semantic.Name "length") when (match path_of env o with Some (b,p) -> array b p | None -> false) ->
    (match path_of env o with Some (b,path) -> Some ([length_term ~path b,1],0) | None -> None)
  | Read (_,Semantic.Name _) when (match path_of env e with Some (b,p) -> p <> [] && is_int fs (path_term b p) | None -> false) ->
    (match path_of env e with Some (b,p) -> Some ([path_term b p,1],0) | None -> None)
  (* `b.length` of a typed array, `%ByteLength%(b)`, whose result facts
     state it the view's element count. *)
  | Call ({node=Id "%ByteLength%";_},None,[o],[],_) when path_of env o <> None ->
    (match path_of env o with Some (b,path) -> Some ([view_term ~path b,1],0) | None -> None)
  | Arith ((Add | Sub) as op,a,b) ->
    (match linear ~array env fs a, linear ~array env fs b with
     | Some (ta,ca),Some (tb,cb) ->
       let r = if op = Add then norm (ta @ tb),ca+cb else norm (ta @ scale (-1) tb),ca-cb in
       if safe fs r then Some r else None
     | _ -> None)
  | _ -> None

(* `x = t + c`: x a safe integer equal to the sum. *)
let equal x (t,c) : fact list =
  [int_fact x; norm ((x,1) :: scale (-1) t), c; norm ((x,-1) :: t), -c]

let assign ~array env fs x (e : expr) =
  if not (value_binding env x) then forget x fs else
  match linear ~array env fs e with
  | Some ([y,1],c) when y = x ->
    (* `x = x + c`: each fact of the old value restated of the new one. *)
    List.map (fun ((t,d) as f) -> match List.assoc_opt x t with
      | Some a when not (is_int_fact f) -> t, d + a*c
      | _ -> f) fs
  | Some (t,c) when not (List.mem_assoc x t) -> forget x fs @ equal x (t,c)
  | _ -> forget x fs

let names_assigned (s : stmt) env =
  List.filter (fun (n,_) -> not (is_fact n) && Source.assigns n s) env |> List.map fst

(* Whether evaluating an expression writes no heap location: slots and
   constants, operators on them, reads, element reads (`%ElementAt%`, which
   writes nothing) and assignments of value bindings. *)
(* Whether every signature the binding `f` holds keeps the heap: its
   footprint keeps every location's value and store, and it changes neither
   its receiver's store nor its own locations, so Lean keeps every fact
   across a normal return (`call-keep`, `PromiseCalls.keepsHeap`). Set by the
   statement analysis, which reads the binding's declared type. *)
let keeps_heap : ((string * Environment.binding) list -> string -> bool) ref = ref (fun _ _ -> false)
let signatures_keep (calls : Semantic.signature list) =
  calls <> [] && List.for_all (fun (s : Semantic.signature) -> let e = s.Semantic.call_effect in
    e.Semantic.footprint.Semantic.on_value = Semantic.Keep && e.Semantic.footprint.Semantic.on_store = Semantic.Keep &&
    not e.Semantic.receiver_store && not e.Semantic.receiver_own) calls

let rec heap_free env (e : expr) = match e.node with
  | Id _ | Literal _ -> true
  | Not a | Unary (_,a) | Cast (_,_,a) | Read (a,_) -> heap_free env a
  | Arith (_,a,b) | Equality (_,a,b) | Logical (_,a,b) | Coalesce (a,b) -> heap_free env a && heap_free env b
  | Conditional (c,a,b) -> heap_free env c && heap_free env a && heap_free env b
  | Call ({node=Id "%ElementAt%";_},None,args,[],_) -> List.for_all (heap_free env) args
  | Call ({node=Id f;_},None,args,_,_) when !keeps_heap env f -> List.for_all (heap_free env) args
  | Assign (x,_,rhs) -> value_binding env x && heap_free env rhs
  | Update (_,{node=Id x;_},rhs,_) -> value_binding env x && Option.fold ~none:true ~some:(heap_free env) rhs
  | _ -> false

(* A destructuring that reads fields of a path alone, `const { f, g: h } = p`:
   each field bound to a name, no default and no rest; its path and the
   fields with the names they are bound to. *)
let destructure_reads env (s : stmt) = match s.statement with
  | Destructure (PObject (props,None),None,init) when heap_free env init ->
    (match path_of env init with
     | Some (root,path) ->
       let fields = List.filter_map (fun (f,t,d) -> match t,d with
         | PName (n,_),None when not (String.contains f '.') && not (String.contains f ':') -> Some (f,n)
         | _ -> None) props in
       if List.length fields = List.length props && not (List.mem_assoc root (List.map (fun (f,n) -> n,f) fields))
       then Some ((root,path),fields) else None
     | None -> None)
  | _ -> None

let statement_heap_free env (s : stmt) = match s.statement with
  | Effect e | Return e -> heap_free env e
  | Declare (_,bs) -> List.for_all (fun (_,_,e) -> heap_free env e) bs
  | If (c,_,_) | While (c,_,_) -> heap_free env c
  | Destructure _ -> destructure_reads env s <> None
  | _ -> false

(* The facts restated where a binding is declared at a path's read
   (`const b = p.f`): each fact naming a term of a path extending it restated
   of the binding, the path's prefix replaced by the binding's name, as Lean's
   read link and its bridge relate them. *)
let restate_read name (root,path) (fs : fact list) : fact list =
  let rec prefix p q = match p,q with
    | [],rest -> Some rest
    | f :: p,g :: q when f = g -> prefix p q
    | _ -> None in
  let rename t = let b,p,kind = term_parts t in
    if b <> root then None else Option.map (fun rest -> make_term ~path:rest kind name) (prefix path p) in
  List.filter_map (fun ((t,d) : fact) ->
    if List.exists (fun (n,_) -> rename n <> None) t then
      Some (norm (List.map (fun (n,c) -> (match rename n with Some m -> m | None -> n),c) t),d)
    else None) fs

(* A statement's effect on the facts: an assignment or update of a slot
   binding by a linear expression, and every other assigned binding
   forgotten. *)
let statement ~(array : string -> string list -> bool) env fs (s : stmt) : fact list =
  (* A fact naming a length or an element count reads the heap: kept where
     the statement writes none, as Lean keeps it (`IndexFact.envOnly`). *)
  let fs = if statement_heap_free env s then fs else List.filter (fun f -> not (has_heap_term f)) fs in
  match s.statement with
  | Effect {node=Assign (x,_,e);_} -> assign ~array env fs x e
  | Effect {node=Update ((Add | Sub) as op,({node=Id x;_} as target),rhs,_);pos} ->
    let one = {node=Literal (LNumber "1"); pos} in
    let r = match rhs with Some r -> r | None -> one in
    assign ~array env fs x {node=Arith (op,target,r); pos}
  | Destructure _ ->
    let fs = List.fold_left (fun fs x -> forget x fs) fs (names_assigned s env) in
    (* Each field's read restated of the name it is bound to. *)
    (match destructure_reads env s with
     | Some ((root,path),fields) ->
       let fs = List.fold_left (fun fs (_,n) -> forget n fs) fs fields in
       fs @ List.concat_map (fun (f,n) -> restate_read n (root,path @ [f]) fs) fields
     | None -> fs)
  | _ -> List.fold_left (fun fs x -> forget x fs) fs (names_assigned s env)

let declaration ~(array : string -> string list -> bool) env fs name (init : expr) : fact list =
  let fs = if heap_free env init then fs else List.filter (fun f -> not (has_heap_term f)) fs in
  let fs = forget name fs in
  let fs = match path_of env init with
    | Some (root,(_ :: _ as path)) when root <> name && heap_free env init -> fs @ restate_read name (root,path) fs
    | _ -> fs in
  match linear ~array env fs init with
  | Some (t,c) when not (List.mem_assoc name t) -> fs @ equal name (t,c)
  | _ -> fs

(* What each answer of a comparison of two operands states. *)
let atom_comparison ~array env fs (cond : expr) : fact list * fact list =
  match cond.node with
  | Arith ((Lt | Le | Gt | Ge) as op,a,b) ->
    (match linear ~array env fs a, linear ~array env fs b with
     | Some (ta,ca),Some (tb,cb) ->
       let d = norm (ta @ scale (-1) tb) and c = ca - cb in
       let neg = scale (-1) d in
       (match op with
        | Lt -> [d,-1-c],[neg,c]
        | Le -> [d,-c],[neg,c-1]
        | Gt -> [neg,c-1],[d,-c]
        | _ -> [neg,c],[d,-1-c])
     | _ -> [],[])
  (* A strict equality of two operands states `a = b` on its `true` answer
     and `a ≠ b` on its `false` one, a strict inequality the reverse (Lean's
     `IndexWrites.equalAtoms`). The facts here are inequalities: `a ≠ b`
     with `a ≤ b` held is `a ≤ b - 1`, as Lean's strict step derives it, and
     with `b ≤ a` held `b ≤ a - 1`. A comparison with a number literal is a
     tag test in Lean's lowering (`numEq`), which states no linear fact. *)
  | Equality ((StrictEqual | StrictUnequal) as op,a,b)
    when (match a.node, b.node with Literal (LNumber _),_ | _,Literal (LNumber _) -> false | _ -> true) ->
    (match linear ~array env fs a, linear ~array env fs b with
     | Some (ta,ca),Some (tb,cb) ->
       let d = norm (ta @ scale (-1) tb) and c = ca - cb in
       let equal = [d,-c; scale (-1) d,c] in
       let unequal = (if entails fs (d,-c) then [d,-c-1] else []) @
         (if entails fs (scale (-1) d,c) then [scale (-1) d,c-1] else []) in
       if op = StrictEqual then equal,unequal else unequal,equal
     | _ -> [],[])
  | _ -> [],[]

(* The bounds (`Environment.bound_key`): an array binding, an index binding
   and whether the index is below the length (`strict`) or at most it. They
   flow beside the linear facts and mirror what Lean's steps keep: a
   comparison with an array's length states one on the answer giving
   `j < length` (`IndexWrites.lengthAtoms`); a statement that writes no heap
   keeps those whose bindings it does not assign; every other statement
   forgets them. *)
type bound = string * string * bool

let bounds env : bound list = List.filter_map (fun (n,_) -> bound_parts n) env
let strip_bounds env = List.filter (fun (n,_) -> not (is_bound n)) env

(* One bound per array and index, strict where any is. *)
let tighten_bounds (bs : bound list) : bound list =
  let pairs = List.sort_uniq compare (List.map (fun (a,i,_) -> a,i) bs) in
  List.map (fun (a,i) -> a,i,List.exists (fun (a',i',s) -> a'=a && i'=i && s) bs) pairs

let add_bounds env (bs : bound list) =
  strip_bounds env @ List.map (fun (a,i,s) -> bound_key ~strict:s a i, Value Semantic.top) (tighten_bounds bs)

(* At a merge, a bound both paths hold, strict where both are. *)
let join_bounds (l : bound list) (r : bound list) : bound list =
  let r = tighten_bounds r in
  List.filter_map (fun (a,i,s) -> match List.find_opt (fun (a',i',_) -> a'=a && i'=i) r with
    | Some (_,_,s') -> Some (a,i,s && s')
    | None -> None) (tighten_bounds l)

(* The bounds a statement keeps: those whose bindings it does not assign, where
   it writes no heap. *)
let statement_bounds env (bs : bound list) (s : stmt) =
  if not (statement_heap_free env s) then [] else
  let assigned = names_assigned s env in
  List.filter (fun (a,i,_) -> not (List.mem a assigned) && not (List.mem i assigned)) bs

(* What each answer of a comparison of an index with an array's length states:
   on the answer giving `j < xs.length`, with `0 ≤ j` known, `j` an index
   below the length (`IndexWrites.lengthPair`). *)
let atom_bounds ~array env fs (cond : expr) : bound list * bound list =
  let index j = value_binding env j && is_int fs j && (match range fs j with Some l,_ -> l >= 0 | _ -> false) in
  let length (e : expr) = match e.node with
    | Read ({node=Id xs;_},Semantic.Name "length") when value_binding env xs && array xs [] -> Some xs
    | _ -> None in
  match cond.node with
  | Arith (Lt,{node=Id j;_},l) when index j -> (match length l with Some xs -> [xs,j,true],[] | None -> [],[])
  | Arith (Ge,{node=Id j;_},l) when index j -> (match length l with Some xs -> [],[xs,j,true] | None -> [],[])
  | Arith (Gt,l,{node=Id j;_}) when index j -> (match length l with Some xs -> [xs,j,true],[] | None -> [],[])
  | Arith (Le,l,{node=Id j;_}) when index j -> (match length l with Some xs -> [],[xs,j,true] | None -> [],[])
  | _ -> [],[]

(* Whether the path from a binding holds an array, by its declared type: set
   by the statement analysis. *)
let array_path : ((string * Environment.binding) list -> string -> string list -> bool) ref = ref (fun _ _ _ -> false)

(* The true answer of `j < xs.length`, with `0 ≤ j` known: `j` is at most
   `2^32 - 2`, which Lean derives from the length's range. *)
let atom_length_test ~array env fs (cond : expr) =
  match atom_bounds ~array env fs cond with
  | [_,j,_],_ -> [[j,1],max_index]
  | _ -> []

(* What each answer of a test states, its facts and its bounds. A
   comparison's as above; `a && b` answers `true` where both do, `b`
   evaluated with what `a`'s `true` states, and `a || b` answers `false`
   where both do, `b` evaluated with what `a`'s `false` states; the other
   answer states nothing. Lean evaluates `b` only on that answer of `a`
   (`choose`), so both answers' facts hold where the test answers so. *)
let rec test ~array env fs (cond : expr) : (fact list * bound list) * (fact list * bound list) =
  match cond.node with
  | Logical (conjunction,a,b) ->
    let (ta,bta),(fa,bfa) = test ~array env fs a in
    let left,left_bounds = if conjunction then ta,bta else fa,bfa in
    let (tb,btb),(fb,bfb) = test ~array env (fs @ left) b in
    if conjunction then (left @ tb, left_bounds @ btb),([],[])
    else ([],[]),(left @ fb, left_bounds @ bfb)
  | _ ->
    let t,f = atom_comparison ~array env fs cond and bt,bf = atom_bounds ~array env fs cond in
    (t @ atom_length_test ~array env fs cond, bt),(f,bf)

let comparison ~array env fs cond = let (t,_),(f,_) = test ~array env fs cond in t,f
let comparison_bounds ~array env fs cond = let (_,t),(_,f) = test ~array env fs cond in t,f

(* The bounds holding where the statement being typed starts, for a call
   whose signature states a precondition (`Expression_calls`): set by the
   flow around each statement it types, empty elsewhere. *)
let current_bounds : bound list ref = ref []
(* The linear facts holding there, alike. *)
let current_facts : fact list ref = ref []

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

(* `f ()` with the facts of a call stating a precondition (`current_facts`)
   extended by what the answer `yes` of the test `c` states: an arm of
   `c ? a : b`. A proposal: Lean promotes the test's facts where it observes
   its answer. *)
let with_test env (c : expr) yes f =
  let saved = !current_facts in
  if saved = [] then f () else begin
    let array = !array_path env in
    let t,fl = comparison ~array env saved c in
    current_facts := saved @ (if yes then t else fl);
    Fun.protect ~finally:(fun () -> current_facts := saved) f
  end
