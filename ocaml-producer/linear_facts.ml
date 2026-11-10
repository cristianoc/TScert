(* The linear facts the producer proposes at statement entries
   (ARITHMETIC.md, "Linear facts"): a must-analysis over safe-integer
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
   `:view` for the length of the typed array it is, `:strlen` for the length
   of the string it is. A binding's name and a field name have no `.`; a
   shadowing local's name (`ends@7:11`) has `:`, so the kind is the suffix
   after the last one, where it names a kind. *)
type kind = Value_term | Length_term | View_term | Str_length_term
let make_term ?(path=[]) kind b =
  String.concat "." (b :: path) ^ (match kind with Value_term -> "" | Length_term -> ":length" | View_term -> ":view"
    | Str_length_term -> ":strlen")
(* A kind's name on the wire (`HeapKnowledge.Term.Kind`). *)
let kind_name = function Value_term -> "value" | Length_term -> "length" | View_term -> "view"
  | Str_length_term -> "strLength"
let length_term ?path xs = make_term ?path Length_term xs
let view_term ?path b = make_term ?path View_term b
let str_length_term ?path b = make_term ?path Str_length_term b
let path_term b path = make_term ~path Value_term b
(* A term's binding, path and kind: the kind its suffix names, where it has
   one. A binding's own name may hold `:` (a shadowing local's
   `after@26:11`, `Fragment.shadowName`), so the suffix is matched whole. *)
let term_parts t : string * string list * kind =
  let base,kind = match String.rindex_opt t ':' with
    | Some i ->
      (match String.sub t (i + 1) (String.length t - i - 1) with
       | "length" -> String.sub t 0 i, Length_term
       | "view" -> String.sub t 0 i, View_term
       | "strlen" -> String.sub t 0 i, Str_length_term
       | _ -> t, Value_term)
    | None -> t, Value_term in
  match String.split_on_char '.' base with
  | root :: path -> root,path,kind
  | [] -> base,[],kind
let term_binding t = let b,_,_ = term_parts t in b
(* The bindings of the body being analysed held in cells, early ones
   aside (ARITHMETIC.md, "Terms for bindings held in cells"): a term
   rooted at one reads the cell's field `value`, as Lean's lowering roots it
   (`termRoot`). Set by the flow around each body. *)
let cell_terms : (string -> bool) ref = ref (fun _ -> false)
(* The body's parameters held in slots, whose objects are older than its
   cells. Set by the flow around each body. *)
let parameter_binding : (string -> bool) ref = ref (fun _ -> false)
(* Whether a binding was declared before every cell the write at hand
   writes, set by `after_cell_updates`: its object is older than those
   cells, which Lean's separation at each cut keeps apart from the fields
   its record names (`Observations.separationFacts`). *)
let older_than_written : (string -> bool) ref = ref (fun _ -> false)
(* How many bodies' flows are being solved, a closure's inside its owner's. *)
let body_depth = ref 0
(* A path, a length or a typed-array length reads the heap (Lean's
   `Term.envOnly`), as does a term rooted at a cell; a binding's value and
   the length of the string it holds read the environment alone. *)
let reads_heap t = let b,path,kind = term_parts t in
  (kind <> Value_term && kind <> Str_length_term) || path <> [] || !cell_terms b
let has_heap_term ((t,_) : fact) = List.exists (fun (n,_) -> reads_heap n) t
(* A slot's own value, which an `int` fact states defined (Lean's `intSlot`);
   any other term is defined by a fact naming it (`termDefined`). *)
let slot_value t = let _,_,kind = term_parts t in kind = Value_term && not (reads_heap t)

(* Whether the path from a binding holds a string, set by the statement
   analysis, which reads the type. *)
let string_path : ((string * Environment.binding) list -> string -> string list -> bool) ref = ref (fun _ _ _ -> false)

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

(* The facts with every term rooted at the binding `x` eliminated: those
   naming none kept, and each pair of opposite signs on one such term
   combined to cancel it (Fourier–Motzkin), at most 64 new facts per term,
   as Lean eliminates a dropped slot (`HeapKnowledge.eliminateIndices`). So
   `j = i + 1` with `0 ≤ i` keeps `1 ≤ j` where `i` is reassigned. *)
let forget x fs =
  let coeff n t = Option.value ~default:0 (List.assoc_opt n t) in
  let rec eliminate (fs : fact list) = function
    | [] -> fs
    | n :: rest ->
      let pos = List.filter (fun ((t,_) : fact) -> coeff n t > 0) fs
      and neg = List.filter (fun ((t,_) : fact) -> coeff n t < 0) fs
      and zero = List.filter (fun ((t,_) : fact) -> coeff n t = 0) fs in
      let made = List.concat_map (fun (tp,bp) -> List.map (fun (tn,bn) ->
        let a = coeff n tp and b = - (coeff n tn) in
        norm (List.map (fun (m,c) -> m,b*c) tp @ List.map (fun (m,c) -> m,a*c) tn), b * bp + a * bn) neg) pos in
      eliminate (zero @ List.filteri (fun i _ -> i < 64) (List.filter (fun ((t,d) : fact) -> t <> [] || d < 0) made)) rest in
  let fs = List.filter (fun f -> not (is_int_fact f && mentions x f)) fs in
  let terms = List.sort_uniq compare (List.concat_map (fun ((t,_) : fact) ->
    List.filter_map (fun (n,_) -> if term_binding n = x then Some n else None) t) fs) in
  if terms = [] then fs else List.filter (fun f -> not (mentions x f)) (eliminate fs terms)

(* The facts derived by eliminating each term reading a path (Fourier–
   Motzkin, as `forget` eliminates a binding's terms), those naming no path
   added, at most 16: a fact over bindings, root lengths and root element
   counts survives a heap change that a path does not, so `n = p.xs.length`
   and `b.length = p.xs.length` keep `n = b.length` past a call writing `p`'s
   fields. Lean checks each at the edge into the statement claiming it. *)
(* A fact over integers at its coefficients divided by their greatest
   common divisor, its bound rounded down (Lean's tightening step). *)
let tighten_fact ((t,d) as f : fact) : fact =
  let rec gcd a b = if b = 0 then a else gcd b (a mod b) in
  let g = List.fold_left (fun g (_,c) -> gcd g (abs c)) 0 t in
  if g > 1 then List.map (fun (n,c) -> n, c / g) t, (if d >= 0 then d / g else - ((- d + g - 1) / g)) else f

let close (fs : fact list) : fact list =
  let fs = List.sort_uniq compare (List.map tighten_fact fs) in
  let path_term n = let _,path,_ = term_parts n in path <> [] in
  let terms = List.sort_uniq compare (List.concat_map (fun ((t,_) : fact) ->
    List.filter_map (fun (n,_) -> if path_term n then Some n else None) t) fs) in
  if terms = [] then fs else
  let coeff n t = Option.value ~default:0 (List.assoc_opt n t) in
  let rec eliminate (fs : fact list) = function
    | [] -> fs
    | n :: rest ->
      let pos = List.filter (fun ((t,_) : fact) -> coeff n t > 0) fs
      and neg = List.filter (fun ((t,_) : fact) -> coeff n t < 0) fs
      and zero = List.filter (fun ((t,_) : fact) -> coeff n t = 0) fs in
      let made = List.concat_map (fun (tp,bp) -> List.map (fun (tn,bn) ->
        let a = coeff n tp and b = - (coeff n tn) in
        norm (List.map (fun (m,c) -> m,b*c) tp @ List.map (fun (m,c) -> m,a*c) tn), b * bp + a * bn) neg) pos in
      eliminate (zero @ List.filteri (fun i _ -> i < 64) (List.filter (fun ((t,d) : fact) -> t <> [] || d < 0) made)) rest in
  let rooted ((t,_) : fact) = List.for_all (fun (n,_) -> not (path_term n)) t in
  let derived = List.filter (fun ((t,_) as f) -> rooted f && List.exists (fun (n,_) -> reads_heap n) t &&
    not (List.mem f fs)) (eliminate (List.filter (fun f -> not (is_int_fact f)) fs) terms) in
  fs @ List.filteri (fun i _ -> i < 16) (List.sort_uniq compare derived)

(* One fact per form, at its least bound. *)
let tighten (fs : fact list) : fact list =
  let forms = List.sort_uniq compare (List.map fst fs) in
  List.map (fun t -> t, List.fold_left (fun acc (t',d) -> if t' = t then min acc d else acc) max_int fs) forms

(* A guarded fact (ARITHMETIC.md, "Guarded clauses"; Lean's
   `IndexFact.guarded`): where none of its guards, in order, reads its tag's
   value, its fact holds; a guard a value binding's name, the named data
   fields read from it in turn, and `null` or `undefined`. Held as a fact's
   pseudo-binding whose name, after `\003G`, encodes it; `fact_parts` reads
   none of these. *)
type guard = string * string list * string
type gfact = guard list * fact
let gfact_key ((gs,(t,b)) : gfact) =
  "\003G" ^ String.concat "\008" (List.map (fun (x,p,tag) -> x ^ "\007" ^ String.concat "." p ^ "\007" ^ tag) gs)
  ^ "\006" ^ fact_key (norm t) b
let gfact_parts n : gfact option =
  if String.length n < 2 || String.sub n 0 2 <> "\003G" then None else
  match String.index_opt n '\006' with
  | None -> None
  | Some i ->
    let gs = String.sub n 2 (i - 2) and f = String.sub n (i + 1) (String.length n - i - 1) in
    let guard g = match String.split_on_char '\007' g with
      | [x; p; tag] -> Some (x, (if p = "" then [] else String.split_on_char '.' p), tag)
      | _ -> None in
    let guards = List.map guard (String.split_on_char '\008' gs) in
    if gs = "" || List.exists Option.is_none guards then None else
    Option.map (fun fact -> List.filter_map Fun.id guards, fact) (fact_parts f)
let is_gfact n = gfact_parts n <> None
let gfacts env : gfact list = List.filter_map (fun (n,_) -> gfact_parts n) env

(* Disjunctions of linear facts, carried as entry claims. *)
type dfact = DAtom of fact | DEither of dfact * dfact
let rec djson = function
  | DAtom (t,b) -> Json.String (fact_key t b)
  | DEither (a,b) -> Json.Array [djson a;djson b]
let rec ddecode = function
  | Json.String s -> Option.map (fun f -> DAtom f) (fact_parts s)
  | Json.Array [a;b] -> (match ddecode a,ddecode b with Some a,Some b -> Some (DEither (a,b)) | _ -> None)
  | _ -> None
let dfact_key d = "\003D" ^ Json.encode (djson d)
let dfact_parts n =
  if not (String.starts_with ~prefix:"\003D" n) then None
  else ddecode (Json.parse (String.sub n 2 (String.length n - 2)))
let is_dfact n = String.starts_with ~prefix:"\003D" n
let dfacts env = List.filter_map (fun (n,_) -> dfact_parts n) env
let rec datoms = function DAtom f -> [f] | DEither (a,b) -> datoms a @ datoms b
let dbindings d = List.concat_map (fun (t,_) -> List.map (fun (n,_) -> term_binding n) t) (datoms d)
let dadd env ds = List.filter (fun (n,_) -> not (is_dfact n)) env @
  List.map (fun d -> dfact_key d,Value Semantic.top) (List.sort_uniq compare ds)
let current_dfacts : dfact list ref = ref []

(* A quantified fact (ARITHMETIC.md, "Quantified clauses"; Lean's
   `IndexFact.every`): for every index below the term `stop` of the array a
   value binding's path reads, each body fact holds, its terms the index
   (`%index`), the element at it (`%elem`) and terms over bindings. Held as
   a pseudo-binding whose name, after `\003E`, encodes it; `fact_parts` and
   `gfact_parts` read none of these. *)
type efact = { arr : string * string list; stop : string; body : fact list; choices : dfact list }
let rec dmap f = function DAtom a -> DAtom (f a) | DEither (a,b) -> DEither (dmap f a,dmap f b)
let index_var = "%index" and elem_var = "%elem"
let efact_key (e : efact) =
  "\003E" ^ fst e.arr ^ "\007" ^ String.concat "." (snd e.arr) ^ "\007" ^ e.stop ^ "\006" ^
  String.concat "\008" (List.map (fun (t,b) -> fact_key t b) e.body) ^ "\009" ^ Json.encode (Json.Array (List.map djson e.choices))
let efact_parts n : efact option =
  if String.length n < 2 || String.sub n 0 2 <> "\003E" then None else
  match String.index_opt n '\006' with
  | None -> None
  | Some i ->
    let head = String.sub n 2 (i - 2) and rest = String.sub n (i + 1) (String.length n - i - 1) in
    (match String.split_on_char '\007' head with
     | [root; path; stop] ->
       (match String.split_on_char '\009' rest with
        | [rest;choices] ->
          let body = if rest = "" then [] else List.map fact_parts (String.split_on_char '\008' rest) in
          let choices = try match Json.parse choices with Json.Array xs -> List.map ddecode xs | _ -> [None] with _ -> [None] in
          if List.exists Option.is_none body || List.exists Option.is_none choices then None else
          Some { arr = (root, if path = "" then [] else String.split_on_char '.' path); stop;
                 body = List.filter_map Fun.id body; choices = List.filter_map Fun.id choices }
        | _ -> None)
     | _ -> None)
let is_efact n = efact_parts n <> None
let efacts env : efact list = List.filter_map (fun (n,_) -> efact_parts n) env
(* The bindings a quantified fact names: its array's root, its bound's and
   its body terms'. *)
let ebindings (e : efact) =
  fst e.arr :: term_binding e.stop ::
    List.concat_map (fun ((t,_) : fact) -> List.filter_map (fun (n,_) ->
      if n = index_var || term_binding n = elem_var || String.starts_with ~prefix:"%offset" n then None else Some (term_binding n)) t) (e.body @ List.concat_map datoms e.choices)
(* The quantified facts holding where the statement being analysed starts,
   and the element reads of it they instantiate, each by the expression's
   position and the name of its value (`with_reads`). *)
let current_efacts : efact list ref = ref []
let element_reads : (Json.t * string) list ref = ref []
let eadd env (es : efact list) =
  List.filter (fun (n,_) -> not (is_efact n)) env @
    List.map (fun e -> efact_key e, Value Semantic.top) (List.sort_uniq compare es)

(* A region fact (Lean's `IndexFact.apart`; FOOTPRINTS.md, "Element
   regions"): the regions of the arrays two value bindings hold share no
   location. Held as a pseudo-binding whose name, after `\003R`, names both. *)
type rfact = string * string
let rfact_key ((x,y) : rfact) = "\003R" ^ x ^ "\007" ^ y
let rfact_parts n : rfact option =
  if String.length n < 2 || String.sub n 0 2 <> "\003R" then None else
  match String.split_on_char '\007' (String.sub n 2 (String.length n - 2)) with
  | [x; y] -> Some (x, y)
  | _ -> None
let is_rfact n = rfact_parts n <> None
let rfacts env : rfact list = List.filter_map (fun (n,_) -> rfact_parts n) env
let radd env (rs : rfact list) =
  List.filter (fun (n,_) -> not (is_rfact n)) env @
    List.map (fun r -> rfact_key r, Value Semantic.top) (List.sort_uniq compare rs)
let rapart (rs : rfact list) x y = List.mem (x,y) rs || List.mem (y,x) rs

(* A store separation (Lean's `IndexFact.storeApart`; ARITHMETIC.md, "Store
   separation"): the arrays two paths read from value bindings hold
   different stores. Held as a pseudo-binding whose name, after `\003S`,
   names both sides, each a binding and its fields; the sides in order. *)
type sfact = (string * string list) * (string * string list)
let sfact_norm ((a,b) : sfact) : sfact = if compare a b <= 0 then (a,b) else (b,a)
let sfact_key ((a,b) : sfact) =
  let side (x,p) = String.concat "\005" (x :: p) in
  "\003S" ^ side a ^ "\007" ^ side b
let sfact_parts n : sfact option =
  if String.length n < 2 || String.sub n 0 2 <> "\003S" then None else
  let side s = match String.split_on_char '\005' s with x :: p -> Some (x,p) | [] -> None in
  match String.split_on_char '\007' (String.sub n 2 (String.length n - 2)) with
  | [a; b] -> (match side a, side b with Some a, Some b -> Some (a,b) | _ -> None)
  | _ -> None
let is_sfact n = sfact_parts n <> None
let sfacts env : sfact list = List.filter_map (fun (n,_) -> sfact_parts n) env
let sadd env (ss : sfact list) =
  List.filter (fun (n,_) -> not (is_sfact n)) env @
    List.map (fun r -> sfact_key r, Value Semantic.top) (List.sort_uniq compare (List.map sfact_norm ss))
let sbindings (((x,_),(y,_)) : sfact) = [x; y]

let add env (fs : fact list) =
  let fs = tighten fs in
  List.filter (fun (n,_) -> not (is_fact n) || is_gfact n || is_efact n || is_dfact n || is_rfact n || is_sfact n) env @ List.map (fun (t,b) -> fact_key t b, Value Semantic.top) fs
let gadd env (gs : gfact list) =
  List.filter (fun (n,_) -> not (is_gfact n)) env @
    List.map (fun g -> gfact_key g, Value Semantic.top) (List.sort_uniq compare gs)
(* The bindings a guarded fact names, its guards' and its fact's. *)
let gbindings ((gs,(t,_)) : gfact) = List.map (fun (x,_,_) -> x) gs @ List.map (fun (n,_) -> term_binding n) t
let gmentions x g = List.mem x (gbindings g)
let gforget x (gs : gfact list) = List.filter (fun g -> not (gmentions x g)) gs

(* A binding held in a slot: a value or a slot local. *)
let slot_binding env x = match List.assoc_opt x env with
  | Some (Value _) | Some (Local _) -> true
  | _ -> false
(* A binding a fact may name: a slot's, or one held in a cell of the body
   (`cell_terms`). *)
let value_binding env x = slot_binding env x ||
  (match List.assoc_opt x env with Some (Storage _) -> !cell_terms x | _ -> false)

(* Whether a binding's type states a view's `[[viewLength]]` stable, set by
   the statement analysis, which reads the type. *)
let stable_view : ((string * Environment.binding) list -> string -> bool) ref = ref (fun _ _ -> false)

(* A term every step keeps (Lean's `HeapExpressionRules.stableTerm`): a
   binding's own value, or the length of a typed array a value
   binding holds whose type states `[[viewLength]]` stable, a location of
   one value. *)
let stable_term env t = not (reads_heap t) ||
  (let b,path,kind = term_parts t in kind = View_term && path = [] && slot_binding env b && !stable_view env b)
let stable_fact env ((t,_) : fact) = List.for_all (fun (n,_) -> stable_term env n) t
(* The facts a step writing the heap keeps whatever it writes. *)
let keep_stable env fs = List.filter (stable_fact env) fs

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
   finds; a fact proposed here is a claim Lean checks. The answer is a
   function of the facts and the goal, kept for the process: most calls
   repeat an earlier call's arguments. *)
let fm_memo : (fact list * fact, bool) Hashtbl.t = Hashtbl.create 1024
let rec fm_entails (fs : fact list) (goal : fact) =
  match Hashtbl.find_opt fm_memo (fs, goal) with
  | Some r -> r
  | None -> let r = fm_eliminate fs goal in Hashtbl.replace fm_memo (fs, goal) r; r
and fm_eliminate (fs : fact list) ((t,d) : fact) =
  let limit = 400 and large = 1 lsl 58 in
  let rec coeff (x : string) = function [] -> 0 | (y,c) :: r -> if String.equal x y then c else coeff x r in
  (* A row holds of integers at its coefficients divided by their greatest
     common divisor, its bound rounded down, as Lean's tightening step
     concludes it (`Linear.preSteps`). *)
  let rec gcd a b = if b = 0 then a else gcd b (a mod b) in
  let floor_div b g = if b >= 0 then b / g else - ((- b + g - 1) / g) in
  let tight (t,b) =
    let g = List.fold_left (fun g (_,c) -> gcd g (abs c)) 0 t in
    if g > 1 then List.map (fun (n,c) -> n, c / g) t, floor_div b g else t,b in
  let rows = List.map tight ((norm (scale (-1) t), -d-1) :: List.map (fun (t,b) -> norm t, b) fs) in
  let overflows (tp,bp) (tn,bn) x =
    let a = coeff x tp and b = - (coeff x tn) in abs bp > large / (b + 1) || abs bn > large / (a + 1) in
  let rec go rows =
    if List.exists (fun (t,b) -> t = [] && b < 0) rows then true else
    match List.sort_uniq compare (List.concat_map (fun (t,_) -> List.map fst t) rows) with
    | [] -> false
    | vars ->
      let split x = List.filter (fun (t,_) -> coeff x t > 0) rows, List.filter (fun (t,_) -> coeff x t < 0) rows in
      (* A variable none of whose combinations leaves the integers held
         first: a combination past them is dropped, losing its fact. Then
         the variable combining the fewest pairs. *)
      let key x = let pos,neg = split x in
        (not (List.for_all (fun p -> List.for_all (fun n -> not (overflows p n x)) neg) pos), List.length pos * List.length neg) in
      let keyed = List.map (fun x -> x,key x) vars in
      let x,_ = List.fold_left (fun (y,ky) (z,kz) -> if kz < ky then (z,kz) else (y,ky)) (List.hd keyed) keyed in
      let pos_x,neg_x = split x in
      let zero = List.filter (fun (t,_) -> coeff x t = 0) rows in
      let combined = List.concat_map (fun (tp,bp) -> List.filter_map (fun (tn,bn) ->
        let a = coeff x tp and b = - (coeff x tn) in
        let bound = b * bp + a * bn in
        if overflows (tp,bp) (tn,bn) x then None
        else Some (tight (norm (scale b tp @ scale a tn), bound))) neg_x) pos_x in
      let rows = zero @ combined in
      if List.length rows > limit then false else go rows in
  go rows

(* Whether the facts state a linear fact `Σ c·x ≤ d` over terms: a fact of
   one term by its range, any other by a held fact of the same form at a
   bound at most `d`, or by elimination (`fm_entails`). Lean decides the same
   entailment by its own search. *)
let entails_held fs ((terms,d) : fact) =
  let terms = norm terms in
  (match terms with
   | [x,1] -> (match range fs x with _,Some h -> h <= d | _ -> false)
   | [x,-1] -> (match range fs x with Some l,_ -> -l <= d | _ -> false)
   | _ -> List.exists (fun ((t,b) : fact) -> norm t = terms && b <= d) fs)
  || fm_entails fs (terms,d)

(* The safe-integer range of each value term the facts name (Lean's
   `HeapKnowledge.valueRanges`). *)
let value_ranges (fs : fact list) : fact list =
  List.concat_map (fun ((t,_) : fact) -> List.concat_map (fun (n,_) -> match (let _,_,k = term_parts n in k) with
    | Value_term -> [[n,-1],max_safe; [n,1],max_safe]
    | Length_term | View_term | Str_length_term -> []) t) fs |> List.sort_uniq compare

(* Entailment as Lean decides it (`Linear.entailsWith`, `entailsKnown`): by
   the facts, or, where they alone entail no goal, with the range of each
   safe integer they name. *)
let entails fs (goal : fact) = entails_held fs goal || entails_held (fs @ value_ranges fs) goal
let rec dpossible fs = function
  | DAtom f -> not (entails (f :: fs) ([], -1))
  | DEither (a,b) -> dpossible fs a || dpossible fs b
let rec dfreed fs = function
  | DAtom f -> [f]
  | DEither (a,b) ->
    if not (dpossible fs a) then dfreed fs b
    else if not (dpossible fs b) then dfreed fs a else []
let deliminate fs ds = List.sort_uniq compare (fs @ List.concat_map (dfreed fs) ds)


(* The ranges Lean's knowledge states of each length, typed-array length and
   string's length the facts name (`HeapKnowledge.lengthRange`, `viewRange`). *)
let term_ranges (fs : fact list) : fact list =
  List.concat_map (fun ((t,_) : fact) -> List.concat_map (fun (n,_) -> match (let _,_,k = term_parts n in k) with
    | Length_term -> [[n,-1],0; [n,1],max_index + 1]
    | View_term | Str_length_term -> [[n,-1],0; [n,1],max_safe]
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
  | Cast ("nonNull",_,a) -> path_of env a
  | Call ({node=Id ("%ElementAt%" | "%ByteAt%");_},None,[_;_],[],_)
    when List.mem_assoc e.pos !element_reads -> Some (List.assoc e.pos !element_reads,[])
  | Id x when value_binding env x -> Some (x,[])
  | Read (o,Semantic.Name f) when not (String.contains f '.') && not (String.contains f ':') ->
    Option.map (fun (b,p) -> b,p @ [f]) (path_of env o)
  | _ -> None

(* The step an update adds: `1` for `++`, the literal of `+= n`, negated
   for a subtraction. *)
let cell_step op (rhs : expr option) = match rhs with
  | None -> Some (if op = Add then 1 else -1)
  | Some {node=Literal (LNumber n);_} -> Option.map (fun d -> if op = Add then d else -d) (literal_int n)
  | Some _ -> None

(* An operand Lean reads as a safe integer: a literal, or a binding or a
   path a fact states one; a sum or a difference of such, each step's result
   in range. `array b path` tells whether the path from `b` holds an array,
   whose `length` is its store's. *)
(* The type of a module constant, set by the statement analysis. *)
let module_constant_type : (string -> Semantic.ty option) ref = ref (fun _ -> None)

(* The safe integer a binding's type admits alone: a value binding of the
   body, or else a module constant, whose type is one number's literal. *)
let literal_constant env x =
  let literal = function
    | Some (Semantic.Atoms [Semantic.NumLit bits]) -> literal_int (Printf.sprintf "%.17g" (Int64.float_of_bits bits))
    | _ -> None in
  match List.assoc_opt x env with
  | Some (Environment.Value t) -> literal (Some t)
  | Some _ -> None
  | None -> literal (!module_constant_type x)

let rec linear ?(array = fun _ _ -> false) env fs (e : expr) : ((string * int) list * int) option = match e.node with
  | Arith ((Shr | BitAnd),_,_) when List.mem_assoc e.pos !element_reads ->
    Some ([List.assoc e.pos !element_reads,1],0)
  | Literal (LNumber s) -> Option.map (fun i -> [],i) (literal_int s)
  | Id x when value_binding env x && is_int fs x -> Some ([x,1],0)
  | Read (o,Semantic.Name "length") when (match path_of env o with Some (b,p) -> array b p | None -> false) ->
    (match path_of env o with Some (b,path) -> Some ([length_term ~path b,1],0) | None -> None)
  | Read (_,Semantic.Name _) when (match path_of env e with Some (b,p) -> p <> [] && is_int fs (path_term b p) | None -> false) ->
    (match path_of env e with Some (b,p) -> Some ([path_term b p,1],0) | None -> None)
  (* An element read a quantified fact instantiates (`with_reads`), its
     value named, read through a non-null assertion. *)
  | Call ({node=Id ("%ElementAt%" | "%ByteAt%");_},None,[_;_],[],_) when List.mem_assoc e.pos !element_reads && is_int fs (List.assoc e.pos !element_reads) ->
    Some ([List.assoc e.pos !element_reads,1],0)
  | Cast ("nonNull",_,({node=Call ({node=Id ("%ElementAt%" | "%ByteAt%");_},None,[_;_],[],_);_} as a))
    when List.mem_assoc a.pos !element_reads && is_int fs (List.assoc a.pos !element_reads) ->
    Some ([List.assoc a.pos !element_reads,1],0)
  (* `s.length` of a string, the string's length (Lean's `string-length`). *)
  | Read (o,Semantic.Name "length") when (match path_of env o with Some (b,p) -> !string_path env b p | None -> false) ->
    (match path_of env o with Some (b,path) -> Some ([str_length_term ~path b,1],0) | None -> None)
  | Read (o,Semantic.Name "length") when (match path_of env o with
      | Some (b,p) -> List.exists (is_int fs) [length_term ~path:p b; view_term ~path:p b; str_length_term ~path:p b]
      | None -> false) ->
    (match path_of env o with
     | Some (b,p) -> Option.map (fun t -> [t,1],0)
         (List.find_opt (is_int fs) [length_term ~path:p b; view_term ~path:p b; str_length_term ~path:p b])
     | None -> None)
  (* `b.length` of a typed array, `%ByteLength%(b)`, whose postcondition
     states it the typed-array length. *)
  | Call ({node=Id "%ByteLength%";_},None,[o],[],_) when path_of env o <> None ->
    (match path_of env o with Some (b,path) -> Some ([view_term ~path b,1],0) | None -> None)
  (* `++x` or `x++` of a binding held in a cell or a slot, read against
     the facts after the update (`after_cell_updates`): the new value is
     `x`, the old one `x` less the step. *)
  | Update ((Add | Sub) as op,{node=Id x;_},rhs,post) when (!cell_terms x || slot_binding env x) && is_int fs x ->
    (match cell_step op rhs with
     | Some d -> Some ([x,1], if post then -d else 0)
     | None -> None)
  | Arith ((Add | Sub) as op,a,b) ->
    (match linear ~array env fs a, linear ~array env fs b with
     | Some (ta,ca),Some (tb,cb) ->
       let r = if op = Add then norm (ta @ tb),ca+cb else norm (ta @ scale (-1) tb),ca-cb in
       if safe fs r then Some r else None
     | _ -> None)
  | Arith (Mul,a,b) ->
    (match linear ~array env fs a, linear ~array env fs b with
     | Some ([],ca),Some (tb,cb) ->
       let r = norm (scale ca tb),ca*cb in if safe fs r then Some r else None
     | Some (ta,ca),Some ([],cb) ->
       let r = norm (scale cb ta),ca*cb in if safe fs r then Some r else None
     | _ -> None)
  | _ -> None

(* `x = t + c`: x a safe integer equal to the sum. *)
let equal x (t,c) : fact list =
  [int_fact x; norm ((x,1) :: scale (-1) t), c; norm ((x,-1) :: t), -c]

(* `a ± (c ? p : q)` read as `c ? a ± p : a ± q`, as Lean's lowering runs
   the rest of the expression in each arm, where `a` is a binding or a
   literal `c` does not assign. *)
let distribute (e : expr) = match e.node with
  | Arith ((Add | Sub) as op,({node=(Id _ | Literal _);_} as a),{node=Conditional (c,p,q);_})
    when (match a.node with Id x -> not (Source.assigns_expr x c) | _ -> true) ->
    Some (c,{e with node=Arith (op,a,p)},{e with node=Arith (op,a,q)})
  | _ -> None

(* The facts after `x = c ? p : q`, each arm assigned under what its answer
   of `c` states and the two joined (set below, where the comparison and the
   join are defined). *)
let assign_arms : (array:(string -> string list -> bool) -> (string * Environment.binding) list -> fact list ->
    string -> expr -> expr -> expr -> fact list option) ref = ref (fun ~array:_ _ _ _ _ _ _ -> None)

(* Signed shifts retain their quotient inequalities; a nonnegative mask
   bounds its result by the mask and the left operand. *)
let bitwise_facts ~array env fs x (e : expr) = match e.node with
  | Arith ((Shr | BitAnd as op),a,b) ->
    (match linear ~array env fs a, linear ~array env fs b with
     | Some (t,c),Some ([],d) when not (List.mem_assoc x t) && 0 <= d &&
         d < (if op = Shr then 32 else 2147483648) &&
         entails fs (scale (-1) t,c) && entails fs (t,2147483647-c) ->
       let base = [int_fact x; [x,-1],0] in
       if op = Shr then
         let q = 1 lsl d in
         base @ [norm ((x,q) :: scale (-1) t),c; norm ((x,-q) :: t),q-1-c]
       else base @ [[x,1],d; norm ((x,1) :: scale (-1) t),c]
     | _ -> [])
  | _ -> []

(* String addition states an equality of immutable UTF-16 lengths. *)
let concat_facts env name (e : expr) = match e.node with
  | Arith (Add,({node=Id a;_}),({node=Id b;_}))
    when a <> name && b <> name && !string_path env a [] && !string_path env b [] ->
    let r = str_length_term name and x = str_length_term a and y = str_length_term b in
    [norm [r,1;x,-1;y,-1],0; norm [r,-1;x,1;y,1],0]
  | _ -> []

(* The facts of `const x = e` over facts naming no `x`, set by the
   declaration analysis below: an assignment `x = e` whose value reads no
   `x` binds `x` as such a declaration does. *)
let assign_declared : (array:(string -> string list -> bool) -> (string * Environment.binding) list -> fact list ->
    string -> expr -> fact list) ref = ref (fun ~array:_ _ fs _ _ -> fs)

let rec mentions_name x (e : expr) = match e.node with
  | Id y -> y = x
  | _ -> List.exists (mentions_name x) (Source.children e)

let assign ~array env fs x (e : expr) =
  if not (value_binding env x) then forget x fs else
  match distribute e with
  | Some (c,p,q) -> (match !assign_arms ~array env fs x c p q with Some fs -> fs | None -> forget x fs)
  | None ->
  (* A constant whose type is one safe integer's literal (`lastKind = TEXT`,
     `const TEXT = 0`), a binding of the body or a module constant: that
     integer (Lean's `litSlot`). *)
  match (match e.node with Id y -> literal_constant env y | _ -> None) with
  | Some i -> forget x fs @ equal x ([],i)
  | None ->
  match linear ~array env fs e with
  | Some ([y,1],c) when y = x ->
    (* `x = x + c`: each fact of the old value restated of the new one. *)
    List.map (fun ((t,d) as f) -> match List.assoc_opt x t with
      | Some a when not (is_int_fact f) -> t, d + a*c
      | _ -> f) fs
  | Some (t,c) when not (List.mem_assoc x t) -> forget x fs @ equal x (t,c)
  | _ when not (mentions_name x e) -> !assign_declared ~array env (forget x fs) x e
  | _ -> forget x fs @ bitwise_facts ~array env fs x e @ concat_facts env x e

let names_assigned (s : stmt) env =
  List.filter (fun (n,_) -> not (is_fact n) && Source.assigns n s) env |> List.map fst

(* The slot bindings a statement writes inside an expression, a write other
   than the statement's own (the assignment or update an expression
   statement is): Lean rebinds the slot where the write runs
   (SOURCE-ELABORATION.md, "Slot or cell"), and the facts here read each
   operand at the statement's entry. Where there is one, the statement's
   facts of these bindings and of the bindings it assigns are forgotten. *)
let nested_slot_writes env (s : stmt) : string list =
  let rec writes (e : expr) acc = match e.node with
    | Lambda _ -> acc
    | _ ->
      let acc = match e.node with
        | Assign (n,_,_) | NullishAssign (n,_,_) | LogicalAssign (_,{node=Id n;_},_) -> n :: acc
        (* An update by a literal step is restated (`after_cell_updates`). *)
        | Update ((Add | Sub),{node=Id _;_},(None | Some {node=Literal _;_}),_) -> acc
        | Update (_,{node=Id n;_},_,_) -> n :: acc
        | ArrayAssign (targets,rest,_) ->
          List.filter_map (fun (_,(t:expr),_) -> match t.node with Id n -> Some n | _ -> None) targets
          @ (match rest with Some (_,_,{node=Id n;_},_) -> [n] | _ -> []) @ acc
        | _ -> acc in
      List.fold_left (fun acc c -> writes c acc) acc (Source.children e) in
  let rec statement_writes (e : expr) = match e.node with
    | Comma (a,b) -> statement_writes a @ statement_writes b
    | _ -> List.fold_left (fun acc c -> writes c acc) [] (Source.children e) in
  let names = match s.statement with
    | Effect e -> statement_writes e
    | Declare _ | Destructure _ | Return _ | Throw _ ->
      List.fold_left (fun acc e -> writes e acc) [] (Source.statement_children s)
    | If (c,_,_) | While (c,_,_) | ForOf (_,_,_,c,_) -> writes c []
    | Block _ | Try _ | Closing _ | Break _ | Continue -> [] in
  List.sort_uniq compare (List.filter (slot_binding env) names)

(* Whether evaluating an expression writes no heap location: slots and
   constants, operators on them, reads, element reads (`%ElementAt%`, which
   writes nothing) and assignments of value bindings. *)
(* Whether every signature the binding `f` holds keeps the heap: its
   footprint keeps every location's value and store, and it changes neither
   its receiver's store nor its own locations, so Lean preserves every fact
   across a normal return (`call-keep`, `PromiseCalls.keepsHeap`). Set by the
   statement analysis, which reads the binding's declared type. *)
let keeps_heap : ((string * Environment.binding) list -> string -> bool) ref = ref (fun _ _ -> false)
(* Whether every signature of the method `key` of the receiver's type keeps
   the heap, alike (`call-keep` at a method call). *)
(* Whether every construct signature of the class value `c` holds keeps the
   heap, alike (`call-keep` at a construction). *)
let ctor_keeps_heap : ((string * Environment.binding) list -> string -> bool) ref = ref (fun _ _ -> false)
let method_keeps_heap : ((string * Environment.binding) list -> expr -> Semantic.key -> bool) ref =
  ref (fun _ _ _ -> false)
let signatures_keep (calls : Semantic.signature list) =
  calls <> [] && List.for_all (fun (s : Semantic.signature) -> let e = s.Semantic.call_effect in
    e.Semantic.regions = [] && e.Semantic.footprint.Semantic.on_value = Semantic.Keep && e.Semantic.footprint.Semantic.on_store = Semantic.Keep &&
    not e.Semantic.receiver_store && not e.Semantic.receiver_own) calls

(* Whether `heap_free` admits updates of cells (`cell_terms`), whose
   facts the caller states (`after_cell_updates`). *)
let cells_written = ref false
let with_cells admitted f =
  let saved = !cells_written in
  cells_written := admitted;
  Fun.protect ~finally:(fun () -> cells_written := saved) f
let rec heap_free env (e : expr) = match e.node with
  | Id _ | Literal _ -> true
  | Not a | Unary (_,a) | Cast (_,_,a) | Read (a,_) -> heap_free env a
  | Arith (_,a,b) | Equality (_,a,b) | Logical (_,a,b) | Coalesce (a,b) | Comma (a,b) -> heap_free env a && heap_free env b
  | Conditional (c,a,b) -> heap_free env c && heap_free env a && heap_free env b
  | Call ({node=Id "%ElementAt%";_},None,args,[],_) -> List.for_all (heap_free env) args
  (* An index read of a string, a primitive, which reads no location. *)
  | Index (a,k) when (match path_of env a with Some (b,p) -> !string_path env b p | None -> false) ->
    heap_free env a && heap_free env k
  | Call ({node=Id f;_},None,args,_,_) when !keeps_heap env f -> List.for_all (heap_free env) args
  | Invoke ({node=Read (r,key);_},args,[],_) when heap_free env r && !method_keeps_heap env r key ->
    List.for_all (heap_free env) args
  | New ({node=Id c;_},_,args,[]) when !ctor_keeps_heap env c -> List.for_all (heap_free env) args
  (* An object literal of named fields allocates and writes only its own
     fresh locations (Lean's `allocOutput` keeps every index atom). *)
  | Alloc fields -> List.for_all (fun (_,v) -> heap_free env v) fields
  (* An array literal without spreads allocates only its store and its
     elements' fresh locations, as Lean's allocation keeps every index atom. *)
  | ArrayLiteral (es,[]) -> List.for_all (heap_free env) es
  | Assign (x,_,rhs) -> (slot_binding env x || (!cells_written && !cell_terms x)) && heap_free env rhs
  | Update (_,{node=Id x;_},rhs,_) -> (slot_binding env x || (!cells_written && !cell_terms x)) &&
    Option.fold ~none:true ~some:(heap_free env) rhs
  (* `x ??= v`, `x ||= v` and `x &&= v` read the binding, then on one path
     assign it, as `Assign` does. *)
  | NullishAssign (x,_,rhs) | LogicalAssign (_,{node=Id x;_},rhs) ->
    (slot_binding env x || (!cells_written && !cell_terms x)) && heap_free env rhs
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
  (* A parameter's default, `const x = p === undefined ? d : p`, binds a
     name alone. *)
  | Destructure (PName _,default,init) ->
    heap_free env init && Option.fold ~none:true ~some:(heap_free env) default
  | Destructure _ -> destructure_reads env s <> None
  | _ -> false

(* The bounds holding where the statement being typed starts, for a call
   whose signature states a precondition (`Expression_calls`): set by the
   flow around each statement it types, empty elsewhere. *)
let current_bounds : (string * string * bool) list ref = ref []
(* The linear facts holding there, alike. *)
let current_facts : fact list ref = ref []
(* The guarded facts holding there, alike. *)
let current_gfacts : gfact list ref = ref []

(* What a statement's one heap write may change, by what a location held
   before it (Lean's `HeapKnowledge.Changes`): an object, a number, an array
   store (its contents kept, its length kept, grown, or neither). A fact is
   kept where no location its terms read holds what the write may change
   (`Term.keptBy`): a path's locations hold objects, its last a number for a
   value term; a length reads a store, a typed-array length a number; or, where
   the write grows stores, where each length it names that is not kept has a
   coefficient at most 0 (`Term.formKeptBy`). *)
type changes = { obj : bool; num : bool; store : [`Keep | `Length | `Grow | `Any];
                 framed : string -> string -> bool;
                 (* The write's location is apart from every cell of the
                    body (Lean's `first`): a field of a parameter's object,
                    allocated before the body's cells. *)
                 apart : bool;
                 (* The write is a cell's of the body, apart from every
                    parameter's object. *)
                 cell_write : bool }

(* The classes a field's type admits, `(object, number, store)`, where the
   receiver's type states the field (Lean's `fieldChanges`); set by the
   statement analysis, which reads the receiver's type. *)
let field_classes : ((string * Environment.binding) list -> expr -> Semantic.key -> (bool * bool * bool) option) ref =
  ref (fun _ _ _ -> None)
(* The footprint every signature of the binding `f` states, where none
   excepts its receiver's store or own locations (Lean's `effectKept`). *)
let call_footprint : ((string * Environment.binding) list -> string -> Semantic.footprint option) ref =
  ref (fun _ _ -> None)
(* The footprint of a receiver method signature compatible with its actuals. *)
let method_footprint : ((string * Environment.binding) list -> expr -> Semantic.key -> expr list -> Semantic.footprint option) ref =
  ref (fun _ _ _ _ -> None)
(* Whether every signature of the binding `f`, or of a receiver's method,
   states a typed array's element write, which alters no object or number and
   keeps every store's length (Lean's `Effect.elementWrite`). *)
let call_element_write : ((string * Environment.binding) list -> string -> bool) ref = ref (fun _ _ -> false)
let method_element_write : ((string * Environment.binding) list -> expr -> Semantic.key -> bool) ref =
  ref (fun _ _ _ -> false)
(* Whether every signature of a receiver's method grows only its receiver's
   store (Lean's `Effect.receiverGrows`, `PromiseCalls.growChanges`). *)
let method_grows : ((string * Environment.binding) list -> expr -> Semantic.key -> bool) ref =
  ref (fun _ _ _ -> false)
(* Whether the array binding's store holds source values at every position,
   one writable homogeneous contract (Lean's `keepsLengths`). *)
let source_elements : ((string * Environment.binding) list -> string -> bool) ref = ref (fun _ _ -> false)
(* Whether every type the binding's type states for a field states
   `[[viewLength]]` stable (Lean's `viewField`): a field write keeps the
   typed-array length of the view the field holds (`view-path-stable`). *)
let view_field : ((string * Environment.binding) list -> string -> string -> bool) ref = ref (fun _ _ _ -> false)

let no_frame _ _ = false
let element_changes = { obj = false; num = false; store = `Length; framed = no_frame; apart = false; cell_write = false }
let of_classes env (o,n,a) = { obj = o; num = n; store = (if a then `Any else `Keep);
  framed = (fun b g -> slot_binding env b && !view_field env b g); apart = false; cell_write = false }
let of_footprint env (fp : Semantic.footprint) =
  { obj = fp.Semantic.on_value = Semantic.Any; num = not (Semantic.change_le fp.Semantic.on_value Semantic.Init);
    store = (match fp.Semantic.on_store with Semantic.Keep | Semantic.Init | Semantic.Scalar -> `Keep | _ -> `Any); framed = (fun b g -> slot_binding env b && !view_field env b g); apart = false; cell_write = false }

let term_kept ch t =
  let b,path,kind = term_parts t in
  (* A cell's term reads its field `value` first. The first location a
     term reads is one the write keeps (Lean's `first`) where the write is
     apart from the body's cells and the term a cell's, or the write is a
     cell's and the term rooted at a parameter, whose object is older. *)
  let cell = !cell_terms b in
  let path = if cell then "value" :: path else path in
  let first = (ch.apart && cell) || (ch.cell_write && (!parameter_binding b || !older_than_written b)) in
  let last = if kind = Value_term then ch.num else ch.obj in
  ((match path with
   | [] -> true
   | _ :: q -> (first || not (if q = [] then last else ch.obj)) && (q = [] || (not last && (List.length q = 1 || not ch.obj)))) &&
  (match kind with Value_term -> true | Length_term -> ch.store = `Keep || ch.store = `Length | View_term -> not ch.num
    | Str_length_term -> path = [])) ||
  (* A view's count read through one field the write keeps, its type stating
     the count stable (Lean's `Term.viewFramed`). *)
  (match kind, path with View_term, [g] -> not ch.obj && ch.framed b g | _ -> false)
(* A length a growing change grows, its path kept (Lean's `Term.grownBy`). *)
let term_grown ch t = let _,_,kind = term_parts t in
  kind = Length_term && ch.store = `Grow && term_kept { ch with store = `Keep } t
let fact_kept ch ((t,_) : fact) =
  List.for_all (fun (n,c) -> term_kept ch n || (c <= 0 && term_grown ch n)) t

(* An index below an array's length: a strict bound, or `0 ≤ k` and
   `k ≤ |xs| - 1` from the facts (Lean's `bounded`, strict). *)
let strictly_bounded ~facts ~bounds xs k =
  List.mem (xs,k,true) bounds ||
  (let fs = facts @ term_ranges facts in
   entails fs ([k,-1],0) && entails fs (norm [k,1; length_term xs,-1],-1))

(* The footprint of an expression whose heap writes are calls each keeping
   every location holding a store, within `{value: any, store: keep}`, its
   other parts writing none: the join of the calls'
   footprints, which the facts a call at it keeps bound (Lean's
   `Changes.ofClosed`); none for any other expression. *)
let rec object_calls env (e : expr) : Semantic.footprint option =
  let within fp = if Semantic.footprint_le fp {Semantic.on_value=Semantic.Any;on_store=Semantic.Keep} then Some fp else None in
  let join a b = match a,b with
    | Some a,Some b -> Some {Semantic.on_value=Semantic.join_change a.Semantic.on_value b.Semantic.on_value;
        on_store=Semantic.join_change a.Semantic.on_store b.Semantic.on_store}
    | _ -> None in
  let all es = List.fold_left (fun acc e -> join acc (object_calls env e)) (Some Semantic.empty_footprint) es in
  if heap_free env e then Some Semantic.empty_footprint else match e.node with
  | Lambda _ -> Some Semantic.empty_footprint
  | Not a | Unary (_,a) | Cast (_,_,a) | Read (a,_) -> object_calls env a
  | Arith (_,a,b) | Equality (_,a,b) | Logical (_,a,b) | Coalesce (a,b) | Comma (a,b) -> all [a;b]
  | Conditional (c,a,b) -> all [c;a;b]
  | Call ({node=Id f;_},None,args,[],_) -> join (all args) (Option.bind (!call_footprint env f) within)
  | Invoke ({node=Read (r,key);_},args,[],_) when not (!method_grows env r key) ->
    join (all (r :: args)) (if !method_keeps_heap env r key then Some Semantic.empty_footprint
      else Option.bind (!method_footprint env r key args) within)
  | Alloc fields -> all (List.map snd fields)
  | Assign (x,_,rhs) when slot_binding env x -> object_calls env rhs
  | Update (_,{node=Id x;_},Some rhs,_) when slot_binding env x -> object_calls env rhs
  | _ -> None
let object_changes env e = Option.map (of_footprint env) (object_calls env e)

(* The change of an expression whose one heap write is a field's, a checked
   element's or a call's, its operands writing none. *)
let write_changes ~facts ~bounds env (e : expr) : changes option =
  match e.node with
  | Write (recv,key,rhs) when heap_free env recv && heap_free env rhs ->
    Option.map (fun c -> { (of_classes env c) with apart = (match recv.node with
      | Id x -> !parameter_binding x | _ -> false) }) (!field_classes env recv key)
  | Update (_,{node=Read (recv,key);_},rhs,_) when heap_free env recv && Option.fold ~none:true ~some:(heap_free env) rhs ->
    Option.map (of_classes env) (!field_classes env recv key)
  | IndexWrite ({node=Id xs;_},{node=Id k;_},rhs)
    when heap_free env rhs && slot_binding env xs && slot_binding env k && !source_elements env xs && strictly_bounded ~facts ~bounds xs k ->
    Some { obj = true; num = true; store = `Length; framed = no_frame; apart = false; cell_write = false }
  (* `xs[j + 1] = v`: an index the facts give as a linear form, evaluated to
     a slot before the write, below the length as a slot's index is. *)
  | IndexWrite ({node=Id xs;_},k,rhs)
    when heap_free env k && heap_free env rhs && slot_binding env xs && !source_elements env xs &&
      (match linear env facts k with
       | Some (t,c) -> let fs = facts @ term_ranges ((t,0) :: facts) in
         entails fs (norm (scale (-1) t), c) && entails fs (norm ((length_term xs,-1) :: t), -1 - c)
       | None -> false) ->
    Some { obj = true; num = true; store = `Length; framed = no_frame; apart = false; cell_write = false }
  | Call ({node=Id f;_},None,args,[],_) when List.for_all (heap_free env) args ->
    if !call_element_write env f then Some { element_changes with framed = (fun b g -> slot_binding env b && !view_field env b g) }
    else Option.map (of_footprint env) (!call_footprint env f)
  | Invoke ({node=Read (r,key);_},args,[],_) when heap_free env r && List.for_all (heap_free env) args ->
    if !method_grows env r key then Some { obj = false; num = false; store = `Grow; framed = no_frame; apart = false; cell_write = false }
    else if !method_element_write env r key then Some { element_changes with framed = (fun b g -> slot_binding env b && !view_field env b g) }
    else Option.map (of_footprint env) (!method_footprint env r key args)
  | _ -> object_changes env e

let statement_changes ~facts ~bounds env (s : stmt) = match s.statement with
  | Effect e -> (match write_changes ~facts ~bounds env e with
    | Some ch -> Some ch
    | None -> object_changes env e)
  | Declare (_,bs) -> List.fold_left (fun acc (_,_,e) -> match acc, object_calls env e with
      | Some a, Some b -> Some {Semantic.on_value=Semantic.join_change a.Semantic.on_value b.Semantic.on_value;
          on_store=Semantic.join_change a.Semantic.on_store b.Semantic.on_store}
      | _ -> None) (Some Semantic.empty_footprint) bs |> Option.map (of_footprint env)
  | Return e -> object_changes env e
  | _ -> None

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

(* A string's length plus one (Lean's sum rule `int-sum-past`: the exact
   sum, or the double 2^53, `IndexFact.pastSafe`), as a construction's actual
   reads it: one operand a string's length or a binding the facts state
   equal to one, the other the literal 1. *)
let linear_or_past ~array env fs (e : expr) = match linear ~array env fs e with
  | Some f -> Some f
  | None -> (match e.node with
    | Arith (Add,a,b) ->
      let is_length n = (let _,_,k = term_parts n in k = Str_length_term) ||
        List.exists (fun ((t,d) : fact) -> d = 0 && match t with
          | [(x,1);(l,-1)] | [(l,-1);(x,1)] when x = n ->
            let _,_,k = term_parts l in k = Str_length_term && List.mem (norm [x,-1;l,1],0) fs
          | _ -> false) fs in
      (match linear ~array env fs a, linear ~array env fs b with
       | Some ([n,1],0),Some ([],1) | Some ([],1),Some ([n,1],0) when is_length n -> Some ([n,1],1)
       | _ -> None)
    | _ -> None)

(* Index facts at a call's positions restated over bindings, `name p` the
   binding the position `p` holds; a fact naming a position no binding holds
   is left out. *)
let of_index_facts (name : int -> string option) (fs : Semantic.index_fact list) : fact list =
  List.filter_map (fun (fact : Semantic.index_fact) -> match fact with
    | Semantic.Int_at k -> Option.map int_fact (name k)
    | Semantic.Linear_le (form,d) ->
      let terms = List.map (fun (t,c) -> match (t : Semantic.term) with
        | Semantic.Value_at (x,path) -> Option.map (fun n -> path_term n path,c) (name x)
        | Semantic.Length_at (x,path) -> Option.map (fun n -> length_term ~path n,c) (name x)
        | Semantic.View_at (x,path) -> Option.map (fun n -> view_term ~path n,c) (name x)
        | Semantic.Str_length_at (x,path) -> Option.map (fun n -> str_length_term ~path n,c) (name x)) form in
      if List.for_all Option.is_some terms then Some (norm (List.filter_map Fun.id terms),d) else None
    | _ -> None) fs

(* The facts every signature of the binding `f` states of its result, at
   position 0 alone (Lean's `call-ensures`), set by the statement analysis. *)
let call_ensures : ((string * Environment.binding) list -> string -> Semantic.index_fact list) ref =
  ref (fun _ _ -> [])

(* The construct signatures of the binding `c`, in order, set by the
   statement analysis. *)
let ctor_signatures : ((string * Environment.binding) list -> string -> Semantic.signature list) ref =
  ref (fun _ _ -> [])

(* The postcondition of `new c(args)` bound to `name`: that of the first
   construct signature, in order, that states no precondition or one the
   facts establish of the actuals (as Lean's search admits it, `call-requires`),
   its positions 0 the result and `i + 2` the `i`-th actual, each actual a
   linear expression. A fact naming another position is left out. *)
let construct_ensures ~array env fs name c (args : expr list) : fact list =
  let form p = if p >= 1 then Option.bind (List.nth_opt args (p - 1)) (linear_or_past ~array env fs) else None in
  let rec holds = function
    | Semantic.Int_at k -> Option.is_some (form k)
    (* A safe integer meets the left side; the right, the double 2^53, is the
       case Lean's sum rule adds where the actual's bound reaches it. *)
    | Semantic.Either (a,Semantic.Past_safe _) -> holds a
    | Semantic.Linear_le (f,d) ->
      let parts = List.map (fun (t,c) -> match (t : Semantic.term) with
        | Semantic.Value_at (x,[]) -> Option.map (fun (t,k) -> scale c t, c * k) (form x)
        | _ -> None) f in
      List.for_all Option.is_some parts &&
      (let parts = List.filter_map Fun.id parts in
       let terms = norm (List.concat_map fst parts) in
       let constant = List.fold_left (fun acc (_,k) -> acc + k) 0 parts in
       terms = [] && constant <= d || entails (fs @ term_ranges ((terms,0) :: fs)) (terms, d - constant))
    | _ -> false in
  let plain (s : Semantic.signature) = s.Semantic.call_effect.Semantic.promise = None && s.Semantic.call_effect.Semantic.requires = None &&
    s.Semantic.call_effect.Semantic.pre = [] in
  match List.find_opt (fun (s : Semantic.signature) -> List.length args <= List.length s.Semantic.params &&
      (plain s || s.Semantic.call_effect.Semantic.promise = None && s.Semantic.call_effect.Semantic.requires = None && List.for_all holds s.Semantic.call_effect.Semantic.pre))
      (!ctor_signatures env c) with
  | None -> []
  | Some s -> List.filter_map (fun (fact : Semantic.index_fact) -> match fact with
    | Semantic.Linear_le (f,d) ->
      let parts = List.map (fun (t,k) -> match (t : Semantic.term) with
        | Semantic.Value_at (0,path) -> Some ([path_term name path,k],0)
        | Semantic.Length_at (0,path) -> Some ([length_term ~path name,k],0)
        | Semantic.View_at (0,path) -> Some ([view_term ~path name,k],0)
        | Semantic.Str_length_at (0,path) -> Some ([str_length_term ~path name,k],0)
        | Semantic.Value_at (p,[]) when p >= 2 -> Option.map (fun (t,c) -> scale k t, k * c) (form (p - 1))
        | _ -> None) f in
      if List.for_all Option.is_some parts then
        let parts = List.filter_map Fun.id parts in
        Some (norm (List.concat_map fst parts), d - List.fold_left (fun acc (_,c) -> acc + c) 0 parts)
      else None
    | _ -> None) s.Semantic.call_effect.Semantic.ensures

(* Whether an expression reads the binding `x`. *)
let rec mentions_id x (e : expr) = match e.node with
  | Id y -> y = x
  | _ -> List.exists (mentions_id x) (Source.children e)

(* The signatures of a receiver's method, set by the statement analysis. *)
let method_signatures : ((string * Environment.binding) list -> expr -> Semantic.key -> expr list -> Semantic.signature list) ref =
  ref (fun _ _ _ _ -> [])

(* A term at a call's position over bindings: the actual there as a linear
   expression, for a value term with no path, else as a path, with the
   term's path after it. *)
let position_form ~array env fs (actual : expr option) (t : Semantic.term) =
  let at q kind = Option.bind actual (fun e -> Option.map (fun (b,p) -> [make_term ~path:(p @ q) kind b,1],0) (path_of env e)) in
  match t with
  | Semantic.Value_at (_,[]) -> Option.bind actual (linear ~array env fs)
  | Semantic.Value_at (_,q) -> at q Value_term
  | Semantic.Length_at (_,[]) when Option.fold ~none:false ~some:(fun (e : expr) -> match e.node with ArrayLiteral (_,[]) -> true | _ -> false) actual ->
    Option.bind actual (fun (e : expr) -> match e.node with ArrayLiteral (es,[]) -> Some ([],List.length es) | _ -> None)
  | Semantic.Length_at (_,q) -> at q Length_term
  | Semantic.View_at (_,q) -> at q View_term
  | Semantic.Str_length_at (_,q) -> at q Str_length_term

let term_position (t : Semantic.term) = match t with
  | Semantic.Value_at (p,_) | Semantic.Length_at (p,_) | Semantic.View_at (p,_) | Semantic.Str_length_at (p,_) -> p

(* The postcondition of `r.m(args)` bound to `name` (Lean's `call-ensures`):
   that of the first of the method's signatures stating a precondition the
   facts establish of the receiver and the actuals (positions 0 the
   receiver, `i + 1` the `i`-th actual, as `call-requires` reads them), or,
   where none does, of the first compatible signature stating none.
   Its positions are 0 the result, 1 the receiver and `i + 2` the `i`-th
   actual. A fact naming a position no term reads is left out. *)
let method_ensures ~array env fs name (recv : expr) key (args : expr list) : fact list =
  let sigs = !method_signatures env recv key args in
  let combine form parts = List.map (fun (t,c) -> Option.map (fun (t',k) -> scale c t', c * k) (form t)) parts in
  let sum parts = let parts = List.filter_map Fun.id parts in
    norm (List.concat_map fst parts), List.fold_left (fun acc (_,k) -> acc + k) 0 parts in
  let pre_actual p = if p = 0 then Some recv else List.nth_opt args (p - 1) in
  let holds = function
    | Semantic.Int_at k -> Option.bind (pre_actual k) (linear ~array env fs) <> None
    | Semantic.Linear_le (f,d) ->
      let parts = combine (fun t -> position_form ~array env fs (pre_actual (term_position t)) t) f in
      List.for_all Option.is_some parts &&
      (let terms,constant = sum parts in
       terms = [] && constant <= d || entails (fs @ term_ranges ((terms,0) :: fs)) (terms, d - constant))
    | _ -> false in
  let plain (s : Semantic.signature) = s.Semantic.call_effect.Semantic.pre = [] in
  let chosen = match List.find_opt (fun (s : Semantic.signature) -> not (plain s) &&
      s.Semantic.call_effect.Semantic.promise = None && List.for_all holds s.Semantic.call_effect.Semantic.pre) sigs with
    | Some s -> Some s.Semantic.call_effect.Semantic.ensures
    | None -> Option.map (fun (s : Semantic.signature) -> s.Semantic.call_effect.Semantic.ensures)
        (List.find_opt plain sigs) in
  let post_actual p = if p = 1 then Some recv else List.nth_opt args (p - 2) in
  match chosen with
  | None -> []
  | Some ensures -> List.filter_map (fun (fact : Semantic.index_fact) -> match fact with
    | Semantic.Int_at 0 -> Some (int_fact name)
    | Semantic.Linear_le (f,d) ->
      let parts = combine (fun t -> match t with
        | Semantic.Value_at (0,path) -> Some ([path_term name path,1],0)
        | Semantic.Length_at (0,path) -> Some ([length_term ~path name,1],0)
        | Semantic.View_at (0,path) -> Some ([view_term ~path name,1],0)
        | Semantic.Str_length_at (0,path) -> Some ([str_length_term ~path name,1],0)
        | t -> position_form ~array env fs (post_actual (term_position t)) t) f in
      if List.for_all Option.is_some parts then
        let terms,constant = sum parts in Some (terms, d - constant)
      else None
    | _ -> None) ensures

(* The facts the signatures of the binding `f` state at a call's normal
   return (Lean's `call-ensures`), over bindings: position `0` the result
   `name`, where one is bound, and `i + 2` the `i`-th actual, where it is a
   value binding; a fact naming another position is left out. *)
let call_facts ?name env f (args : expr list) : fact list =
  of_index_facts (fun p ->
    if p = 0 then name
    else if p >= 2 then (match List.nth_opt args (p - 2) with
      | Some {node=Id a;_} when value_binding env a -> Some a
      | _ -> None)
    else None) (!call_ensures env f)

(* A numeric result identified with an actual by both postcondition bounds.
   This is proposal only; the call's postcondition is checked at every edge. *)
let rec result_form ~array env fs (e : expr) =
  match linear ~array env fs e with
  | Some f -> Some f
  | None -> (match e.node with
    | Call ({node=Id f;_},None,args,[],_) ->
      let ensures = !call_ensures env f in
      List.find_map (fun (p,a) ->
        let r = Semantic.Value_at (0,[]) and x = Semantic.Value_at (p + 2,[]) in
        if List.mem (Semantic.Linear_le ([r,1;x,-1],0)) ensures &&
           List.mem (Semantic.Linear_le ([r,-1;x,1],0)) ensures then
          result_form ~array env fs a else None) (List.mapi (fun p a -> p,a) args)
    | _ -> None)

let call_expression_facts ~array env fs name f args =
  List.filter_map (function
    | Semantic.Int_at 0 -> Some (int_fact name)
    | Semantic.Linear_le (form,d) ->
      let parts = List.map (fun (t,c) ->
        let value = match t with
          | Semantic.Value_at (0,p) -> Some ([path_term name p,1],0)
          | Semantic.Length_at (0,p) -> Some ([length_term ~path:p name,1],0)
          | Semantic.View_at (0,p) -> Some ([view_term ~path:p name,1],0)
          | Semantic.Str_length_at (0,p) -> Some ([str_length_term ~path:p name,1],0)
          | Semantic.Value_at (p,[]) when p >= 2 ->
            Option.bind (List.nth_opt args (p - 2)) (result_form ~array env fs)
          | _ when term_position t >= 2 -> position_form ~array env fs (List.nth_opt args (term_position t - 2)) t
          | _ -> None in
        Option.map (fun (f,k) -> scale c f,c*k) value) form in
      if List.for_all Option.is_some parts then
        let parts = List.filter_map Fun.id parts in
        Some (norm (List.concat_map fst parts),d - List.fold_left (fun k (_,n) -> k+n) 0 parts)
      else None
    | _ -> None) (!call_ensures env f)

(* The facts a test's call states at its normal return, `f(…)` or `!f(…)`. *)
let rec test_call_facts ?(held = []) env (c : expr) : fact list = match c.node with
  | Call ({node=Id f;_},None,args,[],_) | Not {node=Call ({node=Id f;_},None,args,[],_);_} -> call_facts env f args
  (* `a && f(…)` or `a || f(…)`, `a` writing no heap: where `f` runs, its
     facts hold after it; where it does not, the heap is the test's entry
     one. So each of `f`'s facts the entry's facts (`held`) entail holds on
     either answer, as Lean's merge of the two paths keeps it. *)
  | Logical (_,a,b) when heap_free env a ->
    List.filter (fun f -> entails held f) (test_call_facts ~held env b)
  | _ -> []

(* The postcondition past the guard excluded by the call's Boolean answer. *)
let rec test_conditional_facts env (c : expr) answer : fact list = match c.node with
  | Not c -> test_conditional_facts env c (not answer)
  | Call ({node=Id f;_},None,args,[],_) ->
    let facts = List.filter_map (function
      | Semantic.Guarded (0,[],tag,body) when tag = (if answer then "false" else "true") -> Some body
      | _ -> None) (!call_ensures env f) in
    of_index_facts (fun p -> if p >= 2 then match List.nth_opt args (p - 2) with
      | Some {node=Id a;_} when value_binding env a -> Some a
      | _ -> None else None) facts
  | _ -> []

(* The facts after the updates an expression makes of bindings held in
   cells (ARITHMETIC.md, "Terms for bindings held in cells"): Lean reads
   the cell's `value` into a slot, the old value, computes the new one, and
   writes it back, a number field's write that its read link restates. So
   each updated binding's facts are restated of its old value, the write's
   change applied (a number's: every cell's term goes), and the new value
   stated the old one plus the step, the old one then eliminated. A binding
   updated twice, read elsewhere in the expression, or by a step no literal
   gives is forgotten. *)
let after_cell_updates ?(root=true) env (e : expr) (fs : fact list) : fact list =
  (* Each child, and whether it runs wherever its parent does: the right
     operand of a short circuit, an arm and a default run only on a path. *)
  let sure_children (e : expr) = match e.node with
    | Logical (_,a,b) | Coalesce (a,b) | Optional (a,b) | LogicalAssign (_,a,b) -> [a,true; b,false]
    | Conditional (a,b,c) -> [a,true; b,false; c,false]
    | NullishAssign (_,_,b) -> [b,false]
    | ArrayAssign (targets,rest,rhs) ->
      (rhs,true) :: List.concat_map (fun (_,t,d) -> (t,true) :: List.map (fun d -> d,false) (Option.to_list d)) targets
      @ (match rest with Some (_,_,t,_) -> [t,true] | None -> [])
    | _ -> List.map (fun c -> c,true) (Source.children e) in
  (* An update on only some paths leaves the binding unknown. *)
  let rec updates ~nested ~sure (e : expr) acc =
    if (match e.node with Lambda _ -> true | _ -> false) then acc else
    let held x = !cell_terms x || (nested && slot_binding env x) in
    let acc = match e.node with
      | Update ((Add | Sub) as op,{node=Id x;_},rhs,_) when held x -> (x,if sure then cell_step op rhs else None) :: acc
      | Assign (x,_,_) when held x -> (x,None) :: acc
      | _ -> acc in
    List.fold_left (fun acc (c,s) -> updates ~nested:true ~sure:(sure && s) c acc) acc (sure_children e) in
  let updates e acc = updates ~nested:root ~sure:true e acc in
  let rec mentions_id x (e : expr) =
    (match e.node with Id y | Assign (y,_,_) -> if y = x then 1 else 0 | _ -> 0) +
    List.fold_left (fun n c -> n + mentions_id x c) 0 (Source.children e) in
  match updates e [] with
  | [] -> fs
  | ups ->
    (* A slot's update writes no heap location; a cell's is a number
       field's write. *)
    let cells = List.exists (fun (x,_) -> !cell_terms x) ups in
    let change = { obj = false; num = true; store = `Keep; framed = no_frame; apart = false; cell_write = true } in
    let renamed x old t = let b,path,kind = term_parts t in if b = x then make_term ~path kind old else t in
    let steps = List.map (fun (x,d) -> x, (if mentions_id x e = 1 then d else None), "%old" ^ x) ups in
    let fs = List.fold_left (fun fs (x,_,old) ->
      List.map (fun ((t,b) as f : fact) -> let t' = List.map (fun (n,c) -> renamed x old n,c) t in
        (if is_int_fact f then t' else norm t'), b) fs) fs steps in
    let position n = let rec go i = function [] -> None | (m,_) :: t -> if m = n then Some i else go (i+1) t in go 0 env in
    let older b = value_binding env b && not (!cell_terms b) && match position b with
      | Some p -> List.for_all (fun (x,_) -> match position x with Some q -> p < q | None -> false) ups
      | None -> false in
    let saved = !older_than_written in
    older_than_written := older;
    let fs = if not cells then fs else Fun.protect ~finally:(fun () -> older_than_written := saved) (fun () ->
      List.filter (fun f -> fact_kept change f || stable_fact env f) fs) in
    List.fold_left (fun fs (x,d,old) -> match d with
      | Some d when is_int fs old && safe fs ([old,1],d) -> forget old (fs @ equal x ([old,1],d))
      | _ -> forget old fs) fs steps

(* The store regions every signature of the module function `f` states,
   each a call position and a path, and its frame's closed bound; none for a
   binding of the body. Set by the statement analysis. *)
let call_regions : ((string * Environment.binding) list -> string -> ((int * string list) list * Semantic.footprint) option) ref =
  ref (fun _ _ -> None)

(* Where a statement is a call of a function stating store regions whose
   closed bound keeps every store, the arrays whose store the call keeps
   (Lean's `regionFirst`): a value binding separated from the store each
   region selects at the call, by a region fact with the actual of a
   region's own store, or by a store separation with the region's path at
   the actual. *)
let region_separated ?(regions=[]) ?(stores=[]) env (s : stmt) : (string -> bool) option =
  match s.statement with
  | Effect {node=Call ({node=Id f;_},None,args,[],_);_} when List.for_all (heap_free env) args ->
    (match !call_regions env f with
     | Some (rs,closed) when rs <> [] &&
         (match closed.Semantic.on_store with Semantic.Keep | Semantic.Init | Semantic.Scalar -> true | _ -> false) ->
       let stores = List.map sfact_norm stores in
       Some (fun y -> slot_binding env y && List.for_all (fun (p,q) -> p >= 1 &&
         match List.nth_opt args (p - 1) with
         | Some {node=Id a;_} -> (q = [] && rapart regions a y) || List.mem (sfact_norm ((a,q),(y,[]))) stores
         | _ -> false) rs)
     | _ -> None)
  | _ -> None

(* A statement's effect on the facts: an assignment or update of a slot
   binding by a linear expression, and every other assigned binding
   forgotten. *)
let rec statement ~(array : string -> string list -> bool) ?(bounds=[]) ?(regions=[]) ?(stores=[]) env fs (s : stmt) : fact list =
  match s.statement with
  (* `i++;` of a binding held in a cell: its read, step and write. *)
  | Effect ({node=Update (_,{node=Id x;_},None,_);_} as e) when !cell_terms x -> after_cell_updates env e fs
  (* `a, b` (a loop's update `j = k, k = s.charCodeAt(i), i++`): `a`'s
     statement, then `b`'s, as Lean's steps run them in turn. *)
  | Effect {node=Comma (a,b);_} ->
    statement ~array ~bounds env (statement ~array ~bounds env fs {s with statement=Effect a}) {s with statement=Effect b}
  (* A statement updating a cell inside it (`s += xs[at++]!`): the update's
     facts, then the statement as one writing no other location. *)
  | Effect e ->
    let updated = after_cell_updates ~root:false env e fs in
    if updated == fs then statement_slots ~array ~bounds ~regions ~stores env fs s
    else with_cells true (fun () -> statement_slots ~array ~bounds env updated s)
  | _ -> statement_slots ~array ~bounds ~regions ~stores env fs s
and statement_slots ~(array : string -> string list -> bool) ?(bounds=[]) ?(regions=[]) ?(stores=[]) env fs (s : stmt) : fact list =
  (* A write `x.f = e` of a field the receiver's type states, of a value
     binding, by a linear expression: the field's new value is `e`'s, read through the old value where `e`
     reads it (Lean's `write-link`, a read link from `x.f` to the written
     slot). The old value is renamed apart before the write's change and
     eliminated after. *)
  let old = "%written" in
  let written = match s.statement with
    | Effect {node=Write (({node=Id x;_} as recv),(Semantic.Name f as key),rhs);_}
      when slot_binding env x && heap_free env rhs && !field_classes env recv key <> None ->
      Option.map (fun form -> path_term x [f], form) (linear ~array env fs rhs)
    | _ -> None in
  let fs = match written with
    | Some (p,_) -> List.map (fun ((t,d) : fact) -> List.map (fun (n,c) -> (if n = p then old else n),c) t, d) fs
    | None -> fs in
  (* A fact naming a length or a typed-array length reads the heap: kept where
     the statement writes none, as Lean keeps it (`IndexFact.envOnly`). *)
  (* Whether an expression reads the binding `x`. *)
  let rec reads x (e : expr) = match e.node with
    | Id n -> n = x
    | _ -> List.exists (reads x) (Source.children e) in
  let appended = match s.statement with
    | Effect {node=Invoke ({node=Read (({node=Id x;_} as r),key);_},args,[],_);_}
        when !method_grows env r key && List.for_all (heap_free env) args
          && not (List.exists (reads x) args) ->
      let length = length_term x in
      let ch = { obj=false; num=false; store=`Grow; framed=no_frame; apart=false; cell_write=false } in
      (* The length of an array a region fact keeps apart from the
         receiver's, whose store cell the growth keeps (Lean's `growFirst`). *)
      let region_kept t = let b,path,kind = term_parts t in
        path = [] && kind = Length_term && rapart regions x b in
      List.filter_map (fun ((form,d) : fact) ->
        if List.for_all (fun (t,_) -> t = length || term_kept ch t || region_kept t) form then
          Some (form, d + List.fold_left (fun acc (t,c) ->
            if t = length then acc + c * List.length args else acc) 0 form)
        else None) (fs @ term_ranges fs)
    | _ -> [] in
  (* Across a call of a function stating store regions, each fact whose
     lengths are of arrays the call keeps (`region-call-keep`). *)
  let separated = match region_separated ~regions ~stores env s with
    | Some sep -> List.filter (fun ((t,_) : fact) -> List.for_all (fun (n,_) -> stable_term env n ||
        (let b,path,kind = term_parts n in kind = Length_term && path = [] && sep b)) t) fs
    | None -> [] in
  let fs = if statement_heap_free env s then fs else match statement_changes ~facts:fs ~bounds env s with
    | Some ch -> List.filter (fun f -> fact_kept ch f || stable_fact env f) fs
    | None -> keep_stable env fs in
  let fs = List.sort_uniq compare (fs @ separated) @ appended in
  let fs = match written with
    | Some (p,(t,c)) ->
      let t = List.map (fun (n,k) -> (if n = p then old else n),k) t in
      forget old (fs @ [norm ((p,1) :: scale (-1) t), c; norm ((p,-1) :: t), -c])
    | None -> fs in
  match s.statement with
  (* `x = r.m(…)`, or its non-null assertion, of a method stating a
     postcondition, `x` read by neither: each of its facts, of `x`. *)
  | Effect {node=Assign (x,_,({node=(Invoke ({node=Read (r,key);_},args,[],_)
      | Cast ("nonNull",_,{node=Invoke ({node=Read (r,key);_},args,[],_);_}));_} as e));_}
    when value_binding env x && not (mentions_id x e) ->
    forget x fs @ method_ensures ~array env fs x r key args
  | Effect {node=Assign (x,_,e);_} -> assign ~array env fs x e
  | Effect {node=Update ((Add | Sub) as op,({node=Id x;_} as target),rhs,_);pos} ->
    let one = {node=Literal (LNumber "1"); pos} in
    let r = match rhs with Some r -> r | None -> one in
    assign ~array env fs x {node=Arith (op,target,r); pos}
  | Effect {node=Call ({node=Id f;_},None,args,[],_);_} ->
    List.fold_left (fun fs x -> forget x fs) fs (names_assigned s env) @ call_facts env f args
  | Destructure _ ->
    let fs = List.fold_left (fun fs x -> forget x fs) fs (names_assigned s env) in
    (* Each field's read restated of the name it is bound to, in the
       pattern's order, each over the facts the earlier ones restated, as
       the declarations `const n = root.path.f` one after another restate
       them: a fact naming two of the fields is restated of both names. *)
    (match destructure_reads env s with
     | Some ((root,path),fields) ->
       let fs = List.fold_left (fun fs (_,n) -> forget n fs) fs fields in
       List.fold_left (fun fs (f,n) -> fs @ restate_read n (root,path @ [f]) fs) fs fields
     | None -> fs)
  | _ -> List.fold_left (fun fs x -> forget x fs) fs (names_assigned s env)

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
     tag test in Lean's lowering (`numEq`), whose answers state the same
     (`HeapKnowledge.numEqIndices`). *)
  | Equality ((StrictEqual | StrictUnequal) as op,a,b) ->
    (match linear ~array env fs a, linear ~array env fs b with
     | Some (ta,ca),Some (tb,cb) ->
       let d = norm (ta @ scale (-1) tb) and c = ca - cb in
       let equal = [d,-c; scale (-1) d,c] in
       let ranged = fs @ term_ranges fs in
       let unequal = (if entails ranged (d,-c) then [d,-c-1] else []) @
         (if entails ranged (scale (-1) d,c) then [scale (-1) d,c-1] else []) in
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
let statement_bounds ?(facts=[]) ?(regions=[]) ?(stores=[]) env (bs : bound list) (s : stmt) =
  let kept = statement_heap_free env s ||
    (match statement_changes ~facts ~bounds:bs env s with Some ch -> ch.store <> `Any | None -> false) in
  let assigned = names_assigned s env in
  let unassigned (a,i,_) = not (List.mem a assigned) && not (List.mem i assigned) in
  if kept then List.filter unassigned bs else
  (* Across a call of a function stating store regions, the bounds of the
     arrays it keeps (`region-call-keep`). *)
  match region_separated ~regions ~stores env s with
  | Some sep -> List.filter (fun ((a,_,_) as b) -> unassigned b && sep a) bs
  | None -> []

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

(* The true branch of `j < xs.length`, with `0 ≤ j` known: `j` is at most
   `2^32 - 2`, which Lean derives from the length's range. *)
let atom_length_test ~array env fs (cond : expr) =
  match atom_bounds ~array env fs cond with
  | [_,j,_],_ -> [[j,1],max_index]
  | _ -> []

(* Whether the binding's path holds an array where it is not `null` or
   `undefined`, set by the statement analysis, which reads the type. *)
let array_unless_nullish : ((string * Environment.binding) list -> string -> string list -> bool) ref =
  ref (fun _ _ _ -> false)

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
    (* The other answer: `a`'s own, where `b` is not evaluated, or `b`'s
       after `a`'s other answer; Lean merges the two paths, so each fact
       both entail holds, and each bound both state. *)
    let either (sa,ba) (sb,bb) =
      List.filter (fun f -> entails (fs @ sa) f && entails (fs @ left @ sb) f) (sa @ left @ sb),
      List.filter (fun x -> List.mem x bb) ba in
    if conjunction then (left @ tb, left_bounds @ btb),either (fa,bfa) (fb,bfb)
    else either (ta,bta) (tb,btb),(left @ fb, left_bounds @ bfb)
  | _ ->
    let t,f = atom_comparison ~array env fs cond and bt,bf = atom_bounds ~array env fs cond in
    (t @ atom_length_test ~array env fs cond, bt),(f,bf)

let comparison ~array env fs cond = let (t,_),(f,_) = test ~array env fs cond in t,f
let comparison_bounds ~array env fs cond = let (_,t),(_,f) = test ~array env fs cond in t,f

(* At a merge, a fact of one form holds at the larger bound where both
   paths bound it. A bound larger than the one the earlier state (`l`, the
   state the flow solver joins into) held is raised at once to `0` where it
   is at most that and the earlier one is negative, otherwise to `2^32 - 1`,
   the largest length, or `2^53 - 1`, the largest safe integer, where it is
   at most that, and forgotten otherwise, so each form changes at most four
   times and a loop settles as it would without facts. *)
let join ?(keep = true) (l : fact list) (r : fact list) : fact list =
  let l = tighten l and r = tighten r in
  (* Each path's bound of a form: the least of the bounds either path
     states, `0` and the largest length that its facts, with the ranges of
     the lengths and typed-array lengths they name, entail, where its facts name
     every length, typed-array length and path the form does and state each
     binding it names a safe integer, as Lean requires of an edge's source
     (`linearFollows`). So a loop's entry, `i = 0`, and its iteration's
     `i - xs.length ≤ -1` keep `i ≤ 2^32 - 1` where the iteration bounds
     `i` by the length. *)
  let defines side ((t,_) : fact) = List.for_all (fun (n,_) ->
    if not (slot_value n) then List.exists (fun ((t',_) : fact) -> List.mem_assoc n t') side
    else List.mem ([n,0],0) side) t in
  (* The earlier state (`l`) keeps a bound it states, so the join is never
     stronger than it and a loop settles; the later state, and an earlier one
     not stating the form, are read at the least candidate their facts
     entail. Two arms of one test (`keep` false) are both read so. *)
  let bound ?(keep = false) side candidates ((t,_) as f : fact) =
    match List.assoc_opt t side with
    | Some d when keep -> Some d
    | _ ->
    if not (defines side f) then None else
    let side' = side @ term_ranges side in
    List.find_opt (fun b -> List.mem (t,b) side || entails side' (t,b)) candidates in
  let forms = List.sort_uniq compare (List.map fst l @ List.map fst r) in
  List.filter_map (fun t ->
    let dl = List.assoc_opt t l and dr = List.assoc_opt t r in
    if is_int_fact (t,0) then (match dl,dr with Some d,Some _ -> Some (t,d) | _ -> None) else
    let candidates = List.sort_uniq compare (List.filter_map Fun.id [dl; dr] @ [0; max_index + 1; max_safe]) in
    match bound ~keep l candidates (t,0), bound r candidates (t,0) with
    | Some d, Some d' when d' <= d -> Some (t,d)
    | Some d, Some d' when d' <= 0 && d < 0 -> Some (t, 0)
    | Some d, Some d' when d' <= max_index + 1 && d < max_index + 1 -> Some (t, max_index + 1)
    | Some d, Some d' when d' <= max_safe && d < max_safe -> Some (t, max_safe)
    | _ -> None) forms
  (* A binding's own safe-integer range, which the knowledge states of each
     safe integer it names (`HeapKnowledge.valueRange`), is not restated. *)
  |> fun fs -> List.filter (fun ((t,d) : fact) -> match t with
    | [x,(1 | -1)] when slot_value x && d >= max_safe -> not (List.mem ([x,0],0) fs)
    | _ -> true) fs

let () = assign_arms := (fun ~array env fs x c p q ->
  let t,f = comparison ~array env fs c in
  let l = assign ~array env (fs @ t) x p and r = assign ~array env (fs @ f) x q in
  (* The facts of each arm joined, neither arm the earlier state, beside
     those naming no `x`, which neither arm changes. *)
  let fs' = forget x fs in
  Some (fs' @ List.filter (fun f -> not (List.mem f fs')) (join ~keep:false l r)))

let rec declaration ~(array : string -> string list -> bool) env fs name (init : expr) : fact list =
  (* An initializer updating a cell (`xs[at++]!`): the update's facts, then
     the initializer as one writing no other location. *)
  let updated = after_cell_updates env init fs in
  with_cells (updated != fs) @@ fun () ->
  let fs = updated in
  let fs = if heap_free env init then fs
    else match object_changes env init with
      | Some ch -> List.filter (fun f -> fact_kept ch f || stable_fact env f) fs
      | None -> keep_stable env fs in
  let fs = forget name fs in
  (* `const x = f(…)` of a function stating a postcondition: each of
     its facts, of `x`. *)
  let fs = fs @ concat_facts env name init in
  let fs = match init.node with
    | ArrayLiteral (es,[]) -> fs @ [[length_term name,1],List.length es; [length_term name,-1],-(List.length es)]
    | Call ({node=Id f;_},None,args,[],_) -> fs @ call_expression_facts ~array env fs name f args
    (* `const x = new c(…)` at a construct signature stating facts of its
       result: each of them, of `x`, over the actuals. *)
    | New ({node=Id c;_},_,args,[]) -> fs @ construct_ensures ~array env fs name c args
    (* `const x = r.m(…)`, or its non-null assertion, of a method stating a
       postcondition: each of its facts, of `x`. *)
    | Invoke ({node=Read (r,key);_},args,[],_)
    | Cast ("nonNull",_,{node=Invoke ({node=Read (r,key);_},args,[],_);_}) ->
      fs @ method_ensures ~array env fs name r key args
    (* `const x = { f: e, … }`: each named field's value, a linear
       expression, is the path's (Lean's `freshLinks`, a read link from each
       field of the allocated object to its initializer's slot). *)
    | Alloc fields ->
      fs @ List.concat_map (fun (key,(e : expr)) -> match key with
        | Semantic.Name f -> (match linear ~array env fs e with
          | Some (t,c) -> let p = path_term name [f] in [norm ((p,1) :: scale (-1) t), c; norm ((p,-1) :: t), -c]
          | None -> [])
        | _ -> []) fields
    | _ -> fs in
  (* A type assertion's value is its operand's (`const internal = prepared
     as Internal`): the binding aliases the operand, as Lean's cast node
     transfers the slot. *)
  let rec uncast (e : expr) = match e.node with
    | Cast (("as" | "satisfies" | "nonNull"),_,a) -> uncast a
    | _ -> e in
  let fs = match path_of env (uncast init) with
    | Some (root,(_ :: _ as path)) when root <> name && heap_free env init -> fs @ restate_read name (root,path) fs
    | Some (root,[]) when root <> name && init != uncast init -> fs @ restate_read name (root,[]) fs
    | _ -> fs in
  let init = match distribute init with
    | Some (c,p,q) -> {init with node=Conditional (c,p,q)}
    | None -> init in
  match init.node with
  (* `const x = c ? a : b`: on each arm, what the arm's answer of `c` states
     and `x` the arm's value, the two joined (Lean's branch on `c`, each arm
     binding its value, merged at the declaration's end). *)
  | Conditional (c,a,b) ->
    let t,f = comparison ~array env fs c in
    let arm answer (e : expr) = match linear ~array env (fs @ answer) e with
      | Some (te,ce) when not (List.mem_assoc name te) -> Some (fs @ answer @ equal name (te,ce))
      (* An arm stating facts of its value as a declaration does, a call
         stating a postcondition say: those facts. *)
      | _ -> let d = declaration ~array env (fs @ answer) name e in
        if List.exists (mentions name) d then Some d else None in
    (match arm t a, arm f b with
     | Some l, Some r -> List.filter (fun f -> mentions name f) (join l r) @ fs
     | _ -> fs)
  | _ ->
  match linear ~array env fs init with
  | Some (t,c) when not (List.mem_assoc name t) -> fs @ equal name (t,c)
  | _ -> fs @ bitwise_facts ~array env fs name init

(* Widening preserves the facts that did not change. *)

let () = assign_declared := (fun ~array env fs x e -> declaration ~array env fs x e)

let widen (previous : fact list) (current : fact list) =
  let previous = tighten previous in
  List.filter (fun (t,d) -> match List.assoc_opt t previous with
    | Some d' -> d <= d'
    | None -> false) (tighten current)

(* Guarded facts across a step (ARITHMETIC.md, "Guarded clauses"), as
   Lean keeps them: a step writing no heap keeps each; one writing it keeps
   those whose guards read slots alone and whose fact the step keeps
   (`IndexFact.keptBy`), here the stable ones or those `ch` keeps. *)
let gkept ?ch env (gs : gfact list) =
  List.filter (fun ((guards,f) : gfact) -> List.for_all (fun (_,p,_) -> p = []) guards &&
    (stable_fact env f || match ch with Some ch -> fact_kept ch f | None -> false)) gs

(* The guarded facts restated where a binding is declared at a path's read
   (`const b = p.f`), as `restate_read` restates facts: each guard's path and
   each term extending the read path restated of the binding, as Lean's
   read link restates a guard's path (`liftGuard`) and a term. *)
let grestate_read name (root,path) (gs : gfact list) : gfact list =
  let rec prefix p q = match p,q with
    | [],rest -> Some rest
    | f :: p,g :: q when f = g -> prefix p q
    | _ -> None in
  let rename t = let b,p,kind = term_parts t in
    if b <> root then None else Option.map (fun rest -> make_term ~path:rest kind name) (prefix path p) in
  let guard (x,p,tag) = if x <> root then None else Option.map (fun rest -> name,rest,tag) (prefix path p) in
  List.filter_map (fun ((guards,(t,d)) : gfact) ->
    if List.exists (fun g -> guard g <> None) guards || List.exists (fun (n,_) -> rename n <> None) t then
      Some (List.map (fun g -> Option.value ~default:g (guard g)) guards,
        (norm (List.map (fun (n,c) -> (match rename n with Some m -> m | None -> n),c) t),d))
    else None) gs

(* What a test's answer excludes of a path: `p === null` answering `false`
   (`!==` answering `true`) excludes `null` of `p`, `undefined` alike, `==`
   both; a truthy answer excludes both; `a && b` answering `true` and `a ||
   b` answering `false` what both operands' answers exclude, in order. *)
let rec excluded env (c : expr) (answer : bool) : (string * string list * string list) list =
  let nullish (e : expr) = match e.node with
    | Literal (LBool true) -> Some ["true"]
    | Literal (LBool false) -> Some ["false"]
    | Literal LNull -> Some ["null"]
    | Literal LUndefined | Id "undefined" -> Some ["undefined"]
    | _ -> None in
  match c.node with
  | Equality (op,a,b) ->
    let operand,tags = match nullish b, nullish a with
      | Some t,_ -> a,t | None,Some t -> b,t | None,None -> a,[] in
    let tags = match op with LooseEqual | LooseUnequal when List.mem "null" tags || List.mem "undefined" tags -> ["null"; "undefined"] | _ -> tags in
    let unequal = match op with StrictUnequal | LooseUnequal -> true | _ -> false in
    (match path_of env operand with
     | Some (x,p) when tags <> [] && unequal = answer -> [x,p,tags]
     | _ -> [])
  | Logical (conjunction,a,b) when conjunction = answer -> excluded env a answer @ excluded env b answer
  | Not a -> excluded env a (not answer)
  | Id _ | Read _ -> (match path_of env c with
    | Some (x,p) -> [x,p,(if answer then ["null"; "undefined"; "false"] else ["true"])] | None -> [])
  | _ -> []

(* Guard elimination (Lean's `unguardIndices`, which keeps the atoms it
   reads): each exclusion in turn adds, of a guarded fact whose first guard
   reads the excluded path with an excluded tag, the fact past that guard; a
   fact left with no guard is a fact. *)
let geliminate exclusions (gs : gfact list) : fact list * gfact list =
  let gs = List.fold_left (fun gs (x,p,tags) -> gs @ List.filter_map (fun ((guards,f) : gfact) -> match guards with
    | (y,q,tag) :: rest when y = x && q = p && List.mem tag tags -> Some (rest,f)
    | _ -> None) gs) gs exclusions in
  List.filter_map (fun ((guards,f) : gfact) -> if guards = [] then Some f else None) gs,
  List.sort_uniq compare (List.filter (fun ((guards,_) : gfact) -> guards <> []) gs)

(* `f ()` with the facts of a call stating a precondition (`current_facts`)
   extended by what the answer `yes` of the test `c` states, and by the
   bodies of the guarded facts (`current_gfacts`) whose guards that answer
   excludes (`geliminate`): an arm of `c ? a : b`. A proposal: Lean
   promotes the test's facts, and frees the guards (`unguardIndices`),
   where it observes its answer. *)
let with_test env (c : expr) yes f =
  let saved = !current_facts and gsaved = !current_gfacts in
  if saved = [] && gsaved = [] then f () else begin
    let array = !array_path env in
    let t,fl = comparison ~array env saved c in
    let freed,gs = geliminate (excluded env c yes) gsaved in
    current_facts := deliminate (saved @ (if yes then t else fl) @ freed @ test_conditional_facts env c yes) !current_dfacts;
    current_gfacts := gs;
    Fun.protect ~finally:(fun () -> current_facts := saved; current_gfacts := gsaved) f
  end

(* What an answer of `a && b` (`a || b`) that `a` alone may give states,
   where `a`'s other answer excludes one tag of a path (`x !== null`): on
   that answer either the path reads the tag's value, or `b` gave it, so
   each fact `b`'s answer states holds guarded by the path's test
   (`guard-introduce`). *)
let gtest ~array env fs (c : expr) answer : gfact list =
  match c.node with
  | Logical (conjunction,a,b) when conjunction <> answer ->
    (match excluded env a conjunction with
     | [(x,p,[tag])] ->
       let (ta,_),(fa,_) = test ~array env fs a in
       (* `b` runs where `a` excludes the tag: an array path's type there
          is its type without `null` or `undefined`. *)
       let array y q = array y q || (y = x && q = p && !array_unless_nullish env x p) in
       let (tb,_),(fb,_) = test ~array env (fs @ (if conjunction then ta else fa)) b in
       List.map (fun f -> [x,p,tag],f) (if conjunction then fb else tb)
     | _ -> [])
  | _ -> []

(* The guarded facts a precondition's index facts state, at a call's
   positions restated over bindings (`of_index_facts`). *)
let rec of_guarded_fact (name : int -> string option) (fact : Semantic.index_fact) : gfact option =
  match fact with
  | Semantic.Guarded (x,path,tag,body) ->
    (match name x with
     | None -> None
     | Some n ->
       let guard = n,path,tag in
       (match body with
        | Semantic.Guarded _ -> Option.map (fun (gs,f) -> guard :: gs,f) (of_guarded_fact name body)
        | _ -> (match of_index_facts name [body] with [f] -> Some ([guard],f) | _ -> None)))
  | _ -> None

let rec of_disjunction name = function
  | Semantic.Either (a,b) -> (match of_disjunction name a,of_disjunction name b with
    | Some a,Some b -> Some (DEither (a,b)) | _ -> None)
  | f -> (match of_index_facts name [f] with [f] -> Some (DAtom f) | _ -> None)
let disjunctions name fs = List.filter_map (function
  | Semantic.Either _ as f -> of_disjunction name f | _ -> None) fs
let dstatement env ds s =
  let assigned = names_assigned s env in
  List.filter (fun d -> not (List.exists (fun b -> List.mem b assigned) (dbindings d)) &&
    (statement_heap_free env s || List.for_all (stable_fact env) (datoms d))) ds

(* The guarded facts the signatures of the binding `f` state at a call's
   normal return, as `call_facts` states its facts. *)
let call_gfacts ?name env f (args : expr list) : gfact list =
  List.filter_map (fun fact -> of_guarded_fact (fun p ->
    if p = 0 then name
    else if p >= 2 then (match List.nth_opt args (p - 2) with
      | Some {node=Id a;_} when value_binding env a -> Some a
      | _ -> None)
    else None) fact) (!call_ensures env f)

(* A declaration's guarded facts: as a statement's, then restated at a
   path's read; `const x = c ? null : p.f` (or with the arms swapped, or
   `undefined`) states of `x` what the read's arm states, under the guard
   `x === null`: on the literal's arm the guard reads its tag's value. *)
let gdeclaration env (gs : gfact list) (fs : fact list) name (init : expr) : gfact list =
  let gs = if heap_free env init then gs
    else gkept ?ch:(object_changes env init) env gs in
  let gs = gforget name gs in
  (* `const x = f(…)` of a function stating a guarded postcondition. *)
  let gs = match init.node with
    | Call ({node=Id f;_},None,args,[],_) -> gs @ call_gfacts ~name env f args
    | _ -> gs in
  let rec uncast (e : expr) = match e.node with
    | Cast (("as" | "satisfies" | "nonNull"),_,a) -> uncast a
    | _ -> e in
  let read = match path_of env (uncast init) with
    | Some (root,(_ :: _ as path)) when root <> name && heap_free env init -> grestate_read name (root,path) gs
    | _ -> [] in
  let literal (e : expr) = match e.node with
    | Literal LNull -> Some "null"
    | Literal LUndefined | Id "undefined" -> Some "undefined"
    | _ -> None in
  let conditional = match init.node with
    | Conditional (c,a,b) when heap_free env init ->
      let arm = match literal a, literal b with
        | Some tag,None -> Some (tag,b,false)
        | None,Some tag -> Some (tag,a,true)
        | _ -> None in
      (match arm with
       | Some (tag,e,answer) ->
         (match path_of env e with
          | Some (root,(_ :: _ as path)) when root <> name ->
            let facts,guarded = geliminate (excluded env c answer) gs in
            let under ((guards,_) : gfact) = match guards with
              | (x,[],t) :: _ -> x = name && t = tag
              | _ -> false in
            List.filter under (grestate_read name (root,path) guarded) @
            List.map (fun f -> [name,[],tag],f) (List.filter (mentions name) (restate_read name (root,path) (fs @ facts)))
          | _ -> [])
       | None -> [])
    | _ -> [] in
  gs @ read @ conditional

(* A statement's guarded facts: those naming a binding it assigns
   forgotten, those a heap write keeps (`gkept`), and a destructuring's
   field reads restated of the names they are bound to. *)
let gstatement ?(bounds=[]) env (fs : fact list) (gs : gfact list) (s : stmt) : gfact list =
  let gs = if statement_heap_free env s then gs else gkept ?ch:(statement_changes ~facts:fs ~bounds env s) env gs in
  let gs = List.fold_left (fun gs x -> gforget x gs) gs (names_assigned s env) in
  let gs = match s.statement with
    | Effect {node=Call ({node=Id f;_},None,args,[],_);_} -> gs @ call_gfacts env f args
    | _ -> gs in
  match s.statement with
  | Destructure _ ->
    (match destructure_reads env s with
     | Some ((root,path),fields) ->
       let gs = List.fold_left (fun gs (_,n) -> gforget n gs) gs fields in
       gs @ List.concat_map (fun (f,n) -> grestate_read n (root,path @ [f]) gs) fields
     | None -> gs)
  | _ -> gs


(* Element reads of quantified facts (ARITHMETIC.md, "Quantified
   clauses"; Lean's `HeapKnowledge.instantiateEvery`): a read `xs[k]` of an
   array or a typed array (`%ElementAt%`, `%ByteAt%`) a quantified fact
   holding where the statement starts names, at an
   index the facts state `0 ≤ k < stop`, gives a value of which each body
   fact holds, the index read as `k` and the element as the value. Each such
   read's value is named (`element_reads`) while an expression is analysed,
   its body facts added, and the name eliminated after, as Lean drops the
   read's slot. *)
let instantiate fs reads (e : efact) ((kt,kc) : (string * int) list * int) (name : string) : fact list =
  let offset n = if String.starts_with ~prefix:"%offset" n then int_of_string_opt (String.sub n 7 (String.length n - 7)) else None in
  let shifted d = List.find_map (fun (arr,(jt,jc),r) ->
    if arr = e.arr && entails fs (norm (jt @ scale (-1) kt), kc+d-jc) && entails fs (norm (kt @ scale (-1) jt), jc-kc-d) then Some r else None) reads in
  let available f = List.for_all (fun (n,_) -> match offset n with None -> true | Some d -> shifted d <> None) (fst f) in
  let body = List.filter available e.body in
  let choices = List.filter (fun d -> List.for_all available (datoms d)) e.choices in
  let named = List.exists (fun ((t,_) : fact) -> List.mem_assoc elem_var t) body in
  let rename ((t,d) : fact) =
    let a = Option.value ~default:0 (List.assoc_opt index_var t) in
    let t = List.concat_map (fun (n,c) ->
      if n = index_var then scale c kt else if offset n <> None then [Option.get (shifted (Option.get (offset n))),c] else if term_binding n = elem_var then (let _,p,k = term_parts n in [make_term ~path:p k name,c]) else [n,c]) t in
    norm t, d - a * kc in
  let facts = (if named then [int_fact name] else []) @ List.map rename body in
  facts @ List.concat_map (dfreed (fs @ facts)) (List.map (dmap rename) choices)

(* The same local names carry bounded shifts and masks inside a larger
   expression. Their facts are the arithmetic postconditions checked by
   Lean's `IndexWrites.bitAtoms`; children are named before their parents. *)
let element_facts ~array env fs (e : expr) : fact list * (Json.t * string) list =
  let found = ref [] and extra = ref [] and reads = ref [] in
  let rec go (e : expr) =
    List.iter go (Source.children e);
    let saved = !element_reads in
    element_reads := !found @ saved;
    Fun.protect ~finally:(fun () -> element_reads := saved) (fun () ->
    let fs = fs @ !extra in
    match e.node with
    | Arith ((Shr | BitAnd),_,_) when not (List.mem_assoc e.pos !found) ->
      let name = "%bit" ^ string_of_int (List.length !found) in
      let facts = bitwise_facts ~array env fs name e in
      if facts <> [] then begin
        found := (e.pos,name) :: !found;
        extra := !extra @ facts
      end
    | Call ({node=Id ("%ElementAt%" | "%ByteAt%");_},None,[xs;k],[],_) when not (List.mem_assoc e.pos !found) ->
      (match path_of env xs, linear ~array env fs k with
       | Some (root,path), Some (kt,kc) ->
         let ranged = fs @ term_ranges ((kt,0) :: fs) in
         (match List.filter (fun (ef : efact) -> ef.arr = (root,path) &&
             entails (ranged @ term_ranges [[ef.stop,1],0]) (scale (-1) kt, kc) &&
             entails (ranged @ term_ranges [[ef.stop,1],0]) (norm (kt @ [ef.stop,-1]), -1 - kc)) !current_efacts with
          | [] -> ()
          | efs ->
            let name = "%elem" ^ string_of_int (List.length !found) in
            found := (e.pos,name) :: !found;
            reads := ((root,path),(kt,kc),name) :: !reads;
            extra := List.sort_uniq compare (!extra @ List.concat_map (fun (arr,idx,r) ->
              List.concat_map (fun ef -> if ef.arr = arr then instantiate (fs @ !extra) !reads ef idx r else []) efs) !reads))
       | _ -> ())
    | _ -> ()) in
  go e;
  !extra, !found

(* `f` with the element reads of `e` named and their facts added, its result
   with the names eliminated by `clean`. *)
let with_reads ~array env fs (e : expr) (f : fact list -> 'a) (clean : string list -> 'a -> 'a) : 'a =
  let extra, found = element_facts ~array env fs e in
  if found = [] then f fs else begin
    let saved = !element_reads in
    element_reads := found @ saved;
    Fun.protect ~finally:(fun () -> element_reads := saved) (fun () ->
      clean (List.map snd found) (f (fs @ extra)))
  end
let forget_all names fs = List.fold_left (fun fs x -> forget x fs) fs names

let test ~array env fs (cond : expr) =
  with_reads ~array env fs cond (fun fs' -> fs', test ~array env fs' cond)
    (fun names (fs', ((t,bt),(f,bf))) ->
      let answer a = List.filter (fun x -> not (List.mem x fs)) (forget_all names (fs' @ a)) in
      fs', ((answer t, List.filter (fun (_,i,_) -> not (List.mem i names)) bt),
            (answer f, List.filter (fun (_,i,_) -> not (List.mem i names)) bf)))
  |> snd
let declaration ~array env fs name (init : expr) =
  with_reads ~array env fs init (fun fs ->
    let stated = declaration ~array env fs name init in
    let rec uncast e = match e.node with Cast (_,_,a) -> uncast a | _ -> e in
    match List.assoc_opt (uncast init).pos !element_reads with
    | None -> stated
    | Some read ->
      let projected = List.filter (fun (t,_) -> List.exists (fun (n,_) -> term_binding n = read) t) fs in
      stated @ List.map (fun (t,d) -> List.map (fun (n,c) ->
        let b,p,k = term_parts n in (if b = read then make_term ~path:p k name else n),c) t,d) projected) forget_all
let statement ~array ?(bounds=[]) ?(regions=[]) ?(stores=[]) env fs (s : stmt) =
  match s.statement with
  | Effect e -> with_reads ~array env fs e (fun fs -> statement ~array ~bounds ~regions ~stores env fs s) forget_all
  | _ -> statement ~array ~bounds ~regions ~stores env fs s

(* A quantified fact restated where a binding `name` is declared at the read
of the path `(root, path)` (Lean's `readEvery`): its array, its bound and its
body terms through the path, of the binding. *)
let erestate_read name (root,path) (e : efact) : efact option =
  let rec prefix p q = match p,q with
    | [],rest -> Some rest
    | f :: p,g :: q when f = g -> prefix p q
    | _ -> None in
  let rename t = if t = index_var || term_binding t = elem_var || String.starts_with ~prefix:"%offset" t then t else
    let b,p,kind = term_parts t in
    if b <> root then t else match prefix path p with Some rest -> make_term ~path:rest kind name | None -> t in
  let arr = if fst e.arr = root then (match prefix path (snd e.arr) with Some rest -> (name,rest) | None -> e.arr) else e.arr in
  let e' = { arr; stop = rename e.stop; body = List.map (fun ((t,d) : fact) -> List.map (fun (n,c) -> rename n,c) t, d) e.body;
    choices = List.map (dmap (fun (t,d) -> List.map (fun (n,c) -> rename n,c) t,d)) e.choices } in
  if e' = e then None else Some e'

(* The quantified facts a call growing its receiver's store keeps, `xs.push(a)`
   or a growing method of another receiver (Lean's `PromiseCalls.everyGrown`):
   each whose body facts the growth keeps, the index and the element read
   apart, and whose bound it keeps (`every-grow`); and, for `xs.push(a)` of one
   actual, a safe integer the facts give as a linear form, each over `xs`'s
   whole array whose body facts the facts state of `a` at the index
   `xs.length` (`every-push`). *)
let egrown ?(regions = []) ~array env fs (es : efact list) (e : expr) : efact list option =
  let es = List.filter (fun e -> e.choices = []) es in
  match e.node with
  | Invoke ({node=Read (r,key);_},args,[],_) when heap_free env r && List.for_all (heap_free env) args &&
      !method_grows env r key ->
    let ch = { obj = false; num = false; store = `Grow; framed = no_frame; apart = false; cell_write = false } in
    (* The length of an array a region fact keeps apart from the receiver's,
       whose store cell the growth keeps (Lean's `growFirst`). *)
    let region_kept n = match r.node with
      | Id xs -> let b,path,kind = term_parts n in path = [] && kind = Length_term && rapart regions xs b
      | _ -> false in
    let term_kept ch n = term_kept ch n || region_kept n in
    let body_kept ((t,_) : fact) =
      List.for_all (fun (n,c) -> n = index_var || n = elem_var || (term_binding n <> elem_var && (term_kept ch n || (c <= 0 && term_grown ch n)))) t in
    let appended (ef : efact) = match r.node, args with
      | Id xs, [a] when ef.arr = (xs,[]) && ef.stop = length_term xs ->
        let int_actual = match a.node with Id x -> is_int fs x | _ -> true in
        int_actual && (match linear ~array env fs a with
          | Some (at,ac) ->
            let ranged = fs @ term_ranges ((at,0) :: fs) @ term_ranges [[length_term xs,1],0] in
            List.for_all (fun ((t,d) : fact) ->
              let k = Option.value ~default:0 (List.assoc_opt elem_var t) in
              let t = List.concat_map (fun (n,c) ->
                if n = index_var then [length_term xs,c] else if n = elem_var then scale c at else [n,c]) t in
              entails ranged (norm t, d - k * ac)) ef.body
          | None -> false)
      | _ -> false in
    Some (List.filter (fun (ef : efact) -> ef.choices = [] && List.for_all body_kept ef.body &&
      (term_kept ch ef.stop || appended ef)) es)
  | _ -> None

(* Whether a term reads, through the heap, nothing of the region of the array
   `xs` holds: a binding's value, a string's length, or the length of an array
   a region fact keeps apart from it (Lean's `termApart`). *)
let term_apart (rs : rfact list) xs t =
  t = index_var || t = elem_var || String.starts_with ~prefix:"%offset" t ||
  (let b,path,kind = term_parts t in
   path = [] && (match kind with
     | Value_term | Str_length_term -> true
     | Length_term -> rapart rs xs b
     | View_term -> false))

(* The quantified facts a step keeps: across a growing call, those `egrown`
   keeps; where it writes no heap, those naming no binding it assigns (Lean
   keeps an atom across a step that keeps the heap); across a write at a
   checked index, those over arrays apart from the written one; across a
   change keeping stores and numbers, those whose array, bound and terms it
   keeps (Lean's `everyKept`); none otherwise. *)
(* The quantified facts a typed array's element write `b[k] = v` keeps (Lean's
   `PromiseCalls.everyWritten`, `every-write`): each over `b`'s array whose
   bound the facts state at most `k`, or each of whose body facts they state
   of `v` at the index `k`. A fact over any other array is dropped: views may
   share bytes. *)
let ewritten ~array env fs (es : efact list) (e : expr) : efact list option =
  let es = List.filter (fun e -> e.choices = []) es in
  match e.node with
  | Call ({node=Id "%ByteSet%";_},None,[{node=Id b;_};k;v],[],_) when !call_element_write env "%ByteSet%" ->
    (match linear ~array env fs k, linear ~array env fs v with
     | Some (kt,kc), Some (vt,vc) ->
       let ranged extra = fs @ term_ranges ((kt,0) :: (vt,0) :: fs) @ term_ranges [extra,0] in
       let past (ef : efact) = entails (ranged [ef.stop,1]) (norm ((ef.stop,1) :: scale (-1) kt), kc) in
       let meets (ef : efact) = List.for_all (fun ((t,d) : fact) ->
         let a = Option.value ~default:0 (List.assoc_opt index_var t) in
         let c = Option.value ~default:0 (List.assoc_opt elem_var t) in
         let t = List.concat_map (fun (n,x) ->
           if n = index_var then scale x kt else if n = elem_var then scale x vt else [n,x]) t in
         entails (ranged [ef.stop,1]) (norm t, d - a * kc - c * vc)) ef.body in
       let terms = List.sort_uniq String.compare (List.concat_map (fun (t,_) -> List.map fst t) fs) in
       Some (List.concat_map (fun (ef : efact) ->
         if ef.arr <> (b,[]) || ef.body = [] then [] else
         (if past ef || meets ef then [ef] else []) @
         (if not (meets ef) || not (entails (ranged [ef.stop,1]) (norm (kt @ [ef.stop,-1]), -kc)) then [] else
          List.filter_map (fun stop ->
            if entails (ranged [stop,1]) (norm ((stop,1) :: scale (-1) kt), kc + 1) &&
               entails (ranged [stop,1]) (norm (kt @ [stop,-1]), -kc - 1)
            then Some { ef with stop } else None) terms)) es)
     | _ -> Some [])
  | _ -> None

let estatement ?(array = fun _ _ -> false) ?(facts = []) ?(regions = []) env (es : efact list) (s : stmt) : efact list =
  let es = match (match s.statement with
    | Effect e -> (match egrown ~regions ~array env facts es e with Some es -> Some es | None -> ewritten ~array env facts es e)
    | _ -> None) with
  | Some es -> es
  | None -> if statement_heap_free env s then es else
    match s.statement with
    (* A write at an index of `xs` keeps each quantified fact over an array
       apart from it whose bound and free terms read nothing of its region
       (Lean's `writeAtoms`, `every-apart-write`). *)
    | Effect {node=IndexWrite ({node=Id xs;_},{node=Id _;_},rhs);_} when heap_free env rhs && slot_binding env xs ->
      List.filter (fun e -> snd e.arr = [] && rapart regions xs (fst e.arr) && term_apart regions xs e.stop &&
        List.for_all (fun ((t,_) : fact) -> List.for_all (fun (n,_) -> term_apart regions xs n) t) (e.body @ List.concat_map datoms e.choices)) es
    | _ ->
    match statement_changes ~facts:[] ~bounds:[] env s with
    | Some ch when ch.store = `Keep && not ch.num ->
      List.filter (fun e -> term_kept ch (length_term ~path:(snd e.arr) (fst e.arr)) &&
        term_kept ch e.stop && List.for_all (fun (ts,_) -> List.for_all (fun (t,_) ->
          t = index_var || t = elem_var || String.starts_with ~prefix:"%offset" t ||
          (term_binding t <> elem_var && term_kept ch t)) ts) (e.body @ List.concat_map datoms e.choices)) es
    | _ -> [] in
  let assigned = names_assigned s env in
  let es = List.filter (fun e -> not (List.exists (fun b -> List.mem b assigned) (ebindings e))) es in
  let reads = match destructure_reads env s with
    | Some ((root,path),fields) -> List.map (fun (f,n) -> n,(root,path @ [f])) fields
    | None -> (match s.statement with
      | Declare (_,bindings) -> List.filter_map (fun (n,_,init) -> match path_of env init with
          | Some (root,(_ :: _ as path)) when root <> n -> Some (n,(root,path))
          | _ -> None) bindings
      | Effect {node=Assign (n,_,{node=Id root;_});_} when slot_binding env n -> [n,(root,[])]
      | _ -> []) in
  (* Each read in turn restates the facts the reads before it gave, as Lean's
     reads do one after another. *)
  let es = List.fold_left (fun es (n,rp) -> es @ List.filter_map (erestate_read n rp) es) es reads in
  match s.statement with
  | Declare (_,bindings) -> es @ List.filter_map (fun (name,_,init) -> match init.node with
      | New ({node=Id c;_},_,([_] as args),[]) when
          List.mem c ["Uint8Array"; "Uint16Array"; "Int32Array"; "Float64Array"] &&
          List.exists (fun (terms,_) -> List.mem_assoc (view_term name) terms)
            (construct_ensures ~array env facts name c args) ->
          Some { arr = (name,[]); stop = view_term name; body = []; choices = [] }
      | _ -> None) bindings
  | _ -> es

(* A precondition's quantified facts over bindings, `name p` the binding the
   position `p` holds; a fact naming a position no binding holds is left out. *)
let of_every_fact (name : int -> string option) (fact : Semantic.index_fact) : efact option =
  let term (t : Semantic.term) = match t with
    | Semantic.Value_at (x,path) -> Option.map (fun n -> path_term n path) (name x)
    | Semantic.Length_at (x,path) -> Option.map (fun n -> length_term ~path n) (name x)
    | Semantic.View_at (x,path) -> Option.map (fun n -> view_term ~path n) (name x)
    | Semantic.Str_length_at (x,path) -> Option.map (fun n -> str_length_term ~path n) (name x) in
  match fact with
  | Semantic.Every (x,path,stop,body) ->
    let var = function
      | Semantic.Body_index -> Some index_var
      | Semantic.Body_elem -> Some elem_var
      | Semantic.Body_offset d -> Some ("%offset" ^ string_of_int d)
      | Semantic.Body_project (k,p) -> Some (make_term ~path:p (match k with
        | "length" -> Length_term | "view" -> View_term | "strLength" -> Str_length_term | _ -> Value_term) elem_var)
      | Semantic.Body_term t -> term t in
    let rec fact = function
      | Semantic.Body_either (a,b) -> (match fact a,fact b with Some a,Some b -> Some (DEither (a,b)) | _ -> None)
      | Semantic.Body_le (form,d) ->
        let terms = List.map (fun (v,c) -> Option.map (fun n -> n,c) (var v)) form in
        if List.for_all Option.is_some terms then Some (DAtom (List.filter_map Fun.id terms, d)) else None
      | Semantic.Body_ne _ -> None in
    let body = List.map fact body in
    (match name x, term stop with
     | Some root, Some stop when List.for_all Option.is_some body ->
       let clauses = List.filter_map Fun.id body in
       Some { arr = (root,path); stop;
         body = List.filter_map (function DAtom f -> Some f | DEither _ -> None) clauses;
         choices = List.filter (function DAtom _ -> false | DEither _ -> true) clauses }
     | _ -> None)
  | _ -> None

(* The region facts a statement keeps and states (Lean's `writeAtoms`,
   `grownRegions` and `regionAtoms`): each across a statement writing no heap;
   across `xs.push(a)` of actuals writing no heap, each between two arrays; across `xs[k] = v`, one side `xs` and the other an
   array apart from it, or both apart from it; none naming a binding the
   statement assigns. A declaration of an array literal states its binding
   apart from every older array binding `visible` names, one Lean's scope
   holds (`region-alloc`). *)
(* Whether every type the binding's type states for a field states it
   `@stable` (Lean's `HeapExpressionRules.stableFirst`): every step keeps the
   field's location. Set by the statement analysis, which reads the type. *)
let stable_field : ((string * Environment.binding) list -> string -> string -> bool) ref = ref (fun _ _ _ -> false)

(* The store separations a statement keeps (Lean's `IndexFact.keptBy`):
   each across a statement writing no heap; one between two bindings' own
   stores across any statement, which reads no heap (`envOnly`); one whose
   paths are at most one `@stable` field across a call of a function, whose
   step keeps every stable field's location (`stableFirst`); none naming a
   binding the statement assigns. A declaration of an object literal whose
   field holds an empty array literal states the field's array apart from
   every older array binding `visible` names (`region-alloc`, read through
   the literal's field link, `store-apart-links`). *)
let sstatement ?(array = fun _ _ -> false) ?(visible = fun _ -> true) env (ss : sfact list) (s : stmt) : sfact list =
  let assigned = names_assigned s env in
  let ss = List.filter (fun f -> not (List.exists (fun x -> List.mem x assigned) (sbindings f))) ss in
  let fresh = match s.statement with
    | Declare (_,bindings) -> List.concat_map (fun (n,_,(init:expr)) -> match init.node with
        | Alloc fields -> List.concat_map (fun (key,(v:expr)) -> match key, v.node with
            | Semantic.Name f, ArrayLiteral (_,[]) -> List.filter_map (fun (m,_) ->
                if m <> n && visible m && not (is_fact m) && not (is_bound m) && not (is_field m) && slot_binding env m && array m []
                then Some ((n,[f]),(m,[])) else None) env
            | _ -> []) fields
        | _ -> []) bindings
    | _ -> [] in
  fresh @ if statement_heap_free env s then ss else
  let call = match s.statement with
    | Effect {node=Call ({node=Id _;_},None,args,[],_);_} -> List.for_all (heap_free env) args
    | _ -> false in
  let side (x,p) = match p with
    | [] -> true
    | [f] -> slot_binding env x && !stable_field env x f
    | _ -> false in
  List.filter (fun (((_,p),(_,q)) as f) -> (p = [] && q = []) || (call && side (fst f) && side (snd f))) ss

let rstatement ?(array = fun _ _ -> false) ?(visible = fun _ -> true) env (rs : rfact list) (s : stmt) : rfact list =
  let rs = if statement_heap_free env s then rs else match s.statement with
    | Effect {node=IndexWrite ({node=Id xs;_},{node=Id _;_},rhs);_} when heap_free env rhs && slot_binding env xs ->
      List.filter (fun (x,y) ->
        if x = xs then y <> xs && rapart rs xs y && array y []
        else if y = xs then rapart rs xs x && array x []
        else rapart rs xs x && rapart rs xs y) rs
    (* A call growing its receiver's store appends cells past the old heap:
       each fact between two arrays is kept (Lean's `grownRegions`). *)
    | Effect {node=Invoke ({node=Read (r,key);_},args,[],_);_}
      when heap_free env r && List.for_all (heap_free env) args && !method_grows env r key ->
      List.filter (fun (x,y) -> array x [] && array y []) rs
    | _ -> [] in
  let assigned = names_assigned s env in
  let rs = List.filter (fun (x,y) -> not (List.mem x assigned) && not (List.mem y assigned)) rs in
  let fresh = match s.statement with
    | Declare (_,bindings) -> List.concat_map (fun (n,_,(init:expr)) -> match init.node with
        | ArrayLiteral (_,[]) -> List.filter_map (fun (m,_) ->
            if m <> n && visible m && not (is_fact m) && not (is_bound m) && not (is_field m) && slot_binding env m && array m []
            then Some (n,m) else None) env
        | _ -> []) bindings
    | _ -> [] in
  List.sort_uniq compare (rs @ fresh)
