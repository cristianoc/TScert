(* proposal_types.ml defines the candidate records that inference supplies for SourceClaims serialization. *)
open Json
open Proposal_types
open Semantic
open Environment
open Source
(* The rigid parameters a type uses as a rest's argument lists: a
   declaration's packed parameters, whose arguments its applications complete
   with their argument lists. *)
let rec packed_rigids (t : ty) : rigid list = match t with
  | Rigid _ -> []
  | Union ts -> List.concat_map packed_rigids ts
  | Meet (t,ts) -> List.concat_map packed_rigids (t::ts)
  | Atoms atoms -> List.concat_map (function
      | Shape s ->
        List.concat_map (fun (f:field) ->
          packed_rigids f.read @ (match f.write with Some w -> packed_rigids w | None -> [])) s.fields
        @ List.concat_map (fun (i:index_signature) -> packed_rigids i.value) s.indexes
        @ List.concat_map signature_packed s.calls
        @ (match s.elements with Some q -> sequence_packed q | None -> [])
      | Ctors (ss,statics) -> List.concat_map signature_packed ss
        @ List.concat_map (fun (f:field) -> packed_rigids f.read) statics
      | Named (_,args) -> List.concat_map packed_rigids args
      | Exact fs -> List.concat_map (fun (f:field) -> packed_rigids f.read) fs
      | _ -> []) atoms
and signature_packed (s : signature) =
  (match s.rest_pack with Some (PackParameter r) -> [r] | Some (Pack q) -> sequence_packed q | None -> [])
  @ List.concat_map packed_rigids (s.receiver :: s.result :: s.params @ Option.to_list s.variadic)
and sequence_packed (q : sequence) =
  List.concat_map packed_rigids (q.required @ q.optional_elements @ Option.to_list q.rest)
(* A property key as the claim wire spells it: the decoding of
   `Source.property_key`. *)
let key_json = function
  | Name name -> String name
  | Key i -> Object ["symbol",int i]

let unsupported s = fail ("unsupported: " ^ s)
(* The graph's sole callable contract shape. Effects become definition
   obligations when a qualified signature is proposed. *)
let effect_json = function
  | Unrestricted -> String "unrestricted"
  | PreservesInputHeap -> String "preservesInputHeap"
let rec resolution_json = function
  | StableResolution -> Object ["k",String "stable"]
  | NativeResolution child -> Object ["k",String "native";"child",resolution_json child]
  | PromiseObservation -> Object ["k",String "promise"]
  | UnionResolution arms -> Object ["k",String "union";"arms",Array (List.map resolution_json arms)]
  | BinderResolution binder -> Object ["k",String "binder";"binder",String binder]
let call_contract call_effect receiver arguments result = Object [
  "receiver",receiver; "arguments",arguments; "result",result;
  "effect",effect_json call_effect]

(* A label on the wire (SOURCE-CLAIMS.md, "Encoding"): a row of the document's
   own table, or a term naming what only Lean builds rows for, a declaration's
   application, an intersection, an array or a binder in scope. The
   constructors are in the canonical order, and OCaml's structural order on
   this type is the order a label list is written in. *)
type label =
  | Row of int
  | Decl of int * label list list
  | Meet of label list list
  | Arr of label list * bool
  | Binder of string

let rec label_json = function
  | Row n -> int n
  | Decl (k,[]) -> Object ["decl",int k]
  | Decl (k,args) -> Object ["decl",int k;"args",Array (List.map labels_json args)]
  | Meet parts -> Object ["meet",Array (List.map labels_json parts)]
  | Arr (store,readonly) -> Object ["array",labels_json store;"readonly",Bool readonly]
  | Binder name -> Object ["binder",String name]
and labels_json ls = Array (List.map label_json ls)

let encode (proposal : Proposal_types.t) =
  (* The table holds the producer's own rows: the four primitives, then each
     clause row it states, interned structurally. *)
  let declarations = proposal.program.declarations in
  let rows = ref [Array [String "nul"]; Array [Object ["boolLit",Object ["value",Bool true]]];
                  Array [Object ["boolLit",Object ["value",Bool false]]]; Array [String "undef"]]
  in
  let intern row =
    let rec find n = function [] -> rows := !rows @ [row]; n
      | r::rs -> if r=row then n else find (n+1) rs in find 0 !rows
  in
  (* The operand lists an intersection distributes into over its operands'
     union arms, each a choice of one arm per operand (at most 16 are
     written; more stay one meet, as before). *)
  let distributed parts =
    let rec arms = function
      | Union ts -> List.concat_map arms ts
      | Atoms (_::_::_ as atoms) -> List.map (fun a -> Atoms [a]) atoms
      | t -> [t] in
    List.fold_right (fun part acc ->
      List.concat_map (fun arm -> List.map (fun rest -> arm :: rest) acc) (arms part)) parts [[]] in
  (* The binders a type uses as packed ones: as a rest's argument lists, or
     as the argument of a declaration's packed parameter. *)
  let rec packed_uses (t : ty) : rigid list = match t with
    | Rigid _ -> []
    | Union ts -> List.concat_map packed_uses ts
    | Meet (t,ts) -> List.concat_map packed_uses (t::ts)
    | Atoms atoms -> List.concat_map (function
        | Shape s ->
          List.concat_map (fun (f:field) ->
            packed_uses f.read @ (match f.write with Some w -> packed_uses w | None -> [])) s.fields
          @ List.concat_map (fun (i:index_signature) -> packed_uses i.value) s.indexes
          @ List.concat_map signature_uses s.calls
          @ (match s.elements with Some q -> sequence_uses q | None -> [])
        | Ctors (ss,statics) -> List.concat_map signature_uses ss
          @ List.concat_map (fun (f:field) -> packed_uses f.read) statics
        | Named (id,args) ->
          let packed = match List.find_opt (fun (d:Source.declaration) -> d.id = id) declarations with
            | Some d -> packed_rigids d.expression | None -> [] in
          let parameters = match List.find_opt (fun (d:Source.declaration) -> d.id = id) declarations with
            | Some d -> d.parameters | None -> [] in
          List.concat (List.mapi (fun i arg -> match List.nth_opt parameters i, arg with
            | Some p, (Rigid r | Meet (Rigid r,_)) when List.mem p packed -> [r]
            | _ -> packed_uses arg) args)
        | Exact fs -> List.concat_map (fun (f:field) -> packed_uses f.read) fs
        | _ -> []) atoms
  and signature_uses (s : signature) =
    (match s.rest_pack with Some (PackParameter r) -> [r] | Some (Pack q) -> sequence_uses q | None -> [])
    @ List.concat_map packed_uses (s.receiver :: s.result :: s.params @ Option.to_list s.variadic)
  and sequence_uses (q : sequence) =
    List.concat_map packed_uses (q.required @ q.optional_elements @ Option.to_list q.rest) in
  let rec labels t = labels_json (label_list t)
  and label_list = function
    (* A binder is its name: Lean reads it as its unit or closure binds it,
       a bounded one within its bound. *)
    | Rigid r -> [Binder r.spelling]
    | Union ts -> List.sort_uniq compare (List.concat_map label_list ts)
    | Meet (t,ts) when (let n = List.length (distributed (t::ts)) in n > 1 && n <= 16) ->
      (* An intersection with a union operand is the union of the
         intersections with each of its arms, `(A | B) & C` is
         `(A & C) | (B & C)`, the same values: the claim states it so, one
         meet row per arm, which a read then splits on. *)
      (* An arm meeting two disjoint primitives, `"hi" & "fixed"` at an
         instance, holds no value, and is left out. *)
      let empty parts = List.exists (fun a -> List.exists (fun b -> match a,b with
        | Atoms [x],Atoms [y] -> Inference.meet_atom x y = Some []
        | _ -> false) parts) parts in
      List.sort_uniq compare (List.concat_map (fun parts -> match parts with
        | _ when empty parts -> []
        | p::ps -> label_list (Meet (p,ps))
        | [] -> []) (distributed (t::ts)))
    (* An intersection, whose row Lean builds from its operands'. *)
    | Meet (t,ts) -> [Meet (List.map label_list (t::ts))]
    | Atoms atoms -> List.sort_uniq compare (List.concat_map atom_labels atoms)
  and atom_labels = function
    | Nul -> [Row 0] | True -> [Row 1] | False -> [Row 2] | Undef -> [Row 3]
    | Num -> [Row (intern (Array [String "num"]))] | Str -> [Row (intern (Array [String "str"]))]
    | Bigint -> [Row (intern (Array [String "bigint"]))] | Symbol -> [Row (intern (Array [String "symbol"]))]
    | NumLit bits -> [Row (intern (Array [Object ["numLit",Object ["bits",String (Printf.sprintf "%Lu" bits)]]]))]
    | StrLit value -> [Row (intern (Array [Object ["strLit",Object ["value",String value]]]))]
    | BigintLit value -> [Row (intern (Array [Object ["bigintLit",Object ["value",Number value]]]))]
    | SymbolLit id -> [Row (intern (Array [Object ["symbolLit",Object ["id",Number (string_of_int id)]]]))]
    | Top -> [Row (intern (Array [String "source"]))]
    | Callable -> [Row (intern (Array [Object ["arrs",Object ["arrows",Array []]]]))]
    (* A quantified construct signature, `new <T>(x: T) => C<T>`: a construct
       scheme row, its binders the names the source spells, each construct
       signature an arrow's arguments and result (no receiver). *)
    (* A generic class value's static fields name none of its binders and are
       read at an instance; the scheme states its construct signatures. *)
    | Ctors ([s],_) when s.quantified <> [] ->
      let binders = List.map (fun (q:Semantic.rigid) -> label_json (Binder q.spelling))
        (List.concat_map quantifier_identities s.quantified) in
      if List.exists (fun (q:Semantic.quantifier) -> q.resolution <> None) s.quantified then
        unsupported "a resolution-qualified construct scheme";
      let within_bounds = List.filter_map (fun (q:Semantic.quantifier) ->
        match Option.value q.bound ~default:(ValueArgument top) with
        | ValueArgument bound -> Some (q.identity, ValueArgument (Meet (Rigid q.identity,[bound])))
        | _ -> None) s.quantified in
      let body = Inference.substitute_signature within_bounds {s with quantified=[]} in
      let signature,variadic = match body.rest_pack with
        | None -> [call_contract Unrestricted (Array []) (Array (List.map labels body.params)) (labels body.result)],[]
        | Some r -> [],[call_contract Unrestricted (Array [])
            (Array [Array (List.map labels body.params);pack_labels r]) (labels body.result)] in
      let bounds = List.map (fun (q:Semantic.quantifier) ->
        let bound = Option.value q.bound ~default:(ValueArgument top) in
        Array [label_json (Binder q.identity.spelling);
          (match bound with ValueArgument t -> labels t | PackArgument p -> pack_labels p
           | ResolutionArgument _ -> unsupported "a resolution descriptor is not a construct binder bound")]) s.quantified in
      [Row (intern (Object ["scheme",Object (["binders",Array binders;"signatures",Array signature]
        @ (if bounds = [] then [] else ["bounds",Array bounds])
        @ (if variadic = [] then [] else ["variadic",Array variadic])
        @ ["construct",Bool true])]))]
    | Ctors (signatures,statics) ->
      List.iter (fun (s:Semantic.signature) ->
        if s.quantified <> [] then unsupported "quantified construct signature claim encoding") signatures;
      (* Variadic construct signatures carry their rest, an argument-list type;
         the list is left out when empty, its one spelling of none. *)
      let fixed = List.filter_map (fun (s:Semantic.signature) -> match s.rest_pack with
        | None -> Some (Array [Array (List.map labels s.params);labels s.result])
        | Some _ -> None) signatures in
      let rests = List.filter_map (fun (s:Semantic.signature) -> Option.map (fun r ->
        Array [Array (List.map labels s.params);Array [pack_labels r;labels s.result]]) s.rest_pack) signatures in
      (* The static fields, invariant, and the readonly ones, views, each
         list left out when empty. *)
      let invariant,readonly = List.partition (fun (f:Semantic.field) -> f.write <> None) statics in
      let entry (f:Semantic.field) =
        if f.optional || (f.write <> None && f.write <> Some f.read) then
          unsupported "a class value's static field is invariant or readonly";
        Array [key_json f.name;labels f.read] in
      let first = List.map entry invariant and views = List.map entry readonly in
      [Row (intern (Array [Object ["ctors",Object (("signatures",Array fixed) ::
        (if rests = [] then [] else ["variadic",Array rests]) @
        (if first = [] then [] else ["first",Array first]) @
        (if views = [] then [] else ["views",Array views]))]]))]
    | Named (id,args) -> declaration_labels id args
    | Exact fs ->
      (* Invariant fields, and one own-key bound: its own keys are among
         exactly theirs. *)
      [Row (intern (Array [Object ["refs",Object ["first",Array (List.map (fun (f:Semantic.field) ->
          if f.optional || f.write <> Some f.read then unsupported "an exact record's fields are invariant";
          Array [key_json f.name;labels f.read]) fs);"rest",Array [];"views",Array [];
        "bounds",Array [Object ["among",Bool true;
          "keys",Array (List.map (fun (f:Semantic.field) -> key_json f.name) fs)]]]]]))]
    (* A quantified signature inside a type (a class's generic method held by
       its prototype, a field of a generic function type): a scheme row,
       which binds its binders' names, the parser's for a closure's binders
       (`"key"#k`) or the ones the source spells. *)
    | Shape {fields=[];indexes=[];elements=None;calls=[s]}
        when s.quantified <> [] ->
      let binders = List.map (fun (q:Semantic.rigid) -> label_json (Binder q.spelling))
        (List.concat_map quantifier_identities s.quantified) in
      let _,resolution = List.fold_left (fun (offset,groups) (q:Semantic.quantifier) ->
        match q.resolution with None -> offset+1,groups
        | Some (_,None) -> offset+2,groups @ [Object ["input",int offset;
            "observation",int (offset+1);"result",Null]]
        | Some (_,Some _) -> offset+3,groups @ [Object ["input",int offset;
            "observation",int (offset+1);"result",int (offset+2)]]) (0,[]) s.quantified in
      (* A bounded value binder is read within its bound, as in the
         closure claim. Keep the bound itself on the scheme as well. A
         packed binder is read at its row, in both components, and has no
         bound: the scheme holds at each of its instances. *)
      let packed = signature_uses s in
      let s = {s with quantified = List.map (fun (q:Semantic.quantifier) ->
        if List.mem q.identity packed then {q with bound = None} else q) s.quantified} in
      let within_bounds = List.filter_map (fun (q:Semantic.quantifier) ->
        match q.bound with
        | _ when List.mem q.identity packed -> None
        | None -> Some (q.identity, ValueArgument (Meet (Rigid q.identity,[top])))
        | Some (ValueArgument bound) -> Some (q.identity, ValueArgument (Meet (Rigid q.identity,[bound])))
        | Some _ -> None) s.quantified in
      let body = Inference.substitute_signature within_bounds {s with quantified=[]} in
      let signature,variadic = match body.variadic,body.rest_pack with
        | None,None -> [call_contract body.call_effect (labels body.receiver) (Array (List.map labels body.params)) (labels body.result)],[]
        | Some element,None ->
          [],[call_contract body.call_effect (labels body.receiver)
            (Array [Array (List.map labels body.params);
              pack_labels (Pack {required=[];optional_elements=[];rest=Some element;readonly=false;presence=Dense})])
            (labels body.result)]
        | _,Some _ -> unsupported "a pack parameter in a generic method's scheme" in
      let bounds = List.map (fun (q:Semantic.quantifier) ->
        let bound = Option.value q.bound ~default:(ValueArgument top) in
        Array [label_json (Binder q.identity.spelling);
          (match bound with ValueArgument t -> labels t | PackArgument p -> pack_labels p
           | ResolutionArgument _ -> unsupported "a resolution descriptor is not a method binder bound")])
        (List.filter (fun (q:Semantic.quantifier) -> not (List.mem q.identity packed)) s.quantified) in
      [Row (intern (Object ["scheme",Object (["binders",Array binders;"signatures",Array signature]
        @ (if bounds = [] then [] else ["bounds",Array bounds])
        @ (if resolution = [] then [] else ["resolution",Array resolution])
        @ (if variadic = [] then [] else ["variadic",Array variadic]))]))]
    | Shape shape ->
      (* An optional field constrains its key only where the object has it:
         a writable one under one invariant contract, a readonly one as a
         view there. *)
      let hosted,plain = List.partition (fun (f:Semantic.field) -> f.host) shape.fields in
      let optional,present = List.partition (fun (f:Semantic.field) -> f.optional) plain in
      let writes,reads = List.partition (fun (f:Semantic.field) -> f.write <> None) present in
      (* A method is a host-relative member: its signatures, received by the
         object, as Lean lowers method syntax (`methods`). *)
      let methods = match hosted with
        | [] -> []
        | fs -> ["methods",Array (List.map (fun (f:Semantic.field) ->
            let signatures = match f.read with
              | Atoms [Shape {fields=[];indexes=[];calls=(_::_ as calls);elements=None}] -> calls
              | _ -> unsupported "a method is one or more signatures" in
            List.iter (fun (s:Semantic.signature) ->
              if s.quantified <> [] then unsupported "quantified method claim encoding") signatures;
            let calls = List.filter_map (fun (s:Semantic.signature) ->
              if s.variadic = None && s.rest_pack = None then
                Some (call_contract s.call_effect (Object []) (Array (List.map labels s.params)) (labels s.result)) else None) signatures in
            let rests = List.filter_map (fun (s:Semantic.signature) ->
              let rest = match s.variadic,s.rest_pack with
                | Some element,None -> Some (pack_labels (Pack {
                    required=[];optional_elements=[];rest=Some element;readonly=false;presence=Dense}))
                | None,Some r -> Some (pack_labels r)
                | Some _,Some _ -> unsupported "signature has both element and pack rests"
                | None,None -> None in
              Option.map (fun rest -> call_contract s.call_effect (Object [])
                (Array [Array (List.map labels s.params);rest]) (labels s.result)) rest) signatures in
            Object ["key",key_json f.name;"calls",Array calls;"rests",Array rests;
                    "schemes",Array [];"receivers",Array (List.map labels f.receivers)]) fs)] in
      let fields writable fs = Array (List.map (fun (f:Semantic.field) ->
        if writable && f.write <> Some f.read then unsupported "asymmetric read/write capability export";
        Array [key_json f.name;labels f.read]) fs) in
      let optional_list = match optional with
        | [] -> []
        | fs -> ["optional",Array (List.map (fun (f:Semantic.field) ->
            if f.write <> None && f.write <> Some f.read then
              unsupported "asymmetric read/write capability export";
            Object ["key",key_json f.name;"readonly",Bool (f.write = None);"type",labels f.read]) fs)] in

      let fields,views = fields true writes,fields false reads in
      (* A record holding its prototype does not own the keys the prototype
         states (the library overlay's hidden members). *)
      let hidden_bound = match List.find_opt (fun (f:Semantic.field) -> f.name = Name "[[proto]]") shape.fields with
        | Some {read=Atoms [Shape p];_} ->
          ["bounds",Array [Object ["among",Bool false;
            "keys",Array (List.map (fun (f:Semantic.field) -> key_json f.name) p.fields)]]]
        | _ -> [] in
      List.iter (fun (a:Semantic.signature) ->
        if a.quantified <> [] then unsupported "quantified callable claim encoding") shape.calls;
      (* Fixed arrows and variadic signatures of one value share its clause; the
         variadic list is left out when empty, its one spelling of none. *)
      let fixed = List.filter (fun (a:Semantic.signature) ->
        a.variadic = None && a.rest_pack = None) shape.calls in
      let arrows = Array (List.map (fun (a:Semantic.signature) ->
        call_contract a.call_effect (labels a.receiver) (Array (List.map labels a.params)) (labels a.result)) fixed) in
      let variadic = List.filter_map (fun (a:Semantic.signature) ->
        (* A rest's type is a pack: of any number of actuals at an element, or
           the one a pack parameter's instance states. *)
        let rest = match a.variadic,a.rest_pack with
          | Some element,None -> Some (pack_labels (Pack {
              required=[];optional_elements=[];rest=Some element;readonly=false;presence=Dense}))
          | Some _,Some _ -> unsupported "signature has both element and pack rests"
          | None,Some r -> Some (pack_labels r)
          | None,None -> None in
        Option.map (fun rest -> call_contract a.call_effect (labels a.receiver)
          (Array [Array (List.map labels a.params);rest]) (labels a.result)) rest) shape.calls in
      let calls = ("arrows",arrows) :: (if variadic = [] then [] else ["variadic",Array variadic]) in
      match shape.elements with
      | Some sequence ->
        if shape.fields <> [] || shape.calls <> [] || shape.indexes <> []
        then unsupported "array with additional fields, indexes or calls";
        (* The store's contract is the producer's; the array holding it, with
           its prototype, is Lean's, over that store. *)
        let store = intern (Array [Object ["list",Object ["first",Object [
          "required",Array (List.map labels sequence.required);
          "optional",Array (List.map labels sequence.optional_elements);
          "rest",(match sequence.rest with None -> Null | Some t -> labels t);
          "readonly",Bool sequence.readonly;"presence",String (presence_name sequence.presence)];"rest",Array []]]]) in
        [Arr ([Row store],sequence.readonly)]
      | None ->
        let clause = match shape.fields,shape.indexes,shape.calls with
        | _,(_::_ as indexes),[] ->
          (* Each index is over the keys its class admits; a mutable one is
             also a writable one, at its one contract. *)
          let entry (index:Semantic.index_signature) = Array [String (match index.keys with
            | Strings -> "strings" | Numeric -> "numeric" | Symbols -> "symbols");labels index.value] in
          let cells = List.filter_map (fun (index:Semantic.index_signature) -> match index.writable with
            | None -> None
            | Some w when w = index.value -> Some (entry index)
            | Some _ -> unsupported "asymmetric index signature") indexes in
          Object ["dict",Object (["first",fields;"rest",Array [];"views",views;
            "indexes",Array (List.map entry indexes)] @ optional_list @ methods
            @ (if cells = [] then [] else ["cells",Array cells]))]
        | _,_::_,_ -> unsupported "callable with an index signature needs a combined clause"
        | _,[],[] -> Object ["refs",Object (["first",fields;"rest",Array [];"views",views] @ optional_list @ methods @ hidden_bound)]
        | _ when methods <> [] -> unsupported "a callable object with methods needs a combined clause"
        | [],[],_ -> Object ["arrs",Object calls]
        | _,_,_ ->
          if optional <> [] then unsupported "callable with optional fields";
          if reads <> [] then unsupported "callable with readonly fields";
          Object ["callable",Object (["first",fields;"rest",Array []] @ calls)] in
        [Row (intern (Array [clause]))]

  and pack_labels p = labels_json (pack_label_list p)
  and pack_label_list = function
    (* A binder's argument lists: its packed name, which Lean reads as the
       unit binds it, a pack binder's row or a packed binder's. *)
    | PackParameter r -> [Binder (r.spelling ^ "#pack")]
    | Pack sequence -> [Row (intern (Array [Object ["pack",Object ["first",Object [
        "required",Array (List.map labels sequence.required);
        "optional",Array (List.map labels sequence.optional_elements);
        "rest",(match sequence.rest with None -> Null | Some t -> labels t);
        "readonly",Bool false;"presence",String "dense"];"rest",Array []]]]))]
  (* An application names its declaration by position, with every argument:
     one left to its default is that default, at the earlier arguments, so
     `IteratorResult<number>` and `IteratorResult<number, unknown>` are one
     label. A nullary declaration's label has no arguments. *)
  and declaration_labels id args =
    let rec find k = function
      | [] -> unsupported ("unknown declaration " ^ id)
      | (d:Source.declaration)::rest ->
        if d.id<>id then find (k + 1) rest
        else if d.parameters=[] && args=[] then [Decl (k,[])]
        else begin
          let rec complete previous supplied parameters defaults = match parameters,defaults with
            | parameter::more,default::others ->
              (match supplied,default with
               | value::tail,_ -> complete ((parameter,Semantic.ValueArgument value)::previous) tail more others
               | [],Some value ->
                 let value = Inference.substitute (List.rev previous) value in
                 complete ((parameter,Semantic.ValueArgument value)::previous) [] more others
               | [],None -> None)
            | [],[] when supplied=[] -> Some (List.rev_map (fun (_,a) -> match a with
                | Semantic.ValueArgument t -> t | _ -> assert false) previous)
            | _ -> None in
          match complete [] args d.parameters d.defaults with
          | Some args ->
            (* A packed parameter's argument with its argument lists: those
               of its array's tuple contract, or a binder's own. *)
            let packed = packed_rigids d.expression in
            [Decl (k,List.map2 (fun parameter arg ->
              if List.mem parameter packed then
                List.sort_uniq compare (label_list arg @ pack_label_list
                  (Inference.substitute_pack [parameter,Semantic.ValueArgument arg] (PackParameter parameter)))
              else label_list arg) d.parameters args)]
          | None -> unsupported "type application has wrong arity"
        end in
    find 0 declarations
  in
  (* A callable whose signature mentions a rigid parameter has no graph row:
     it is exported in the scheme form, with its own binders (possibly none),
     so a returned closure can retain an outer binder in its result. *)
  let rec contains_symbolic = function
    | Rigid _ -> true
    | Meet (t,ts) -> List.exists contains_symbolic (t::ts)
    | Union ts -> List.exists contains_symbolic ts
    | Atoms atoms -> List.exists (function
        | Named (_,args) -> List.exists contains_symbolic args
        | Shape s ->
          List.exists (fun (f:Semantic.field) -> contains_symbolic f.read
            || Option.fold ~none:false ~some:contains_symbolic f.write) s.fields
          || List.exists (fun (i:Semantic.index_signature) ->
              contains_symbolic i.value || Option.fold ~none:false ~some:contains_symbolic i.writable) s.indexes
          || List.exists signature_contains_symbolic s.calls
          || Option.fold ~none:false ~some:sequence_contains_symbolic s.elements
        | Exact fs -> List.exists (fun (f:Semantic.field) -> contains_symbolic f.read) fs
        | Ctors (signatures,statics) -> List.exists signature_contains_symbolic signatures
          || List.exists (fun (f:Semantic.field) -> contains_symbolic f.read) statics
        | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Top
        | Bigint | Symbol | BigintLit _ | SymbolLit _ | Callable -> false) atoms
  and pack_contains_symbolic = function
    | PackParameter _ -> true
    | Pack s -> sequence_contains_symbolic s
  and sequence_contains_symbolic s = List.exists contains_symbolic
      (s.required @ s.optional_elements @ Option.to_list s.rest)
  and signature_contains_symbolic (s:Semantic.signature) =
    List.exists contains_symbolic (s.receiver :: s.result :: s.params @ Option.to_list s.variadic)
    || Option.fold ~none:false ~some:pack_contains_symbolic s.rest_pack
    || List.exists (fun (q:Semantic.quantifier) ->
        Option.fold ~none:false ~some:argument_contains_symbolic q.bound) s.quantified
  and argument_contains_symbolic = function
    | ValueArgument t -> contains_symbolic t
    | PackArgument p -> pack_contains_symbolic p
    | ResolutionArgument (input,(_,observation),result,_) ->
      List.exists contains_symbolic (input :: observation :: Option.to_list (Option.map snd result))
  in
  let rec claim_type t = match t with
    | Rigid n -> Object ["param",String n.spelling]
    | Atoms [Shape {fields=[];indexes=[];calls=[signature];elements=None}]
        when signature.quantified <> [] || List.exists contains_symbolic
          (signature.receiver :: signature.result :: signature.params @ Option.to_list signature.variadic) ->
      if signature.rest_pack <> None then unsupported "a pack parameter in a scheme claim";
      (* A packed binder has no bound: the scheme holds at each instance. *)
      let packed = signature_uses signature in
      let type_params = Array (List.map (fun (q:Semantic.quantifier) -> Object [
        "name",String q.identity.spelling;
        "resolution",(match q.resolution with None -> Null | Some (observation,result) ->
          Object ["observation",String observation.spelling;
            "result",(match result with None -> Null | Some (r:Semantic.rigid) -> String r.spelling)]);
        "bound",(match q.bound with None -> Null
          | Some _ when List.mem q.identity packed -> Null
          | Some (ValueArgument t) -> claim_type t
          | Some (PackArgument _ | ResolutionArgument _) -> unsupported "a non-value bound in a scheme claim")])
        signature.quantified) in
      Object ["scheme",Object ["effect",effect_json signature.call_effect;"typeParams",type_params;
        "this",claim_type signature.receiver;
        "params",Array (List.map claim_type signature.params);
        "rest",(match signature.variadic with None -> Null | Some t -> claim_type t);
        "result",claim_type signature.result]]
    | Atoms [Shape {fields=[];indexes=[];calls=[];elements=Some
        {required=[];optional_elements=[];rest=Some element;readonly=false;presence=Readable}}]
        when contains_symbolic element -> Object ["array",claim_type element]
    | Atoms (_::_::_ as atoms) when contains_symbolic (Atoms atoms) ->
      let rigid, ground = List.partition (fun a -> contains_symbolic (Atoms [a])) atoms in
      let parts = List.map (fun a -> Atoms [a]) rigid @
        (if ground=[] then [] else [Atoms ground]) in
      Object ["union", Array (List.map claim_type parts)]
    | Union ts when List.exists contains_symbolic ts ->
      let rigid, ground = List.partition contains_symbolic ts in
      Object ["union", Array (List.map claim_type (rigid @ ground))]
    | (Atoms _ | Union _) as t -> labels t
    | Meet _ as t -> labels t
  in
  (* The substitution is exported so Lean re-checks the elimination it names,
     rather than re-inferring one of its own. A site that calls no quantified
     callable omits the field: unlike `current`, its absence asserts nothing. *)
  let instantiate = function
    | None -> []
    | Some subst -> ["instantiate",Array (List.map (fun (name,t) ->
        Object ["name",String name; "type",(match t with ValueArgument t -> claim_type t
          | ResolutionArgument (input,_,_,_) -> claim_type input
          | PackArgument p -> pack_labels p);
          "resolution",(match t with
            | ResolutionArgument (_,_,_,certificate) -> Object ["certificate",resolution_json certificate]
            | ValueArgument _ | PackArgument _ -> Null)]) subst)]
  in
  let point t extra = Object (extra @ ["type",claim_type t; "current",Null])
  in
  let named (n,b) = point (binding_type b) ["name",String n]
  in
  (* A statement entry's bindings; a field's known contents are its object's
     `current` assertion, one `[field, type]` pair per field. *)
  let bindings bs = Array (List.filter_map (fun (n,b) ->
    if Environment.is_field n then None else
    let fields = List.filter_map (fun (m,f) ->
      if Environment.is_field m && Environment.owner m = n then
        Some (Array [String (Environment.field_of m); claim_type (binding_type f)])
      else None) bs in
    Some (Object ["name",String n; "type",claim_type (binding_type b);
                  "current",(if fields = [] then Null else Array fields)])) bs)

  in
  let contracts row = Array (List.map (fun (c : Proposal_types.contract) ->
    Object ["pos",c.pos;"name",String c.name;"type",claim_type c.type_]) row) in
  let interior (f : Proposal_types.function_claim) =
    let expressions row = Array (List.map (fun (e : Proposal_types.expression) ->
      Object (["point",String e.point; "pos",e.pos; "type",claim_type e.type_; "current",Null]
        @ instantiate e.instantiation)) row) in
    let entries es = Array (List.map (fun (e : Proposal_types.entry) ->
      Object ["point",String e.point; "start",e.start;"bindings",bindings e.bindings]) es) in
    let arrows = if f.arrows = [] then [] else
      ["arrows",Array (List.map (fun (pos,rows) ->
        Object ["pos",pos;"rows",Array (List.map (fun (o : Proposal_types.overlay) ->
          Object ["contracts",contracts o.row_contracts;"expressions",expressions o.row_expressions;
                  "entries",entries o.row_entries]) rows)]) f.arrows)] in
    ["contracts",contracts f.contracts;"entries",entries f.entries; "expressions",expressions f.expressions] @ arrows in
  let functions = List.map (fun (f : Proposal_types.function_claim) ->
    let source = f.source in
    let expressions row = Array (List.map (fun (e : Proposal_types.expression) ->
      Object (["point",String e.point; "pos",e.pos; "type",claim_type e.type_; "current",Null]
        @ instantiate e.instantiation)) row) in
    (* One set of interior claims per advertised signature, in signature order,
       stated only by a closure that advertises more than one. *)
    let entries es = Array (List.map (fun (e : Proposal_types.entry) ->
      Object ["point",String e.point; "start",e.start;"bindings",bindings e.bindings]) es) in
    let arrows = if f.arrows = [] then [] else
      ["arrows",Array (List.map (fun (pos,rows) ->
        Object ["pos",pos;"rows",Array (List.map (fun (o : Proposal_types.overlay) ->
          Object ["contracts",contracts o.row_contracts;"expressions",expressions o.row_expressions;
                  "entries",entries o.row_entries]) rows)]) f.arrows)] in
    Object (["name",String source.name; "namePos",source.name_pos;
      "params",Array (List.map (fun (n,t) -> named (n,Value t)) source.params);
      "result",claim_type source.result;
      "contracts",contracts f.contracts;
      "entries",entries f.entries;
      "expressions",expressions f.expressions]
      @ arrows)) proposal.functions in
  (* The initialization unit's claims, stated only for a module that has
     top-level code. *)
  let init = match proposal.init with
    | None -> []
    | Some f -> ["init",Object (interior f)] in
  Object (["file",proposal.program.file; "sourceSha256",proposal.program.digest;
    "types",Array !rows; "functions",Array functions] @ init)
