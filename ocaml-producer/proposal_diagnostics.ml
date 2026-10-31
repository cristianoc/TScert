open Semantic
open Type_queries

(* Explanation observations belong to one producer run. Its function analyses,
   retries and closure bodies share this state; separate runs receive fresh
   state. These observations explain proposals without changing acceptance. *)
let unsupported s = Json.fail ("unsupported: " ^ s)

type state = {
  explaining : bool ref;
  explanations : (Json.t * string) list ref;
  (* Names introduced by for...in steps. *)
  for_in_keys : string list ref;
  (* Method reads used directly as callees. *)
  method_callees : Json.t list ref;
  (* Primitive shapes established for unknown or parameter-typed names. *)
  shape_tests : (string * string) list ref;
  (* Unknown names whose values pass a class instanceof test. *)
  unknown_instance_tests : string list ref;
}

let create ?(explaining=false) () = {
  explaining = ref explaining;
  explanations = ref [];
  for_in_keys = ref [];
  method_callees = ref [];
  shape_tests = ref [];
  unknown_instance_tests = ref [];
}

(* A run that explains a failed search (`producer --explain`): each form
   whose failure has a known cause is recorded at its source span with its
   reason, and the one at the failed obligation names it. An ordinary run
   proposes these forms as any other, and Lean decides; an explanation only
   names why it found no derivation. *)
let explain state pos s =
  if !(state.explaining) then state.explanations := (pos,s) :: !(state.explanations)
let iteration_reason =
  "the iteration of a host kind is stated (%Iterate:K%), picked by the iterable's type, and a loop over \
   a union of host kinds steps their union's iteration: a spread over such a union, or a loop over a value \
   of no host kind, has no intrinsic (an iterable the program defines, or a union with one, runs the \
   iterator protocol)"
let module_arity_reason =
  "its use is read at the instance it names, a signature of its own parameters, which carries no \
   extension by a rest"
let rest_arity_reason =
  "its rest collects the further actuals rather than discarding them, so each must be within the rest's \
   element, which the signature binding more parameters does not state"
let value_arity_reason =
  "a value known only by its type may read the further actuals: a function with further optional or rest \
   parameters meets a shorter function type, so `(x: T) => U` may be `(x: T, y?: S) => U`, and a call \
   passing more actuals may pass `y` a value outside `S`; only a module function's own code is known to \
   discard them"
let for_in_key_reason =
  "the read is the entry the loop's step visited only where nothing since the step can remove the key or \
   change the object read (a call, a construction, a write of a property or of the object's name), and \
   here something may have run, so the read may miss"
let generic_instances_reason =
  "the covering rule for quantified signatures relates two members up to renaming the target's binders to \
   the source's: as many binders, of the same kinds, each target bound within the source's, and the source's \
   signatures covering the target's renamed; members binding different numbers of binders need an instance \
   table naming each source signature's image at the target's binders"
let implicit_index_reason =
  "TypeScript admits a type literal whose named fields fit the index (an implicit index signature), but \
   a value of it may carry other keys of any type, so it meets no index"
let receiver_reason =
  "that type admits a call passing any receiver, and the function requires its own"
let invariance_reason =
  "a writable element or field is invariant, as a write through the wider view would break the narrower \
   one; TypeScript relates them covariantly, which is unsound"
let family_test_reason =
  "the value is narrowed to that primitive family, and a tag test does not narrow a type parameter's \
   row to its meet with the family, the `T & number` of TypeScript, so it is no longer read as a `T`"
let object_cell_reason =
  "a `let` without an initializer holds `undefined` until it is assigned, and is known to hold another \
   value only where every path into the read assigned one, with no step between that may write it (a \
   call, whose callee may write any location its operands reach)"
let forgotten_cell_reason =
  "a cell is known by its contract after a step that may write it (a call, whose callee may write any \
   location its operands reach, as the model states no reachability; a closure run later; a throw from \
   anywhere in a `try`)"
let equality_reason =
  "neither operand is known to be a primitive or an object, the kinds strict equality decides, and \
   a value of a type parameter may be of any kind"
let dictionary_spread_reason =
  "the copy owns the keys the dictionary holds when it runs, which no type states: the result is a \
   dictionary only where every part says what it gives under the index's keys, by an index or its \
   exact keys"
let relational_reason =
  "`<` converts a string compared with another kind by `StringToNumber`, which the model does not \
   state; it states the comparison of two strings, and of two numbers, bigints, Booleans, `null` or \
   `undefined` after `ToNumeric`"
let relational_object_reason =
  "`<` converts an object through its `valueOf` or `toString`: the host runs client code"
let exact_optional_reason =
  "the pipeline reads `f?: T` exactly, as absent or a `T` (as `exactOptionalPropertyTypes` does), \
   where the default reading of TypeScript also admits a present `undefined`; `f?: T | undefined` states it"
let thenable_reason =
  "JavaScript adopts a thenable, calling its `then`, instead of settling to it; an open record can hide a \
   callable `then`, its own or one on its prototype (a `PromiseLike` is one)"
let symbol_copy_reason =
  "the copy is stated at its string keys only, and JavaScript also copies an own enumerable \
   symbol-keyed property, so the result states no symbol key"
let copy_field_reason =
  "the copy is allocated per pair of its operands' clauses at one record, and several arms of the expected \
   union with the copy's keys type a written field apart (TypeScript types the literal per arm of the \
   contextual union), so no one record meets them all, a writable field being invariant"
let extraction_reason =
  "a method is a member of its object, called with it as receiver, and read off it the function loses \
   that receiver; TypeScript types the read as a function, which is unsound"
(* Whether a read of `key` from a value of `t` finds a method: a host-relative
   member of its record, or of the prototype it reads through. *)
let method_member declarations t key =
  let rec go depth t = depth < 4 && List.exists (function
      | Shape {fields;_} | Exact fields ->
        (match List.find_opt (fun (f:Semantic.field) -> f.name = key) fields with
         | Some f -> f.host
         | None -> List.exists (fun (f:Semantic.field) -> f.name = Name proto_key && go (depth+1) f.read) fields)
      | _ -> false) (try Option.value ~default:[] (flat_atoms declarations t) with Json.Error _ -> []) in
  go 0 t
let builtin_array_reason =
  "`Array.isArray` finds a `readonly unknown[]` in `unknown` or a record, which may be a tuple: its \
   positions hold different types, so no instance of the binder is its store's contract, and a callee \
   rearranging its `Array<A>` breaks the tuple's type"
let mutable_tuple_length_reason =
  "the length of a mutable tuple is not fixed by its type, since `push` is allowed on it (an unsoundness \
   of TypeScript), so its `length` is a number"
let unknown_instance_reason =
  "`x instanceof C` does not narrow `unknown` to C: an object gets C's prototype without C's constructor \
   running (`Object.create(C.prototype)`, `Object.setPrototypeOf`, `Reflect.construct` with C as the new \
   target), so C's prototype on its chain is no evidence of C's fields, and the model assumes it of no value \
   a unit receives"
