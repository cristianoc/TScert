import Verification.Source.Claims.Json

/-! # A module function's lowered code

A function declared without `this` runs as a closure of its module: its
request's node lists behind one prologue node, which evaluates `undefined`
and continues at the request's start with the frame past the receiver
(`PassUnit.dropReceiver`). `realizedCode` is that code, and
`FilePlans.moduleCodes` gives it, with the function's arity, the module
values it names and its component, for each planned member of a group. -/

namespace Verification.SourceClaimJson
open Lean ControlFlow LabelStore

/-- A code's node lists: each node's expression, and its continuation and
handler. -/
abbrev LoweredCode := List Tm × List (Continuation × Option Target)

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **The realized code of a request** of a function declared without
`this` (`PassUnit.dropReceiver`): its node lists behind one prologue node,
which evaluates `undefined` and continues at the request's start with the
frame past the receiver. -/
def realizedCode (r : SourceElaboration.SourceRequest σ ι) : LoweredCode :=
  (r.program.map (·.expression) ++ [.undef],
    r.program.map (fun n => (n.continuation, n.handler)) ++
      [(.effect ⟨r.start, some ((List.range (r.inputs.length + 1)).map (· + 1))⟩, none)])
end

/-- **A module function's closure code**: its realized code, its arity, the
module values it names (its captures), its component and whether it
collects a rest parameter. A function declaring `this` has none. -/
structure LoweredModule where
  name : String
  code : LoweredCode
  ar : Nat
  siblings : List String
  comp : ComponentTag
  rest : Bool := false

def LoweredModule.ofRequest {σ ι : Type} [Labels ι] [StoreView σ ι] (name : String)
    (r : SourceElaboration.SourceRequest σ ι) : Option LoweredModule :=
  if r.receiver then none else
  -- (the rest's spine is one input, past the arity)
  let ar := r.inputs.length - r.siblings.length - (if r.restParam then 1 else 0)
  some ⟨name, realizedCode r, ar, r.siblings, r.comp, r.restParam⟩

/-- **A native's step model**, the graph whose run the native's call
performs, with its arity. Each row is trusted input, audited against the
native's definition:

- `%ElementAt%(xs, k)`: the element of `xs`'s spine at `k`, `undefined`
  where none (`tools/intrinsics.mts`: on an array of the program the read
  runs no code; no accessor or proxy, DESIGN.md "Trust surface"). Of an
  array or a tuple only: the model reads the spine field. -/
def hostModel? (name : String) : Option (LoweredCode × Nat) :=
  if name == "%ElementAt%" then
    some (([.elemAt (.readAt arraySpineKey (.var 1)) (.var 2)], [(.ret, none)]), 2)
  else none

/-- The module codes of a file's planned members. -/
def FilePlans.moduleCodes (f : FilePlans) (units : List Nat) : List LoweredModule :=
  units.filterMap fun j => match (f.plans.drop j).head? with
    | some (.ok (.graph name _ r)) => if name.isEmpty then none else LoweredModule.ofRequest name r
    | _ => none

end Verification.SourceClaimJson
