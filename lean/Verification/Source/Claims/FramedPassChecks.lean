import Verification.Source.Claims.FramedBinding
import Verification.Source.ComponentChecks

/-! # The binding checks a framed plan's pass reads of its request

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The binding checks" and "The
plan"). Beside the checks over the plan's flow (`ReadOnlyBinding`,
`FramedBinding`) and those that read the component alone
(`FramedComponentChecks`), the pass reads from the component family the
declaration document describes:

- **The `@clients` rows** (`componentRows`): the rows of the exported
  types of `C`'s module, which `clientsB` compares with the wire's
  $`\Theta_C`$.
- **The read-only types** (`readOnlyInputs`, `readOnlyB`): an input of the
  member is read-only where its entry code's declared shape is read-only
  throughout (`ComponentChecks.readOnlyShape`); `readOnlyB` decides that
  every type a plan reads read-only is one.
- **A realized code's body** (`moduleBody_realized`): the request's code. -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping SourceExtraction ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly

/-- **The `@clients` rows of a component**: the rows of the exported types
of its module. -/
def componentRows (F : ComponentWire.Components) (C : Nat) : List ComponentWire.Clients :=
  match F.components[C]? with
  | some k => F.clients.filter (·.module == k.location)
  | none => []

/-- **The declared shapes of a member's parameters**: those of the code its
component's interface names under the member's name; none where no entry
names it. -/
def memberShapes (F : ComponentWire.Components) (C : Nat) (member : String) : List (Option ComponentWire.Shape) :=
  match (F.components[C]?).map ComponentWire.Component.interface with
  | some (ComponentWire.Interface.known es) => match es.find? (·.name == member) with
    | some e => match F.codes.find? fun c => c.module == e.module && c.pos == e.pos with
      | some c => c.params.map (·.2.2)
      | none => []
    | none => []
  | _ => []

/-- A declared shape read-only throughout (`ComponentChecks.readOnlyShape`);
a position with no declared shape is writable. -/
def shapeReadOnly (F : ComponentWire.Components) : Option ComponentWire.Shape → Bool
  | some t => ComponentChecks.readOnlyShape F.types (ComponentWire.shapeLimit * (F.types.length + 1)) [] t
  | none => false

section
variable {ι : Type} [Labels ι]

/-- **The read-only inputs of a member**: each input whose parameter's
declared shape is read-only throughout. -/
def readOnlyInputs (F : ComponentWire.Components) (C : Nat) (member : String) (inputs : List (Ty ι)) :
    List (Ty ι) :=
  (inputs.zip (memberShapes F C member)).filterMap fun (T, s) => if shapeReadOnly F s then some T else none

/-- **The read-only types check** (`ro_of_readOnlyShape`'s premise),
decided: every type the plan reads read-only is a read-only input. -/
def readOnlyB (F : ComponentWire.Components) (C : Nat) (member : String) (inputs readOnly : List (Ty ι)) : Bool :=
  let ro := readOnlyInputs F C member inputs
  readOnly.all (ro.contains ·)
end

/-- The realized code's body is the request's code (proved). -/
theorem moduleBody_realized {σ ι : Type} [Labels ι] [StoreView σ ι] {codes : List Code}
    {r : SourceRequest σ ι} (h : realizedCode r ∈ codes) : moduleBody codes (realizedCode r) = requestCode r := by
  simp only [moduleBody, List.contains_iff_mem.mpr h, if_true]
  simp [realizedCode, requestCode]

end Verification.SourceClaimJson
