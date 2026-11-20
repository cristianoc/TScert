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
- **The read-only positions** (`readOnlyPositions`): a parameter position
  is read-only where the member and every module function sharing its
  realized code declare it read-only throughout
  (`ComponentChecks.readOnlyShape`); `roPositionsB` decides a plan's.
- **The read-only types** (`readOnlyInputs`, `readOnlyB`): the inputs at
  the read-only positions, and the type outgoing values cross at none of
  them.
- **A realized code's body** (`moduleBody_realized`): the request's code. -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping SourceElaboration ControlFlow LabelStore
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

/-- **A declared parameter read-only throughout**: the shape of position
`j` in a member's declared shapes is read-only (`shapeReadOnly`). -/
def declaredReadOnly (F : ComponentWire.Components) (C : Nat) (member : String) (j : Nat) : Bool :=
  shapeReadOnly F (((memberShapes F C member)[j]?).join)

/-- **The read-only positions of a realized code** (the meet, by position,
of the shapes its functions declare): below the arity, position `j` is
read-only where the member and every module function of `C` whose code
(in `codes`, named in `names`) is `m` declare it read-only
(`declaredReadOnly`). -/
def readOnlyPositions (F : ComponentWire.Components) (C : Nat) (member : String) (codes : List Code)
    (names : List (String × Nat × List String)) (m : Code) (arity : Nat) : List Bool :=
  (List.range arity).map fun j => declaredReadOnly F C member j &&
    (codes.zip names).all fun (m', n) => m' != m || declaredReadOnly F C n.1 j

section
variable {ι : Type} [Labels ι]

/-- **The read-only inputs of a plan**: each input at a read-only
position. -/
def readOnlyInputs (inputs : List (Ty ι)) (ro : List Bool) : List (Ty ι) :=
  (inputs.zip ro).filterMap fun (T, b) => if b then some T else none

/-- **The read-only types check**, decided: every type the plan reads
read-only is an input at a read-only position, every input at a read-only
position is one, and the type outgoing values cross at is none. -/
def readOnlyB (inputs readOnly : List (Ty ι)) (ro : List Bool) (outType : Ty ι) : Bool :=
  readOnly.all (fun T => (inputs.zip ro).any fun (T', b) => b && T' == T) &&
    (inputs.zip ro).all (fun (T, b) => !b || readOnly.contains T) && !readOnly.contains outType
end

/-- **The read-only positions check**, decided: the plan's read-only
positions are the realized code's (`readOnlyPositions`) at the member. -/
def FramedSpec.roPositionsB {σ ι : Type} [Labels ι] [StoreView σ ι] (spec : FramedSpec ι) (name : String)
    (r : SourceRequest σ ι) : Bool :=
  spec.roPositions == readOnlyPositions spec.family spec.C name spec.codes spec.names (realizedCode r) spec.arity

/-- **The arity check**, decided: the layout of the realized code in the
plan's flow has the plan's arity, so every closure of it a term or heap
meeting layout provenance holds takes `arity` parameters, and the
parameters are among the request's inputs. -/
def FramedSpec.arityB {σ ι : Type} [Labels ι] [StoreView σ ι] (spec : FramedSpec ι) (r : SourceRequest σ ι) : Bool :=
  (layAt spec.checked spec.lay (realizedCode r)).map (·.1) == some spec.arity && decide (spec.arity ≤ r.inputs.length)

/-- The realized code's body is the request's code (proved). -/
theorem moduleBody_realized {σ ι : Type} [Labels ι] [StoreView σ ι] {codes : List Code}
    {r : SourceRequest σ ι} (h : realizedCode r ∈ codes) : moduleBody codes (realizedCode r) = requestCode r := by
  simp only [moduleBody, List.contains_iff_mem.mpr h, if_true]
  simp [realizedCode, requestCode]

end Verification.SourceClaimJson
