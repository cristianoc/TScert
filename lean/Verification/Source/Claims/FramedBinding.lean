import Verification.Source.Claims.FramedSpec
import Verification.Paper.TolerantFrames.ReadOnlyBinding

/-! # The binding checks of a framed plan, at its request

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The binding checks" and
"Realization"). The checks of `ReadOnlyBinding` read at a framed plan's
request:

- **The request's code** (`requestCode`): the tables of the request's
  program, which the claim's term runs (`gotoOf_requestCode`).
- **The realized code's proposals are the request's at body labels**
  (`realizedFlowB`, `realizedFlowB_sound`): at every context of the
  realized code, the request's code has a proposal with the same nodes at
  each label of the request's program, the same allocation sites at each
  of its nodes' continuations and handlers, and the same return set, so
  `Fits`, `Provenance` and the frame check read the same proposal in
  either code. -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **The request's code**: the tables of its program. -/
def requestCode (r : SourceRequest σ ι) : Code :=
  (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler))

/-- The claim's term runs the request's code (proved, by definition). -/
theorem gotoOf_requestCode (r : SourceRequest σ ι) (s : Nat) (L : List Tm) (d : Tm) (c : ComponentTag) :
    PassUnit.gotoOf r.program s L d c = .goto (requestCode r).1 (requestCode r).2 s L d c := rfl

/-- **The realized code's proposals are the request's at body labels**,
decided (`agreeB` at the request's program's labels and node keys). -/
def realizedFlowB {P : Package} [DecidableEq P.Site] (F : FFlow P) (r : SourceRequest σ ι) : Bool :=
  agreeB F (realizedCode r) (requestCode r) (requestCode r).2 r.program.length

/-- **The realization check is sound** (proved, `agreeB_sound`). -/
theorem realizedFlowB_sound {P : Package} [DecidableEq P.Site] {F : FFlow P} {r : SourceRequest σ ι}
    (h : realizedFlowB F r = true) {c : Nat} {π₁ : CodeFlow P} (h₁ : F.flow.code (realizedCode r) c = some π₁) :
    ∃ π₂, F.flow.code (requestCode r) c = some π₂ ∧ π₁.ret = π₂.ret ∧
      (∀ kx ∈ (requestCode r).2, π₁.alloc kx = π₂.alloc kx) ∧
      ∀ l, l < r.program.length → π₁.env l = π₂.env l ∧ π₁.val l = π₂.val l ∧ π₁.fn l = π₂.fn l ∧
        π₁.vfn l = π₂.vfn l ∧ π₁.out l = π₂.out l :=
  agreeB_sound h h₁

end
end Verification.SourceClaimJson
