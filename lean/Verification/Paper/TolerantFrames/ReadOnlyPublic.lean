import Verification.Paper.TolerantFrames.ReadOnlyCrossings

/-! # Read-only handles: the public calls of a component

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The calls the claim is about"). A
framed unit's claim is about the calls of its code that outside code makes
in a program: from an initial configuration, along actual steps each
keeping the client obligation at the program's history, an entering step
from outside code into the unit's realized code. This module states that
notion over a frame's core, before any frame:

- **The innermost run** of a term (`innermostGoto`): the code, label, slots,
  default and tag of the run not yet entered at the head of its path.
- **An entering step** (`FrameCore.Entering`): a step keeping the
  obligation whose active frame runs outside code, after which one more
  call of `C` is active and the innermost run is the code `m`.
- **A public call** (`FrameCore.PublicCall`): an initial configuration
  (`Init`), an execution of steps keeping the obligation from it at the
  history before any entry (`bareStart`), and an entering step of `m`.
- **The whole execution** (`PublicCall.ex`, proved): the execution with
  its entering step is one execution of steps keeping the obligation. -/

namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

/-- **The innermost run of a term**: the run not yet entered at the head of
its path (`path`, a `goto` is a frame not yet entered), with its code,
label, slots, default and tag. -/
def innermostGoto (t : Tm) : Option (Code × Nat × List Tm × Tm × ComponentTag) :=
  match (path none t).head? with
  | some (_, .goto E K l L d c) => some ((E, K), l, L, d, c)
  | _ => none

/-- The code `entered` reads is the innermost run's (proved). -/
theorem entered_of_innermostGoto {t : Tm} {m : Code} {l : Nat} {L : List Tm} {d : Tm} {c : ComponentTag}
    (h : innermostGoto t = some (m, l, L, d, c)) : entered none t = some m := by
  unfold innermostGoto at h
  unfold entered
  split at h
  · rename_i E K l' L' d' c' _ heq
    rw [heq]
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  · cases h

namespace FrameCore
variable {τ : Type} (core : FrameCore τ)

/-- **An entering step of the code `m`**: a step keeping the obligation
from a state whose active frame runs outside code to one with one more call
of `C` active, its innermost run the code `m`. -/
def Entering (m : Code) (x a₁ : Conf × Ghost (core.F.at core.C)) : Prop :=
  core.KStep x a₁ ∧ OutsideAt core.F core.C none x.1.t ∧ entered none a₁.1.t = some m ∧
    depthC core.F core.C none a₁.1.t = depthC core.F core.C none x.1.t + 1

/-- **A public call of the code `m`** (the draft, "The calls the claim is
about"): `x₀` an initial configuration (`Init`); an execution of `n` steps
keeping the obligation from `x₀` at the history before any entry; and an
entering step of `m` from its last state `x` to `a₁`. -/
def PublicCall (Init : Conf → Prop) (m : Code) (x₀ : Conf) (n : Nat) (x a₁ : Conf × Ghost (core.F.at core.C)) :
    Prop :=
  Init x₀ ∧ Ex core.KStep (fun _ => True) n (x₀, bareStart core.F core.C x₀.t) x ∧ core.Entering m x a₁

variable {core}

/-- **A public call is one execution** (proved): its steps and its entering
step, each keeping the obligation. -/
theorem PublicCall.ex {Init : Conf → Prop} {m : Code} {x₀ : Conf} {n : Nat} {x a₁ : Conf × Ghost (core.F.at core.C)}
    (h : core.PublicCall Init m x₀ n x a₁) :
    Ex core.KStep (fun _ => True) (n + 1) (x₀, bareStart core.F core.C x₀.t) a₁ :=
  h.2.1.snoc trivial h.2.2.1

/-- **The entering step raises the calls of `C` active** (proved). -/
theorem Entering.depth {m : Code} {x a₁ : Conf × Ghost (core.F.at core.C)} (h : core.Entering m x a₁) :
    depthC core.F core.C none a₁.1.t = depthC core.F core.C none x.1.t + 1 :=
  h.2.2.2

end FrameCore

end Verification.TolerantFrames.ReadOnly
