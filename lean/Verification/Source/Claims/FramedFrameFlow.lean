import Verification.Source.Claims.FramedFlow
import Verification.Paper.TolerantFrames.ReadOnlyLayouts
import Verification.Paper.TolerantFrames.ReadOnlyWriteKinds

/-! # The flow at the frame's sites, checked

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "What the pass checks"). The frame of
a framed plan reads its component's flow over the sites of the family of
one component $`C`$ (`oneComponent`), whose tags of $`C`$'s code are those
the family runs at $`C`$ (`Family.ofC`). That package and the one whose
tags are decided (`framePkg`, a tag runs $`C`$'s code where it is $`C`$)
have the same sites and marks and equal tags (`framePkg_ofC`), so a check
of the flow at the decided package is the check at the frame's
(`frame_transport`).

The checks of the flow the frame reads, over the component alone
(`frameFlowB`): the flow's facts (`FFlow.check`), its tokens sites
(`tokensSomeB`), its codes lowered (`codesLoweredB`), the closure of its
capture sites and `O` closed (`capClosedB`) and its marks (`marksB`). -/

namespace Verification.SourceClaimJson
open Verification Verification.TolerantFrames.ReadOnly ControlFlow

/-- A numbered family's sites seen from a component are numbers, so
equality of them is decided. -/
instance (N : NumberedFamily) (C : Nat) : DecidableEq (N.family.at C).Site :=
  show DecidableEq {s : Nat // N.family.Runs (N.family.siteOf s) C} from inferInstance

/-- A numbered family's sites seen from a component are hashed by their
numbers. -/
instance (N : NumberedFamily) (C : Nat) : Hashable (N.family.at C).Site :=
  ⟨fun s => @hash Nat _ (show {s : Nat // N.family.Runs (N.family.siteOf s) C} from s).1⟩

/-! ## The frame's package, its tags decided -/

/-- **The frame's package, its tags decided**: the sites and marks of the
family of one component `C` (`oneComponent`) seen from `C`, and the tags of
`C`'s code those equal to `C`. -/
abbrev framePkg (C : Nat) (mark : Nat → Mark) : Package :=
  ⟨((oneComponent C mark).family.at C).Site, fun s => mark s.1, fun t => t == some C⟩

/-- **The tags the family of one component runs at `C`** are those equal
to `C` (proved). -/
theorem framePkg_ofC (C : Nat) (mark : Nat → Mark) :
    (fun t : ComponentTag => t == some C) = (oneComponent C mark).family.ofC C := by
  funext t
  simp only [Family.ofC, Family.Runs, oneComponent, NumberedFamily.family]
  cases t with
  | none => simp
  | some c => by_cases h : c = C <;> simp [h]

/-- **A component's flow at the frame's sites, its tags decided**: its
sites renamed into the family of one component (`oneComponent.site`). -/
def frameFlowOf {ofC : ComponentTag → Bool} {O : List (Option Nat)} (C : Nat) (F : FFlow (markedPackage ofC O)) :
    FFlow (framePkg C (markedPackage ofC O).mark) :=
  F.mapSites (Q := framePkg C (markedPackage ofC O).mark) (oneComponent.site C (markedPackage ofC O).mark) (·.1)

/-- **A property of a renamed flow at one package's tags is the property
at equal tags** (proved). -/
theorem ofC_transport {S : Type} {mk : S → Mark} {o₁ o₂ : ComponentTag → Bool} (he : o₁ = o₂) {P₀ : Package}
    (F₀ : FFlow P₀) (f : P₀.Site → S) (g : S → P₀.Site)
    (Φ : (o : ComponentTag → Bool) → FFlow (⟨S, mk, o⟩ : Package) → Prop)
    (h : Φ o₁ (F₀.mapSites (Q := ⟨S, mk, o₁⟩) f g)) : Φ o₂ (F₀.mapSites (Q := ⟨S, mk, o₂⟩) f g) := by
  subst he; exact h

/-- **A property of the flow at the decided tags is the property at the
frame's** (proved, the two tags equal, `framePkg_ofC`): any property `Φ`
of the renamed flow, read at a package with the frame's sites and marks
and some tags. -/
theorem frame_transport {ofC : ComponentTag → Bool} {O : List (Option Nat)} (C : Nat) (F : FFlow (markedPackage ofC O))
    (Φ : (o : ComponentTag → Bool) →
      FFlow (⟨((oneComponent C (markedPackage ofC O).mark).family.at C).Site,
        fun s => (markedPackage ofC O).mark s.1, o⟩ : Package) → Prop)
    (h : Φ (fun t => t == some C) (frameFlowOf C F)) :
    Φ ((oneComponent C (markedPackage ofC O).mark).family.ofC C)
      (F.mapSites (Q := ⟨((oneComponent C (markedPackage ofC O).mark).family.at C).Site,
        fun s => (markedPackage ofC O).mark s.1, (oneComponent C (markedPackage ofC O).mark).family.ofC C⟩)
        (oneComponent.site C (markedPackage ofC O).mark) (·.1)) :=
  ofC_transport (framePkg_ofC C (markedPackage ofC O).mark) F _ _ Φ h

/-! ## The checks of the frame's flow -/

section
variable {P : Package} [DecidableEq P.Site] [Hashable P.Site]

/-- **The checks of the flow the frame reads, over the component alone**:
its facts (`FFlow.check`), its marks (`marksB`), its tokens sites
(`tokensSomeB`), its codes holding no located value (`codesLoweredB`), and
the closure of its capture sites and `O` closed (`capClosedB`). -/
def frameFlowB (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) : Bool :=
  let S := captureSites F lay ++ F.O
  F.check && F.marksB && tokensSomeB F && codesLoweredB F &&
    capClosedB F (tokenCaps F lay) S (capClose F (tokenCaps F lay) S)

/-- **What the checks of the frame's flow give** (proved): the flow's
facts and marks, its tokens and the codes holding no located value, and
the closure of its capture sites and `O` closed. -/
theorem frameFlowB_sound {F : FFlow P} {lay : List (Nat × Bool × Nat × Nat)} (h : frameFlowB F lay = true) :
    F.flow.Facts ∧ F.marksB = true ∧ tokensSomeB F = true ∧ codesLoweredB F = true ∧
      capClosedB F (tokenCaps F lay) (captureSites F lay ++ F.O)
        (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O)) = true := by
  simp only [frameFlowB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hc, hm⟩, ht⟩, hl⟩, hT⟩ := h
  exact ⟨FFlow.check_sound hc, hm, ht, hl, hT⟩
end

end Verification.SourceClaimJson
