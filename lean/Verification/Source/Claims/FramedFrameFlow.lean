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
capture sites and `O` closed (`capClosedB`), its marks (`marksB`), and the initialization's node
expressions free of runs and, with the realm's values, meeting layout
provenance at the flow's layouts (`layP`) and the residual invariant
(`WOk`, decided by `wokB`). -/

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

/-! ## The residual invariant, decided -/

mutual
/-- **The residual invariant**, decided (`WOk`). -/
def wokB : Tm → Bool
  | .frame E _ t L d _ _ _ =>
    (writesK t).all (fun k => decide (k ∈ E.flatMap writesK)) && wokB t && woksB E && plainArgsB L &&
      ((writesK d).isEmpty && wokB d)
  | .goto E _ _ L d _ => woksB E && plainArgsB L && ((writesK d).isEmpty && wokB d)
  | .objAt _ (.bound t r pre) _ => ((writesK t).isEmpty && wokB t) && ((writesK r).isEmpty && wokB r) && plainArgsB pre
  | .objAt _ (.graph _ E _ _ caps _ _ _) _ => woksB E && plainArgsB caps
  | .makeAt (.bound t r pre) _ xs =>
    (((writesK t).isEmpty && wokB t) && ((writesK r).isEmpty && wokB r) && plainArgsB pre) && woksB xs
  | .makeAt (.graph _ E _ _ caps _ _ _) _ xs => (woksB E && plainArgsB caps) && woksB xs
  | .makeAt .absent _ xs => woksB xs
  | .makeAt (.view _ _ _) _ xs => woksB xs
  | .arrLit xs => woksB xs
  | .invoke f r args => wokB f && wokB r && woksB args
  | .construct f args => wokB f && woksB args
  | .letE a b => wokB a && wokB b
  | .indexAt a b => wokB a && wokB b
  | .writeAt _ a b => wokB a && wokB b
  | .arith _ a b => wokB a && wokB b
  | .elemAt a b => wokB a && wokB b
  | .merge _ a b => wokB a && wokB b
  | .makeKey a b => wokB a && wokB b
  | .ite a b c => wokB a && wokB b && wokB c
  | .setElem a b c => wokB a && wokB b && wokB c
  | .readAt _ a => wokB a
  | .test _ a => wokB a
  | .lenOf a => wokB a
  | .spread a => wokB a
  | .throw a => wokB a
  | _ => true
termination_by structural t => t

/-- The invariant at each term of a list, decided. -/
def woksB : List Tm → Bool
  | [] => true
  | x :: xs => wokB x && woksB xs
termination_by structural xs => xs

/-- Each term of a list performs no write and meets the invariant, decided. -/
def plainArgsB : List Tm → Bool
  | [] => true
  | x :: xs => ((writesK x).isEmpty && wokB x) && plainArgsB xs
termination_by structural xs => xs
end

@[simp] theorem woksB_iff : ∀ {xs : List Tm}, woksB xs = true ↔ ∀ x ∈ xs, wokB x = true
  | [] => by simp [woksB]
  | x :: xs => by simp [woksB, woksB_iff]

@[simp] theorem plainArgsB_iff : ∀ {xs : List Tm},
    plainArgsB xs = true ↔ ∀ x ∈ xs, writesK x = [] ∧ wokB x = true
  | [] => by simp [plainArgsB]
  | x :: xs => by simp [plainArgsB, plainArgsB_iff]

/-- **The decided invariant is the invariant** (proved, by induction on
the term). -/
theorem wokB_sound (t : Tm) : wokB t = true → WOk t := by
  induction t using Tm.induct with
  | _ =>
    intro h
    simp only [wokB, WOk, woksB_iff, plainArgsB_iff, wOks_iff, plainArgs_iff, Plain, Bool.and_eq_true,
      List.isEmpty_iff, List.all_eq_true, decide_eq_true_eq] at h ⊢
    try grind

/-- **A plain term**, decided. -/
def plainB (t : Tm) : Bool := (writesK t).isEmpty && wokB t

theorem plainB_sound {t : Tm} (h : plainB t = true) : Plain t := by
  simp only [plainB, Bool.and_eq_true, List.isEmpty_iff] at h
  exact ⟨h.1, wokB_sound t h.2⟩

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
its facts (`FFlow.check`), its marks (`marksB`), its tokens sites (`tokensSomeB`), its codes
lowered (`codesLoweredB`), the closure of its capture sites and `O` closed
(`capClosedB`), and each node expression of the initialization and each
value of the realm meeting layout provenance at the flow's layouts and the
residual invariant, each node expression of the initialization free of
runs, each value of the realm plain. -/
def frameFlowB (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (realm : Heap) (initE : List Tm) : Bool :=
  let S := captureSites F lay ++ F.O
  F.check && F.marksB && tokensSomeB F && codesLoweredB F &&
    capClosedB F (tokenCaps F lay) S (capClose F (tokenCaps F lay) S) &&
    initE.all (fun e => layP (layQ F lay) e && wokB e && free false e) &&
    realm.all (fun v => layP (layQ F lay) v && plainB v)

/-- **What the checks of the frame's flow give** (proved): the flow's
facts and marks, its tokens and lowered codes, the closure of its capture sites and
`O` closed, layout provenance and the residual invariant of the
initialization's node expressions and of the realm's heap, and the
initialization's node expressions free of runs. -/
theorem frameFlowB_sound {F : FFlow P} {lay : List (Nat × Bool × Nat × Nat)} {realm : Heap} {initE : List Tm}
    (h : frameFlowB F lay realm initE = true) :
    F.flow.Facts ∧ F.marksB = true ∧ tokensSomeB F = true ∧ codesLoweredB F = true ∧
      capClosedB F (tokenCaps F lay) (captureSites F lay ++ F.O)
        (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O)) = true ∧
      (∀ e ∈ initE, layP (layQ F lay) e = true) ∧ (∀ e ∈ initE, WOk e) ∧
      HeapLay (layQ F lay) realm ∧ HeapW realm ∧ (∀ e ∈ initE, free false e = true) := by
  simp only [frameFlowB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hc, hm⟩, ht⟩, hl⟩, hT⟩, hi⟩, hr⟩ := h
  exact ⟨FFlow.check_sound hc, hm, ht, hl, hT, fun e he => (hi e he).1.1, fun e he => wokB_sound e (hi e he).1.2,
    fun v hv => (hr v hv).1, fun v hv => plainB_sound (hr v hv).2, fun e he => (hi e he).2⟩
end

end Verification.SourceClaimJson
