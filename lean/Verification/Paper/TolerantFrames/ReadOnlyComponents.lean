import Verification.Paper.TolerantFrames.ReadOnlySteps

/-! # Read-only handles: a laminar family of components

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`,
"Components", "Frames and whose code runs", "Marks, one per allocation site
and component"): the components of a program form a laminar family, any
two nested or disjoint, named as the calculus's frame tags name them
(`ComponentTag`). Each component `C` is read as a package (`Family.at`):
its sites are the sites of `C`'s code, nested components' included, each
with its mark for `C`; every definition and lemma of `ReadOnlyRegion`,
`ReadOnlyFrame` and `ReadOnlyChecks` stated for a package holds at
`F.at C`, with its own `E_C`, `A_C`, `B_C`, `Ψ_C`, members and runs.

- A frame running a nested component's code runs the enclosing one's
  (`Family.runs_mono`), so a step outside `C` is outside every component
  nested in it (`Family.outside_mono`).
- A component's storage includes its nested components': a location a
  nested component's site allocated is classified by `C`'s mark, never as
  outside storage (`Family.nested_origin`), and with the marks consistent
  along the family, nested local storage is in `R_C`
  (`Family.nested_local_inR`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

/-- **A laminar family of components** (the draft, Components): the
relation "nested in", reflexive and transitive, any two components nested
or disjoint; each allocation site's innermost component; and each site's
mark for each component. -/
structure Family where
  Site : Type
  nested : Nat → Nat → Prop
  refl : ∀ c, nested c c
  trans : ∀ a b c, nested a b → nested b c → nested a c
  laminar : ∀ a b, nested a b ∨ nested b a ∨ ∀ c, ¬ (nested c a ∧ nested c b)
  siteOf : Site → ComponentTag
  mark : Site → Nat → Mark

namespace Family
variable (F : Family)

/-- **A frame runs `C`'s code** (the draft, "Frames and whose code runs")
when its innermost component is `C` or nested in `C`. -/
def Runs (t : ComponentTag) (C : Nat) : Prop := ∃ c, t = some c ∧ F.nested c C

/-- **The component `C` read as a package**: the sites of `C`'s code, each
with its mark for `C`. -/
def «at» (C : Nat) : Package := ⟨{ s : F.Site // F.Runs (F.siteOf s) C }, fun s => F.mark s.1 C⟩

open Classical in
/-- A location's site seen from `C`: a site of `C`'s code, or outside
storage. -/
noncomputable def restrict (C : Nat) (site : Nat → Option F.Site) : Nat → Option (F.at C).Site :=
  fun l => match site l with
    | some s => if h : F.Runs (F.siteOf s) C then some ⟨s, h⟩ else none
    | none => none

variable {F}

/-- **A frame running a nested component's code runs the enclosing
one's.** -/
theorem runs_mono {t : ComponentTag} {D C : Nat} (hDC : F.nested D C) (h : F.Runs t D) : F.Runs t C :=
  let ⟨c, ht, hc⟩ := h
  ⟨c, ht, F.trans c D C hc hDC⟩

/-- **A step outside `C` is outside every component nested in `C`.** -/
theorem outside_mono {t : ComponentTag} {D C : Nat} (hDC : F.nested D C) (h : ¬ F.Runs t C) : ¬ F.Runs t D :=
  fun hD => h (runs_mono hDC hD)

/-- **Two components' code**: of nested components, the inner's code is the
outer's; of disjoint ones, no frame runs both. -/
theorem runs_laminar {t : ComponentTag} (a b : Nat) (ha : F.Runs t a) (hb : F.Runs t b) :
    F.nested a b ∨ F.nested b a := by
  rcases F.laminar a b with h | h | h
  · exact .inl h
  · exact .inr h
  · obtain ⟨c, rfl, hc⟩ := ha
    obtain ⟨c', hc', hc'b⟩ := hb
    cases hc'
    exact (h c ⟨hc, hc'b⟩).elim

/-- **A component's storage includes its nested components'**: a location
allocated at a site of a component `D` nested in `C` is classified by the
site's mark for `C`, never as outside storage of `C`. -/
theorem nested_origin {C D : Nat} (hDC : F.nested D C) {site : Nat → Option F.Site} {g : Ghost (F.at C)}
    (hg : g.site = F.restrict C site) {l : Nat} {s : F.Site} (hs : site l = some s)
    (hD : F.Runs (F.siteOf s) D) : g.origin l = some (F.mark s C) := by
  have hC : F.Runs (F.siteOf s) C := runs_mono hDC hD
  simp only [Ghost.origin, hg, restrict, hs, dif_pos hC]
  rfl

/-- The order of the marks: `local ⊑ internal ⊑ exposed ⊑ released`. -/
def Mark.rank : Mark → Nat
  | .local => 0
  | .internal => 1
  | .exposed => 2
  | .released => 3

/-- **Consistent marks along the family**: a site's mark for an enclosing
component is at most its mark for a nested one. A crossing of the
enclosing component reaches what crossed the nested one, so what the nested
component keeps local is local for the enclosing one, and what it exposes
is at most exposed. The pass checks each component's marks. -/
def MarksConsistent (F : Family) : Prop :=
  ∀ s D C, F.nested D C → F.Runs (F.siteOf s) D → Mark.rank (F.mark s C) ≤ Mark.rank (F.mark s D)

/-- **Nested local storage is in `R_C`.** -/
theorem nested_local_inR (hm : MarksConsistent F) {C D : Nat} (hDC : F.nested D C)
    {site : Nat → Option F.Site} {g : Ghost (F.at C)} (hg : g.site = F.restrict C site) {l : Nat}
    {s : F.Site} (hs : site l = some s) (hD : F.Runs (F.siteOf s) D) (hloc : F.mark s D = .local) :
    g.InR l := by
  have hr := hm s D C hDC hD
  rw [hloc] at hr
  have hc : F.mark s C = .local := by
    cases h : F.mark s C <;> rw [h] at hr <;> simp [Mark.rank] at hr ⊢
  exact .inl (by rw [nested_origin hDC hg hs hD, hc])

/-- **Nested exposed storage is local, internal or exposed for `C`.** -/
theorem nested_exposed (hm : MarksConsistent F) {C D : Nat} (hDC : F.nested D C) {s : F.Site}
    (hD : F.Runs (F.siteOf s) D) (hex : F.mark s D = .exposed) : F.mark s C ≠ .released := by
  have hr := hm s D C hDC hD
  rw [hex] at hr
  intro h
  rw [h] at hr
  simp [Mark.rank] at hr

end Family

end Verification.TolerantFrames.ReadOnly
