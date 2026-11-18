import Verification.Paper.TolerantFrames.ReadOnlyChecks
import Verification.Source.ComponentChecks

/-! # Read-only handles: what the checks of the wire give a step

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
checks the rule requires"): the checks (K) and (O) the verifier runs over a
component family's description (`ComponentChecks`), read at a step of a
component's code. A package's sites are read as the description's
(`WireSites`): each site of the package is a site of the description, with
the description's mark for the component. The flow of the description
interprets a step (the hypotheses named `flow` below) when every location
a value of the step reaches is of a site of the value's reachable storage
in the description (`ComponentChecks.Ctx.closure`), and every location a
step writes is of a site of the store's receiver, holding a site of the
stored value's. With that interpretation:

- a crossing out whose check passes (`crossBad` empty) meets the marks
  (`crossOk_of_check`), the field `crossOk` of a step's checks (`PkgStep`);
- storage the step writes that references local storage is local where the
  contents check passes (`contentsBad` empty) and every write into outside
  storage is a crossing whose check passes (`localStores_of_check`), the
  field `localStores`;
- a value a closure of outside code binds reaches no local storage where it
  is a value of a crossing whose check passes (`localBindings_of_check`),
  the field `localBindings`;
- an install whose check passes (`installBad` empty, values entering from
  outside only read-only) is admitted (`admitted_of_check`), the premise of
  (O) `ownership`.

The interpretation of an actual step by the description is a hypothesis:
the correspondence of the paper model's steps with the front's events is
not stated. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

/-- A mark of the description read as the package's. -/
def ofWire : ComponentWire.Mark → Mark
  | .local => .local
  | .internal => .internal
  | .exposed => .exposed
  | .released => .released

/-- **A package's sites read as a description's**: each site of the package
is the description's site `ι s`, with the description's mark for the
component `C`. -/
structure WireSites (P : Package) (cx : ComponentChecks.Ctx) (C : Nat) where
  ι : P.Site → Nat
  mark : ∀ s, (cx.mark (ι s) C).map ofWire = some (P.mark s)

variable {P : Package} {cx : ComponentChecks.Ctx} {C : Nat}

/-- **The marks a passing crossing check leaves**: no reachable site of
the crossing's value is local or internal for `C`, and an exposed one only
at a read-only position. -/
theorem crossBad_mark {T : ComponentChecks.Tokens} {ro : Bool} {t : Nat}
    (h : ComponentChecks.crossBad cx C T ro = []) (ht : t ∈ (cx.closure T).sites) :
    cx.mark t C ≠ some .local ∧ cx.mark t C ≠ some .internal ∧ (cx.mark t C = some .exposed → ro = true) := by
  have hn := List.filter_eq_nil_iff.mp h t ht
  refine ⟨fun he => hn (by simp [he]), fun he => hn (by simp [he]), fun he => ?_⟩
  cases ro
  · exact absurd (by simp [he]) hn
  · rfl

/-- The package's mark of a site from the description's. -/
theorem WireSites.mark_eq (w : WireSites P cx C) {s : P.Site} {m : ComponentWire.Mark}
    (h : cx.mark (w.ι s) C = some m) : P.mark s = ofWire m := by
  have := w.mark s
  rw [h] at this
  exact (Option.some.inj this).symm

theorem ofWire_local {m : ComponentWire.Mark} (h : ofWire m = .local) : m = .local := by
  cases m <;> simp_all [ofWire]

/-- The contents check of a site that is not local for `C`. -/
theorem contentsBad_eq {t : Nat} {m : ComponentWire.Mark} (h : cx.mark t C = some m) (hm : m ≠ .local) :
    ComponentChecks.contentsBad cx t C = (cx.contents t).sites.filter fun u => cx.mark u C == some .local := by
  unfold ComponentChecks.contentsBad
  rw [h]
  cases m <;> simp_all

theorem WireSites.wire_of (w : WireSites P cx C) (s : P.Site) :
    ∃ m, cx.mark (w.ι s) C = some m ∧ P.mark s = ofWire m := by
  have hm := w.mark s
  cases h : cx.mark (w.ι s) C with
  | none => rw [h] at hm; cases hm
  | some m => exact ⟨m, rfl, w.mark_eq h⟩

/-- **(K) at a crossing**: a crossing whose value's reachable locations
are of sites of the description's reachable storage (`flow`), at a
position read-only where the description states it, meets the marks
(`CrossOk`) when its check passes. -/
theorem crossOk_of_check {tv : TypeView} (w : WireSites P cx C) {g : Ghost P} {h : Heap} {c : Crossing tv}
    {T : ComponentChecks.Tokens} {ro : Bool} (hk : ComponentChecks.crossBad cx C T ro = [])
    (hro : ro = true → tv.RO c.ty)
    (flow : ∀ l s, Reaches P.ofC h c.val l → g.site l = some s → w.ι s ∈ (cx.closure T).sites) :
    CrossOk tv g h c := by
  intro l hr
  unfold Ghost.origin
  cases hs : g.site l with
  | none => simp
  | some s =>
    obtain ⟨hl, hi, he⟩ := crossBad_mark hk (flow l s hr hs)
    obtain ⟨m, hm, hP⟩ := w.wire_of s
    simp only [Option.map_some, hP]
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
    · cases m <;> simp_all [ofWire]
    · cases m <;> simp_all [ofWire]
    · have hme : m = .exposed := by cases m <;> simp_all [ofWire]
      obtain ⟨π, hπ⟩ := hr
      exact ⟨π, hπ, [], π, rfl, hro (he (hm.trans (by rw [hme])))⟩

/-- **(K) at a write**: a location the step writes, whose new contents
reference a local location, is local where the description interprets the
write (`flow`: a write into a site's storage holds a site of that site's
contents; a write into outside storage is the value of a crossing whose
check passes, reaching the location) and the contents check passes. This is
`PkgStep.localStores`. -/
theorem localStores_of_check (w : WireSites P cx C) {mid : Ghost P} {h h' : Heap}
    (hk : ∀ t, ComponentChecks.contentsBad cx t C = [])
    (flow : ∀ x u, ¬ Same h h' x → h'[x]? = some u → ∀ a l, next u a = some l → ∀ sl, mid.site l = some sl →
      (∃ sx, mid.site x = some sx ∧ w.ι sl ∈ (cx.contents (w.ι sx)).sites) ∨
        (mid.site x = none ∧ ∃ T ro, ComponentChecks.crossBad cx C T ro = [] ∧ w.ι sl ∈ (cx.closure T).sites)) :
    ∀ x u, ¬ Same h h' x → h'[x]? = some u → ∀ a l, next u a = some l →
      mid.origin l = some .local → mid.origin x = some .local := by
  intro x u hs hu a l hn hloc
  unfold Ghost.origin at hloc ⊢
  obtain ⟨sl, hsl, hml⟩ := Option.map_eq_some_iff.mp hloc
  obtain ⟨ml, hwl, hPl⟩ := w.wire_of sl
  have hml' : ml = .local := ofWire_local (hPl.symm.trans hml)
  rcases flow x u hs hu a l hn sl hsl with ⟨sx, hsx, hc⟩ | ⟨_, T, ro, hb, ht⟩
  · rw [hsx]
    obtain ⟨mx, hwx, hPx⟩ := w.wire_of sx
    simp only [Option.map_some, hPx]
    by_cases hx : mx = .local
    · rw [hx]; rfl
    · have hb := hk (w.ι sx)
      rw [contentsBad_eq hwx hx] at hb
      have hc' := List.filter_eq_nil_iff.mp hb (w.ι sl) hc
      simp [hwl, hml'] at hc'
  · exact absurd (hwl.trans (by rw [hml'])) (crossBad_mark hb ht).1

/-- **(K) at a binding**: a location a closure of outside code reaches
through what it binds is not local where it is reached by the value of a
crossing whose check passes (`flow`, the description's crossings out at
the bindings outside code holds). This is `PkgStep.localBindings`. -/
theorem localBindings_of_check (w : WireSites P cx C) {mid : Ghost P} {h h' : Heap}
    (flow : ∀ x u, ¬ Same h h' x → h'[x]? = some u → ∀ v ∈ codeVals P.ofC u, ∀ l, Leaves P.ofC v l → ∀ sl,
      mid.site l = some sl → ∃ T ro, ComponentChecks.crossBad cx C T ro = [] ∧ w.ι sl ∈ (cx.closure T).sites) :
    ∀ x u, ¬ Same h h' x → h'[x]? = some u → ∀ v ∈ codeVals P.ofC u, ∀ l,
      Leaves P.ofC v l → mid.origin l ≠ some .local := by
  intro x u hs hu v hv l hl hloc
  unfold Ghost.origin at hloc
  obtain ⟨sl, hsl, hml⟩ := Option.map_eq_some_iff.mp hloc
  obtain ⟨ml, hwl, hPl⟩ := w.wire_of sl
  obtain ⟨T, ro, hb, ht⟩ := flow x u hs hu v hv l hl sl hsl
  have hml' : ml = .local := ofWire_local (hPl.symm.trans hml)
  exact (crossBad_mark hb ht).1 (hwl.trans (by rw [hml']))

/-- **(O) at an install**: an install whose check passes (`installBad`
empty, `installIncoming`: no value entering from outside but read-only into
the component) is admitted (`Admitted`), where every location the support
reads through the stored value is of a site of the description's storage
reachable from it, or, reached through a value entering read-only, is
released or outside storage the history protects (`flow`: the meaning of a
value reached read-only from a crossing in at a read-only type). -/
theorem admitted_of_check (w : WireSites P cx C) {st : St P} {L : Nat → Prop} {stored : ComponentChecks.Tokens}
    (hk : ComponentChecks.installBad cx C stored = [])
    (flow : ∀ l, L l → (∃ s, st.g.site l = some s ∧ w.ι s ∈ (cx.closure stored).sites) ∨ (st.g.Lent l ∧ st.g.Prot l)) :
    Admitted st L := by
  intro l hl
  rcases flow l hl with ⟨s, hs, ht⟩ | hp
  · have hn := List.filter_eq_nil_iff.mp hk (w.ι s) ht
    obtain ⟨m, hm, hP⟩ := w.wire_of s
    have ho : st.g.origin l = some (P.mark s) := by simp [Ghost.origin, hs]
    cases m with
    | «local» => exact .inr (.inl (by rw [ho, hP]; rfl))
    | exposed => exact .inl (by rw [ho, hP]; rfl)
    | internal | released => exact absurd (by simp [hm]) hn
  · exact .inr (.inr (.inr hp))

end Verification.TolerantFrames.ReadOnly
