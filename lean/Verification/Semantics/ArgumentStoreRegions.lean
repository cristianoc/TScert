import Verification.Semantics.ClosedFootprints
import Verification.Semantics.IndexFacts
import Verification.Semantics.ExceptionalPosts
import Verification.Semantics.FootprintStability

/-! Store regions read from entry values through data-field paths. A region
excepts the store location alone. Element locations remain subject to the
closed footprint. -/
namespace Verification.Footprints

/-- A call position (`0` is the receiver) and a path of own data fields. -/
structure ArgumentStoreRegion where
  position : Nat
  path : List String
  deriving Repr, DecidableEq

/-- The store selected in the entry heap. A failed read selects no location. -/
def ArgumentStoreRegion.resolve (r : ArgumentStoreRegion) (ρ : Env) (h : Heap) : Option Nat :=
  (HeapKnowledge.readPath h (ρ r.position) r.path).bind storeOf

/-- A footprint on all old locations except the selected entry stores. -/
def ArgumentStoreRegionsWithin (c : Closed) (regions : List ArgumentStoreRegion)
    (ρ : Env) (entry after : Heap) : Prop :=
  c.HoldsOn (fun l => ∀ r ∈ regions, r.resolve ρ entry ≠ some l) entry after

/-- Separation of a path's selected store from another value's store.
Undefined stores give no separation witness. -/
def StoreApart (h : Heap) (x : Val) (path : List String) (y : Val) : Prop :=
  ∃ v s t, HeapKnowledge.readPath h x path = some v ∧ storeOf v = some s ∧
    storeOf y = some t ∧ s ≠ t

/-- Every location on a path has a contract fixing the value read there.
The final value may have a mutable array store. -/
inductive StablePath {n : Nat} (W : WorldT n) : Val → List String → Val → Prop where
  | nil : StablePath W v [] v
  | cons {fs code oid field l c v path result} :
      fs.lookup (.str field) = some l → lookup W l = some c → CtrStable c v →
      StablePath W v path result → StablePath W (.objAt fs code oid) (field :: path) result

/-- Dropping the step budget and extending the world retains the fixed path. -/
theorem StablePath.transfer {n m : Nat} {W : WorldT n} {U : WorldT m} {x path v}
    (hp : StablePath W x path v) (hm : m ≤ n) (hx : WExt (trunc m hm W) U) :
    StablePath U x path v := by
  induction hp with
  | nil => exact .nil
  | cons hf hl hc _ ih =>
    exact .cons hf (WExt_lookup hx (lookup_trunc hm W _ _ hl)) (hc.restrict hm) ih

/-- A heap meeting the path's contracts reads its fixed value. -/
theorem StablePath.read {n : Nat} {W : WorldT n} {h x path v}
    (hp : StablePath W x path v) (hn : 0 < n) (hh : HeapOk n W h) :
    HeapKnowledge.readPath h x path = some v := by
  induction hp with
  | nil => rfl
  | cons hf hl hc _ ih =>
    rw [HeapKnowledge.readPath_cons hf (hh.stable_value hn hl hc)]
    exact ih

/-- Stable paths survive normal and exceptional returns by the heap
invariant. This does not supply a footprint guarantee on a throw. -/
theorem StablePath.frame {Ξ T Q R x path v} : ∀ {n W h t},
    StablePath W x path v → HeapOk n W h →
    HeapObservations.SafePostExc Ξ T Q R n W h t →
    HeapObservations.SafePostExc Ξ T
      (fun h' u => Q h' u ∧ HeapKnowledge.readPath h' x path = some v)
      (fun h' => R h' ∧ HeapKnowledge.readPath h' x path = some v) n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hp hh hs
    rcases hs with (⟨hv, ht, hq⟩ | ⟨hr, hR⟩) | ⟨U, h', t', hx, hu, st, hh', hs'⟩
    · exact .inl (.inl ⟨hv, ht, hq, hp.read (Nat.zero_lt_succ n) hh⟩)
    · exact .inl (.inr ⟨hr, hR, hp.read (Nat.zero_lt_succ n) hh⟩)
    · exact .inr ⟨U, h', t', hx, hu, st, hh',
        ih (hp.transfer (Nat.le_succ n) hx) hh' hs'⟩

theorem ArgumentStoreRegion.resolve_nil (i : Nat) (ρ : Env) (h : Heap) :
    (ArgumentStoreRegion.mk i []).resolve ρ h = storeOf (ρ i) := rfl

/-- Fixed protected locations compose even when intermediate heaps grow. -/
theorem Closed.HoldsOn.trans_on {c : Closed} {P : Nat → Prop} {h₀ h h' : Heap}
    (h₁ : c.HoldsOn P h₀ h) (h₂ : c.HoldsOn (fun l => l < h₀.length ∧ P l) h h') :
    c.HoldsOn P h₀ h' := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun l v hl hv => ?_⟩
  obtain ⟨v₁, hv₁, hc₁⟩ := h₁.2 l v hl hv
  obtain ⟨v₂, hv₂, hc₂⟩ := h₂.2 l v₁ ⟨(List.getElem?_eq_some_iff.mp hv).1, hl⟩ hv₁
  refine ⟨v₂, hv₂, ?_⟩
  by_cases hany : c.at v = .any
  · rw [hany]; trivial
  · have hclass := Change.Holds.same_class hany hc₁ .store
    have heq : c.at v₁ = c.at v := by simp only [Cls.has] at hclass; simp only [Closed.at, hclass]
    rw [heq] at hc₂
    exact hc₁.trans h₁.1 hc₂

/-- A nested call composes when its selected stores agree with entry's.
The agreement is an obligation on paths, independent of the footprint. -/
theorem ArgumentStoreRegionsWithin.trans {c : Closed} {regions : List ArgumentStoreRegion}
    {ρ : Env} {entry middle after : Heap}
    (h₁ : ArgumentStoreRegionsWithin c regions ρ entry middle)
    (h₂ : ArgumentStoreRegionsWithin c regions ρ middle after)
    (hs : ∀ r ∈ regions, r.resolve ρ middle = r.resolve ρ entry) :
    ArgumentStoreRegionsWithin c regions ρ entry after := by
  apply h₁.trans_on
  exact h₂.weaken (fun l hl r hr => by rw [hs r hr]; exact hl.2 r hr)

/-- A nested call may select entry stores or stores allocated since entry.
The actuals and the paths of the nested call may differ from the caller's. -/
theorem ArgumentStoreRegionsWithin.nested {c : Closed}
    {regions nested : List ArgumentStoreRegion} {ρ actuals : Env} {entry middle after : Heap}
    (h₁ : ArgumentStoreRegionsWithin c regions ρ entry middle)
    (h₂ : ArgumentStoreRegionsWithin c nested actuals middle after)
    (hs : ∀ r ∈ nested, ∀ l, r.resolve actuals middle = some l → l < entry.length →
      ∃ outer ∈ regions, outer.resolve ρ entry = some l) :
    ArgumentStoreRegionsWithin c regions ρ entry after := by
  apply h₁.trans_on
  apply h₂.weaken
  intro l hl r hr heq
  obtain ⟨outer, hm, he⟩ := hs r hr l heq hl.1
  exact hl.2 outer hm he

/-- A receiver-store call is a regional call at the empty receiver path. -/
theorem ArgumentStoreRegionsWithin.receiver {c : Closed} {ρ : Env} {before after : Heap}
    (h : c.HoldsOn (fun l => storeOf (ρ 0) ≠ some l) before after) :
    ArgumentStoreRegionsWithin c [⟨0, []⟩] ρ before after := by
  apply h.weaken
  intro l hl
  exact hl ⟨0, []⟩ (by simp)

/-- The caller's separated array store meets the closed footprint. -/
theorem ArgumentStoreRegionsWithin.frame_store {c : Closed} {regions : List ArgumentStoreRegion}
    {ρ : Env} {entry after : Heap} {y : Val} {s : Nat} {ls : List (Option Nat)}
    (hw : ArgumentStoreRegionsWithin c regions ρ entry after)
    (ha : ∀ r ∈ regions, StoreApart entry (ρ r.position) r.path y)
    (hy : storeOf y = some s) (hl : entry[s]? = some (.arr ls)) :
    ∃ v, after[s]? = some v ∧ c.store.Holds entry.length (.arr ls) v := by
  apply hw.2 s (.arr ls) _ hl
  intro r hr heq
  obtain ⟨v, a, b, hv, hvs, hys, hne⟩ := ha r hr
  have hb : b = s := Option.some.inj (hys.symm.trans hy)
  have has : a = s := by
    simpa [ArgumentStoreRegion.resolve, hv, hvs] using heq
  exact hne (has.trans hb.symm)

/-- A kept store retains its exact length across the regional call. -/
theorem ArgumentStoreRegionsWithin.frame_length {c : Closed} {regions : List ArgumentStoreRegion}
    {ρ : Env} {entry after : Heap} {y : Val} {n : Int}
    (hw : ArgumentStoreRegionsWithin c regions ρ entry after)
    (ha : ∀ r ∈ regions, StoreApart entry (ρ r.position) r.path y)
    (hc : c.store = .keep) (hn : HeapKnowledge.lengthOf entry y = some n) :
    HeapKnowledge.lengthOf after y = some n := by
  obtain ⟨s, ls, hy, hl, rfl, hm⟩ := HeapKnowledge.lengthOf_store hn
  obtain ⟨v, hv, hchange⟩ := hw.frame_store ha hy hl
  rw [hc] at hchange
  change v = .arr ls at hchange
  subst v
  exact HeapKnowledge.lengthOf_of_store hy hv hm

/-- A growing store retains every dense prefix, hence the corresponding
lower bound on length. -/
theorem ArgumentStoreRegionsWithin.frame_densePrefix {c : Closed}
    {regions : List ArgumentStoreRegion} {ρ : Env} {entry after : Heap}
    {y : Val} {s n : Nat} {ls : List (Option Nat)}
    (hw : ArgumentStoreRegionsWithin c regions ρ entry after)
    (ha : ∀ r ∈ regions, StoreApart entry (ρ r.position) r.path y)
    (hc : c.store = .grow) (hy : storeOf y = some s)
    (hl : entry[s]? = some (.arr ls)) (hd : DensePrefix n ls) :
    ∃ ls', after[s]? = some (.arr ls') ∧ DensePrefix n ls' := by
  obtain ⟨v, hv, hchange⟩ := hw.frame_store ha hy hl
  rw [hc] at hchange
  rcases hchange with heq | ⟨a, b, heq, rfl, hprefix, _⟩ | hscalar
  · subst v; exact ⟨ls, hv, hd⟩
  · cases heq; exact ⟨b, hv, hprefix n hd⟩
  · simp [ScalarStep, isArr] at hscalar

/-- Re-reading a preserved path keeps its store separation. -/
theorem StoreApart.transport {h h' : Heap} {x y : Val} {path : List String}
    (ha : StoreApart h x path y)
    (hp : ∀ v, HeapKnowledge.readPath h x path = some v → HeapKnowledge.readPath h' x path = some v) :
    StoreApart h' x path y := by
  obtain ⟨v, s, t, hv, hs, ht, hne⟩ := ha
  exact ⟨v, s, t, hp v hv, hs, ht, hne⟩

/-- A stable path retains store separation on normal and exceptional returns.
Preservation of another fact additionally needs the call's footprint there. -/
theorem StoreApart.stable_path_frame {Ξ T Q R x path v y s t n W h term}
    (hp : StablePath W x path v) (hs : storeOf v = some s) (ht : storeOf y = some t)
    (hne : s ≠ t) (hh : HeapOk n W h)
    (hr : HeapObservations.SafePostExc Ξ T Q R n W h term) :
    HeapObservations.SafePostExc Ξ T
      (fun h' u => Q h' u ∧ StoreApart h' x path y)
      (fun h' => R h' ∧ StoreApart h' x path y) n W h term := by
  apply HeapObservations.SafePostExc.weaken _ _ (hp.frame hh hr)
  · intro h' u hq
    exact ⟨hq.1, v, s, t, hq.2, hs, ht, hne⟩
  · intro h' hq
    exact ⟨hq.1, v, s, t, hq.2, hs, ht, hne⟩

/-- An alias of the selected array supplies no store-separation witness. -/
theorem StoreApart.not_alias {h x path y}
    (hp : HeapKnowledge.readPath h x path = some y) : ¬ StoreApart h x path y := by
  rintro ⟨v, s, t, hv, hs, ht, hne⟩
  have he : y = v := Option.some.inj (hp.symm.trans hv)
  subst v
  exact hne (Option.some.inj (hs.symm.trans ht))

/-- A stable own field keeps separation on every normal return. -/
theorem StoreApart.stable_frame {Ξ T Q} {fs : List (PropKey × Nat)} {code : CallCode}
    {oid l : Nat} {field : String} {v y : Val} {s t : Nat} {n W h term} {c : Ctr n}
    (hf : fs.lookup (.str field) = some l) (hl : lookup W l = some c) (hc : CtrStable c v)
    (hs : storeOf v = some s) (ht : storeOf y = some t) (hne : s ≠ t)
    (hh : HeapOk n W h) (hr : HeapObservations.SafePost Ξ T Q n W h term) :
    HeapObservations.SafePost Ξ T
      (fun h' u => Q h' u ∧ StoreApart h' (.objAt fs code oid) [field] y) n W h term := by
  apply HeapObservations.weaken _ (HeapObservations.stable_frame hl hc hh hr)
  intro h' u hp
  exact ⟨hp.1, v, s, t, by simp [HeapKnowledge.readPath, hf, hp.2], hs, ht, hne⟩

/-! ## The regions as entries of the regional footprint -/

/-- The region's entry: its selected store's location, at `any`. -/
def ArgumentStoreRegion.entry (r : ArgumentStoreRegion) : Region × Change :=
  (.path r.position r.path arrayStoreKey, .any)

theorem ArgumentStoreRegion.mem_entry (r : ArgumentStoreRegion) (ρ : Env) (h : Heap) (l : Nat) :
    r.entry.1.mem ρ h l = true ↔ r.resolve ρ h = some l := by
  simp only [ArgumentStoreRegion.entry, Region.mem, ArgumentStoreRegion.resolve]
  cases HeapKnowledge.readPath h (ρ r.position) r.path <;> simp [storeOf]

/-- **The bridge.** A closed footprint excepting the selected stores is the
regional footprint of its two classes and each selected store at `any`. -/
theorem ArgumentStoreRegionsWithin.iff_post {c : Closed} {regions : List ArgumentStoreRegion}
    {ρ : Env} {entry after : Heap} :
    ArgumentStoreRegionsWithin c regions ρ entry after ↔
      Post (c.fp ++ regions.map ArgumentStoreRegion.entry) ρ entry after := by
  constructor
  · intro hw
    refine ⟨hw.1, fun l v hv => ?_⟩
    have hl := (List.getElem?_eq_some_iff.mp hv).1
    by_cases hsel : ∀ r ∈ regions, r.resolve ρ entry ≠ some l
    · obtain ⟨v', hv', hc⟩ := hw.2 l v hsel hv
      refine ⟨v', hv', ?_⟩
      rcases (Closed.allowed_iff (ρ := ρ) (v' := v') hv).mpr hc with h | ⟨e, he, hm, hh⟩
      · exact .inl h
      · exact .inr ⟨e, List.mem_append_left _ he, hm, hh⟩
    · obtain ⟨r, hr, hres⟩ : ∃ r ∈ regions, r.resolve ρ entry = some l :=
        Classical.byContradiction fun hn => hsel fun r hr hres => hn ⟨r, hr, hres⟩
      have hla : l < after.length := Nat.lt_of_lt_of_le hl hw.1
      refine ⟨after[l], List.getElem?_eq_getElem hla, .inr
        ⟨r.entry, List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩),
          (r.mem_entry ρ entry l).mpr hres, trivial⟩⟩
  · intro hp
    refine ⟨hp.1, fun l v hsel hv => ?_⟩
    obtain ⟨v', hv', ha⟩ := hp.2 l v hv
    refine ⟨v', hv', (Closed.allowed_iff (ρ := ρ) hv).mp ?_⟩
    rcases ha with h | ⟨e, he, hm, hh⟩
    · exact .inl h
    · rcases List.mem_append.mp he with he | he
      · exact .inr ⟨e, he, hm, hh⟩
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
        exact absurd ((r.mem_entry ρ entry l).mp hm) (hsel r hr)

/-- A kept store retains its exact length across a regional footprint whose
selected stores are apart from it (`frame_length` on `Post`). -/
theorem ArgumentStoreRegion.post_frame_length {c : Closed} {regions : List ArgumentStoreRegion}
    {ρ : Env} {entry after : Heap} {y : Val} {n : Int}
    (hp : Post (c.fp ++ regions.map ArgumentStoreRegion.entry) ρ entry after)
    (ha : ∀ r ∈ regions, StoreApart entry (ρ r.position) r.path y)
    (hc : c.store = .keep) (hn : HeapKnowledge.lengthOf entry y = some n) :
    HeapKnowledge.lengthOf after y = some n :=
  (ArgumentStoreRegionsWithin.iff_post.mpr hp).frame_length ha hc hn

/-- Regional footprints at unchanged selected stores compose (`trans` on
`Post`). -/
theorem ArgumentStoreRegion.post_trans {c : Closed} {regions : List ArgumentStoreRegion}
    {ρ : Env} {entry middle after : Heap}
    (h₁ : Post (c.fp ++ regions.map ArgumentStoreRegion.entry) ρ entry middle)
    (h₂ : Post (c.fp ++ regions.map ArgumentStoreRegion.entry) ρ middle after)
    (hs : ∀ r ∈ regions, r.resolve ρ middle = r.resolve ρ entry) :
    Post (c.fp ++ regions.map ArgumentStoreRegion.entry) ρ entry after :=
  ArgumentStoreRegionsWithin.iff_post.mp
    ((ArgumentStoreRegionsWithin.iff_post.mpr h₁).trans (ArgumentStoreRegionsWithin.iff_post.mpr h₂) hs)

/-- Store separation of a path from a slot is the separation knowledge
`storeApart` states: the path's store location is not the slot's. -/
theorem StoreApart.sep {h : Heap} {ρ : Env} {x y : Nat} {p : List String}
    (ha : StoreApart h (ρ x) p (ρ y)) :
    ∀ l, (Region.path x p arrayStoreKey).mem ρ h l = true →
      (Region.field y arrayStoreKey).mem ρ h l = false := by
  intro l hm
  obtain ⟨v, s, t, hv, hs, ht, hne⟩ := ha
  simp only [Region.mem, hv, beq_iff_eq] at hm
  simp only [storeOf] at hs ht
  rw [hs] at hm
  cases hm
  simp only [Region.mem, ht]
  simpa [beq_iff_eq] using fun h => hne h.symm

end Verification.Footprints
