import Verification.Semantics.StoreRegions
import Verification.Semantics.IndexFacts
import Verification.Semantics.ExceptionalPosts
import Verification.Semantics.FootprintStability

/-! Store regions read from entry values through data-field paths. A region
excepts the store location alone. Element locations remain subject to the
closed footprint. -/
namespace Verification.Footprints

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
  | zero => intro _ _ _ _ _ hs; exact hs
  | succ n ih =>
    intro W h t hp hh hs
    obtain ⟨hrf, hs⟩ := hs
    rcases hs with (⟨hv, ht, hq⟩ | ⟨hr, hR⟩) | ⟨U, h', t', hx, hu, st, hh', hs'⟩
    · exact ⟨hrf, .inl (.inl ⟨hv, ht, hq, hp.read (Nat.zero_lt_succ n) hh⟩)⟩
    · exact ⟨hrf, .inl (.inr ⟨hr, hR, hp.read (Nat.zero_lt_succ n) hh⟩)⟩
    · exact ⟨hrf, .inr ⟨U, h', t', hx, hu, st, hh',
        ih (hp.transfer (Nat.le_succ n) hx) hh' hs'⟩⟩

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

end Verification.Footprints
