import Verification.Semantics.SpineRegions
import Verification.Semantics.IndexFacts
import Verification.Semantics.ExceptionalPosts
import Verification.Semantics.FootprintStability

/-! Spine regions read from entry values through data-field paths. A region
excepts the spine location alone. Element locations remain subject to the
closed footprint. -/
namespace Verification.Footprints

/-- Separation of a path's selected spine from another value's spine.
Undefined spines give no separation witness. -/
def SpineApart (h : Heap) (x : Val) (path : List String) (y : Val) : Prop :=
  ∃ v s t, HeapKnowledge.readPath h x path = some v ∧ spineOf v = some s ∧
    spineOf y = some t ∧ s ≠ t

/-- Every location on a path has a contract fixing the value read there.
The final value may have a mutable array spine. -/
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
  · have heq : c.at v₁ = c.at v := Closed.at_of_holds hc₁ hany
    rw [heq] at hc₂
    exact hc₁.trans h₁.1 hc₂

end Verification.Footprints
