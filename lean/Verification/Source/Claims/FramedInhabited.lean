import Verification.Source.Claims.FlowProbe
import Verification.Types.InhabitedTypes

/-! # The inhabitance of a framed plan's outside slots

A framed plan's claim is stated over the initial configurations whose
module functions' outside captures meet their contracts at the
configuration's own world and every world extending it (the framed
acceptance draft, "The initialization as a premise", `SlotsMet`). That
premise is inhabited where every outside slot's type has a value at one
world: the check (`outsideInhabitedRefusal`), run on every framed plan
(`FilePlans.framedPlan`), reads each module function of the component and
each of its slots naming no module function of the component, the type its
request reads that slot at decided, in its request's graph, by the
inhabitance check (`InhabitedTypes.typeWitnessB`, `slotsWitnessed`). Its soundness
(`slotsWitnessed_inhabited`): in an extension of any admissible world whose
heap meets it, one closed value per slot, with valid references, meeting
the slot's type at every budget up to the world's and every world above
it. -/
namespace Verification.SourceClaimJson
open Lean PositiveGraphs PositiveRules InhabitedTypes

section
variable {ι : Type}

/-- **A list of types the check passes has values at one world** (proved):
in an extension of any admissible world whose heap meets it, one closed
value per type with valid references, each meeting its type at every budget
up to the world's and every world above the extension (`Above`). By
induction on the list, each value allocated past the previous ones, whose
meanings the extension keeps. -/
theorem typesWitness_sound {G : NormalGraph ι} (tag : ComponentTag) :
    ∀ {As : List (List ι)}, As.all (typeWitnessB G) = true → ∀ {n : Nat} {W : WorldT n} {heap : Heap},
      WorldAdm W → HeapOk n W heap →
      ∃ (W' : WorldT n) (heap' : Heap) (vs : List Val), WExt W W' ∧ WorldAdm W' ∧ HeapOk n W' heap' ∧
        vs.length = As.length ∧ ∀ (i : Nat) A v, As[i]? = some A → vs[i]? = some v →
          isVal v = true ∧ Scoped 0 v ∧ RefsOk W' v ∧
            ∀ j (V : WorldT j), (∃ hj : j ≤ n, WExt (trunc j hj W') V) → meaning G A j V v
  | [], _, _, W, heap, hA, hh => ⟨W, heap, [], WExt_refl _, hA, hh, rfl, fun i A v hA' _ => by simp at hA'⟩
  | A :: As, h, n, W, heap, hA, hh => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨W₁, heap₁, v₁, hx₁, hA₁, hh₁, hv₁, hs₁, hr₁, hm₁⟩ := typeWitness_sound h.1 tag hA hh
    obtain ⟨W₂, heap₂, vs, hx₂, hA₂, hh₂, hlen, hall⟩ := typesWitness_sound tag h.2 hA₁ hh₁
    refine ⟨W₂, heap₂, v₁ :: vs, WExt_trans hx₁ hx₂, hA₂, hh₂, by simp [hlen], ?_⟩
    intro i B v hB hv
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hB hv
      subst hB hv
      exact ⟨hv₁, hs₁, RefsOk_mono hx₂ hr₁, fun j V ⟨hj, hV⟩ =>
        hm₁ j hj V (WExt_trans (WExt_trunc hj hx₂) hV)⟩
    | succ i => exact hall i B v (by simpa using hB) (by simpa using hv)

end

/-- **The refusal of the inhabitance check** at a component's module
functions: none where every slot of each naming no module function of
`mods` is witnessed (`ProbeModule.witnessed`, `slotsWitnessed`), and
otherwise the first that is not. -/
def outsideInhabitedRefusal (mods : List ProbeModule) : Option String :=
  (mods.findSome? fun g => (g.siblings.zipIdx.find? fun (x, k) =>
      !(mods.any (·.name == x)) && !(g.witnessed.getD k false)).map fun (x, _) => (g.name, x)).map fun (g, x) =>
    s!"a framed plan's initial premise is not shown inhabited: the module function {g} reads {x} at a type the inhabitance check builds no value of"

/-- **The check is sound at a module function's request** (proved): where
a request's slots `ks` are witnessed, they have values at one world, in an
extension of any admissible world whose heap meets it: one closed value
per slot, with valid references, meeting the type the request reads the
slot at in its graph, at every budget up to the world's and every world
above it. -/
theorem slotsWitnessed_inhabited {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι]
    {r : SourceElaboration.SourceRequest σ ι} {ks : List Nat}
    (h : ∀ k ∈ ks, (slotsWitnessed r).getD k false = true) (tag : ComponentTag)
    {n : Nat} {W : WorldT n} {heap : Heap} (hA : WorldAdm W) (hh : HeapOk n W heap) :
    ∃ (W' : WorldT n) (heap' : Heap) (vs : List Val), WExt W W' ∧ WorldAdm W' ∧ HeapOk n W' heap' ∧
      vs.length = ks.length ∧ ∀ (i k : Nat) A v, ks[i]? = some k →
        r.inputs[r.inputs.length - r.siblings.length + k]? = some A → vs[i]? = some v →
        isVal v = true ∧ Scoped 0 v ∧ RefsOk W' v ∧
          ∀ j (V : WorldT j), (∃ hj : j ≤ n, WExt (trunc j hj W') V) →
            meaning (LabelStore.StoreView.graph r.types) A j V v := by
  let base := r.inputs.length - r.siblings.length
  have hk : ∀ k ∈ ks, ∃ A, r.inputs[base + k]? = some A ∧
      typeWitnessB (LabelStore.StoreView.graph r.types) A = true := by
    intro k hkm
    have := h k hkm
    unfold slotsWitnessed at this
    by_cases hlt : k < r.siblings.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt] at this
      cases hA' : r.inputs[base + k]? with
      | none => simp [base, hA'] at this
      | some A => exact ⟨A, rfl, by simpa [base, hA'] using this⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt)] at this
      simp at this
  let As := ks.filterMap fun k => r.inputs[base + k]?
  have hlen : As.length = ks.length := by
    have : ∀ (L : List Nat), (∀ k ∈ L, ∃ A, r.inputs[base + k]? = some A) →
        (L.filterMap fun k => r.inputs[base + k]?).length = L.length := by
      intro L hL
      induction L with
      | nil => rfl
      | cons k L ih =>
        obtain ⟨A, hA'⟩ := hL k (by simp)
        simp [hA', ih fun k' hk' => hL k' (by simp [hk'])]
    exact this ks fun k hkm => (hk k hkm).imp fun _ h => h.1
  have hget : ∀ (i k : Nat), ks[i]? = some k → As[i]? = r.inputs[base + k]? := by
    have : ∀ (L : List Nat), (∀ k ∈ L, ∃ A, r.inputs[base + k]? = some A) → ∀ (i k : Nat), L[i]? = some k →
        (L.filterMap fun k => r.inputs[base + k]?)[i]? = r.inputs[base + k]? := by
      intro L hL
      induction L with
      | nil => intro i k h; simp at h
      | cons k' L ih =>
        intro i k hi
        obtain ⟨A, hA'⟩ := hL k' (by simp)
        cases i with
        | zero => simp at hi; subst hi; simp [hA']
        | succ i => simp [hA']; exact ih (fun k'' hk'' => hL k'' (by simp [hk''])) i k (by simpa using hi)
    exact this ks fun k hkm => (hk k hkm).imp fun _ h => h.1
  have hall : As.all (typeWitnessB (LabelStore.StoreView.graph r.types)) = true := by
    rw [List.all_eq_true]
    intro A hA'
    obtain ⟨k, hkm, hkA⟩ := List.mem_filterMap.mp hA'
    obtain ⟨B, hB, hw⟩ := hk k hkm
    rw [hB] at hkA; cases hkA; exact hw
  obtain ⟨W', heap', vs, hx, hA₂, hh₂, hlen', hvs⟩ := typesWitness_sound tag hall hA hh
  exact ⟨W', heap', vs, hx, hA₂, hh₂, by rw [hlen', hlen], fun i k A v hki hAk hv =>
    hvs i A v (by rw [hget i k hki]; exact hAk) hv⟩

end Verification.SourceClaimJson
