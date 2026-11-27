import Verification.Programs.TolerantFramesMergeGuarded

/-! # Tolerant frames: the merge's entailed bounds and their terms

A merge keeps a linear bound one predecessor states where every view holds
or entails it (`mergeEntailed`). The bound holds on the path through `p`
where `p`'s view holds it as a stored fact (its holding states its terms
defined), or where each of its terms is one `HeapKnowledge.termDefined`
accepts over the facts the entailment reads (`Store.linearNear`): those facts
hold on the path, so the term is defined there (`termDefined_sound`). The
check `entailDefinedCheck` states this per view; with it at every view, the
merge's entailed part holds (`OnPath.entailed_ok_checked`).

No term is defined at every valuation: a term reads its slot's value
(`termValue`) through its kind, and a value of another kind gives none
(`termValue_value_undef`, `termValue_length_num`). -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations HeapKnowledge
open Verification.SinglePass (Atom Store State)
open ProgramTyping PositiveGraphs

/-- A slot's value term is undefined where the slot holds `undefined`. -/
theorem termValue_value_undef {ρ : Env} {h : Heap} {s : Nat} (hs : ρ s = .undef) :
    termValue ε ρ h (.value s) = none := by
  simp [hs, intValue]

/-- A length term is undefined where the slot holds a number. -/
theorem termValue_length_num {ρ : Env} {h : Heap} {s : Nat} {b : UInt64} (hs : ρ s = .num b) :
    termValue ε ρ h (.length s) = none := by
  simp [hs, lengthOf, Footprints.spineOf, fieldsOf]

/-- The facts `linearNear` lists hold where the store does. -/
theorem linearNear_holds (hnear : LinearNearSound) {s : Store} {η : Env} {h : Heap} (hs : StoreOk ε s η h)
    (names : List Nat) (limit : Nat) : IndexHolds ε (s.linearNear names limit) η h :=
  fun x hx => hs _ (hnear _ _ _ x hx) x (List.mem_singleton_self _)

/-- **A checked bound holds at a holding view** where the view holds or
entails it (lowering any field-path terms through the view's read links). -/
theorem checked_bound_holds (hnear : LinearNearSound) {qs : State} {F : Linear.Fact Term} {neg : Bool}
    {η : Env} {h : Heap} (hv : StoreOk ε qs.store η h)
    (hview : SinglePass.entailLinearView qs F neg = true) :
    AtomHolds ε (.index ⟨.linear F, none, neg⟩) η h := by
  have core : ∀ (G : Linear.Fact Term),
      (qs.store.holds (.index ⟨.linear G, none, neg⟩) ||
        HeapKnowledge.entailsKnown (qs.store.linearNear (Atom.index ⟨.linear G, none, neg⟩).names) G) = true →
      SinglePass.entailDefinedCheck qs (.index ⟨.linear G, none, neg⟩) G = true →
      AtomHolds ε (.index ⟨.linear G, none, neg⟩) η h := by
    intro G hdec hc
    rcases Bool.or_eq_true_iff.mp hc with hl | hall
    · exact atomHolds_canon.mp (hv _ (live_storeAll (Std.HashSet.contains_iff_mem.mp hl)))
    have hdG : ∀ t ∈ G.vars, (termValue ε η h t).isSome := fun t ht =>
      termDefined_sound (linearNear_holds hnear hv _ 40) (List.all_eq_true.mp hall t ht)
    rcases Bool.or_eq_true_iff.mp hdec with hh | he
    · exact holds_sound hv hh hdG
    · exact index_none_holds ⟨hdG, HeapKnowledge.entailsKnown_sound (linearNear_holds hnear hv _ 40) he⟩
  unfold SinglePass.entailLinearView at hview
  simp only [Bool.and_eq_true] at hview
  split at hview
  · have hF' := core _ hview.1 hview.2
    intro y hy hcond
    simp only [List.mem_singleton] at hy; subst hy
    have hb := hF' _ (List.mem_singleton_self _) hcond
    exact (HeapKnowledge.IndexFact.holdsAt_linear_mapVars (HeapKnowledge.renameFact_mapVars _ F)
      fun x _ y hy => by cases hy; exact lowerTerm_eq hv _ x).mp hb
  · exact core F hview.1 hview.2

section Path
variable {preds : List State} {width fresh0 p : Nat} {ρ η : Env} {h : Heap}

/-- **The entailed bounds hold** on the path, with `LinearNearSound`: the
merge adds a bound only where every view passes `entailLinearView`. -/
theorem OnPath.entailed_ok_checked (P : OnPath preds width fresh0 p ε ρ η h) (hnear : LinearNearSound) {met : Store}
    (hm : StoreOk ε met (mVal preds width fresh0 ρ η) h) :
    let live := Std.HashSet.ofList (mNames preds width fresh0).toList
    let met0 := mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0)
    let diffs := mergeDiffs live preds (mRen preds width fresh0)
      (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)) met0
    StoreOk ε (mergeEntailed live diffs
      (mergeViews (mNames preds width fresh0).toList diffs met0) met) (mVal preds width fresh0 ρ η) h := by
  intro live met0 diffs
  obtain ⟨v, -, hv, hall⟩ := P.view_ok
  refine mergeEntailed_inv (fun s => StoreOk ε s (mVal preds width fresh0 ρ η) h)
    (fun a => AtomHolds ε a (mVal preds width fresh0 ρ η) h) (fun _ _ hs ha => add_ok hs ha) ?_ hm
  intro F neg _ hviews
  exact checked_bound_holds hnear hv (hall _ hviews)

end Path

end Verification.TolerantFrames
