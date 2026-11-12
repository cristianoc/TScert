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
open Verification Footprints HeapObservations HeapKnowledge
open Verification.SinglePass (Atom Store State)
open ProgramTyping PositiveGraphs

/-- A slot's value term is undefined where the slot holds `undefined`. -/
theorem termValue_value_undef {ρ : Env} {h : Heap} {s : Nat} (hs : ρ s = .undef) :
    termValue ρ h (.value s) = none := by
  simp [hs, intValue]

/-- A length term is undefined where the slot holds a number. -/
theorem termValue_length_num {ρ : Env} {h : Heap} {s : Nat} {b : UInt64} (hs : ρ s = .num b) :
    termValue ρ h (.length s) = none := by
  simp [hs, lengthOf, Footprints.storeOf, fieldsOf]

/-- The facts `linearNear` lists hold where the store does. -/
theorem linearNear_holds (hnear : LinearNearSound) {s : Store} {η : Env} {h : Heap} (hs : StoreOk s η h)
    (names : List Nat) (limit : Nat) : IndexHolds (s.linearNear names limit) η h :=
  fun x hx => hs _ (hnear _ _ _ x hx) x (List.mem_singleton_self _)

/-- **A checked bound holds at a holding view** where the view holds or
entails it. -/
theorem checked_bound_holds (hnear : LinearNearSound) {qs : State} {F : Linear.Fact Term} {neg : Bool}
    {η : Env} {h : Heap} (hv : StoreOk qs.store η h)
    (hdec : (qs.store.holds (.index ⟨.linear F, none, neg⟩) ||
      HeapKnowledge.entailsKnown (qs.store.linearNear (Atom.index ⟨.linear F, none, neg⟩).names) F) = true)
    (hc : SinglePass.entailDefinedCheck qs (.index ⟨.linear F, none, neg⟩) F = true) :
    AtomHolds (.index ⟨.linear F, none, neg⟩) η h := by
  rcases Bool.or_eq_true_iff.mp hc with hl | hall
  · exact atomHolds_canon.mp (hv _ (live_storeAll (Std.HashSet.contains_iff_mem.mp hl)))
  have hdF : ∀ t ∈ F.vars, (termValue η h t).isSome := fun t ht =>
    termDefined_sound (linearNear_holds hnear hv _ 40) (List.all_eq_true.mp hall t ht)
  rcases Bool.or_eq_true_iff.mp hdec with hh | he
  · exact holds_sound hv hh hdF
  · exact index_none_holds ⟨hdF, HeapKnowledge.entailsKnown_sound (linearNear_holds hnear hv _ 40) he⟩

section Path
variable {preds : List State} {width fresh0 p : Nat} {ρ η : Env} {h : Heap}

/-- **The entailed bounds hold** on the path, with `LinearNearSound`: the
merge adds a bound only where every view passes `entailDefinedCheck`. -/
theorem OnPath.entailed_ok_checked (P : OnPath preds width fresh0 p ρ η h) (hnear : LinearNearSound) {met : Store}
    (hm : StoreOk met (mVal preds width fresh0 ρ η) h) :
    let met0 := mergeMet0 preds (mNames preds width fresh0) (mRen preds width fresh0)
    let diffs := mergeDiffs preds (mRen preds width fresh0)
      (mergeVariants preds (mNames preds width fresh0) (mRen preds width fresh0)) met0
    StoreOk (mergeEntailed (Std.HashSet.ofList (mNames preds width fresh0).toList) diffs
      (mergeViews (mNames preds width fresh0).toList diffs met0) met) (mVal preds width fresh0 ρ η) h := by
  intro met0 diffs
  obtain ⟨v, -, hv, hall⟩ := P.view_ok
  refine mergeEntailed_inv (fun s => StoreOk s (mVal preds width fresh0 ρ η) h)
    (fun a => AtomHolds a (mVal preds width fresh0 ρ η) h) (fun _ _ hs ha => add_ok hs ha) ?_ hm
  intro d hd F neg ha hviews hdefs
  exact checked_bound_holds hnear hv (hall _ hviews) (hall _ hdefs)

end Path

end Verification.TolerantFrames
