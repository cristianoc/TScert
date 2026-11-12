import Verification.Programs.TolerantFramesMergeNear

/-! # Tolerant frames: the merge's implications from the edges' check, and the merge theorem

**The joined implications.** The pass records each edge into a merge as
`(Γe, atSlots, m)`: the source's context, the implications the edge carries
restated at the source's slots (`atSlotsOf`), the edge's mapping. The check
each incoming edge needs (the pass lane's D3) is
`PromiseCalls.impliesCheck G Γe atSlots m (meetImplications G edgesIn width context)`:
with it, the merge's joined implications hold at the merge's slot
environment, the edge's mapping applied to the source's (`meetImplications_ok_of_check`),
so the merge's implications hold (`mergeImplies_ok_of_check`).

**The merge theorem** (`mergeState_holdsAt_checked`) with every premise that
is a theorem removed: `GuardedHolds` (`guardedHolds_of_path`),
`LinearNearSound` from the equation `LinearNearFuelEq`, `EntailedDefined`
replaced by the pass's check `EntailedChecked`, the joined implications from
the edge check. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)
open ProgramTyping PositiveGraphs

section Implies
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- Each name's slots among `names` (`slotsOf` in `SinglePass.run`). -/
def slotsOfNames (names : List Nat) : Std.HashMap Nat (List Nat) :=
  names.zipIdx.foldl (fun acc (x, i) => acc.insert x (i :: acc.getD x [])) {}

/-- An edge's implications over names restated at the source's slots
(`atSlots` in `SinglePass.run`). -/
def atSlotsOf (names : List Nat) (carried : List (PromiseCalls.Implication ι)) : List (PromiseCalls.Implication ι) :=
  carried.flatMap fun (x : PromiseCalls.Implication ι) =>
    ((slotsOfNames names).getD x.test []).flatMap fun i => ((slotsOfNames names).getD x.target []).map fun j =>
      (⟨i, j, x.type⟩ : PromiseCalls.Implication ι)

omit [DecidableEq ι] [Hashable ι] in
/-- **A name's slots hold the name.** -/
theorem slotsOfNames_get {names : List Nat} {x i : Nat} (hi : i ∈ (slotsOfNames names).getD x []) :
    names[i]? = some x := by
  unfold slotsOfNames at hi
  revert hi
  refine foldl_inv (fun (acc : Std.HashMap Nat (List Nat)) => ∀ x i, i ∈ acc.getD x [] → names[i]? = some x)
    _ _ _ (fun x i h => by simp at h) ?_ x i
  intro ⟨y, j⟩ hyj acc hacc x i hi
  rw [Std.HashMap.getD_insert] at hi
  split at hi
  · rename_i he
    simp only [beq_iff_eq] at he
    subst he
    rcases List.mem_cons.mp hi with rfl | hi
    · obtain ⟨hj, hjy⟩ := List.mem_zipIdx' hyj
      rw [List.getElem?_eq_getElem hj, hjy]
    · exact hacc _ _ hi
  · exact hacc x i hi

omit [DecidableEq ι] [Hashable ι] in
/-- **The implications at the source's slots hold** where the slots hold their
names' values and the implications over names hold. -/
theorem atSlots_ok {G : NormalGraph ι} {names : List Nat} {carried : List (PromiseCalls.Implication ι)}
    {ρ η : Env} {n : Nat} {W : WorldT n} (hs : SlotsNamed names ρ η)
    (hc : PromiseCalls.ImpliesOk G carried η n W) : PromiseCalls.ImpliesOk G (atSlotsOf names carried) ρ n W := by
  intro y hy ht
  obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
  obtain ⟨i, hi, hy⟩ := List.mem_flatMap.mp hy
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
  have hti := hs _ _ (slotsOfNames_get hi)
  have htj := hs _ _ (slotsOfNames_get hj)
  show PositiveRules.meaning G x.type n W (ρ j)
  rw [htj]
  exact hc x hx (by rw [← hti]; exact ht)

omit [Hashable ι] in
/-- **(Joined implications) The check each edge into a merge needs**: where an
edge `(Γe, xs, m)` into the merge passes `impliesCheck` against the merge's
joined implications, its source environment `ρs` meets `Γe` and its
implications hold there, the joined implications hold at the merge's slot
environment `mapEnv m ρs`. -/
theorem meetImplications_ok_of_check {G : NormalGraph ι} {context : List (Ty ι)}
    {edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Γe : List (Ty ι)} {xs : List (PromiseCalls.Implication ι)} {m : PointClaims.Mapping} {ρs : Env}
    {n : Nat} {W : WorldT n}
    (hc : PromiseCalls.impliesCheck G Γe xs m
      (CertificateProducer.meetImplications G edgesIn context.length context) = true)
    (he : EnvOk G Γe ρs n W) (hx : PromiseCalls.ImpliesOk G xs ρs n W) :
    PromiseCalls.ImpliesOk G (CertificateProducer.meetImplications G edgesIn context.length context)
      (PointClaims.mapEnv m ρs) n W :=
  PromiseCalls.impliesCheck_sound hc he hx

/-- **The merge's implications hold from the edge check** on the path whose
edge passes it. -/
theorem mergeImplies_ok_of_check {G : NormalGraph ι} {context : List (Ty ι)}
    {edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Γe : List (Ty ι)} {sourceNames : List Nat} {carried : List (PromiseCalls.Implication ι)}
    {m : PointClaims.Mapping} {ρs ηs : Env} {names : List Nat} {η : Env} {n : Nat} {W : WorldT n}
    (hc : PromiseCalls.impliesCheck G Γe (atSlotsOf sourceNames carried) m
      (CertificateProducer.meetImplications G edgesIn context.length context) = true)
    (he : EnvOk G Γe ρs n W) (hss : SlotsNamed sourceNames ρs ηs)
    (hcar : PromiseCalls.ImpliesOk G carried ηs n W)
    (hs : SlotsNamed names (PointClaims.mapEnv m ρs) η) :
    PromiseCalls.ImpliesOk G (mergeImplies G context edgesIn names) η n W :=
  mergeImplies_ok hs (meetImplications_ok_of_check hc he (atSlots_ok hss hcar))

end Implies

section Merge
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- **(Merge) The merged state holds on the path through a predecessor**,
from its theorems: where predecessor `p`'s state holds at `η`, every
predecessor has the merge's width, a well-formed store and names below the
merge's first fresh name `fresh`, the start names are below it, the pass's
`linearNear` is its search on fuel (`LinearNearFuelEq`), every entailed bound
passes the check at every view (`EntailedChecked`) and the edges' joined
implications hold at the slot environment `hI`, the merged state with the
merge's implications holds at the merge's valuation `mVal`. -/
theorem mergeState_holdsAt_checked {G : NormalGraph ι} {context : List (Ty ι)} {preds : List State}
    {edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)} {fresh : Nat}
    {start : List Nat} {entry : Env} {implies : List (PromiseCalls.Implication ι)} {p : Nat} {η ρ : Env}
    {mark : Nat} {s : IndexedHeap} (hp : p < preds.length)
    (hlen : ∀ q ∈ preds, q.names.length = context.length) (hwf : ∀ q ∈ preds, StoreWF q.store)
    (hbel : ∀ q ∈ preds, StateBelow q fresh) (hstart : ∀ x ∈ start, x < fresh) (hnear : LinearNearFuelEq)
    (hchk : EntailedChecked preds context.length fresh)
    (hI : PromiseCalls.ImpliesOk G (CertificateProducer.meetImplications G edgesIn context.length context) ρ s.n s.W)
    (hS : StateHoldsAt G preds[p] implies start entry η ρ mark s) :
    StateHoldsAt G (SinglePass.mergeState G context preds edgesIn fresh).state
      (SinglePass.mergeState G context preds edgesIn fresh).implies start entry
      (mVal preds context.length fresh ρ η) ρ mark s := by
  obtain ⟨hslots, hstore, -, hfresh, hst⟩ := hS
  have P : OnPath preds context.length fresh p ρ η s.h :=
    { hp, len := hlen, bel := fun q hq => (hbel q hq).1, facts := fun q hq => (hbel q hq).2.1, wf := hwf,
      slots := hslots, store := hstore }
  have hn := linearNearSound_of_eq hnear
  rw [mergeState_state, mergeState_implies]
  refine ⟨P.slotsNamed, ?_, mergeImplies_ok P.slotsNamed hI,
    P.fresh_ok (hbel _ (List.getElem_mem hp)).2.2 hfresh, fun q x hq => ?_⟩
  · exact P.guarded_ok (guardedHolds_of_path P) (P.entailed_ok_checked hn hchk (P.bounds_ok P.met0_ok))
  rw [show mVal preds context.length fresh ρ η x = η x from mergeVal_below (hstart x (List.mem_of_getElem? hq))]
  exact hst q x hq

/-- **(Merge) The merged state holds** (`StateHolds`) where predecessor `p`'s
does, from its theorems and the premises `LinearNearFuelEq`,
`EntailedChecked` and the joined implications. -/
theorem mergeState_holds_checked {G : NormalGraph ι} {context : List (Ty ι)} {preds : List State}
    {edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)} {fresh : Nat}
    {start : List Nat} {entry : Env} {implies : List (PromiseCalls.Implication ι)} {p : Nat} {ρ : Env}
    {mark : Nat} {s : IndexedHeap} (hp : p < preds.length)
    (hlen : ∀ q ∈ preds, q.names.length = context.length) (hwf : ∀ q ∈ preds, StoreWF q.store)
    (hbel : ∀ q ∈ preds, StateBelow q fresh) (hstart : ∀ x ∈ start, x < fresh) (hnear : LinearNearFuelEq)
    (hchk : EntailedChecked preds context.length fresh)
    (hI : PromiseCalls.ImpliesOk G (CertificateProducer.meetImplications G edgesIn context.length context) ρ s.n s.W)
    (hS : StateHolds G preds[p] implies start entry ρ mark s) :
    StateHolds G (SinglePass.mergeState G context preds edgesIn fresh).state
      (SinglePass.mergeState G context preds edgesIn fresh).implies start entry ρ mark s := by
  obtain ⟨η, hη⟩ := hS
  exact ⟨_, mergeState_holdsAt_checked hp hlen hwf hbel hstart hnear hchk hI hη⟩

end Merge

end Verification.TolerantFrames
