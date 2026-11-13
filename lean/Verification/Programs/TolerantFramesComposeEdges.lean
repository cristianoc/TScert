import Verification.Programs.TolerantFramesNodeAsserted
import Verification.Programs.TolerantFramesNodeBound

/-! # Tolerant frames: an edge's slot evidence checked

`run` accepts an edge whose slots' types the target's do not admit by a
subtype answer where the edge search's evidence is accepted by the
certificate checker's slot check (`SinglePass.checkedEdge`, its check
`SinglePass.edgeEvidenceChecked`): `PointClaims.checkMappedUsing`, or under
the edge's observation `BranchRefinement.checkObservedUsing` at slot 0 with
the fields, optional fields and cells it read; or the edge's context
unsatisfiable. `checkedEdge_env` proves that acceptance gives the target's
types at the mapped environment, as `ControlFlow.target_sound` and
`branch_target_sound` give them for the checker: the "target types"
premise (`htc`) of the edge lemmas. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Edges
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

omit [Hashable ι] [Instantiates ι] in
/-- **An edge's checked evidence gives the target's types**: where
`edgeEvidenceChecked` accepts the evidence at the edge's context `Γ`, the
target's context `Δ` and the facts' fields, optional fields and cells, the
edge's facts `k` hold at `ρ` (the fields and cells read off them), `Γ`
types `ρ` and the observation holds of slot 0, `Δ` types the mapped
environment. -/
theorem edgeEvidenceChecked_env {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ Δ : List (Ty ι)}
    {t : Target} {observed : Option BranchRefinement.Observation} {k : HeapKnowledge.Knowledge}
    {p : PointClaims.EdgeEvidence ι} {ρ : Env} {n : Nat} {W : WorldT (n + 1)} {h : Heap}
    (hc : edgeEvidenceChecked G images Γ Δ t observed (readFields k 0) (optionalFields k 0)
      (match observed with
        | some o => HeapKnowledge.aliasCells (HeapKnowledge.observeTyped G Γ k 0 o)
        | none => []) p = true)
    (hk : HeapKnowledge.Holds k ε ρ h) (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h)
    (ho : ∀ o, observed = some o → o.holds (ρ 0)) :
    EnvOk G Δ (PointClaims.mapEnv t.mapping ρ) (n + 1) W := by
  unfold edgeEvidenceChecked at hc
  rcases Bool.or_eq_true_iff.mp hc with hu | hc
  · exact (unsatisfiable_sound hu he).elim
  cases observed with
  | some o =>
    exact (BranchRefinement.checkObserved_sound hc).env he (ho o rfl) hh (readFields_holds hk)
      (optionalFields_holds hk) (HeapKnowledge.aliasCells_holds (HeapKnowledge.observeTyped_holds he hk (ho o rfl)))
  | none => exact (PointClaims.checkMapped_sound hc).env he

/-- **An edge the edge search accepts gives the target's types**
(`checkedEdge`): where it accepts over the facts `k` holding at `ρ`, the
edge's context `Γ` typing `ρ` and the observation holding of slot 0, the
target's context `Δ` types the mapped environment. -/
theorem checkedEdge_env {G : NormalGraph ι} {images : InstanceImageCheck G} {claimed : Array (PointClaim ι)}
    {Γ Δ : List (Ty ι)} {t : Target} {observed : Option BranchRefinement.Observation} {k : HeapKnowledge.Knowledge}
    {answers : Answered G} {ρ : Env} {n : Nat} {W : WorldT (n + 1)} {h : Heap}
    (hce : (checkedEdge G images claimed Δ Γ t observed k answers).1 = true)
    (hk : HeapKnowledge.Holds k ε ρ h) (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h)
    (ho : ∀ o, observed = some o → o.holds (ρ 0)) :
    EnvOk G Δ (PointClaims.mapEnv t.mapping ρ) (n + 1) W := by
  unfold checkedEdge at hce
  simp only at hce
  obtain ⟨p, -, hp⟩ := option_any_some hce
  exact edgeEvidenceChecked_env hp hk he hh ho

end Edges

/-! ## A start an edge enters

`run` enters a start that an edge enters as any loop head (pass change D8,
`headEntry g false`): the slots outside the given inputs and the promised
input take fresh names, and each edge into the start is checked as an edge
into a head. So the edge lemma of a head (`exitDelivers_head`) covers the
edges into the start, and the start's own first entry holds by
`start_entered_passPreT`: the premise `StartNotReentered` is not needed. -/

section Start
variable {ι : Type} [DecidableEq ι]

omit [DecidableEq ι] in
theorem range_get {n i a : Nat} (h : (List.range n)[i]? = some a) : i = a := by
  obtain ⟨_, he⟩ := List.getElem?_eq_some_iff.mp h
  simpa using he

/-- **A start an edge enters holds at the invocation's entry**: its entry
`headEntry` of the start's given facts over fresh names
(`headEntry … false`), the entry accepted by `entryRefusal`, the counter
past the start names, the entry meeting the inputs, the separation and the
index facts: the start's typed assertion holds at the entry values. -/
theorem start_entered_passPreT {G : NormalGraph ι} {w : Walk ι} {inputs : List (Ty ι)}
    {ctx : Nat → List (Ty ι)} {claims : List (CertificateProducer.PointClaim ι)} {start : Nat}
    {goal : ControlFlow.Goal ι} {written : Option HeapKnowledge.Knowledge} {supplied : List HeapKnowledge.IndexAtom}
    {givenImplies : List (PromiseCalls.Implication ι)} {givenArgs : List Nat} {givenInputs : List (Nat × Nat)}
    {entryIndices : List HeapKnowledge.IndexAtom} {entrySeparation : HeapSeparation.Separation} {fresh : Nat}
    (hacc : SinglePass.entryRefusal G inputs claims start goal written supplied givenImplies givenArgs givenInputs
      entryIndices entrySeparation = none)
    (hv : w.visited start) (hfresh : inputs.length ≤ fresh)
    (hentry : w.entry start = (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) false
      inputs.length fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs
      givenInputs givenImplies).1)
    (himp : w.implies start = (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) false
      inputs.length fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs
      givenInputs givenImplies).2.1)
    (hctx : ctx start = inputs)
    {ρ : Env} {m : Nat} {s : IndexedHeap} (he : EnvOk G inputs ρ s.n s.W)
    (hs : HeapSeparation.Holds entrySeparation ρ) (hi : HeapKnowledge.IndexHolds ⟨ρ, s.h⟩ entryIndices ρ s.h) :
    passPreT G w (List.range inputs.length) ⟨ρ, s.h⟩ ctx start ρ m s := by
  obtain ⟨-, -, hnoimp, hargs, hinputs, hk⟩ := entryRefusal_ok hacc
  have hest : HeadEstablishes G (startGiven written entryIndices entrySeparation supplied) givenImplies
      (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs givenInputs ⟨ρ, s.h⟩ ρ s :=
    { facts := startGiven_holds hk he hs hi
      implies := by subst hnoimp; intro x hx; cases hx
      inputs := fun j q _ hjq _ => by have := hinputs _ hjq; simp only at this; rw [this]
      arg := fun j a q hj ha hq => by
        have hsl := hargs j hj
        rw [hsl] at ha
        simp only [Option.bind_some] at ha
        rw [range_get ha, range_get hq] }
  refine ⟨⟨hv, ?_⟩, hctx ▸ he⟩
  rw [hentry, himp]
  refine (headEntry_holds List.nodup_range (fun x hx => ?_) (fun a ha => ?_) hest).1
  · have := List.mem_range.mp hx; omega
  · cases hsl : goal.slot with
    | none => simp [hsl] at ha
    | some sl =>
      simp only [hsl, Option.bind_some] at ha
      exact ⟨sl, ha⟩

end Start

end Verification.TolerantFrames
