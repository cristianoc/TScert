import Verification.Programs.TolerantFramesExitTypes
import Verification.Programs.TolerantFramesComposeYields
import Verification.Programs.TolerantFramesNodeCallFresh

/-! # Tolerant frames: an exit's type checks in a form every reassigned graph keeps

`exitTypes` accepts an exit's types by one of four checks: every slot
`differing` names below the target's type by a subtype answer
(`diffSubtypes`), or the edge search's evidence accepted
(`checkedEdge`) at the edge's context over the edge's facts, at the refined
context over the step's output, or at the mixed context. Each is stated
here by what it found (`SubtypesPass`: the answers; `EdgeFound`: the
evidence; `MixedOf`: where each slot of the mixed context comes from), a
form the same at every reassigned graph (`subtypeUsing_reassign`,
`edgeEvidenceChecked_reassign`). Proved:

- `yieldsOk_atSlots`: yields holding at an environment hold restated at
  every slot holding their target's name (`yieldsAtSlots`);
- `outFreshOf_eq`: the step's `outFresh` is `passOutFreshChecked`;
- `subtypesPass_of`, `edgeFound_of_checked`, `mixedOf_mixedContext`: what
  each check gives in that form;
- `ExitTyped.reassign`, `ExitTyped.env`: the form at every reassigned
  graph, and the target's context typing the mapped environment from it,
  the subtype answers sound;
- `vacuous_false`: an exit the pass finds vacuous meets no environment. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Yields
variable {ι : Type}

/-- **Yields restated at every slot holding their target's name hold**
(`yieldsAtSlots`), where the slots hold their names' values. -/
theorem yieldsOk_atSlots {G : NormalGraph ι} {names : List Nat} {ys : List (PromiseCalls.Yield ι)} {ρ η : Env}
    {n : Nat} {W : WorldT n} {u : Tm} (hs : SlotsNamed names ρ η) (h : PromiseCalls.YieldsOk G ys ρ n W u) :
    PromiseCalls.YieldsOk G (yieldsAtSlots names ys) ρ n W u := by
  intro y' hy' hc hf
  obtain ⟨y, hy, hm⟩ := List.mem_flatMap.mp hy'
  split at hm
  · rename_i nm hnm
    obtain ⟨⟨x, j⟩, hmem, rfl⟩ := List.mem_map.mp hm
    obtain ⟨hz, hx⟩ := List.mem_filter.mp hmem
    have hxj : names[j]? = some x := by
      obtain ⟨hj, hjx⟩ := List.mem_zipIdx' hz
      rw [List.getElem?_eq_getElem hj, hjx]
    have hxn : x = nm := by simpa using hx
    subst hxn
    have := h y hy hc hf
    show PositiveRules.meaning G y.type n W (ρ j)
    rw [hs _ _ hxj, ← hs _ _ hnm]
    exact this
  · obtain rfl := List.mem_singleton.mp hm
    exact h y' hy hc hf

variable [DecidableEq ι] in
/-- **The step's `outFresh` is `passOutFreshChecked`'s answer**, at the
same values. -/
theorem outFreshOf_eq (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (entry : SinglePass.State)
    (stepK : HeapKnowledge.Knowledge) (deriv : ProgramCertificates.Evidence ι) :
    outFreshOf G images codes sums c node entry stepK deriv =
      passOutFreshChecked G images codes sums c node entry stepK deriv := rfl

end Yields

section Typed
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **Every named slot below the target's type by an accepted subtype
answer** (what `diffSubtypes` passing gives, `diffSubtypes_pairs`). -/
def SubtypesPass (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ Δ : List (Ty ι)) (diff : List (Nat × Nat)) :
    Prop :=
  ∀ p ∈ diff, ∃ A B a, Γ[p.2]? = some A ∧ Δ[p.1]? = some B ∧ ((subtypeUsing G images A B a).1).value.isSome = true

/-- The cells an edge's evidence check reads off the facts `k`
(`checkedEdge`). -/
def edgeCells (G : NormalGraph ι) (Γ : List (Ty ι)) (k : HeapKnowledge.Knowledge)
    (observed : Option BranchRefinement.Observation) : HeapFacts.Facts :=
  match observed with
  | some o => HeapKnowledge.aliasCells (HeapKnowledge.observeTyped G Γ k 0 o)
  | none => []

/-- **Evidence the edge's check accepts** at the edge's context `Γ`, the
target's `Δ` and the facts `k` (what `checkedEdge` found). -/
def EdgeFound (G : NormalGraph ι) (images : InstanceImageCheck G) (Δ Γ : List (Ty ι)) (t : Target)
    (observed : Option BranchRefinement.Observation) (k : HeapKnowledge.Knowledge) : Prop :=
  ∃ p, edgeEvidenceChecked G images Γ Δ t observed (readFields k 0) (optionalFields k 0) (edgeCells G Γ k observed) p
    = true

/-- **A context each of whose slots has the refined context's type or the
edge context's** (`mixedContext`). -/
def MixedOf (Γm Γr Γ : List (Ty ι)) : Prop := ∀ (j : Nat) (X : Ty ι), Γm[j]? = some X → Γr[j]? = some X ∨ Γ[j]? = some X

/-- **An exit's types checked** (`exitTypes`): at the edge's context `Γ`
over the edge's facts `ko`, the refined context `Γr` over the step's
output `outL`, by `diffSubtypes`, or the edge search at `Γ`, at `Γr`, or at
a mixed context. -/
def ExitTyped (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ Δ : List (Ty ι)) (t : Target)
    (observed : Option BranchRefinement.Observation) (ko : HeapKnowledge.Knowledge) (Γr : List (Ty ι))
    (outL : HeapKnowledge.Knowledge) : Prop :=
  SubtypesPass G images Γ Δ (differing Γ Δ t.mapping) ∨ EdgeFound G images Δ Γ t observed ko ∨
    EdgeFound G images Δ Γr t observed outL ∨ ∃ Γm, MixedOf Γm Γr Γ ∧ EdgeFound G images Δ Γm t observed outL

theorem subtypesPass_of {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ Δ : List (Ty ι)}
    {diff : List (Nat × Nat)} {observed : Option BranchRefinement.Observation} {answers : Answered G}
    (h : (diffSubtypes G images Γ Δ diff observed answers).1 = true) : SubtypesPass G images Γ Δ diff :=
  diffSubtypes_pairs h

theorem edgeFound_of_checked {G : NormalGraph ι} {images : InstanceImageCheck G} {claimed : Array (PointClaim ι)}
    {Γ Δ : List (Ty ι)} {t : Target} {observed : Option BranchRefinement.Observation} {k : HeapKnowledge.Knowledge}
    {answers : Answered G} (h : (checkedEdge G images claimed Δ Γ t observed k answers).1 = true) :
    EdgeFound G images Δ Γ t observed k := by
  unfold checkedEdge at h
  simp only at h
  obtain ⟨p, -, hp⟩ := option_any_some h
  exact ⟨p, hp⟩

theorem mixedOf_mixedContext (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ Γ' Δ : List (Ty ι))
    (m : PointClaims.Mapping) (answers : Answered G) : MixedOf (mixedContext G images Γ Γ' Δ m answers).1 Γ' Γ := by
  intro j X hj
  unfold mixedContext at hj
  rw [Array.getElem?_toList] at hj
  exact mixed_fold Γ Γ' _ (fun acc A' s => ⟨_, rfl⟩) Γ' 0 (#[], answers) rfl (by simp)
    (fun j X h => by simpa using h) j X hj

/-- **The checks at a reassigned graph**: the same answers and evidence,
the answers reassigned. -/
theorem ExitTyped.reassign {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ Δ : List (Ty ι)} {t : Target}
    {observed : Option BranchRefinement.Observation} {ko : HeapKnowledge.Knowledge} {Γr : List (Ty ι)}
    {outL : HeapKnowledge.Knowledge} (h : ExitTyped G images Γ Δ t observed ko Γr outL) (η : MixedAssignment ι) :
    ExitTyped (PositiveRules.reassign G η) (images.reassign η) Γ Δ t observed ko Γr outL := by
  have hf : ∀ {Γ0 k}, EdgeFound G images Δ Γ0 t observed k →
      EdgeFound (PositiveRules.reassign G η) (images.reassign η) Δ Γ0 t observed k := fun ⟨p, hp⟩ =>
    ⟨p, (edgeEvidenceChecked_reassign G η images _ _ t observed _ _ _ p).trans hp⟩
  rcases h with h | h | h | ⟨Γm, hm, h⟩
  · refine .inl fun p hp => ?_
    obtain ⟨A, B, a, hA, hB, hs⟩ := h p hp
    exact ⟨A, B, Answered.reassign a η, hA, hB, by rw [subtypeUsing_reassign]; exact hs⟩
  · exact .inr (.inl (hf h))
  · exact .inr (.inr (.inl (hf h)))
  · exact .inr (.inr (.inr ⟨Γm, hm, hf h⟩))

omit [Hashable ι] [Instantiates ι] in
/-- **Accepted evidence gives the target's types**, the facts read only
where the edge observes the result (`edgeEvidenceChecked_env`). -/
theorem edgeFound_env {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ Δ : List (Ty ι)} {t : Target}
    {observed : Option BranchRefinement.Observation} {k : HeapKnowledge.Knowledge}
    (hf : EdgeFound G images Δ Γ t observed k) {ρ : Env} {n : Nat} {W : WorldT (n + 1)} {h : Heap}
    (hk : observed.isSome = true → HeapKnowledge.Holds k ε ρ h) (he : EnvOk G Γ ρ (n + 1) W)
    (hh : HeapOk (n + 1) W h) (ho : ∀ o, observed = some o → o.holds (ρ 0)) :
    EnvOk G Δ (PointClaims.mapEnv t.mapping ρ) (n + 1) W := by
  obtain ⟨p, hp⟩ := hf
  cases observed with
  | some o => exact edgeEvidenceChecked_env hp (hk rfl) he hh ho
  | none =>
    unfold edgeEvidenceChecked at hp
    rcases Bool.or_eq_true_iff.mp hp with hu | hc
    · exact (unsatisfiable_sound hu he).elim
    · exact (PointClaims.checkMapped_sound hc).env he

/-- **The target's types from an exit's checks** (`ExitTyped`): the
subtype answers sound; the edge's context typing the environment, the
edge's facts holding there; the refined context typing it, the step's
output holding there where the edge observes the result. -/
theorem ExitTyped.env {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ Δ : List (Ty ι)} {t : Target}
    {observed : Option BranchRefinement.Observation} {ko : HeapKnowledge.Knowledge} {Γr : List (Ty ι)}
    {outL : HeapKnowledge.Knowledge} (h : ExitTyped G images Γ Δ t observed ko Γr outL)
    (hsub : SubtypeAnswersSound G images) {ρ : Env} {n : Nat} {W : WorldT (n + 1)} {hp : Heap}
    (he : EnvOk G Γ ρ (n + 1) W) (hk : HeapKnowledge.Holds ko ε ρ hp) (her : EnvOk G Γr ρ (n + 1) W)
    (hout : observed.isSome = true → HeapKnowledge.Holds outL ε ρ hp) (hh : HeapOk (n + 1) W hp)
    (ho : ∀ o, observed = some o → o.holds (ρ 0)) :
    EnvOk G Δ (PointClaims.mapEnv t.mapping ρ) (n + 1) W := by
  rcases h with h | h | h | ⟨Γm, hm, h⟩
  · refine PointClaims.MappedCovers.env (fun i B hB => ?_) he
    by_cases hd : (i, PointClaims.slot t.mapping i) ∈ differing Γ Δ t.mapping
    · obtain ⟨A, B', a, hA, hB', hs⟩ := h _ hd
      rw [hB] at hB'
      obtain rfl := Option.some.inj hB'
      exact ⟨A, hA, hsub A B a hs⟩
    · exact ⟨B, differing_cover Γ Δ t.mapping hB hd, fun _ _ _ h => h⟩
  · exact edgeFound_env h (fun _ => hk) he hh ho
  · exact edgeFound_env h hout her hh ho
  · refine edgeFound_env h hout ⟨he.1, fun j X hj => ?_⟩ hh ho
    rcases hm j X hj with hx | hx
    · exact her.2 j X hx
    · exact he.2 j X hx

/-- **Whether the pass finds an exit vacuous** (`exitStep`'s `vacuous`):
the node's own answer `here`, a pushed result of an empty type, or an
observation impossible at the edge's slot 0. -/
def vacuousOf (G : NormalGraph ι) (here : Bool) (A : Ty ι) (Γ : List (Ty ι)) (pushed : Bool)
    (observed : Option BranchRefinement.Observation) : Bool :=
  match observed with
  | some o => (here || (pushed && ControlFlow.unsatisfiable G [A])) || (Γ[0]?).any (BranchRefinement.impossible G · o)
  | none => here || (pushed && ControlFlow.unsatisfiable G [A])

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
theorem HereEmpty.reassign {G : NormalGraph ι} {C : List (Ty ι)} (h : HereEmpty G C) (η : MixedAssignment ι) :
    HereEmpty (PositiveRules.reassign G η) C := by unfold HereEmpty; exact h

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
theorem hereEmpty_false {G : NormalGraph ι} {C : List (Ty ι)} (h : HereEmpty G C) {ρ : Env} {n : Nat}
    {W : WorldT n} (he : EnvOk G C ρ n W) : False := by
  rcases h with h | ⟨i, B, hB, hu⟩
  · exact unsatisfiable_sound h he
  · exact unsatisfiable_sound hu (Γ := [B]) (ρ := fun _ => ρ i) ⟨fun _ => he.1 i, fun j X hj => by
      cases j with
      | zero => exact (Option.some.inj hj) ▸ he.2 i B hB
      | succ j => simp at hj⟩

omit [Hashable ι] [Instantiates ι] in
/-- **A vacuous exit meets no environment**: where the node's `here`
answer states its context empty, no pushed environment of the claim's type
and context with the exit's observation holds. -/
theorem vacuous_false {G : NormalGraph ι} {here : Bool} {A : Ty ι} {C : List (Ty ι)} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    (hv : vacuousOf G here A (if pushed then A :: C else C) pushed observed = true)
    (hhere : here = true → HereEmpty G C) (hpo : observed.isSome = true → pushed = true)
    {ρ : Env} {s : IndexedHeap} {v : Tm} (he : EnvOk G (A :: C) (push v ρ) s.n s.W)
    (ho : ObservedOk observed promote v) : False := by
  have hunsat : (here || (pushed && ControlFlow.unsatisfiable G [A])) = true → False := by
    intro hu
    rcases Bool.or_eq_true_iff.mp hu with hh | hp
    · exact hereEmpty_false (hhere hh) (envOk_tail he)
    · simp only [Bool.and_eq_true] at hp
      exact unsatisfiable_sound hp.2 (Γ := [A]) ⟨he.1, fun j X hj => by
        cases j with
        | zero => exact (Option.some.inj hj) ▸ he.2 0 A rfl
        | succ j => simp at hj⟩
  unfold vacuousOf at hv
  cases observed with
  | none => exact hunsat hv
  | some o =>
    rcases Bool.or_eq_true_iff.mp hv with hu | hi
    · exact hunsat hu
    · have hp : pushed = true := hpo rfl
      subst hp
      simp only [if_true, List.getElem?_cons_zero, Option.any_some] at hi
      exact BranchRefinement.impossible_sound hi (he.2 0 A rfl) (by simpa [ObservedOk, push] using ho)

end Typed

end Verification.TolerantFrames
