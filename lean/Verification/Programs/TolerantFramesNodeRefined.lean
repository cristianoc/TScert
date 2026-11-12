import Verification.Programs.TolerantFramesNodeYielded

/-! # Tolerant frames: the context as a step's yields refine it

`run` refines a normal edge's context by the step's yields restated at every
slot holding their targets' names (`ysAll`, `passReturnYields`), through the
alias links of the step's output over the node's context (`outAll`), per
continuation and arm (`refinedΓ`): this context is the edge's recorded
context at a merge (`incomingEdges`) and the one an edge into a stated node
is checked at. `passRefined` is `refinedΓ`, `passOutAll` is `outAll`.
Proved:

- `passRefined_env`: at a normal exit of the node, the arm `first` the exit's
  position among the successors gives (`passFirst`), the arms distinct
  (`ArmsDistinct`), the pushed environment typed by the claim's type and
  context, the value of the continuation's shape, the exit's observation
  holding of it, the yields holding of it and the step's output holding at
  the pushed environment ⟹ `passRefined` types the edge's environment. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Refined
variable {ι : Type} [DecidableEq ι]

/-- `run`'s `outAll`: the step's output with its links restated on every
slot of their classes over the pushed context. -/
def passOutAll (G : NormalGraph ι) (c : PointClaim ι) (stepOut : HeapKnowledge.Knowledge) :
    HeapKnowledge.Knowledge :=
  KnowledgeExpand.expandLinks (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G c.context) 1) stepOut

/-- `run`'s `refinedΓ`: the edge's context as the yields `ysAll` refine it,
through the links of `out`, at the arm `first`. -/
def passRefined (G : NormalGraph ι) (c : PointClaim ι) (k : Continuation) (ysAll : List (PromiseCalls.Yield ι))
    (out : HeapKnowledge.Knowledge) (first : Bool) : List (Ty ι) :=
  let pushedRefine := fun facts => PromiseCalls.refineBy G (c.type :: c.context)
    (PromiseCalls.aliasFacts out.links facts 1) 0
  let keptRefine := fun facts => PromiseCalls.refineBy G c.context
    (PromiseCalls.aliasFacts (HeapKnowledge.dropResult out).links facts 0) 0
  let unconditional := PromiseCalls.yieldFacts ysAll false
  let conditional := PromiseCalls.yieldFacts ysAll true
  match k with
  | .bind _ => pushedRefine unconditional
  | .effect _ => keptRefine unconditional
  | .branch .. => keptRefine (if first then conditional else unconditional)
  | .branchBind .. => pushedRefine (if first then conditional else PromiseCalls.yieldFacts ysAll false true)
  | .tagBind tg .. => pushedRefine (if first then PromiseCalls.yieldFacts ysAll (ControlFlow.truthyBoolean G tg c.type)
      else unconditional)
  | .ret => c.context

/-- `run`'s arm of an exit into `t`: whether `t` is the continuation's first
successor. -/
def passFirst (k : Continuation) (t : Target) : Bool := t == (successors k).headD t

/-- **(Pass premise, D13) The two arms of a test enter distinct targets**:
where they do not, `passFirst` reads both exits as the first arm. -/
def ArmsDistinct (k : Continuation) : Prop := ∀ y n, successors k = [y, n] → y ≠ n

omit [DecidableEq ι] in
/-- A value of a test's shape whose truthiness is the arm's answer is that
arm's Boolean. -/
theorem truthy_arm {v : Tm} (hv : v = .tru ∨ v = .fls) {q : Bool} (ht : tagHolds .truthy v = q) :
    v = if q then .tru else .fls := by
  rcases hv with rfl | rfl <;> cases q <;> simp_all [tagHolds]

/-- **The refined context types the edge's environment**: at a normal exit
of the node, its arm by position, the arms distinct, where the pushed
environment meets the claim's type and context, the value has the
continuation's shape, the exit's observation holds of it, the yields `ysAll`
hold of it and the step's output holds at the pushed environment. -/
theorem passRefined_env {G : NormalGraph ι} {c : PointClaim ι} {node : Node} {ysAll : List (PromiseCalls.Yield ι)}
    {stepOut : HeapKnowledge.Knowledge} {t : Target} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    (hm : Exit.normal t pushed observed promote ∈ Exit.ofNode node) (harms : ArmsDistinct node.continuation)
    {ρ : Env} {s : IndexedHeap} {v : Tm}
    (he : EnvOk G (c.type :: c.context) (push v ρ) s.n s.W) (hshape : ShapeOk v node.continuation)
    (ho : ObservedOk observed promote v) (hy : PromiseCalls.YieldsOk G ysAll ρ s.n s.W v)
    (hout : HeapKnowledge.Holds stepOut (push v ρ) s.h) :
    EnvOk G (passRefined G c node.continuation ysAll (passOutAll G c stepOut) (passFirst node.continuation t))
      (if pushed then push v ρ else ρ) s.n s.W := by
  cases s with
  | mk n W h pos adm hh =>
  cases n with
  | zero => exact absurd pos (Nat.lt_irrefl 0)
  | succ n =>
    simp only at he hy hout ⊢
    have heΓ : EnvOk G c.context ρ (n + 1) W := envOk_tail he
    have hv : meaning G c.type (n + 1) W v := he.2 0 _ rfl
    have hl := (KnowledgeExpand.expandLinks_holds (setsCtx_push_ok heΓ v) hout).2.2.1
    have hld := (HeapKnowledge.dropResult_holds
      (KnowledgeExpand.expandLinks_holds (setsCtx_push_ok heΓ v) hout)).2.2.1
    unfold Exit.ofNode at hm
    replace hm := (List.mem_append.mp hm).resolve_right (by simp)
    unfold passRefined passFirst
    split at hm
    · simp at hm
    · rename_i t0 hk
      simp only [List.mem_singleton, Exit.normal.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      rw [hk]
      exact refined_push_aliased hh heΓ hv hy (fun h => by cases h) (fun h => by cases h) hl
    · rename_i t0 hk
      simp only [List.mem_singleton, Exit.normal.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      rw [hk]
      exact refined_env_aliased hh heΓ hy (fun h => by cases h) (fun h => by cases h) hld
    · rename_i y0 n0 hk
      rw [hk] at hshape harms ⊢
      have hd := harms y0 n0 rfl
      simp only [List.mem_cons, Exit.normal.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · have hv1 : v = .tru := by simpa using truthy_arm hshape ho
        simp only [successors, List.headD_cons, beq_self_eq_true, ↓reduceIte]
        exact refined_env_aliased hh heΓ hy (fun _ => hv1) (fun h => by cases h) hld
      · have hne : (t == y0) = false := by simpa using fun h => hd h.symm
        simp only [successors, List.headD_cons, hne, Bool.false_eq_true, ↓reduceIte]
        exact refined_env_aliased hh heΓ hy (fun h => by cases h) (fun h => by cases h) hld
    · rename_i y0 n0 hk
      rw [hk] at harms ⊢
      have hd := harms y0 n0 rfl
      simp only [List.mem_cons, Exit.normal.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · have hv1 : v = .tru := by simpa [ObservedOk, BranchRefinement.Observation.holds] using ho
        simp only [successors, List.headD_cons, beq_self_eq_true, ↓reduceIte]
        exact refined_push_aliased hh heΓ hv hy (fun _ => hv1) (fun h => by cases h) hl
      · have hv0 : v = .fls := by simpa [ObservedOk, BranchRefinement.Observation.holds] using ho
        have hne : (t == y0) = false := by simpa using fun h => hd h.symm
        simp only [successors, List.headD_cons, hne, Bool.false_eq_true, ↓reduceIte]
        exact refined_push_aliased hh heΓ hv hy (fun h => by cases h) (fun _ => hv0) hl
    · rename_i tg y0 n0 hk
      rw [hk] at harms ⊢
      have hd := harms y0 n0 rfl
      simp only [List.mem_cons, Exit.normal.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · simp only [successors, List.headD_cons, beq_self_eq_true, ↓reduceIte]
        refine refined_push_aliased hh heΓ hv hy (fun hb => ?_) (fun h => by cases h) hl
        simp only [ControlFlow.truthyBoolean, Bool.and_eq_true, beq_iff_eq] at hb
        obtain ⟨rfl, hb⟩ := hb
        have ht : tagHolds .truthy v = true := by
          simpa [ObservedOk, BranchRefinement.Observation.holds, protoFree] using ho
        simpa using truthy_arm (BranchRefinement.onlyBoolean_sound hb hv) ht
      · have hne : (t == y0) = false := by simpa using fun h => hd h.symm
        simp only [successors, List.headD_cons, hne, Bool.false_eq_true, ↓reduceIte]
        exact refined_push_aliased hh heΓ hv hy (fun h => by cases h) (fun h => by cases h) hl

omit [DecidableEq ι] in
/-- **An unobserved edge the edge search accepts gives the target's types**
(`checkedEdge_env` with no observation, which reads no fact). -/
theorem checkedEdge_env_none [Hashable ι] [DecidableEq ι] [Instantiates ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {claimed : Array (PointClaim ι)} {Γ Δ : List (Ty ι)} {t : Target} {k : HeapKnowledge.Knowledge}
    {answers : Answered G} {ρ : Env} {n : Nat} {W : WorldT (n + 1)}
    (hce : (checkedEdge G images claimed Δ Γ t none k answers).1 = true) (he : EnvOk G Γ ρ (n + 1) W) :
    EnvOk G Δ (PointClaims.mapEnv t.mapping ρ) (n + 1) W := by
  unfold checkedEdge at hce
  simp only at hce
  obtain ⟨p, -, hp⟩ := option_any_some hce
  unfold edgeEvidenceChecked at hp
  rcases Bool.or_eq_true_iff.mp hp with hu | hc
  · exact (unsatisfiable_sound hu he).elim
  · exact (PointClaims.checkMapped_sound hc).env he

/-- **The target's types from an edge checked at the refined context**
(`refinedEdge_env`): where `checkedEdge` accepts the edge at `passRefined`
over the step's output (`passOutAll`), under `passRefined_env`'s premises,
the target's context types the mapped environment. -/
theorem refinedEdge_env [Hashable ι] [Instantiates ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {claimed : Array (PointClaim ι)} {c : PointClaim ι} {node : Node} {ysAll : List (PromiseCalls.Yield ι)}
    {stepOut : HeapKnowledge.Knowledge} {Δ : List (Ty ι)} {t : Target} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool} {answers : Answered G}
    (hm : Exit.normal t pushed observed promote ∈ Exit.ofNode node) (harms : ArmsDistinct node.continuation)
    (hce : (checkedEdge G images claimed Δ
      (passRefined G c node.continuation ysAll (passOutAll G c stepOut) (passFirst node.continuation t)) t observed
      (passOutAll G c stepOut) answers).1 = true)
    {ρ : Env} {s : IndexedHeap} {v : Tm}
    (he : EnvOk G (c.type :: c.context) (push v ρ) s.n s.W) (hshape : ShapeOk v node.continuation)
    (ho : ObservedOk observed promote v) (hy : PromiseCalls.YieldsOk G ysAll ρ s.n s.W v)
    (hout : HeapKnowledge.Holds stepOut (push v ρ) s.h) :
    EnvOk G Δ (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) s.n s.W := by
  have hr := passRefined_env hm harms he hshape ho hy hout
  have hpo := (ofNode_flags hm).1
  cases s with
  | mk n W h pos adm hh =>
  cases n with
  | zero => exact absurd pos (Nat.lt_irrefl 0)
  | succ n =>
    simp only at he hout hr ⊢
    cases observed with
    | none => exact checkedEdge_env_none hce hr
    | some o =>
      have hp : pushed = true := hpo rfl
      subst hp
      simp only [↓reduceIte] at hr ⊢
      exact checkedEdge_env hce (KnowledgeExpand.expandLinks_holds (setsCtx_push_ok (envOk_tail he) v) hout) hr hh
        (fun o' ho' => by obtain rfl := Option.some.inj ho'; simpa [push, ObservedOk] using ho)

end Refined

end Verification.TolerantFrames
