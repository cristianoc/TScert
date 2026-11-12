import Verification.Programs.TolerantFramesMergeHead
import Verification.Programs.TolerantFramesStepLinkReturns

/-! # Tolerant frames: one obligation per node of the pass

The graph invariant (`TolerantFramesMergeGraph`) reads a node's assertion as
its entry state holding (`passPre`). A node's step needs, beside the state,
the node's context's types at its environment (`checkedStep_parts`'s
`EnvOk` premise), which no state carries: the pass checks them on every edge
into the node (the edge's type check). This module carries them in the node
assertion (`passPreT`, `edgePreT`), proves graph safety from the typed
assertions exactly as `run_sound_of_walk` does from the untyped ones
(`run_sound_of_walk_typed`, whose entry premise `EntriesFromEdges` is the
untyped one), and composes a step's parts with its exits' obligations into
`NodeObligations` (`nodeObligations_of_parts`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Trace

/-- **A run's endpoint is reached**: a judgment's normal post may also state
that its value is reached from the judged term by a run. -/
theorem safePostExc_trace {Ξ T : Fam} {Q : Post} {R : Heap → Prop} :
    ∀ {n W h t}, SafePostExc Ξ T Q R n W h t →
      SafePostExc Ξ T (fun h' v => Q h' v ∧ ∃ k, Steps k h t h' v) R n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with (⟨hv, hT, hq⟩ | ⟨hx, hr⟩) | ⟨U, h', t', hx, hu, st, hh, hs'⟩
    · exact .inl (.inl ⟨hv, hT, hq, 0, .refl⟩)
    · exact .inl (.inr ⟨hx, hr⟩)
    · refine .inr ⟨U, h', t', hx, hu, st, hh, ?_⟩
      exact SafePostExc.weaken (fun _ _ ⟨hq, k, hk⟩ => ⟨hq, k + 1, .next st hk⟩) (fun _ h => h) (ih hs')

end Trace

section Typed
variable {ι : Type}

/-- **The typed node assertion**: the pass's node assertion (`passPre`) and
the node's context `ctx l` typing its environment. -/
def passPreT (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι)) :
    Nat → Assertion :=
  fun l ρ m s => passPre G w startNames ρ0 l ρ m s ∧ EnvOk G (ctx l) ρ s.n s.W

/-- **The typed edge assertion**: an edge state into `t` holds (`edgePre`) and
`t`'s context types the environment. -/
def edgePreT (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι)) :
    Nat → Assertion :=
  fun t ρ m s => edgePre G w startNames ρ0 t ρ m s ∧ EnvOk G (ctx t) ρ s.n s.W

/-- **Each visited node's step and edges deliver, typed**: `StepEdgesSound`
at the typed node and edge assertions. -/
def StepEdgesSoundT (P : ControlFlow.Program) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (ctx : Nat → List (Ty ι)) (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (m : Nat) : Prop :=
  ∀ l ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s → ∃ node, P[l]? = some node ∧
    ∃ (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
      SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
        s.n s.W s.h (instantiate 0 ρ node.expression) ∧
      NodeObligations (edgePreT G w startNames ρ0 ctx) Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s
        node.continuation node.handler

theorem envOk_admissible {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {s s' : IndexedHeap}
    (ha : Admissible s s') (he : EnvOk G Γ ρ s.n s.W) : EnvOk G Γ ρ s'.n s'.W :=
  he.transfer s'.n ha.1 s'.W ha.2

theorem passPreT_adminClosed {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {m : Nat} : AdminClosed (passPreT G w startNames ρ0 ctx) m :=
  fun l ρ s s' ha hh ⟨hp, he⟩ => ⟨passPre_adminClosed l ρ s s' ha hh hp, envOk_admissible ha he⟩

variable [DecidableEq ι] [Hashable ι] in
/-- **The pass's graph is safe from the start's typed entry**: the walk built
as `Traversed` states, its steps and edges delivering at the typed
assertions, its heads entered and its merges' side conditions holding. The
entries follow from the untyped `EntriesFromEdges`: the types an edge
establishes are the target's. -/
theorem run_sound_of_walk_typed {P : ControlFlow.Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {ρ0 : Env} {ctx : Nat → List (Ty ι)} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} (hT : Traversed G w startNames given ctx edgesIn fresh)
    (hstep : StepEdgesSoundT P G w startNames ρ0 ctx Ξres Tres Qres Rres m)
    (hheads : HeadsEntered G w startNames ρ0 given m) (hmerges : MergesSound G w given ctx edgesIn)
    {start : Nat} {s : IndexedHeap} (hpre : passPreT G w startNames ρ0 ctx start ρ0 m s) :
    ControlFlow.SafeGraph Ξres P Tres s.n s.W s.h (.at start ρ0) := by
  have hentries := entries_of_traversed (ρ0 := ρ0) (m := m) hT hheads hmerges
  refine graph_safe_at (pre := passPreT G w startNames ρ0 ctx) (Qres := Qres) (Rres := Rres) ?_
    passPreT_adminClosed hpre
  intro l ρ s hp
  obtain ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hsafe, ho⟩ := hstep l ρ s hp
  exact ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hsafe,
    nodeObligations_mono (fun t ρ s h => ⟨hentries t ρ s h.1, h.2⟩) ho⟩

/-- **The heads a walk records its own entry for are entered**: where every
edge state the walk records into a head is the head's entry state and
implications, `HeadsEntered` holds. The edge into a head establishes the
head's entry (`headEntry_holds` from `HeadEstablishes`), and the walk records
that state as the edge's. -/
theorem headsEntered_of_recorded {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {given : Nat → Bool} {m : Nat}
    (hrec : ∀ t, given t = true → ∀ e ∈ w.incoming t, e = (w.entry t, w.implies t)) :
    HeadsEntered G w startNames ρ0 given m := by
  intro t ρ s hg ⟨e, he, hh⟩
  rw [hrec t hg e he] at hh
  exact hh

end Typed

section Compose
variable {ι : Type}

/-- **A node's obligations from its step's parts.** Where the step's parts
hold at the node (`StepParts`, from `checkedStep_parts`) and the node's
context types its environment: with `T` the claim's type, the shape a
continuation needs given by the claim's type (`hshape`), each normal exit's
target obligation given by the state after the step, the pushed
environment's types and the rule's output (`hnormal`), and each throw's by
the throw state, the context's types and the raised value's family
(`hraise`), the node meets `NodeObligations` with its local judgment. -/
theorem nodeObligations_of_parts {G : NormalGraph ι} {A : Ty ι} {Γ : List (Ty ι)} {cn ce : Footprints.Closed}
    {t : Tm} {out : HeapKnowledge.Knowledge} {Fn Fe : Assertion} {ρ : Env} {m : Nat} {s : IndexedHeap}
    {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {k : Continuation} {x : Option Target}
    (hp : StepParts G A cn ce t out Fn Fe ρ m s) (he : EnvOk G Γ ρ s.n s.W)
    (hshape : ∀ j (U : WorldT (j + 1)) v, meaning G A (j + 1) U v → ShapeOk v k)
    (hnormal : ∀ (s' : IndexedHeap) v, Admissible s s' → isVal v = true → Fn (push v ρ) m s' →
      EnvOk G (A :: Γ) (push v ρ) s'.n s'.W → HeapKnowledge.Holds out (push v ρ) s'.h →
      NormalTarget pre Tres Qres ρ m s' v k)
    (hraise : ∀ (s' : IndexedHeap) e, Admissible s s' → Fe ρ m s' → EnvOk G Γ ρ s'.n s'.W → Scoped 0 e →
      excOf G s'.n s'.W e → RaiseTarget pre Ξres Rres ρ m s' e x) :
    SafePostExc (excOf G) (meaning G A)
      (fun h' v => cn.Holds s.h h' ∧ (HeapKnowledge.Holds out (push v ρ) h' ∧
        ∃ k, Steps k s.h (instantiate 0 ρ t) h' v))
      (fun h' => ce.Holds s.h h' ∧ True) s.n s.W s.h (instantiate 0 ρ t) ∧
    NodeObligations pre Ξres Tres Qres Rres (excOf G) (meaning G A) cn ce
      (fun h' v => HeapKnowledge.Holds out (push v ρ) h' ∧ ∃ k, Steps k s.h (instantiate 0 ρ t) h' v)
      (fun _ => True) ρ m s k x := by
  obtain ⟨hj, hn, hx⟩ := hp
  refine ⟨SafePostExc.weaken (fun _ _ ⟨⟨hc, ho⟩, hk⟩ => ⟨hc, ho, hk⟩) (fun _ h => h) (safePostExc_trace hj),
    ⟨fun j U h v _ hT _ _ => hshape j U v hT, ?_, ?_⟩⟩
  · intro s' v ha hv ⟨U, hU, hT⟩ ⟨ho, k', hk⟩
    have hT' : meaning G A s'.n s'.W v := by
      have := (meaning_adm G A).down_le (s'.n + 1) s'.n (Nat.le_succ _) U v hT
      rwa [hU] at this
    exact hnormal s' v ha.1 hv (hn k' s'.h v s' hk hv ha rfl ho) ((envOk_admissible ha.1 he).push hT') ho
  · intro s' e ha hsc ⟨U, hU, hΞ⟩ _
    have hΞ' : excOf G s'.n s'.W e := by
      have := (builtinExc_adm G _).down_le (s'.n + 1) s'.n (Nat.le_succ _) U e hΞ
      rwa [hU] at this
    exact hraise s' e ha.1 (hx s' ha) (envOk_admissible ha.1 he) hsc hΞ'

end Compose

end Verification.TolerantFrames
