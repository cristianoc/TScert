import Verification.Programs.TolerantFramesRunSound
import Verification.Programs.TolerantFramesDriverHeads

/-! # Tolerant frames: the driver's record read as the walk

`SinglePass.run` is `SinglePass.runWalk`'s record read by
`SinglePass.Walk.outcome`; `runWalk` sets up the walk and runs
`SinglePass.drive`, which visits the queue's first node on fuel. Proved
here about those functions: a drive that returns has visited its queue to
the end, each visit from the queue's first node (`Drives`,
`drives_of_drive`), so a property every visit keeps holds of its result
(`Drives.inv`); an accepted call is a walk that returned, its record
visiting at least the nodes the start reaches, its answers the call's
(`walk_of_accepts`, where a stopped walk is never accepted:
`WalkStopsRefuse`).

The record read as the proof's walk (`ofPass`): a label visited where its
record says so; its entry state and implications the recorded ones; the
states into a node other than a loop head those every processed edge
carried, each with its implications; into a loop head, its own entry,
where a processed edge enters it. With the loop heads, label contexts,
written assertions, merge edges and merge counters the call and the record
give (`passHeads`, `passCtx`, `passStated`, `passEdgesIn`, `passFresh`),
each edge state into a head is the head's entry by construction
(`ofPass_heads`). `RecordSound` is what the record must give beyond it, and
`run_traversedA` builds the walk of `RunTraversedA` from it. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules LabelStore

section Drive
variable {ι : Type} [DecidableEq ι] [Hashable ι] {G : NormalGraph ι}

/-- **The visits of a drive**: from `σ`, each step visits the queue's first
node over the rest of the queue (`SinglePass.drive`'s step), until the queue
is empty at `σ'`. -/
inductive Drives (visit : SinglePass.WalkState ι G → Nat → Except (SinglePass.WalkStop ι G) (SinglePass.WalkState ι G)) :
    SinglePass.WalkState ι G → SinglePass.WalkState ι G → Prop where
  | done {σ} : σ.queue = [] → Drives visit σ σ
  | step {σ σ₁ σ'} {l : Nat} {rest : List Nat} : σ.queue = l :: rest → visit { σ with queue := rest } l = .ok σ₁ →
      Drives visit σ₁ σ' → Drives visit σ σ'

/-- **A drive that returns made its visits** (`Drives`). -/
theorem drives_of_drive {visit : SinglePass.WalkState ι G → Nat → Except (SinglePass.WalkStop ι G) (SinglePass.WalkState ι G)} :
    ∀ (fuel : Nat) (σ σ' : SinglePass.WalkState ι G), SinglePass.drive visit fuel σ = .ok σ' → Drives visit σ σ'
  | 0, σ, σ', h => by
    cases hq : σ.queue with
    | nil => simp only [SinglePass.drive, hq, Except.ok.injEq] at h; subst h; exact .done hq
    | cons l rest => simp [SinglePass.drive, hq] at h
  | fuel + 1, σ, σ', h => by
    cases hq : σ.queue with
    | nil => simp only [SinglePass.drive, hq, Except.ok.injEq] at h; subst h; exact .done hq
    | cons l rest =>
      simp only [SinglePass.drive, hq] at h
      cases hv : visit { σ with queue := rest } l with
      | error e => rw [hv] at h; cases h
      | ok σ₁ => rw [hv] at h; exact .step hq hv (drives_of_drive fuel σ₁ σ' h)

/-- A drive's result has an empty queue. -/
theorem Drives.queue {visit : SinglePass.WalkState ι G → Nat → Except (SinglePass.WalkStop ι G) (SinglePass.WalkState ι G)}
    {σ σ' : SinglePass.WalkState ι G} (h : Drives visit σ σ') : σ'.queue = [] := by
  induction h with
  | done hq => exact hq
  | step _ _ _ ih => exact ih

/-- **A property every visit keeps holds of a drive's result.** -/
theorem Drives.inv {visit : SinglePass.WalkState ι G → Nat → Except (SinglePass.WalkStop ι G) (SinglePass.WalkState ι G)}
    (Q : SinglePass.WalkState ι G → Prop)
    (hstep : ∀ σ σ₁ l rest, σ.queue = l :: rest → Q σ → visit { σ with queue := rest } l = .ok σ₁ → Q σ₁)
    {σ σ' : SinglePass.WalkState ι G} (h : Drives visit σ σ') (h0 : Q σ) : Q σ' := by
  induction h with
  | done _ => exact h0
  | step hq hv _ ih => exact ih (hstep _ _ _ _ hq h0 hv)

end Drive

section Record
variable {ι : Type} [Labels ι]

/-- The walk of a call (`SinglePass.runWalk` over its arguments). -/
def RunCall.walk {G : NormalGraph ι} {I : InstanceImageCheck G} (c : Target.RunCall G I) :
    Except (SinglePass.WalkStop ι G) (SinglePass.WalkState ι G × Nat) :=
  SinglePass.runWalk G I c.pool c.fuel c.P c.claims c.start c.inputs c.goal c.assertions c.cuts c.candidates
    c.entryIndices c.suggestions c.known c.codes c.aliases c.passChecker c.answers c.reference c.debugNode
    c.bound c.givenImplies c.givenArgs c.ensures c.givenInputs c.entrySeparation c.observe c.tracing
    c.observeEntry c.regional

/-- **An accepted call's walk**: either it stopped with an accepted
outcome, or it returned a record that visited at least the nodes the start
reaches, its answers those the call leaves (`run` is the record's
`Walk.outcome`). -/
theorem walk_of_accepts' {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I}
    {after : Answered G} (h : c.Accepts after) :
    (∃ stop : SinglePass.WalkStop ι G, RunCall.walk c = .error stop ∧ stop.1 = .accepted) ∨
      ∃ σ reach, RunCall.walk c = .ok (σ, reach) ∧ reach ≤ σ.walk.visited ∧ σ.answers = after := by
  obtain ⟨counts, trace, h⟩ := h
  unfold Target.RunCall.result SinglePass.run at h
  cases hw : RunCall.walk c with
  | error stop =>
    unfold RunCall.walk at hw
    rw [hw] at h
    simp only at h
    exact .inl ⟨stop, rfl, by rw [h]⟩
  | ok p =>
    obtain ⟨σ, reach⟩ := p
    unfold RunCall.walk at hw
    rw [hw] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨ho, -, ha, -⟩ := h
    refine .inr ⟨σ, reach, rfl, ?_, ha⟩
    unfold SinglePass.Walk.outcome at ho
    split at ho
    · cases ho
    · omega

variable (ι) in
/-- **(Named hypothesis) A stopped walk is never accepted**: every outcome
`runWalk` stops with is a refusal, a gap or an observation. The pass states
each one explicitly; a stop type without acceptance (a pass change) makes
this hold by its type. -/
def WalkStopsRefuse : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) (stop : SinglePass.WalkStop ι G),
    RunCall.walk c = .error stop → stop.1 ≠ .accepted

/-- **An accepted call's walk returned** (`walk_of_accepts'` and
`WalkStopsRefuse`). -/
theorem walk_of_accepts (hstop : WalkStopsRefuse ι) {G : NormalGraph ι} {I : InstanceImageCheck G}
    {c : Target.RunCall G I} {after : Answered G} (h : c.Accepts after) :
    ∃ σ reach, RunCall.walk c = .ok (σ, reach) ∧ reach ≤ σ.walk.visited ∧ σ.answers = after := by
  rcases walk_of_accepts' h with ⟨stop, hw, ha⟩ | h
  · exact (hstop G I c stop hw ha).elim
  · exact h

omit [Labels ι] in
/-- **The record read as the proof's walk**, with the loop heads `heads`: a
label visited where its record says so; its recorded entry state and
implications; into a node other than a head, the states and implications
the processed edges carried, in order; into a head, its own entry where a
processed edge enters it. -/
def ofPass (r : SinglePass.Walk ι) (heads : Nat → Bool) : Walk ι where
  visited l := ∃ x, r.labels[l]? = some x ∧ x.visited = true
  entry l := ((r.labels[l]?).bind (·.entry)).getD { names := [] }
  implies l := ((r.labels[l]?).map (·.implies)).getD []
  incoming t := if heads t then
      (if r.edges.toList.any (·.target.label == t) then
        [(((r.labels[t]?).bind (·.entry)).getD { names := [] }, ((r.labels[t]?).map (·.implies)).getD [])] else [])
    else ((r.incoming[t]?).getD []).zip ((r.incomingImpl[t]?).getD [])

omit [Labels ι] in
/-- **Each edge state into a head is the head's entry**, by the reading. -/
theorem ofPass_heads (r : SinglePass.Walk ι) (heads : Nat → Bool) :
    ∀ t, heads t = true → ∀ e ∈ (ofPass r heads).incoming t,
      e = ((ofPass r heads).entry t, (ofPass r heads).implies t) := by
  intro t ht e he
  simp only [ofPass, ht, if_true] at he
  split at he
  · exact List.mem_singleton.mp he
  · simp at he

/-- The loop heads `runWalk` marks: `loopHeads`' targets of retreating
edges, and the start. -/
def passIsHead (P : ControlFlow.Program) (start : Nat) : Array Bool :=
  if start < P.toArray.size then (SinglePass.loopHeads P.toArray start).1.set! start true
  else (SinglePass.loopHeads P.toArray start).1

/-- A call's loop heads, by label. -/
def passHeads {G : NormalGraph ι} {I : InstanceImageCheck G} (c : Target.RunCall G I) (t : Nat) : Bool :=
  (passIsHead c.P c.start)[t]?.getD false

/-- **A call's loop heads cut every cycle of the nodes `loopHeads`
reaches** (`loopHeads_cuts` under `LoopHeadsFuelEq`; the start marked
besides, `HeadsCutCycles.mono`). -/
theorem passHeads_cuts (heq : LoopHeadsFuelEq) {G : NormalGraph ι} {I : InstanceImageCheck G}
    (c : Target.RunCall G I) :
    HeadsCutCycles (nodeSucc c.P.toArray) c.P.toArray.size
      (fun t => (SinglePass.loopHeads c.P.toArray c.start).2[t]?.getD false) (passHeads c) := by
  refine HeadsCutCycles.mono (fun v hv => ?_) (loopHeads_cuts heq c.P.toArray c.start)
  unfold passHeads passIsHead
  split
  · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    split
    · rename_i hs
      subst hs
      by_cases hlt : c.start < (SinglePass.loopHeads c.P.toArray c.start).1.size
      · simp [hlt]
      · simp [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hv
    · exact hv
  · exact hv

/-- A call's label contexts: each label's claim's. -/
def passCtx {G : NormalGraph ι} {I : InstanceImageCheck G} (c : Target.RunCall G I) (t : Nat) : List (Ty ι) :=
  ((c.claims[t]?).map (·.context)).getD []

/-- A call's written assertions by label (`byLabel`, as `runWalk` reads
them). -/
def passStated {G : NormalGraph ι} {I : InstanceImageCheck G} (c : Target.RunCall G I) (t : Nat) :
    Option HeapKnowledge.Knowledge :=
  (CertificateProducer.byLabel c.P.toArray.size c.assertions)[t]?.getD none

omit [Labels ι] in
/-- A record's edges into each merge, as the merge reads them. -/
def passEdgesIn (r : SinglePass.Walk ι) (t : Nat) :
    List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping) :=
  (r.incomingEdges[t]?).getD []

omit [Labels ι] in
/-- A record's fresh counter at each merge, where the merge started. -/
def passFresh (r : SinglePass.Walk ι) (t : Nat) : Nat :=
  (((r.labels[t]?).bind (·.merge)).map (·.2)).getD 0

/-- **What the driver's record of a returned walk gives**, read as the
proof's walk (`ofPass`): every visited node checked with its searches as
oracles; the walk's construction with the written facts (`TraversedA`);
the start entered. -/
structure RecordSound (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
    (σ : SinglePass.WalkState ι G) : Prop where
  node : ∀ l, (ofPass σ.walk (passHeads c)).visited l →
    Nonempty (NodeChecked G I c.codes c.passChecker c.P (ofPass σ.walk (passHeads c)) (List.range c.inputs.length)
      (passCtx c) l)
  traversed : TraversedA G (ofPass σ.walk (passHeads c)) (List.range c.inputs.length) (passHeads c) (passCtx c)
    (passEdgesIn σ.walk) (passFresh σ.walk) (passStated c)
  start : StartEntered c (ofPass σ.walk (passHeads c)) (passCtx c) (passStated c)

variable (ι) in
/-- **(Named hypothesis) The driver's record of an accepted call is
sound** (`RecordSound`): a walk that returned, visiting at least the nodes
the start reaches, whose final summaries are sound. -/
def RecordsSound : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) (σ : SinglePass.WalkState ι G) reach,
    RunCall.walk c = .ok (σ, reach) → reach ≤ σ.walk.visited →
    SummariesSound G I σ.answers.summaries.toList → RecordSound G I c σ

/-- **(`run_traversedA`) The driver's walk from its record**: an accepted
call's walk returned (`walk_of_accepts`), its record read as the proof's
walk (`ofPass`), each edge state into a head the head's entry
(`ofPass_heads`), the rest from `RecordsSound`. -/
theorem run_traversedA (hstop : WalkStopsRefuse ι) (hrec : RecordsSound ι) : RunTraversedA ι := by
  intro G I c after hacc hsums
  obtain ⟨σ, reach, hw, hle, ha⟩ := walk_of_accepts hstop hacc
  have hr := hrec G I c σ reach hw hle (ha ▸ hsums)
  exact ⟨⟨ofPass σ.walk (passHeads c), passHeads c, passCtx c, passEdgesIn σ.walk, passFresh σ.walk,
    passStated c, fun l hl => Classical.choice (hr.node l hl), hr.traversed, ofPass_heads σ.walk (passHeads c),
    hr.start, fun _ => rfl⟩⟩

/-- **THE GRAPH THEOREM from the driver's record** (`run_sound` with
`RunTraversedA` from `run_traversedA`): from a stopped walk never being
accepted (`WalkStopsRefuse`), the record's soundness (`RecordsSound`), the
nodes' meaning (`NodesMean`), the merges' premises (`LinearNearFuelEq`,
`MergeExitsJoined`), the per-node hypotheses of the guarantee's other
fields and the call's assertions at their labels, an accepted call of the
pass guarantees `GraphGuarantee` of its options at its inputs. -/
theorem run_sound_18b (hstop : WalkStopsRefuse ι) (hrec : RecordsSound ι) (hmean : NodesMean ι)
    (hnear : LinearNearFuelEq) (hjoin : MergeExitsJoined ι) (hfoot : FootprintsKept ι) (hret : ReturnsKept ι)
    (hreg : RegionsHeld ι) (hasr : AssertionsLabelled ι) : Target.RunSound ι :=
  run_sound (run_traversedA hstop hrec) hmean hnear hjoin hfoot hret hreg hasr

end Record

end Verification.TolerantFrames
