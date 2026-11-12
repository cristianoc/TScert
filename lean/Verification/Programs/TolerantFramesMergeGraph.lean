import Verification.Programs.TolerantFramesMergeChecked
import Verification.Programs.TolerantFramesInvocation

/-! # Tolerant frames: the pass's graph invariant

The node assertion of the pass at a label it visits is that its entry state
holds (`passPre`): the state `StateHolds` reads, with the invocation's start
names holding its entry values. A walk of the pass (`Walk`) records each
visited node's entry state and implications and the states the edges carry
into each node. `entries_of_traversed` gives a node's entry state wherever
an edge state into it holds (`EntriesFromEdges`) from the walk's
construction (`Traversed`: one predecessor's state taken as it is, several
merged by `mergeState`, a loop head's given state), the merges' premises
(`MergesSound`) and the head entry's (`HeadsEntered`); with each node's step
and edges delivering, `run_sound_of_walk_typed` instantiates
`graph_safe_at` with the typed node assertion. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open ProgramTyping PositiveGraphs

section Graph
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- **A walk of the pass**: the labels it visits, each node's entry state
and implications, and the states (with their implications) edges carry into
each node. -/
structure Walk (ι : Type) where
  visited : Nat → Prop
  entry : Nat → SinglePass.State
  implies : Nat → List (PromiseCalls.Implication ι)
  incoming : Nat → List (SinglePass.State × List (PromiseCalls.Implication ι))

/-- **The pass's node assertion**: at a visited label, its entry state
holds, the start names `startNames` holding the entry values `ρ0`. -/
def passPre (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) : Nat → Assertion :=
  fun l ρ m s => w.visited l ∧ StateHolds G (w.entry l) (w.implies l) startNames ρ0 ρ m s

/-- An edge state into `t` holds. -/
def edgePre (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) : Nat → Assertion :=
  fun t ρ m s => ∃ e ∈ w.incoming t, StateHolds G e.1 e.2 startNames ρ0 ρ m s

/-- **A node's entry state holds wherever an edge state into it holds.** -/
def EntriesFromEdges (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (m : Nat) : Prop :=
  ∀ t ρ (s : IndexedHeap), edgePre G w startNames ρ0 t ρ m s → passPre G w startNames ρ0 t ρ m s

/-- The node obligations are monotone in the node assertions. -/
theorem nodeObligations_mono {pre pre' : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop}
    {cn ce : Footprints.Closed} {Qn : Post} {Qe : Heap → Prop} {ρ : Env} {m : Nat} {s₀ : IndexedHeap}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} (hpre : ∀ l ρ s, pre l ρ m s → pre' l ρ m s)
    (ho : NodeObligations pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x) :
    NodeObligations pre' Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x where
  shape := ho.shape
  normal := fun s v ha hv hT hQ => by
    have := ho.normal s v ha hv hT hQ
    cases k with
    | ret => exact this
    | bind l => exact hpre _ _ _ this
    | effect l => exact hpre _ _ _ this
    | branch y n =>
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact .inl ⟨h1, hpre _ _ _ h2⟩
      · exact .inr ⟨h1, hpre _ _ _ h2⟩
    | branchBind y n => exact this.imp (fun h => ⟨h.1, hpre _ _ _ h.2⟩) (fun h => ⟨h.1, hpre _ _ _ h.2⟩)
    | tagBind tg y n => exact this.imp (fun h => ⟨h.1, hpre _ _ _ h.2⟩) (fun h => ⟨h.1, hpre _ _ _ h.2⟩)
  raise := fun s e ha he hΞ hQ => by
    have := ho.raise s e ha he hΞ hQ
    cases x with
    | some l => exact hpre _ _ _ this
    | none => exact this

omit [DecidableEq ι] [Hashable ι] in
/-- **The pass's node assertions survive the administrative steps**: a
state's meaning reads the heap, and the world only through the
implications' types, which admissibility keeps (`impliesOk_admissible`). -/
theorem passPre_adminClosed {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env} {m : Nat} :
    AdminClosed (passPre G w startNames ρ0) m := by
  intro l ρ s s' ha hh ⟨hv, η, hsl, hn, hi, hf, hst⟩
  refine ⟨hv, η, hsl, fun a ha' => ?_, impliesOk_admissible ha hi, hf, hst⟩
  rw [hh]; exact hn a ha'

/-! ## The walk's construction -/

/-- **The walk the pass's driver builds**: a node with given facts (a loop
head or the start) enters with its head entry (`given`); a node with one
incoming edge state takes it as it is; a node with several takes their merge
(`SinglePass.mergeState`), over the context `ctx t`, the merge's edges
`edgesIn t` and fresh counter `fresh t`, with the merge's premises: each
incoming state has the context's width, a well-formed store and names below
the counter, and the start names are below it; every node an edge state
enters is visited. -/
structure Traversed (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (given : Nat → Bool)
    (ctx : Nat → List (Ty ι))
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (fresh : Nat → Nat) : Prop where
  visited : ∀ t, w.incoming t ≠ [] → w.visited t
  single : ∀ t e, given t = false → w.incoming t = [e] → w.entry t = e.1 ∧ w.implies t = e.2
  merge : ∀ t, given t = false → 2 ≤ (w.incoming t).length →
    w.entry t = (SinglePass.mergeState G (ctx t) ((w.incoming t).map (·.1)) (edgesIn t) (fresh t)).state ∧
    w.implies t = (SinglePass.mergeState G (ctx t) ((w.incoming t).map (·.1)) (edgesIn t) (fresh t)).implies
  width : ∀ t, given t = false → 2 ≤ (w.incoming t).length → ∀ e ∈ w.incoming t, e.1.names.length = (ctx t).length
  wf : ∀ t, given t = false → 2 ≤ (w.incoming t).length → ∀ e ∈ w.incoming t, StoreWF e.1.store
  below : ∀ t, given t = false → 2 ≤ (w.incoming t).length → ∀ e ∈ w.incoming t, StateBelow e.1 (fresh t)
  startBelow : ∀ t, given t = false → 2 ≤ (w.incoming t).length → ∀ x ∈ startNames, x < fresh t

/-- **(Named hypothesis) A head's given state holds where an edge state
into it holds**: the head entry's theorem from the edge check
(`HeadEstablishes`, Leg 8's interface with the edge check). -/
def HeadsEntered (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (given : Nat → Bool)
    (m : Nat) : Prop :=
  ∀ t ρ (s : IndexedHeap), given t = true → edgePre G w startNames ρ0 t ρ m s →
    StateHolds G (w.entry t) (w.implies t) startNames ρ0 ρ m s

/-- **The merges' premises**: the pass's `linearNear` is its search on fuel
(`LinearNearFuelEq`), and at each merge the joined implications it keeps
(`joinedChecked`) hold wherever an edge state into the merge holds. -/
def MergesSound (G : NormalGraph ι) (w : Walk ι) (given : Nat → Bool) (ctx : Nat → List (Ty ι))
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) : Prop :=
  LinearNearFuelEq ∧ ∀ t, given t = false → 2 ≤ (w.incoming t).length →
    ∀ startNames ρ0 m ρ (s : IndexedHeap), edgePre G w startNames ρ0 t ρ m s →
      PromiseCalls.ImpliesOk G (joinedChecked G (ctx t) (edgesIn t)) ρ s.n s.W

/-- **Entry states hold where edge states into them do**, from the walk's
construction: a head by `HeadsEntered`, one predecessor as it is, several by
the merge theorem (`mergeState_holds_checked`) with its premises. -/
theorem entries_of_traversed {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} {m : Nat} (hT : Traversed G w startNames given ctx edgesIn fresh)
    (hheads : HeadsEntered G w startNames ρ0 given m) (hmerges : MergesSound G w given ctx edgesIn) :
    EntriesFromEdges G w startNames ρ0 m := by
  intro t ρ s he
  obtain ⟨e, hein, heh⟩ := he
  have hne : w.incoming t ≠ [] := List.ne_nil_of_mem hein
  refine ⟨hT.visited t hne, ?_⟩
  cases hg : given t with
  | true => exact hheads t ρ s hg ⟨e, hein, heh⟩
  | false =>
    by_cases h2 : 2 ≤ (w.incoming t).length
    · obtain ⟨hentry, himp⟩ := hT.merge t hg h2
      rw [hentry, himp]
      obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hein
      obtain ⟨hnear, hside⟩ := hmerges
      have hI := hside t hg h2
      have hp' : p < ((w.incoming t).map (·.1)).length := by simpa using hp
      refine mergeState_holds_checked (implies := (w.incoming t)[p].2) hp' ?_ ?_ ?_ (hT.startBelow t hg h2) hnear
        (hI startNames ρ0 m ρ s ⟨_, List.getElem_mem hp, heh⟩) (by simpa using heh)
      · intro q hq; obtain ⟨e', he', rfl⟩ := List.mem_map.mp hq; exact hT.width t hg h2 e' he'
      · intro q hq; obtain ⟨e', he', rfl⟩ := List.mem_map.mp hq; exact hT.wf t hg h2 e' he'
      · intro q hq; obtain ⟨e', he', rfl⟩ := List.mem_map.mp hq; exact hT.below t hg h2 e' he'
    · have hone : w.incoming t = [e] := by
        match hl : w.incoming t, hein with
        | [e'], hein' => rw [List.mem_singleton.mp hein']
        | [], hein' => cases hein'
        | _ :: _ :: _, _ => rw [hl] at h2; simp at h2
      obtain ⟨hentry, himp⟩ := hT.single t e hg hone
      rw [hentry, himp]; exact heh

omit [Hashable ι] in
/-- **The start's node assertion holds at the unit's entry**: where the walk
enters the start with its head entry over the given invariant (`startGiven`)
and the pass's entry check accepts, the start's state holds at every entry
meeting the inputs, the entry separation and the entry index facts
(`entry_stateHolds`). -/
theorem start_passPre {G : NormalGraph ι} {w : Walk ι} {inputs : List (Ty ι)}
    {claims : List (CertificateProducer.PointClaim ι)} {start : Nat} {goal : ControlFlow.Goal ι}
    {written : Option HeapKnowledge.Knowledge} {supplied : List HeapKnowledge.IndexAtom}
    {givenImplies : List (PromiseCalls.Implication ι)} {givenArgs : List Nat} {givenInputs : List (Nat × Nat)}
    {entryIndices : List HeapKnowledge.IndexAtom} {entrySeparation : HeapSeparation.Separation} {fresh : Nat}
    (hacc : SinglePass.entryRefusal G inputs claims start goal written supplied givenImplies givenArgs givenInputs
      entryIndices entrySeparation = none)
    (hv : w.visited start)
    (hentry : w.entry start = (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true
      inputs.length fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs
      givenInputs givenImplies).1)
    (himp : w.implies start = (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true
      inputs.length fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs
      givenInputs givenImplies).2.1)
    {ρ : Env} {m : Nat} {s : IndexedHeap} (he : EnvOk G inputs ρ s.n s.W)
    (hs : HeapSeparation.Holds entrySeparation ρ) (hi : HeapKnowledge.IndexHolds entryIndices ρ s.h) :
    passPre G w (List.range inputs.length) ρ start ρ m s := by
  refine ⟨hv, ?_⟩
  rw [hentry, himp]
  exact (entry_stateHolds hacc he hs hi fresh).1

end Graph

end Verification.TolerantFrames
