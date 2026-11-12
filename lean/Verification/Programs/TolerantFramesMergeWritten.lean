import Verification.Programs.TolerantFramesNodeAsserts
import Verification.Programs.TolerantFramesMergeExits

/-! # Tolerant frames: a node's entry with its written assertion's facts

At a node other than a loop head, the pass adds the facts of the node's
written assertion to the state it enters with (`SinglePass.runWalk`'s
visit: the single incoming state or the merge, then the written facts,
each renamed from its slot to the name the slot holds), and records that
state as the label's entry (`SinglePass.LabelWalk.entry`). `withWritten`
is that addition; `withWritten_holds`: the state with the facts added
holds where the state holds and the written assertion holds at the slots.

`TraversedA` states the walk's construction over the entries before the
addition (`Traversed` of the walk with those entries) and each entry the
addition over them at a node other than a head. `entry_of_edgeA`: a
node's entry holds where an edge state into it, the node's written
assertion and, at a merge, the joined implications hold. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open ProgramTyping PositiveGraphs PositiveRules

section Written
variable {ι : Type}

/-- **The written facts added to an entry state**: each atom of the
written assertion renamed from its slot to the name the state's slot holds
and added to the store (`Store.add`), an atom with a slot no name holds
left out; the state itself where the label states no assertion. -/
def withWritten (req : Option HeapKnowledge.Knowledge) (e : SinglePass.State) : SinglePass.State :=
  match req with
  | some req => { e with store := (SinglePass.atomsOf req).foldl (fun s a => match a.rename (fun i => e.names[i]?) with
      | some b => s.add b | none => s) e.store }
  | none => e

theorem withWritten_names (req : Option HeapKnowledge.Knowledge) (e : SinglePass.State) :
    (withWritten req e).names = e.names := by
  cases req <;> rfl

theorem withWritten_fresh (req : Option HeapKnowledge.Knowledge) (e : SinglePass.State) :
    (withWritten req e).fresh = e.fresh := by
  cases req <;> rfl

/-- **The written facts keep the store well-formed** (`add_wf`). -/
theorem withWritten_wf {req : Option HeapKnowledge.Knowledge} {e : SinglePass.State} (hw : StoreWF e.store) :
    StoreWF (withWritten req e).store := by
  cases req with
  | none => exact hw
  | some k =>
    refine foldl_inv StoreWF _ _ _ hw fun a _ st hst => ?_
    split
    · exact add_wf hst _
    · exact hst

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- **An entry with its written facts holds** where the entry holds and the
written assertion holds at the slots: each added fact is a written atom
renamed from a slot to the name holding its value (`atomHolds_rename`,
`add_ok`). -/
theorem withWritten_holds {G : NormalGraph ι} {req : Option HeapKnowledge.Knowledge} {e : SinglePass.State}
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {ρ0 ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G e I start ρ0 ρ m s) (hA : ∀ k, req = some k → HeapKnowledge.Holds k ρ s.h) :
    StateHolds G (withWritten req e) I start ρ0 ρ m s := by
  cases req with
  | none => exact hS
  | some k =>
    obtain ⟨η, hsl, hn, hi, hf, hst⟩ := hS
    refine ⟨η, hsl, ?_, hi, hf, hst⟩
    show StoreOk _ η s.h
    refine foldl_inv (fun st => StoreOk st η s.h) _ _ _ hn fun a ha st hst => ?_
    split
    · rename_i b hb
      exact add_ok hst (atomHolds_rename (fun x i hx => (hsl x i hx).symm) hb (atomsOf_holds (hA k rfl) a ha))
    · exact hst

variable [Hashable ι]

omit [DecidableEq ι] in
/-- **A merge at a reassigned graph** is the merge at the graph: `mergeState`
reads the graph through no rule whose result depends on the assignment. -/
theorem mergeState_reassign [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)
    (context : List (Ty ι)) (preds : List SinglePass.State)
    (edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) (fresh : Nat) :
    SinglePass.mergeState (reassign G η) context preds edgesIn fresh = SinglePass.mergeState G context preds edgesIn fresh :=
  rfl

/-- **The walk's construction at a reassigned graph**: `Traversed` reads the
graph only through `mergeState` (`mergeState_reassign`). -/
theorem Traversed.reassign {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} (h : Traversed G w startNames given ctx edgesIn fresh) (η : MixedAssignment ι) :
    Traversed (reassign G η) w startNames given ctx edgesIn fresh :=
  { h with merge := fun t hg h2 => by rw [mergeState_reassign]; exact h.merge t hg h2 }

/-- **The walk's construction with the written facts**: there are entries
`base` (a head's entry, the single incoming state, the merge) over which
the walk is constructed (`Traversed` of the walk with entries `base`), and
each visited label's entry is its base, with the label's written facts
added at a node other than a head (`withWritten`). -/
def TraversedA (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (given : Nat → Bool)
    (ctx : Nat → List (Ty ι))
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (fresh : Nat → Nat) (stated : Nat → Option HeapKnowledge.Knowledge) : Prop :=
  ∃ base : Nat → SinglePass.State, Traversed G { w with entry := base } startNames given ctx edgesIn fresh ∧
    ∀ t, w.visited t → w.entry t = if given t then base t else withWritten (stated t) (base t)

/-- `TraversedA` at a reassigned graph (`Traversed.reassign`). -/
theorem TraversedA.reassign {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} {stated : Nat → Option HeapKnowledge.Knowledge}
    (h : TraversedA G w startNames given ctx edgesIn fresh stated) (η : MixedAssignment ι) :
    TraversedA (reassign G η) w startNames given ctx edgesIn fresh stated :=
  let ⟨base, hT, he⟩ := h
  ⟨base, hT.reassign η, he⟩

/-- **A node's entry state holds where an edge state into it, its written
assertion and, at a merge, the joined implications hold**: `entry_of_edge`
over the entries before the written facts, then `withWritten_holds` at a
node other than a head. -/
theorem entry_of_edgeA {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} {stated : Nat → Option HeapKnowledge.Knowledge} {m : Nat}
    (hT : TraversedA G w startNames given ctx edgesIn fresh stated)
    (hheads : HeadsEntered G w startNames ρ0 given m) (hnear : LinearNearFuelEq) {t : Nat} {ρ : Env}
    {s : IndexedHeap} (he : edgePre G w startNames ρ0 t ρ m s) (hA : AssertsAt stated t ρ s)
    (hJ : given t = false → 2 ≤ (w.incoming t).length →
      PromiseCalls.ImpliesOk G (joinedChecked G (ctx t) (edgesIn t)) ρ s.n s.W) :
    passPre G w startNames ρ0 t ρ m s := by
  obtain ⟨base, hTb, hent⟩ := hT
  have hp := entry_of_edge (w := { w with entry := base }) hTb (fun t' ρ' s' hg he' => by
      have := hheads t' ρ' s' hg he'
      obtain ⟨e, hein, -⟩ := he'
      rw [hent t' (hTb.visited t' (List.ne_nil_of_mem hein)), if_pos hg] at this
      exact this) hnear he hJ
  refine ⟨hp.1, ?_⟩
  rw [hent t hp.1]
  split
  · exact hp.2
  · exact withWritten_holds hp.2 hA

/-- **What an exit into a node delivers, with the target's written
assertion and, at a merge, its joined implications**: `edgePreA` and the
joined part of `edgePreJ`. -/
def edgePreAJ (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι))
    (stated : Nat → Option HeapKnowledge.Knowledge) (given : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) :
    Nat → Assertion :=
  fun t ρ m s => edgePreA G w startNames ρ0 ctx stated t ρ m s ∧
    (given t = false → 2 ≤ (w.incoming t).length →
      PromiseCalls.ImpliesOk G (joinedChecked G (ctx t) (edgesIn t)) ρ s.n s.W)

/-- **The node assertion where an exit delivers** (`edgePreAJ` ⟹
`passPreA`, by `entry_of_edgeA`). -/
theorem passPreA_of_edgeAJ {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} {stated : Nat → Option HeapKnowledge.Knowledge} {m : Nat}
    (hT : TraversedA G w startNames given ctx edgesIn fresh stated)
    (hheads : HeadsEntered G w startNames ρ0 given m) (hnear : LinearNearFuelEq) {t : Nat} {ρ : Env}
    {s : IndexedHeap} (h : edgePreAJ G w startNames ρ0 ctx stated given edgesIn t ρ m s) :
    passPreA G w startNames ρ0 ctx stated t ρ m s :=
  ⟨⟨entry_of_edgeA hT hheads hnear h.1.1.1 h.1.2 h.2, h.1.1.2⟩, h.1.2⟩

end Written

end Verification.TolerantFrames
