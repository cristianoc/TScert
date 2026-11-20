import Verification.Programs.TolerantFramesNodeAsserts
import Verification.Programs.TolerantFramesRegionalRuns

/-! # Tolerant frames: the guarantee of a walk, at one node assertion

The node assertion every field of `GraphGuarantee` reads is `passPreU`: the
typed node assertion (`passPreT`), the entry mark bounded by the current
heap, the label's written assertion
(`AssertsAt`) and the regions' traversed fields fixed in the current world
(`StableNow`, over no field where the call states no regional bound). The
walk delivers it: each edge establishes the target's typed and written
assertion (`StepEdgesSoundA`), and every admissible transition keeps
`StableNow` (`nodesChecked_stable`). Each field is then `keeps_postExc`,
`graph_safe_at` or `reached_pre` at `passPreU`, with the per-node
hypotheses (`FootprintKept`, `ReturnsEnsured` at `passPreT`, `RegionsKeptS`
at `passPreS`) read at the stronger assertion (`nodesKeep_anti`).
`run_guarantee`: `PassWalkSound` at every admitted assignment ⟹
`GraphGuarantee`. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules
open GraphCode

section Walk
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- The fields a regional bound fixes: its regions' traversed fields, none
where the call states no regional bound. -/
def regionFields (regional : Option (Footprints.Closed × List Footprints.ArgumentSpineRegion × Bool)) :
    List (Nat × String) :=
  match regional with
  | some (_, regions, _) => ArgumentPathTracking.stableFields regions
  | none => []

omit [DecidableEq ι] [Hashable ι] in
/-- **The node assertion**: `passPreT`, the label's written assertion,
the mark bounded by the current heap, and
the fields `fields` of the entry values `ε.env` fixed from the entry heap `h₀`
in the current world. -/
def passPreU (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ε : HeapKnowledge.EntryState) (ctx : Nat → List (Ty ι))
    (stated : Nat → Option HeapKnowledge.Knowledge) (fields : List (Nat × String)) (h₀ : Heap) : Nat → Assertion :=
  fun l ρ m s => marked (passPreA G w startNames ε ctx stated) l ρ m s ∧ ArgumentPathTracking.StableNow fields ε.env h₀ s.W

omit [DecidableEq ι] [Hashable ι] in
theorem passPreU_adminClosed {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} 
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {fields : List (Nat × String)}
    {h₀ : Heap} {m : Nat} : AdminClosed (passPreU G w startNames ε ctx stated fields h₀) m :=
  fun l ρ s s' ha hh ⟨⟨hp, hm⟩, hs⟩ =>
    ⟨⟨passPreA_adminClosed l ρ s s' ha hh hp, Nat.le_trans hm ha.length_le⟩, hs.transfer ha.1 ha.2⟩

omit [DecidableEq ι] [Hashable ι] in
/-- **A per-node hypothesis holds at a stronger node assertion.** -/
theorem nodesKeep_anti {P : Program} {pre pre' : Nat → Assertion} {X : Nat → Env → Heap → Prop}
    {Q : Heap → Tm → Prop} {R : Heap → Prop} {m : Nat} (hle : ∀ l ρ s, pre' l ρ m s → pre l ρ m s)
    (h : NodesKeep P pre X Q R m) : NodesKeep P pre' X Q R m :=
  fun l ρ s hp hx => h l ρ s (hle l ρ s hp) hx

omit [DecidableEq ι] [Hashable ι] in
/-- **A per-node hypothesis at framed returns holds at a stronger node
assertion.** -/
theorem nodesKeepR_anti {P : Program} {pre pre' : Nat → Assertion} {F : Nat → Bool}
    {Ret RetE : Nat → Env → Heap → Heap → Prop} {X : Nat → Env → Heap → Prop}
    {Q : Heap → Tm → Prop} {R : Heap → Prop} {m : Nat} (hle : ∀ l ρ s, pre' l ρ m s → pre l ρ m s)
    (h : NodesKeepR P pre F Ret RetE X Q R m) : NodesKeepR P pre' F Ret RetE X Q R m :=
  fun l ρ s hp hx => h l ρ s (hle l ρ s hp) hx

omit [DecidableEq ι] [Hashable ι] in
/-- **The checked nodes at the node assertion with the traversed fields, at
framed returns**: every admissible transition keeps the fields fixed
(`nodesCheckedR_stable`), so the nodes checked at `passPreA` are checked at
`passPreU`. -/
theorem nodesChecked_of_walkR {P : Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {Ξres Tres : Fam} {m : Nat}
    {F : Nat → Bool} {Ret RetE : Nat → Env → Heap → Heap → Prop}
    (hw : NodesCheckedR P (marked (passPreA G w startNames ε ctx stated)) F Ret RetE Ξres Tres (fun _ => True)
      (fun _ => True) m)
    (fields : List (Nat × String)) (h₀ : Heap) :
    NodesCheckedR P (passPreU G w startNames ε ctx stated fields h₀) F Ret RetE Ξres Tres (fun _ => True)
      (fun _ => True) m :=
  nodesCheckedR_stable (S := fun s => ArgumentPathTracking.StableNow fields ε.env h₀ s.W)
    (fun _ _ ha hs => hs.transfer ha.1 ha.2) hw

omit [DecidableEq ι] [Hashable ι] in
/-- **The checked nodes at the node assertion with the traversed fields**
(`nodesChecked_of_walkR` with no framed node). -/
theorem nodesChecked_of_walk {P : Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {Ξres Tres : Fam} {m : Nat}
    (hw : NodesChecked P (marked (passPreA G w startNames ε ctx stated)) Ξres Tres (fun _ => True) (fun _ => True) m)
    (fields : List (Nat × String)) (h₀ : Heap) :
    NodesChecked P (passPreU G w startNames ε ctx stated fields h₀) Ξres Tres (fun _ => True) (fun _ => True) m :=
  (nodesChecked_of_walkR (Ret := fun _ _ _ _ => True) (RetE := fun _ _ _ _ => True) hw.toR fields h₀).toPlain

/-- **What the pass's walk at one assignment provides**: every node
checked at the node assertion stating the written assertions, at every
entry value and mark bounded by the heap; the start's typed and written
assertion at every entry meeting the inputs, the separation and the index
facts (`entered`); the regions' traversed fields fixed at such an entry
(`stable`); the per-node hypotheses of each stated option; and each
assertion of the request the written assertion at its label
(`labelled`). -/
structure PassWalkSound (G : NormalGraph ι) (P : Program) (start : Nat) (goal : Goal ι) (inputs : List (Ty ι))
    (sep : HeapSeparation.Separation) (idx : List HeapKnowledge.IndexAtom)
    (assertions : List (Nat × HeapKnowledge.Knowledge)) (bound : Option RunBound)
    («ensures» : List HeapKnowledge.IndexFact)
    (regional : Option (Footprints.Closed × List Footprints.ArgumentSpineRegion × Bool))
    (w : Walk ι) («given» : Nat → Bool) (ctx : Nat → List (Ty ι))
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (fresh : Nat → Nat) (stated : Nat → Option HeapKnowledge.Knowledge) : Prop where
  walk : ∀ ε m, NodesChecked P (marked (passPreA G w (List.range inputs.length) ε ctx stated)) (excOf G)
    (GoalHolds G goal (goal.argument ε.env)) (fun _ => True) (fun _ => True) m
  entered : ∀ ρ m (s : IndexedHeap), EnvOk G inputs ρ s.n s.W → HeapSeparation.Holds sep ρ →
    HeapKnowledge.IndexHolds ⟨ρ, s.h⟩ idx ρ s.h → passPreA G w (List.range inputs.length) ⟨ρ, s.h⟩ ctx stated start ρ m s
  stable : ∀ Φ regions exc, regional = some (Φ, regions, exc) → ∀ ρ (s : IndexedHeap), EnvOk G inputs ρ s.n s.W →
    ArgumentPathTracking.StableNow (ArgumentPathTracking.stableFields regions) ρ s.h s.W
  footprint : ∀ Φ Ψ fr, bound = some (⟨Φ, Ψ⟩, fr) → ∃ dead, ∀ ε h₀,
    FootprintKept P G w (List.range inputs.length) ε ctx Φ Ψ h₀ dead fr
  returns : «ensures» ≠ [] → ∀ ε m, ReturnsEnsured P G w (List.range inputs.length) ε ctx «ensures» m
  regions : ∀ Φ regions exc, regional = some (Φ, regions, exc) →
    ∃ X : HeapKnowledge.EntryState → Heap → Nat → Env → Heap → Prop, ∀ ε h₀, X ε h₀ start ε.env h₀ ∧
      RegionsKeptS P G w (List.range inputs.length) ε ctx (X ε h₀) Φ regions h₀ exc
  labelled : ∀ l k, (l, k) ∈ assertions → w.visited l → stated l = some k

omit [DecidableEq ι] [Hashable ι] in
/-- **The start's node assertion** at an entry meeting the inputs, the
separation and the index facts. -/
theorem PassWalkSound.start {G : NormalGraph ι} {P : Program} {start : Nat} {goal : Goal ι}
    {inputs : List (Ty ι)} {sep : HeapSeparation.Separation} {idx : List HeapKnowledge.IndexAtom}
    {assertions : List (Nat × HeapKnowledge.Knowledge)} {bound : Option RunBound}
    {ensures : List HeapKnowledge.IndexFact}
    {regional : Option (Footprints.Closed × List Footprints.ArgumentSpineRegion × Bool)}
    {w : Walk ι} {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} {stated : Nat → Option HeapKnowledge.Knowledge}
    (hp : PassWalkSound G P start goal inputs sep idx assertions bound ensures regional w given ctx edgesIn fresh
      stated) {ρ : Env} {m : Nat} {s : IndexedHeap} (he : EnvOk G inputs ρ s.n s.W)
    (hs : HeapSeparation.Holds sep ρ) (hi : HeapKnowledge.IndexHolds ⟨ρ, s.h⟩ idx ρ s.h) (hm : m ≤ s.h.length) :
    passPreU G w (List.range inputs.length) ⟨ρ, s.h⟩ ctx stated (regionFields regional) s.h start ρ m s := by
  refine ⟨⟨hp.entered ρ m s he hs hi, hm⟩, ?_⟩
  cases hr : regional with
  | none => intro p hp'; simp [regionFields] at hp'
  | some r =>
    obtain ⟨Φ, regions, exc⟩ := r
    simpa [regionFields] using hp.stable Φ regions exc hr ρ s he

omit [DecidableEq ι] [Hashable ι] in
/-- **An accepted run's guarantee from its walk**: where the pass's walk
provides `PassWalkSound` at every admitted assignment, the run guarantees
every field of `GraphGuarantee`, each read at the node assertion
`passPreU`. -/
theorem run_guarantee {G : NormalGraph ι} {admits : MixedAssignment ι → Prop} {P : Program} {start : Nat}
    {goal : Goal ι} {inputs : List (Ty ι)} {sep : HeapSeparation.Separation} {idx : List HeapKnowledge.IndexAtom}
    {assertions : List (Nat × HeapKnowledge.Knowledge)} {bound : Option RunBound}
    {ensures : List HeapKnowledge.IndexFact}
    {regional : Option (Footprints.Closed × List Footprints.ArgumentSpineRegion × Bool)}
    (hall : ∀ η, admits η → ∃ (w : Walk ι) (given : Nat → Bool) (ctx : Nat → List (Ty ι))
      (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
      (fresh : Nat → Nat) (stated : Nat → Option HeapKnowledge.Knowledge),
      PassWalkSound (reassign G η) P start goal inputs sep idx assertions bound ensures regional w given ctx
        edgesIn fresh stated) :
    GraphGuarantee G admits P start goal inputs sep idx assertions bound ensures regional where
  safe η hη n W h ρ he hPn hρ := by
    obtain ⟨w, given, ctx, edgesIn, fresh, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    cases n with
    | zero => exact hρ
    | succ n =>
      let s : IndexedHeap := ⟨n + 1, W, h, Nat.zero_lt_succ _, ha, ho⟩
      exact graph_safe_at (nodesChecked_of_walk (hp.walk ⟨ρ, h⟩ 0) (regionFields regional) h) passPreU_adminClosed
        (hp.start (s := s) hv hs hi (by simp)) hPn hρ
  bounded Φ Ψ fr hb E K hP η hη n W h L d _ he hgo _ _ := by
    obtain ⟨w, given, ctx, edgesIn, fresh, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    obtain ⟨dead, hkeep⟩ := hp.footprint Φ Ψ fr hb
    subst hP
    exact keeps_postExc (nodesChecked_of_walk (hp.walk ⟨envOf L d, h⟩ h.length) (regionFields regional) h)
      passPreU_adminClosed (nodesKeep_anti (fun _ _ _ hu => hu.1.1.1) (hkeep ⟨envOf L d, h⟩ h)) (fun _ _ _ h => h)
      n W h _ _ .goto ha ho (GraphCode.goto_refs hgo).1 (GraphCode.goto_refs hgo).2
      (fun hq ha' ho' => hp.start (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp))
      (.inr (Footprints.Closed.Holds.refl Φ h))
  ensured hne E K hP η hη n W h L d _ he hgo := by
    obtain ⟨w, given, ctx, edgesIn, fresh, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    subst hP
    exact (keeps_postExc (nodesChecked_of_walk (hp.walk ⟨envOf L d, h⟩ 0) (regionFields regional) h)
      passPreU_adminClosed (nodesKeep_anti (fun _ _ _ hu => hu.1.1.1) (hp.returns hne ⟨envOf L d, h⟩ 0))
      (fun _ _ _ h => h) n W h _ _ .goto ha ho (GraphCode.goto_refs hgo).1 (GraphCode.goto_refs hgo).2
      (fun hq ha' ho' => hp.start (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp))
      trivial).post
  regionally Φ regions exc hr E K hP η hη n W h L d _ he hgo := by
    obtain ⟨w, given, ctx, edgesIn, fresh, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    obtain ⟨X, hX⟩ := hp.regions Φ regions exc hr
    subst hP
    have hf : regionFields regional = ArgumentPathTracking.stableFields regions := by simp [regionFields, hr]
    exact keeps_postExc (nodesChecked_of_walk (hp.walk ⟨envOf L d, h⟩ h.length) (regionFields regional) h)
      passPreU_adminClosed (nodesKeep_anti (fun _ _ _ hu => ⟨hu.1.1.1, hf ▸ hu.2⟩) (hX ⟨envOf L d, h⟩ h).2)
      (fun _ _ _ h => h) n W h _ _ .goto ha ho (GraphCode.goto_refs hgo).1 (GraphCode.goto_refs hgo).2
      (fun hq ha' ho' => hp.start (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp))
      (hX ⟨envOf L d, h⟩ h).1
  asserted η hη n W h ρ he hPn hρ l k hl j h' ρ' hj hrun := by
    obtain ⟨w, given, ctx, edgesIn, fresh, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    cases n with
    | zero => omega
    | succ n =>
      let s : IndexedHeap := ⟨n + 1, W, h, Nat.zero_lt_succ _, ha, ho⟩
      obtain ⟨s', he', hp'⟩ := reached_pre (nodesChecked_of_walk (hp.walk ⟨ρ, h⟩ 0) (regionFields regional) h)
        passPreU_adminClosed (hp.start (s := s) hv hs hi (by simp)) hPn hρ hrun hj
      exact he' ▸ hp'.1.1.2 k (hp.labelled l k hl hp'.1.1.1.1.1)

omit [DecidableEq ι] [Hashable ι] in
/-- Nodes checked are checked at framed returns at every framed set: an
exit's target required everywhere is required where the exit meets its
returns. -/
theorem NodesChecked.toRF {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop}
    {m : Nat} (F : Nat → Bool) (Ret RetE : Nat → Env → Heap → Heap → Prop)
    (hn : NodesChecked P pre Ξres Tres Qres Rres m) : NodesCheckedR P pre F Ret RetE Ξres Tres Qres Rres m := by
  intro l ρ s hp
  obtain ⟨node, hP, hck⟩ := hn l ρ s hp
  refine ⟨node, hP, fun hr hρ => ?_⟩
  obtain ⟨Ξ, T, cn, ce, Qn, Qe, hs, ho⟩ := hck hr hρ
  exact ⟨Ξ, T, cn, ce, Qn, Qe, hs, ho.toR _ _⟩

omit [DecidableEq ι] [Hashable ι] in
/-- Nodes keeping a run property keep it at framed returns at every framed
set. -/
theorem NodesKeep.toRF {P : Program} {pre : Nat → Assertion} {X : Nat → Env → Heap → Prop}
    {Q : Heap → Tm → Prop} {R : Heap → Prop} {m : Nat} (F : Nat → Bool) (Ret RetE : Nat → Env → Heap → Heap → Prop)
    (hk : NodesKeep P pre X Q R m) : NodesKeepR P pre F Ret RetE X Q R m :=
  fun l ρ s hp hx => by
    obtain ⟨node, hP, hk⟩ := hk l ρ s hp hx
    exact ⟨node, hP, fun hr hρ j h' t' hs hj =>
      ⟨fun hv _ => (hk hr hρ j h' t' hs hj).1 hv, fun e he _ => (hk hr hρ j h' t' hs hj).2 e he⟩⟩

/-- **What a walk at framed returns provides** (`PassWalkSound` at framed
returns): every node checked at framed returns (`NodesCheckedR`) at the
node assertion stating the written assertions, the per-node hypotheses
of each stated option kept at framed returns (`NodesKeepR`), and the
start's assertion, the traversed fields and the labelled assertions as
`PassWalkSound` states them. -/
structure PassWalkSoundR (G : NormalGraph ι) (P : Program) (start : Nat) (goal : Goal ι) (inputs : List (Ty ι))
    (sep : HeapSeparation.Separation) (idx : List HeapKnowledge.IndexAtom)
    (assertions : List (Nat × HeapKnowledge.Knowledge)) (bound : Option RunBound)
    («ensures» : List HeapKnowledge.IndexFact)
    (regional : Option (Footprints.Closed × List Footprints.ArgumentSpineRegion × Bool))
    (F : Nat → Bool) (Ret RetE : Nat → Env → Heap → Heap → Prop)
    (w : Walk ι) (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge) : Prop where
  walk : ∀ ε m, NodesCheckedR P (marked (passPreA G w (List.range inputs.length) ε ctx stated)) F Ret RetE
    (excOf G) (GoalHolds G goal (goal.argument ε.env)) (fun _ => True) (fun _ => True) m
  entered : ∀ ρ m (s : IndexedHeap), EnvOk G inputs ρ s.n s.W → HeapSeparation.Holds sep ρ →
    HeapKnowledge.IndexHolds ⟨ρ, s.h⟩ idx ρ s.h → passPreA G w (List.range inputs.length) ⟨ρ, s.h⟩ ctx stated start ρ m s
  stable : ∀ Φ regions exc, regional = some (Φ, regions, exc) → ∀ ρ (s : IndexedHeap), EnvOk G inputs ρ s.n s.W →
    ArgumentPathTracking.StableNow (ArgumentPathTracking.stableFields regions) ρ s.h s.W
  footprint : ∀ Φ Ψ fr, bound = some (⟨Φ, Ψ⟩, fr) → ∃ dead, ∀ ε h₀,
    NodesKeepR P (passPreT G w (List.range inputs.length) ε ctx) F Ret RetE (BoundX Φ h₀ dead) (BoundQ Φ h₀ fr)
      (BoundR Ψ h₀) h₀.length
  returns : «ensures» ≠ [] → ∀ ε m, NodesKeepR P (passPreT G w (List.range inputs.length) ε ctx) F Ret RetE
    (fun _ _ _ => True) (EnsuresQ «ensures» ε) (fun _ => True) m
  regions : ∀ Φ regions exc, regional = some (Φ, regions, exc) →
    ∃ X : HeapKnowledge.EntryState → Heap → Nat → Env → Heap → Prop, ∀ ε h₀, X ε h₀ start ε.env h₀ ∧
      NodesKeepR P (passPreS G w (List.range inputs.length) ε ctx regions h₀) F Ret RetE (X ε h₀)
        (RegionQ Φ regions ε h₀) (RegionR Φ regions ε h₀ exc) h₀.length
  labelled : ∀ l k, (l, k) ∈ assertions → w.visited l → stated l = some k

omit [DecidableEq ι] [Hashable ι] in
/-- **A walk's provisions hold at framed returns at every framed set.** -/
theorem PassWalkSound.toR {G : NormalGraph ι} {P : Program} {start : Nat} {goal : Goal ι}
    {inputs : List (Ty ι)} {sep : HeapSeparation.Separation} {idx : List HeapKnowledge.IndexAtom}
    {assertions : List (Nat × HeapKnowledge.Knowledge)} {bound : Option RunBound}
    {ensures : List HeapKnowledge.IndexFact}
    {regional : Option (Footprints.Closed × List Footprints.ArgumentSpineRegion × Bool)}
    {w : Walk ι} {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} {stated : Nat → Option HeapKnowledge.Knowledge}
    (hp : PassWalkSound G P start goal inputs sep idx assertions bound ensures regional w given ctx edgesIn fresh
      stated) (F : Nat → Bool) (Ret RetE : Nat → Env → Heap → Heap → Prop) :
    PassWalkSoundR G P start goal inputs sep idx assertions bound ensures regional F Ret RetE w ctx stated where
  walk ε m := (hp.walk ε m).toRF F Ret RetE
  entered := hp.entered
  stable := hp.stable
  footprint Φ Ψ fr hb := by
    obtain ⟨dead, hk⟩ := hp.footprint Φ Ψ fr hb
    exact ⟨dead, fun ε h₀ => (hk ε h₀).toRF F Ret RetE⟩
  returns hne ε m := (hp.returns hne ε m).toRF F Ret RetE
  regions Φ regions exc hr := by
    obtain ⟨X, hX⟩ := hp.regions Φ regions exc hr
    exact ⟨X, fun ε h₀ => ⟨(hX ε h₀).1, (hX ε h₀).2.toRF F Ret RetE⟩⟩
  labelled := hp.labelled

omit [DecidableEq ι] [Hashable ι] in
/-- **The start's node assertion** of a walk at framed returns. -/
theorem PassWalkSoundR.start {G : NormalGraph ι} {P : Program} {start : Nat} {goal : Goal ι}
    {inputs : List (Ty ι)} {sep : HeapSeparation.Separation} {idx : List HeapKnowledge.IndexAtom}
    {assertions : List (Nat × HeapKnowledge.Knowledge)} {bound : Option RunBound}
    {ensures : List HeapKnowledge.IndexFact}
    {regional : Option (Footprints.Closed × List Footprints.ArgumentSpineRegion × Bool)}
    {F : Nat → Bool} {Ret RetE : Nat → Env → Heap → Heap → Prop}
    {w : Walk ι} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    (hp : PassWalkSoundR G P start goal inputs sep idx assertions bound ensures regional F Ret RetE w ctx stated)
    {ρ : Env} {m : Nat} {s : IndexedHeap} (he : EnvOk G inputs ρ s.n s.W)
    (hs : HeapSeparation.Holds sep ρ) (hi : HeapKnowledge.IndexHolds ⟨ρ, s.h⟩ idx ρ s.h) (hm : m ≤ s.h.length) :
    passPreU G w (List.range inputs.length) ⟨ρ, s.h⟩ ctx stated (regionFields regional) s.h start ρ m s := by
  refine ⟨⟨hp.entered ρ m s he hs hi, hm⟩, ?_⟩
  cases hr : regional with
  | none => intro p hp'; simp [regionFields] at hp'
  | some r =>
    obtain ⟨Φ, regions, exc⟩ := r
    simpa [regionFields] using hp.stable Φ regions exc hr ρ s he

omit [DecidableEq ι] [Hashable ι] in
/-- The written assertion of each stated label at every graph-code term
running `E K` at it, read from the entry environment `ρ` and heap `h`. -/
def GotoAsserted (E : List Tm) (K : List (Continuation × Option Target))
    (assertions : List (Nat × HeapKnowledge.Knowledge)) (ρ : Env) (h : Heap) (h' : Heap) (t' : Tm) : Prop :=
  ∀ l k, (l, k) ∈ assertions → ∀ (L' : List Tm) (d' : Tm) (c' : ComponentTag),
    t' = .goto E K l L' d' c' → HeapKnowledge.Holds k ⟨ρ, h⟩ (envOf L' d') h'

/-- **What an accepted run guarantees at framed returns** (`GraphGuarantee`
at framed returns, each clause of the term that runs the graph code):
at every assignment `admits` lets through, from every entry meeting the
inputs, the term running any node lists whose graph is `P` is safe at
framed returns (`SafeRet` at the framed nodes `F` and the returns `Ret`,
`RetE`, nothing pending); within a footprint where `bound` names one; the
stated postcondition where `ensures` is not empty; within the regional
bound where `regional` names one; and each stated assertion at every state
reached at a `goto` of its label (`GotoAsserted`). -/
structure GraphGuaranteeR (G : NormalGraph ι) (admits : MixedAssignment ι → Prop) (P : Program)
    (start : Nat) (goal : Goal ι) (inputs : List (Ty ι)) (sep : HeapSeparation.Separation)
    (idx : List HeapKnowledge.IndexAtom) (assertions : List (Nat × HeapKnowledge.Knowledge))
    (bound : Option RunBound) («ensures» : List HeapKnowledge.IndexFact)
    (regional : Option (Footprints.Closed × List Footprints.ArgumentSpineRegion × Bool))
    (F : Nat → Bool) (Ret RetE : Nat → Env → Heap → Heap → Prop) : Prop where
  safe : ∀ E K, GraphCode.program E K = P → ∀ η, admits η → ∀ n W h L d comp,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h → RefsOk W (.goto E K start L d comp) →
    SafeRet (fun _ _ => True) (excOf (reassign G η)) (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun _ _ _ _ => True) (fun _ _ _ => True) F Ret RetE n W none h (.goto E K start L d comp)
  bounded : ∀ Φ Ψ fresh, bound = some (⟨Φ, Ψ⟩, fresh) → ∀ E K, GraphCode.program E K = P →
    ∀ η, admits η → ∀ n W h L d comp,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h → RefsOk W (.goto E K start L d comp) →
    (∀ v ∈ L, isVal v = true) → isVal d = true →
    SafeRet (fun _ _ => True) (excOf (reassign G η)) (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (WPost.lift fun h' v => Φ.Holds h h' ∧ (fresh = true → Footprints.FreshAt h.length v))
      (WExc.lift fun h' => Ψ ≠ .top → Ψ.Holds h h') F Ret RetE n W none h (.goto E K start L d comp)
  ensured : «ensures» ≠ [] → ∀ E K, GraphCode.program E K = P → ∀ η, admits η → ∀ n W h L d comp,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h → RefsOk W (.goto E K start L d comp) →
    SafeRet (fun _ _ => True) (excOf (reassign G η)) (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (WPost.lift fun h' v => GraphCode.EnsuresAt «ensures» ⟨envOf L d, h⟩ h' (push v (envOf L d)))
      (fun _ _ _ => True) F Ret RetE n W none h (.goto E K start L d comp)
  regionally : ∀ Φ regions exc, regional = some (Φ, regions, exc) → ∀ E K, GraphCode.program E K = P →
    ∀ η, admits η → ∀ n W h L d comp,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h → RefsOk W (.goto E K start L d comp) →
    SafeRet (fun _ _ => True) (excOf (reassign G η)) (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (WPost.lift fun h' _ => Footprints.ArgumentSpineRegionsWithin Φ regions (envOf L d) h h')
      (WExc.lift fun h' => exc = true → Footprints.ArgumentSpineRegionsWithin Φ regions (envOf L d) h h')
      F Ret RetE n W none h (.goto E K start L d comp)
  asserted : ∀ E K, GraphCode.program E K = P → ∀ η, admits η → ∀ n W h L d comp,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h → RefsOk W (.goto E K start L d comp) →
    SafeRet (GotoAsserted E K assertions (envOf L d) h) (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun _ _ _ _ => True) (fun _ _ _ => True) F Ret RetE n W none h (.goto E K start L d comp)

omit [DecidableEq ι] [Hashable ι] in
/-- **An accepted run's guarantee at framed returns from its walk**
(`run_guarantee` at framed returns): where the walk provides
`PassWalkSoundR` at every admitted assignment, each clause of
`GraphGuaranteeR` holds: safety by `graph_safe_atR` read on the term
(`safeRet_of_sim`), the footprint, the postcondition and the regional
bound by `keeps_postExcR` over the per-node hypotheses, and the
assertions by `keeps_postExcR` with the state property `GotoAsserted`,
which the node assertion `passPreU` gives at every `goto` (its written
assertion, the label's stated one). -/
theorem run_guaranteeR {G : NormalGraph ι} {admits : MixedAssignment ι → Prop} {P : Program} {start : Nat}
    {goal : Goal ι} {inputs : List (Ty ι)} {sep : HeapSeparation.Separation} {idx : List HeapKnowledge.IndexAtom}
    {assertions : List (Nat × HeapKnowledge.Knowledge)} {bound : Option RunBound}
    {ensures : List HeapKnowledge.IndexFact}
    {regional : Option (Footprints.Closed × List Footprints.ArgumentSpineRegion × Bool)}
    {F : Nat → Bool} {Ret RetE : Nat → Env → Heap → Heap → Prop}
    (hall : ∀ η, admits η → ∃ (w : Walk ι) (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge),
      PassWalkSoundR (reassign G η) P start goal inputs sep idx assertions bound ensures regional F Ret RetE w ctx
        stated) :
    GraphGuaranteeR G admits P start goal inputs sep idx assertions bound ensures regional F Ret RetE where
  safe E K hP η hη n W h L d _ he hgo := by
    obtain ⟨w, ctx, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    subst hP
    cases n with
    | zero => exact hgo
    | succ n =>
      let s : IndexedHeap := ⟨n + 1, W, h, Nat.zero_lt_succ _, ha, ho⟩
      exact safeRet_of_sim (n + 1) W none h .goto (GraphCode.goto_refs hgo).1
        (graph_safe_atR (nodesChecked_of_walkR (hp.walk ⟨envOf L d, h⟩ 0) (regionFields regional) h)
          passPreU_adminClosed (hp.start (s := s) hv hs hi (by simp)) (GraphCode.program_refs (GraphCode.goto_refs hgo).1)
          (GraphCode.goto_refs hgo).2 none)
  bounded Φ Ψ fr hb E K hP η hη n W h L d _ he hgo _ _ := by
    obtain ⟨w, ctx, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    obtain ⟨dead, hkeep⟩ := hp.footprint Φ Ψ fr hb
    subst hP
    exact keeps_postExcR (J := fun _ _ => True)
      (nodesChecked_of_walkR (hp.walk ⟨envOf L d, h⟩ h.length) (regionFields regional) h)
      passPreU_adminClosed (nodesKeepR_anti (fun _ _ _ hu => hu.1.1.1) (hkeep ⟨envOf L d, h⟩ h)) (fun _ _ _ h => h)
      (fun _ _ _ _ _ _ => trivial) n W none h _ _ .goto ha ho (GraphCode.goto_refs hgo).1 (GraphCode.goto_refs hgo).2
      (fun hq ha' ho' => hp.start (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp))
      (.inr (Footprints.Closed.Holds.refl Φ h))
  ensured hne E K hP η hη n W h L d _ he hgo := by
    obtain ⟨w, ctx, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    subst hP
    exact keeps_postExcR (J := fun _ _ => True)
      (nodesChecked_of_walkR (hp.walk ⟨envOf L d, h⟩ 0) (regionFields regional) h)
      passPreU_adminClosed (nodesKeepR_anti (fun _ _ _ hu => hu.1.1.1) (hp.returns hne ⟨envOf L d, h⟩ 0))
      (fun _ _ _ h => h) (fun _ _ _ _ _ _ => trivial) n W none h _ _ .goto ha ho (GraphCode.goto_refs hgo).1
      (GraphCode.goto_refs hgo).2
      (fun hq ha' ho' => hp.start (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp)) trivial
  regionally Φ regions exc hr E K hP η hη n W h L d _ he hgo := by
    obtain ⟨w, ctx, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    obtain ⟨X, hX⟩ := hp.regions Φ regions exc hr
    subst hP
    have hf : regionFields regional = ArgumentPathTracking.stableFields regions := by simp [regionFields, hr]
    exact keeps_postExcR (J := fun _ _ => True)
      (nodesChecked_of_walkR (hp.walk ⟨envOf L d, h⟩ h.length) (regionFields regional) h)
      passPreU_adminClosed (nodesKeepR_anti (fun _ _ _ hu => ⟨hu.1.1.1, hf ▸ hu.2⟩) (hX ⟨envOf L d, h⟩ h).2)
      (fun _ _ _ h => h) (fun _ _ _ _ _ _ => trivial) n W none h _ _ .goto ha ho (GraphCode.goto_refs hgo).1
      (GraphCode.goto_refs hgo).2
      (fun hq ha' ho' => hp.start (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp))
      (hX ⟨envOf L d, h⟩ h).1
  asserted E K hP η hη n W h L d _ he hgo := by
    obtain ⟨w, ctx, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    subst hP
    have hn := nodesChecked_of_walkR (hp.walk ⟨envOf L d, h⟩ 0) (regionFields regional) h
    refine keeps_postExcR hn passPreU_adminClosed hn.keepsTrue (fun _ _ _ h => h) ?_ n W none h _ _ .goto ha ho
      (GraphCode.goto_refs hgo).1 (GraphCode.goto_refs hgo).2
      (fun hq ha' ho' => hp.start (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp)) trivial
    intro s p ts st sim hinv l k hl L' d' c' hts
    subst hts
    cases sim with
    | goto =>
      have hp' := hinv s.pos s.adm s.ok
      exact hp'.1.1.2 k (hp.labelled l k hl hp'.1.1.1.1.1)
    | done hv => simp [isVal] at hv

end Walk

end Verification.TolerantFrames
