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
open Verification Footprints HeapObservations ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules
open GraphCode

section Walk
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- The fields a regional bound fixes: its regions' traversed fields, none
where the call states no regional bound. -/
def regionFields (regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)) :
    List (Nat × String) :=
  match regional with
  | some (_, regions, _) => ArgumentPathTracking.stableFields regions
  | none => []

omit [DecidableEq ι] [Hashable ι] in
/-- **The node assertion**: `passPreT`, the label's written assertion,
the mark bounded by the current heap, and
the fields `fields` of the entry values `ρ0` fixed from the entry heap `h₀`
in the current world. -/
def passPreU (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι))
    (stated : Nat → Option HeapKnowledge.Knowledge) (fields : List (Nat × String)) (h₀ : Heap) : Nat → Assertion :=
  fun l ρ m s => marked (passPreA G w startNames ρ0 ctx stated) l ρ m s ∧ ArgumentPathTracking.StableNow fields ρ0 h₀ s.W

omit [DecidableEq ι] [Hashable ι] in
theorem passPreU_adminClosed {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {fields : List (Nat × String)}
    {h₀ : Heap} {m : Nat} : AdminClosed (passPreU G w startNames ρ0 ctx stated fields h₀) m :=
  fun l ρ s s' ha hh ⟨⟨hp, hm⟩, hs⟩ =>
    ⟨⟨passPreA_adminClosed l ρ s s' ha hh hp, Nat.le_trans hm ha.length_le⟩, hs.transfer ha.1 ha.2⟩

omit [DecidableEq ι] [Hashable ι] in
/-- **A per-node hypothesis holds at a stronger node assertion.** -/
theorem nodesKeep_anti {P : Program} {pre pre' : Nat → Assertion} {X : Nat → Env → Heap → Prop}
    {Q : Heap → Tm → Prop} {R : Heap → Prop} {m : Nat} (hle : ∀ l ρ s, pre' l ρ m s → pre l ρ m s)
    (h : NodesKeep P pre X Q R m) : NodesKeep P pre' X Q R m :=
  fun l ρ s hp hx => h l ρ s (hle l ρ s hp) hx

omit [DecidableEq ι] [Hashable ι] in
/-- **The checked nodes at the node assertion with the traversed fields**:
every admissible transition keeps the fields fixed (`nodesChecked_stable`),
so the nodes checked at `passPreA` are checked at `passPreU`. -/
theorem nodesChecked_of_walk {P : Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {Ξres Tres : Fam} {ρ0 : Env} {m : Nat}
    (hw : NodesChecked P (marked (passPreA G w startNames ρ0 ctx stated)) Ξres Tres (fun _ => True) (fun _ => True) m)
    (fields : List (Nat × String)) (h₀ : Heap) :
    NodesChecked P (passPreU G w startNames ρ0 ctx stated fields h₀) Ξres Tres (fun _ => True) (fun _ => True) m :=
  nodesChecked_stable (S := fun s => ArgumentPathTracking.StableNow fields ρ0 h₀ s.W)
    (fun _ _ ha hs => hs.transfer ha.1 ha.2) hw

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
    (assertions : List (Nat × HeapKnowledge.Knowledge)) (bound : Option (Footprints.Closed × Bool × Bool))
    (ensures : List HeapKnowledge.IndexFact)
    (regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool))
    (w : Walk ι) (given : Nat → Bool) (ctx : Nat → List (Ty ι))
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (fresh : Nat → Nat) (stated : Nat → Option HeapKnowledge.Knowledge) : Prop where
  walk : ∀ ρ0 m, NodesChecked P (marked (passPreA G w (List.range inputs.length) ρ0 ctx stated)) (excOf G)
    (GoalHolds G goal (goal.argument ρ0)) (fun _ => True) (fun _ => True) m
  entered : ∀ ρ m (s : IndexedHeap), EnvOk G inputs ρ s.n s.W → HeapSeparation.Holds sep ρ →
    HeapKnowledge.IndexHolds idx ρ s.h → passPreA G w (List.range inputs.length) ρ ctx stated start ρ m s
  stable : ∀ Φ regions exc, regional = some (Φ, regions, exc) → ∀ ρ (s : IndexedHeap), EnvOk G inputs ρ s.n s.W →
    ArgumentPathTracking.StableNow (ArgumentPathTracking.stableFields regions) ρ s.h s.W
  footprint : ∀ Φ fr ex, bound = some (Φ, fr, ex) → ∃ dead, ∀ ρ0 h₀,
    FootprintKept P G w (List.range inputs.length) ρ0 ctx Φ h₀ dead fr ex
  returns : ensures ≠ [] → ∀ ρ0 m, ReturnsEnsured P G w (List.range inputs.length) ρ0 ctx ensures m
  regions : ∀ Φ regions exc, regional = some (Φ, regions, exc) →
    ∃ X : Env → Heap → Nat → Env → Heap → Prop, ∀ ρ0 h₀, X ρ0 h₀ start ρ0 h₀ ∧
      RegionsKeptS P G w (List.range inputs.length) ρ0 ctx (X ρ0 h₀) Φ regions h₀ exc
  labelled : ∀ l k, (l, k) ∈ assertions → w.visited l → stated l = some k

omit [DecidableEq ι] [Hashable ι] in
/-- **The start's node assertion** at an entry meeting the inputs, the
separation and the index facts. -/
theorem PassWalkSound.start {G : NormalGraph ι} {P : Program} {start : Nat} {goal : Goal ι}
    {inputs : List (Ty ι)} {sep : HeapSeparation.Separation} {idx : List HeapKnowledge.IndexAtom}
    {assertions : List (Nat × HeapKnowledge.Knowledge)} {bound : Option (Footprints.Closed × Bool × Bool)}
    {ensures : List HeapKnowledge.IndexFact}
    {regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)}
    {w : Walk ι} {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} {stated : Nat → Option HeapKnowledge.Knowledge}
    (hp : PassWalkSound G P start goal inputs sep idx assertions bound ensures regional w given ctx edgesIn fresh
      stated) {ρ : Env} {m : Nat} {s : IndexedHeap} (he : EnvOk G inputs ρ s.n s.W)
    (hs : HeapSeparation.Holds sep ρ) (hi : HeapKnowledge.IndexHolds idx ρ s.h) (hm : m ≤ s.h.length) :
    passPreU G w (List.range inputs.length) ρ ctx stated (regionFields regional) s.h start ρ m s := by
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
    {assertions : List (Nat × HeapKnowledge.Knowledge)} {bound : Option (Footprints.Closed × Bool × Bool)}
    {ensures : List HeapKnowledge.IndexFact}
    {regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)}
    (hall : ∀ η, admits η → ∃ (w : Walk ι) (given : Nat → Bool) (ctx : Nat → List (Ty ι))
      (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
      (fresh : Nat → Nat) (stated : Nat → Option HeapKnowledge.Knowledge),
      PassWalkSound (reassign G η) P start goal inputs sep idx assertions bound ensures regional w given ctx
        edgesIn fresh stated) :
    GraphGuarantee G admits P start goal inputs sep idx assertions bound ensures regional where
  safe η hη n W h ρ he := by
    obtain ⟨w, given, ctx, edgesIn, fresh, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    cases n with
    | zero => trivial
    | succ n =>
      let s : IndexedHeap := ⟨n + 1, W, h, Nat.zero_lt_succ _, ha, ho⟩
      exact graph_safe_at (nodesChecked_of_walk (hp.walk ρ 0) (regionFields regional) h) passPreU_adminClosed
        (hp.start (s := s) hv hs hi (by simp))
  bounded Φ fr ex hb E K hP η hη n W h L d he _ _ := by
    obtain ⟨w, given, ctx, edgesIn, fresh, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    obtain ⟨dead, hkeep⟩ := hp.footprint Φ fr ex hb
    subst hP
    exact keeps_postExc (nodesChecked_of_walk (hp.walk (envOf L d) h.length) (regionFields regional) h)
      passPreU_adminClosed (nodesKeep_anti (fun _ _ _ hu => hu.1.1.1) (hkeep (envOf L d) h)) (fun _ _ _ h => h)
      n W h _ _ .goto ha ho (fun hq ha' ho' => hp.start (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp))
      (.inr (Footprints.Closed.Holds.refl Φ h))
  ensured hne E K hP η hη n W h L d he := by
    obtain ⟨w, given, ctx, edgesIn, fresh, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    subst hP
    exact (keeps_postExc (nodesChecked_of_walk (hp.walk (envOf L d) 0) (regionFields regional) h)
      passPreU_adminClosed (nodesKeep_anti (fun _ _ _ hu => hu.1.1.1) (hp.returns hne (envOf L d) 0))
      (fun _ _ _ h => h) n W h _ _ .goto ha ho (fun hq ha' ho' => hp.start (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp))
      trivial).post
  regionally Φ regions exc hr E K hP η hη n W h L d he := by
    obtain ⟨w, given, ctx, edgesIn, fresh, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    obtain ⟨X, hX⟩ := hp.regions Φ regions exc hr
    subst hP
    have hf : regionFields regional = ArgumentPathTracking.stableFields regions := by simp [regionFields, hr]
    exact keeps_postExc (nodesChecked_of_walk (hp.walk (envOf L d) h.length) (regionFields regional) h)
      passPreU_adminClosed (nodesKeep_anti (fun _ _ _ hu => ⟨hu.1.1.1, hf ▸ hu.2⟩) (hX (envOf L d) h).2)
      (fun _ _ _ h => h) n W h _ _ .goto ha ho (fun hq ha' ho' => hp.start (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp))
      (hX (envOf L d) h).1
  asserted η hη n W h ρ he l k hl j h' ρ' hj hrun := by
    obtain ⟨w, given, ctx, edgesIn, fresh, stated, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    cases n with
    | zero => omega
    | succ n =>
      let s : IndexedHeap := ⟨n + 1, W, h, Nat.zero_lt_succ _, ha, ho⟩
      obtain ⟨s', he', hp'⟩ := reached_pre (nodesChecked_of_walk (hp.walk ρ 0) (regionFields regional) h)
        passPreU_adminClosed (hp.start (s := s) hv hs hi (by simp)) hrun hj
      exact he' ▸ hp'.1.1.2 k (hp.labelled l k hl hp'.1.1.1.1.1)

end Walk

end Verification.TolerantFrames
