import Verification.Programs.TolerantFramesDriverRecords
import Verification.Programs.TolerantFramesExitVacuity

/-! # Tolerant frames: the setup starts the walk's invariant

`SinglePass.setup` checks the call, then returns what every visit reads
(`setupEnv`) and the state the first visit starts from (`setupState`).
Proved (`setup_ok`): a setup that returns gives the claims one per node,
the entry accepted, and the environment and state of `setupEnv` and
`setupState` at the loop heads' marks, the written assertions by label, the
heads' given states (`setupGiven`), the in-degrees (`inDegrees`) and the
queue (`initialQueue`). -/
namespace Verification.TolerantFrames
open Verification ControlFlow PositiveGraphs PositiveCertificates LabelStore ProgramTyping CertificateProducer

section Setup
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- **What a returned setup gives** (an unfolding of `SinglePass.setup`). -/
structure SetupOk (c : Target.RunCall G I) (env : SinglePass.WalkEnv ι G I) (σ0 : SinglePass.WalkState ι G) :
    Prop where
  claimed : c.claims.toArray.size = c.P.toArray.size
  entry : SinglePass.entryRefusal G c.inputs c.claims c.start c.goal
    ((byLabel c.P.toArray.size c.assertions).getD c.start none)
    (((byLabel c.P.toArray.size (SinglePass.withStartOld G c.inputs c.entryIndices c.entrySeparation c.start c.ensures c.candidates)).getD c.start none).getD [])
    ((c.givenImplies[c.start]?).getD []) ((c.givenArgs[c.start]?).getD []) ((c.givenInputs[c.start]?).getD [])
    c.entryIndices c.entrySeparation = none
  nodes : env.nodes = c.P.toArray
  claims : env.claimed = c.claims.toArray
  n : env.n = c.P.toArray.size
  start : env.start = c.start
  isHead : env.isHead = if c.start < c.P.toArray.size then
    (SinglePass.loopHeads c.P.toArray c.start).1.set! c.start true else (SinglePass.loopHeads c.P.toArray c.start).1
  reached : env.reached = (SinglePass.loopHeads c.P.toArray c.start).2
  stated : env.stated = byLabel c.P.toArray.size c.assertions
  given : ∃ counts, env.given = (SinglePass.setupGiven c.P.toArray.size c.start env.isHead env.stated
    (byLabel c.P.toArray.size (SinglePass.withStartOld G c.inputs c.entryIndices c.entrySeparation c.start c.ensures c.candidates)) c.entryIndices c.entrySeparation counts).1
  codes : env.codes = c.codes
  checker : env.passChecker = c.passChecker
  bound : env.bound = c.bound
  goal : env.goal = c.goal
  ensures : env.ensures = c.ensures
  givenImplies : env.givenImplies = c.givenImplies
  givenArgs : env.givenArgs = c.givenArgs
  givenInputs : env.givenInputs = c.givenInputs
  startNames : env.startNames = List.range (((c.claims.toArray[c.start]?).map (·.context.length)).getD 0)
  argName : env.argName = c.goal.slot.bind (env.startNames[·]?)
  state : ∃ counts trace, σ0 = SinglePass.setupState c.P.toArray.size c.answers counts trace
    (SinglePass.inDegrees c.P.toArray env.reached env.isHead)
    (SinglePass.initialQueue c.P.toArray.size env.reached (SinglePass.inDegrees c.P.toArray env.reached env.isHead)
      env.isHead c.start)
    (((c.claims.toArray[c.start]?).map (·.context.length)).getD 0)
  merging : env.merging = passMerging c

  regional : env.regional = c.regional
  startKept : SinglePass.startSeparationKept (passStated c c.start) c.entrySeparation = true

theorem setup_ok {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I} {σ0 : SinglePass.WalkState ι G}
    (h : RunCall.setup c = .ok (env, σ0)) : SetupOk c env σ0 := by
  unfold RunCall.setup SinglePass.setup at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | (cases h; done) | skip
  all_goals
    cases h
    have hl := ‹SinglePass.loopHeadsRun _ _ = _›
    rw [SinglePass.loopHeadsRun] at hl
    obtain ⟨-, hl⟩ := Prod.mk.inj hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hl
    have hg := ‹SinglePass.setupGiven _ _ _ _ _ _ _ _ = _›
    have hcl : ¬(c.claims.toArray.size != c.P.toArray.size) = true := by assumption
    refine ⟨by simpa using hcl, by assumption, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ⟨_, (congrArg Prod.fst hg).symm⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨_, _, rfl⟩, ?_, rfl, ?_⟩
    case refine_3 =>
      have hk := entryRefusal_startKept
        (‹SinglePass.entryRefusal G _ _ _ _ _ _ _ _ _ _ _ = none›)
      simpa only [passStated, Array.getD_eq_getD_getElem?] using hk
    all_goals
      dsimp only [SinglePass.setupEnv, passMerging, passDegrees, passIsHead]
      split <;> rename_i hs <;>
        first | rfl | exact absurd (‹c.start < _› : c.start < c.P.toArray.size) hs |
          exact absurd hs (‹¬c.start < _› : ¬c.start < c.P.toArray.size)

/-- A regional setup excludes every edge into the start. -/
theorem setup_regional_no_start {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I}
    {σ0 : SinglePass.WalkState ι G} (h : RunCall.setup c = .ok (env, σ0))
    (hreg : c.regional.isSome = true) :
    (c.P.toArray.any fun node =>
      (successors node.continuation ++ node.handler.toList).any (·.label == c.start)) = false := by
  unfold RunCall.setup SinglePass.setup at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | (cases h; done) | skip
  all_goals
    have hn : ¬((c.P.toArray.any fun node =>
      (successors node.continuation ++ node.handler.toList).any (·.label == c.start)) &&
      c.regional.isSome) = true := by assumption
    simp only [hreg, Bool.and_true] at hn
    exact Bool.eq_false_iff.mpr hn

omit [Labels ι] in
/-- **The heads' given states** (`setupGiven`'s fold over the labels
below `n`): a label other than a head has none, a head below `n` its
written assertion with the claims' facts, at the start `startGiven`. -/
theorem setupGiven_get (n start : Nat) (isHead : Array Bool) (stated : Array (Option HeapKnowledge.Knowledge))
    (supplied : Array (Option (List HeapKnowledge.IndexAtom))) (entryIndices : List HeapKnowledge.IndexAtom)
    (entrySeparation : HeapSeparation.Separation) (counts : SinglePass.Counts) (t : Nat) :
    (SinglePass.setupGiven n start isHead stated supplied entryIndices entrySeparation counts).1[t]! =
      if t < n ∧ isHead[t]! = true then
        some (if t == start then SinglePass.startGiven stated[t]! entryIndices entrySeparation ((supplied[t]!).getD [])
          else { (stated[t]!).getD {} with indices := ((stated[t]!).getD {}).indices ++ (supplied[t]!).getD [] })
      else none := by
  unfold SinglePass.setupGiven
  -- The fold over `xs`, a sublist of the labels below `n` without repeats.
  have key : ∀ (xs : List Nat) (acc : Array (Option HeapKnowledge.Knowledge) × SinglePass.Counts),
      acc.1.size = n → xs.Nodup → (∀ x ∈ xs, x < n) →
      (xs.foldl (fun (acc : Array (Option HeapKnowledge.Knowledge) × SinglePass.Counts) l =>
        if isHead[l]! then
          let written : HeapKnowledge.Knowledge := if l == start then
              SinglePass.startWritten stated[l]! entryIndices entrySeparation else (stated[l]!).getD {}
          let claimsFacts := (supplied[l]!).getD []
          let counts := { acc.2 with
            givenWritten := acc.2.givenWritten + (SinglePass.atomsOf written).length
            givenClaims := acc.2.givenClaims + claimsFacts.length }
          (acc.1.set! l (some (if l == start then SinglePass.startGiven stated[l]! entryIndices entrySeparation claimsFacts
            else { written with indices := written.indices ++ claimsFacts })), counts)
        else acc) acc).1[t]! =
        if t ∈ xs ∧ isHead[t]! = true then
          some (if t == start then SinglePass.startGiven stated[t]! entryIndices entrySeparation ((supplied[t]!).getD [])
            else { (stated[t]!).getD {} with indices := ((stated[t]!).getD {}).indices ++ (supplied[t]!).getD [] })
        else acc.1[t]! := by
    intro xs
    induction xs with
    | nil => intro acc _ _ _; simp
    | cons x xs ih =>
      intro acc hsz hnd hlt
      obtain ⟨hx, hnd⟩ := List.nodup_cons.mp hnd
      rw [List.foldl_cons]
      split
      · rename_i hh
        rw [ih _ (by simp [hsz]) hnd (fun y hy => hlt y (List.mem_cons_of_mem _ hy))]
        by_cases htx : t = x
        · subst htx
          simp only [hh, and_true, List.mem_cons, true_or, if_true]
          have hts : t < acc.1.size := by have := hlt t (List.mem_cons_self ..); omega
          split
          · exact absurd ‹t ∈ xs› hx
          · rw [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds_self_of_lt hts]
            dsimp only; split <;> simp_all
        · have hne : x ≠ t := Ne.symm htx
          simp only [List.mem_cons, htx, false_or]
          split
          · rfl
          · simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds_ne hne]
      · rename_i hh
        rw [ih _ hsz hnd (fun y hy => hlt y (List.mem_cons_of_mem _ hy))]
        by_cases htx : t = x
        · subst htx; simp [hh]
        · simp [htx]
  rw [key _ _ (by simp) List.nodup_range (fun x hx => List.mem_range.mp hx)]
  simp only [List.mem_range]
  split
  · rfl
  · rw [getElem!_def, Array.getElem?_replicate]
    split <;> simp_all <;> rfl

omit [Labels ι] in
theorem getElem!_eq_getD_none {α : Type} (a : Array (Option α)) (t : Nat) : a[t]! = (a[t]?).getD none := by
  rw [getElem!_def]; cases a[t]? <;> rfl

/-- The start is below the bound and its claim's context is the inputs
(`entryRefusal_ok`). -/
theorem SetupOk.startClaim {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I}
    {σ0 : SinglePass.WalkState ι G} (hs : SetupOk c env σ0) :
    c.start < c.P.toArray.size ∧ passCtx c c.start = c.inputs ∧
      ((c.claims.toArray[c.start]?).map (·.context.length)).getD 0 = c.inputs.length := by
  obtain ⟨⟨cl, hcl, hctx⟩, -⟩ := entryRefusal_ok hs.entry
  have hlt : c.start < c.claims.length := (List.getElem?_eq_some_iff.mp hcl).1
  refine ⟨by rw [← hs.claimed]; simpa using hlt, by simp [passCtx, hcl, hctx], ?_⟩
  rw [List.getElem?_toArray, hcl]; simp [hctx]

/-- **The setup's environment states the call** (`EnvFacts`, by
`envFacts_of_loopHeads` from `setup_ok`, `setupGiven_get`). -/
theorem SetupOk.envFacts {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I}
    {σ0 : SinglePass.WalkState ι G} (hs : SetupOk c env σ0) : EnvFacts c env := by
  obtain ⟨hlt, hctx, hw⟩ := hs.startClaim
  obtain ⟨counts, hgiven⟩ := hs.given
  have hhead : envHead env = passHeads c := by
    funext t
    simp only [envHead, passHeads, passIsHead, hs.isHead]
  have hstartHead : env.isHead[c.start]! = true := by
    rw [hs.isHead, if_pos hlt, Array.set!_eq_setIfInBounds, getElem!_def,
      Array.getElem?_setIfInBounds_self_of_lt (by simp [SinglePass.loopHeads, SinglePass.Dfs.marks]; exact hlt)]
  have hstated : ∀ l, env.stated[l]! = passStated c l := fun l => by
    rw [hs.stated, getElem!_eq_getD_none]; rfl
  have hnames : env.startNames = List.range c.inputs.length := by rw [hs.startNames, hw]
  refine envFacts_of_loopHeads hs.nodes hs.n hs.reached hhead (by rw [hs.n]; exact hlt)
    (by rw [hs.claims, hs.n]; exact hs.claimed) hs.claims (fun t ht => ?_) hs.codes hs.checker hs.bound hs.goal
    hs.ensures hnames (by rw [hs.argName, hnames]) hstated hs.start hstartHead hctx ?_ hs.merging hs.regional hs.startKept
  · rw [hgiven, setupGiven_get, if_neg (fun h => by rw [ht] at h; exact Bool.false_ne_true h.2)]
  · refine ⟨((byLabel c.P.toArray.size (SinglePass.withStartOld G c.inputs c.entryIndices c.entrySeparation c.start c.ensures c.candidates)).getD c.start none).getD [], ?_, ?_⟩
    · have he := hs.entry
      rw [hs.givenImplies, hs.givenArgs, hs.givenInputs]
      unfold passStated
      rw [← Array.getD_eq_getD_getElem?]
      exact he
    · rw [hgiven, setupGiven_get, if_pos ⟨hlt, hstartHead⟩, if_pos (by simp), hstated c.start,
        getElem!_eq_getD_none (byLabel _ (SinglePass.withStartOld G c.inputs c.entryIndices c.entrySeparation c.start c.ensures c.candidates)), Array.getD_eq_getD_getElem?]
      rfl

omit [Labels ι] in
/-- One node's edges counted into the in-degrees: a label below the bound
other than a head gains its count among the edges' targets. -/
theorem inDeg_inner (N : Nat) (isHead : Array Bool) (t : Nat) (ht : t < N) (hh : isHead[t]! = false) :
    ∀ (ts : List Target) (a : Array Nat), a.size = N →
      (ts.foldl (fun (indeg : Array Nat) (x : Target) =>
        if x.label < N && !isHead[x.label]! then indeg.modify x.label (· + 1) else indeg) a).size = N ∧
      ((ts.foldl (fun (indeg : Array Nat) (x : Target) =>
        if x.label < N && !isHead[x.label]! then indeg.modify x.label (· + 1) else indeg) a)[t]?).getD 0 =
        (a[t]?).getD 0 + (ts.map (·.label)).count t
  | [], a, hs => by simp [hs]
  | x :: ts, a, hs => by
    rw [List.foldl_cons]
    split
    · obtain ⟨h1, h2⟩ := inDeg_inner N isHead t ht hh ts (a.modify x.label (· + 1)) (by simp [hs])
      refine ⟨h1, ?_⟩
      rw [h2, Array.getElem?_modify]
      by_cases hx : x.label = t
      · subst hx
        rw [if_pos rfl, Array.getElem?_eq_getElem (by omega)]
        simp; omega
      · rw [if_neg hx, List.map_cons, List.count_cons]
        simp [hx]
    · rename_i hc
      obtain ⟨h1, h2⟩ := inDeg_inner N isHead t ht hh ts a hs
      refine ⟨h1, ?_⟩
      rw [h2, List.map_cons, List.count_cons]
      by_cases hx : x.label = t
      · subst hx; simp [ht, hh] at hc
      · simp [hx]

omit [Labels ι] in
theorem zipIdx_range {α : Type} [Inhabited α] (a : Array α) :
    a.toList.zipIdx = (List.range a.size).map fun l => (a[l]!, l) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range, Array.getElem_toList, Nat.zero_add]
    rw [getElem!_pos a i (by simpa using h2)]

omit [Labels ι] in
/-- **The setup's in-degrees**: at a label below the bound other than a
head, the count of its edges from the nodes the start reaches. -/
theorem inDegrees_get (nodes : Array Node) (reached isHead : Array Bool) (t : Nat) (ht : t < nodes.size)
    (hh : isHead[t]! = false) :
    ((SinglePass.inDegrees nodes reached isHead)[t]?).getD 0 =
      ((List.range nodes.size).map fun s => if reached[s]! then (SinglePass.nodeSucc nodes s).count t else 0).sum := by
  unfold SinglePass.inDegrees
  rw [← Array.foldl_toList, Array.toList_zipIdx, zipIdx_range, List.foldl_map]
  have key : ∀ (xs : List Nat) (a : Array Nat), a.size = nodes.size →
      (xs.foldl (fun (indeg : Array Nat) (l : Nat) =>
        if reached[l]! then
          (successors nodes[l]!.continuation ++ nodes[l]!.handler.toList).foldl (fun (indeg : Array Nat) x =>
            if x.label < nodes.size && !isHead[x.label]! then indeg.modify x.label (· + 1) else indeg) indeg
        else indeg) a).size = nodes.size ∧
      ((xs.foldl (fun (indeg : Array Nat) (l : Nat) =>
        if reached[l]! then
          (successors nodes[l]!.continuation ++ nodes[l]!.handler.toList).foldl (fun (indeg : Array Nat) x =>
            if x.label < nodes.size && !isHead[x.label]! then indeg.modify x.label (· + 1) else indeg) indeg
        else indeg) a)[t]?).getD 0 =
        (a[t]?).getD 0 + (xs.map fun s => if reached[s]! then (SinglePass.nodeSucc nodes s).count t else 0).sum := by
    intro xs
    induction xs with
    | nil => intro a hs; simp [hs]
    | cons x xs ih =>
      intro a hs
      rw [List.foldl_cons]
      split
      · obtain ⟨i1, i2⟩ := inDeg_inner nodes.size isHead t ht hh _ a hs
        obtain ⟨h1, h2⟩ := ih _ i1
        refine ⟨h1, ?_⟩
        rw [h2, i2]
        simp only [List.map_cons, List.sum_cons, SinglePass.nodeSucc, *, if_true]
        omega
      · obtain ⟨h1, h2⟩ := ih a hs
        refine ⟨h1, ?_⟩
        rw [h2]
        simp only [List.map_cons, List.sum_cons, *]
        simp_all
  rw [(key _ _ (by simp)).2]
  simp [ht]

omit [Labels ι] in
theorem visB_replicate (n t : Nat) :
    visB (⟨Array.replicate n {}, Array.replicate n [], Array.replicate n [], Array.replicate n [], #[], 0⟩ :
      SinglePass.Walk ι) t = false := by
  simp only [visB, Array.getElem?_replicate]
  split <;> rfl

/-- **The state the first visit starts from meets the walk's invariant**
(`RecInv`): nothing visited or come in yet, the queue the reached labels
of in-degree 0 that are heads or the start, each in-degree the count of
the edges still to come (`inDegrees_get`), the start's names below the
counter. -/
theorem SetupOk.recInv {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I}
    {σ0 : SinglePass.WalkState ι G} (hs : SetupOk c env σ0) : RecInv c env σ0 := by
  obtain ⟨hlt, hctx, hw⟩ := hs.startClaim
  obtain ⟨counts, trace, rfl⟩ := hs.state
  have hvis : ∀ t, visB (SinglePass.setupState (G := G) c.P.toArray.size c.answers counts trace
      (SinglePass.inDegrees c.P.toArray env.reached env.isHead)
      (SinglePass.initialQueue c.P.toArray.size env.reached (SinglePass.inDegrees c.P.toArray env.reached env.isHead)
        env.isHead c.start)
      (((c.claims.toArray[c.start]?).map (·.context.length)).getD 0)).walk t = false := by
    intro t
    simp only [visB, SinglePass.setupState, Array.getElem?_replicate]
    split <;> rfl
  have hreach : ∀ s, envReached env s = env.reached[s]! := fun s => by
    simp only [envReached, getElem!_def]; cases env.reached[s]? <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.nodup_range.filter _
  · intro q hq
    simp only [SinglePass.setupState, SinglePass.initialQueue, List.mem_filter, List.mem_range, Bool.and_eq_true,
      beq_iff_eq] at hq
    obtain ⟨hq, ⟨hr, h0⟩, -⟩ := hq
    refine ⟨by rw [hs.n]; exact hq, by rw [hreach]; exact hr, hvis q, fun _ => ?_⟩
    simp only [deg, SinglePass.setupState]
    rw [getElem!_def] at h0
    revert h0; cases (SinglePass.inDegrees c.P.toArray env.reached env.isHead)[q]? <;> simp
  · intro t h; rw [hvis] at h; cases h
  · intro t h; rw [hvis] at h; cases h
  · intro s h; rw [hvis] at h; cases h
  · simp only [SinglePass.setupState]
    rw [List.filter_eq_nil_iff.mpr (fun t _ => by simp [visB_replicate])]
    rfl
  · simp [SinglePass.setupState, hs.n]
  · intro t ht hh
    have hh' : env.isHead[t]! = false := by
      simp only [envHead] at hh; rw [getElem!_def]; revert hh; cases env.isHead[t]? <;> simp
    simp only [deg, SinglePass.setupState]
    rw [hs.n] at ht
    rw [inDegrees_get _ _ _ t ht hh', pend, hs.n]
    congr 1
    refine List.map_congr_left fun s _ => ?_
    rw [hreach, exitsOf, hs.nodes]
    simp [visB_replicate]
  · intro t; simp [incS, incI, SinglePass.setupState, Array.getElem?_replicate]; split <;> rfl
  · simp [SinglePass.setupState]
  · intro t h; exfalso; apply h; simp [incS, SinglePass.setupState, Array.getElem?_replicate]; split <;> rfl
  · intro e he; simp [SinglePass.setupState] at he
  · intro t x hx; simp [incS, SinglePass.setupState, Array.getElem?_replicate] at hx; split at hx <;> simp at hx
  · intro x hx; simp only [SinglePass.setupState, hw]; exact List.mem_range.mp hx
  · refine ⟨fun x hx => ?_, fun a ha => ?_, fun i hi => ?_⟩
    · rw [hs.startNames] at hx; simpa [SinglePass.setupState] using List.mem_range.mp hx
    · rw [hs.argName] at ha
      obtain ⟨sl, -, hsl⟩ := Option.bind_eq_some_iff.mp ha
      rw [hs.startNames] at hsl
      simpa [SinglePass.setupState] using (List.mem_range.mp (List.mem_of_getElem? hsl))
    · rw [hs.startNames, hs.claims, hs.start] at *
      simp only [SinglePass.setupState]
      have : (List.range (((c.claims.toArray[c.start]?).map (·.context.length)).getD 0)).headD 0 = 0 := by
        cases ((c.claims.toArray[c.start]?).map (·.context.length)).getD 0 <;> simp [List.range_succ_eq_map]
      rw [this, Nat.add_zero]
      rw [getElem!_pos _ _ (by rw [List.size_toArray, ← List.size_toArray, hs.claimed]; exact hlt)] at hi
      rw [List.getElem?_toArray, List.getElem?_eq_getElem (by rw [← List.size_toArray, hs.claimed]; exact hlt)]
      simpa using hi
  · intro t h; rw [hvis] at h; cases h
  · intro t xs hx; simp [incI, SinglePass.setupState, Array.getElem?_replicate] at hx; split at hx <;> simp at hx
  · exact cachedVacuity_empty _ _
  · simp [SinglePass.setupState, hs.n]
  · intro t _ _
    simp only [SinglePass.setupState, incS, deg, Array.getElem?_replicate]
    have hd : SinglePass.inDegrees c.P.toArray env.reached env.isHead = passDegrees c := by
      rw [hs.reached, hs.isHead]; rfl
    rw [hd]
    split <;> simp
  · intro t h; rw [hvis] at h; cases h
  · intro t h; rw [hvis] at h; cases h
  · simp [SinglePass.setupState, hs.n]

/-- **(`setupRecords_of`) The setup starts the walk's invariant**
(`SetupRecords`): a returned setup's environment states the call and its
state meets `RecInv` (`setup_ok`, `SetupOk.envFacts`, `SetupOk.recInv`). -/
theorem setupRecords_of : SetupRecords ι := fun _ _ _ _ _ h => ⟨(setup_ok h).envFacts, (setup_ok h).recInv⟩

end Setup
end Verification.TolerantFrames
