import Verification.Programs.TolerantFramesRegionalAlignment

/-! # Sparse readback of recorded regional visits -/
namespace Verification.TolerantFrames
open Verification SinglePass ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open ProgramTyping LabelStore GraphCode GraphCode.ArgumentRegionGraph
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- All projections of a sparse entry select the same last occurrence. -/
theorem sparseFold_pick (xs : List (Nat × RegionState)) (t : Nat)
    (hm : ∃ r, (t, r) ∈ xs) :
    ∃ r, (t, r) ∈ xs ∧ ∀ {α : Type} (get : RegionState → α) (table : List α)
      (empty : α), t < table.length →
      ((xs.map fun x => (x.1, get x.2)).foldl
        (fun acc (j, x) => acc.set j x) table).getD t empty = get r := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    by_cases ht : ∃ r, (t, r) ∈ xs
    · obtain ⟨r, hr, hp⟩ := ih ht
      refine ⟨r, List.mem_cons_of_mem _ hr, ?_⟩
      intro α get table empty hb
      simpa only [List.map_cons, List.foldl_cons] using
        hp get (table.set x.1 (get x.2)) empty (by simpa using hb)
    · obtain ⟨r, hr⟩ := hm
      have he : (t, r) = x := (List.mem_cons.mp hr).resolve_right (fun h => ht ⟨r, h⟩)
      subst x
      refine ⟨r, List.mem_cons_self .., ?_⟩
      intro α get table empty hb
      simp only [List.map_cons, List.foldl_cons, List.getD_eq_getElem?_getD]
      rw [sparseFold_frame]
      · simp [hb]
      · intro y hy heq
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        change z.1 = t at heq
        exact ht ⟨z.2, by simpa only [← heq] using hz⟩

/-- A target occurrence overrides the initial own entry in every projection. -/
theorem sparse_region_target (n l t : Nat) (own : RegionState) (xs : List (Nat × RegionState))
    (ht : t < n) (hm : ∃ r, (t, r) ∈ xs) :
    ∃ r, (t, r) ∈ xs ∧
      (⟨(sparse n [] (((l, own) :: xs).map fun x => (x.1, x.2.facts))).getD t [],
        (sparse n [] (((l, own) :: xs).map fun x => (x.1, x.2.values))).getD t [],
        (sparse n [] (((l, own) :: xs).map fun x => (x.1, x.2.cells))).getD t [],
        (sparse n [] (((l, own) :: xs).map fun x => (x.1, x.2.fields))).getD t []⟩ : RegionState) = r := by
  obtain ⟨r, hr, hp⟩ := sparseFold_pick xs t hm
  refine ⟨r, hr, ?_⟩
  have hf := hp RegionState.facts ((List.replicate n []).set l own.facts) [] (by simpa using ht)
  have hv := hp RegionState.values ((List.replicate n []).set l own.values) [] (by simpa using ht)
  have hc := hp RegionState.cells ((List.replicate n []).set l own.cells) [] (by simpa using ht)
  have hs := hp RegionState.fields ((List.replicate n []).set l own.fields) [] (by simpa using ht)
  simp only [sparse, List.map_cons, List.foldl_cons, hf, hv, hc, hs]

/-- Every in-bounds non-head target's established state survives the target fold. -/
theorem regionalFold_retains_target (heads : Nat → Bool) (given : Nat → RegionState)
    (established : Target → Bool → RegionState) (ts : List (Target × Bool))
    (acc : List (Nat × RegionState) × Array (List RegionState))
    (x : Target × Bool) (hx : x ∈ ts) (hh : heads x.1.label = false)
    (hb : x.1.label < acc.2.size) :
    established x.1 x.2 ∈ (ts.foldl (fun acc (t, h) =>
      if heads t.label then (acc.1 ++ [(t.label, given t.label)], acc.2)
      else (acc.1 ++ [(t.label, established t h)], acc.2.modify t.label (established t h :: ·))) acc).2[x.1.label]! := by
  induction ts generalizing acc with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with he | he
    · subst y
      simp only [List.foldl_cons, hh, Bool.false_eq_true, ↓reduceIte]
      apply (regionalFold_inputs heads given established ys _).1
      simp [getElem!_def, Array.getElem?_modify, Array.getElem?_eq_getElem hb]
    · simp only [List.foldl_cons]
      split
      · exact ih _ he hb
      · exact ih _ he (by simpa using hb)

/-- A non-head target reads a state retained in this visit's incoming table. -/
theorem regionalAt_nonhead_target {env : WalkEnv ι G I} {l t : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming : Array (List RegionState)} {done : RegionalDone ι}
    (h : regionalAt G I env l en sd rg a incoming = .ok done) (ht : t < env.n)
    (hm : t ∈ nodeSucc env.nodes l) (hh : env.isHead[t]! = false) (hb : t < incoming.size) :
    regionalTableState done t ∈ done.regionIn[t]! := by
  unfold regionalAt at h
  extract_lets node c width st here sums ordinaryEv kHere cEv t0 F C Fs origins pushes outR outF outC outFs established targets n at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals
    have hf := regionalFold_entries (fun t => env.isHead[t]!)
      (fun t => ((rg.heads[t]?).join).getD {}) established targets
      ([(l, { here with cells := C, fields := Fs })], incoming)
    have hm' : ∃ x ∈ targets, x.1.label = t := by
      obtain ⟨target, htarget, hlabel⟩ := List.mem_map.mp hm
      rcases List.mem_append.mp htarget with hs | hs
      · exact ⟨(target, false), List.mem_append_left _ (List.mem_map.mpr ⟨target, hs, rfl⟩), hlabel⟩
      · exact ⟨(target, true), List.mem_append_right _ (List.mem_map.mpr ⟨target, hs, rfl⟩), hlabel⟩
    obtain ⟨x, hx, hxt⟩ := hm'
    let xs := targets.map fun (t, h) => (t.label, if env.isHead[t.label]! then ((rg.heads[t.label]?).join).getD {} else established t h)
    have hm'' : ∃ r, (t, r) ∈ xs := by
      refine ⟨established x.1 x.2, List.mem_map.mpr ⟨x, hx, ?_⟩⟩
      simp [hxt, hh]
    obtain ⟨r, hr, he⟩ := sparse_region_target env.n l t { here with cells := C, fields := Fs } xs ht hm''
    obtain ⟨y, hy, hy'⟩ := List.mem_map.mp hr
    have hyt := congrArg Prod.fst hy'
    have hyr := congrArg Prod.snd hy'
    dsimp only at hyt hyr
    have hr' : r = established y.1 y.2 := by simpa [hyt, hh] using hyr.symm
    have hi := regionalFold_retains_target (fun t => env.isHead[t]!)
      (fun t => ((rg.heads[t]?).join).getD {}) established targets
      ([(l, { here with cells := C, fields := Fs })], incoming) y hy
      (by simpa only [hyt] using hh) (by simpa only [hyt] using hb)
    simp_all only
    rename_i hderiv x' at_ rin table ft hcheck
    have hread : regionalTableState
        { regionIn := rin, state := { here with cells := C, fields := Fs }, table, ft, cEv } t = established y.1 y.2 := by
      simp only [regionalTableState, ArgumentPathTracking.atLabel, factsAt, fieldsAt]
      dsimp only [table, ft]
      rw [hf]
      exact he
    rw [hread]
    exact hi

/-- Every head target reads exactly the supplied head state, including a self-edge. -/
theorem regionalAt_head_target {env : WalkEnv ι G I} {l t : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming : Array (List RegionState)} {done : RegionalDone ι}
    (h : regionalAt G I env l en sd rg a incoming = .ok done) (ht : t < env.n)
    (hm : t ∈ nodeSucc env.nodes l) (hh : env.isHead[t]! = true) :
    regionalTableState done t = ((rg.heads[t]?).join).getD {} := by
  unfold regionalAt at h
  extract_lets node c width st here sums ordinaryEv kHere cEv t0 F C Fs origins pushes outR outF outC outFs established targets n at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals
    have hf := regionalFold_entries (fun t => env.isHead[t]!)
      (fun t => ((rg.heads[t]?).join).getD {}) established targets
      ([(l, { here with cells := C, fields := Fs })], incoming)
    have hm' : ∃ x ∈ targets, x.1.label = t := by
      obtain ⟨target, htarget, hlabel⟩ := List.mem_map.mp hm
      rcases List.mem_append.mp htarget with hs | hs
      · exact ⟨(target, false), List.mem_append_left _ (List.mem_map.mpr ⟨target, hs, rfl⟩), hlabel⟩
      · exact ⟨(target, true), List.mem_append_right _ (List.mem_map.mpr ⟨target, hs, rfl⟩), hlabel⟩
    obtain ⟨x, hx, hxt⟩ := hm'
    let xs := targets.map fun (t, h) => (t.label, if env.isHead[t.label]! then ((rg.heads[t.label]?).join).getD {} else established t h)
    have hm'' : ∃ r, (t, r) ∈ xs := by
      refine ⟨((rg.heads[t]?).join).getD {}, List.mem_map.mpr ⟨x, hx, ?_⟩⟩
      simp [hxt, hh]
    obtain ⟨r, hr, he⟩ := sparse_region_target env.n l t { here with cells := C, fields := Fs } xs ht hm''
    have hr' : r = ((rg.heads[t]?).join).getD {} := by
      obtain ⟨y, hy, hy'⟩ := List.mem_map.mp hr
      have hyt := congrArg Prod.fst hy'
      have hyr := congrArg Prod.snd hy'
      dsimp only at hyt hyr
      simpa [hyt, hh] using hyr.symm
    simp_all only
    rename_i hderiv x' at_ rin table ft hcheck
    simp only [regionalTableState, ArgumentPathTracking.atLabel, factsAt, fieldsAt]
    dsimp only [table, ft]
    rw [hf]
    exact he

/-- The selected regional proof has the source claim's context. -/
theorem regionalAt_entry_header
    {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming : Array (List RegionState)} {done : RegionalDone ι}
    (hd : regionalAt G I env l en sd rg a incoming = .ok done) :
    entry done.cEv = (env.claimed[l]!).context := by
  obtain ⟨hc, hev, _⟩ := regionalAt_checks hd
  rw [hev]
  cases hderiv : sd.st.stepDeriv with
  | some d =>
    rw [hderiv] at hc
    simp only [regionalDerivChecked, derivChecked, Bool.and_eq_true, beq_iff_eq] at hc
    simpa [entry, passRegionalEvidence, NodeEvidence.expression] using hc.1.2
  | none =>
    have hp := fun p => regionalAt_header hd hderiv (p := p)
    simp only [passRegionalEvidence, entry, NodeEvidence.expression, NodeEvidence.header]
    cases he : sd.st.stepEffect with
    | none => rfl
    | some e =>
      cases hep : e.proof? with
      | none => simp only [Option.bind_some, hep]; rfl
      | some p => simpa [hep] using (hp p (by simp [he, hep])).1

/-- A successful self-edge check retains the head's cells and fields. -/
theorem regionalAt_own_head {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming : Array (List RegionState)} {done : RegionalDone ι}
    (h : regionalAt G I env l en sd rg a incoming = .ok done) (hl : l < env.n)
    (hm : l ∈ nodeSucc env.nodes l) (hh : env.isHead[l]! = true) (hn : l ≠ env.start)
    (hentry : entry done.cEv = (env.claimed[l]!).context) :
    regionalTableState done l = done.state := by
  have ht := regionalAt_head_target h hl hm hh
  have hc := (regionalAt_checks h).2.2
  have hF := congrArg RegionState.values ht
  have hC := congrArg RegionState.cells ht
  have hFs := congrArg RegionState.fields ht
  simp only [regionalTableState] at hF hC hFs
  simp only [checkNode, checkFresh, Bool.and_eq_true] at hc
  have hk := hc.1.1.1.1.2.2
  have hfields := hc.1.1.1.1.1.1.1.1.1
  rw [hF, hC] at hk
  rw [hFs] at hfields
  unfold regionalAt at h
  extract_lets node c width st here sums ordinaryEv kHere cEv t0 F C Fs origins pushes outR outF outC outFs established targets n at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals
    have hhere : here = ((rg.heads[l]?).join).getD {} := by
      simp only [here, beq_eq_false_iff_ne.mpr hn, Bool.false_eq_true, ↓reduceIte, hh]
    have hcells : C = here.cells := by
      have hk' : cellsKept G I sums rg.Φ F here.cells cEv t0 node.handler.isSome = true := by
        simpa only [F, hhere] using hk
      exact if_pos hk'
    have hfields' : Fs = here.fields := by
      apply List.filter_eq_self.mpr
      intro p hp
      have hf := List.all_eq_true.mp hfields p (hhere ▸ hp)
      simpa only [hentry] using hf
    rw [ht]
    change ((rg.heads[l]?).join).getD {} = { here with cells := C, fields := Fs }
    rw [hcells, hfields']
    exact hhere.symm

/-- A returned walk has a successful setup. -/
theorem returnedWalk_setup {c : Target.RunCall G I} {σ : WalkState ι G} {reach : Nat}
    (hw : RunCall.walk c = .ok (σ, reach)) :
    ∃ env σ0, RunCall.setup c = .ok (env, σ0) := by
  unfold RunCall.walk SinglePass.runWalk at hw
  cases hr : RunCall.setup c with
  | error stop =>
    unfold RunCall.setup at hr
    simp only [hr, bind, Except.bind] at hw
    cases hw
  | ok p => exact ⟨p.1, p.2, rfl⟩

/-- The final invariant holds in the environment returned by setup. -/
theorem returnedWalk_setup_inv {c : Target.RunCall G I} {σ : WalkState ι G} {reach : Nat}
    (hw : RunCall.walk c = .ok (σ, reach)) :
    ∃ env σ0, RunCall.setup c = .ok (env, σ0) ∧ EnvFacts c env ∧ RecInv c env σ := by
  have hv : VisitsRecord ι := visitsRecord_of (visitsRest_of (exitsPushOk_of exitsWidth)
    (visitsSettle_of (visitStepPrefix_of_exitStep exitStepPrefix)) visitsImplications) visitExits_answers_prefix
  unfold RunCall.walk SinglePass.runWalk at hw
  cases hr : RunCall.setup c with
  | error stop =>
    unfold RunCall.setup at hr
    simp only [hr, bind, Except.bind] at hw
    cases hw
  | ok p =>
    obtain ⟨env, σ0⟩ := p
    have hr' := hr
    unfold RunCall.setup at hr'
    obtain ⟨hE, hI0⟩ := setupRecords_of G I c env σ0 hr
    cases hd : SinglePass.drive (SinglePass.visit G I env) (env.n + 1) σ0 with
    | error stop =>
      simp only [hr', hd, bind, Except.bind] at hw
      cases hw
    | ok σf =>
      simp only [hr', hd, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hdr := drives_of_drive _ _ _ hd
      have hinv := Drives.inv (RecInv c env)
        (fun σ σ₁ l rest hq hI hvis => recInv_visit hE hI hq (hv G I c env σ0 σ σ₁ l rest hr hE hI hq hvis)
          ((visitsKeepSummaries ι G I env).1 { σ with queue := rest } l σ₁ hvis)) hdr hI0
      exact ⟨env, σ0, rfl, hE, hinv⟩

/-- A visited self-edge is a head: otherwise it is a one-edge non-head cycle. -/
theorem returnedWalk_self_head {c : Target.RunCall G I} {env : WalkEnv ι G I}
    {σ : WalkState ι G} {reach l : Nat}
    (hw : RunCall.walk c = .ok (σ, reach)) (hE : EnvFacts c env)
    (hl : visB σ.walk l = true) (hself : l ∈ nodeSucc env.nodes l) :
    env.isHead[l]! = true := by
  obtain ⟨env0, σ0, hsetup, _, hi⟩ := returnedWalk_setup_inv hw
  have hok := setup_ok hsetup
  have hv := hi.visR l hl
  have hb : l < c.P.toArray.size := hok.n ▸ hv.1
  have hr : (loopHeads c.P.toArray c.start).2[l]?.getD false = true := by
    simpa only [envReached, hok.reached] using hv.2
  have hs : l ∈ nodeSucc c.P.toArray l := hE.nodes ▸ hself
  have hh : passHeads c l = true := by
    cases hh : passHeads c l with
    | true => rfl
    | false => exact False.elim (passHeads_cuts c l (.one ⟨hr, hs, hb, hh⟩))
  have he : envHead env l = true := by rw [hE.heads]; exact hh
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  exact he

/-- Regional setup excludes start targets, including handlers. -/
theorem returnedWalk_regional_no_start {c : Target.RunCall G I} {env : WalkEnv ι G I}
    {σ : WalkState ι G} {reach : Nat} {rg : Regional}
    (hw : RunCall.walk c = .ok (σ, reach)) (hE : EnvFacts c env) (hi : RecInv c env σ)
    (hreg : env.regional = some rg) {l : Nat} (hl : visB σ.walk l = true) :
    ∀ t ∈ nodeSucc env.nodes l, t ≠ env.start := by
  obtain ⟨env0, σ0, hsetup⟩ := returnedWalk_setup hw
  have hr : c.regional.isSome = true := by rw [← hE.regional, hreg]; rfl
  have hn := setup_regional_no_start hsetup hr
  have hbound : l < env.nodes.size := by simpa [hE.nodes, hE.nodeCount] using (hi.visR l hl).1
  intro t ht heq
  have hall := Bool.eq_false_iff.mp hn
  apply hall
  rw [← hE.nodes]
  apply Array.any_eq_true.mpr
  refine ⟨l, hbound, ?_⟩
  rw [← getElem!_pos env.nodes l hbound]
  obtain ⟨target, htarget, hlabel⟩ := List.mem_map.mp ht
  apply List.any_eq_true.mpr
  exact ⟨target, htarget, by simp [hlabel, heq, hE.startLabel]⟩

/-- The invariant's chosen visit reads retained final inputs at every
non-head target, using the allocation retained with that visit. -/
theorem RecInv.regionalInputReadback {c : Target.RunCall G I} {env : WalkEnv ι G I}
    {σ : WalkState ι G} (hi : RecInv c env σ) {l : Nat} (hl : visB σ.walk l = true)
    {rg : Regional} (hreg : env.regional = some rg) :
    ∃ (before : WalkState ι G) (en : Entered ι) (sd : StepDone ι G) (ex : ExitsDone ι G)
      (done : RegionalDone ι),
      visitEntry G I env before l = .ok en ∧ visitStep G I env before l en = .ok sd ∧
      visitExits G I env before l en sd = .ok ex ∧
      regionalAt G I env l en sd rg (exitsYields G I env l en sd).2 before.regionIn = .ok done ∧
      σ.walk.labels[l]? = some (LabelWalk.ofVisit before.fresh en sd (some done.state)) ∧
      SumsPrefix ex.answers σ.answers ∧
      ∀ t ∈ nodeSucc env.nodes l, envHead env t = false →
        regionalTableState done t ∈ σ.regionIn[t]! := by
  obtain ⟨before, en, sd, ex, done, he, hs, hx, hd, hr, hp, hb, _, hm⟩ := hi.regionalInputWitness hl hreg
  refine ⟨before, en, sd, ex, done, he, hs, hx, hd, hr, hp, ?_⟩
  intro t ht hh
  have hh' : env.isHead[t]! = false := by
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    exact hh
  exact hm t _ (regionalAt_nonhead_target hd (hi.exits l hl t ht) ht hh' (hb ▸ hi.exits l hl t ht))

/-- A retained non-head input bounds the final target's recorded state. -/
theorem regionalRecorded_nonhead_of_inputs {c : Target.RunCall G I} {env : WalkEnv ι G I}
    {σ : WalkState ι G} {reach l t : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming : Array (List RegionState)} {done : RegionalDone ι}
    (hw : RunCall.walk c = .ok (σ, reach)) (hle : reach ≤ σ.walk.visited)
    (hE : EnvFacts c env) (hi : RecInv c env σ) (hreg : env.regional = some rg)
    (hl : visB σ.walk l = true) (ht : t ∈ nodeSucc env.nodes l) (hh : envHead env t = false)
    (hd : regionalAt G I env l en sd rg a incoming = .ok done) (hb : t < incoming.size)
    (hm : ∀ e ∈ done.regionIn[t]!, e ∈ σ.regionIn[t]!) :
    RegionBelow (recordedRegionState σ.walk t) (regionalTableState done t) := by
  have hh' : env.isHead[t]! = false := by
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    exact hh
  have he := hm _ (regionalAt_nonhead_target hd (hi.exits l hl t ht) ht hh' hb)
  exact hi.regional_nonhead_bound (returnedWalk_successor_visited hw hle hE hl ht) hreg
    (returnedWalk_regional_no_start hw hE hi hreg hl t ht) hh he

/-- Readback separates the own entry, start exclusion and target entries. -/
theorem regionalRecordedReadback :
    RegionalRecordedReadback ι := by
  intro G I c env σ reach rg hw hle hE hi hreg _ l hl
  obtain ⟨before, en, sd, ex, done, he, hs, hx, hd, hr, hp, targets⟩ := hi.regionalInputReadback hl hreg
  refine ⟨before, en, sd, ex, done, he, hs, hx, hd, hr, hp, ?_⟩
  have own : regionalTableState done l = done.state := by
    by_cases hloop : l ∈ nodeSucc env.nodes l
    · exact regionalAt_own_head hd (hi.visR l hl).1 hloop (returnedWalk_self_head hw hE hl hloop)
        (returnedWalk_regional_no_start hw hE hi hreg hl l hloop) (regionalAt_entry_header hd)
    · exact regionalAt_own_no_self hd (hi.visR l hl).1 hloop
  have noStart : ∀ t ∈ nodeSucc env.nodes l, t ≠ env.start :=
    returnedWalk_regional_no_start hw hE hi hreg hl
  refine ⟨own, ?_⟩
  intro t ht
  have hm : t.label ∈ nodeSucc env.nodes l := by
    apply List.mem_map.mpr
    refine ⟨t, ?_, rfl⟩
    rcases ht with ht | ht
    · exact List.mem_append_left _ ht
    · exact List.mem_append_right _ (by simpa using ht)
  refine ⟨noStart t.label hm, ?_⟩
  cases hh : envHead env t.label with
  | true =>
    simp only [↓reduceIte]
    have hh' : env.isHead[t.label]! = true := by
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      exact hh
    rw [regionalAt_head_target hd (hi.exits l hl t.label hm) hm hh']
    exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨regionalTableState done t.label, targets t.label hm hh,
      fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

end Verification.TolerantFrames
