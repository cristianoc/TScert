import Verification.Source.Claims.PassUnitHeadline

/-! # The single pass's unit theorem: mode 8's inferred route

Mode 8 checks a group by `FilePlans.passGroupMode8`, with no given lines:
the loop heads' proposals inference computes, each member run until
accepted or its refusal stands, a refused proposal dropped between runs
(`passGroupInferred`). Inference changes only the candidates the pass
reads (`Recandidated`), and the verdict is accepted only where each
member's last run is the pass's accepted run over its plans at that run's
candidates: `passGroupMode8_safe`, every member of an accepted group is
safe at the plans the route started from. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore

/-- **`f'` is `f` with other candidates**: the same file and store, each
plan of `f'` the one of `f` at the same
index with its request's candidates replaced. -/
def Recandidated (f f' : FilePlans) : Prop :=
  ∃ P : List (Except String (FunctionPlan (EquationStore.Checked f.F.equations f.F.primitive)
      (EquationStore.CheckedLabel f.F.equations f.F.primitive))),
    f' = { f with plans := P } ∧
    ∀ (i : Nat) (x : FunctionPlan (EquationStore.Checked f.F.equations f.F.primitive)
      (EquationStore.CheckedLabel f.F.equations f.F.primitive)), P[i]? = some (.ok x) →
      ∃ x₀, f.plans[i]? = some (.ok x₀) ∧ ∃ cands, x = x₀.mapRequest fun r => { r with candidates := cands }

theorem mapRequest_candidates_self {σ ι : Type} [Labels ι] [StoreView σ ι] (x : FunctionPlan σ ι) :
    x = x.mapRequest fun r => { r with candidates := x.parts.2.2.candidates } := by
  cases x <;> rfl

theorem mapRequest_candidates_twice {σ ι : Type} [Labels ι] [StoreView σ ι] (x : FunctionPlan σ ι) (c₀ c₁) :
    (x.mapRequest fun r => { r with candidates := c₀ }).mapRequest (fun r => { r with candidates := c₁ }) =
      x.mapRequest fun r => { r with candidates := c₁ } := by
  cases x <;> rfl

theorem Recandidated.refl (f : FilePlans) : Recandidated f f :=
  ⟨f.plans, rfl, fun _ x h => ⟨x, h, _, mapRequest_candidates_self x⟩⟩

theorem Recandidated.trans {f f' f'' : FilePlans} (h₁ : Recandidated f f') (h₂ : Recandidated f' f'') :
    Recandidated f f'' := by
  obtain ⟨P, rfl, hP⟩ := h₁
  obtain ⟨Q, rfl, hQ⟩ := h₂
  refine ⟨Q, rfl, fun i x h => ?_⟩
  obtain ⟨x₁, h₁, c₁, rfl⟩ := hQ i x h
  obtain ⟨x₀, h₀, c₀, rfl⟩ := hP i x₁ h₁
  exact ⟨x₀, h₀, c₁, mapRequest_candidates_twice x₀ c₀ c₁⟩

/-- Other candidates keep the store every plan is over (proved). -/
theorem Recandidated.overStore {f f' : FilePlans} (h : Recandidated f f') (hover : OverStore f) : OverStore f' := by
  obtain ⟨P, rfl, hP⟩ := h
  exact overStore_of_mapRequest (fun i x hx => by
    obtain ⟨x₀, h₀, c, rfl⟩ := hP i x hx
    exact ⟨x₀, _, h₀, rfl, rfl⟩) hover

/-- A member safe at other candidates is safe (proved): a request's safety
reads no candidate (`requestSafe_recandidated`). -/
theorem Recandidated.memberSafe {f f' : FilePlans} (h : Recandidated f f') {j : Nat} (hs : MemberSafe f' j) :
    MemberSafe f j := by
  obtain ⟨P, rfl, hP⟩ := h
  obtain ⟨p, c, hp, hc, hsafe⟩ := hs
  obtain ⟨x₀, h₀, cands, rfl⟩ := hP j p hp
  cases x₀ with
  | graph name pos r =>
    simp only [FunctionPlan.mapRequest, FunctionPlan.certify, pure, Except.pure, Except.ok.injEq] at hc
    subst hc
    exact ⟨.graph name pos r, .graph name pos r, h₀, rfl, requestSafe_recandidated r cands hsafe⟩

/-- Plans mapped index by index, each one of the original's with its
request's candidates replaced, are `Recandidated` (proved). -/
theorem recandidated_of_map {f : FilePlans}
    (ψ : Except String (FunctionPlan (EquationStore.Checked f.F.equations f.F.primitive)
      (EquationStore.CheckedLabel f.F.equations f.F.primitive)) × Nat →
      Except String (FunctionPlan (EquationStore.Checked f.F.equations f.F.primitive)
        (EquationStore.CheckedLabel f.F.equations f.F.primitive)))
    (hψ : ∀ e j x, ψ (e, j) = .ok x → ∃ x₀, e = .ok x₀ ∧ ∃ cands, x = x₀.mapRequest fun r => { r with candidates := cands }) :
    Recandidated f { f with plans := f.plans.zipIdx.map ψ } := by
  refine ⟨_, rfl, fun i x h => ?_⟩
  simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_eq_some_iff] at h
  obtain ⟨⟨p, j⟩, hp, he⟩ := h
  simp only [Prod.mk.injEq] at hp
  obtain ⟨p', hp', rfl, rfl⟩ := hp
  obtain ⟨x₀, rfl, hr⟩ := hψ _ _ _ he
  exact ⟨x₀, hp', hr⟩

/-- Candidates left out keep the plans `Recandidated` (proved). -/
theorem dropCandidates_recandidated (f : FilePlans) (i l : Nat) (drop : List HeapKnowledge.Candidate) :
    Recandidated f (f.dropCandidates i l drop) := by
  unfold FilePlans.dropCandidates
  refine recandidated_of_map _ (fun e j x h => ?_)
  dsimp only at h
  split at h
  · exact ⟨x, h, _, mapRequest_candidates_self x⟩
  · cases e with
    | error _ => cases h
    | ok q =>
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      cases q <;> exact ⟨_, rfl, _, rfl⟩

/-- The region separations proposed keep the plans `Recandidated` (proved). -/
theorem withFreshApart_recandidated (f : FilePlans) (force : Bool) (group : List Nat) :
    Recandidated f (f.withFreshApart force group) := by
  unfold FilePlans.withFreshApart
  refine recandidated_of_map _ (fun e j x h => ?_)
  dsimp only at h
  split at h
  · exact ⟨x, h, _, mapRequest_candidates_self x⟩
  · cases e with
    | error _ => cases h
    | ok q =>
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      cases q with
      | graph n ps r₀ =>
        simp only [FunctionPlan.mapRequest]
        split
        · exact ⟨_, rfl, r₀.candidates, rfl⟩
        · exact ⟨_, rfl, _, rfl⟩

/-- **A member's runs end at a run of the state they reach** (proved):
`settleInferred`'s run is `run` of its last state, and that state is
related to the first by any reflexive, transitive relation each next state
keeps. -/
theorem settleInferred_last {S G R W : Type} {run : S → G → R} {refusal : R → Option W}
    {next : S → G → W → Option (S × G × List String × Nat)} (Q : S → S → Prop)
    (hrefl : ∀ s, Q s s) (htrans : ∀ a b c, Q a b → Q b c → Q a c)
    (hnext : ∀ s g w s' g' ls d, next s g w = some (s', g', ls, d) → Q s s') :
    ∀ n s g ls d runs, Q s (settleInferred run refusal next n s g ls d runs).state ∧
      (settleInferred run refusal next n s g ls d runs).last =
        run (settleInferred run refusal next n s g ls d runs).state (settleInferred run refusal next n s g ls d runs).given := by
  intro n
  induction n with
  | zero => intro s g ls d runs; exact ⟨hrefl s, rfl⟩
  | succ n ih =>
    intro s g ls d runs
    simp only [settleInferred]
    cases refusal (run s g) with
    | none => exact ⟨hrefl s, rfl⟩
    | some w =>
      dsimp only
      cases hn : next s g w with
      | none => exact ⟨hrefl s, rfl⟩
      | some x =>
        obtain ⟨s', g', ls', d'⟩ := x
        dsimp only
        obtain ⟨hq, hr⟩ := ih s' g' (ls ++ ls') (d + d') (runs + 1)
        exact ⟨htrans _ _ _ (hnext _ _ _ _ _ _ _ hn) hq, hr⟩

/-- A next state of `inferredNext` is `Recandidated` (proved). -/
theorem inferredNext_recandidated {f : FilePlans} {fixed : Bool} {protect : List (Nat × List HeapKnowledge.Candidate)}
    {given : Option (Std.HashMap String Json)} {i : Nat} {w : String × Option (Nat × List HeapKnowledge.Candidate)}
    {f' : FilePlans} {given' : Option (Std.HashMap String Json)} {ls : List String} {d : Nat}
    (h : f.inferredNext fixed protect given i w = some (f', given', ls, d)) : Recandidated f f' := by
  unfold FilePlans.inferredNext at h
  split at h
  · split at h
    · cases h
    · simp only [bind, Option.bind, pure] at h
      split at h
      · cases h
      · cases h; exact Recandidated.refl _
  · split at h
    · split at h
      · cases h
      · simp only [bind, Option.bind, pure] at h
        split at h
        · cases h
        · cases h; exact Recandidated.refl _
    · simp only [bind, Option.bind, pure] at h
      split at h
      · cases h
      · rename_i x _
        obtain ⟨l, missing⟩ := x
        dsimp only at h
        split at h
        · cases h
        · dsimp only at h
          split at h
          · cases h
          · dsimp only at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -, -, -⟩ := h
            have key : ∀ (xs : List (Nat × List HeapKnowledge.Candidate)) (g : FilePlans), Recandidated f g →
                Recandidated f (xs.foldl (fun (g : FilePlans) (x : Nat × List HeapKnowledge.Candidate) =>
                  g.dropCandidates i x.1 x.2) g) := by
              intro xs
              induction xs with
              | nil => intro g h; exact h
              | cons x xs ih => intro g h; exact ih _ (h.trans (dropCandidates_recandidated _ _ _ _))
            exact key _ _ (dropCandidates_recandidated _ _ _ _)

/-- Leaving candidates out head by head keeps the plans `Recandidated`
(proved). -/
theorem dropAll_recandidated (f : FilePlans) (i : Nat) (ds : List (Nat × List HeapKnowledge.Candidate)) :
    Recandidated f (f.dropAll i ds) := by
  unfold FilePlans.dropAll
  have key : ∀ (xs : List (Nat × List HeapKnowledge.Candidate)) (g : FilePlans), Recandidated f g →
      Recandidated f (xs.foldl (fun (g : FilePlans) (x : Nat × List HeapKnowledge.Candidate) =>
        g.dropCandidates i x.1 x.2) g) := by
    intro xs
    induction xs with
    | nil => intro g h; exact h
    | cons x xs ih => intro g h; exact ih _ (h.trans (dropCandidates_recandidated _ _ _ _))
  exact key ds f (Recandidated.refl f)

/-- A next state of `inferredNextAll` is `Recandidated` (proved):
`inferredNext`'s, then candidates left out. -/
theorem inferredNextAll_recandidated {f : FilePlans} {fuel : Nat} {fixed : Bool}
    {protect : List (Nat × List HeapKnowledge.Candidate)}
    {given : Option (Std.HashMap String Json)} {i : Nat} {w : String × Option (Nat × List HeapKnowledge.Candidate)}
    {f' : FilePlans} {given' : Option (Std.HashMap String Json)} {ls : List String} {d : Nat}
    (h : f.inferredNextAll fuel fixed protect given i w = some (f', given', ls, d)) : Recandidated f f' := by
  unfold FilePlans.inferredNextAll at h
  split at h
  · cases h
  · rename_i f₁ g₁ ls₁ d₁ hn
    have h₁ := inferredNext_recandidated hn
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -, -⟩ := h
      exact h₁
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -, -⟩ := h
      exact h₁.trans (dropAll_recandidated _ _ _)

/-- **A member's runs end at an inferred run of plans with other
candidates** (proved). -/
theorem inferredSettle_last {f : FilePlans} {fuel : Nat} {keep : Nat → List (Nat × List HeapKnowledge.Candidate)}
    {fixed compare : Bool} {debugNode repeats : Nat} {observe : Option String} {counting located : Bool}
    {given : Option (Std.HashMap String Json)} {i : Nat} :
    Recandidated f (f.inferredSettle fuel keep fixed compare debugNode repeats observe counting located given i).state ∧
      (f.inferredSettle fuel keep fixed compare debugNode repeats observe counting located given i).last =
        (f.inferredSettle fuel keep fixed compare debugNode repeats observe counting located given i).state.inferredRun
          fuel compare debugNode repeats observe counting located
          (f.inferredSettle fuel keep fixed compare debugNode repeats observe counting located given i).given i := by
  unfold FilePlans.inferredSettle
  exact settleInferred_last Recandidated Recandidated.refl (fun _ _ _ => Recandidated.trans)
    (fun _ _ _ _ _ _ _ hn => inferredNextAll_recandidated hn) _ _ _ _ _ _

/-- An accepted inferred run is the pass's accepted run (proved). -/
theorem inferredRun_accepted {g : FilePlans} {fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {observe : Option String} {counting located : Bool} {given : Option (Std.HashMap String Json)} {i : Nat}
    (h : (g.inferredRun fuel compare debugNode repeats observe counting located given i).2.2 = none) :
    ∃ m, g.passMember fuel i compare debugNode repeats given observe counting = .ok m ∧ m.accepted = true := by
  unfold FilePlans.inferredRun at h
  cases hm : g.passMember fuel i compare debugNode repeats given observe counting with
  | ok m =>
    rw [hm] at h
    refine ⟨m, rfl, ?_⟩
    unfold MemberRun.accepted
    cases ho : m.outcome <;> simp_all
  | error r => rw [hm] at h; simp at h

/-- **A group `passGroupInferred` accepts has each member's last run
accepted** (proved): each member `j` has an accepted `passMember` run over
plans `Recandidated` from the group's. -/
theorem passGroupInferred_members {f : FilePlans} {fuel : Nat} {group : List Nat}
    {keep : Nat → List (Nat × List HeapKnowledge.Candidate)} {fixed compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool}
    {deps : List String}
    (h : (f.passGroupInferred fuel group keep fixed compare debugNode repeats given observe counting located).2.1 =
      .ok deps) :
    ∀ j ∈ group, ∃ f', Recandidated f f' ∧ MemberAccepted f' j := by
  let step := FilePlans.inferredStep fuel keep fixed compare debugNode repeats observe counting located
  let observe' := settlingObservation observe
  have key : ∀ (xs : List Nat) (acc : InferredAcc), Recandidated f acc.plans →
      (xs.foldl step acc).failed = none →
      acc.failed = none ∧ ∀ j ∈ xs, ∃ f' g', Recandidated f f' ∧ ∃ m,
        f'.passMember fuel j compare debugNode repeats g' observe' counting = .ok m ∧ m.accepted = true := by
    intro xs
    induction xs with
    | nil => intro acc _ h; exact ⟨h, fun _ hj => absurd hj List.not_mem_nil⟩
    | cons i rest ih =>
      intro acc hacc h
      obtain ⟨hq, hlast⟩ := inferredSettle_last (f := acc.plans) (fuel := fuel) (keep := keep) (fixed := fixed)
        (compare := compare) (debugNode := debugNode) (repeats := repeats) (observe := observe')
        (counting := counting) (located := located) (given := acc.given) (i := i)
      have hstep : Recandidated f (step acc i).plans := hacc.trans hq
      obtain ⟨h1, hrest⟩ := ih (step acc i) hstep h
      have h1' : (acc.failed.orElse fun _ =>
          (acc.plans.inferredSettle fuel keep fixed compare debugNode repeats observe' counting located acc.given i).last.2.2.map
            Thunk.get) = none := h1
      cases ha : acc.failed with
      | some _ => rw [ha] at h1'; simp [Option.orElse] at h1'
      | none =>
        rw [ha] at h1'
        simp only [Option.orElse] at h1'
        rw [hlast, Option.map_eq_none_iff] at h1'
        obtain ⟨m, hm, hacc'⟩ := inferredRun_accepted h1'
        refine ⟨rfl, fun j hj => ?_⟩
        rcases List.mem_cons.mp hj with rfl | hj
        · exact ⟨_, _, hstep, m, hm, hacc'⟩
        · exact hrest j hj
  have hfail : (group.foldl step ⟨f, given, [], none, 0, 0⟩).failed = none := by
    unfold FilePlans.passGroupInferred at h
    dsimp only at h
    revert h
    cases (group.foldl step ⟨f, given, [], none, 0, 0⟩).failed <;> simp
  intro j hj
  obtain ⟨-, hall⟩ := key group ⟨f, given, [], none, 0, 0⟩ (Recandidated.refl f) hfail
  obtain ⟨f', g', hr, m, hm, hacc⟩ := hall j hj
  exact ⟨f', hr, passMember_sound f' fuel compare debugNode repeats g' observe' counting j m hm hacc⟩

/-- **A group mode 8 accepts is safe** (proved, under `RunSound` and
`RunKeepsSummaries`, its plans over the file's store): by the given lines
(`passGroup`), or by the inferred route, each member's accepted run over
plans with other candidates, whose safety is the member's. -/
theorem passGroupMode8_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    {f : FilePlans} (hover : OverStore f) {infer : Bool} {force : List String}
    {keep : Nat → List (Nat × List HeapKnowledge.Candidate)} {i fuel : Nat} {compare : Bool}
    {debugNode repeats : Nat} {given : Option (Std.HashMap String Json)} {observe : Option String}
    {counting located : Bool} {deps : List String}
    (haccepted : (f.passGroupMode8 infer force keep fuel (f.fr.group i) compare debugNode repeats given observe
      counting located).2.1 = .ok deps) :
    PassUnitSafe f i := by
  unfold FilePlans.passGroupMode8 at haccepted
  cases infer with
  | false =>
    exact fun j hj => member_safe (hrun _) (hkeep _) hover (passGroupChecks _ _ _ _ _ _ _ _ _ _ _ haccepted j hj)
  | true =>
    intro j hj
    have ha := withFreshApart_recandidated f (force.contains "head-apart") (f.fr.group i)
    obtain ⟨f', hr, hm⟩ := passGroupInferred_members haccepted j hj
    have hr' := ha.trans hr
    exact hr'.memberSafe (member_safe (hrun _) (hkeep _) (hr'.overStore hover) hm)

/-- **The headline** (proved, under the graph-level hypotheses `RunSound`
and `RunKeepsSummaries`): when mode 8 prints a unit accepted, its plans are
those `fragmentPlans` gives with the given head facts (and, with `infer`,
the proposals inference recorded), the unit is selected and mode 8's check
(`passGroupMode8`) accepts its group, then every member of its group is
safe (`PassUnitSafe`). -/
theorem passUnit_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f : FilePlans} {i : Nat}
    {givenLines : Std.HashMap String Json} {infer : Bool} {keep : Nat → List (Nat × List HeapKnowledge.Candidate)}
    {fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool} {deps : List String}
    (hplans : fragmentPlans ast fileKey budget selection standIns force = .ok f)
    (_hselected : i ∈ f.fr.selected selection)
    (haccepted : ((f.withHeadFacts givenLines false infer).passGroupMode8 infer force keep fuel (f.fr.group i) compare
      debugNode repeats given observe counting located).2.1 = .ok deps) :
    PassUnitSafe (f.withHeadFacts givenLines false infer) i :=
  passGroupMode8_safe hrun hkeep (withHeadFacts_overStore (fragmentPlans_overStore hplans)) haccepted

end Verification.SourceClaimJson.PassUnit
