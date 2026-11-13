import Verification.Source.Claims.PassUnitWrapper

/-! # The single pass's unit theorem: what an accepted member run establishes

`passMember_sound` proves `PassMemberSound`: where `FilePlans.passMember`,
returns a run whose outcome is acceptance, the member is `MemberAccepted`,
at every value of every argument, the observation asked included. The proof follows the function's own steps: the
plan through `certify`, the request's own conditions, the qualified run or
each code request's run in order (`codesInOrder_accepted`) and the main
graph's route (direct, the regional fallback, the fallback then the stated
regions), each step's refusals excluded by the outcome.
docs/SINGLE-PASS-THEOREM.md, section 3. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore


/-- A pure `Except` value is the value it returns. -/
theorem except_pure_ok {ε α : Type} {a b : α} (h : (pure a : Except ε α) = .ok b) : b = a := by
  cases h; rfl

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **The codes in order, every run accepted** (proved): where each step
the wrapper takes is `CodeRunAccepted` when its outcome is acceptance,
`codesInOrder` returning only accepted runs threads `CodesAccepted` and
returns the table extended by every code's entry. -/
theorem codesInOrder_accepted {G : NormalGraph ι} {I : PositiveCertificates.InstanceImageCheck G}
    (r : SourceRequest σ ι)
    (step : List (CodeEntry ι) → CertificateProducer.Answered G → CodeRequest ι × Nat →
      CodeRun ι (CertificateProducer.Answered G))
    (hstep : ∀ table a x, (step table a x).outcome = .accepted →
      CodeRunAccepted G I r table x.1 x.2 a (step table a x).answers) :
    ∀ (qs : List (CodeRequest ι × Nat)) table a runs t a',
      codesInOrder (·.1.entry) step table a qs = (runs, t, a') → (∀ c ∈ runs, c.outcome = .accepted) →
      CodesAccepted G I r table qs a a' ∧ t = table ++ qs.map (·.1.entry) := by
  intro qs
  induction qs with
  | nil =>
    intro table a runs t a' h _
    simp only [codesInOrder, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact ⟨rfl, by simp⟩
  | cons x rest ih =>
    intro table a runs t a' h hall
    obtain ⟨q, ci⟩ := x
    unfold codesInOrder at h
    generalize hc : step table a (q, ci) = c at h
    cases ho : c.outcome with
    | accepted =>
      simp only [ho] at h
      generalize hrec : codesInOrder (·.1.entry) step (table ++ [q.entry]) c.answers rest = R at h
      obtain ⟨cs, t', a''⟩ := R
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hca, ht⟩ := ih _ _ _ _ _ hrec (fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))
      refine ⟨⟨c.answers, ?_, hca⟩, by simp [ht]⟩
      have := hstep table a (q, ci) (by rw [hc]; exact ho)
      rwa [hc] at this
    | _ =>
      simp only [ho, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      have := hall c (List.mem_singleton_self c)
      rw [ho] at this; cases this
end

/-- The read summaries' check this proof names is the wrapper's. -/
theorem summariesChecked_eq {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι)
    (s : List (ProgramCertificates.ReadSummary ι)) :
    summariesChecked r s = SourceClaimJson.summariesChecked r s := rfl

/-- A run's outcome read as a refusal is acceptance only where the run
accepted. -/
theorem asRefusal_accepted {ι : Type} {o : SinglePass.Outcome ι} (h : o.asRefusal = .accepted) :
    o = .accepted := by
  cases o <;> simp_all [SinglePass.Outcome.asRefusal]

/-- **What an accepted member run establishes** (proved): `PassMemberSound`,
the member's plan, conditions, code runs and main runs as `MemberAccepted`
states them. -/
theorem passMember_sound : PassMemberSound := by
  intro f fuel compare debugNode repeats given observe counting j m h hacc
  unfold FilePlans.passMember at h
  extract_lets G I answers reference line tracing at h
  obtain ⟨plan, hplan, h⟩ := except_bind_ok h
  obtain ⟨cp, hcert, h⟩ := except_bind_ok h
  split at h
  rename_i name pos r
  have hplanAt : PlanAt f j name pos r := by
    unfold PlanAt
    cases hp : f.plans[j]? with
    | none => rw [hp] at hplan; cases hplan
    | some x =>
      rw [hp] at hplan; simp only [Option.getD_some] at hplan; subst hplan
      cases plan with
      | graph n' p' r' =>
        simp only [FunctionPlan.certify, pure, Except.pure, Except.ok.injEq, CertifiedPlan.graph.injEq] at hcert
        obtain ⟨rfl, rfl, rfl⟩ := hcert; rfl
  extract_lets bounded bound labels pool main givenImplies givenArgs givenInputs G' I' pool' observed regionalOf regional fallback claimAt place at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp [MemberRun.accepted, MemberRun.before] at hacc
  rename_i hdecl
  have hdecl' : declaredEffect r = true := by
    simpa only [declaredEffect, Bool.not_eq_true', Bool.not_eq_false] using hdecl
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp [MemberRun.accepted, MemberRun.before] at hacc
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp [MemberRun.accepted, MemberRun.before] at hacc
  rename_i hens
  obtain ⟨en, hen, h⟩ := except_bind_ok h
  split at h
  rename_i e next
  split at h
  rename_i rendered next' hrend
  split at h
  · rename_i q hq
    split at h
    · have := except_pure_ok h; subst this; simp [MemberRun.accepted, MemberRun.before] at hacc
    rename_i hfp
    split at h
    · have := except_pure_ok h; subst this; simp [MemberRun.accepted, MemberRun.before] at hacc
    rename_i hreg
    split at h
    · have := except_pure_ok h; subst this; simp [MemberRun.accepted, MemberRun.before] at hacc
    rename_i hcodes
    split at h
    rename_i o counts after tr hrun
    extract_lets sums sumsOk obligations outcome at h
    have := except_pure_ok h; subst this
    simp only [MemberRun.accepted, outcome] at hacc
    obtain ⟨ho, hsok, hobl⟩ : o = .accepted ∧ sumsOk = true ∧ obligations.accepted = true := by
      cases o with
      | accepted =>
        refine ⟨rfl, ?_⟩
        cases hs : sumsOk <;> cases hb : obligations.accepted <;> simp only [hs, hb] at hacc <;> simp at hacc
        exact ⟨rfl, rfl⟩
      | _ => simp at hacc
    subst ho
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, Bool.not_eq_false', beq_eq_false_iff_ne,
      Bool.not_eq_true, not_or, ne_eq, Decidable.not_not] at hfp
    obtain ⟨⟨hfp, hot⟩, hfr⟩ := hfp
    simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hreg
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, Decidable.not_not] at hcodes
    simp only [hq, Option.isSome_some, Bool.and_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq,
      Decidable.not_not] at hens
    simp only [CertificateProducer.timed] at hrun
    refine MemberAccepted.qualified name pos r q
      { pool := pool', fuel, P := r.program, claims := r.claims, start := r.start, inputs := r.inputs,
        goal := r.goal, assertions := r.assertions, cuts := r.cuts, candidates := r.candidates,
        entryIndices := r.entryIndices, suggestions := [], known := e ++ rendered, codes := GraphCode.admits [],
        aliases := r.aliases, passChecker := .qualified q.body q.ordinary,
        answers := { summaries := next'.summaries, summaryAnswers := next'.summaryAnswers },
        reference := #[], debugNode, bound := none, givenImplies := givenImplies, givenArgs := givenArgs,
        ensures := r.ensures, givenInputs := givenInputs, entrySeparation := r.entrySeparation, observe := none,
        tracing := false, observeEntry := false, regional := none }
      _ after hplanAt hq hdecl' hfp hot hfr hens hreg hcodes
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl ⟨counts, tr, ?_⟩ hsok
    unfold RunCall.result
    dsimp only
    exact hrun
  · rename_i hq
    extract_lets codeStep at h
    split at h
    rename_i codeRuns table sumsAnswers hcio
    split at h
    · rename_i c hc
      have := except_pure_ok h; subst this
      have := List.find?_some hc
      simp only [MemberRun.accepted] at hacc
      revert this hacc; cases c.outcome <;> simp
    rename_i hfind
    have hall : ∀ c ∈ codeRuns, c.outcome = .accepted := by
      intro c hc
      have := List.find?_eq_none.mp (Option.eq_none_iff_forall_ne_some.mpr hfind) c hc
      revert this; cases c.outcome <;> simp
    have hstep : ∀ table a x, (codeStep table a x).outcome = .accepted →
        CodeRunAccepted G I r table x.1 x.2 a (codeStep table a x).answers := by
      intro table a x hacc'
      obtain ⟨q, ci⟩ := x
      generalize hcs : codeStep table a (q, ci) = cr at hacc' ⊢
      unfold codeStep at hcs
      split at hcs
      rename_i q ci heqx
      cases heqx
      extract_lets refuse hints rq eff conditions codeBound' codePool codeGiven codeImplies codeArgs at hcs
      split at hcs
      · subst hcs; simp [refuse] at hacc'
      rename_i hcond
      split at hcs
      · subst hcs; simp [refuse] at hacc'
      rename_i hasync
      split at hcs
      rename_i o cnt a' tr hrun
      generalize hor : o.asRefusal = O at hcs
      cases O <;> subst hcs <;> (try simp at hacc')
      have ho : o = .accepted := by cases o <;> simp [SinglePass.Outcome.asRefusal] at hor ⊢
      subst ho
      have hcond' : conditions = true := by simpa only [Bool.not_eq_true', Bool.not_eq_false] using hcond
      refine ⟨hcond',
        by simpa only [Bool.not_eq_true', Bool.not_eq_false] using hasync,
        { pool := codePool, fuel, P := rq.program, claims := rq.claims, start := rq.start, inputs := rq.inputs,
          goal := q.entry.goal, assertions := hints.requirements, cuts := hints.cuts, candidates := hints.candidates,
          entryIndices := rq.entryIndices, suggestions := [], known := e ++ rendered,
          codes := GraphCode.admits table, aliases := r.aliases, passChecker := .ordinary, answers := a,
          reference := #[], debugNode := 1000000000, bound := codeBound', givenImplies := codeImplies,
          givenArgs := codeArgs, ensures := [], givenInputs := #[], entrySeparation := {}, observe := none,
          tracing := false, observeEntry := false, regional := none },
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨cnt, tr, ?_⟩⟩
      unfold RunCall.result
      dsimp only
      exact hrun
    obtain ⟨hcodesAcc, htable⟩ := codesInOrder_accepted (I := I) r codeStep hstep _ _ _ _ _ _ hcio hall
    have htable' : table = r.codes.map (·.entry) := by
      rw [htable, List.nil_append]
      calc r.codes.zipIdx.map (·.1.entry) = (r.codes.zipIdx.map (·.1)).map (·.entry) := by
            rw [List.map_map]; rfl
        _ = r.codes.map (·.entry) := by rw [List.zipIdx_map_fst]
    extract_lets codes walk jp at h
    split at h
    · have := except_pure_ok h; subst this; simp [MemberRun.accepted] at hacc
    obtain ⟨u, hfor, h⟩ := except_bind_ok h
    have hq' : r.qualification = none := Option.eq_none_iff_forall_ne_some.mpr fun q h => hq q h
    have hjp : (∀ Φ regions, r.regional = some (Φ, regions) → r.async = false ∧ r.fresh = false ∧
          GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions = true) →
        ∀ m', jp () = .ok m' → m'.accepted = true → MemberAccepted f j := by
      intro hregs m' h hacc
      unfold jp at h
      split at h
      rename_i o₀ counts₀ after₀ trace₀ hwalk
      extract_lets mainRun counts trace obligations sumsOk o₁ o₂ checked jp₂ at h
      have hj : jp₂ () = .ok m' := by
        generalize o₂ = O at h
        split at h
        · split at h
          · exfalso
            have := except_pure_ok h; subst this
            simp [checked, MemberRun.accepted] at hacc
          · exact h
        · exact h
      unfold jp₂ at hj
      -- The observation rerun's outcome replaces a refusal only where it is
      -- no acceptance: an accepted outcome is the main run's own.
      have h21 : o₂ = .accepted → o₁ = .accepted := by
        intro hO; unfold o₂ at hO
        generalize o₁ = O at hO ⊢
        generalize observed = Ob at hO
        cases O <;> cases Ob <;> simp only at hO ⊢
        all_goals first
          | exact hO
          | (split at hO
             · cases hO
             · split at hO
               · cases hO
               · rename_i hne; exact (hne hO).elim)
      generalize hO : o₂ = O at hj
      cases O <;> (have := except_pure_ok hj; subst this) <;>
        (try simp only [checked, MemberRun.accepted] at hacc) <;> (try simp at hacc)
      have h1 : o₁ = .accepted := h21 hO
      obtain ⟨hmo, hsok, hobl⟩ : mainRun.outcome = .accepted ∧ sumsOk = true ∧ obligations.accepted = true := by
        unfold o₁ at h1
        generalize mainRun.outcome = O at h1 ⊢
        cases O <;> simp only [reduceCtorEq] at h1
        refine ⟨rfl, ?_⟩
        cases hs : sumsOk <;> cases hb : obligations.accepted <;> simp only [hs, hb] at h1 <;> simp at h1
        exact ⟨rfl, rfl⟩
      have hsok' : SourceClaimJson.summariesChecked r mainRun.after.summaries.toList = true ∧
          mainRun.fallbackAfter.all (fun a => SourceClaimJson.summariesChecked r a.summaries.toList) = true := by
        simpa only [sumsOk, Bool.and_eq_true] using hsok
      have hcodesEq : codes = GraphCode.admits (r.codes.map (·.entry)) := by simp only [codes, htable']
      have mk : ∀ bnd rg, ∃ c : RunCall G I,
          MainCall r c (GraphCode.admits (r.codes.map (·.entry))) .ordinary sumsAnswers ∧
          c.bound = bnd ∧ c.regional = rg ∧ c.result = walk bnd rg := by
        intro bnd rg
        refine ⟨
          { pool := pool, fuel := fuel, P := r.program, claims := r.claims, start := r.start, inputs := r.inputs,
            goal := r.goal, assertions := r.assertions, cuts := r.cuts, candidates := r.candidates,
            entryIndices := r.entryIndices, suggestions := [], known := e ++ rendered, codes := codes,
            aliases := r.aliases, passChecker := .ordinary, answers := sumsAnswers, reference := reference, debugNode := debugNode,
            bound := bnd, givenImplies := givenImplies, givenArgs := givenArgs, ensures := r.ensures,
            givenInputs := givenInputs,
            entrySeparation := r.entrySeparation, observe := observed, tracing := tracing, observeEntry := false,
            regional := rg },
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcodesEq, rfl, rfl, rfl, rfl⟩, rfl, rfl,
          by simp only [RunCall.result, walk]⟩
      have hrof : ∀ k Φ R ex, regionOf (some (regionalOf k Φ R ex)) = some (Φ, R, ex) := by
        intro k Φ R ex; simp only [regionOf, regionalOf, Option.map_some]
      have hspec : regionOf regional = regionalSpec r := by
        simp only [regional, regionalSpec]
        cases r.regional with
        | none => rfl
        | some p => obtain ⟨Φ, R⟩ := p; exact hrof _ _ _ _
      have hrun0 : walk bound regional = (o₀, counts₀, after₀, trace₀) := hwalk
      refine MemberAccepted.ordinary name pos r _ sumsAnswers hplanAt hq' hdecl' hregs hcodesAcc ?_
      have hs1 := hsok'.1
      have hs2 := hsok'.2
      have hmo' := hmo
      unfold mainRun at hs1 hs2 hmo'
      revert hs1 hs2 hmo'
      split
      · rename_i l
        split
        · rename_i hfr
          have hfr' : r.fresh = false := by simpa using hfr
          obtain ⟨c₁, hm₁, hb₁, hrg₁, hres₁⟩ := mk none (some fallback)
          have hreg₁ : regionOf c₁.regional = some (r.footprint, [], r.onThrow) := by
            rw [hrg₁]; exact hrof _ _ _ _
          generalize hw1 : walk none (some fallback) = W1
          obtain ⟨o1, n1, a1, t1⟩ := W1
          cases o1 with
          | accepted =>
            have hacc₁ : c₁.Accepts a1 := ⟨n1, t1, by rw [hres₁, hw1]⟩
            generalize hR : regional = R at hspec ⊢
            cases R with
            | some rg =>
              intro hs1 hs2 hmo'
              dsimp only at hs1 hs2 hmo'
              have ho2 := asRefusal_accepted hmo'
              obtain ⟨c₂, hm₂, hb₂, hrg₂, hres₂⟩ := mk none (some rg)
              have hw2 : walk none (some rg) = (.accepted, (walk none (some rg)).2.1, (walk none (some rg)).2.2.1,
                  (walk none (some rg)).2.2.2) := Prod.ext ho2 rfl
              refine MainAccepted.fallback c₁ a1 hfr' hm₁ hb₁ hreg₁ hacc₁ ?_
                (Or.inr ⟨c₂, _, hm₂, hb₂, by rw [hrg₂, ← hspec], ⟨_, _, by rw [hres₂]; exact hw2⟩,
                  by rw [summariesChecked_eq]; exact hs1⟩)
              rw [summariesChecked_eq]; simpa only [Option.all_some] using hs2
            | none =>
              intro hs1 _ _
              dsimp only at hs1
              refine MainAccepted.fallback c₁ a1 hfr' hm₁ hb₁ hreg₁ hacc₁ hs1 (Or.inl ?_)
              cases h' : r.regional with
              | none => rfl
              | some p => simp only [regional, h', Option.map_some, reduceCtorEq] at hR
          | refused w => intro _ _ hmo'; simp at hmo'
          | _ => intro _ _ hmo'; simp [SinglePass.Outcome.asRefusal] at hmo'
        · intro _ _ hmo'; simp [SinglePass.Outcome.asRefusal] at hmo'
      · rename_i o₀' hne
        intro hs1 _ hmo'
        dsimp only at hs1 hmo'
        have ho := asRefusal_accepted hmo'
        obtain ⟨c, hm, hb, hrg, hres⟩ := mk bound regional
        exact MainAccepted.direct c after₀ hm (hb.trans rfl) (by rw [hrg]; exact hspec)
          ⟨counts₀, trace₀, by rw [hres, hrun0, ho]⟩ hs1
    split at h
    · rename_i Φ regions hr
      split at h
      · have := except_pure_ok h; subst this; simp [MemberRun.accepted] at hacc
      · rename_i hc
        refine hjp (fun Φ' regions' hr' => ?_) m h hacc
        rw [hr] at hr'; cases hr'
        simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_false', and_assoc] using hc
    · rename_i hr
      exact hjp (fun Φ' regions' hr' => absurd hr' (hr Φ' regions')) m h hacc
/-- **H3** (proved): `passGroup` accepting a group makes every member
`MemberAccepted`, at every value of every argument. -/
theorem passGroupChecks : PassGroupChecks := passGroupChecks_of_sound passMember_sound

end Verification.SourceClaimJson.PassUnit
