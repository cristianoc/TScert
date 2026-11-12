import Verification.Programs.TolerantFramesNodeYields

/-! # Tolerant frames: a promise call's kept yields

`run` keeps the yields of a call at a promise signature where
`SinglePass.checkedYields`' promise branch accepts them
(`PromiseCalls.promiseYields`); `PromiseCalls.promiseCall_sound` proves
them of the call's value from the derivation's tree check
(`checkTreeUsing`). The pass reads that derivation's tree only through
`SinglePass.derivChecked`: the tree check, or `PromiseCalls.requiresTree`
at the step's facts. Proved:

- `promiseCall_yields_local`: `promiseCall_sound`'s typed yields from the
  call's local rule at any `allowRequires` and its operands' trees: the
  run is the promise signature's, which states no precondition; the proof
  is `promiseCall_sound`'s with no output facts;
- `promiseCall_yields_checked`: a derivation stating a promise
  (`promiseOf`) that `derivChecked` accepts, claimed at the node's
  context, term and type, gives values of the type meeting the yields
  `promiseYields` accepts, at every environment the context types. -/
namespace Verification.PromiseCalls
open ProgramTyping ProgramCertificates PositiveGraphs PositiveRules HeapObservations BranchRefinement
open CallEffects (Effect Arrow Contract)
open PositiveCertificates (InstanceImageCheck)

section
variable {ι : Type} [DecidableEq ι]

/-- **A promise call's yields from its local rule** (`promiseCall_sound`'s
proof, its claim's type dropped): a call node stating a promise, its local
rule at any `allowRequires` and its operands' trees accepted, its value
meets the claim's type and the yields `promiseYields` accepts. -/
theorem promiseCall_yields_local {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ : List (Ty ι)}
    {t : Tm} {A : Ty ι} {r0 : Effect} {ps : List (Evidence ι)} {allow : Bool}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {effect a T} {ys : List (Yield ι)}
    (hp : promiseOf G (.node ⟨Γ, t, A⟩ (.app r0) ps) = some (effect, a, T))
    (hlocal : LocalUsing G images ⟨Γ, t, A⟩ (.app r0) (ps.map claim) codes (sums := sums) (allowRequires := allow))
    (htrees : ∀ e ∈ ps, checkTreeUsing G images e codes sums = true) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums)
    (hy : promiseYields G A effect a T ys = true)
    {ρ n W h} (he : EnvOk G Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (fun m U u => meaning G A m U u ∧ YieldsOk G ys ρ m U u) (fun _ _ => True) n W h
      (instantiate 0 ρ t) := by
  simp only [promiseOf] at hp
  split at hp
  case isFalse => contradiction
  rename_i hvals
  simp only [List.all_eq_true, Bool.and_eq_true] at hvals
  have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
    intro p hm
    obtain ⟨e, heq, rfl⟩ := List.mem_map.mp hm
    exact checkTreeUsing_sound e (htrees e heq) hcodes hsums
  have hvals' : ∀ p ∈ ps.map claim, ExpressionEffects.valueTerm p.term = true ∧
      checkScope p.context.length p.term = true := by
    intro p hm
    obtain ⟨e, heq, rfl⟩ := List.mem_map.mp hm
    exact hvals e heq
  generalize ps.map claim = qs at hp hlocal typed hvals'
  split at hp
  case h_2 => contradiction
  rename_i f rv args jf jr jas
  obtain ⟨hΓf, htf, hΓr, htr, hargs, hundef, hcontexts, hL⟩ := hlocal
  split at hp
  case h_2 => contradiction
  rename_i L S hF
  obtain ⟨s, hs, hsome⟩ := List.exists_of_findSome?_eq_some hp
  split at hsome
  case isFalse => contradiction
  rename_i hsig
  obtain ⟨hrecv, hargsig, hreq, hpre⟩ := hsig
  have context : ∀ p ∈ jf::jr::jas, p.context = Γ := by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact hΓf
    · exact hΓr
    · exact hcontexts p hp
  have typed' : ∀ p ∈ jf::jr::jas, HasTyUsing G images Γ p.term p.type := by
    intro p hp
    simpa only [context p hp] using typed p hp
  have values : ∀ p ∈ jf::jr::jas, isVal (instantiate 0 ρ p.term) = true := by
    intro p hp
    exact ExpressionEffects.valueTerm_instantiate (hvals' p hp).1 (hvals' p hp).2
      (by simpa [context p hp] using he)
  cases n with
  | zero => trivial
  | succ n =>
    have member : ∀ p ∈ jf::jr::jas, meaning G p.type (n+1) W (instantiate 0 ρ p.term) := by
      intro p hp
      exact safe_value_mem (values p hp) ((typed' p hp).sound _ _ h ρ he hw hh)
    have hf := ((represents_raw hF (n+1) W _) (member jf (by simp))).1
    have hpw := hf.2 _ (List.mem_map_of_mem hs)
    simp only [CallEffects.Arrow.map, CallEffects.Contract.map] at hpw
    have hArgs := ExpressionEffects.argument_values (ps := jas)
      (fun p hp => typed' p (by simp [hp])) (fun p hp => values p (by simp [hp])) he hw hh
    have actual : (jas.take args.length).map (fun p => instantiate 0 ρ p.term)
        = args.map (instantiate 0 ρ) := by
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (instantiate 0 ρ)) hargs
    have ha : ArgsShort (jas.map (fun p => meaning G p.type)) (n+1) W
        (args.map (instantiate 0 ρ)) := by
      rw [← actual]
      apply ArgsShort_of_pad (pad := (jas.drop args.length).map (fun p => instantiate 0 ρ p.term))
      · intro v hv'
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv'
        simp [hundef p hp, instantiate]
      · simpa [← List.map_append, List.take_append_drop] using hArgs
    have hvs : CallArguments.Values (args.map (instantiate 0 ρ)) := by
      rw [← actual]
      intro v hv'
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv'
      exact values p (by simp [List.mem_of_mem_take hp])
    have hr := member jr (by simp)
    have hrval := values jr (by simp)
    rw [hargsig, hrecv] at hpw
    have hs' := CallEffects.call_safe
      (P := ArgsShort (jas.map (fun p => meaning G p.type)))
      (Adm.of_transfer (fun ha j hj U hx => ArgsShort_transfer (fun T hm => by
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type) ha j hj U hx))
      (meaning_adm G jr.type) (by simpa [List.map_map, Function.comp_def] using hpw) hr hrval hvs ha hw hh
      (CallEffects.Effect.requires_none hreq hpre _ _ _)
    have hterm : instantiate 0 ρ (.invoke f rv args) = .invoke (instantiate 0 ρ jf.term)
        (instantiate 0 ρ jr.term) (args.map (instantiate 0 ρ)) := by
      simp [instantiate, instantiateArgs_eq_map, htf, htr]
    rw [hterm]
    refine consequence (fun m U u hu => ?_) (fun _ _ _ => trivial) hs'
    split at hsome
    · rename_i p heff
      split at hsome
      · rename_i a' harg
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨he', rfl, hT⟩ := hsome
        subst he' hT
        have hpromised : s.effect.promised (args.map (instantiate 0 ρ)) = ρ a' := by
          simp [CallEffects.Effect.promised, heff, CallEffects.TypePromise.param,
            List.getD_eq_getElem?_getD, harg, instantiate]
        rw [hpromised] at hu
        simp only [CallEffects.Effect.result, heff, CallEffects.TypePromise.result] at hu
        simp only [promiseYields, heff, Bool.and_eq_true, List.all_eq_true] at hy
        obtain ⟨⟨hbt, hbf⟩, hall⟩ := hy
        refine ⟨?_, fun y hym hcond _ => ?_⟩
        · rcases hu with ⟨rfl, _⟩ | rfl
          · exact booleanMember_sound (q := true) hbt m U
          · exact booleanMember_sound (q := false) hbf m U
        · obtain ⟨⟨htarget, hw⟩, hc⟩ := hall y hym
          rw [beq_iff_eq.mp htarget]
          rcases hu with ⟨_, hT⟩ | rfl
          · exact meaning_within hw hT
          · exact absurd (hcond hc) (by simp)
      · contradiction
    · rename_i p heff
      split at hsome
      · rename_i a' harg
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨he', rfl, hT⟩ := hsome
        subst he' hT
        have hpromised : s.effect.promised (args.map (instantiate 0 ρ)) = ρ a' := by
          simp [CallEffects.Effect.promised, heff, CallEffects.TypePromise.param,
            List.getD_eq_getElem?_getD, harg, instantiate]
        rw [hpromised] at hu
        simp only [CallEffects.Effect.result, heff, CallEffects.TypePromise.result] at hu
        simp only [promiseYields, heff, Bool.and_eq_true, List.all_eq_true] at hy
        obtain ⟨hundefA, hall⟩ := hy
        obtain ⟨rfl, hT⟩ := hu
        refine ⟨admitsUndef_sound hundefA m U, fun y hym _ _ => ?_⟩
        obtain ⟨⟨htarget, hw⟩, _⟩ := hall y hym
        rw [beq_iff_eq.mp htarget]
        exact meaning_within hw hT
      · contradiction
    · contradiction

theorem promiseOf_app {G : NormalGraph ι} {e : Evidence ι} {x : Effect × Nat × Ty ι}
    (hp : promiseOf G e = some x) : ∃ j r ps, e = .node j (.app r) ps := by
  obtain ⟨j, r, ps⟩ := e
  cases r <;> first | exact ⟨_, _, _, rfl⟩ | (simp only [promiseOf] at hp; contradiction)

/-- **A checked promise derivation's yields** (`derivChecked`'s tree check
or `requiresTree` at the step's facts): a derivation stating a promise,
claimed at the context `Γ`, the term `t` and the type `A`, accepted by
either, gives values of `A` meeting the yields `promiseYields` accepts, at
every environment `Γ` types. -/
theorem promiseCall_yields_checked {G : NormalGraph ι} {images : InstanceImageCheck G} {e : Evidence ι}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {k : HeapKnowledge.Knowledge} {effect a T}
    {ys : List (Yield ι)} {Γ : List (Ty ι)} {t : Tm} {A : Ty ι}
    (hp : promiseOf G e = some (effect, a, T))
    (hc : checkTreeUsing G images e codes sums = true ∨ requiresTree G images k codes sums e = true)
    (hctx : (claim e).context = Γ) (hterm : (claim e).term = t) (hty : (claim e).type = A)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (hy : promiseYields G A effect a T ys = true)
    {ρ n W h} (he : EnvOk G Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (fun m U u => meaning G A m U u ∧ YieldsOk G ys ρ m U u) (fun _ _ => True) n W h
      (instantiate 0 ρ t) := by
  obtain ⟨⟨Γ', t', A'⟩, r0, ps, rfl⟩ := promiseOf_app hp
  simp only [claim] at hctx hterm hty
  subst hctx hterm hty
  rcases hc with hc | hc
  · simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    exact promiseCall_yields_local hp hc.1 (fun e he' => hc.2 ⟨e, he'⟩ (List.mem_attach _ _)) hcodes hsums hy he hw hh
  · simp only [requiresTree, requiresApp, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    exact promiseCall_yields_local hp hc.1.1.2 (fun e he' => hc.1.2 ⟨e, he'⟩ (List.mem_attach _ _)) hcodes hsums hy
      he hw hh

end

end Verification.PromiseCalls
