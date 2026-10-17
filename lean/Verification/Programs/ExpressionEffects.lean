import Verification.Programs.HeapExpressionRules

/-! Definition-side effect checks over lowered expressions. Safety comes from
ordinary evidence; this layer establishes the additional heap postcondition. -/
namespace Verification.ExpressionEffects
open ProgramTyping ProgramCertificates PositiveGraphs PositiveRules HeapObservations

/-- Operands already evaluated by source lowering. -/
def valueTerm : Tm → Bool
  | .var _ => true
  | t => isVal t

theorem valueTerm_instantiate {G : NormalGraph ι} {Γ t ρ n W}
    (hv : valueTerm t = true) (hc : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) : isVal (instantiate 0 ρ t) = true := by
  cases t <;> simp_all [valueTerm, isVal, instantiate, checkScope]
  case objAt fs code oid => cases code <;> rfl
  case var i =>
    exact (meaning_value (he.2 i Γ[i] (List.getElem?_eq_some_iff.mpr ⟨hc, rfl⟩))).1

private theorem operand_instantiate {G : NormalGraph ι} {Γ t ρ n W} {d : Nat}
    (ho : Purity.operandTerm t = true) (hc : checkScope (Γ.length + d) t = true)
    (he : EnvOk G Γ ρ n W) : Purity.operandTerm (instantiate d ρ t) = true := by
  cases t
  case var i =>
    simp only [instantiate]
    split
    · rfl
    · have hi : i - d < Γ.length := by simp [checkScope] at hc; omega
      have hv := (meaning_value (he.2 (i-d) Γ[i-d] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))).1
      cases h : ρ (i-d) <;> simp_all [Purity.operandTerm, isVal]
  case objAt fs code oid => cases code <;> simp [instantiate, Purity.operandTerm, isVal]
  all_goals simp_all [Purity.operandTerm, isVal, instantiate]

/-- Substituting the environment's values for the free slots keeps an
inspection: a slot becomes the value it holds. -/
theorem inspect_instantiate {G : NormalGraph ι} {Γ t ρ n W} {d : Nat}
    (hp : Purity.inspectTerm t = true) (hc : checkScope (Γ.length + d) t = true)
    (he : EnvOk G Γ ρ n W) : Purity.inspectTerm (instantiate d ρ t) = true := by
  induction t using Tm.induct generalizing d
  case var i =>
    simp only [instantiate]
    split
    · rfl
    · have hi : i - d < Γ.length := by simp [checkScope] at hc; omega
      exact Purity.inspect_value
        (meaning_value (he.2 (i-d) Γ[i-d] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))).1
  all_goals
    simp only [Purity.inspectTerm, instantiate, instantiateArgs_eq_map, List.all_eq_true,
      List.mem_map, Bool.and_eq_true, checkScope, checkScopes_iff] at hp hc ⊢
  all_goals first
    | (rintro _ ⟨x, hx, rfl⟩; exact operand_instantiate (hp x hx) (hc.2 x hx) he)
    | (rintro _ ⟨x, hx, rfl⟩; exact operand_instantiate (hp x hx) (hc x hx) he)
    | (simp [isVal] at hp ⊢; done)
    | (simp_all [Nat.add_assoc]; done)

/-- An inspection preserves the input heap on normal return: every step keeps
the heap a prefix, reading from a heap that holds values, which every heap
meeting an admissible world does (`heap_values`). Safety is supplied
separately. -/
theorem inspect_safe {T : Fam} {initial : Heap} : ∀ {n W h t},
    initial.IsPrefix h → Purity.inspectTerm t = true → WorldAdm W → HeapOk n W h →
    Safe Ξ T n W h t →
    SafePost Ξ T ((CallEffects.Effect.ofFootprint .empty).post initial) n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hpre hp hw hh hs
    rcases hs with (⟨hv, ht⟩ | hth) | ⟨U, h', t', hx, hu, step, hh', hs⟩
    · exact .inl (.inl ⟨hv, ht, Footprints.Closed.holds_empty.mpr hpre⟩)
    · exact .inl (.inr hth)
    · obtain ⟨hprefix, hp'⟩ := Purity.inspect_step step hp (HeapExpressionRules.heap_values hw hh)
      exact .inr ⟨U, h', t', hx, hu, step, hh', ih (hpre.trans hprefix) hp' hu hh' hs⟩

/-- Reads, tests, arithmetic and allocations whose initializers are evaluated.
Invocation requires a separate qualified-call derivation. -/
def check (_G : NormalGraph ι) (_Γ : List (Ty ι)) (t : Tm) : Bool :=
  Purity.inspectTerm t

theorem sound {G : NormalGraph ι} {Γ t A ρ n W h}
    (hc : check G Γ t = true) (hscope : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : Safe (excOf G) (meaning G A) n W h (instantiate 0 ρ t)) :
    SafePost (excOf G) (meaning G A) ((CallEffects.Effect.ofFootprint .empty).post h)
      n W h (instantiate 0 ρ t) :=
  inspect_safe (List.prefix_refl h) (inspect_instantiate (d := 0) hc hscope he) hw hh hs

/-- Invocation consumes the selected signature's effect. All actual evaluation
has already been lowered to earlier graph nodes; omitted arguments are the
ordinary evidence's explicit `undefined` premises. Subsumption may retain the
postcondition while changing the result type. -/
def selectedCallPreserves : Evidence ι → Bool
  | .node _ (.app e) ps =>
      e == .ofFootprint .empty && ps.all fun p => valueTerm (claim p).term &&
        checkScope (claim p).context.length (claim p).term
  | .node _ (.sub _) [p] => selectedCallPreserves p
  | _ => false

theorem argument_values [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {Γ : List (Ty ι)}
    {ps : List (Sequent ι)} {ρ n W h}
    (ht : ∀ p ∈ ps, HasTyUsing G images Γ p.term p.type)
    (hv : ∀ p ∈ ps, isVal (instantiate 0 ρ p.term) = true)
    (he : EnvOk G Γ ρ (n+1) W) (hw : WorldAdm W) (hh : HeapOk (n+1) W h) :
    ArgsT (ps.map (fun p => meaning G p.type)) (n+1) W (ps.map (fun p => instantiate 0 ρ p.term)) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨safe_value_mem (hv p (by simp)) ((ht p (by simp)).sound _ _ h ρ he hw hh),
      ih (fun p hp => ht p (by simp [hp])) (fun p hp => hv p (by simp [hp]))⟩

private theorem call_local_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {ps : List (Sequent ι)} {codes : CodeEntry ι → Bool}
    (hl : LocalUsing G images j (.app (.ofFootprint .empty)) ps codes)
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hv : ∀ p ∈ ps, valueTerm p.term = true ∧ checkScope p.context.length p.term = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type) ((CallEffects.Effect.ofFootprint .empty).post h)
      n W h (instantiate 0 ρ j.term) := by
  rcases j with ⟨Γ,t,A⟩
  -- The rule admits only a call with a callee and a receiver premise.
  cases t <;> try exact (hl : False).elim
  rename_i f r args
  rcases ps with _ | ⟨jf, _ | ⟨jr, jas⟩⟩
  · exact (hl : False).elim
  · exact (hl : False).elim
  obtain ⟨hΓf, htf, hΓr, htr, hargs, hundef, hcontexts, hL⟩ := hl
  have context : ∀ p ∈ jf::jr::jas, p.context = Γ := by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact hΓf
    · exact hΓr
    · exact hcontexts p hp
  have typed : ∀ p ∈ jf::jr::jas, HasTyUsing G images Γ p.term p.type := by
    intro p hp
    simpa only [context p hp] using ht p hp
  have values : ∀ p ∈ jf::jr::jas, isVal (instantiate 0 ρ p.term) = true := by
    intro p hp
    exact valueTerm_instantiate (hv p hp).1 (hv p hp).2 (by simpa [context p hp] using he)
  cases n with
  | zero => trivial
  | succ n =>
    have member : ∀ p ∈ jf::jr::jas, meaning G p.type (n+1) W (instantiate 0 ρ p.term) := by
      intro p hp
      exact safe_value_mem (values p hp) ((typed p hp).sound _ _ h ρ he hw hh)
    split at hL
    · rename_i L S hF
      have hf := ((represents_raw hF (n+1) W _ ) (member jf (by simp))).1
      have hp := hf.2 _ (List.mem_map_of_mem hL.1)
      simp only [CallEffects.Arrow.map, CallEffects.Contract.map, List.map_map,
        Function.comp_def] at hp
      have hArgs := argument_values (ps := jas)
        (fun p hp => typed p (by simp [hp])) (fun p hp => values p (by simp [hp])) he hw hh
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
      have hvals : CallArguments.Values (args.map (instantiate 0 ρ)) := by
        rw [← actual]
        intro v hv'
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv'
        exact values p (by simp [List.mem_of_mem_take hp])
      have hr := member jr (by simp)
      have hrval := values jr (by simp)
      have hs := CallEffects.call_safe (effect := .ofFootprint .empty)
        (P := ArgsShort (jas.map (fun p => meaning G p.type)))
        (Adm.of_transfer (fun ha j hj U hx => ArgsShort_transfer (fun T hm => by
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type) ha j hj U hx))
        (meaning_adm G jr.type) hp hr hrval hvals ha hw hh
      simpa [CallEffects.Arrow.map, CallEffects.Contract.map, htf, htr,
        instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def] using hs
    · contradiction

theorem selectedCall_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (e : Evidence ι)
    {codes : CodeEntry ι → Bool} (ht : checkTreeUsing G images e codes = true)
    (hp : selectedCallPreserves e = true) (hcodes : CodesSound G codes)
    {ρ n W h} (he : EnvOk G (claim e).context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G (claim e).type) ((CallEffects.Effect.ofFootprint .empty).post h)
      n W h (instantiate 0 ρ (claim e).term) := by
  cases e with
  | node j r ps =>
    simp only [claim] at he ⊢
    simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
    cases r <;> try simp only [selectedCallPreserves] at hp <;> try contradiction
    case app effect =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, hp⟩ := hp
      · apply call_local_sound ht.1 _ _ he hw hh
        · intro p hm
          obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
          exact checkTreeUsing_sound e (ht.2 ⟨e,heq⟩ (by simp)) hcodes
        · intro p hm
          obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
          exact by simpa only [Bool.and_eq_true] using List.all_eq_true.mp hp e heq
    case sub proof =>
      cases ps with
      | nil => contradiction
      | cons child rest =>
        cases rest with
        | cons _ _ => contradiction
        | nil =>
          obtain ⟨hctx,hterm,hsub⟩ := ht.1
          have ih := selectedCall_sound child (ht.2 ⟨child,by simp⟩ (by simp)) hp hcodes
            (ρ := ρ) (n := n) (W := W) (h := h) (by rw [hctx]; exact he) hw hh
          apply consequence (fun j W v hv => PositiveCertificates.acceptedUsing hsub j W v hv)
            (fun _ _ hp => hp) (by rw [hterm] at ih; exact ih)
termination_by sizeOf e

end Verification.ExpressionEffects
