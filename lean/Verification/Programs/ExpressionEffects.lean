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

/-- A required named field, through either an invariant cell or a read view.
The contents contract supplies valuehood; a heap is not assumed to contain
values at every arbitrary, untyped location. -/
def readable (G : NormalGraph ι) (Ref : Ty ι) (fld : PropKey) : Bool :=
  match expand G Ref with
  | [c] => match namedMembers c with
    | some (fs, vs) => (fs ++ vs.filter (·.1 != lengthKey)).any (fun p => p.1 == fld)
    | none => false
  | _ => false

theorem readable_value {G : NormalGraph ι} {Ref fld n W h v}
    (hr : readable G Ref fld = true) (hv : meaning G Ref (n+1) W v)
    (hh : HeapOk (n+1) W h) :
    ∃ u, Step h (.readAt fld v) h u ∧ isVal u = true := by
  unfold readable at hr
  split at hr
  · rename_i c hc
    split at hr
    · rename_i fs vs hm
      obtain ⟨⟨f,A⟩, hf, heq⟩ := List.any_eq_true.mp hr
      have heq : f = fld := by simpa using heq
      subst f
      have hfields := namedMembers_sem hc hm hv
      rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨fields,l,ctr,oid',rfl,hfield,hlookup,hagree⟩ :=
          recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A,hf,rfl⟩) hfields.1
        obtain ⟨u,hu,ht⟩ := hh.2 l ctr hlookup
        exact ⟨u,.readField hfield hu, meaning_valOnly G A 0 _ u
          ((hagree 0 (by omega) _ u).mp (ht 0 (by omega)))⟩
      · obtain ⟨hf, hfl⟩ := List.mem_filter.mp hf
        obtain ⟨fields,l,ctr,oid',rfl,hfield,hlookup,hbound⟩ :=
          viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A,hf,rfl⟩) (by simpa using hfl) hfields.2
        obtain ⟨u,hu,ht⟩ := hh.2 l ctr hlookup
        exact ⟨u,.readField hfield hu, meaning_valOnly G A 0 _ u
          (hbound 0 (by omega) _ u (ht 0 (by omega)))⟩
    · contradiction
  · contradiction

/-- Pure computations, required-field reads, and allocations with evaluated
initializers. Invocation requires a separate qualified-call derivation. -/
def check (G : NormalGraph ι) (Γ : List (Ty ι)) (t : Tm) : Bool :=
  Purity.pureTerm t || match t with
  | .readAt f (.var i) => (Γ[i]?).any (fun Ref => readable G Ref f)
  | .makeAt _ _ xs | .arrLit xs => xs.all valueTerm
  | _ => false

/-- A single allocation changes only freshly appended locations. -/
theorem make_preserves {T n W h code fields xs}
    (hv : ∀ v ∈ xs, isVal v = true)
    (hs : Safe Ξ T n W h (.makeAt code fields xs)) :
    SafePost Ξ T (CallEffects.Effect.preservesInputHeap.post h) n W h (.makeAt code fields xs) := by
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hb,_⟩ | ⟨v,hr,_⟩) | ⟨U,h',t',hx,hu,st,hh,hs⟩
    · contradiction
    · cases hr with
      | makeArg hg _ hr => exact False.elim (by
          have := hv _ (List.mem_of_getElem? hg)
          rw [raises_not_val hr] at this; contradiction)
    · cases st with
      | makeArg hg _ st => exact False.elim (value_no_step (hv _ (List.mem_of_getElem? hg)) st)
      | makeFields hvs hlen =>
        exact .inr ⟨U,_,_,hx,hu,.makeFields hvs hlen,hh,
          refine_value rfl ⟨xs ++ [.nul], by simp⟩ hs⟩

theorem array_preserves {T n W h xs}
    (hv : ∀ v ∈ xs, isVal v = true)
    (hs : Safe Ξ T n W h (.arrLit xs)) :
    SafePost Ξ T (CallEffects.Effect.preservesInputHeap.post h) n W h (.arrLit xs) := by
  apply one_step rfl rfl (.arrAlloc hv) ⟨xs,rfl⟩ hs

theorem sound {G : NormalGraph ι} {Γ t A ρ n W h}
    (hc : check G Γ t = true) (hscope : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe (excOf G) (meaning G A) n W h (instantiate 0 ρ t)) :
    SafePost (excOf G) (meaning G A) (CallEffects.Effect.preservesInputHeap.post h)
      n W h (instantiate 0 ρ t) := by
  simp only [check, Bool.or_eq_true] at hc
  rcases hc with hp | hc
  · exact CallEffects.pure_safe (.term (HeapExpressionRules.pure_instantiate (d := 0) hp hscope he)) hs
  · split at hc
    · rename_i t fld i
      simp only [Option.any_eq_true] at hc
      obtain ⟨Ref,hi,hr⟩ := hc
      cases n with
      | zero => trivial
      | succ n =>
        obtain ⟨u,st,hval⟩ := readable_value hr (he.2 i Ref hi) hh
        exact one_step rfl hval st ⟨[],by simp⟩ hs
    · rename_i t code fields xs
      have hscopes : ∀ a ∈ xs, checkScope Γ.length a = true := by
        cases code <;> simp_all [checkScope, checkScopes_iff, List.all_eq_true]
      have hvalues : ∀ v ∈ xs.map (instantiate 0 ρ), isVal v = true := by
        intro v hv
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
        exact valueTerm_instantiate (List.all_eq_true.mp hc a ha) (hscopes a ha) he
      cases code <;> simp only [instantiate, instantiateArgs_eq_map] at hs ⊢ <;>
        exact make_preserves hvalues hs
    · rename_i t xs
      simp only [checkScope, checkScopes_iff] at hscope
      simp only [instantiate, instantiateArgs_eq_map] at hs ⊢
      apply array_preserves _ hs
      intro v hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
      exact valueTerm_instantiate (List.all_eq_true.mp hc a ha) (hscope a ha) he
    · contradiction

/-- Invocation consumes the selected signature's effect. All actual evaluation
has already been lowered to earlier graph nodes; omitted arguments are the
ordinary evidence's explicit `undefined` premises. Subsumption may retain the
postcondition while changing the result type. -/
def selectedCallPreserves : Evidence ι → Bool
  | .node _ (.app .preservesInputHeap) ps =>
      ps.all fun p => valueTerm (claim p).term &&
        checkScope (claim p).context.length (claim p).term
  | .node _ (.sub _) [p] => selectedCallPreserves p
  | _ => false

private theorem argument_values [DecidableEq ι] {G : NormalGraph ι}
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
    (hl : LocalUsing G images j (.app .preservesInputHeap) ps codes)
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hv : ∀ p ∈ ps, valueTerm p.term = true ∧ checkScope p.context.length p.term = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type) (CallEffects.Effect.preservesInputHeap.post h)
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
      have hp := hf.2 _ (List.mem_map_of_mem hL)
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
      have hs := CallEffects.call_safe (effect := .preservesInputHeap)
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
    SafePost (excOf G) (meaning G (claim e).type) (CallEffects.Effect.preservesInputHeap.post h)
      n W h (instantiate 0 ρ (claim e).term) := by
  cases e with
  | node j r ps =>
    simp only [claim] at he ⊢
    simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
    cases r <;> try simp only [selectedCallPreserves] at hp <;> try contradiction
    case app effect =>
      cases effect with
      | unrestricted => contradiction
      | preservesInputHeap =>
        apply call_local_sound ht.1 _ _ he hw hh
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

#print axioms sound
#print axioms selectedCall_sound
end Verification.ExpressionEffects
