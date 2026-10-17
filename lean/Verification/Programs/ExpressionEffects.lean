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

/-- A type every member of which is a source value: no store and no `top`. -/
def sourceTy (G : NormalGraph ι) (A : Ty ι) : Bool :=
  G.plainTy A && (expand G A).all PositiveNormalization.sourceClause

theorem sourceTy_sound {G : NormalGraph ι} {A n W v} (hs : sourceTy G A = true)
    (hv : meaning G A n W v) : isSourceVal v = true := by
  simp only [sourceTy, Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨c, hc, hcv⟩ := (expand_sem G A hs.1 n W v).mp hv
  exact (PositiveNormalization.sourceClause_sound (hs.2 c hc) hcv.1).1

/-- Whether every alternative is a record whose first invariant operand has
the field `fld`, at a type of source values in each. -/
def sourceField (G : NormalGraph ι) (cs : List (PositiveNormalization.Clause (Ty ι))) (fld : PropKey) : Bool :=
  !cs.isEmpty && cs.all fun c => match HeapExpressionRules.clauseBagOperand c with
    | some B => B.any (fun p => decide (p.1 = fld)) && B.all (fun p => !decide (p.1 = fld) || sourceTy G p.2)
    | none => false

theorem sourceField_sound [DecidableEq ι] {G : NormalGraph ι} {Ref fld n W v}
    (hr : sourceField G (expand G Ref) fld = true) (hv : meaning G Ref n W v) :
    ∃ B A, (fld, A) ∈ B ∧ sourceTy G A = true ∧
      bagT (ReferenceConjunctions.famsOf (meaning G) B) n W v := by
  simp only [sourceField, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hr
  have hp : G.plainTy Ref = true := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hr.1
    exact plain_of_mem_expand (c := c) hc
  obtain ⟨c,hm,hc,-⟩ := (expand_sem G Ref hp n W v).mp hv
  have hb := hr.2 c hm
  cases c <;> simp only [HeapExpressionRules.clauseBagOperand] at hb
  all_goals try contradiction
  all_goals
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hb
    obtain ⟨hany, hall⟩ := hb
    obtain ⟨⟨g, El⟩, hmem, hg⟩ := List.any_eq_true.mp hany
    simp only [decide_eq_true_eq] at hg
    subst hg
    have hsrc : sourceTy G El = true := (hall _ hmem).resolve_left (by simp)
  · exact ⟨_, El, hmem, hsrc, recT_bag hc.1.1⟩
  · exact ⟨_, El, hmem, hsrc, hc.1.1.1⟩

/-- A write of a field of the object in a slot whose type gives it a type of
source values: it changes one location, which holds a value, not a store. -/
def writeWithin (G : NormalGraph ι) (Γ : List (Ty ι)) (Φ : Footprints.Closed) (t : Tm) : Bool :=
  match HeapExpressionRules.writeSlots t with
  | some (f, i, k) => Footprints.Closed.le ⟨.any, .keep⟩ Φ && decide (k < Γ.length) && match Γ[i]? with
    | some Ref => sourceField G (expand G Ref) f
    | none => false
  | none => false

/-- **A typed field write is within `{value: any, store: keep}`.** -/
theorem write_within [DecidableEq ι] {G : NormalGraph ι} {Γ Φ t T ρ n W h}
    (hc : writeWithin G Γ Φ t = true) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' _ => Φ.Holds h h') n W h (instantiate 0 ρ t) := by
  unfold writeWithin at hc
  split at hc
  case h_2 => contradiction
  rename_i f i k hw
  rw [HeapExpressionRules.writeSlots_eq hw] at hs ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hle, hk⟩, hsel⟩ := hc
  split at hsel
  · rename_i Ref hi
    cases n with
    | zero => trivial
    | succ n =>
      have hiv := (meaning_value (he.2 i Ref hi)).1
      have hkv := (meaning_value (he.2 k Γ[k] (List.getElem?_eq_getElem hk))).1
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
      rcases hs with (⟨hbad, _⟩ | hr) | ⟨U, h', t', hx, hu, step, hh', hs'⟩
      · simp [isVal] at hbad
      · exact .inl (.inr hr)
      · obtain ⟨flds, c, oid, l, hl, hfd, hlt, rfl, rfl⟩ := HeapExpressionRules.write_inv hiv hkv step
        refine .inr ⟨U, _, _, hx, hu, step, hh', HeapObservations.refine_value rfl ?_ hs'⟩
        apply Footprints.Closed.Holds.mono hle
        rw [Footprints.Closed.holds_iff]
        refine ⟨by simp, fun l' v hv => ?_⟩
        by_cases hll : l' = l
        · subst hll
          refine ⟨ρ k, by simp [hlt], ?_⟩
          obtain ⟨B, A, hmem, hsrc, hbag⟩ := sourceField_sound hsel (he.2 i Ref hi)
          obtain ⟨flds0, code0, oid0, hl0, _, hrec⟩ := hbag
          obtain ⟨flds1, l1, c1, oid', hproj, hfd1, hlookup, hagree⟩ :=
            recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hmem, rfl⟩) hrec
          rw [hl0] at hl
          cases hl
          cases hproj
          rw [hfd] at hfd1
          cases hfd1
          obtain ⟨u, hu, hmm⟩ := hh.2 l' c1 hlookup
          rw [hv] at hu
          cases hu
          have hA := (hagree 0 (by omega) _ v).mp (hmm 0 (by omega))
          have harr : Footprints.isArr v = false := by
            have := sourceTy_sound hsrc hA
            cases v <;> simp_all [isSourceVal, Footprints.isArr]
          simp only [Footprints.Closed.at, harr]
          trivial
        · refine ⟨v, by rw [List.getElem?_set_ne (Ne.symm hll)]; exact hv, Footprints.Change.Holds.refl _ _ _⟩
  · contradiction

/-- Invocation consumes the selected signature's effect: within the bound
when the signature's footprint is. All actual evaluation has already been
lowered to earlier graph nodes; omitted arguments are the ordinary evidence's
explicit `undefined` premises. Subsumption may retain the postcondition while
changing the result type. -/
def selectedCallWithin (Φ : Footprints.Closed) : Evidence ι → Bool
  | .node _ (.app e) ps =>
      e.footprint.le Φ && ps.all fun p => valueTerm (claim p).term &&
        checkScope (claim p).context.length (claim p).term
  | .node _ (.callRest e _ _ flags _) ps =>
      e.footprint.le Φ && flags.all (· == false) && ps.all fun p => valueTerm (claim p).term &&
        checkScope (claim p).context.length (claim p).term
  | .node _ (.sub _) [p] => selectedCallWithin Φ p
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
    {e : CallEffects.Effect} (hl : LocalUsing G images j (.app e) ps codes)
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hv : ∀ p ∈ ps, valueTerm p.term = true ∧ checkScope p.context.length p.term = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type) (e.post h)
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
      have hplain : e.plain = true := hL.2
      have hs := CallEffects.call_safe (effect := e)
        (P := ArgsShort (jas.map (fun p => meaning G p.type)))
        (Adm.of_transfer (fun ha j hj U hx => ArgsShort_transfer (fun T hm => by
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type) ha j hj U hx))
        (meaning_adm G jr.type) hp hr hrval hvals ha hw hh
      rw [CallEffects.Effect.result_plain hplain] at hs
      simpa [CallEffects.Arrow.map, CallEffects.Contract.map, htf, htr,
        instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def] using hs
    · contradiction

theorem map_spread_false : ∀ (flags : List Bool) (qs : List (Sequent ι)), (∀ b ∈ flags, b = false) →
    flags.length = qs.length →
    (flags.zip qs).map (fun q => spreadTerm (q.1, q.2.term)) = qs.map Sequent.term
  | [], [], _, _ => rfl
  | b :: bs, q :: qs, hf, hl => by
    obtain rfl := hf b (by simp)
    have ih := map_spread_false bs qs (fun b hb => hf b (by simp [hb])) (by simpa using hl)
    simp only [List.zip_cons_cons, List.map_cons, ih]
    rfl
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

theorem map_zip_type : ∀ (flags : List Bool) (qs : List (Sequent ι)), flags.length = qs.length →
    (flags.zip qs).map (fun q => q.2.type) = qs.map Sequent.type
  | [], [], _ => rfl
  | _ :: bs, q :: qs, hl => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [map_zip_type bs qs (by simpa using hl)]
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

/-- A variadic call whose parts are all values, none a spread, at its selected
signature: the signature's postcondition holds of the call. -/
private theorem callRest_local_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {ps : List (Sequent ι)} {codes : CodeEntry ι → Bool}
    {e : CallEffects.Effect} {k u : Nat} {flags : List Bool} {P : Ty ι}
    (hl : LocalUsing G images j (.callRest e k u flags P) ps codes)
    (hnos : flags.all (· == false) = true)
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hv : ∀ p ∈ ps, valueTerm p.term = true ∧ checkScope p.context.length p.term = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type) (e.post h)
      n W h (instantiate 0 ρ j.term) := by
  rcases j with ⟨Γ,t,A⟩
  cases t <;> try exact (hl : False).elim
  rename_i f r args
  rcases ps with _ | ⟨jf, _ | ⟨jr, jas⟩⟩
  · exact (hl : False).elim
  · exact (hl : False).elim
  obtain ⟨hΓf, htf, hΓr, htr, hcontexts, hlen, hshort, hargs, hundef, hparts, hmem, hplain⟩ := hl
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
  -- No part is a spread: the parts are the actuals themselves.
  have hflags : ∀ b ∈ flags, b = false := by
    intro b hb
    simpa using List.all_eq_true.mp hnos b hb
  have hl2 : (jas.drop (k + u)).length = flags.length := by simp [hlen]
  have hl2' : jas.length - (k + u) = flags.length := by simpa using hl2
  have hnospread := map_spread_false flags (jas.drop (k + u)) hflags hl2.symm
  rw [hnospread] at hargs
  cases n with
  | zero => trivial
  | succ n =>
    have member : ∀ p ∈ jf::jr::jas, meaning G p.type (n+1) W (instantiate 0 ρ p.term) := by
      intro p hp
      exact safe_value_mem (values p hp) ((typed p hp).sound _ _ h ρ he hw hh)
    have hf := restsT_of_restSigs hmem (member jf (by simp))
    have hp := hf.2 _ (List.mem_singleton_self _)
    have hAll := argument_values (ps := jas)
      (fun p hp => typed p (by simp [hp])) (fun p hp => values p (by simp [hp])) he hw hh
    -- The actuals' values: the fixed ones, then the parts.
    let vals := fun (qs : List (Sequent ι)) => qs.map (fun p => instantiate 0 ρ p.term)
    have hsplitk := ArgsT_take_drop k hAll
    have hsplitku := ArgsT_take_drop (k + u) hAll
    simp only [← List.map_take, ← List.map_drop] at hsplitk hsplitku
    have hpack : argMeaning G P (n+1) W (vals (jas.drop (k + u))) := by
      unfold RestParts at hparts
      have hany : ((flags.zip (jas.drop (k + u))).map fun q => (q.1, q.2.type)).any (·.1) = false := by
        simp only [List.any_eq_false, List.mem_map, Prod.exists]
        rintro _ ⟨a, b, hab, rfl⟩
        exact by simpa using hflags a (List.of_mem_zip hab).1
      rw [hany] at hparts
      simp only [Bool.false_eq_true, ite_false] at hparts
      split at hparts
      · rename_i T hPT
        obtain ⟨hreq, hbound, hpos⟩ := hparts
        have hzip := map_zip_type flags (jas.drop (k + u)) hl2.symm
        apply restParts_pack hPT (Qs := (jas.drop (k + u)).map Sequent.type)
        · simp only [List.length_map, List.length_drop, hl2']
          simpa [List.length_map, List.length_zip, hl2'] using hreq
        · simp only [List.length_map, List.length_drop, hl2']
          simpa [List.length_map, List.length_zip, hl2'] using hbound
        · intro i hi
          have := hpos i (by
            simp only [List.mem_range, List.length_map, List.length_drop, List.length_zip] at hi ⊢
            omega)
          rw [this, ← hzip]
          simp [List.getElem?_map, Option.map_map, Function.comp_def]
        · simpa [vals, List.map_map, Function.comp_def] using hsplitku.2
      · exact hparts.elim
    have hacc : ArgsRest ((jas.take (k + u)).map (fun p => meaning G p.type)) (argMeaning G P) (n+1) W
        (vals (jas.take k) ++ vals (jas.drop (k + u))) := by
      rcases hshort with rfl | rfl
      · simp only [Nat.add_zero] at hpack ⊢
        exact ArgsRest_of_exact_extra hsplitk.1 hpack
      · have hl2 : jas.drop (k + u) = [] := by
          apply List.eq_nil_of_length_eq_zero; simp [hlen]
        rw [hl2]
        simp only [vals, List.map_nil, List.append_nil]
        have hpad : ArgsShort ((jas.take (k + u)).map (fun p => meaning G p.type)) (n+1) W
            ((jas.take k).map (fun p => instantiate 0 ρ p.term)) := by
          apply ArgsShort_of_pad (pad := ((jas.drop k).take u).map (fun p => instantiate 0 ρ p.term))
          · intro a ha
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
            simp [hundef p hp, instantiate]
          · simpa only [List.take_add, List.map_append] using hsplitku.1
        have hlen' := hpad.1
        refine ⟨by rwa [List.take_of_length_le hlen'], ?_⟩
        rw [List.drop_eq_nil_of_le hlen']
        simpa [vals, hl2] using hpack
    have hvals : CallArguments.Values (vals (jas.take k) ++ vals (jas.drop (k + u))) := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha <;> obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      · exact values p (by simp [List.mem_of_mem_take hp])
      · exact values p (by simp [List.mem_of_mem_drop hp])
    have hr := member jr (by simp)
    have hrval := values jr (by simp)
    have hs := CallEffects.call_safe (effect := e)
      (P := ArgsRest ((jas.take (k + u)).map (fun p => meaning G p.type)) (argMeaning G P))
      (Adm.of_transfer (fun ha j hj U hx => ArgsRest_transfer (fun T hm => by
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type)
        (argMeaning_adm G P) ha j hj U hx))
      (meaning_adm G jr.type)
      (by simpa [CallEffects.RestArrow.mapWith, CallEffects.Contract.map, List.map_map, Function.comp_def] using hp)
      hr hrval hvals hacc hw hh
    rw [CallEffects.Effect.result_plain hplain] at hs
    simpa [htf, htr, hargs, vals, instantiate, instantiateArgs_eq_map, List.map_map,
      Function.comp_def] using hs

theorem selectedCall_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {Φ : Footprints.Closed} (e : Evidence ι)
    {codes : CodeEntry ι → Bool} (ht : checkTreeUsing G images e codes = true)
    (hp : selectedCallWithin Φ e = true) (hcodes : CodesSound G codes)
    {ρ n W h} (he : EnvOk G (claim e).context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G (claim e).type) (fun h' _ => Φ.Holds h h')
      n W h (instantiate 0 ρ (claim e).term) := by
  cases e with
  | node j r ps =>
    simp only [claim] at he ⊢
    simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
    cases r <;> try simp only [selectedCallWithin] at hp <;> try contradiction
    case app effect =>
      simp only [Bool.and_eq_true] at hp
      obtain ⟨hle, hp⟩ := hp
      apply HeapObservations.weaken (fun h' v hq => Footprints.Closed.Holds.mono hle hq)
      apply call_local_sound ht.1 _ _ he hw hh
      · intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound e (ht.2 ⟨e,heq⟩ (by simp)) hcodes
      · intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact by simpa only [Bool.and_eq_true] using List.all_eq_true.mp hp e heq
    case callRest effect k u flags P =>
      simp only [Bool.and_eq_true] at hp
      obtain ⟨⟨hle, hnos⟩, hp⟩ := hp
      apply HeapObservations.weaken (fun h' v hq => Footprints.Closed.Holds.mono hle hq)
      apply callRest_local_sound ht.1 hnos _ _ he hw hh
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
