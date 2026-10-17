import Verification.Programs.HeapExpressionRules

/-! Definition-side effect checks over lowered expressions. Safety comes from
ordinary evidence; this layer establishes the additional heap postcondition. -/
namespace Verification.ExpressionEffects
open ProgramTyping ProgramCertificates PositiveGraphs PositiveRules HeapObservations

/-- The receiver of an invocation, and `undefined` for any other term: what a
selected signature's postcondition is relative to. -/
def receiverOf : Tm → Tm
  | .invoke _ r _ => r
  | _ => .undef

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

private theorem read_instantiate {G : NormalGraph ι} {Γ t ρ n W} {d : Nat}
    (hp : Purity.readTerm t = true) (hc : checkScope (Γ.length + d) t = true)
    (he : EnvOk G Γ ρ n W) : Purity.readTerm (instantiate d ρ t) = true := by
  induction t using Tm.induct generalizing d
  case var i =>
    simp only [instantiate]
    split
    · rfl
    · have hi : i - d < Γ.length := by simp [checkScope] at hc; omega
      exact Purity.read_value
        (meaning_value (he.2 (i-d) Γ[i-d] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))).1
  all_goals simp only [Purity.readTerm, instantiate, checkScope, Bool.and_eq_true] at hp hc ⊢
  all_goals first
    | (simp_all; done)
    | (simp_all [isVal]; done)
    | (simp [isVal] at hp; done)

private theorem init_instantiate {G : NormalGraph ι} {Γ t ρ n W} {d : Nat}
    (hp : Purity.initTerm t = true) (hc : checkScope (Γ.length + d) t = true)
    (he : EnvOk G Γ ρ n W) : Purity.initTerm (instantiate d ρ t) = true := by
  by_cases hs : ∃ b, t = .spread b
  · obtain ⟨b, rfl⟩ := hs
    simp only [instantiate, Purity.initTerm, checkScope] at hp hc ⊢
    exact read_instantiate hp hc he
  · have ho : Purity.operandTerm t = true := by cases t <;> simp_all [Purity.initTerm]
    have h' := operand_instantiate ho hc he
    revert h'
    generalize instantiate d ρ t = u
    intro hu
    cases u <;> simp_all [Purity.initTerm, Purity.operandTerm, isVal]

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
    | (rintro _ ⟨x, hx, rfl⟩; exact init_instantiate (hp x hx) (hc x hx) he)
    | (simp [isVal] at hp ⊢; done)
    | (simp_all [Nat.add_assoc]; done)

/-- An inspection preserves the input heap on normal return: every step keeps
the heap a prefix, reading from a heap that holds values, which every heap
meeting an admissible world does (`heap_values`). Safety is supplied
separately. -/
theorem inspect_safe {T : Fam} {initial : Heap} : ∀ {n W h t},
    initial.IsPrefix h → Purity.inspectTerm t = true → WorldAdm W → HeapOk n W h →
    Safe Ξ T n W h t →
    SafePost Ξ T (fun h' _ => Footprints.Closed.empty.Holds initial h') n W h t := by
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
    SafePost (excOf G) (meaning G A) (fun h' _ => Footprints.Closed.empty.Holds h h')
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

/-- A spread's operand: a value, or a field read of one, the store a spread
reads where it is written. -/
def readOperand : Tm → Bool
  | .readAt _ t => valueTerm t
  | t => valueTerm t

/-- A variadic call's operands with a spread among its parts: the callee, the
receiver and every fixed or omitted actual a value, each plain part a value,
each spread's operand a value or a read of one. -/
def spreadOperands (k u : Nat) (flags : List Bool) : List (Sequent ι) → Bool
  | jf :: jr :: jas => valueTerm jf.term && valueTerm jr.term &&
      (jas.take (k + u)).all (fun q => valueTerm q.term) &&
      (flags.zip (jas.drop (k + u))).all fun q => if q.1 then readOperand q.2.term else valueTerm q.2.term
  | _ => false

/-- The effect of the signature a call's evidence selects: an invocation's, a
variadic invocation's or a construction's, through subsumption. -/
def selectedEffect : Evidence ι → Option CallEffects.Effect
  | .node _ (.app e) _ => some e
  | .node _ (.callRest e _ _ _ _) _ => some e
  | .node _ (.construct e) _ => some e
  | .node _ (.sub _) [p] => selectedEffect p
  | _ => none

/-- A selected call's operands. All actual evaluation has already been
lowered to earlier graph nodes; omitted arguments are the ordinary evidence's
explicit `undefined` premises; a variadic call's spreads read their operands'
stores in place. Subsumption may retain the postcondition while changing the
result type. -/
def selectedOperands : Evidence ι → Bool
  | .node _ (.app _) ps =>
      ps.all fun p => valueTerm (claim p).term && checkScope (claim p).context.length (claim p).term
  | .node _ (.callRest _ k u flags _) ps =>
      ps.all (fun p => checkScope (claim p).context.length (claim p).term) &&
        (ps.all (fun p => valueTerm (claim p).term) ||
          flags.any id && spreadOperands k u flags (ps.map claim))
  | .node _ (.construct _) ps =>
      ps.all fun p => valueTerm (claim p).term && checkScope (claim p).context.length (claim p).term
  | .node _ (.sub _) [p] => selectedOperands p
  | _ => false

/-- Invocation and construction consume the selected signature's effect:
within the bound when the signature's footprint is, and, for a signature
excepting its receiver's store, when the bound lets everything change. -/
def selectedCallWithin (Φ : Footprints.Closed) (e : Evidence ι) : Bool :=
  selectedOperands e && match selectedEffect e with
    | some eff => eff.footprint.le Φ && (!eff.receiverStore || Φ == .top)
    | none => false

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
    SafePostExc (excOf G) (meaning G j.type) (e.post (receiverOf (instantiate 0 ρ j.term)) h)
      (e.excPost (receiverOf (instantiate 0 ρ j.term)) h) n W h (instantiate 0 ρ j.term) := by
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
      have hs := CallEffects.call_safe_exc (effect := e)
        (P := ArgsShort (jas.map (fun p => meaning G p.type)))
        (Adm.of_transfer (fun ha j hj U hx => ArgsShort_transfer (fun T hm => by
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type) ha j hj U hx))
        (meaning_adm G jr.type) hp hr hrval hvals ha hw hh
      rw [CallEffects.Effect.result_plain hplain] at hs
      simpa [CallEffects.Arrow.map, CallEffects.Contract.map, htf, htr, receiverOf,
        instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def] using hs
    · contradiction

/-- Construction consumes the selected construct signature's effect, as
invocation does: the constructor and the actuals are values, each omitted
position an explicit `undefined` premise. -/
private theorem construct_local_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {ps : List (Sequent ι)} {codes : CodeEntry ι → Bool}
    {e : CallEffects.Effect} (hl : LocalUsing G images j (.construct e) ps codes)
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hv : ∀ p ∈ ps, valueTerm p.term = true ∧ checkScope p.context.length p.term = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePostExc (excOf G) (meaning G j.type) (e.post (receiverOf (instantiate 0 ρ j.term)) h)
      (e.excPost (receiverOf (instantiate 0 ρ j.term)) h) n W h (instantiate 0 ρ j.term) := by
  rcases j with ⟨Γ,t,A⟩
  -- The rule admits only a construction with a constructor premise.
  cases t <;> try exact (hl : False).elim
  rename_i f args
  rcases ps with _ | ⟨jf, jas⟩
  · exact (hl : False).elim
  obtain ⟨hΓf, htf, hargs, hundef, hcontexts, hL⟩ := hl
  have context : ∀ p ∈ jf::jas, p.context = Γ := by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hΓf
    · exact hcontexts p hp
  have typed : ∀ p ∈ jf::jas, HasTyUsing G images Γ p.term p.type := by
    intro p hp
    simpa only [context p hp] using ht p hp
  have values : ∀ p ∈ jf::jas, isVal (instantiate 0 ρ p.term) = true := by
    intro p hp
    exact valueTerm_instantiate (hv p hp).1 (hv p hp).2 (by simpa [context p hp] using he)
  cases n with
  | zero => trivial
  | succ n =>
    have member : ∀ p ∈ jf::jas, meaning G p.type (n+1) W (instantiate 0 ρ p.term) := by
      intro p hp
      exact safe_value_mem (values p hp) ((typed p hp).sound _ _ h ρ he hw hh)
    split at hL
    · rename_i L S a bs vs hF
      obtain ⟨hmem, hpl⟩ := hL
      have hf := ((represents_raw hF (n+1) W _ ) (member jf (by simp))).1.1
      have hp := hf.2 _ (List.mem_map_of_mem hmem)
      simp only [CallEffects.MethodArrow.map, CallEffects.Contract.map, List.map_map,
        Function.comp_def] at hp
      have hArgs := argument_values (ps := jas)
        (fun p hp => typed p (by simp [hp])) (fun p hp => values p (by simp [hp])) he hw hh
      have actual : (jas.take args.length).map (fun p => instantiate 0 ρ p.term)
          = args.map (instantiate 0 ρ) := by
        simpa only [List.map_map, Function.comp_def] using
          congrArg (List.map (instantiate 0 ρ)) hargs
      have hsplit : jas.map (fun p => instantiate 0 ρ p.term) = args.map (instantiate 0 ρ) ++
          (jas.drop args.length).map (fun p => instantiate 0 ρ p.term) := by
        rw [← actual, ← List.map_append, List.take_append_drop]
      have hvals : CallArguments.Values (args.map (instantiate 0 ρ)) := by
        rw [← actual]
        intro v hv'
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv'
        exact values p (by simp [List.mem_of_mem_take hp])
      have hs := CallEffects.construct_safe_exc hpl
        (P := ArgsT (jas.map (fun p => meaning G p.type)))
        (Adm.of_transfer (fun ha j hj U hx => ArgsT_transfer (fun T hm => by
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type) ha j hj U hx))
        hp hvals (pad := (jas.drop args.length).map (fun p => instantiate 0 ρ p.term))
        (by
          intro v hv'
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv'
          simp [hundef p hp, instantiate])
        (by rw [← hsplit]; exact hArgs) hw hh
      simpa [htf, receiverOf, instantiate, instantiateArgs_eq_map] using hs
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

/-- A spread operand that reads the heap, in a call whose earlier actuals are
values: its reads keep the heap, so a postcondition of the run from that
heap, once the operand is a value at `S`, is one of the whole. -/
theorem spread_head_post {S R : Fam} {Q : HeapObservations.Post} {f r : Tm} {pre rest : List Tm}
    (hf : isVal f = true) (hrv : isVal r = true) (hp : CallArguments.Values pre) :
    ∀ (n : Nat) (W : WorldT n) (heap : Heap) (s : Tm),
      Purity.readTerm s = true → WorldAdm W → HeapOk n W heap → Safe Ξ S n W heap s →
      (∀ j (hj : j ≤ n) (U : WorldT j), WExt (trunc j hj W) U → WorldAdm U → HeapOk j U heap →
        ∀ v, isVal v = true → S j U v → SafePost Ξ R Q j U heap (.invoke f r (pre ++ .spread v :: rest))) →
      SafePost Ξ R Q n W heap (.invoke f r (pre ++ .spread s :: rest)) := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W heap s hs hw hh hsafe hk
    rcases hsafe with (⟨hv, hS⟩ | hthrown) | ⟨U, h', t', hx, hu, step, hh', ht'⟩
    · exact hk (n+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw hh s hv hS
    · exact Or.inl (Or.inr (hthrown.lift (C := fun t => .invoke f r (pre ++ .spread t :: rest))
        (fun r' => RestCalls.call_raise hf hrv hp (.spreadC r'))))
    · obtain ⟨rfl, hs'⟩ := Purity.read_step step hs (HeapExpressionRules.heap_values hw hh)
      refine Or.inr ⟨U, h', _, hx, hu, RestCalls.call_lift hf hrv hp (.spreadC step), hh', ?_⟩
      apply ih U h' t' hs' hu hh' ht'
      intro j hj V hy hV hhV v hv hS
      apply hk j (by omega) V _ hV hhV v hv hS
      apply WExt_trans _ hy
      simpa only [trunc_trunc] using WExt_trunc hj hx

/-- **Parts after the fixed actuals, every one ready or a read**: each plain
part a value at the element contract `E`, each spread a read of a store at a
type that spreads into `E`, read where it is written. The call steps through
the spreads in the heap it starts in, so any postcondition of the call's run
from that heap holds of the whole. -/
theorem spread_values_post {E R : Fam} {Q : HeapObservations.Post} (hE : Adm E) (hEv : ValOnly E)
    {f r : Tm} (hf : isVal f = true) (hrv : isVal r = true) :
    ∀ (parts : List (Option Fam × Tm)) (n : Nat) (W : WorldT n) (heap : Heap) (pre : List Tm),
      (∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ RestCalls.Spreads S E ∧
        Purity.readTerm p.2 = true ∧ FutureSafe Ξ S n W p.2) →
      WorldAdm W → HeapOk n W heap → CallArguments.Values pre →
      (∀ p ∈ parts, p.1 = none → isVal p.2 = true ∧ E n W p.2) →
      (∀ j (hj : j ≤ n) (U : WorldT j), WExt (trunc j hj W) U → WorldAdm U → HeapOk j U heap →
        ∀ extra, (∀ e ∈ extra, E j U e) → SafePost Ξ R Q j U heap (.invoke f r (pre ++ extra))) →
      SafePost Ξ R Q n W heap (.invoke f r (pre ++ parts.map RestCalls.partTerm))
  | [], n, W, heap, pre, _, hw, hh, _, _, hk => by
    simpa using hk n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw hh [] (by simp)
  | (none, a) :: parts, n, W, heap, pre, hS, hw, hh, hp, hv, hk => by
    obtain ⟨hav, haE⟩ := hv (none, a) (by simp) rfl
    have hrest := spread_values_post hE hEv hf hrv parts n W heap (pre ++ [a])
      (fun q hm => hS q (by simp [hm])) hw hh
      (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hp x hx
        · simp at hx; subst hx; exact hav)
      (fun q hm => hv q (by simp [hm]))
      (by
        intro j hj U hx hu hh' extra he
        have := hk j hj U hx hu hh' (a :: extra) (by
          intro e hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact hE.mono j _ U hx e (hE.down_le n j hj W e haE)
          · exact he e hm)
        simpa using this)
    simpa [RestCalls.partTerm] using hrest
  | (some S, s) :: parts, n, W, heap, pre, hS, hw, hh, hp, hv, hk => by
    obtain ⟨hSa, hSs, hread, hfut⟩ := hS (some S, s) (by simp) S rfl
    show SafePost Ξ R Q n W heap (.invoke f r (pre ++ .spread s :: parts.map RestCalls.partTerm))
    apply spread_head_post hf hrv hp n W heap s hread hw hh
      (hfut n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap hh)
    intro j hj U hx hu hhU v _ hSv
    obtain ⟨ls, vs, rfl, hr, he⟩ := hSs j U heap _ hhU hSv
    cases j with
    | zero => trivial
    | succ p =>
      have hvs : CallArguments.Values vs := fun e hm => hEv p _ e (he e hm p (by omega))
      refine Or.inr ⟨trunc p (Nat.le_succ p) U, heap,
        .invoke f r (pre ++ vs ++ parts.map RestCalls.partTerm), WExt_refl _, WorldAdm_trunc _ hu,
        .callSpread hf hrv rfl hp hr, HeapOk_trunc p U heap hhU, ?_⟩
      have hUV : ∀ i (hi : i ≤ p) (X : WorldT i),
          WExt (trunc i hi (trunc p (Nat.le_succ p) U)) X → WExt (trunc i (by omega) W) X := by
        intro i hi X hy
        apply WExt_trans _ hy
        have := WExt_trunc (show i ≤ p + 1 by omega) hx
        simpa only [trunc_trunc] using this
      have hrest := spread_values_post hE hEv hf hrv parts p _ heap (pre ++ vs)
        (by
          intro q hm T hT
          obtain ⟨h1, h2, h3, h4⟩ := hS q (by simp [hm]) T hT
          refine ⟨h1, h2, h3, ?_⟩
          intro i hi X hy hX heap' hh'
          exact h4 i (by omega) X (hUV i hi X hy) hX heap' hh')
        (WorldAdm_trunc _ hu) (HeapOk_trunc p U heap hhU)
        (by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hp x hx
          · exact hvs x hx)
        (by
          intro q hm hq
          obtain ⟨h1, h2⟩ := hv q (by simp [hm]) hq
          refine ⟨h1, ?_⟩
          have := hE.down_le n p (by omega) W q.2 h2
          exact hE.mono p _ _ (hUV p (Nat.le_refl _) _ (by rw [trunc_id]; exact WExt_refl _)) q.2 this)
        (by
          intro i hi X hy hX hh' extra hex
          have := hk i (by omega) X (hUV i hi X hy) hX hh' (vs ++ extra) (by
            intro e hm
            rcases List.mem_append.mp hm with hm | hm
            · have h0 := he e hm i (by omega)
              exact hE.mono i _ X (by
                apply WExt_trans _ hy
                simp only [trunc_trunc]
                exact WExt_refl _) e h0
            · exact hex e hm)
          simpa using this)
      simpa using hrest

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
    SafePost (excOf G) (meaning G j.type) (e.post (receiverOf (instantiate 0 ρ j.term)) h)
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
    simpa [htf, htr, hargs, vals, receiverOf, instantiate, instantiateArgs_eq_map, List.map_map,
      Function.comp_def] using hs

theorem readOperand_instantiate {G : NormalGraph ι} {Γ t ρ n W}
    (hv : readOperand t = true) (hc : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) : Purity.readTerm (instantiate 0 ρ t) = true := by
  cases t
  case readAt k x =>
    simp only [readOperand] at hv
    simp only [checkScope] at hc
    simp only [instantiate, Purity.readTerm]
    exact Purity.read_value (valueTerm_instantiate hv hc he)
  all_goals exact Purity.read_value (valueTerm_instantiate (by simpa [readOperand] using hv) hc he)

/-- A variadic call with a spread among its parts, the callee, the receiver,
the fixed actuals and the plain parts values, each spread's operand a read, at
its selected signature: the spreads are read in the heap the call starts in,
and the signature's postcondition holds of the call. -/
private theorem callRestSpread_local_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {ps : List (Sequent ι)} {codes : CodeEntry ι → Bool}
    {e : CallEffects.Effect} {k u : Nat} {flags : List Bool} {P : Ty ι}
    (hl : LocalUsing G images j (.callRest e k u flags P) ps codes)
    (hsp : flags.any id = true)
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hsc : ∀ p ∈ ps, checkScope p.context.length p.term = true)
    (hops : spreadOperands k u flags ps = true ∨ (ps.all fun p => valueTerm p.term) = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type) (e.post (receiverOf (instantiate 0 ρ j.term)) h)
      n W h (instantiate 0 ρ j.term) := by
  rcases j with ⟨Γ,t,A⟩
  cases t <;> try exact (hl : False).elim
  rename_i f r args
  rcases ps with _ | ⟨jf, _ | ⟨jr, jas⟩⟩
  · exact (hl : False).elim
  · exact (hl : False).elim
  obtain ⟨hΓf, htf, hΓr, htr, hcontexts, hlen, hshort, hargs, hundef, hparts, hmem, hplain⟩ := hl
  have hops : spreadOperands k u flags (jf :: jr :: jas) = true := by
    rcases hops with hops | hvals
    · exact hops
    · simp only [List.all_eq_true, List.mem_cons] at hvals
      simp only [spreadOperands, Bool.and_eq_true, List.all_eq_true]
      refine ⟨⟨⟨hvals jf (by simp), hvals jr (by simp)⟩,
        fun q hq => hvals q (.inr (.inr (List.mem_of_mem_take hq)))⟩, fun q hq => ?_⟩
      have hv := hvals q.2 (.inr (.inr (List.mem_of_mem_drop (List.of_mem_zip hq).2)))
      split
      · revert hv; cases q.2.term <;> simp [readOperand, valueTerm, isVal]
      · exact hv
  simp only [spreadOperands, Bool.and_eq_true, List.all_eq_true] at hops
  obtain ⟨⟨⟨hfv0, hrv0⟩, hfixed0⟩, hparts0⟩ := hops
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
  have inScope : ∀ p ∈ jf::jr::jas, checkScope Γ.length p.term = true := by
    intro p hp
    simpa [context p hp] using hsc p hp
  have valueOf : ∀ p ∈ jf::jr::jas, valueTerm p.term = true → isVal (instantiate 0 ρ p.term) = true := by
    intro p hp hv
    exact valueTerm_instantiate hv (inScope p hp) (by simpa [context p hp] using he)
  -- A spread among the parts: no fixed position is omitted.
  have hu : u = 0 := by
    rcases hshort with h | h
    · exact h
    · subst h; simp at hsp
  subst hu
  unfold RestParts at hparts
  have hany : ((flags.zip (jas.drop k)).map fun q => (q.1, q.2.type)).any (·.1) = true := by
    obtain ⟨b, hb, hbt⟩ := List.any_eq_true.mp hsp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hlen' : (jas.drop k).length = flags.length := by simp [hlen]
    apply List.any_eq_true.mpr
    refine ⟨(flags[i], ((jas.drop k)[i]'(by omega)).type), ?_, by simpa using hbt⟩
    apply List.mem_map.mpr
    refine ⟨(flags[i], (jas.drop k)[i]'(by omega)), ?_, rfl⟩
    exact List.mem_iff_getElem.mpr ⟨i, by simp [List.length_zip]; omega, by simp⟩
  simp only [Nat.add_zero] at hany hparts hargs hlen hfixed0 hparts0 ⊢
  have hfixedv : ∀ p ∈ jas.take k, isVal (instantiate 0 ρ p.term) = true :=
    fun p hp => valueOf p (by simp [List.mem_of_mem_take hp]) (hfixed0 p hp)
  rw [hany] at hparts
  simp only [if_true] at hparts
  split at hparts
  case h_2 => exact hparts.elim
  rename_i El hel
  cases n with
  | zero => trivial
  | succ n =>
    have member : ∀ p ∈ jf::jr::jas, isVal (instantiate 0 ρ p.term) = true →
        meaning G p.type (n+1) W (instantiate 0 ρ p.term) := by
      intro p hp hv
      exact safe_value_mem hv ((typed p hp).sound _ _ h ρ he hw hh)
    have hfv := valueOf jf (by simp) hfv0
    have hrv := valueOf jr (by simp) hrv0
    have hf := restsT_of_restSigs hmem (member jf (by simp) hfv)
    have hfixed : ArgsT ((jas.take k).map (fun p => meaning G p.type)) (n+1) W
        ((jas.take k).map (fun p => instantiate 0 ρ p.term)) := by
      have hAll := argument_values (ps := jas.take k)
        (fun p hp => typed p (by simp [List.mem_of_mem_take hp]))
        hfixedv he hw hh
      exact hAll
    -- The parts: each spread at its store type, each plain part at the element.
    let parts : List (Option Fam × Tm) := (flags.zip (jas.drop k)).map fun q =>
      ((if q.1 then some (meaning G q.2.type) else none), instantiate 0 ρ q.2.term)
    have hterm : instantiate 0 ρ (.invoke f r args) = .invoke (instantiate 0 ρ jf.term) (instantiate 0 ρ jr.term)
        ((jas.take k).map (fun p => instantiate 0 ρ p.term) ++ parts.map RestCalls.partTerm) := by
      rw [hargs]
      simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map, Function.comp_def,
        instantiate_spreadTerm, htf, htr, parts]
      congr 2
      apply List.map_congr_left
      intro q _
      rcases q with ⟨_ | _, p⟩ <;> rfl
    rw [hterm]
    have hpart : ∀ q ∈ flags.zip (jas.drop k), if q.1 then SpreadsInto G q.2.type El else q.2.type = El :=
      fun q hq => hparts (q.1, q.2.type) (List.mem_map_of_mem hq)
    apply spread_values_post (E := meaning G El) (meaning_adm G El) (meaning_valOnly G El) hfv hrv
      parts (n+1) W h _
      (by
        intro q hq S hS
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
        rcases q' with ⟨_ | _, p⟩
        · simp at hS
        · simp only [if_true, Option.some.injEq] at hS
          subst hS
          have := hpart _ hq'
          simp only [if_true] at this
          have hm : p ∈ jas := List.mem_of_mem_drop (List.of_mem_zip hq').2
          have hro := hparts0 _ hq'
          simp only [if_true] at hro
          have heΓ : EnvOk G Γ ρ (n+1) W := by simpa [context p (by simp [hm])] using he
          refine ⟨meaning_adm G p.type, spreadsInto_sound this,
            readOperand_instantiate hro (inScope p (by simp [hm])) heΓ, ?_⟩
          intro i hi U hx hu heap' hh'
          exact (typed p (by simp [hm])).sound i U heap' ρ (heΓ.transfer i hi U hx) hu hh')
      hw hh
      (by
        intro a ha
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        exact hfixedv p hp)
      (by
        intro q hq hnone
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
        have hm : q'.2 ∈ jas := List.mem_of_mem_drop (List.of_mem_zip hq').2
        rcases q' with ⟨_ | _, p⟩
        · have hv0 := hparts0 _ hq'
          simp only [Bool.false_eq_true, if_false] at hv0
          have hv := valueOf p (by simp [hm]) hv0
          refine ⟨hv, ?_⟩
          have hA : p.type = El := by simpa using hpart _ hq'
          simpa [hA] using member p (by simp [hm]) hv
        · simp at hnone)
    intro i hi U hx hU hh' extra hex
    have hfU := (CallEffects.restsT_adm _).mono i _ U hx _
      ((CallEffects.restsT_adm _).down_le (n+1) i hi W _ hf)
    have hp := hfU.2 _ (List.mem_singleton_self _)
    have hrU := (meaning_adm G jr.type).mono i _ U hx _
      ((meaning_adm G jr.type).down_le (n+1) i hi W _ (member jr (by simp) hrv))
    have hvals : CallArguments.Values ((jas.take k).map (fun p => instantiate 0 ρ p.term) ++ extra) := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        exact hfixedv p hp
      · exact meaning_valOnly G El i U a (hex a ha)
    have hacc : ArgsRest ((jas.take k).map (fun p => meaning G p.type)) (argMeaning G P) i U
        ((jas.take k).map (fun p => instantiate 0 ρ p.term) ++ extra) :=
      ArgsRest_of_exact_extra
        (ArgsT_transfer (fun T hm => by obtain ⟨p,_,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type)
          hfixed i hi U hx)
        ((restElem_args hel).mpr hex)
    have hs := CallEffects.call_safe (effect := e)
      (P := ArgsRest ((jas.take k).map (fun p => meaning G p.type)) (argMeaning G P))
      (Adm.of_transfer (fun ha j hj U hx => ArgsRest_transfer (fun T hm => by
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type)
        (argMeaning_adm G P) ha j hj U hx))
      (meaning_adm G jr.type)
      (by simpa [CallEffects.RestArrow.mapWith, CallEffects.Contract.map, List.map_map, Function.comp_def] using hp)
      hrU hrv hvals hacc hU hh'
    rw [CallEffects.Effect.result_plain hplain] at hs
    exact hs

/-- **A selected call meets its signature's postcondition**, at its receiver,
from the heap it starts in. -/
theorem selected_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (e : Evidence ι)
    {codes : CodeEntry ι → Bool} (ht : checkTreeUsing G images e codes = true)
    (hp : selectedOperands e = true) {eff : CallEffects.Effect} (hsel : selectedEffect e = some eff)
    (hcodes : CodesSound G codes)
    {ρ n W h} (he : EnvOk G (claim e).context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G (claim e).type) (eff.post (receiverOf (instantiate 0 ρ (claim e).term)) h)
      n W h (instantiate 0 ρ (claim e).term) := by
  cases e with
  | node j r ps =>
    simp only [claim] at he ⊢
    simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
    cases r <;> try simp only [selectedEffect, reduceCtorEq] at hsel
    case app effect =>
      cases hsel
      simp only [selectedOperands] at hp
      refine SafePostExc.post (call_local_sound ht.1 ?_ ?_ he hw hh)
      · intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound e (ht.2 ⟨e,heq⟩ (by simp)) hcodes
      · intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact by simpa only [Bool.and_eq_true] using List.all_eq_true.mp hp e heq
    case callRest effect k u flags P =>
      cases hsel
      simp only [selectedOperands, Bool.and_eq_true, Bool.or_eq_true] at hp
      obtain ⟨hscope, hp⟩ := hp
      have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
        intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound e (ht.2 ⟨e,heq⟩ (by simp)) hcodes
      have inScope : ∀ p ∈ ps.map claim, checkScope p.context.length p.term = true := by
        intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact List.all_eq_true.mp hscope e heq
      rcases hp with hvals | ⟨hsp, hops⟩
      · by_cases hsp : flags.any id = true
        · exact callRestSpread_local_sound ht.1 hsp typed inScope (.inr (by simpa using hvals)) he hw hh
        have hnos : flags.all (· == false) = true := by
          simp only [List.all_eq_true, beq_iff_eq]
          intro b hb
          cases b
          · rfl
          · exact absurd (List.any_eq_true.mpr ⟨true, hb, rfl⟩) hsp
        apply callRest_local_sound ht.1 hnos typed _ he hw hh
        intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact ⟨List.all_eq_true.mp hvals e heq, List.all_eq_true.mp hscope e heq⟩
      · exact callRestSpread_local_sound ht.1 hsp typed inScope (.inl (by simpa using hops)) he hw hh
    case construct effect =>
      cases hsel
      simp only [selectedOperands] at hp
      refine SafePostExc.post (construct_local_sound ht.1 ?_ ?_ he hw hh)
      · intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound e (ht.2 ⟨e,heq⟩ (by simp)) hcodes
      · intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact by simpa only [Bool.and_eq_true] using List.all_eq_true.mp hp e heq
    case sub proof =>
      cases ps with
      | nil => simp [selectedEffect] at hsel
      | cons child rest =>
        cases rest with
        | cons _ _ => simp [selectedEffect] at hsel
        | nil =>
          simp only [selectedEffect] at hsel
          simp only [selectedOperands] at hp
          obtain ⟨hctx,hterm,hsub⟩ := ht.1
          have ih := selected_sound child (ht.2 ⟨child,by simp⟩ (by simp)) hp hsel hcodes
            (ρ := ρ) (n := n) (W := W) (h := h) (by rw [hctx]; exact he) hw hh
          rw [hterm] at ih
          exact consequence (fun j W v hv => PositiveCertificates.acceptedUsing hsub j W v hv)
            (fun _ _ hp => hp) ih
termination_by sizeOf e

theorem selectedCall_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {Φ : Footprints.Closed} (e : Evidence ι)
    {codes : CodeEntry ι → Bool} (ht : checkTreeUsing G images e codes = true)
    (hp : selectedCallWithin Φ e = true) (hcodes : CodesSound G codes)
    {ρ n W h} (he : EnvOk G (claim e).context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G (claim e).type) (fun h' _ => Φ.Holds h h')
      n W h (instantiate 0 ρ (claim e).term) := by
  simp only [selectedCallWithin, Bool.and_eq_true] at hp
  obtain ⟨hops, hp⟩ := hp
  split at hp
  · rename_i eff hsel
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
    obtain ⟨hle, hr⟩ := hp
    apply HeapObservations.weaken (fun h' v hq => ?_) (selected_sound e ht hops hsel hcodes he hw hh)
    rcases hr with hr | hr
    · exact (CallEffects.Effect.within_holds hq.1 hr).mono hle
    · rw [hr]; exact CallEffects.Effect.within_top hq.1
  · cases hp

/-! ### Throws

A node a handler catches, or one in a body stating its footprint on a throw,
must bound the heap its throw leaves too. An inspection keeps the heap's
prefix at every step, a raise included; a typed write raises before it
writes; a call at a selected signature raises within the signature's
footprint where it states `onThrow`. -/

/-- An inspection keeps the input heap as a prefix on every step, so where it
raises too. -/
theorem inspect_safe_exc {T : Fam} {initial : Heap} : ∀ {n W h t},
    initial.IsPrefix h → Purity.inspectTerm t = true → WorldAdm W → HeapOk n W h →
    Safe Ξ T n W h t →
    SafePostExc Ξ T (fun h' _ => Footprints.Closed.empty.Holds initial h')
      (fun h' => Footprints.Closed.empty.Holds initial h') n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hpre hp hw hh hs
    rcases hs with (⟨hv, ht⟩ | hth) | ⟨U, h', t', hx, hu, step, hh', hs⟩
    · exact .inl (.inl ⟨hv, ht, Footprints.Closed.holds_empty.mpr hpre⟩)
    · exact .inl (.inr ⟨hth, Footprints.Closed.holds_empty.mpr hpre⟩)
    · obtain ⟨hprefix, hp'⟩ := Purity.inspect_step step hp (HeapExpressionRules.heap_values hw hh)
      exact .inr ⟨U, h', t', hx, hu, step, hh', ih (hpre.trans hprefix) hp' hu hh' hs⟩

theorem sound_exc {G : NormalGraph ι} {Γ t A ρ n W h}
    (hc : check G Γ t = true) (hscope : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : Safe (excOf G) (meaning G A) n W h (instantiate 0 ρ t)) :
    SafePostExc (excOf G) (meaning G A) (fun h' _ => Footprints.Closed.empty.Holds h h')
      (fun h' => Footprints.Closed.empty.Holds h h') n W h (instantiate 0 ρ t) :=
  inspect_safe_exc (List.prefix_refl h) (inspect_instantiate (d := 0) hc hscope he) hw hh hs

/-- A typed write raises, where it does, before it writes: at its entry
heap. -/
theorem write_within_exc [DecidableEq ι] {G : NormalGraph ι} {Γ Φ t T ρ n W h}
    (hc : writeWithin G Γ Φ t = true) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePostExc Ξ T (fun h' _ => Φ.Holds h h') (fun h' => Φ.Holds h h') n W h (instantiate 0 ρ t) := by
  have hpost := write_within hc he hh hs
  unfold writeWithin at hc
  split at hc
  case h_2 => contradiction
  rename_i f i k hw
  rw [HeapExpressionRules.writeSlots_eq hw] at hpost ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨_, hk⟩, hsel⟩ := hc
  split at hsel
  · rename_i Ref hi
    cases n with
    | zero => trivial
    | succ n =>
      have hiv := (meaning_value (he.2 i Ref hi)).1
      have hkv := (meaning_value (he.2 k Γ[k] (List.getElem?_eq_getElem hk))).1
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hpost ⊢
      rcases hpost with (hv | hr) | ⟨U, h', t', hx, hu, step, hh', hs'⟩
      · exact .inl (.inl hv)
      · exact .inl (.inr ⟨hr, Footprints.Closed.Holds.refl Φ h⟩)
      · obtain ⟨_, _, _, _, _, _, _, rfl, rfl⟩ := HeapExpressionRules.write_inv hiv hkv step
        refine .inr ⟨U, _, _, hx, hu, step, hh', ?_⟩
        cases n with
        | zero => trivial
        | succ m =>
          rcases hs' with (hv | hr) | ⟨_, _, _, _, _, step', _, _⟩
          · exact .inl (.inl hv)
          · exact absurd hr (val_not_thrown rfl)
          · exact False.elim (value_no_step rfl step')
  · contradiction

/-- The selected forms a throw postcondition is concluded for: an invocation
or a construction at a fixed signature, through subsumption. -/
def selectedThrows : Evidence ι → Bool
  | .node _ (.app _) _ => true
  | .node _ (.construct _) _ => true
  | .node _ (.sub _) [p] => selectedThrows p
  | _ => false

/-- **A selected call meets its signature's postconditions** on a normal
return and on a throw, at its receiver, from the heap it starts in. -/
theorem selected_sound_exc [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (e : Evidence ι)
    {codes : CodeEntry ι → Bool} (ht : checkTreeUsing G images e codes = true)
    (hp : selectedOperands e = true) (hthrows : selectedThrows e = true)
    {eff : CallEffects.Effect} (hsel : selectedEffect e = some eff)
    (hcodes : CodesSound G codes)
    {ρ n W h} (he : EnvOk G (claim e).context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePostExc (excOf G) (meaning G (claim e).type) (eff.post (receiverOf (instantiate 0 ρ (claim e).term)) h)
      (eff.excPost (receiverOf (instantiate 0 ρ (claim e).term)) h) n W h (instantiate 0 ρ (claim e).term) := by
  cases e with
  | node j r ps =>
    simp only [claim] at he ⊢
    simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
    cases r <;> try simp only [selectedEffect, reduceCtorEq] at hsel
    case app effect =>
      cases hsel
      simp only [selectedOperands] at hp
      apply call_local_sound ht.1 _ _ he hw hh
      · intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound e (ht.2 ⟨e,heq⟩ (by simp)) hcodes
      · intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact by simpa only [Bool.and_eq_true] using List.all_eq_true.mp hp e heq
    case callRest => simp [selectedThrows] at hthrows
    case construct effect =>
      cases hsel
      simp only [selectedOperands] at hp
      apply construct_local_sound ht.1 _ _ he hw hh
      · intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound e (ht.2 ⟨e,heq⟩ (by simp)) hcodes
      · intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact by simpa only [Bool.and_eq_true] using List.all_eq_true.mp hp e heq
    case sub proof =>
      cases ps with
      | nil => simp [selectedEffect] at hsel
      | cons child rest =>
        cases rest with
        | cons _ _ => simp [selectedEffect] at hsel
        | nil =>
          simp only [selectedEffect] at hsel
          simp only [selectedOperands] at hp
          simp only [selectedThrows] at hthrows
          obtain ⟨hctx,hterm,hsub⟩ := ht.1
          have ih := selected_sound_exc child (ht.2 ⟨child,by simp⟩ (by simp)) hp hthrows hsel hcodes
            (ρ := ρ) (n := n) (W := W) (h := h) (by rw [hctx]; exact he) hw hh
          rw [hterm] at ih
          exact SafePostExc.consequence_below' (fun _ _ _ _ h => h)
            (fun j _ W v hv => PositiveCertificates.acceptedUsing hsub j W v hv)
            (fun _ _ hp => hp) (fun _ hp => hp) ih
termination_by sizeOf e

end Verification.ExpressionEffects
