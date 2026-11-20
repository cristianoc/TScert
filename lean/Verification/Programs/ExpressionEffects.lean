import Verification.Programs.HeapExpressionRules
import Verification.Semantics.ForgetActuals

/-! Definition-side effect checks over lowered expressions. Safety comes from
ordinary evidence; this layer establishes the additional heap postcondition. -/
namespace Verification.ExpressionEffects
variable {ε : Verification.HeapKnowledge.EntryState}
open ProgramTyping ProgramCertificates PositiveGraphs PositiveRules HeapObservations

/-- The receiver of an invocation, and `undefined` for any other term: what a
selected signature's postcondition is relative to. -/
def receiverOf : Tm → Tm
  | .invoke _ r _ => r
  | _ => .undef

/-- A call's or a construction's actuals. -/
def actualsOf : Tm → List Tm
  | .invoke _ _ args => args
  | .construct _ args => args
  | _ => []

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
  | zero => intros; assumption
  | succ n ih =>
    intro W h t hpre hp hw hh hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
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
  inspect_safe (List.prefix_refl h) (HeapExpressionRules.inspect_instantiate (d := 0) hc hscope he) hw hh hs

/-- A type every member of which is a source value: no spine and no `top`. -/
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
    | some B => B.any (fun p => decide (p.1 = fld)) && B.all (fun p => !decide (p.1 = fld) || sourceTy G p.2.2)
    | none => false

theorem sourceField_sound [DecidableEq ι] {G : NormalGraph ι} {Ref fld n W v}
    (hr : sourceField G (expand G Ref) fld = true) (hv : meaning G Ref n W v) :
    ∃ B s A, (fld, s, A) ∈ B ∧ sourceTy G A = true ∧
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
    obtain ⟨⟨g, s, El⟩, hmem, hg⟩ := List.any_eq_true.mp hany
    simp only [decide_eq_true_eq] at hg
    subst hg
    have hsrc : sourceTy G El = true := (hall _ hmem).resolve_left (by simp)
  · exact ⟨_, s, El, hmem, hsrc, recT_bag hc.1.1⟩
  · exact ⟨_, s, El, hmem, hsrc, hc.1.1.1.1⟩

/-- A type every member of which is neither an object nor a spine
(`PositiveNormalization.scalarClause`). -/
def scalarTy (G : NormalGraph ι) (A : Ty ι) : Bool :=
  G.plainTy A && (expand G A).all PositiveNormalization.scalarClause

theorem scalarTy_sound {G : NormalGraph ι} {A n W v} (hs : scalarTy G A = true)
    (hv : meaning G A n W v) : Footprints.isObj v = false ∧ Footprints.isArr v = false := by
  simp only [scalarTy, Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨c, hc, hcv⟩ := (expand_sem G A hs.1 n W v).mp hv
  have := PositiveNormalization.scalarClause_sound (hs.2 c hc) hcv.1
  cases v <;> simp_all [Footprints.isObj, Footprints.isArr]

/-- Whether every alternative is a record whose first invariant operand has
the field `fld`, at a type of primitives in each (`scalarTy`). -/
def scalarField (G : NormalGraph ι) (cs : List (PositiveNormalization.Clause (Ty ι))) (fld : PropKey) : Bool :=
  !cs.isEmpty && cs.all fun c => match HeapExpressionRules.clauseBagOperand c with
    | some B => B.any (fun p => decide (p.1 = fld)) && B.all (fun p => !decide (p.1 = fld) || scalarTy G p.2.2)
    | none => false

theorem scalarField_sound [DecidableEq ι] {G : NormalGraph ι} {Ref fld n W v}
    (hr : scalarField G (expand G Ref) fld = true) (hv : meaning G Ref n W v) :
    ∃ B s A, (fld, s, A) ∈ B ∧ scalarTy G A = true ∧
      bagT (ReferenceConjunctions.famsOf (meaning G) B) n W v := by
  simp only [scalarField, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
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
    obtain ⟨⟨g, s, El⟩, hmem, hg⟩ := List.any_eq_true.mp hany
    simp only [decide_eq_true_eq] at hg
    subst hg
    have hsrc : scalarTy G El = true := (hall _ hmem).resolve_left (by simp)
  · exact ⟨_, s, El, hmem, hsrc, recT_bag hc.1.1⟩
  · exact ⟨_, s, El, hmem, hsrc, hc.1.1.1.1⟩

/-- **The contents of a primitive field are no object**: in a heap meeting
its world at a positive budget, the location of the field `f` of an object
whose type gives `f` a type of primitives holds neither an object nor a
spine. -/
theorem scalarField_contents [DecidableEq ι] {G : NormalGraph ι} {Ref : Ty ι} {f : PropKey} {n : Nat}
    {W : WorldT (n + 1)} {h : Heap} {flds : List (PropKey × Nat)} {c : CallCode} {oid l : Nat} {v : Val}
    (hsel : scalarField G (expand G Ref) f = true) (hm : meaning G Ref (n + 1) W (.objAt flds c oid))
    (hh : HeapOk (n + 1) W h) (hfd : flds.lookup f = some l) (hv : h[l]? = some v) :
    Footprints.isObj v = false ∧ Footprints.isArr v = false := by
  obtain ⟨B, _, A, hmem, hsc, hbag⟩ := scalarField_sound hsel hm
  obtain ⟨flds0, code0, oid0, hl0, _, hrec⟩ := hbag
  obtain ⟨flds1, l1, c1, oid', hproj, hfd1, hlookup, hagree⟩ :=
    recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hmem, rfl⟩) hrec
  cases hl0
  cases hproj
  rw [hfd] at hfd1
  cases hfd1
  obtain ⟨u, hu, hmm⟩ := hh.1.2 l c1 hlookup
  rw [hv] at hu
  cases hu
  exact scalarTy_sound hsc ((hagree 0 (by omega) _ v).mp (hmm 0 (by omega)))

/-- A field write whose field and written value are primitives: the write
of a field of the object in slot `i` whose type gives the field a type of
primitives, of the value of a slot of a type of source values. Its old and
new contents are neither objects nor spines, so it is a scalar's step. -/
def scalarWrite (G : NormalGraph ι) (Γ : List (Ty ι)) (t : Tm) : Bool :=
  match HeapExpressionRules.writeSlots t with
  | some (f, i, k) => (match Γ[k]? with
      | some B => sourceTy G B
      | none => false) &&
      match Γ[i]? with
      | some Ref => scalarField G (expand G Ref) f
      | none => false
  | none => false

/-- **A field write's frame** (the note *Tolerant frames*, Field-Write,
`{x.f: any}`): the location of field `f` of the object in slot `i`. -/
def fieldWriteFrame (i : Nat) (f : PropKey) : Footprints.Footprint := [(.field i f, .any)]

/-- The slot and the field a typed field write writes: a write of a field of
the object in a slot whose type gives it a type of source values. -/
def fieldWriteStep (G : NormalGraph ι) (Γ : List (Ty ι)) (t : Tm) : Option (Nat × PropKey) :=
  match HeapExpressionRules.writeSlots t with
  | some (f, i, k) => if decide (k < Γ.length) && (match Γ[i]? with
      | some Ref => sourceField G (expand G Ref) f
      | none => false) then some (i, f) else none
  | none => none

/-- A typed field write within the closed bound `Φ`: its frame's closed
weakening, `{value: any, spine: keep}` (`fieldWriteFrame_closed`), or
`{value: scalar, spine: keep}` where it is a scalar write
(`scalarWrite_closed`), within `Φ`. -/
def fieldWriteWithin (G : NormalGraph ι) (Γ : List (Ty ι)) (Φ : Footprints.Closed) (t : Tm) : Bool :=
  (fieldWriteStep G Γ t).isSome && (Footprints.Closed.le ⟨.any, .keep, .keep⟩ Φ ||
    scalarWrite G Γ t && Footprints.Closed.le ⟨.scalar, .keep, .keep⟩ Φ)

/-- **The closed bound of a field write is a weakening of its frame**: where
every location the frame names holds a value of no spine, `{x.f: any}` is
within `{value: any, spine: keep}`. -/
theorem fieldWriteFrame_closed {i : Nat} {f : PropKey} {ρ : Env} {h h' : Heap}
    (hp : Footprints.Post (fieldWriteFrame i f) ρ h h')
    (hv : ∀ l v, (Footprints.Region.field i f).mem ρ h l = true → h[l]? = some v → Footprints.isArr v = false) :
    Footprints.Closed.Holds ⟨.any, .keep, .keep⟩ h h' := by
  rw [Footprints.Closed.holds_iff]
  refine ⟨hp.1, fun l v hl => ?_⟩
  obtain ⟨v', hl', ha⟩ := hp.2 l v hl
  refine ⟨v', hl', ?_⟩
  rcases ha with rfl | ⟨e, he, hm, -⟩
  · exact Footprints.Change.Holds.refl _ _ _
  · simp only [fieldWriteFrame, List.mem_singleton] at he
    subst he
    simp only [Footprints.Closed.at, hv l v hm hl]
    trivial

/-- The value a write's term writes. -/
def writtenValueOf : Tm → Tm
  | .writeAt _ _ v => v
  | _ => .undef

/-- What a typed field write leaves: its frame `{x.f: any}`, the location it
writes holding a value of no spine before it, and the written value `a`
after it (the note's Field-Write, `x.f ≐ a`). -/
def FieldWritten (i : Nat) (f : PropKey) (a : Tm) (ρ : Env) (h h' : Heap) : Prop :=
  Footprints.Post (fieldWriteFrame i f) ρ h h' ∧
    (∀ l v, (Footprints.Region.field i f).mem ρ h l = true → h[l]? = some v → Footprints.isArr v = false) ∧
    ∀ l, (Footprints.Region.field i f).mem ρ h l = true → h'[l]? = some a

/-- **A typed field write is within its frame**, and leaves its field
holding the written value, on normal return. -/
theorem fieldWriteStep_post [DecidableEq ι] {G : NormalGraph ι} {Γ t T ρ n W h} {i : Nat} {f : PropKey}
    (hc : fieldWriteStep G Γ t = some (i, f)) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' _ => FieldWritten i f (instantiate 0 ρ (writtenValueOf t)) ρ h h') n W h
      (instantiate 0 ρ t) := by
  unfold fieldWriteStep at hc
  split at hc
  case h_2 => cases hc
  rename_i f' i' k hw
  by_cases hcond : (decide (k < Γ.length) && match Γ[i']? with
      | some Ref => sourceField G (expand G Ref) f'
      | none => false) = true
  case neg => rw [if_neg hcond] at hc; cases hc
  rw [if_pos hcond] at hc
  cases hc
  rw [HeapExpressionRules.writeSlots_eq hw] at hs ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨hk, hsel⟩ := hcond
  split at hsel
  · rename_i Ref hi
    cases n with
    | zero => assumption
    | succ n =>
      have hiv := (meaning_value (he.2 i Ref hi)).1
      have hkv := (meaning_value (he.2 k Γ[k] (List.getElem?_eq_getElem hk))).1
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
      obtain ⟨hrf, hs⟩ := hs
      refine ⟨hrf, ?_⟩
      rcases hs with (⟨hbad, _⟩ | hr) | ⟨U, h', t', hx, hu, step, hh', hs'⟩
      · simp [isVal] at hbad
      · exact .inl (.inr hr)
      · obtain ⟨flds, c, oid, l, hl, hfd, hlt, rfl, rfl⟩ := HeapExpressionRules.write_inv hiv hkv step
        -- The written location holds a source value, of no spine.
        have harr : ∀ v, h[l]? = some v → Footprints.isArr v = false := by
          intro v hv
          obtain ⟨B, _, A, hmem, hsrc, hbag⟩ := sourceField_sound hsel (he.2 i Ref hi)
          obtain ⟨flds0, code0, oid0, hl0, _, hrec⟩ := hbag
          obtain ⟨flds1, l1, c1, oid', hproj, hfd1, hlookup, hagree⟩ :=
            recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hmem, rfl⟩) hrec
          rw [hl0] at hl
          cases hl
          cases hproj
          rw [hfd] at hfd1
          cases hfd1
          obtain ⟨u, hu, hmm⟩ := hh.1.2 l c1 hlookup
          rw [hv] at hu
          cases hu
          have hA := (hagree 0 (by omega) _ v).mp (hmm 0 (by omega))
          have := sourceTy_sound hsrc hA
          cases v <;> simp_all [isSourceVal, Footprints.isArr]
        have hmem : ∀ l', (Footprints.Region.field i f).mem ρ h l' = true → l' = l := by
          intro l' hm
          simp only [Footprints.Region.mem, hl, Footprints.fieldsOf, hfd, beq_iff_eq, Option.some.injEq] at hm
          exact hm.symm
        refine .inr ⟨U, _, _, hx, hu, step, hh', HeapObservations.refine_value rfl ?_ hs'⟩
        refine ⟨⟨by simp, fun l' v hv => ?_⟩, fun l' v hm hv => by rw [hmem l' hm] at hv; exact harr v hv,
          fun l' hm => by rw [hmem l' hm]; simp [writtenValueOf, instantiate, hlt]⟩
        by_cases hll : l' = l
        · subst hll
          refine ⟨ρ k, by simp [hlt], .inr ⟨_, List.mem_singleton_self _, ?_, trivial⟩⟩
          simp [Footprints.Region.mem, hl, Footprints.fieldsOf, hfd]
        · exact ⟨v, by rw [List.getElem?_set_ne (Ne.symm hll)]; exact hv, .inl rfl⟩
  · cases hsel

/-- **A typed field write is within its frame** `{x.f: any}` and leaves
`x.f ≐ a` on normal return, and raises, where it does, before it writes:
at its entry heap. -/
theorem fieldWriteStep_sound [DecidableEq ι] {G : NormalGraph ι} {Γ t T ρ n W h} {i : Nat} {f : PropKey}
    (hc : fieldWriteStep G Γ t = some (i, f)) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePostExc Ξ T (fun h' _ => FieldWritten i f (instantiate 0 ρ (writtenValueOf t)) ρ h h') (fun h' => h' = h)
      n W h (instantiate 0 ρ t) := by
  have hpost := fieldWriteStep_post hc he hh hs
  unfold fieldWriteStep at hc
  split at hc
  case h_2 => cases hc
  rename_i f' i' k hw
  by_cases hcond : (decide (k < Γ.length) && match Γ[i']? with
      | some Ref => sourceField G (expand G Ref) f'
      | none => false) = true
  case neg => rw [if_neg hcond] at hc; cases hc
  rw [if_pos hcond] at hc
  cases hc
  rw [HeapExpressionRules.writeSlots_eq hw] at hpost ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨hk, hsel⟩ := hcond
  split at hsel
  · rename_i Ref hi
    cases n with
    | zero => assumption
    | succ n =>
      have hiv := (meaning_value (he.2 i Ref hi)).1
      have hkv := (meaning_value (he.2 k Γ[k] (List.getElem?_eq_getElem hk))).1
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hpost ⊢
      obtain ⟨hrf, hpost⟩ := hpost
      refine ⟨hrf, ?_⟩
      rcases hpost with (hv | hr) | ⟨U, h', t', hx, hu, step, hh', hs'⟩
      · exact .inl (.inl hv)
      · exact .inl (.inr ⟨hr, rfl⟩)
      · obtain ⟨_, _, _, _, _, _, _, rfl, rfl⟩ := HeapExpressionRules.write_inv hiv hkv step
        refine .inr ⟨U, _, _, hx, hu, step, hh', ?_⟩
        cases n with
        | zero => assumption
        | succ m =>
          obtain ⟨hrf, hs'⟩ := hs'
          refine ⟨hrf, ?_⟩
          rcases hs' with (hv | hr) | ⟨_, _, _, _, _, step', _, _⟩
          · exact .inl (.inl hv)
          · exact absurd hr (val_not_thrown rfl)
          · exact False.elim (value_no_step rfl step')
  · cases hsel

/-- **A scalar write's frame at a scalar's step**: a typed field write
that is a scalar write (`scalarWrite`) changes its field by a scalar's step,
`{x.f: scalar}`, on normal return, and raises, where it does, before it
writes. -/
theorem scalarWrite_sound [DecidableEq ι] {G : NormalGraph ι} {Γ t T ρ n W h} {i : Nat} {f : PropKey}
    (hc : fieldWriteStep G Γ t = some (i, f)) (hw : scalarWrite G Γ t = true) (he : EnvOk G Γ ρ n W)
    (hh : HeapOk n W h) (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePostExc Ξ T (fun h' _ => Footprints.Post [(.field i f, .scalar)] ρ h h') (fun h' => h' = h)
      n W h (instantiate 0 ρ t) := by
  have hsound := fieldWriteStep_sound hc he hh hs
  unfold fieldWriteStep at hc
  split at hc
  case h_2 => cases hc
  rename_i f' i' k hws
  by_cases hcond : (decide (k < Γ.length) && match Γ[i']? with
      | some Ref => sourceField G (expand G Ref) f'
      | none => false) = true
  case neg => rw [if_neg hcond] at hc; cases hc
  rw [if_pos hcond] at hc
  cases hc
  simp only [scalarWrite, hws, Bool.and_eq_true] at hw
  obtain ⟨hsk, hsc⟩ := hw
  split at hsk
  case h_2 => cases hsk
  rename_i B hkB
  split at hsc
  case h_2 => cases hsc
  rename_i Ref hiR
  cases n with
  | zero => exact hs
  | succ n =>
    refine SafePostExc.weaken (fun h' _ hq => ⟨hq.1.1, fun l v hv => ?_⟩) (fun _ hq => hq) hsound
    obtain ⟨v', hv', ha⟩ := hq.1.2 l v hv
    refine ⟨v', hv', ?_⟩
    rcases ha with rfl | ⟨e, he', hm, -⟩
    · exact .inl rfl
    · simp only [fieldWriteFrame, List.mem_singleton] at he'
      subst he'
      refine .inr ⟨_, List.mem_singleton_self _, hm, .inr ?_⟩
      have hm' := hm
      simp only [Footprints.Region.mem, beq_iff_eq] at hm'
      cases hρ : ρ i with
      | objAt flds c oid =>
        rw [hρ] at hm'
        have hiv := he.2 i Ref hiR
        rw [hρ] at hiv
        obtain ⟨hobj, harr⟩ := scalarField_contents hsc hiv hh (by simpa [Footprints.fieldsOf] using hm') hv
        have hnew := hq.2.2 l hm
        rw [hv'] at hnew
        cases hnew
        have hsrc := sourceTy_sound hsk (he.2 k B hkB)
        rw [HeapExpressionRules.writeSlots_eq hws]
        simp only [writtenValueOf, instantiate]
        have hk : k < Γ.length := (List.getElem?_eq_some_iff.mp hkB).1
        refine ⟨hobj, harr, ?_⟩
        cases hx : ρ k <;> simp_all [isSourceVal, Footprints.isArr]
      | _ => rw [hρ] at hm'; simp [Footprints.fieldsOf] at hm'

/-- **A scalar write's closed bound**: where every location its frame names
holds a value of no spine, `{x.f: scalar}` is within `{value: scalar, spine:
keep}`. -/
theorem scalarWriteFrame_closed {i : Nat} {f : PropKey} {ρ : Env} {h h' : Heap}
    (hp : Footprints.Post [(.field i f, .scalar)] ρ h h') :
    Footprints.Closed.Holds ⟨.scalar, .keep, .keep⟩ h h' := by
  rw [Footprints.Closed.holds_iff]
  refine ⟨hp.1, fun l v hl => ?_⟩
  obtain ⟨v', hl', ha⟩ := hp.2 l v hl
  refine ⟨v', hl', ?_⟩
  rcases ha with rfl | ⟨e, he, hm, hc⟩
  · exact Footprints.Change.Holds.refl _ _ _
  · simp only [List.mem_singleton] at he
    subst he
    rcases hc with rfl | hst
    · exact Footprints.Change.Holds.refl _ _ _
    · simp only [Footprints.Closed.at, hst.2.1]
      exact .inr hst

/-- **A typed field write is within `{value: any, spine: keep}`**: its
frame's closed weakening (`fieldWriteFrame_closed`); a scalar write is within
`{value: scalar, spine: keep}` (`scalarWriteFrame_closed`). -/
theorem field_write_within_exc [DecidableEq ι] {G : NormalGraph ι} {Γ Φ t T ρ n W h}
    (hc : fieldWriteWithin G Γ Φ t = true) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePostExc Ξ T (fun h' _ => Φ.Holds h h') (fun h' => Φ.Holds h h') n W h (instantiate 0 ρ t) := by
  simp only [fieldWriteWithin, Bool.and_eq_true, Bool.or_eq_true, Option.isSome_iff_exists] at hc
  obtain ⟨⟨⟨i, f⟩, hi⟩, hle | ⟨hsw, hle⟩⟩ := hc
  · exact SafePostExc.weaken (fun _ _ hq => Footprints.Closed.Holds.mono hle (fieldWriteFrame_closed hq.1 hq.2.1))
      (fun _ hq => by rw [hq]; exact Footprints.Closed.Holds.refl Φ h) (fieldWriteStep_sound hi he hh hs)
  · exact SafePostExc.weaken (fun _ _ hq => Footprints.Closed.Holds.mono hle (scalarWriteFrame_closed hq))
      (fun _ hq => by rw [hq]; exact Footprints.Closed.Holds.refl Φ h) (scalarWrite_sound hi hsw he hh hs)

theorem field_write_within [DecidableEq ι] {G : NormalGraph ι} {Γ Φ t T ρ n W h}
    (hc : fieldWriteWithin G Γ Φ t = true) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' _ => Φ.Holds h h') n W h (instantiate 0 ρ t) :=
  SafePostExc.post (field_write_within_exc hc he hh hs)

/-! ### Initializing writes

`x ??= e` writes its location only where it holds `null` or `undefined`
(PROGRAM-TYPING.md, "Frame conditions"): where the knowledge at a field write
states its location so, the write is within `{value: init, spine: keep}`. -/

/-- `null` and `undefined`. -/
def nullishSet : ValueSets.ValueSet := { nul := true, undef := true }

theorem nullishSet_mem {v : Tm} (h : nullishSet.mem v = true) : Footprints.nullish v = true := by
  cases v <;> simp_all [nullishSet, ValueSets.ValueSet.mem, ValueSets.Obj.mem, Footprints.nullish]

/-- Whether the knowledge states that field `f` of slot `i`'s object holds
`null` or `undefined`: a cell fact of it, or a read link from it to a slot a
value fact bounds so. -/
def nullishAt (k : HeapKnowledge.Knowledge) (i : Nat) (f : PropKey) : Bool :=
  k.cells.any (fun c => c.slot == i && c.field == f && c.contents.le nullishSet) ||
  k.links.any (fun g => !g.alias && !g.optional && g.cell == i && g.field == f &&
    k.values.any fun c => c.slot == g.value && c.contents.le nullishSet)

theorem nullishAt_sound {k : HeapKnowledge.Knowledge} {i : Nat} {f : PropKey} {ρ : Env} {h : Heap}
    {flds : List (PropKey × Nat)} {c : CallCode} {oid l : Nat}
    (hn : nullishAt k i f = true) (hk : HeapKnowledge.Holds k ε ρ h)
    (hi : ρ i = .objAt flds c oid) (hl : flds.lookup f = some l) :
    ∃ v, h[l]? = some v ∧ Footprints.nullish v = true := by
  simp only [nullishAt, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hn
  rcases hn with ⟨a, ha, ⟨hs, hf⟩, hle⟩ | ⟨g, hg, ⟨⟨⟨⟨hal, hop⟩, hc⟩, hf⟩, ⟨a, ha, hs, hle⟩⟩⟩
  · obtain ⟨flds', c', oid', v, hρ, hr, hm⟩ := hk.1 a ha
    rw [hs, hi] at hρ
    cases hρ
    rw [hf] at hr
    simp only [HeapFacts.ReadGave, hl] at hr
    exact ⟨v, hr, nullishSet_mem (ValueSets.ValueSet.le_sound hle hm)⟩
  · have hlink := hk.2.2.1 g hg
    simp only [hal, hop] at hlink
    obtain ⟨flds', c', oid', l', hρ, hl', hv⟩ := hlink
    rw [hc, hi] at hρ
    cases hρ
    rw [hf, hl] at hl'
    cases hl'
    have hm := hk.2.1 a ha
    rw [hs] at hm
    exact ⟨_, hv, nullishSet_mem (ValueSets.ValueSet.le_sound hle hm)⟩

/-- A write of a source value to a field whose location the knowledge states
holds `null` or `undefined`. -/
def initWriteWithin (G : NormalGraph ι) (Γ : List (Ty ι)) (k : HeapKnowledge.Knowledge)
    (Φ : Footprints.Closed) (t : Tm) : Bool :=
  match HeapExpressionRules.writeSlots t with
  | some (f, i, j) => Footprints.Closed.le ⟨.init, .keep, .keep⟩ Φ && nullishAt k i f &&
      (match Γ[j]? with
      | some B => sourceTy G B
      | none => false) &&
      match Γ[i]? with
      | some Ref => sourceField G (expand G Ref) f
      | none => false
  | none => false

/-- **An initializing write is within `{value: init, spine: keep}`.** -/
theorem init_write_within [DecidableEq ι] {G : NormalGraph ι} {Γ k Φ t T ρ n W h}
    (hc : initWriteWithin G Γ k Φ t = true) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hk : HeapKnowledge.Holds k ε ρ h) (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' _ => Φ.Holds h h') n W h (instantiate 0 ρ t) := by
  unfold initWriteWithin at hc
  split at hc
  case h_2 => contradiction
  rename_i f i j hw
  rw [HeapExpressionRules.writeSlots_eq hw] at hs ⊢
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hle, hnul⟩, hsrcj⟩, hsel⟩ := hc
  split at hsrcj
  case h_2 => contradiction
  rename_i B hjB
  split at hsel
  · rename_i Ref hi
    cases n with
    | zero => assumption
    | succ n =>
      have hiv := (meaning_value (he.2 i Ref hi)).1
      have hjm := he.2 j B hjB
      have hjv := (meaning_value hjm).1
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
      obtain ⟨hrf, hs⟩ := hs
      refine ⟨hrf, ?_⟩
      rcases hs with (⟨hbad, _⟩ | hr) | ⟨U, h', t', hx, hu, step, hh', hs'⟩
      · simp [isVal] at hbad
      · exact .inl (.inr hr)
      · obtain ⟨flds, c, oid, l, hl, hfd, hlt, rfl, rfl⟩ := HeapExpressionRules.write_inv hiv hjv step
        obtain ⟨u, hu0, hun⟩ := nullishAt_sound hnul hk hl hfd
        refine .inr ⟨U, _, _, hx, hu, step, hh', HeapObservations.refine_value rfl ?_ hs'⟩
        apply Footprints.Closed.Holds.mono hle
        rw [Footprints.Closed.holds_iff]
        refine ⟨by simp, fun l' v hv => ?_⟩
        by_cases hll : l' = l
        · subst hll
          rw [hu0] at hv
          cases hv
          refine ⟨ρ j, by simp [hlt], ?_⟩
          have harr : Footprints.isArr (ρ j) = false := by
            have := sourceTy_sound hsrcj hjm
            cases hjj : ρ j <;> simp_all [isSourceVal, Footprints.isArr]
          have hold : Footprints.isArr u = false := by
            cases u <;> simp_all [Footprints.nullish, Footprints.isArr]
          simp only [Footprints.Closed.at, hold]
          exact .inr ⟨hun, harr⟩
        · exact ⟨v, by rw [List.getElem?_set_ne (Ne.symm hll)]; exact hv, Footprints.Change.Holds.refl _ _ _⟩
  · contradiction

/-- An initializing write raises, where it does, before it writes. -/
theorem init_write_within_exc [DecidableEq ι] {G : NormalGraph ι} {Γ k Φ t T ρ n W h}
    (hc : initWriteWithin G Γ k Φ t = true) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hk : HeapKnowledge.Holds k ε ρ h) (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePostExc Ξ T (fun h' _ => Φ.Holds h h') (fun h' => Φ.Holds h h') n W h (instantiate 0 ρ t) := by
  have hpost := init_write_within hc he hh hk hs
  unfold initWriteWithin at hc
  split at hc
  case h_2 => contradiction
  rename_i f i j hw
  rw [HeapExpressionRules.writeSlots_eq hw] at hpost ⊢
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨_, hsrcj⟩, hsel⟩ := hc
  split at hsrcj
  case h_2 => contradiction
  rename_i B hjB
  split at hsel
  · rename_i Ref hi
    cases n with
    | zero => assumption
    | succ n =>
      have hiv := (meaning_value (he.2 i Ref hi)).1
      have hjv := (meaning_value (he.2 j B hjB)).1
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hpost ⊢
      obtain ⟨hrf, hpost⟩ := hpost
      refine ⟨hrf, ?_⟩
      rcases hpost with (hv | hr) | ⟨U, h', t', hx, hu, step, hh', hs'⟩
      · exact .inl (.inl hv)
      · exact .inl (.inr ⟨hr, Footprints.Closed.Holds.refl Φ h⟩)
      · obtain ⟨_, _, _, _, _, _, _, rfl, rfl⟩ := HeapExpressionRules.write_inv hiv hjv step
        refine .inr ⟨U, _, _, hx, hu, step, hh', ?_⟩
        cases n with
        | zero => assumption
        | succ m =>
          obtain ⟨hrf, hs'⟩ := hs'
          refine ⟨hrf, ?_⟩
          rcases hs' with (hv | hr) | ⟨_, _, _, _, _, step', _, _⟩
          · exact .inl (.inl hv)
          · exact absurd hr (val_not_thrown rfl)
          · exact False.elim (value_no_step rfl step')
  · contradiction

/-- A spread's operand: a value, or a field read of one, the spine a spread
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

/-- **The exits a call's evidence selects** (the note's Call, then
consequence): the selected signature's specification for an invocation, a
construction and a variadic invocation without a spread, all instantiated at
the evaluated actuals; for a variadic invocation with a spread, whose
expanded actuals are not known where the guarantee is consumed, the
specification with what it states of the actuals forgotten
(`Exits.forgetActuals`); through subsumption. -/
def selectedExits : Evidence ι → Option (CallEffects.Exits CallEffects.ExitSchema)
  | .node _ (.app e) _ => some e.schema
  | .node _ (.callRest e _ _ flags _) _ => some (if flags.any id then e.schema.forgetActuals else e.schema)
  | .node _ (.construct e) _ => some e.schema
  | .node _ (.sub _) [p] => selectedExits p
  | _ => none

/-- The signature the deciders read of a call's evidence: the selected
signature, and for a variadic invocation with a spread the signature
without what it states of the actuals (`Effect.withoutActuals`), whose exits
are the selected ones (`selectedExits_entails`); through subsumption. -/
def selectedEffect : Evidence ι → Option CallEffects.Effect
  | .node _ (.app e) _ => some e
  | .node _ (.callRest e _ _ flags _) _ => some (if flags.any id then e.withoutActuals else e)
  | .node _ (.construct e) _ => some e
  | .node _ (.sub _) [p] => selectedEffect p
  | _ => none

/-- **The selected exits entail the signature the deciders read**, on both
exits, at every call. -/
theorem selectedExits_entails (e : Evidence ι) {x : CallEffects.Exits CallEffects.ExitSchema}
    {eff : CallEffects.Effect} (hx : selectedExits e = some x) (he : selectedEffect e = some eff)
    {c : CallEffects.Completion} {r : Tm} {args : List Tm} {s s' : TolerantFrames.IndexedHeap} {v : Tm}
    (hp : x.exitPost c r args s s' v) : eff.schema.exitPost c r args s s' v := by
  cases e with
  | node j rule ps =>
    cases rule <;> try simp only [selectedExits, reduceCtorEq] at hx
    case app => simp only [selectedEffect, Option.some.injEq] at hx he; subst hx he; exact hp
    case construct => simp only [selectedEffect, Option.some.injEq] at hx he; subst hx he; exact hp
    case callRest effect k u flags P =>
      simp only [selectedEffect, Option.some.injEq] at hx he
      subst hx he
      by_cases hsp : flags.any id = true
      · rw [if_pos hsp] at hp ⊢
        exact hp
      · rw [if_neg hsp] at hp ⊢
        exact hp
    case sub =>
      cases ps with
      | nil => simp [selectedExits] at hx
      | cons child rest =>
        cases rest with
        | cons _ _ => simp [selectedExits] at hx
        | nil =>
          simp only [selectedExits, selectedEffect] at hx he
          exact selectedExits_entails child hx he hp
termination_by sizeOf e

/-- A call's evidence selecting a signature selects exits. -/
theorem selectedExits_of_effect (e : Evidence ι) {eff : CallEffects.Effect} (he : selectedEffect e = some eff) :
    ∃ x, selectedExits e = some x := by
  cases e with
  | node j rule ps =>
    cases rule <;> try simp only [selectedEffect, reduceCtorEq] at he
    case app => exact ⟨_, rfl⟩
    case construct => exact ⟨_, rfl⟩
    case callRest => exact ⟨_, rfl⟩
    case sub =>
      cases ps with
      | nil => simp [selectedEffect] at he
      | cons child rest =>
        cases rest with
        | cons _ _ => simp [selectedEffect] at he
        | nil =>
          simp only [selectedEffect] at he
          simpa only [selectedExits] using selectedExits_of_effect child he
termination_by sizeOf e

/-- A selected call's operands. All actual evaluation has already been
lowered to earlier graph nodes; omitted arguments are the ordinary evidence's
explicit `undefined` premises; a variadic call's spreads read their operands'
spines in place. Subsumption may retain the postcondition while changing the
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
within the bound when the closed bound of its normal exit's frame
(`Footprint.close`) is. -/
def selectedCallWithin (Φ : Footprints.Closed) (e : Evidence ι) : Bool :=
  selectedOperands e && match selectedEffect e with
    | some eff => (eff.schema.normal.frame.close).le Φ
    | none => false

theorem argument_values [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {Γ : List (Ty ι)}
    {ps : List (Sequent ι)} {ρ n W h}
    (ht : ∀ p ∈ ps, HasTyUsing G images Γ p.term p.type)
    (hv : ∀ p ∈ ps, isVal (instantiate 0 ρ p.term) = true)
    (he : EnvOk G Γ ρ (n+1) W) (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hr : ∀ p ∈ ps, RefsOk W (instantiate 0 ρ p.term)) :
    ArgsT (ps.map (fun p => meaning G p.type)) (n+1) W (ps.map (fun p => instantiate 0 ρ p.term)) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨safe_value_mem (hv p (by simp)) ((ht p (by simp)).sound _ _ h ρ he hw hh (hr p (by simp))),
      ih (fun p hp => ht p (by simp [hp])) (fun p hp => hv p (by simp [hp])) (fun p hp => hr p (by simp [hp]))⟩

/-- **A call's premises refer to what the call does**: the callee, the
receiver, each actual, and `undefined` at each omitted position. -/
theorem invoke_refs {n : Nat} {W : WorldT n} {ρ : Env} {f r : Tm} {args : List Tm}
    {jf jr : Sequent ι} {jas : List (Sequent ι)} (htf : jf.term = f) (htr : jr.term = r)
    (hargs : (jas.take args.length).map Sequent.term = args)
    (hundef : ∀ ja ∈ jas.drop args.length, ja.term = .undef)
    (href : RefsOk W (instantiate 0 ρ (.invoke f r args))) :
    ∀ p ∈ jf::jr::jas, RefsOk W (instantiate 0 ρ p.term) := by
  obtain ⟨hfr, hrr, har⟩ := RefsOk_invoke.mp (by simpa [instantiate, instantiateArgs_eq_map] using href)
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · rw [htf]; exact hfr
  · rw [htr]; exact hrr
  · rcases List.mem_append.mp (by rwa [List.take_append_drop] : p ∈ jas.take args.length ++ jas.drop args.length)
      with hp' | hp'
    · have hm : p.term ∈ args := by rw [← hargs]; exact List.mem_map_of_mem hp'
      exact har _ (List.mem_map_of_mem hm)
    · rw [hundef p hp']; exact RefsOk_undef

/-- **A construction's premises refer to what it does**: the constructor,
each actual, and `undefined` at each omitted position. -/
theorem construct_refs {n : Nat} {W : WorldT n} {ρ : Env} {f : Tm} {args : List Tm}
    {jf : Sequent ι} {jas : List (Sequent ι)} (htf : jf.term = f)
    (hargs : (jas.take args.length).map Sequent.term = args)
    (hundef : ∀ ja ∈ jas.drop args.length, ja.term = .undef)
    (href : RefsOk W (instantiate 0 ρ (.construct f args))) :
    ∀ p ∈ jf::jas, RefsOk W (instantiate 0 ρ p.term) := by
  obtain ⟨hfr, har⟩ := RefsOk_construct.mp (by simpa [instantiate, instantiateArgs_eq_map] using href)
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · rw [htf]; exact hfr
  · rcases List.mem_append.mp (by rwa [List.take_append_drop] : p ∈ jas.take args.length ++ jas.drop args.length)
      with hp' | hp'
    · have hm : p.term ∈ args := by rw [← hargs]; exact List.mem_map_of_mem hp'
      exact har _ (List.mem_map_of_mem hm)
    · rw [hundef p hp']; exact RefsOk_undef

/-- The local call rule admits a signature with a precondition only where
asked to. -/
theorem app_requires_none [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {ps : List (Sequent ι)} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {e : CallEffects.Effect} (hl : LocalUsing G images j (.app e) ps codes (sums := sums)) :
    e.requires = none ∧ e.pre = [] := by
  rcases j with ⟨Γ,t,A⟩
  cases t <;> try exact (hl : False).elim
  rcases ps with _ | ⟨jf, _ | ⟨jr, jas⟩⟩
  · exact (hl : False).elim
  · exact (hl : False).elim
  obtain ⟨-, -, -, -, -, -, -, hL⟩ := hl
  split at hL
  · exact hL.2.2.resolve_left (by simp)
  · exact hL.elim

/-- **Invocation at the selected signature's exits**: a call whose callee,
receiver and actuals are values is safe at the signature's specification at
its actuals, from an invocation entry held from the call's
(`CallEffects.call_exits`); its actuals are values. -/
theorem call_local_exits [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {ps : List (Sequent ι)} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {allow : Bool}
    {e : CallEffects.Effect} (hl : LocalUsing G images j (.app e) ps codes (sums := sums) (allowRequires := allow))
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hv : ∀ p ∈ ps, valueTerm p.term = true ∧ checkScope p.context.length p.term = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hq : e.Requires (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    CallArguments.Values (actualsOf (instantiate 0 ρ j.term)) ∧ SafePostExcV (excOf G) (meaning G j.type)
      (e.schema.heldPost (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) W h)
      (e.schema.heldExc (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) W h)
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
  have refsOf := invoke_refs htf htr hargs hundef href
  have hact : CallArguments.Values (actualsOf (instantiate 0 ρ (Tm.invoke f r args))) := by
    intro a ha
    simp only [actualsOf, instantiate, instantiateArgs_eq_map, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb' : b ∈ (jas.take args.length).map Sequent.term := by rw [hargs]; exact hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb'
    exact values p (by simp [List.mem_of_mem_take hp])
  refine ⟨hact, ?_⟩
  cases n with
  | zero => exact href
  | succ n =>
    have member : ∀ p ∈ jf::jr::jas, meaning G p.type (n+1) W (instantiate 0 ρ p.term) := by
      intro p hp
      exact safe_value_mem (values p hp) ((typed p hp).sound _ _ h ρ he hw hh (refsOf p hp))
    split at hL
    · rename_i L S hF
      have hf := ((represents_raw hF (n+1) W _ ) (member jf (by simp))).1
      have hp := hf.2 _ (List.mem_map_of_mem hL.1)
      simp only [CallEffects.Arrow.map, CallEffects.Contract.map, List.map_map,
        Function.comp_def] at hp
      have hArgs := argument_values (ps := jas)
        (fun p hp => typed p (by simp [hp])) (fun p hp => values p (by simp [hp])) he hw hh
        (fun p hp => refsOf p (by simp [hp]))
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
      have hres : e.promise = none := hL.2.1
      have hq' : e.Requires (instantiate 0 ρ jr.term) (args.map (instantiate 0 ρ)) h := by
        simpa [receiverOf, actualsOf, instantiate, htr, instantiateArgs_eq_map] using hq
      have hs := CallEffects.call_exits (effect := e)
        (P := ArgsShort (jas.map (fun p => meaning G p.type)))
        (Adm.of_transfer (fun ha j hj U hx => ArgsShort_transfer (fun T hm => by
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type) ha j hj U hx))
        (meaning_adm G jr.type) hp hr hrval hvals ha hw hh hq'
        (by simpa [htf, htr, instantiate, instantiateArgs_eq_map] using href)
      rw [CallEffects.Effect.result_none hres] at hs
      replace hs := SafePostExcV.weaken (R' := e.schema.heldExc _ _ W h) (fun _ _ _ _ hp => hp)
        (fun _ _ _ _ hp => .inl hp) hs
      simpa [CallEffects.Arrow.map, CallEffects.Contract.map, htf, htr, receiverOf, actualsOf,
        instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def] using hs
    · contradiction

/-- Invocation at the selected signature, its exits read at heaps
(`Effect.heldPosts_call`). -/
theorem call_local_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {ps : List (Sequent ι)} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {allow : Bool}
    {e : CallEffects.Effect} (hl : LocalUsing G images j (.app e) ps codes (sums := sums) (allowRequires := allow))
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hv : ∀ p ∈ ps, valueTerm p.term = true ∧ checkScope p.context.length p.term = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hq : e.Requires (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePostExc (excOf G) (meaning G j.type) (e.callPost (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) h)
      (e.callExc (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) h) n W h (instantiate 0 ρ j.term) := by
  obtain ⟨-, hs⟩ := call_local_exits hl ht hv he hw hh hq href
  exact CallEffects.Effect.heldPosts_call (pad := []) (by simp) (.inl rfl) hw hh (by simpa using hs)

/-- **Construction at the selected construct signature's exits**: a
construction whose constructor and actuals are values is safe at the
signature's specification at its actuals followed by the `undefined` of the
positions it omits, the receiver `undefined`, from an invocation entry held
from the construction's (`CallEffects.construct_exits`). -/
theorem construct_local_exits [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {ps : List (Sequent ι)} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {allow : Bool}
    {e : CallEffects.Effect} (hl : LocalUsing G images j (.construct e) ps codes (sums := sums) (allowRequires := allow))
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hv : ∀ p ∈ ps, valueTerm p.term = true ∧ checkScope p.context.length p.term = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hq : e.Requires (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    receiverOf (instantiate 0 ρ j.term) = .undef ∧ CallArguments.Values (actualsOf (instantiate 0 ρ j.term)) ∧
      ∃ pad : List Tm, (∀ a ∈ pad, a = .undef) ∧ SafePostExcV (excOf G) (meaning G j.type)
        (e.schema.heldPost (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term) ++ pad) W h)
        (e.schema.heldExc (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term) ++ pad) W h)
        n W h (instantiate 0 ρ j.term) := by
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
  have refsOf := construct_refs htf hargs hundef href
  have hact : CallArguments.Values (actualsOf (instantiate 0 ρ (Tm.construct f args))) := by
    intro a ha
    simp only [actualsOf, instantiate, instantiateArgs_eq_map, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb' : b ∈ (jas.take args.length).map Sequent.term := by rw [hargs]; exact hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb'
    exact values p (by simp [List.mem_of_mem_take hp])
  refine ⟨rfl, hact, ?_⟩
  cases n with
  | zero => exact ⟨[], by simp, href⟩
  | succ n =>
    have member : ∀ p ∈ jf::jas, meaning G p.type (n+1) W (instantiate 0 ρ p.term) := by
      intro p hp
      exact safe_value_mem (values p hp) ((typed p hp).sound _ _ h ρ he hw hh (refsOf p hp))
    split at hL
    · rename_i L S a bs vs hF
      obtain ⟨hmem, hpl⟩ := hL
      have hf := ((represents_raw hF (n+1) W _ ) (member jf (by simp))).1.1
      have hp := hf.2 _ (List.mem_map_of_mem hmem)
      simp only [CallEffects.MethodArrow.map, CallEffects.Contract.map, List.map_map,
        Function.comp_def] at hp
      have hArgs := argument_values (ps := jas)
        (fun p hp => typed p (by simp [hp])) (fun p hp => values p (by simp [hp])) he hw hh
        (fun p hp => refsOf p (by simp [hp]))
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
      have hpr : e.promise = none := by
        rcases hpl with hpl | ⟨-, hpr⟩
        · simp only [CallEffects.Effect.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at hpl
          exact hpl.1.1
        · exact hpr
      have hq' : e.Requires .undef (args.map (instantiate 0 ρ)) h := by
        simpa [receiverOf, actualsOf, instantiate, instantiateArgs_eq_map] using hq
      have hs := CallEffects.construct_exits hpr
        (P := ArgsT (jas.map (fun p => meaning G p.type)))
        (Adm.of_transfer (fun ha j hj U hx => ArgsT_transfer (fun T hm => by
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type) ha j hj U hx))
        hp hvals (pad := (jas.drop args.length).map (fun p => instantiate 0 ρ p.term))
        (by
          intro v hv'
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv'
          simp [hundef p hp, instantiate])
        (by rw [← hsplit]; exact hArgs) hw hh hq'
        (by simpa [htf, instantiate, instantiateArgs_eq_map] using href)
      replace hs := SafePostExcV.weaken (R' := e.schema.heldExc _ _ W h) (fun _ _ _ _ hp => hp)
        (fun _ _ _ _ hp => .inl hp) hs
      refine ⟨(jas.drop args.length).map (fun p => instantiate 0 ρ p.term), ?_, ?_⟩
      · intro v hv'
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv'
        simp [hundef p hp, instantiate]
      · simpa [htf, receiverOf, actualsOf, instantiate, instantiateArgs_eq_map] using hs
    · contradiction

/-- Construction consumes the selected construct signature's effect, as
invocation does: the constructor and the actuals are values, each omitted
position an explicit `undefined` premise; a signature stating a precondition
(`allowRequires`) where it holds of the construction's actuals; its exits
read at heaps (`Effect.heldPosts_call`). -/
theorem construct_local_requires_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {ps : List (Sequent ι)} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {allow : Bool}
    {e : CallEffects.Effect} (hl : LocalUsing G images j (.construct e) ps codes (sums := sums) (allowRequires := allow))
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hv : ∀ p ∈ ps, valueTerm p.term = true ∧ checkScope p.context.length p.term = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hq : e.Requires (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePostExc (excOf G) (meaning G j.type) (e.callPost (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) h)
      (e.callExc (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) h) n W h (instantiate 0 ρ j.term) := by
  obtain ⟨hrecv, -, pad, hpad, hs⟩ := construct_local_exits hl ht hv he hw hh hq href
  exact CallEffects.Effect.heldPosts_call hpad (.inr (by rw [hrecv]; rfl)) hw hh hs

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

/-- **A spread operand that reads the heap, evaluated** (the note's Call:
evaluation precedes invocation), in a call whose earlier actuals are values:
its reads keep the heap, so the call's evaluation reaches what it reaches
once the operand is a value at `S`, or throws the operand's throw, in the
heap it starts in. -/
theorem spread_head_eval {S : Fam} {E : (n : Nat) → WorldT n → Heap → Tm → Tm → List Tm → Prop}
    {R : HeapObservations.WExcV} {f r : Tm} {pre rest : List Tm}
    (hf : isVal f = true) (hrv : isVal r = true) (hp : CallArguments.Values pre) :
    ∀ (n : Nat) (W : WorldT n) (heap : Heap) (s : Tm),
      Purity.readTerm s = true → WorldAdm W → HeapOk n W heap → Safe Ξ S n W heap s →
      RefsOk W (.invoke f r (pre ++ .spread s :: rest)) →
      (∀ j (hj : j ≤ n) (U : WorldT j), WExt (trunc j hj W) U → ∀ v, R j U heap v) →
      (∀ j (hj : j ≤ n) (U : WorldT j), WExt (trunc j hj W) U → WorldAdm U → HeapOk j U heap →
        ∀ v, isVal v = true → S j U v → RefsOk U (.invoke f r (pre ++ .spread v :: rest)) →
          CallEffects.EvalCallSafe Ξ E R j U heap (.invoke f r (pre ++ .spread v :: rest))) →
      CallEffects.EvalCallSafe Ξ E R n W heap (.invoke f r (pre ++ .spread s :: rest)) := by
  have hC : CtxRefs (fun t => Tm.invoke f r (pre ++ .spread t :: rest)) := by ctx_refs
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ href _ _; exact href
  | succ n ih =>
    intro W heap s hs hw hh hsafe href hR hk
    obtain ⟨-, hsafe⟩ := hsafe
    rcases hsafe with (⟨hv, hS⟩ | ⟨u, hra, hsc, hξ⟩) | ⟨U, h', t', hx, hu, step, hh', ht'⟩
    · exact hk (n+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw hh s hv hS href
    · exact ⟨href, Or.inl (Or.inr ⟨u, RestCalls.call_raise hf hrv hp (.spreadC hra), hsc, hξ,
        hR (n+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) u⟩)⟩
    · obtain ⟨rfl, hs'⟩ := Purity.read_step step hs (HeapExpressionRules.heap_values hw hh)
      have hst : RefsOk W t' := Kinds.step_refs step (by simpa using hh.1.1) hh.2 (hC.hole href)
      refine ⟨href, Or.inr ⟨U, _, _, hx, hu, RestCalls.call_lift hf hrv hp (.spreadC step), hh', ?_⟩⟩
      have hUW : ∀ j (hj : j ≤ n) (V : WorldT j), WExt (trunc j hj U) V → WExt (trunc j (by omega) W) V := by
        intro j hj V hy
        apply WExt_trans _ hy
        simpa only [trunc_trunc] using WExt_trunc hj hx
      apply ih U _ t' hs' hu hh' ht'
        (hC.ok (RefsOk_mono hx (RefsOk_trunc _ hst)) (RefsOk_mono hx (RefsOk_trunc _ (hC.frame href))))
        (fun j hj V hy v => hR j (by omega) V (hUW j hj V hy) v)
      intro j hj V hy hV hhV v hv hS hvr
      exact hk j (by omega) V (hUW j hj V hy) hV hhV v hv hS hvr

/-- **The evaluation of parts after the fixed actuals, every one ready or a
read** (the note's Call: evaluation, spread expansion included, precedes
invocation): each plain part a value at the element contract `E`, each
spread a read of a spine at a type that spreads into `E`, read where it is
written. The call steps through the spreads in the heap it starts in, so its
evaluation reaches an invocation at the fixed actuals followed by values at
`E`, at an admissible extension of the world, or throws a spread's throw in
that heap. -/
theorem spread_values_eval {E : Fam} {I : (n : Nat) → WorldT n → Heap → Tm → Tm → List Tm → Prop}
    {R : HeapObservations.WExcV} (hE : Adm E) (hEv : ValOnly E)
    {f r : Tm} (hf : isVal f = true) (hrv : isVal r = true) :
    ∀ (parts : List (Option Fam × Tm)) (n : Nat) (W : WorldT n) (heap : Heap) (pre : List Tm),
      (∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ RestCalls.Spreads S E ∧
        Purity.readTerm p.2 = true ∧ FutureSafe Ξ S n W p.2) →
      WorldAdm W → HeapOk n W heap → CallArguments.Values pre →
      (∀ p ∈ parts, p.1 = none → isVal p.2 = true ∧ E n W p.2) →
      RefsOk W (.invoke f r (pre ++ parts.map RestCalls.partTerm)) →
      (∀ j (hj : j ≤ n) (U : WorldT j), WExt (trunc j hj W) U → ∀ v, R j U heap v) →
      (∀ j (hj : j ≤ n) (U : WorldT j), WExt (trunc j hj W) U → WorldAdm U → HeapOk j U heap →
        ∀ extra, (∀ e ∈ extra, E j U e) → RefsOk U (.invoke f r (pre ++ extra)) →
          CallEffects.EvalCallSafe Ξ I R j U heap (.invoke f r (pre ++ extra))) →
      CallEffects.EvalCallSafe Ξ I R n W heap (.invoke f r (pre ++ parts.map RestCalls.partTerm))
  | [], n, W, heap, pre, _, hw, hh, _, _, href, _, hk => by
    simpa using hk n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw hh [] (by simp)
      (by simpa using href)
  | (none, a) :: parts, n, W, heap, pre, hS, hw, hh, hp, hv, href, hR, hk => by
    obtain ⟨hav, haE⟩ := hv (none, a) (by simp) rfl
    have hrest := spread_values_eval (I := I) hE hEv hf hrv parts n W heap (pre ++ [a])
      (fun q hm => hS q (by simp [hm])) hw hh
      (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hp x hx
        · simp at hx; subst hx; exact hav)
      (fun q hm => hv q (by simp [hm]))
      (by simpa [RestCalls.partTerm] using href) hR
      (by
        intro j hj U hx hu hh' extra he hre
        have := hk j hj U hx hu hh' (a :: extra) (by
          intro e hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact hE.mono j _ U hx e (hE.down_le n j hj W e haE)
          · exact he e hm) (by simpa using hre)
        simpa using this)
    simpa [RestCalls.partTerm] using hrest
  | (some S, s) :: parts, n, W, heap, pre, hS, hw, hh, hp, hv, href, hR, hk => by
    obtain ⟨hSa, hSs, hread, hfut⟩ := hS (some S, s) (by simp) S rfl
    show CallEffects.EvalCallSafe Ξ I R n W heap (.invoke f r (pre ++ .spread s :: parts.map RestCalls.partTerm))
    apply spread_head_eval hf hrv hp n W heap s hread hw hh
      (hfut n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap hh) (by simpa [RestCalls.partTerm] using href)
      hR
    intro j hj U hx hu hhU v _ hSv hvr
    obtain ⟨ls, vs, rfl, hr, he⟩ := hSs j U heap _ hhU hSv
    cases j with
    | zero => exact hvr
    | succ p =>
      have hvs : CallArguments.Values vs := fun e hm => hEv p _ e (he e hm p (by omega))
      have hnext : RefsOk (trunc p (Nat.le_succ p) U) (.invoke f r (pre ++ vs ++ parts.map RestCalls.partTerm)) := by
        obtain ⟨hfr, hrr, har⟩ := RefsOk_invoke.mp hvr
        refine RefsOk_trunc _ (RefsOk_invoke.mpr ⟨hfr, hrr, fun b hb => ?_⟩)
        simp only [List.mem_append] at hb
        rcases hb with (hb | hb) | hb
        · exact har b (by simp [hb])
        · exact hhU.readElems_refs hr b hb
        · exact har b (by simp [hb])
      refine ⟨hvr, Or.inr ⟨trunc p (Nat.le_succ p) U, heap,
        .invoke f r (pre ++ vs ++ parts.map RestCalls.partTerm), WExt_refl _, WorldAdm_trunc _ hu,
        .callSpread hf hrv rfl hp hr, HeapOk_trunc p U heap hhU, ?_⟩⟩
      have hUV : ∀ i (hi : i ≤ p) (X : WorldT i),
          WExt (trunc i hi (trunc p (Nat.le_succ p) U)) X → WExt (trunc i (by omega) W) X := by
        intro i hi X hy
        apply WExt_trans _ hy
        have := WExt_trunc (show i ≤ p + 1 by omega) hx
        simpa only [trunc_trunc] using this
      have hrest := spread_values_eval (I := I) hE hEv hf hrv parts p _ heap (pre ++ vs)
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
        hnext
        (fun i hi X hy v => hR i (by omega) X (hUV i hi X hy) v)
        (by
          intro i hi X hy hX hh' extra hex hre
          have := hk i (by omega) X (hUV i hi X hy) hX hh' (vs ++ extra) (by
            intro e hm
            rcases List.mem_append.mp hm with hm | hm
            · have h0 := he e hm i (by omega)
              exact hE.mono i _ X (by
                apply WExt_trans _ hy
                simp only [trunc_trunc]
                exact WExt_refl _) e h0
            · exact hex e hm) (by simpa using hre)
          simpa using this)
      simpa using hrest

/-- **A variadic call's premises refer to what its actuals do**: each fixed
or further actual is one of the call's, or a spread of one, and each omitted
position `undefined`. -/
theorem jas_refs {n : Nat} {W : WorldT n} {ρ : Env} {jas : List (Sequent ι)} {k u : Nat} {flags : List Bool}
    {args : List Tm} (hlen : jas.length = k + u + flags.length)
    (hargs : args = (jas.take k).map Sequent.term ++
      (flags.zip (jas.drop (k + u))).map (fun q => spreadTerm (q.1, q.2.term)))
    (hundef : ∀ ja ∈ (jas.drop k).take u, ja.term = .undef)
    (har : ∀ a ∈ args, RefsOk W (instantiate 0 ρ a)) :
    ∀ p ∈ jas, RefsOk W (instantiate 0 ρ p.term) := by
  intro p hp
  rw [← List.take_append_drop k jas] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact har _ (by rw [hargs]; exact List.mem_append_left _ (List.mem_map_of_mem hp))
  · rw [← List.take_append_drop u (jas.drop k)] at hp
    rcases List.mem_append.mp hp with hp | hp
    · rw [hundef p hp]; exact RefsOk_undef
    · rw [List.drop_drop] at hp
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      have hfl : i < flags.length := by simp at hi; omega
      have hm : (flags[i], (jas.drop (k + u))[i]) ∈ flags.zip (jas.drop (k + u)) :=
        List.mem_iff_getElem.mpr ⟨i, by simp [List.length_zip]; omega, by simp⟩
      have := har _ (by rw [hargs]; exact List.mem_append_right _ (List.mem_map_of_mem hm))
      simpa [instantiate_spreadTerm, RefsOk, refs_spreadTerm] using this

/-- A variadic call whose parts are all values, none a spread, at its selected
signature: the call is safe at the signature's specification at its actuals,
from an invocation entry held from the call's (`CallEffects.call_exits`). -/
private theorem callRest_local_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {ps : List (Sequent ι)} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {e : CallEffects.Effect} {k u : Nat} {flags : List Bool} {P : Ty ι}
    (hl : LocalUsing G images j (.callRest e k u flags P) ps codes (sums := sums))
    (hnos : flags.all (· == false) = true)
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hv : ∀ p ∈ ps, valueTerm p.term = true ∧ checkScope p.context.length p.term = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    CallArguments.Values (actualsOf (instantiate 0 ρ j.term)) ∧ SafePostExcV (excOf G) (meaning G j.type)
      (e.schema.heldPost (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) W h)
      (e.schema.heldExc (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) W h)
      n W h (instantiate 0 ρ j.term) := by
  rcases j with ⟨Γ,t,A⟩
  cases t <;> try exact (hl : False).elim
  rename_i f r args
  rcases ps with _ | ⟨jf, _ | ⟨jr, jas⟩⟩
  · exact (hl : False).elim
  · exact (hl : False).elim
  obtain ⟨hΓf, htf, hΓr, htr, hcontexts, hlen, hshort, hargs, hundef, hparts, hmem, hplain⟩ := hl
  have refsOf : ∀ p ∈ jf::jr::jas, RefsOk W (instantiate 0 ρ p.term) := by
    obtain ⟨hfr, hrr, har⟩ := RefsOk_invoke.mp (by simpa [instantiate, instantiateArgs_eq_map] using href)
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · rw [htf]; exact hfr
    · rw [htr]; exact hrr
    · exact jas_refs hlen hargs hundef (fun a ha => har _ (List.mem_map_of_mem ha)) p hp
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
  have hact : CallArguments.Values (actualsOf (instantiate 0 ρ (Tm.invoke f r args))) := by
    intro a ha
    simp only [actualsOf, instantiate, instantiateArgs_eq_map, hargs, List.map_append, List.map_map,
      List.mem_append, List.mem_map, Function.comp_apply] at ha
    rcases ha with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact values p (by simp [List.mem_of_mem_take hp])
    · exact values p (by simp [List.mem_of_mem_drop hp])
  refine ⟨hact, ?_⟩
  cases n with
  | zero => exact href
  | succ n =>
    have member : ∀ p ∈ jf::jr::jas, meaning G p.type (n+1) W (instantiate 0 ρ p.term) := by
      intro p hp
      exact safe_value_mem (values p hp) ((typed p hp).sound _ _ h ρ he hw hh (refsOf p hp))
    have hf := restsT_of_restSigs hmem (member jf (by simp))
    have hp := hf.2 _ (List.mem_singleton_self _)
    have hAll := argument_values (ps := jas)
      (fun p hp => typed p (by simp [hp])) (fun p hp => values p (by simp [hp])) he hw hh
      (fun p hp => refsOf p (by simp [hp]))
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
    have hs := CallEffects.call_exits (effect := e)
      (P := ArgsRest ((jas.take (k + u)).map (fun p => meaning G p.type)) (argMeaning G P))
      (Adm.of_transfer (fun ha j hj U hx => ArgsRest_transfer (fun T hm => by
          obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type)
        (argMeaning_adm G P) ha j hj U hx))
      (meaning_adm G jr.type)
      (by simpa [CallEffects.RestArrow.mapWith, CallEffects.Contract.map, List.map_map, Function.comp_def] using hp)
      hr hrval hvals hacc hw hh
      (CallEffects.Effect.requires_none (CallEffects.Effect.plain_requires hplain)
        (CallEffects.Effect.plain_pre hplain) _ _ _)
      (by simpa [htf, htr, hargs, vals, instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
        using href)
    rw [CallEffects.Effect.result_plain hplain] at hs
    replace hs := SafePostExcV.weaken (R' := e.schema.heldExc _ _ W h) (fun _ _ _ _ hp => hp)
      (fun _ _ _ _ hp => .inl hp) hs
    simpa [htf, htr, hargs, vals, receiverOf, actualsOf, instantiate, instantiateArgs_eq_map, List.map_map,
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
its selected signature (the note's Call, then consequence): the evaluation
reads the spreads in the heap the call starts in and reaches an invocation at
the expanded actuals (`spread_values_eval`), which is safe at the signature's
specification there (`CallEffects.call_exits`); forgetting what it states of
the actuals (`Exits.forgetActuals_sound`), the call is safe at the forgotten
specification at its own actuals. -/
private theorem callRestSpread_local_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {ps : List (Sequent ι)} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {e : CallEffects.Effect} {k u : Nat} {flags : List Bool} {P : Ty ι}
    (hl : LocalUsing G images j (.callRest e k u flags P) ps codes (sums := sums))
    (hsp : flags.any id = true)
    (ht : ∀ p ∈ ps, HasTyUsing G images p.context p.term p.type)
    (hsc : ∀ p ∈ ps, checkScope p.context.length p.term = true)
    (hops : spreadOperands k u flags ps = true ∨ (ps.all fun p => valueTerm p.term) = true)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePostExcV (excOf G) (meaning G j.type)
      (e.schema.forgetActuals.heldPost (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) W h)
      (e.schema.forgetActuals.heldExc (receiverOf (instantiate 0 ρ j.term)) (actualsOf (instantiate 0 ρ j.term)) W h)
      n W h (instantiate 0 ρ j.term) := by
  rcases j with ⟨Γ,t,A⟩
  cases t <;> try exact (hl : False).elim
  rename_i f r args
  rcases ps with _ | ⟨jf, _ | ⟨jr, jas⟩⟩
  · exact (hl : False).elim
  · exact (hl : False).elim
  obtain ⟨hΓf, htf, hΓr, htr, hcontexts, hlen, hshort, hargs, hundef, hparts, hmem, hplain⟩ := hl
  have refsOf : ∀ p ∈ jf::jr::jas, RefsOk W (instantiate 0 ρ p.term) := by
    obtain ⟨hfr, hrr, har⟩ := RefsOk_invoke.mp (by simpa [instantiate, instantiateArgs_eq_map] using href)
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · rw [htf]; exact hfr
    · rw [htr]; exact hrr
    · exact jas_refs hlen hargs hundef (fun a ha => har _ (List.mem_map_of_mem ha)) p hp
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
  | zero => exact href
  | succ n =>
    have member : ∀ p ∈ jf::jr::jas, isVal (instantiate 0 ρ p.term) = true →
        meaning G p.type (n+1) W (instantiate 0 ρ p.term) := by
      intro p hp hv
      exact safe_value_mem hv ((typed p hp).sound _ _ h ρ he hw hh (refsOf p hp))
    have hfv := valueOf jf (by simp) hfv0
    have hrv := valueOf jr (by simp) hrv0
    have hf := restsT_of_restSigs hmem (member jf (by simp) hfv)
    have hfixed : ArgsT ((jas.take k).map (fun p => meaning G p.type)) (n+1) W
        ((jas.take k).map (fun p => instantiate 0 ρ p.term)) := by
      have hAll := argument_values (ps := jas.take k)
        (fun p hp => typed p (by simp [List.mem_of_mem_take hp]))
        hfixedv he hw hh (fun p hp => refsOf p (by simp [List.mem_of_mem_take hp]))
      exact hAll
    -- The parts: each spread at its spine type, each plain part at the element.
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
    have hrefs' : RefsOk W (instantiate 0 ρ (.invoke f r args)) := href
    rw [hterm] at hrefs' ⊢
    have hpart : ∀ q ∈ flags.zip (jas.drop k), if q.1 then SpreadsInto G q.2.type El else q.2.type = El :=
      fun q hq => hparts (q.1, q.2.type) (List.mem_map_of_mem hq)
    let F := instantiate 0 ρ jf.term
    let Rv := instantiate 0 ρ jr.term
    let fixedVals := (jas.take k).map (fun p => instantiate 0 ρ p.term)
    let x := e.schema.forgetActuals
    let Q := x.heldPost Rv (fixedVals ++ parts.map RestCalls.partTerm) W h
    let R := x.heldExc Rv (fixedVals ++ parts.map RestCalls.partTerm) W h
    show SafePostExcV (excOf G) (meaning G A) Q R (n+1) W h (.invoke F Rv (fixedVals ++ parts.map RestCalls.partTerm))
    -- The invocations the evaluation reaches: the callee and the receiver,
    -- the fixed actuals followed by values at the element, in the call's
    -- heap, at a well-formed world reached from the call's.
    let I : (m : Nat) → WorldT m → Heap → Tm → Tm → List Tm → Prop := fun m U h' f' r' vs =>
      h' = h ∧ f' = F ∧ r' = Rv ∧ ∃ extra, vs = fixedVals ++ extra ∧ ∃ hi : m ≤ n + 1,
        WExt (trunc m hi W) U ∧ WorldAdm U ∧ HeapOk m U h' ∧ (∀ a ∈ extra, meaning G El m U a) ∧
          RefsOk U (.invoke f' r' vs)
    -- The call at its callee's exits, at the reached invocation's actuals.
    have hfull := CallEffects.call_site_exits (x := e.schema) (T := meaning G A)
      (R := fun _ _ h' _ => h' = h) (E := I)
      (by
        rintro m U h' f' r' vs ⟨-, rfl, rfl, extra, rfl, -, -, -, -, hex, -⟩
        refine ⟨hfv, hrv, fun a ha => ?_⟩
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
          exact hfixedv p hp
        · exact meaning_valOnly G El _ U a (hex a ha))
      (by
        rintro i U h' f' r' vs ⟨rfl, rfl, rfl, extra, rfl, hi, hx, hU, hh', hex, hre⟩
        have hfU := (CallEffects.restsT_adm _).mono (i+1) _ U hx _
          ((CallEffects.restsT_adm _).down_le (n+1) (i+1) hi W _ hf)
        have hp := hfU.2 _ (List.mem_singleton_self _)
        have hrU := (meaning_adm G jr.type).mono (i+1) _ U hx _
          ((meaning_adm G jr.type).down_le (n+1) (i+1) hi W _ (member jr (by simp) hrv))
        have hvals : CallArguments.Values (fixedVals ++ extra) := by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
            exact hfixedv p hp
          · exact meaning_valOnly G El (i+1) U a (hex a ha)
        have hacc : ArgsRest ((jas.take k).map (fun p => meaning G p.type)) (argMeaning G P) (i+1) U
            (fixedVals ++ extra) :=
          ArgsRest_of_exact_extra
            (ArgsT_transfer (fun T hm => by obtain ⟨p,_,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type)
              hfixed (i+1) hi U hx)
            ((restElem_args hel).mpr hex)
        have hs := CallEffects.call_exits_exact (effect := e)
          (P := ArgsRest ((jas.take k).map (fun p => meaning G p.type)) (argMeaning G P))
          (Adm.of_transfer (fun ha j hj U hx => ArgsRest_transfer (fun T hm => by
              obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type)
            (argMeaning_adm G P) ha j hj U hx))
          (meaning_adm G jr.type)
          (by simpa [CallEffects.RestArrow.mapWith, CallEffects.Contract.map, List.map_map, Function.comp_def] using hp)
          hrU hrv hvals hacc hU hh'
          (CallEffects.Effect.requires_none (CallEffects.Effect.plain_requires hplain)
            (CallEffects.Effect.plain_pre hplain) _ _ _) hre
        rw [CallEffects.Effect.result_plain hplain] at hs
        exact hs)
      hw hh
      (by
        apply spread_values_eval (E := meaning G El) (meaning_adm G El) (meaning_valOnly G El) hfv hrv
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
              exact (typed p (by simp [hm])).sound i U heap' ρ (heΓ.transfer i hi U hx) hu hh'
                (RefsOk_mono hx (RefsOk_trunc _ (refsOf p (by simp [hm])))))
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
          hrefs' (fun _ _ _ _ _ => rfl)
        intro i hi U hx hU hh' extra hex hre
        exact CallEffects.EvalCallSafe.invoke hre ⟨rfl, rfl, rfl, extra, rfl, hi, hx, hU, hh', hex, hre⟩)
    -- Forgetting what the specification states of the actuals, by
    -- consequence (`Exits.forgetActuals_sound`), from the reached
    -- invocation's entry, held from the call's.
    have hheap : ∀ m U h' f' r' vs, I m U h' f' r' vs → h' = h := fun _ _ _ _ _ _ hI => hI.1
    have hforget : ∀ c m U f' r' vs, I m U h f' r' vs → ∀ s s' v, e.schema.exitPost c r' vs s s' v →
        x.exitPost c Rv (fixedVals ++ parts.map RestCalls.partTerm) s s' v := by
      rintro c m U f' r' vs ⟨-, -, rfl, -⟩ s s' v hp
      exact CallEffects.Exits.forgetActuals_sound hp
    exact SafePostExcV.weaken (fun _ _ _ _ hp => CallEffects.Exits.callExit_held hheap (hforget .normal) hp)
      (fun _ _ _ _ hp => hp.elim .inr fun hp => .inl (CallEffects.Exits.callExit_held hheap (hforget .exceptional) hp))
      hfull

/-- **A selected call at its selected exits** (the note's Call, then
consequence): the call is safe at its evidence's exits (`selectedExits`) at
its receiver and its actuals followed by the `undefined` of the positions a
construction omits, from an entry held from the call's; the receiver owns no
spine where positions are omitted. -/
theorem selected_exits_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (e : Evidence ι)
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} (ht : checkTreeUsing G images e codes sums = true)
    (hp : selectedOperands e = true) {x : CallEffects.Exits CallEffects.ExitSchema} (hsel : selectedExits e = some x)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ n W h} (he : EnvOk G (claim e).context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ (claim e).term)) :
    ∃ pad : List Tm, (∀ a ∈ pad, a = .undef) ∧
      (pad = [] ∨ Footprints.spineOf (receiverOf (instantiate 0 ρ (claim e).term)) = none) ∧
      SafePostExcV (excOf G) (meaning G (claim e).type)
        (x.heldPost (receiverOf (instantiate 0 ρ (claim e).term)) (actualsOf (instantiate 0 ρ (claim e).term) ++ pad) W h)
        (x.heldExc (receiverOf (instantiate 0 ρ (claim e).term)) (actualsOf (instantiate 0 ρ (claim e).term) ++ pad) W h)
        n W h (instantiate 0 ρ (claim e).term) := by
  cases e with
  | node j r ps =>
    simp only [claim] at he href ⊢
    simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
    cases r <;> try simp only [selectedExits, reduceCtorEq] at hsel
    case app effect =>
      cases hsel
      simp only [selectedOperands] at hp
      obtain ⟨hact, hs⟩ := call_local_exits ht.1 (fun p hm => by
          obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
          exact checkTreeUsing_sound e (ht.2 ⟨e,heq⟩ (by simp)) hcodes hsums)
        (fun p hm => by
          obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
          exact by simpa only [Bool.and_eq_true] using List.all_eq_true.mp hp e heq) he hw hh
        (CallEffects.Effect.requires_none (app_requires_none ht.1).1 (app_requires_none ht.1).2 _ _ _) href
      refine ⟨[], by simp, .inl rfl, ?_⟩
      simpa only [List.append_nil] using hs
    case callRest effect k u flags P =>
      cases hsel
      simp only [selectedOperands, Bool.and_eq_true, Bool.or_eq_true] at hp
      obtain ⟨hscope, hp⟩ := hp
      have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
        intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound e (ht.2 ⟨e,heq⟩ (by simp)) hcodes hsums
      have inScope : ∀ p ∈ ps.map claim, checkScope p.context.length p.term = true := by
        intro p hm
        obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
        exact List.all_eq_true.mp hscope e heq
      refine ⟨[], by simp, .inl rfl, ?_⟩
      simp only [List.append_nil]
      by_cases hsp : flags.any id = true
      · rw [if_pos hsp]
        rcases hp with hvals | ⟨-, hops⟩
        · exact callRestSpread_local_sound ht.1 hsp typed inScope (.inr (by simpa using hvals)) he hw hh href
        · exact callRestSpread_local_sound ht.1 hsp typed inScope (.inl (by simpa using hops)) he hw hh href
      · have hvals : (ps.all fun p => valueTerm (claim p).term) = true := by
          rcases hp with hvals | ⟨hsp', -⟩
          · exact hvals
          · exact absurd hsp' hsp
        have hnos : flags.all (· == false) = true := by
          simp only [List.all_eq_true, beq_iff_eq]
          intro b hb
          cases b
          · rfl
          · exact absurd (List.any_eq_true.mpr ⟨true, hb, rfl⟩) hsp
        obtain ⟨hact, hs⟩ := callRest_local_sound ht.1 hnos typed (fun p hm => by
          obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
          exact ⟨List.all_eq_true.mp hvals e heq, List.all_eq_true.mp hscope e heq⟩) he hw hh href
        rw [if_neg hsp]
        exact hs
    case construct effect =>
      cases hsel
      simp only [selectedOperands] at hp
      have hl := ht.1
      have hpl : effect.plain = true := by
        rcases j with ⟨Γ,t,A⟩
        cases t <;> try exact (hl : False).elim
        rcases ps with _ | ⟨jf, jas⟩
        · exact (hl : False).elim
        obtain ⟨-, -, -, -, -, hL⟩ := hl
        split at hL
        · exact hL.2.resolve_right (by simp)
        · exact hL.elim
      obtain ⟨hrecv, hact, pad, hpad, hs⟩ := construct_local_exits hl (fun p hm => by
          obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
          exact checkTreeUsing_sound e (ht.2 ⟨e,heq⟩ (by simp)) hcodes hsums)
        (fun p hm => by
          obtain ⟨e,heq,rfl⟩ := List.mem_map.mp hm
          exact by simpa only [Bool.and_eq_true] using List.all_eq_true.mp hp e heq) he hw hh
        (CallEffects.Effect.requires_none (CallEffects.Effect.plain_requires hpl) (CallEffects.Effect.plain_pre hpl)
          _ _ h) href
      exact ⟨pad, hpad, .inr (by rw [hrecv]; rfl), hs⟩
    case sub proof =>
      cases ps with
      | nil => simp [selectedExits] at hsel
      | cons child rest =>
        cases rest with
        | cons _ _ => simp [selectedExits] at hsel
        | nil =>
          simp only [selectedExits] at hsel
          simp only [selectedOperands] at hp
          obtain ⟨hctx,hterm,hsub⟩ := ht.1
          obtain ⟨pad, hpad, hrecv, ih⟩ := selected_exits_sound child (ht.2 ⟨child,by simp⟩ (by simp)) hp hsel
            hcodes hsums (ρ := ρ) (n := n) (W := W) (h := h) (by rw [hctx]; exact he) hw hh (by rw [hterm]; exact href)
          rw [hterm] at hrecv ih
          exact ⟨pad, hpad, hrecv,
            SafePostExcV.mono_result (fun j W v hv => PositiveCertificates.acceptedUsing hsub j W v hv) ih⟩
termination_by sizeOf e

/-- **The selected exits read at the heaps of a run** as the signature the
deciders read (`selectedEffect`): its exits, entailed by the selected ones
(`selectedExits_entails`), at heaps (`Effect.heldPosts_call`). -/
theorem selectedExits_heldPost_call {Ξ T : Fam} {x : CallEffects.Exits CallEffects.ExitSchema}
    {eff : CallEffects.Effect} (ev : Evidence ι) (hx : selectedExits ev = some x) (he : selectedEffect ev = some eff)
    {r : Tm} {args pad : List Tm} (hpad : ∀ a ∈ pad, a = .undef) (hrecv : pad = [] ∨ Footprints.spineOf r = none)
    {n : Nat} {W : WorldT n} {h : Heap} {t : Tm} (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : SafePostExcV Ξ T (x.heldPost r (args ++ pad) W h) (x.heldExc r (args ++ pad) W h) n W h t) :
    SafePostExc Ξ T (eff.callPost r args h) (eff.callExc r args h) n W h t := by
  have hent : ∀ c k (V : WorldT k) after v, x.fromEntry c r (args ++ pad) (CallEffects.HeldEntry W h) k V after v →
      eff.schema.fromEntry c r (args ++ pad) (CallEffects.HeldEntry W h) k V after v := by
    rintro c k V after v ⟨s, hs0, hp⟩
    exact ⟨s, hs0, fun h1 h2 h3 h4 h5 h6 => selectedExits_entails ev hx he (hp h1 h2 h3 h4 h5 h6)⟩
  exact CallEffects.Effect.heldPosts_call hpad hrecv hw hh
    (SafePostExcV.weaken (hent .normal) (fun k V after v hp => hp.imp (hent .exceptional k V after v) id) hs)

/-- **A selected call meets its signature's postcondition**, at its receiver,
from the heap it starts in: its selected exits read at its heaps
(`selected_exits_sound`, `selectedExits_heldPost_call`). -/
theorem selected_sound_exc [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (e : Evidence ι)
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} (ht : checkTreeUsing G images e codes sums = true)
    (hp : selectedOperands e = true) {eff : CallEffects.Effect} (hsel : selectedEffect e = some eff)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ n W h} (he : EnvOk G (claim e).context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ (claim e).term)) :
    SafePostExc (excOf G) (meaning G (claim e).type)
      (eff.callPost (receiverOf (instantiate 0 ρ (claim e).term)) (actualsOf (instantiate 0 ρ (claim e).term)) h)
      (eff.callExc (receiverOf (instantiate 0 ρ (claim e).term)) (actualsOf (instantiate 0 ρ (claim e).term)) h)
      n W h (instantiate 0 ρ (claim e).term) := by
  obtain ⟨x, hx⟩ : ∃ x, selectedExits e = some x := selectedExits_of_effect e hsel
  obtain ⟨pad, hpad, hrecv, hs⟩ := selected_exits_sound e ht hp hx hcodes hsums he hw hh href
  exact selectedExits_heldPost_call e hx hsel hpad hrecv hw hh hs

/-- **A selected call meets its signature's postcondition**, at its receiver,
from the heap it starts in (`selected_sound_exc`). -/
theorem selected_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (e : Evidence ι)
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} (ht : checkTreeUsing G images e codes sums = true)
    (hp : selectedOperands e = true) {eff : CallEffects.Effect} (hsel : selectedEffect e = some eff)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ n W h} (he : EnvOk G (claim e).context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ (claim e).term)) :
    SafePost (excOf G) (meaning G (claim e).type) (eff.callPost (receiverOf (instantiate 0 ρ (claim e).term)) (actualsOf (instantiate 0 ρ (claim e).term)) h)
      n W h (instantiate 0 ρ (claim e).term) :=
  (selected_sound_exc e ht hp hsel hcodes hsums he hw hh href).post

theorem selectedCall_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {Φ : Footprints.Closed} (e : Evidence ι)
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} (ht : checkTreeUsing G images e codes sums = true)
    (hp : selectedCallWithin Φ e = true) (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ n W h} (he : EnvOk G (claim e).context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ (claim e).term)) :
    SafePost (excOf G) (meaning G (claim e).type) (fun h' _ => Φ.Holds h h')
      n W h (instantiate 0 ρ (claim e).term) := by
  simp only [selectedCallWithin, Bool.and_eq_true] at hp
  obtain ⟨hops, hp⟩ := hp
  split at hp
  · rename_i eff hsel
    apply HeapObservations.weaken (fun h' v hq => ?_) (selected_sound e ht hops hsel hcodes hsums he hw hh href)
    -- The frame is within its closed bound (`Footprint.close_sound`).
    have hc := Footprints.Footprint.close_sound (CallEffects.Effect.callPost_within hq)
    exact (Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp hc)).mono hp
  · cases hp

/-! ### No normal return

A term typed at a type no value has never returns normally: its normal
return is within every footprint (`no-return`, FOOTPRINTS.md). The type is
the one the term's ordinary safety gives it; its emptiness is decided as an
unreachable entry's is, a type of clause rows with no clause. -/

/-- A type no value meets: a type of clause rows expanding to no clause. -/
@[nospecialize] def emptyType (G : NormalGraph ι) (A : List ι) : Bool :=
  G.plainTy A && (expand G A).isEmpty

theorem emptyType_sound {G : NormalGraph ι} {A : List ι} (hA : emptyType G A = true) {n W v} :
    ¬ meaning G A n W v := by
  intro hm
  simp only [emptyType, Bool.and_eq_true, List.isEmpty_iff] at hA
  have hm := (expand_sem G A hA.1 n W v).mp hm
  rw [hA.2] at hm
  obtain ⟨_, hmem, _⟩ := hm
  cases hmem

/-- **A term safe at a type no value has meets every normal postcondition**
(`no-return`): its normal return never happens, so the postcondition holds
vacuously; a throw and every step are as its safety gives them. -/
theorem noReturn_sound {Ξ : Fam} {G : NormalGraph ι} {A : List ι} (hA : emptyType G A = true)
    {R : Post} {n W h t} (hs : Safe Ξ (meaning G A) n W h t) : SafePost Ξ (meaning G A) R n W h t :=
  of_value_property (fun _ _ _ _ hv => (emptyType_sound hA hv).elim) hs

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
  | zero => intros; assumption
  | succ n ih =>
    intro W h t hpre hp hw hh hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
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
  inspect_safe_exc (List.prefix_refl h) (HeapExpressionRules.inspect_instantiate (d := 0) hc hscope he) hw hh hs

/-! ### Element writes

`o[b] = v` lowers to one node: the spine `o` holds at its spine field, the
value written at index `b` (`setElem`), and the spine it yields put back.
At a listed index the element's location takes the value and the spine is
unchanged; at a hole or past the end a fresh location is listed. Either way
every old dense prefix stays and no old location is newly listed: within
`{o.spine: grow, o.cells: any}`, the spine at `keep` where the index is a
required position of the spine's tuple contract (`elemWriteFrame`,
FOOTPRINTS.md, "Element writes"). -/

/-- The slots of an element write: the object's, its spine field, the index
and the written value's. -/
def elemWriteSlots : Tm → Option (PropKey × Nat × UInt64 × Nat)
  | .writeAt f (.var i) (.setElem (.readAt f' (.var i')) (.num b) (.var k)) =>
    if f' = f ∧ i' = i then some (f, i, b, k) else none
  | _ => none

theorem elemWriteSlots_eq {t f i b k} (h : elemWriteSlots t = some (f, i, b, k)) :
    t = .writeAt f (.var i) (.setElem (.readAt f (.var i)) (.num b) (.var k)) := by
  unfold elemWriteSlots at h
  split at h
  · rename_i f₀ i₀ f' i' b₀ k₀
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl
    · contradiction
  · contradiction

/-- A spine type whose position `idx` holds source values, a required one
where `present` asks for it. -/
def spineTy (G : NormalGraph ι) (L : Ty ι) (idx : Nat) (present : Bool) : Bool :=
  match expand G L with
  | [.list T []] =>
    (match positionTy T idx with
     | some A => sourceTy G A
     | none => false) && (!present || decide (idx < T.required.length))
  | _ => false

/-- Every alternative is a record whose first invariant operand has the field
`fld`, at a spine type `spineTy` accepts in each. -/
def spineField (G : NormalGraph ι) (cs : List (PositiveNormalization.Clause (Ty ι))) (fld : PropKey)
    (idx : Nat) (present : Bool) : Bool :=
  !cs.isEmpty && cs.all fun c => match HeapExpressionRules.clauseBagOperand c with
    | some B => B.any (fun p => decide (p.1 = fld)) && B.all (fun p => !decide (p.1 = fld) || spineTy G p.2.2 idx present)
    | none => false

theorem spineField_sound [DecidableEq ι] {G : NormalGraph ι} {Ref fld idx present n W v}
    (hr : spineField G (expand G Ref) fld idx present = true) (hv : meaning G Ref n W v) :
    ∃ B s L, (fld, s, L) ∈ B ∧ spineTy G L idx present = true ∧
      bagT (ReferenceConjunctions.famsOf (meaning G) B) n W v := by
  simp only [spineField, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
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
    obtain ⟨⟨g, s, El⟩, hmem, hg⟩ := List.any_eq_true.mp hany
    simp only [decide_eq_true_eq] at hg
    subst hg
    have hsrc : spineTy G El idx present = true := (hall _ hmem).resolve_left (by simp)
  · exact ⟨_, s, El, hmem, hsrc, recT_bag hc.1.1⟩
  · exact ⟨_, s, El, hmem, hsrc, hc.1.1.1.1⟩

/-- A listed position of a spine under a tuple contract has a location whose
contract implies the position's family. -/
theorem listT_slot {T : TupleF} {k : Nat} {W : WorldT k} {ls : List (Option Nat)} {i l : Nat} {A : Fam}
    (h : listT T k W (.arr ls)) (hl : ls[i]? = some (some l)) (hA : positionFam T i = some A) :
    ∃ c : Ctr k, lookup W l = some c ∧ ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val),
      c j hj W' u → A j W' u := by
  obtain ⟨ls', heq, -, -, -, -, hreq, hopt, hrest⟩ := h
  cases heq
  unfold positionFam at hA
  split at hA
  · rename_i A' hreq'
    cases hA
    obtain ⟨l', c, hl', hw, hag⟩ := hreq i _ hreq'
    rw [hl] at hl'
    cases hl'
    exact ⟨c, hw, fun j hj W' u hu => (hag j hj W' u).1 hu⟩
  · rename_i hnone
    have hge : T.required.length ≤ i := List.getElem?_eq_none_iff.mp hnone
    split at hA
    · rename_i A' hopt'
      cases hA
      have hk : T.required.length + (i - T.required.length) = i := by omega
      obtain ⟨c, hw, hag⟩ := hopt (i - T.required.length) _ l hopt' (by rw [hk]; exact hl)
      exact ⟨c, hw, fun j hj W' u hu => (hag j hj W' u).1 hu⟩
    · split at hA
      · rename_i hle
        obtain ⟨E, c, hE, hw, hag⟩ := hrest i l hle hl
        rw [hE] at hA
        cases hA
        exact ⟨c, hw, fun j hj W' u hu => (hag j hj W' u).1 hu⟩
      · contradiction

/-- A padded write keeps every dense prefix. -/
theorem placeAt_dense {ls : List (Option Nat)} {k l n : Nat} (h : Footprints.DensePrefix n ls) :
    Footprints.DensePrefix n (placeAt ls k l) := by
  obtain ⟨hlen, hp⟩ := h
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [placeAt, List.length_set, List.length_append, List.length_replicate]; omega
  · simp only [placeAt]
    by_cases hik : k = i
    · subst hik
      rw [List.getElem?_set_self (by simp; omega)]
      simp
    · rw [List.getElem?_set_ne hik, List.getElem?_append_left (by omega)]
      exact hp i hi

/-- A padded write lists, beside the old locations, only the one it writes. -/
theorem placeAt_mem {ls : List (Option Nat)} {k l x : Nat} (hm : some x ∈ placeAt ls k l) :
    some x ∈ ls ∨ x = l := by
  simp only [placeAt] at hm
  rcases List.mem_or_eq_of_mem_set hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · exact .inl hm
    · simp [List.mem_replicate] at hm
  · exact .inr (Option.some.inj hm)

/-- The heap after a write at a listed location of the spine at `fl`, that
spine put back. -/
theorem elem_present_holds {h : Heap} {l fl : Nat} {v u : Val} {ls : List (Option Nat)}
    (hfl : h[fl]? = some (.arr ls)) (hl : h[l]? = some u) (hu : Footprints.isArr u = false) :
    Footprints.Closed.Holds ⟨.any, .keep, .keep⟩ h ((h.set l v).set fl (.arr ls)) := by
  rw [Footprints.Closed.holds_iff]
  refine ⟨by simp, fun l' w hw => ?_⟩
  by_cases hf : l' = fl
  · subst hf
    rw [hfl] at hw; cases hw
    refine ⟨.arr ls, ?_, ?_⟩
    · rw [List.getElem?_set_self]; simp only [List.length_set]
      exact (List.getElem?_eq_some_iff.mp hfl).1
    · simp [Footprints.Closed.at, Footprints.isArr, Footprints.Change.Holds]
  · by_cases hll : l' = l
    · subst hll
      rw [hl] at hw; cases hw
      refine ⟨v, ?_, ?_⟩
      · rw [List.getElem?_set_ne (Ne.symm hf), List.getElem?_set_self (List.getElem?_eq_some_iff.mp hl).1]
      · simp [Footprints.Closed.at, hu, Footprints.Change.Holds]
    · refine ⟨w, ?_, Footprints.Change.Holds.refl _ _ _⟩
      rw [List.getElem?_set_ne (Ne.symm hf), List.getElem?_set_ne (Ne.symm hll), hw]

/-- The heap after a write taking a fresh location at an array index, the
spine recording it put back. -/
theorem elem_grow_holds {h : Heap} {fl k : Nat} {v : Val} {ls : List (Option Nat)}
    (hfl : h[fl]? = some (.arr ls)) (hk : k < maxArrayLength) :
    Footprints.Closed.Holds ⟨.any, .grow, .grow⟩ h ((h ++ [v]).set fl (.arr (placeAt ls k h.length))) := by
  rw [Footprints.Closed.holds_iff]
  have hflt := (List.getElem?_eq_some_iff.mp hfl).1
  refine ⟨by simp, fun l' w hw => ?_⟩
  have hlt := (List.getElem?_eq_some_iff.mp hw).1
  by_cases hf : l' = fl
  · subst hf
    rw [hfl] at hw; cases hw
    refine ⟨.arr (placeAt ls k h.length), ?_, ?_⟩
    · rw [List.getElem?_set_self (by simp; omega)]
    · simp only [Footprints.Closed.at, Footprints.isArr, if_true]
      exact .inr (.inl ⟨ls, _, rfl, rfl, fun n hd => placeAt_dense hd,
        fun x hx => (placeAt_mem hx).imp id (fun e => by omega),
        ⟨by rw [placeAt_length]; omega, fun _ => by rw [placeAt_length]; omega⟩⟩)
  · refine ⟨w, ?_, Footprints.Change.Holds.refl _ _ _⟩
    rw [List.getElem?_set_ne (Ne.symm hf), List.getElem?_append_left hlt, hw]


/-! ### An element write's frame and postcondition

The note *Tolerant frames*, "Exact postconditions": Write-In and Write-End
change the written array's spine by growth and its cells, nothing else; the
spine's length is kept below it and one longer at it. -/

/-- **An element write's frame** (the note, Write-In and Write-End,
`{x.spine: grow, x.cells: any}`), read at the node's slots: the spine
location of the object in slot `i`, where it holds an array spine, within
`s`, and the element cells that spine lists, where they hold values, within
`any`. At a position the spine's contract requires, `s` is `keep`. -/
def elemWriteFrame (i : Nat) (s : Footprints.Change) : Footprints.Footprint :=
  [((Footprints.Region.field i arraySpineKey).inCls .arrays, s),
    ((Footprints.Region.cells i).inCls .values, .any)]

/-- **What an element write leaves**, at the index value `ix`: its frame,
and the written spine one past the index where that is beyond its length
and of its length otherwise (the note's exact postconditions: Write-In
keeps the length, Write-End adds one). -/
def ElemWritten (i : Nat) (s : Footprints.Change) (ix : Tm) (ρ : Env) (h h' : Heap) : Prop :=
  Footprints.Post (elemWriteFrame i s) ρ h h' ∧
  ∀ fl ls b idx, Footprints.spineOf (ρ i) = some fl → h[fl]? = some (.arr ls) → ix = .num b →
    indexOfBits b = some idx → ∃ ls', h'[fl]? = some (.arr ls') ∧ ls'.length = max ls.length (idx + 1)

/-- **The closed bound of an element write is a weakening of its frame**:
`{x.spine: s, x.cells: any}` is within `{value: any, spine: s}`. -/
theorem elemWriteFrame_closed {i : Nat} {s : Footprints.Change} {ρ : Env} {h h' : Heap}
    (hp : Footprints.Post (elemWriteFrame i s) ρ h h') : (Footprints.Closed.ofSpines .any s).Holds h h' :=
  Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp
    (Footprints.Post.mono (cl := fun _ _ => none) (by cases s <;> rfl) (fun _ _ _ _ hc => by cases hc) hp))

/-- **Write-In keeps every spine's length**: where the index is below the
written spine's length, every spine of the entry heap is one of the same
length after. -/
theorem ElemWritten.lengths {i : Nat} {s : Footprints.Change} {ix : Tm} {ρ : Env} {h h' : Heap}
    {fl idx : Nat} {ls0 : List (Option Nat)} {b : UInt64}
    (hw : ElemWritten i s ix ρ h h') (hs : Footprints.spineOf (ρ i) = some fl) (hls0 : h[fl]? = some (.arr ls0))
    (hb : ix = .num b) (hidx : indexOfBits b = some idx) (hlt : idx < ls0.length) :
    (⟨true, true, .length⟩ : HeapKnowledge.Changes).Holds h h' := by
  refine ⟨fun _ v _ ha => by cases v <;> simp_all [HeapKnowledge.Changes.alters], fun _ l ls hl => ?_,
    fun hg => by simp at hg⟩
  by_cases hf : l = fl
  · subst hf
    rw [hls0] at hl; cases hl
    obtain ⟨ls', hl', hlen⟩ := hw.2 l ls0 b idx hs hls0 hb hidx
    exact ⟨ls', hl', by omega⟩
  · obtain ⟨v', hv', ha⟩ := hw.1.2 l _ hl
    rcases ha with rfl | ⟨e, he, hm, -⟩
    · exact ⟨ls, hv', rfl⟩
    · simp only [elemWriteFrame, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp only [Footprints.Region.mem, Bool.and_eq_true, beq_iff_eq] at hm
        exact absurd (Option.some.inj (hm.1.symm.trans hs)) hf
      · simp [Footprints.Region.mem, hl, Footprints.isArr] at hm

/-- The spine location of the object in slot `i`, holding an array spine,
is in the frame's spine region. -/
theorem spine_mem_frame {ρ : Env} {i : Nat} {h : Heap} {fl : Nat} {ls : List (Option Nat)}
    (hs : Footprints.spineOf (ρ i) = some fl) (hfl : h[fl]? = some (.arr ls)) :
    ((Footprints.Region.field i arraySpineKey).inCls .arrays).mem ρ h fl = true := by
  simp only [Footprints.Region.mem, Bool.and_eq_true, beq_iff_eq, hfl]
  exact ⟨hs, rfl⟩

/-- A location the spine of the object in slot `i` lists, holding a value,
is in the frame's cell region. -/
theorem cell_mem_frame {ρ : Env} {i : Nat} {h : Heap} {fl l : Nat} {ls : List (Option Nat)} {u : Val}
    (hs : Footprints.spineOf (ρ i) = some fl) (hfl : h[fl]? = some (.arr ls)) (hm : some l ∈ ls)
    (hl : h[l]? = some u) (hu : Footprints.isArr u = false) :
    ((Footprints.Region.cells i).inCls .values).mem ρ h l = true := by
  have hs' : (Footprints.fieldsOf (ρ i)).lookup arraySpineKey = some fl := hs
  simp [Footprints.Region.mem, Footprints.spineCells, Footprints.entriesAt, hs', hfl, spineEntries, hm, hl, hu]

/-- **A write at a listed cell is within the frame**: the spine put back
unchanged and the cell, which held a value, written. -/
theorem elem_present_written {i : Nat} {s : Footprints.Change} {ix : Tm} {ρ : Env} {h : Heap}
    {fl l idx : Nat} {ls : List (Option Nat)} {v u : Val}
    (hs : Footprints.spineOf (ρ i) = some fl) (hfl : h[fl]? = some (.arr ls)) (hlk : ls[idx]? = some (some l))
    (hl : h[l]? = some u) (hu : Footprints.isArr u = false)
    (hix : ∀ b idx', ix = .num b → indexOfBits b = some idx' → idx' = idx) :
    ElemWritten i s ix ρ h ((h.set l v).set fl (.arr ls)) := by
  have hflt := (List.getElem?_eq_some_iff.mp hfl).1
  refine ⟨⟨by simp, fun l' w hw => ?_⟩, fun fl' ls' b idx' hs' hfl' hb hidx' => ?_⟩
  · by_cases hf : l' = fl
    · subst hf
      rw [hfl] at hw; cases hw
      exact ⟨.arr ls, by rw [List.getElem?_set_self (by simpa using hflt)], .inl rfl⟩
    · by_cases hll : l' = l
      · subst hll
        rw [hl] at hw; cases hw
        refine ⟨v, ?_, .inr ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
          cell_mem_frame hs hfl (List.mem_of_getElem? hlk) hl hu, trivial⟩⟩
        rw [List.getElem?_set_ne (Ne.symm hf), List.getElem?_set_self (List.getElem?_eq_some_iff.mp hl).1]
      · exact ⟨w, by rw [List.getElem?_set_ne (Ne.symm hf), List.getElem?_set_ne (Ne.symm hll), hw], .inl rfl⟩
  · rw [hs] at hs'; cases hs'
    rw [hfl] at hfl'; cases hfl'
    obtain rfl := hix b idx' hb hidx'
    have hlt := (List.getElem?_eq_some_iff.mp hlk).1
    exact ⟨ls, by rw [List.getElem?_set_self (by simpa using hflt)], by omega⟩

/-- **A write taking a fresh cell is within the frame**: the spine grown by
`placeAt`, at a hole, at its length or past it, nothing else of the entry
heap changed. -/
theorem elem_grow_written {i : Nat} {ix : Tm} {ρ : Env} {h : Heap} {fl idx : Nat} {ls : List (Option Nat)}
    {v : Val} (hs : Footprints.spineOf (ρ i) = some fl) (hfl : h[fl]? = some (.arr ls))
    (hk : idx < maxArrayLength) (hix : ∀ b idx', ix = .num b → indexOfBits b = some idx' → idx' = idx) :
    ElemWritten i .grow ix ρ h ((h ++ [v]).set fl (.arr (placeAt ls idx h.length))) := by
  have hflt := (List.getElem?_eq_some_iff.mp hfl).1
  have hc := (Footprints.Closed.holds_iff.mp (elem_grow_holds (v := v) hfl hk)).2
  refine ⟨⟨by simp, fun l' w hw => ?_⟩, fun fl' ls' b idx' hs' hfl' hb hidx' => ?_⟩
  · by_cases hf : l' = fl
    · subst hf
      obtain ⟨w', hw', hch⟩ := hc l' w hw
      rw [hfl] at hw; cases hw
      exact ⟨w', hw', .inr ⟨_, List.mem_cons_self .., spine_mem_frame hs hfl, hch⟩⟩
    · exact ⟨w, by rw [List.getElem?_set_ne (Ne.symm hf),
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp hw).1, hw], .inl rfl⟩
  · rw [hs] at hs'; cases hs'
    rw [hfl] at hfl'; cases hfl'
    obtain rfl := hix b idx' hb hidx'
    exact ⟨_, by rw [List.getElem?_set_self (by simp; omega)], by rw [placeAt_length]; omega⟩

theorem elem_read_inv {f : PropKey} {flds : List (PropKey × Nat)} {c : CallCode} {oid : Nat} {iv : Tm}
    {v : Tm} {h h' : Heap} {t : Tm} {fl : Nat} (hf : flds.lookup f = some fl)
    (hs : Step h (.writeAt f (.objAt flds c oid) (.setElem (.readAt f (.objAt flds c oid)) iv v)) h' t) :
    ∃ u, h[fl]? = some u ∧ h = h' ∧ t = .writeAt f (.objAt flds c oid) (.setElem u iv v) := by
  cases hs with
  | writeC1 s => exact False.elim (value_no_step rfl s)
  | writeC2 _ s =>
    cases s with
    | setC1 s =>
      cases s with
      | readC s => exact False.elim (value_no_step rfl s)
      | readField hf' hu => rw [hf] at hf'; cases hf'; exact ⟨_, hu, rfl, rfl⟩
      | readProto hn _ _ => rw [hf] at hn; cases hn
      | readMissing hn _ => rw [hf] at hn; cases hn
    | setC2 hval _ => simp [isVal] at hval
    | setC3 hval _ _ => simp [isVal] at hval
  | writeField hval _ _ => simp [isVal] at hval

theorem elem_set_inv {f : PropKey} {o u v iv : Tm} {h h' : Heap} {t : Tm}
    (ho : isVal o = true) (hu : isVal u = true) (hiv : isVal iv = true) (hv : isVal v = true)
    (hs : Step h (.writeAt f o (.setElem u iv v)) h' t) :
    ∃ b ls, iv = .num b ∧ u = .arr ls ∧
      ((∃ l, elemLoc ls b = some l ∧ h' = h.set l v ∧ t = .writeAt f o (.arr ls)) ∨
       (∃ k, indexOfBits b = some k ∧ elemLoc ls b = none ∧ h' = h ++ [v] ∧
          t = .writeAt f o (.arr (placeAt ls k h.length)))) := by
  cases hs with
  | writeC1 s => exact False.elim (value_no_step ho s)
  | writeC2 _ s =>
    cases s with
    | setC1 s => exact False.elim (value_no_step hu s)
    | setC2 _ s => exact False.elim (value_no_step hiv s)
    | setC3 _ _ s => exact False.elim (value_no_step hv s)
    | setPresent _ hl _ => exact ⟨_, _, rfl, rfl, .inl ⟨_, hl, rfl, rfl⟩⟩
    | setGrow _ hk hn => exact ⟨_, _, rfl, rfl, .inr ⟨_, hk, hn, rfl, rfl⟩⟩
  | writeField hval _ _ => simp [isVal] at hval

/-- A term writing a value into a field of a value raises nothing. -/
theorem write_values_not_thrown {f : PropKey} {o u : Tm} {k W} (ho : isVal o = true) (hu : isVal u = true) :
    ¬ Thrown Ξ k W (.writeAt f o u) := by
  rintro ⟨_, hr, _⟩
  cases hr with
  | writeC1 r => rw [raises_not_val r] at ho; contradiction
  | writeC2 _ r => rw [raises_not_val r] at hu; contradiction

/-- The last step of an element write puts the spine back; the heap it
ends in is the one `P` holds of. -/
theorem write_back {f : PropKey} {flds : List (PropKey × Nat)} {c : CallCode} {oid fl : Nat}
    {ls' : List (Option Nat)} {P Q : Heap → Prop} {T : Fam} {n U h2}
    (hfd : flds.lookup f = some fl) (hq : P (h2.set fl (.arr ls')))
    (hs : Safe Ξ T n U h2 (.writeAt f (.objAt flds c oid) (.arr ls'))) :
    SafePostExc Ξ T (fun h' _ => P h') Q n U h2 (.writeAt f (.objAt flds c oid) (.arr ls')) := by
  cases n with
  | zero => assumption
  | succ n =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hbad, _⟩ | hr) | ⟨U3, h3, t3, hx, hu, st, hh3, hs3⟩
    · simp [isVal] at hbad
    · exact absurd hr (write_values_not_thrown rfl rfl)
    obtain ⟨flds', c', oid', l3, ho, hl3, -, rfl, rfl⟩ := HeapExpressionRules.write_inv rfl rfl st
    cases ho
    rw [hfd] at hl3; cases hl3
    refine .inr ⟨U3, _, _, hx, hu, st, hh3, ?_⟩
    cases n with
    | zero => assumption
    | succ m =>
      obtain ⟨hrf, hs3⟩ := hs3
      refine ⟨hrf, ?_⟩
      rcases hs3 with (⟨hv, ht⟩ | hr) | ⟨_, _, _, _, _, st', _, _⟩
      · exact .inl (.inl ⟨hv, ht, hq⟩)
      · exact absurd hr (val_not_thrown rfl)
      · exact False.elim (value_no_step rfl st')

theorem write_back_post {f : PropKey} {flds : List (PropKey × Nat)} {c : CallCode} {oid fl : Nat}
    {ls' : List (Option Nat)} {P : Heap → Prop} {T : Fam} {n U h2}
    (hfd : flds.lookup f = some fl) (hq : P (h2.set fl (.arr ls')))
    (hs : Safe Ξ T n U h2 (.writeAt f (.objAt flds c oid) (.arr ls'))) :
    SafePostExc Ξ T (fun h' _ => P h') (fun h' => P h') n U h2 (.writeAt f (.objAt flds c oid) (.arr ls')) :=
  write_back hfd hq hs

/-- **An element write at a literal index leaves its frame and its exact
postcondition** (`ElemWritten`), its spine at `keep` at a required position
and at `grow` otherwise; where it raises, it has written nothing. -/
theorem elem_write_core [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {i k : Nat}
    {b : UInt64} {idx : Nat} {Ref : Ty ι} {present : Bool} {T : Fam} {ρ n W h}
    (hk : k < Γ.length) (hi : Γ[i]? = some Ref) (hidx : indexOfBits b = some idx)
    (hst : spineField G (expand G Ref) arraySpineKey idx present = true)
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ
      (.writeAt arraySpineKey (.var i) (.setElem (.readAt arraySpineKey (.var i)) (.num b) (.var k))))) :
    SafePostExc Ξ T (fun h' _ => ElemWritten i (if present then .keep else .grow) (.num b) ρ h h')
      (fun h' => h' = h) n W h
      (instantiate 0 ρ (.writeAt arraySpineKey (.var i) (.setElem (.readAt arraySpineKey (.var i)) (.num b) (.var k)))) := by
  have hvv := (meaning_value (he.2 k Γ[k] (List.getElem?_eq_getElem hk))).1
  obtain ⟨B, _, L, hmem, hspine, hbag⟩ := spineField_sound hst (he.2 i Ref hi)
  obtain ⟨flds, code, oid, hl0, _, hrec⟩ := hbag
  obtain ⟨flds1, fl, cfl, oid', hproj, hfd, hlookup, hagree⟩ :=
    recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨L, hmem, rfl⟩) hrec
  cases hproj
  have hsp : Footprints.spineOf (ρ i) = some fl := by
    simpa [Footprints.spineOf, Footprints.fieldsOf, hl0] using hfd
  have hix : ∀ b' idx', Tm.num b = .num b' → indexOfBits b' = some idx' → idx' = idx := by
    intro b' idx' hb' hi'
    cases hb'
    rw [hidx] at hi'
    exact (Option.some.inj hi').symm
  simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
  rw [hl0] at hs ⊢
  generalize hvk : ρ k = v at hs hvv ⊢
  cases n with
  | zero => assumption
  | succ n1 =>
  obtain ⟨hrf, hs⟩ := hs
  refine ⟨hrf, ?_⟩
  rcases hs with (⟨hbad, _⟩ | hr) | ⟨U1, h1, t1, hx1, hu1, step1, hh1, hs1⟩
  · simp [isVal] at hbad
  · exact .inl (.inr ⟨hr, rfl⟩)
  obtain ⟨u, hfu, rfl, rfl⟩ := elem_read_inv hfd step1
  refine .inr ⟨U1, h, _, hx1, hu1, step1, hh1, ?_⟩
  cases n1 with
  | zero => assumption
  | succ n2 =>
  -- The spine field's contents meet its spine type.
  obtain ⟨u0, hu0, hcu⟩ := hh.1.2 fl cfl hlookup
  rw [hfu] at hu0; cases hu0
  have hmL : meaning G L 1 (trunc 1 (by omega) W) u := (hagree 1 (by omega) _ u).mp (hcu 1 (by omega))
  have huv := (meaning_value hmL).1
  obtain ⟨hrf, hs1⟩ := hs1
  refine ⟨hrf, ?_⟩
  rcases hs1 with (⟨hbad, _⟩ | hr) | ⟨U2, h2, t2, hx2, hu2, step2, hh2, hs2⟩
  · simp [isVal] at hbad
  · exact .inl (.inr ⟨hr, rfl⟩)
  obtain ⟨b', ls, hb', rfl, hcase⟩ := elem_set_inv rfl huv rfl hvv step2
  cases hb'
  unfold spineTy at hspine
  split at hspine
  case h_2 => contradiction
  rename_i Tup hexp
  have hlist := (represents_raw (show Represents G L (.list Tup []) from hexp) 1 _ _ hmL).1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hspine
  obtain ⟨hpos, hpresent⟩ := hspine
  rcases hcase with ⟨l, hl, rfl, rfl⟩ | ⟨k', hk', hn, rfl, rfl⟩
  · -- A listed position: its location held a source value, which is no spine.
    have hlk : ls[idx]? = some (some l) := by
      simp only [elemLoc, hidx, Option.bind_some] at hl
      cases hls : ls[idx]? with
      | none => simp [hls] at hl
      | some o => cases o with
        | none => simp [hls] at hl
        | some l' => simp [hls] at hl; subst hl; rfl
    split at hpos
    case h_2 => contradiction
    rename_i A hA
    obtain ⟨c', hc', himp⟩ := listT_slot hlist hlk
      (by rw [ProgramTyping.positionFam_tupleFams, hA]; rfl)
    obtain ⟨c, hc, rfl⟩ := lookup_trunc_inv _ W l c' hc'
    obtain ⟨w, hw, hcw⟩ := hh.1.2 l c hc
    have hmA : meaning G A 0 (trunc 0 (by omega) W) w := himp 0 (by omega) _ w (hcw 0 (by omega))
    have hnarr : Footprints.isArr w = false := by
      have := sourceTy_sound hpos hmA
      cases w <;> simp_all [isSourceVal, Footprints.isArr]
    exact .inr ⟨U2, _, _, hx2, hu2, step2, hh2, write_back hfd (elem_present_written hsp hfu hlk hw hnarr hix) hs2⟩
  · -- A fresh location: a required position is listed, so the index is not one.
    rw [hidx] at hk'; cases hk'
    cases present with
    | true =>
      have hp : idx < Tup.required.length := by simpa using hpresent
      obtain ⟨ls', heq, -, -, -, -, hreq, -, -⟩ := hlist
      cases heq
      obtain ⟨l, -, hl, -, -⟩ := hreq idx _ (by
        simp only [PositiveNormalization.tupleFams, List.getElem?_map]
        rw [List.getElem?_eq_getElem hp]; rfl)
      simp [elemLoc, hidx, hl] at hn
    | false =>
      exact .inr ⟨U2, _, _, hx2, hu2, step2, hh2,
        write_back hfd (elem_grow_written hsp hfu (indexOfBits_lt hidx) hix) hs2⟩

/-! ### Element writes at a run-time index

`o[k] = v` with `k` a slot (FOOTPRINTS.md, "Element writes"): where every
position of the spine's tuple contract holds source values, a tuple of no
required or optional position whose rest does, the write is within
`{o.spine: grow, o.cells: any}` whatever index the slot holds, as a literal
index's write is (`elem_write_core`). -/

/-- The slots of an element write at a run-time index: the object's, its
spine field, the index's and the written value's. -/
def elemVarWriteSlots : Tm → Option (PropKey × Nat × Nat × Nat)
  | .writeAt f (.var i) (.setElem (.readAt f' (.var i')) (.var j) (.var k)) =>
    if f' = f ∧ i' = i then some (f, i, j, k) else none
  | _ => none

theorem elemVarWriteSlots_eq {t f i j k} (h : elemVarWriteSlots t = some (f, i, j, k)) :
    t = .writeAt f (.var i) (.setElem (.readAt f (.var i)) (.var j) (.var k)) := by
  unfold elemVarWriteSlots at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h; rfl
    · cases h
  · cases h

/-- A spine type every position of which holds source values: a tuple of no
required or optional position whose rest holds them. -/
def spineTyEvery (G : NormalGraph ι) (L : Ty ι) : Bool :=
  match expand G L with
  | [.list ⟨[], [], some A, _, _⟩ []] => sourceTy G A
  | _ => false

theorem spineTyEvery_at {G : NormalGraph ι} {L : Ty ι} (h : spineTyEvery G L = true) (idx : Nat) :
    spineTy G L idx false = true := by
  unfold spineTyEvery at h
  split at h
  · rename_i A ro pr hexp
    simp [spineTy, hexp, positionTy, h]
  · cases h

/-- Every alternative is a record whose first invariant operand has the field
`fld`, at a spine type `spineTyEvery` accepts in each. -/
def spineFieldEvery (G : NormalGraph ι) (cs : List (PositiveNormalization.Clause (Ty ι))) (fld : PropKey) : Bool :=
  !cs.isEmpty && cs.all fun c => match HeapExpressionRules.clauseBagOperand c with
    | some B => B.any (fun p => decide (p.1 = fld)) && B.all (fun p => !decide (p.1 = fld) || spineTyEvery G p.2.2)
    | none => false

theorem spineFieldEvery_sound [DecidableEq ι] {G : NormalGraph ι} {Ref fld n W v}
    (hr : spineFieldEvery G (expand G Ref) fld = true) (hv : meaning G Ref n W v) :
    ∃ B s L, (fld, s, L) ∈ B ∧ spineTyEvery G L = true ∧
      bagT (ReferenceConjunctions.famsOf (meaning G) B) n W v := by
  simp only [spineFieldEvery, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
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
    obtain ⟨⟨g, s, El⟩, hmem, hg⟩ := List.any_eq_true.mp hany
    simp only [decide_eq_true_eq] at hg
    subst hg
    have hsrc : spineTyEvery G El = true := (hall _ hmem).resolve_left (by simp)
  · exact ⟨_, s, El, hmem, hsrc, recT_bag hc.1.1⟩
  · exact ⟨_, s, El, hmem, hsrc, hc.1.1.1.1⟩

/-- **An element write at a run-time index leaves its frame and its exact
postcondition** (`ElemWritten`), its spine at `grow`; where it raises, it
has written nothing. The index decodes, where the write steps, to some
position of the spine, which every position the spine's contract holds
source values at. -/
theorem elem_var_write_core [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {i j k : Nat}
    {Ref : Ty ι} {T : Fam} {ρ n W h}
    (hk : k < Γ.length) (hj : j < Γ.length) (hi : Γ[i]? = some Ref)
    (hst : spineFieldEvery G (expand G Ref) arraySpineKey = true)
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ
      (.writeAt arraySpineKey (.var i) (.setElem (.readAt arraySpineKey (.var i)) (.var j) (.var k))))) :
    SafePostExc Ξ T (fun h' _ => ElemWritten i .grow (ρ j) ρ h h') (fun h' => h' = h) n W h
      (instantiate 0 ρ (.writeAt arraySpineKey (.var i) (.setElem (.readAt arraySpineKey (.var i)) (.var j) (.var k)))) := by
  have hvv := (meaning_value (he.2 k Γ[k] (List.getElem?_eq_getElem hk))).1
  have hjv := (meaning_value (he.2 j Γ[j] (List.getElem?_eq_getElem hj))).1
  obtain ⟨B, _, L, hmem, hevery, hbag⟩ := spineFieldEvery_sound hst (he.2 i Ref hi)
  obtain ⟨flds, code, oid, hl0, _, hrec⟩ := hbag
  obtain ⟨flds1, fl, cfl, oid', hproj, hfd, hlookup, hagree⟩ :=
    recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨L, hmem, rfl⟩) hrec
  cases hproj
  have hsp : Footprints.spineOf (ρ i) = some fl := by
    simpa [Footprints.spineOf, Footprints.fieldsOf, hl0] using hfd
  simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
  rw [hl0] at hs ⊢
  generalize hvk : ρ k = v at hs hvv ⊢
  generalize hjk : ρ j = iv at hs hjv ⊢
  cases n with
  | zero => assumption
  | succ n1 =>
  obtain ⟨hrf, hs⟩ := hs
  refine ⟨hrf, ?_⟩
  rcases hs with (⟨hbad, _⟩ | hr) | ⟨U1, h1, t1, hx1, hu1, step1, hh1, hs1⟩
  · simp [isVal] at hbad
  · exact .inl (.inr ⟨hr, rfl⟩)
  obtain ⟨u, hfu, rfl, rfl⟩ := elem_read_inv hfd step1
  refine .inr ⟨U1, h, _, hx1, hu1, step1, hh1, ?_⟩
  cases n1 with
  | zero => assumption
  | succ n2 =>
  obtain ⟨u0, hu0, hcu⟩ := hh.1.2 fl cfl hlookup
  rw [hfu] at hu0; cases hu0
  have hmL : meaning G L 1 (trunc 1 (by omega) W) u := (hagree 1 (by omega) _ u).mp (hcu 1 (by omega))
  have huv := (meaning_value hmL).1
  obtain ⟨hrf, hs1⟩ := hs1
  refine ⟨hrf, ?_⟩
  rcases hs1 with (⟨hbad, _⟩ | hr) | ⟨U2, h2, t2, hx2, hu2, step2, hh2, hs2⟩
  · simp [isVal] at hbad
  · exact .inl (.inr ⟨hr, rfl⟩)
  obtain ⟨b, ls, rfl, rfl, hcase⟩ := elem_set_inv rfl huv hjv hvv step2
  rcases hcase with ⟨l, hl, rfl, rfl⟩ | ⟨k', hk', hn, rfl, rfl⟩
  · -- A listed position: its location held a source value, which is no spine.
    obtain ⟨idx, hidx⟩ : ∃ idx, indexOfBits b = some idx := by
      simp only [elemLoc] at hl
      cases hb : indexOfBits b with
      | none => simp [hb] at hl
      | some idx => exact ⟨idx, rfl⟩
    have hspine := spineTyEvery_at hevery idx
    unfold spineTy at hspine
    split at hspine
    case h_2 => contradiction
    rename_i Tup hexp
    have hlist := (represents_raw (show Represents G L (.list Tup []) from hexp) 1 _ _ hmL).1
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hspine
    obtain ⟨hpos, -⟩ := hspine
    have hlk : ls[idx]? = some (some l) := by
      simp only [elemLoc, hidx, Option.bind_some] at hl
      cases hls : ls[idx]? with
      | none => simp [hls] at hl
      | some o => cases o with
        | none => simp [hls] at hl
        | some l' => simp [hls] at hl; subst hl; rfl
    split at hpos
    case h_2 => contradiction
    rename_i A hA
    obtain ⟨c', hc', himp⟩ := listT_slot hlist hlk
      (by rw [ProgramTyping.positionFam_tupleFams, hA]; rfl)
    obtain ⟨c, hc, rfl⟩ := lookup_trunc_inv _ W l c' hc'
    obtain ⟨w, hw, hcw⟩ := hh.1.2 l c hc
    have hmA : meaning G A 0 (trunc 0 (by omega) W) w := himp 0 (by omega) _ w (hcw 0 (by omega))
    have hnarr : Footprints.isArr w = false := by
      have := sourceTy_sound hpos hmA
      cases w <;> simp_all [isSourceVal, Footprints.isArr]
    exact .inr ⟨U2, _, _, hx2, hu2, step2, hh2, write_back hfd (elem_present_written hsp hfu hlk hw hnarr
      fun b' idx' hb' hi' => by cases hb'; rw [hidx] at hi'; exact (Option.some.inj hi').symm) hs2⟩
  · exact .inr ⟨U2, _, _, hx2, hu2, step2, hh2, write_back hfd (elem_grow_written hsp hfu (indexOfBits_lt hk')
      fun b' idx' hb' hi' => by cases hb'; rw [hk'] at hi'; exact (Option.some.inj hi').symm) hs2⟩

theorem Changes.length_refl (h : Heap) : (⟨true, true, .length⟩ : HeapKnowledge.Changes).Holds h h :=
  ⟨fun _ _ hv _ => hv, fun _ _ ls hls => ⟨ls, hls, rfl⟩, fun hg => by simp at hg⟩

/-- **An element write below its spine's length keeps every spine's
length** (ARITHMETIC.md, "Linear facts"; the note's Write-In): its exact
postcondition at an index below the length (`ElemWritten.lengths`). -/
theorem elem_var_write_length [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {i j k : Nat}
    {Ref : Ty ι} {T : Fam} {ρ n W h} {flds : List (PropKey × Nat)} {cd : CallCode} {oid fl : Nat}
    {ls0 : List (Option Nat)} {b0 : UInt64} {idx : Nat}
    (hk : k < Γ.length) (hj : j < Γ.length) (hi : Γ[i]? = some Ref)
    (hst : spineFieldEvery G (expand G Ref) arraySpineKey = true)
    (hoi : ρ i = .objAt flds cd oid) (hfl : flds.lookup arraySpineKey = some fl) (hls0 : h[fl]? = some (.arr ls0))
    (hb0 : ρ j = .num b0) (hidx : indexOfBits b0 = some idx) (hlt : idx < ls0.length)
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ
      (.writeAt arraySpineKey (.var i) (.setElem (.readAt arraySpineKey (.var i)) (.var j) (.var k))))) :
    SafePostExc Ξ T (fun h' _ => (⟨true, true, .length⟩ : HeapKnowledge.Changes).Holds h h')
      (fun h' => (⟨true, true, .length⟩ : HeapKnowledge.Changes).Holds h h') n W h
      (instantiate 0 ρ (.writeAt arraySpineKey (.var i) (.setElem (.readAt arraySpineKey (.var i)) (.var j) (.var k)))) :=
  have hsp : Footprints.spineOf (ρ i) = some fl := by simpa [Footprints.spineOf, Footprints.fieldsOf, hoi] using hfl
  SafePostExc.weaken (fun _ _ hq => hq.lengths hsp hls0 hb0 hidx hlt)
    (fun _ hq => by rw [hq]; exact Changes.length_refl _) (elem_var_write_core hk hj hi hst he hh hs)

/-! ### An element write's step

`elemWriteStep` reads once, off the write's typing, the slot an element
write writes and its spine's change: `grow` at a run-time index whose every
position holds source values, and at a literal index `keep` where the
spine's contract requires the position and `grow` where it does not. Its
frame (`elemWriteFrame`) is the step's effect, and its closed weakening
(`elemWriteFrame_closed`) the grade the closed check reads. -/

/-- The typing an element write at a run-time index needs for its change. -/
def varWriteOk (G : NormalGraph ι) (Γ : List (Ty ι)) (f : PropKey) (i j k : Nat) : Bool :=
  decide (f = arraySpineKey) && decide (k < Γ.length) && decide (j < Γ.length) &&
    (match Γ[i]? with
      | some Ref => spineFieldEvery G (expand G Ref) f
      | none => false)

/-- The change of its spine an element write at the literal index `b`
makes: `keep` at a position the spine's contract requires, `grow` at
another position holding source values. -/
@[nospecialize] def litWriteChange (G : NormalGraph ι) (Γ : List (Ty ι)) (f : PropKey) (i : Nat) (b : UInt64)
    (k : Nat) : Option Footprints.Change :=
  if decide (f = arraySpineKey) && decide (k < Γ.length) then
    match Γ[i]?, indexOfBits b with
    | some Ref, some idx =>
      if spineField G (expand G Ref) f idx true then some .keep
      else if spineField G (expand G Ref) f idx false then some .grow else none
    | _, _ => none
  else none

theorem litWriteChange_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {f : PropKey} {i : Nat} {b : UInt64}
    {k : Nat} {s : Footprints.Change} (h : litWriteChange G Γ f i b k = some s) :
    f = arraySpineKey ∧ k < Γ.length ∧ ∃ Ref idx present, Γ[i]? = some Ref ∧ indexOfBits b = some idx ∧
      spineField G (expand G Ref) f idx present = true ∧ s = (if present then .keep else .grow) := by
  unfold litWriteChange at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨hc.1, hc.2, ?_⟩
    split at h
    · rename_i Ref idx hi hidx
      split at h
      · rename_i ht
        cases h
        exact ⟨Ref, idx, true, hi, hidx, ht, rfl⟩
      · split at h
        · rename_i hf
          cases h
          exact ⟨Ref, idx, false, hi, hidx, hf, rfl⟩
        · cases h
    · cases h
  · cases h

/-- **The slot and the spine change of a typed element write**: of the
array in a slot whose type gives its spine a contract holding source values
at the written position (`varWriteOk`, `litWriteChange`). -/
@[nospecialize] def elemWriteStep (G : NormalGraph ι) (Γ : List (Ty ι)) (t : Tm) : Option (Nat × Footprints.Change) :=
  match elemVarWriteSlots t with
  | some (f, i, j, k) => if varWriteOk G Γ f i j k then some (i, .grow) else none
  | none => match elemWriteSlots t with
    | some (f, i, b, k) => (litWriteChange G Γ f i b k).map (i, ·)
    | none => none

/-- What `elemWriteStep` reads off a write: its term, at a run-time index
or a literal one, and the typing of each. -/
theorem elemWriteStep_cases {G : NormalGraph ι} {Γ : List (Ty ι)} {t : Tm} {i : Nat} {s : Footprints.Change}
    (hc : elemWriteStep G Γ t = some (i, s)) :
    (∃ j k Ref, t = .writeAt arraySpineKey (.var i) (.setElem (.readAt arraySpineKey (.var i)) (.var j) (.var k)) ∧
      k < Γ.length ∧ j < Γ.length ∧ Γ[i]? = some Ref ∧
      spineFieldEvery G (expand G Ref) arraySpineKey = true ∧ s = .grow) ∨
    (∃ b k Ref idx present,
      t = .writeAt arraySpineKey (.var i) (.setElem (.readAt arraySpineKey (.var i)) (.num b) (.var k)) ∧
      k < Γ.length ∧ Γ[i]? = some Ref ∧ indexOfBits b = some idx ∧
      spineField G (expand G Ref) arraySpineKey idx present = true ∧ s = (if present then .keep else .grow)) := by
  unfold elemWriteStep at hc
  split at hc
  · rename_i f i' j k hw
    split at hc
    · rename_i hcond
      cases hc
      simp only [varWriteOk, Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨rfl, hk⟩, hj⟩, hsel⟩ := hcond
      split at hsel
      · rename_i Ref hi
        exact .inl ⟨j, k, Ref, elemVarWriteSlots_eq hw, hk, hj, hi, hsel, rfl⟩
      · cases hsel
    · cases hc
  · split at hc
    · rename_i f i' b k hw
      obtain ⟨s', hs', he⟩ := Option.map_eq_some_iff.mp hc
      cases he
      obtain ⟨rfl, hk, Ref, idx, present, hi, hidx, hst, rfl⟩ := litWriteChange_sound hs'
      exact .inr ⟨b, k, Ref, idx, present, elemWriteSlots_eq hw, hk, hi, hidx, hst, rfl⟩
    · cases hc

/-- The index an element write's term writes at. -/
def writeIndexOf : Tm → Tm
  | .writeAt _ _ (.setElem _ ix _) => ix
  | _ => .undef

/-- **A typed element write leaves its frame and its exact postcondition**
(`ElemWritten`) on normal return, and raises, where it does, before it
writes: at its entry heap. -/
theorem elemWriteStep_sound [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {t : Tm} {i : Nat}
    {s : Footprints.Change} {T : Fam} {ρ n W h} (hc : elemWriteStep G Γ t = some (i, s))
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h) (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePostExc Ξ T (fun h' _ => ElemWritten i s (instantiate 0 ρ (writeIndexOf t)) ρ h h') (fun h' => h' = h)
      n W h (instantiate 0 ρ t) := by
  rcases elemWriteStep_cases hc with ⟨j, k, Ref, rfl, hk, hj, hi, hst, rfl⟩ |
    ⟨b, k, Ref, idx, present, rfl, hk, hi, hidx, hst, rfl⟩
  · have hix : instantiate 0 ρ (.var j) = ρ j := by simp [instantiate]
    simp only [writeIndexOf, hix]
    exact elem_var_write_core hk hj hi hst he hh hs
  · simp only [writeIndexOf, instantiate]
    exact elem_write_core hk hi hidx hst he hh hs

/-- The spine change `elemWriteStep` reads is within `grow`. -/
theorem elemWriteStep_le_grow {G : NormalGraph ι} {Γ : List (Ty ι)} {t : Tm} {i : Nat} {s : Footprints.Change}
    (hc : elemWriteStep G Γ t = some (i, s)) :
    (Footprints.Closed.ofSpines .any s).le ⟨.any, .grow, .grow⟩ = true := by
  rcases elemWriteStep_cases hc with ⟨-, -, -, -, -, -, -, -, rfl⟩ | ⟨-, -, -, -, present, -, -, -, -, -, rfl⟩
  · rfl
  · cases present <;> rfl

/-- **A typed element write is within `{value: any, spine: s}`**, on normal
return and where it raises: its frame's closed weakening
(`elemWriteFrame_closed`). -/
theorem elemWriteStep_closed [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {t : Tm} {i : Nat}
    {s : Footprints.Change} {T : Fam} {ρ n W h} (hc : elemWriteStep G Γ t = some (i, s))
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h) (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePostExc Ξ T (fun h' _ => (Footprints.Closed.ofSpines .any s).Holds h h')
      (fun h' => (Footprints.Closed.ofSpines .any s).Holds h h') n W h (instantiate 0 ρ t) :=
  SafePostExc.weaken (fun _ _ hq => elemWriteFrame_closed hq.1)
    (fun _ hq => by rw [hq]; exact Footprints.Closed.Holds.refl _ h) (elemWriteStep_sound hc he hh hs)

/-- An element write within `Φ`: its closed grade `{value: any, spine: s}`
within `Φ`. -/
def elemWriteWithin (G : NormalGraph ι) (Γ : List (Ty ι)) (Φ : Footprints.Closed) (t : Tm) : Bool :=
  match elemWriteStep G Γ t with
  | some (_, s) => (Footprints.Closed.ofSpines .any s).le Φ
  | none => false

theorem elem_write_within_exc [DecidableEq ι] {G : NormalGraph ι} {Γ Φ t T ρ n W h}
    (hc : elemWriteWithin G Γ Φ t = true) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePostExc Ξ T (fun h' _ => Φ.Holds h h') (fun h' => Φ.Holds h h') n W h (instantiate 0 ρ t) := by
  unfold elemWriteWithin at hc
  split at hc
  · rename_i i s hw
    exact SafePostExc.weaken (fun _ _ hq => Footprints.Closed.Holds.mono hc hq)
      (fun _ hq => Footprints.Closed.Holds.mono hc hq) (elemWriteStep_closed hw he hh hs)
  · cases hc

/-- A typed write within `Φ`: of a field holding a value, or of an element. -/
def writeWithin (G : NormalGraph ι) (Γ : List (Ty ι)) (Φ : Footprints.Closed) (t : Tm) : Bool :=
  fieldWriteWithin G Γ Φ t || elemWriteWithin G Γ Φ t

/-- **A typed write is within its footprint**, where it raises too. -/
theorem write_within_exc [DecidableEq ι] {G : NormalGraph ι} {Γ Φ t T ρ n W h}
    (hc : writeWithin G Γ Φ t = true) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePostExc Ξ T (fun h' _ => Φ.Holds h h') (fun h' => Φ.Holds h h') n W h (instantiate 0 ρ t) := by
  simp only [writeWithin, Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · exact field_write_within_exc hc he hh hs
  · exact elem_write_within_exc hc he hh hs

theorem write_within [DecidableEq ι] {G : NormalGraph ι} {Γ Φ t T ρ n W h}
    (hc : writeWithin G Γ Φ t = true) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' _ => Φ.Holds h h') n W h (instantiate 0 ρ t) :=
  SafePostExc.post (write_within_exc hc he hh hs)

/-- **An element write grows the spines** (ARITHMETIC.md, "Linear facts"):
its closed grade is within `{value: any, spine: grow}`, so it alters
locations holding objects and numbers and leaves every spine no shorter and
within `maxArrayLength` where it was (`HeapKnowledge.Changes.ofClosed`). -/
theorem elemWriteStep_grow [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {t : Tm}
    {w : Nat × Footprints.Change} {T : Fam} {ρ n W h} (hc : elemWriteStep G Γ t = some w)
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h) (hs : Safe Ξ T n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' _ => (HeapKnowledge.Changes.ofClosed ⟨.any, .grow, .grow⟩).Holds h h') n W h
      (instantiate 0 ρ t) := by
  obtain ⟨i, s⟩ := w
  exact SafePostExc.post (SafePostExc.weaken
    (fun _ _ hq => HeapKnowledge.Changes.ofClosed_holds (Footprints.Closed.Holds.mono (elemWriteStep_le_grow hc) hq))
    (fun _ hq => HeapKnowledge.Changes.ofClosed_holds (Footprints.Closed.Holds.mono (elemWriteStep_le_grow hc) hq))
    (elemWriteStep_closed hc he hh hs))


/-! ## A write's local effect

Each write rule above admits a bound `Φ` exactly where one of the closed
footprints its side conditions grant is below `Φ`: the rule's own grade,
which reads no bound. `writeGrades` lists them; `writeWithin_eq_grades`
and `initWriteWithin_eq_grades` state the equality. -/

/-- The grade `g` where the side condition `c` holds, else none. -/
def grantIf (c : Bool) (g : Footprints.Closed) : List Footprints.Closed := if c then [g] else []

theorem grantIf_any (c : Bool) (g : Footprints.Closed) (p : Footprints.Closed → Bool) :
    (grantIf c g).any p = (c && p g) := by
  cases c <;> simp [grantIf]

/-- The grades a typed write's rules grant (`fieldWriteWithin`,
`elemWriteWithin`): each its frame's closed weakening, where the write's
step reads it. -/
def writeGrades (G : NormalGraph ι) (Γ : List (Ty ι)) (t : Tm) : List Footprints.Closed :=
  ((fieldWriteStep G Γ t).map fun _ => (⟨.any, .keep, .keep⟩ : Footprints.Closed)).toList ++
  ((fieldWriteStep G Γ t).bind fun _ =>
    if scalarWrite G Γ t then some (⟨.scalar, .keep, .keep⟩ : Footprints.Closed) else none).toList ++
  ((elemWriteStep G Γ t).map fun w => Footprints.Closed.ofSpines .any w.2).toList

/-- **A typed write's check is its grades' below the bound** (proved). -/
theorem writeWithin_eq_grades (G : NormalGraph ι) (Γ : List (Ty ι)) (Φ : Footprints.Closed) (t : Tm) :
    writeWithin G Γ Φ t = (writeGrades G Γ t).any (·.le Φ) := by
  simp only [writeWithin, writeGrades, List.any_append]
  congr 1
  · unfold fieldWriteWithin
    cases fieldWriteStep G Γ t <;> cases scalarWrite G Γ t <;> simp
  · unfold elemWriteWithin
    rcases elemWriteStep G Γ t with _ | ⟨i, s⟩ <;> simp

/-- The grade an initializing write's rule grants (`initWriteWithin`). -/
def initWriteGrades (G : NormalGraph ι) (Γ : List (Ty ι)) (k : HeapKnowledge.Knowledge) (t : Tm) :
    List Footprints.Closed :=
  match HeapExpressionRules.writeSlots t with
  | some (f, i, j) => grantIf (nullishAt k i f &&
      (match Γ[j]? with
      | some B => sourceTy G B
      | none => false) &&
      match Γ[i]? with
      | some Ref => sourceField G (expand G Ref) f
      | none => false) ⟨.init, .keep, .keep⟩
  | none => []

/-- **An initializing write's check is its grade below the bound** (proved). -/
theorem initWriteWithin_eq_grades (G : NormalGraph ι) (Γ : List (Ty ι)) (k : HeapKnowledge.Knowledge)
    (Φ : Footprints.Closed) (t : Tm) :
    initWriteWithin G Γ k Φ t = (initWriteGrades G Γ k t).any (·.le Φ) := by
  unfold initWriteWithin initWriteGrades
  split
  · rw [grantIf_any]
    simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
  · rfl

end Verification.ExpressionEffects
