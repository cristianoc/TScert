-- ResolutionDescriptors.lean defines descriptors relating a generic input to its observation and result; without it a lexical instance has no descriptor to retain.
import Verification.Types.ResolutionDescriptors
import Verification.Types.PositiveCertificates

/- Lexical instances of schemes whose binders carry resolution descriptors:
the body assignment retains each group's observation and descriptor, and a
lexical instance is admitted against its enclosing scheme. -/
namespace Verification.QualifiedGraphs
open PositiveGraphs PositiveNormalization ResolutionDescriptors Tower
open PositiveCertificates (ComparisonResult)

variable {ι : Type} {U N : Fam} {C : Capabilities U N}

open Classical in
/-- A value binder's assigned family, read through the graph. -/
theorem assigned_value (G : NormalGraph ι) (η : MixedAssignment ι)
    (s : SchemeRow ι) (As : List MixedFamily) (p : ι) (A : MixedFamily)
    (hp : (s.binders.zip As).lookup p = some A)
    (hk : G.parameterKinds p = some .value) :
    PositiveRules.mixedValues G (assign η s.binders As) [p] = A.value.1 := by
  have he := mixedMeaning_parameter G (assign η s.binders As) p .value hk
  funext n W v
  have hv := congrFun (congrFun (congrFun he n) W) (Sum.inl v)
  simpa [mixedMeaning, mixedParameters, PositiveRules.mixedValues,
    selectParameter, assign, hp, MixedFamily.value] using hv

open Classical in
/-- The body assignment retains every group's observation at its declared
binder nodes. -/
theorem assigned_observation (G : NormalGraph ι) (η : MixedAssignment ι)
    (s : SchemeRow ι) (As : List MixedFamily)
    (ha : (descriptorDomain C).allowed s As)
    (g : ResolutionSlots) (hg : g ∈ s.resolution) (t o : ι)
    (ht : (s.binders.zip As).lookup t = As[g.input]?)
    (ho : (s.binders.zip As).lookup o = As[g.observation]?)
    (kt : G.parameterKinds t = some .value)
    (ko : G.parameterKinds o = some .value) :
    ∃ d : Observation C,
      PositiveRules.mixedValues G (assign η s.binders As) [t] = d.input ∧
      PositiveRules.mixedValues G (assign η s.binders As) [o] = d.observation := by
  obtain ⟨d, T, O, hT, hO, eT, eO⟩ := allowed_observation C s As ha g hg
  exact ⟨d, (assigned_value G η s As t T (ht.trans hT) kt).trans eT,
    (assigned_value G η s As o O (ho.trans hO) ko).trans eO⟩

open Classical in
/-- The body assignment retains a resolvable group's descriptor at its
declared binder nodes. -/
theorem assigned_descriptor (G : NormalGraph ι) (η : MixedAssignment ι)
    (s : SchemeRow ι) (As : List MixedFamily)
    (ha : (descriptorDomain C).allowed s As)
    (g : ResolutionSlots) (hg : g ∈ s.resolution) (slot : Nat) (hs : g.result = some slot)
    (t o r : ι)
    (ht : (s.binders.zip As).lookup t = As[g.input]?)
    (ho : (s.binders.zip As).lookup o = As[g.observation]?)
    (hr : (s.binders.zip As).lookup r = As[slot]?)
    (kt : G.parameterKinds t = some .value)
    (ko : G.parameterKinds o = some .value)
    (kr : G.parameterKinds r = some .value) :
    ∃ d : Descriptor C,
      PositiveRules.mixedValues G (assign η s.binders As) [t] = d.input ∧
      PositiveRules.mixedValues G (assign η s.binders As) [o] = d.observation ∧
      PositiveRules.mixedValues G (assign η s.binders As) [r] = d.result := by
  obtain ⟨d, T, O, R, hT, hO, hR, eT, eO, eR⟩ :=
    allowed_descriptor C s As ha g hg slot hs
  exact ⟨d, (assigned_value G η s As t T (ht.trans hT) kt).trans eT,
    (assigned_value G η s As o O (ho.trans hO) ko).trans eO,
    (assigned_value G η s As r R (hr.trans hR) kr).trans eR⟩

#print axioms assigned_observation
#print axioms assigned_descriptor

/-- A group's value binders, checked against the graph: the input, the
observation, and the result where the group has one. -/
structure GroupBinders (ι : Type) where
  input : ι
  observation : ι
  result : Option (Nat × ι)

/-- The result binder of a group, where it has a result slot. -/
@[nospecialize] def groupResult (s : SchemeRow ι) (g : ResolutionSlots) :
    Option (Option (Nat × ι)) :=
  match g.result with
  | none => some none
  | some slot => (s.binders[slot]?).map fun r => some (slot, r)

/-- The value binders of a resolution group, checked against the graph. -/
@[nospecialize] def groupBinders [DecidableEq ι] (G : NormalGraph ι)
    (s : SchemeRow ι) (g : ResolutionSlots) : Option (GroupBinders ι) := do
  let t ← s.binders[g.input]?
  let o ← s.binders[g.observation]?
  let r ← groupResult s g
  if G.parameterKinds t == some .value && G.parameterKinds o == some .value &&
      r.all (fun p => G.parameterKinds p.2 == some .value) then some ⟨t, o, r⟩ else none

/-- A source view retains a parameter's JavaScript-valued members. -/
@[nospecialize] def sourceView [DecidableEq ι] (G : NormalGraph ι) (A : List ι) (p : ι) : Bool :=
  A == [p] || match A with
    | [i] => G.meetRow i && PositiveRules.meetParts G i == [p] &&
        PositiveRules.meetClauses G i == [.source]
    | _ => false

/-- Source restriction is the identity on a JavaScript-valued parameter. -/
theorem sourceView_sound [DecidableEq ι] {G : NormalGraph ι} {A : List ι} {p : ι}
    (checked : sourceView G A p = true) (kind : G.parameterKinds p = some .value)
    (η : MixedAssignment ι) (source : FamLe (PositiveRules.mixedValues G η [p]) (PositiveRules.excOf G)) :
    PositiveRules.mixedValues G η A = PositiveRules.mixedValues G η [p] := by
  simp only [sourceView, Bool.or_eq_true, beq_iff_eq] at checked
  rcases checked with rfl | checked
  · rfl
  · match A with
    | [i] =>
      simp only [Bool.and_eq_true, beq_iff_eq] at checked
      obtain ⟨⟨hm, parts⟩, clauses⟩ := checked
      have hp : G.partRow p = true := by simp [NormalGraph.partRow, NormalGraph.params, kind]
      funext n W v
      apply propext
      change (∃ q ∈ [i], _) ↔ (∃ q ∈ [p], _)
      simp only [List.mem_singleton, exists_eq_left]
      rw [PositiveRules.meet_row_iff hm, parts, clauses]
      simp only [List.mem_singleton, forall_eq, exists_eq_left]
      constructor
      · exact fun h => (PositiveRules.part_denote hp).mpr h.1
      · intro h
        refine ⟨(PositiveRules.part_denote hp).mp h, ?_⟩
        exact source n W v ⟨p, List.mem_singleton_self _, h⟩
    | [] => cases checked
    | _ :: _ :: _ => cases checked

#print axioms sourceView_sound

/-- A lexical instance retains the input and observation of one enclosing
group, and its result wherever the target group has one. -/
@[nospecialize] def groupInstance [DecidableEq ι] (G : NormalGraph ι)
    (source : SchemeRow ι) (g : ResolutionSlots) (args : List (List ι))
    (target : ResolutionSlots) : Bool :=
  match groupBinders G source g with
  | none => false
  | some b => (args[target.input]?).any (sourceView G · b.input) &&
      (args[target.observation]?).any (sourceView G · b.observation) &&
      match target.result, b.result with
      | none, _ => true
      | some slot, some (_, r) => (args[slot]?).any (sourceView G · r)
      | some _, none => false

/-- Check a lexical instance against its enclosing scheme. Each target group
must retain one complete source group. Bounds are checked by the instance rule. -/
@[nospecialize] def lexicalAdmission [DecidableEq ι] (G : NormalGraph ι)
    (source target : SchemeRow ι) (args : List (List ι)) : Bool :=
  decide source.binders.Nodup && target.resolutionValid &&
    target.resolution.all fun h => source.resolution.any fun g => groupInstance G source g args h

theorem groupBinders_some [DecidableEq ι] {G : NormalGraph ι}
    {s : SchemeRow ι} {g : ResolutionSlots} {b : GroupBinders ι}
    (h : groupBinders G s g = some b) :
    s.binders[g.input]? = some b.input ∧ s.binders[g.observation]? = some b.observation ∧
    G.parameterKinds b.input = some .value ∧ G.parameterKinds b.observation = some .value ∧
    (∀ slot, g.result = some slot → ∃ r, b.result = some (slot, r) ∧
      s.binders[slot]? = some r ∧ G.parameterKinds r = some .value) ∧
    (g.result = none → b.result = none) := by
  simp only [groupBinders, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, o, ho, r, hr, h⟩ := h
  split at h
  · rename_i hk
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hk
    refine ⟨ht, ho, hk.1.1, hk.1.2, ?_, ?_⟩
    · intro slot hs
      simp only [groupResult, hs, Option.map_eq_some_iff] at hr
      obtain ⟨x, hx, rfl⟩ := hr
      exact ⟨x, rfl, hx, by simpa using hk.2⟩
    · intro hs
      simp only [groupResult, hs, Option.some.injEq] at hr
      exact hr.symm
  · cases h

open Classical in
theorem assignment_position {bs : List ι} {As : List MixedFamily}
    (hn : bs.Nodup) (hl : As.length = bs.length) {p : Nat} {b : ι}
    (hb : bs[p]? = some b) : (bs.zip As).lookup b = As[p]? := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hb
  have hj : p < As.length := by omega
  rw [← he, List.getElem?_eq_getElem hj]
  exact PositiveRules.lookup_zip_getElem hn p hi hj

/-- The checked lexical substitution is admissible at every assignment
permitted by its enclosing scheme. No independent choice of projections is made. -/
theorem lexicalAdmission_sound [DecidableEq ι] (G : NormalGraph ι)
    (source target : SchemeRow ι) (args : List (List ι))
    (checked : lexicalAdmission G source target args = true)
    (η : MixedAssignment ι) (As : List MixedFamily)
    (hl : As.length = source.binders.length)
    (ha : (descriptorDomain C).allowed source As) (hU : FamLe U (PositiveRules.excOf G)) :
    (descriptorDomain C).allowed target
      (args.map fun U => ⟨mixedMeaning G (assign η source.binders As) U,
        mixedMeaning_valid G (assign η source.binders As) U⟩) := by
  simp only [lexicalAdmission, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true] at checked
  refine ⟨PositiveRules.resolutionValid_protected checked.1.2, ?_⟩
  intro h hh
  obtain ⟨g, hg, hm⟩ := checked.2 h hh
  unfold groupInstance at hm
  cases hb : groupBinders G source g with
  | none => simp [hb] at hm
  | some b =>
    rw [hb] at hm
    simp only [Bool.and_eq_true] at hm
    obtain ⟨⟨hmt, hmo⟩, hmr⟩ := hm
    obtain ⟨T, hmt, tv⟩ := (Option.any_eq_true _ _).mp hmt
    obtain ⟨O, hmo, ov⟩ := (Option.any_eq_true _ _).mp hmo
    obtain ⟨ht, ho, kt, ko, hres, _⟩ := groupBinders_some hb
    let F (U : List ι) : MixedFamily :=
      ⟨mixedMeaning G (assign η source.binders As) U,
        mixedMeaning_valid G (assign η source.binders As) U⟩
    have at_ (slot : Nat) (U : List ι) (e : args[slot]? = some U) :
        (args.map F)[slot]? = some (F U) := by
      simp only [List.getElem?_map, e, Option.map_some]
    obtain ⟨d, et, eo⟩ := assigned_observation G η source As ha g hg b.input b.observation
      (assignment_position checked.1.1 hl ht)
      (assignment_position checked.1.1 hl ho) kt ko
    have et' : (F T).value.1 = d.input :=
      (sourceView_sound tv kt _ (by rw [et]; exact fun n W v h => hU n W v ((C.observe_source d.observed).1 n W v h))).trans et
    have eo' : (F O).value.1 = d.observation :=
      (sourceView_sound ov ko _ (by rw [eo]; exact fun n W v h => hU n W v ((C.observe_source d.observed).2 n W v h))).trans eo
    refine ⟨F T, F O, at_ _ _ hmt, at_ _ _ hmo,
      by rw [et', eo']; exact d.observed, ?_⟩
    intro slot hslot
    have hts : h.result = some slot := hslot
    rw [hts] at hmr
    obtain ⟨gs, hgs⟩ : ∃ gs, g.result = some gs := by
      cases hgr : g.result with
      | some gs => exact ⟨gs, rfl⟩
      | none =>
        obtain ⟨_, _, _, _, _, hnone⟩ := groupBinders_some hb
        rw [hnone hgr] at hmr
        simp at hmr
    obtain ⟨r, hbr, hr, kr⟩ := hres gs hgs
    rw [hbr] at hmr
    obtain ⟨R, hmr, rv⟩ := (Option.any_eq_true _ _).mp hmr
    obtain ⟨e, et, eo, er⟩ := assigned_descriptor G η source As ha g hg gs hgs
      b.input b.observation r
      (assignment_position checked.1.1 hl ht)
      (assignment_position checked.1.1 hl ho)
      (assignment_position checked.1.1 hl hr) kt ko kr
    have et' : (F T).value.1 = e.input :=
      (sourceView_sound tv kt _ (by rw [et]; exact fun n W v h => hU n W v ((C.observe_source e.observed).1 n W v h))).trans et
    have eo' : (F O).value.1 = e.observation :=
      (sourceView_sound ov ko _ (by rw [eo]; exact fun n W v h => hU n W v ((C.observe_source e.observed).2 n W v h))).trans eo
    have er' : (F R).value.1 = e.result :=
      (sourceView_sound rv kr _ (by rw [er]; exact fun n W v h => hU n W v ((C.resolve_source e.resolved).2 n W v h))).trans er
    refine ⟨F R, at_ _ _ hmr, ?_, ?_, ?_⟩
    · rw [er']; exact e.stable
    · rw [et', er']; exact e.resolved
    · rw [eo', er']; exact e.forwarded

#print axioms lexicalAdmission_sound

/-- The shared instance checker with admission checked against the enclosing
lexical descriptor. Signature images, kinds and bounds use the ordinary checks. -/
@[nospecialize] def compareLexicalInstance [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (source : SchemeRow ι)
    (compare : List ι → List ι → σ → ComparisonResult α × σ) (empty : α)
    (S : List ι) (L : PositiveRules.Ops ι)
    (M : List (CallEffects.RestArrow (List ι)))
    (c : PositiveCertificates.Instance ι) (state : σ) : ComparisonResult (List α) × σ :=
  PositiveCertificates.compareInstArrsState G images compare empty S L M c state
    (fun target inst => ComparisonResult.fromBool
      (lexicalAdmission G source target inst.instances))

/-- Successful lexical instantiation is sound under the enclosing descriptor,
using the same computational instance rule as unconditional instantiation. -/
theorem compareLexicalInstance_sound [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (source : SchemeRow ι)
    (hd : G.domain = descriptorDomain C)
    {compare : List ι → List ι → σ → ComparisonResult α × σ}
    {empty S L M c state} (η : MixedAssignment ι) (As : List MixedFamily)
    (hl : As.length = source.binders.length) (ha : G.domain.allowed source As)
    (hU : FamLe U (PositiveRules.excOf G))
    (hc : ∀ U V prior, (compare U V prior).1.accepted = true →
      FamLe (mixedMeaning G (assign η source.binders As) U)
        (mixedMeaning G (assign η source.binders As) V))
    (checked : (compareLexicalInstance G images source compare empty S L M c state).1.accepted = true) :
    FamLe (PositiveRules.mixedValues G (assign η source.binders As) S)
      (PositiveRules.mixedSem G (assign η source.binders As) (.arrs L M)) := by
  apply PositiveCertificates.compareInstArrsState_sound_at
    (assign η source.binders As) ?_ hc checked
  intro target inst h
  simp only [ComparisonResult.accepted_fromBool] at h
  rw [hd] at ha ⊢
  exact lexicalAdmission_sound G source target inst.instances h η As hl ha hU

#print axioms compareLexicalInstance_sound

end Verification.QualifiedGraphs
