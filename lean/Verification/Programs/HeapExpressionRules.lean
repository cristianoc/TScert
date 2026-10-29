import Verification.Semantics.Purity
import Verification.Semantics.HeapKnowledge
import Verification.Semantics.LinkClasses

/-! Checked expression rules with primitive state postconditions. Ordinary evidence
retains only immutable-value facts; special rules justify stronger heap facts.
No fact is accepted as an ordinary reference type or captured as a permanent call contract. -/
namespace Verification.HeapExpressionRules
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower
open HeapFacts HeapKnowledge HeapObservations ProgramCertificates
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

/-- Evidence names the particular observation used. The checker binds it to
an actual source sequent, so neither the slot nor the requested result type can
be changed by an untrusted producer. -/
inductive StepEvidence (ι : Type) where
  | ordinary (proof : ProgramCertificates.Evidence ι)
  | pure (proof : ProgramCertificates.Evidence ι)
  /-- Inspections (`Purity.inspectTerm`: reads, tests, arithmetic and
  allocations of evaluated operands): the ordinary derivation, and every
  fact of the heap kept, since an inspection only extends the heap. -/
  | reading (proof : ProgramCertificates.Evidence ι)
  | created (proof : ProgramCertificates.Evidence ι)
  | typedRead (slot : Nat) (proof : ProgramCertificates.Evidence ι)
  | observedRead (slot : Nat) (contents : ValueSets.ValueSet)
  /-- A read of a location whose contents answer `tag` with `answer`: the
  ordinary read at the location's contract (`proof`), whose slice by that
  answer is below the claim (`sub`, or a slice no subtype proof is needed
  for, `Array.isArray`'s). -/
  | slicedRead (tag : Tag) (answer : Bool) (slot : Nat) (proof : ProgramCertificates.Evidence ι) (sub : PositiveCertificates.SubtypeChoices ι)
  | knownValue (slot : Nat) (contents : ValueSets.ValueSet)
  /-- A read of `slot`'s field where a read link says the field holds the
  value of `value` (HOST-FAMILIES.md, "Linked reads"): the read gives that
  value, at its type, below the claim by `sub`. -/
  | linkedRead (slot value : Nat) (sub : PositiveCertificates.SubtypeChoices ι)
  /-- The fields, their slots and their contents are read off the term and the
  state, so this carries only the ordinary derivation it stands beside. -/
  | allocated (proof : ProgramCertificates.Evidence ι)
  | written (receiver value : Nat) (contents : Option ValueSets.ValueSet) (proof : ProgramCertificates.Evidence ι)

/-- An expression-step checker carries the safety theorem required by graph
composition, including its output heap knowledge. -/
structure Checker [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) where
  run : Sequent ι → Knowledge → StepEvidence ι →
    (CodeEntry ι → Bool) → List (ReadSummary ι) → CheckResult ι Knowledge
  /-- Search's choice of a step for a derivation search built itself: `run`,
  or a variant taking that derivation as given. Untrusted: the final check
  runs `run`. -/
  select : Sequent ι → Knowledge → StepEvidence ι →
    (CodeEntry ι → Bool) → List (ReadSummary ι) → CheckResult ι Knowledge := run
  sound : ∀ {j k e out codes sums}, (run j k e codes sums).value = some out →
    CodesSound G codes → SummariesSound G images sums → ∀ {ρ n W h},
    EnvOk G j.context ρ n W → HeapKnowledge.Holds k ρ h →
    WorldAdm W → HeapOk n W h →
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds out (push v ρ) h')
      n W h (instantiate 0 ρ j.term)

/-- Copy an immutable slot into the result while preserving the old slots. -/
def copyFacts (fs : Facts) (i : Nat) : Facts :=
  (fs.filter (fun f => f.slot == i)).map (fun f => {f with slot := 0}) ++ HeapFacts.shift fs

def copySlots (i j : Nat) : List Nat := if j = i then [0,j+1] else [j+1]

def copy (k : Knowledge) (i : Nat) : Knowledge :=
  ⟨copyFacts k.cells i,copyFacts k.values i,
    ⟨0,i+1,true,valueField,false⟩ :: HeapLinks.pull k.links (copySlots i),
    HeapSeparation.copy k.separation i⟩

theorem copy_holds {k i ρ h} (hk : HeapKnowledge.Holds k ρ h) :
    HeapKnowledge.Holds (copy k i) (push (ρ i) ρ) h := by
  have shifted := HeapKnowledge.shift_holds (v := ρ i) hk
  refine ⟨?_,?_,?_,HeapSeparation.copy_holds hk.2.2.2⟩
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      have hg := List.mem_filter.mp hg
      simpa [push,of_decide_eq_true (show decide (g.slot = i) = true from hg.2)] using hk.1 g hg.1
    · exact shifted.1 f hf
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      have hg := List.mem_filter.mp hg
      simpa [push,of_decide_eq_true (show decide (g.slot = i) = true from hg.2)] using hk.2.1 g hg.1
    · exact shifted.2.1 f hf

  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · rfl
    · have hp := HeapLinks.pull_holds (pre := copySlots i) (τ := push (ρ i) ρ) hk.2.2.1 (by
        intro j v hv
        unfold copySlots at hv
        split at hv
        · rename_i hj
          rcases List.mem_cons.mp hv with rfl | hv
          · simp [push,hj]
          · have hv := List.mem_singleton.mp hv; subst v; rfl
        · have hv := List.mem_singleton.mp hv; subst v; rfl)
      exact hp g hg

/-- The strongest supported nullish exclusion implied by a value type. -/
def nullishAtoms (G : NormalGraph ι) (A : Ty ι) : Option (List Atom) :=
  if G.plainTy A then
    let nn := (expand G A).all (fun c => tagClause .isNul c == some false)
    let nu := (expand G A).all (fun c => tagClause .isUndef c == some false)
    if nn && nu then some [.nonNullish]
    else if nu then some [.defined]
    else if nn then some [.nonNull]
    else none
  else none

theorem nullishAtoms_sound {G : NormalGraph ι} {A R n W v}
    (hr : nullishAtoms G A = some R) (hv : meaning G A n W v) :
    ∃ a ∈ R, a.holds v := by
  unfold nullishAtoms at hr
  split at hr
  · rename_i hp
    have hn : (expand G A).all (fun c => tagClause .isNul c == some false) = true → v ≠ .nul := by
      intro h he
      have hq : Answers G A .isNul false := ⟨hp, by simpa only [List.all_eq_true, beq_iff_eq] using h⟩
      have := answers_sound hq hv
      rw [he] at this; simp [tagHolds] at this
    have hu : (expand G A).all (fun c => tagClause .isUndef c == some false) = true → v ≠ .undef := by
      intro h he
      have hq : Answers G A .isUndef false := ⟨hp, by simpa only [List.all_eq_true, beq_iff_eq] using h⟩
      have := answers_sound hq hv
      rw [he] at this; simp [tagHolds] at this
    dsimp only at hr
    split at hr
    · rename_i hb; cases hr
      simp only [Bool.and_eq_true] at hb
      exact ⟨.nonNullish, by simp, (meaning_value hv).1, hn hb.1, hu hb.2⟩
    · split at hr
      · rename_i h; cases hr
        exact ⟨.defined, by simp, (meaning_value hv).1, hu h⟩
      · split at hr
        · rename_i h; cases hr
          exact ⟨.nonNull, by simp, (meaning_value hv).1, hn h⟩
        · cases hr
  · cases hr

/-- Every value is null, undefined, or neither. This observation alone
restricts no read; a guard can refine it through a live read link. -/
theorem nullish_partition {v : Tm} (hv : isVal v = true) :
    ∃ a ∈ [Atom.nul, .undef, .nonNullish], a.holds v := by
  by_cases hn : v = .nul
  · exact ⟨.nul, by simp, hn⟩
  by_cases hu : v = .undef
  · exact ⟨.undef, by simp, hu⟩
  exact ⟨.nonNullish, by simp, hv, hn, hu⟩

/-- The values a slot's type admits, as a value set; a type with no
primitive description still gives its nullish exclusions. -/
def typeValues (G : NormalGraph ι) (Γ : List (Ty ι)) (i : Nat) : Option ValueSets.ValueSet :=
  (Γ[i]?).map fun B => ValueSets.ofAtoms
    (((HeapKnowledge.atoms G B).orElse fun _ => nullishAtoms G B).getD [.nul,.undef,.nonNullish])

theorem typeValues_sound {G : NormalGraph ι} {Γ i R ρ n W}
    (hr : typeValues G Γ i = some R) (he : EnvOk G Γ ρ n W) : R.mem (ρ i) = true := by
  unfold typeValues at hr
  cases hb : Γ[i]? with
  | none => simp [hb] at hr
  | some B =>
    simp only [hb,Option.map_some, Option.some.injEq] at hr
    cases ha : HeapKnowledge.atoms G B with
    | some S =>
      simp only [ha, Option.orElse_some, Option.getD_some] at hr
      subst R
      exact ValueSets.ofAtoms_holds ((atoms_sem ha n W (ρ i)).mp (he.2 i B hb))
    | none =>
      simp only [ha, Option.orElse_none] at hr
      cases hn : nullishAtoms G B with
      | some S =>
        simp only [hn, Option.getD_some] at hr; subst R
        exact ValueSets.ofAtoms_holds (nullishAtoms_sound hn (he.2 i B hb))
      | none =>
        simp only [hn, Option.getD_none] at hr; subst R
        exact ValueSets.ofAtoms_holds (nullish_partition (meaning_value (he.2 i B hb)).1)

/-- What the knowledge states of a slot's value, gathered over its aliases
(`HeapKnowledge.valueBy`), met with what its type admits; the type alone
where the knowledge states nothing. -/
def valuesAt (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (i : Nat) : Option ValueSets.ValueSet :=
  match HeapKnowledge.valueBy k (HeapLinks.aliases k.links) i, typeValues G Γ i with
  | some V, some T => some (V.meet T)
  | some V, none => some V
  | none, T => T

theorem valuesAt_sound {G : NormalGraph ι} {Γ k i R ρ n W h}
    (hr : valuesAt G Γ k i = some R) (he : EnvOk G Γ ρ n W)
    (hk : HeapKnowledge.Holds k ρ h) : R.mem (ρ i) = true := by
  unfold valuesAt at hr
  split at hr
  · rename_i V T hV hT
    cases hr
    rw [ValueSets.ValueSet.mem_meet, HeapKnowledge.valueBy_mem hk (HeapKnowledge.aliases_class hk.2.2.1) hV,
      typeValues_sound hT he]; rfl
  · rename_i V hV _
    cases hr
    exact HeapKnowledge.valueBy_mem hk (HeapKnowledge.aliases_class hk.2.2.1) hV
  · exact typeValues_sound hr he

/-- A primitive type's predicate is a structural view, not semantic search. -/
def includes (G : NormalGraph ι) (A : Ty ι) (R : ValueSets.ValueSet) : Bool :=
  match atoms G A with
  | some S => R.le (ValueSets.ofAtoms S)
  | none => false

theorem includes_sound {G : NormalGraph ι} {A R v} (hc : includes G A R = true)
    (hv : R.mem v = true) (n W) : meaning G A n W v := by
  unfold includes at hc
  split at hc
  · rename_i S hs
    apply (atoms_sem hs n W v).mpr
    exact ValueSets.holds_ofAtoms (HeapKnowledge.atoms_noTag hs) (ValueSets.ValueSet.le_sound hc hv)
  · contradiction

def withResult (k : Knowledge) (R : ValueSets.ValueSet) : Knowledge :=
  ⟨k.cells,⟨0,R,valueField⟩::k.values,k.links,k.separation⟩

theorem result_holds {k R ρ h v} (hk : HeapKnowledge.Holds k (push v ρ) h)
    (hr : R.mem v = true) : HeapKnowledge.Holds (withResult k R) (push v ρ) h := by
  refine ⟨hk.1,?_,hk.2.2⟩
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hr
  · exact hk.2.1 f hf

/-- An ordinary typed read preserves the heap and records which cell its result
came from. This does not claim the cell had any particular contents beforehand. -/
def readFrame (k : Knowledge) (i : Nat) (fld : PropKey) (optional : Bool := false) : Knowledge :=
  let out := HeapKnowledge.shift k
  let fresh := (HeapLinks.aliases k.links i).map fun j => (⟨j+1,0,false,fld,optional⟩ : HeapLinks.Link)
  {out with links := fresh ++ out.links}

/-- Reading uses a current-cell fact; its result is also an immutable value fact.
This latter fact is what permits a subsequent result-contract check to retain
precision even when the producer supplied a wider expression type. The read
link is optional, a read of the field or the `undefined` of an absent one,
unless the receiver's type states the field (`presentRead_sound`). -/
def readOutput (k : Knowledge) (i : Nat) (fld : PropKey) (R : ValueSets.ValueSet) (optional : Bool := true) : Knowledge :=
  withResult (readFrame k i fld optional) R

/-- A cell the knowledge states of a slot and field, gathered over its
aliases, at least as narrow as `R`: the read gives a value in `R`. -/
theorem cellHolds {k : Knowledge} {i : Nat} {fld : PropKey} {R : ValueSets.ValueSet} {ρ h}
    (hk : HeapKnowledge.Holds k ρ h)
    (hc : (HeapKnowledge.cellBy k (HeapLinks.aliases k.links) i fld).any (·.le R) = true) :
    ∃ flds c oid v, ρ i = .objAt flds c oid ∧ ReadGave flds fld h v ∧ R.mem v = true := by
  obtain ⟨C, hC, hle⟩ := HeapKnowledge.any_some hc
  obtain ⟨flds, c, oid, v, he, hr, hm⟩ := HeapKnowledge.cellBy_holds hk (HeapKnowledge.aliases_class hk.2.2.1) hC
  exact ⟨flds, c, oid, v, he, hr, ValueSets.ValueSet.le_sound hle hm⟩

theorem read_sound {G : NormalGraph ι} {Γ k i fld R A ρ n W h}
    (hm : ∃ flds c oid v, ρ i = .objAt flds c oid ∧ ReadGave flds fld h v ∧ R.mem v = true) (hc : includes G A R = true)
    (_he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readOutput k i fld R) (push v ρ) h') n W h
      (.readAt fld (ρ i)) := by
  obtain ⟨flds,c,oid,v,hl,hrd,hav⟩ := hm
  rw [hl]
  apply consequence _ _ (hrd.observed (ValueSets.ValueSet.mem_isVal hav) hw hh)
  · intro j U u hu; subst u; exact includes_sound hc hav j U
  · intro h' u hp
    rw [hp.1]
    have hout := result_holds (HeapKnowledge.shift_holds (v := u) hk) (by simpa [hp.2] using hav)
    refine ⟨hout.1,hout.2.1,?_,hout.2.2.2⟩
    intro link hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
      have he := HeapLinks.aliases_eq hk.2.2.1 hj
      exact ⟨flds,c,oid,he.trans hl,by simpa [push,hp.2] using hrd⟩
    · exact hout.2.2.1 link hm

/-- A clause's first invariant bag operand, independent of callability. -/
def clauseBagOperand : PositiveNormalization.Clause α → Option (List (PropKey × α))
  | .refs B _ _ _ _ _ _ | .callable B _ _ _ _ => some B
  | _ => none

/-- Whether a clause states the field `fld` of a location: in its first
invariant operand, or, for a record, as a readonly view other than `length`
(a view of `length` an array meets too, whose length is no field location). -/
def clauseField (c : PositiveNormalization.Clause α) (fld : PropKey) : Bool :=
  (match clauseBagOperand c with
    | some B => B.any fun p => decide (p.1 = fld)
    | none => false) ||
  (match c with
    | .refs _ _ vs _ _ _ _ => fld != lengthKey && vs.any fun p => decide (p.1 = fld)
    | _ => false)

/-- The keys a clause states as locations: its first invariant operand's,
and, for a record, its readonly views'. -/
def clauseKeys (c : PositiveNormalization.Clause α) : List PropKey :=
  (match clauseBagOperand c with
    | some B => B.map Prod.fst
    | none => []) ++
  (match c with
    | .refs _ _ vs _ _ _ _ => vs.map Prod.fst
    | _ => [])

/-- Whether every alternative is a record stating the field `fld`, an
invariant field or a readonly view, whatever its type in each: a read of it
is then of a location of the object. -/
def fieldOperand (cs : List (PositiveNormalization.Clause α)) (fld : PropKey) : Bool :=
  !cs.isEmpty && cs.all fun c => clauseField c fld

/-- What such a read finds: the object, its location at `fld`, and that
location's stored contract, which admits only members of the field's type. -/
theorem fieldOperand_sound [DecidableEq ι] {G : NormalGraph ι} {Ref fld n W v}
    (hr : fieldOperand (expand G Ref) fld = true) (hv : meaning G Ref n W v) :
    ∃ (El : Ty ι) (flds : List (PropKey × Nat)) (code : CallCode) (oid l : Nat) (c : Ctr n), v = .objAt flds code oid ∧ flds.lookup fld = some l ∧
      lookup W l = some c ∧ ∀ (j : Nat) (hj : j < n) (W' : WorldT j) (u : Val), c j hj W' u → meaning G El j W' u := by
  simp only [fieldOperand, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hr
  have hp : G.plainTy Ref = true := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hr.1
    exact plain_of_mem_expand (c := c) hc
  obtain ⟨c,hm,hc,-⟩ := (expand_sem G Ref hp n W v).mp hv
  have hb := hr.2 c hm
  have ofBag : ∀ {B : List (PropKey × Ty ι)} {El : Ty ι}, (fld, El) ∈ B →
      bagT (ReferenceConjunctions.famsOf (meaning G) B) n W v →
      ∃ (El : Ty ι) (flds : List (PropKey × Nat)) (code : CallCode) (oid l : Nat) (c : Ctr n), v = .objAt flds code oid ∧ flds.lookup fld = some l ∧
        lookup W l = some c ∧ ∀ (j : Nat) (hj : j < n) (W' : WorldT j) (u : Val), c j hj W' u → meaning G El j W' u := by
    intro B El hmem hbag
    obtain ⟨flds,code,oid,hl,_,hrec⟩ := hbag
    obtain ⟨flds',l,c',oid',hproj,hfd,hlookup,hagree⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) hrec
    cases hproj
    exact ⟨El, flds, code, oid, l, c', hl, hfd, hlookup, fun j hj W' u hu => (hagree j hj W' u).mp hu⟩
  cases c with
  | refs a bs vs os ms ks =>
    simp only [clauseField, clauseBagOperand, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      List.any_eq_true, decide_eq_true_eq] at hb
    rcases hb with ⟨⟨g, El⟩, hmem, rfl⟩ | ⟨hlen, ⟨g, El⟩, hmem, rfl⟩
    · exact ofBag hmem (recT_bag hc.1.1)
    · obtain ⟨flds,l,c',oid,hl,hfd,hlookup,himp⟩ :=
        viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) hlen hc.2.1
      exact ⟨El, flds, .absent, oid, l, c', hl, hfd, hlookup, himp⟩
  | callable a bs L S ms =>
    simp only [clauseField, clauseBagOperand, Bool.or_false, List.any_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨g, El⟩, hmem, rfl⟩ := hb
    exact ofBag hmem hc.1.1.1.1
  | _ => simp [clauseField, clauseBagOperand] at hb

/-- A read a cell fact answers, of a field the receiver's type states: the
object has the field's location, so the read link is present, as a typed
read's is. -/
theorem presentRead_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k i fld R Ref A ρ n W h}
    (hm : ∃ flds c oid v, ρ i = .objAt flds c oid ∧ ReadGave flds fld h v ∧ R.mem v = true) (hc : includes G A R = true)
    (hi : Γ[i]? = some Ref) (hr : fieldOperand (expand G Ref) fld = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readOutput k i fld R false) (push v ρ) h') n W h
      (.readAt fld (ρ i)) := by
  cases n with
  | zero => trivial
  | succ n =>
    obtain ⟨_,flds',_,_,l,_,hl',hfd,_,_⟩ := fieldOperand_sound hr (he.2 i Ref hi)
    obtain ⟨flds,c,oid,v,hl,hrd,hav⟩ := hm
    have hflds : flds = flds' := by
      have := hl.symm.trans hl'
      simp only [Tm.objAt.injEq] at this
      exact this.1
    subst hflds
    have hlv : h[l]? = some v := by simpa [ReadGave, hfd] using hrd
    rw [hl]
    apply consequence _ _ (hrd.observed (ValueSets.ValueSet.mem_isVal hav) hw hh)
    · intro j U u hu; subst u; exact includes_sound hc hav j U
    · intro h' u hp
      rw [hp.1]
      have hout := result_holds (HeapKnowledge.shift_holds (v := u) hk) (by simpa [hp.2] using hav)
      refine ⟨hout.1,hout.2.1,?_,hout.2.2.2⟩
      intro link hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
        have he := HeapLinks.aliases_eq hk.2.2.1 hj
        exact ⟨flds,c,oid,l,he.trans hl,hfd,by simpa [push,hp.2] using hlv⟩
      · exact hout.2.2.1 link hm

theorem typedRead_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ k i fld Ref A ρ n W h}
    (ht : HasTyUsing G images Γ (.readAt fld (.var i)) A) (hi : Γ[i]? = some Ref)
    (hr : fieldOperand (expand G Ref) fld = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readFrame k i fld) (push v ρ) h') n W h
      (.readAt fld (ρ i)) := by
  cases n with
  | zero => trivial
  | succ n =>
    obtain ⟨El,flds,code,oidb,l,c,hl,hfd,hlookup,himp⟩ := fieldOperand_sound hr (he.2 i Ref hi)
    obtain ⟨v,hv,hmm⟩ := hh.2 l c hlookup
    have hval := meaning_valOnly G El 0 _ v (himp 0 (by omega) _ v (hmm 0 (by omega)))
    have hs : Safe (excOf G) (meaning G A) (n+1) W h (.readAt fld (ρ i)) := by
      simpa [instantiate] using ht.sound (n+1) W h ρ he hw hh
    rw [hl] at hs ⊢
    apply one_step rfl hval (.readField hfd hv) _ hs
    have hout := HeapKnowledge.shift_holds (v := v) hk
    refine ⟨hout.1,hout.2.1,?_,hout.2.2.2⟩
    intro link hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
      exact ⟨flds,code,oidb,l,(HeapLinks.aliases_eq hk.2.2.1 hj).trans hl,hfd,hv⟩
    · exact hout.2.2.1 link hm

/-- A completed read whose value meets an observation belongs to every type
the observation refines its type to, at every step count. -/
theorem slice_value {G : NormalGraph ι} {C B : Ty ι} {Q : Post} {n W h v o}
    (hs : SafePost (excOf G) (meaning G C) Q n W h v) (hv : isVal v = true)
    (hsub : BranchRefinement.ObservedSub G C B o) (hq : o.holds v) :
    SafePost (excOf G) (meaning G B) Q n W h v := by
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hv',ht,hpost⟩ | hth) | ⟨_,_,_,_,_,step,_,_⟩
    · exact Or.inl (Or.inl ⟨hv',hsub _ _ _ ht hq,hpost⟩)
    · exact absurd hth (val_not_thrown hv)
    · exact False.elim (value_no_step hv step)

/-- A read of a location whose contents answer a tag, typed at its
contract `C` by the ordinary rule: its result is of every type that answer
refines `C` to. The fact is about the location the read finds, so the value
it returns is one the fact describes. -/
theorem slicedRead_sound {G : NormalGraph ι} {k i fld C B ρ n W h tag q} {R : ValueSets.ValueSet} {Q : Post}
    (base : SafePost (excOf G) (meaning G C) Q n W h (.readAt fld (ρ i)))
    (hm : ∃ flds c oid v, ρ i = .objAt flds c oid ∧ ReadGave flds fld h v ∧ R.mem v = true) (hR : R.answers tag q = true)
    (hsub : BranchRefinement.ObservedSub G C B (.tag tag q))
    (hk : HeapKnowledge.Holds k ρ h) :
    SafePost (excOf G) (meaning G B) Q n W h (.readAt fld (ρ i)) := by
  obtain ⟨flds,c,oid,v,hl,hrd,hav⟩ := hm
  have hq := ValueSets.ValueSet.answers_sound hR hav
  have hvv : isVal v = true := ValueSets.ValueSet.mem_isVal hav
  have step : Step h (.readAt fld (ρ i)) h v := by rw [hl]; exact hrd.step
  cases n with
  | zero => trivial
  | succ n =>
    rcases base with (⟨hval,_,_⟩ | hth) | ⟨U,h',t',hx,hu,step',hh',hs'⟩
    · rw [hl] at hval; simp [isVal] at hval
    · exact absurd step hth.no_step
    · obtain ⟨rfl,rfl⟩ := Step_det step' step
      exact Or.inr ⟨U,h',t',hx,hu,step',hh',slice_value hs' hvv hsub hq⟩

/-- Whether a string-keyed index reaches a key. -/
def stringIndex (d : IndexKeys × α) (fld : PropKey) : Bool :=
  d.1 == .strings && match fld with | .str _ => true | .sym _ => false

/-- Whether every alternative is a plain record naming the field `fld`,
required or optional, or a dictionary whose string index reaches it: a read
of it is then of a location of the object, or, where the key is absent,
`undefined`, since such an object has no prototype. -/
def optionalOperand (cs : List (PositiveNormalization.Clause α)) (fld : PropKey) : Bool :=
  !cs.isEmpty && cs.all fun c => match c with
    | .refs a _ vs os _ _ _ => a.any (fun p => decide (p.1 = fld)) ||
      vs.any (fun p => p.1 != lengthKey && decide (p.1 = fld)) || os.any (fun o => decide (o.key = fld))
    | .dict _ _ _ ds _ _ _ cs _ => (ds ++ cs).any (stringIndex · fld)
    | _ => false

/-- What such a read finds: the object, and, where it has the key, a
location whose contract admits only values, or else no prototype. -/
theorem optionalOperand_sound [DecidableEq ι] {G : NormalGraph ι} {Ref fld n W v}
    (hr : optionalOperand (expand G Ref) fld = true) (hv : meaning G Ref (n+1) W v) :
    ∃ flds oid, v = .objAt flds .absent oid ∧
      (∀ l, flds.lookup fld = some l → ∃ c : Ctr (n+1), lookup W l = some c ∧
        ∀ (W' : WorldT 0) (u : Val), c 0 (by omega) W' u → isVal u = true) ∧
      (flds.lookup fld = none → flds.lookup CallArguments.protoField = none) := by
  simp only [optionalOperand, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hr
  have hp : G.plainTy Ref = true := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hr.1
    exact plain_of_mem_expand (c := c) hc
  obtain ⟨c,hm,hc,-⟩ := (expand_sem G Ref hp (n+1) W v).mp hv
  have hb := hr.2 c hm
  cases c with
  | refs a bs vs os ms ks =>
    simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne] at hb
    obtain ⟨⟨flds, oid, hvf, hrec⟩, _⟩ := hc.1
    subst hvf
    refine ⟨flds, oid, rfl, ?_, ?_⟩
    · intro l hl
      rcases hb with (⟨⟨g, El⟩, hmem, rfl⟩ | ⟨⟨g, El⟩, hmem, hne, rfl⟩) | ⟨o, hmem, rfl⟩
      · obtain ⟨l', c', hl', hw, hag⟩ := hrec g (meaning G El)
          (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩)
        rw [hl] at hl'
        cases hl'
        exact ⟨c', hw, fun W' u hu => meaning_valOnly G El 0 W' u ((hag 0 (by omega) W' u).mp hu)⟩
      · obtain ⟨flds', loc, ctr, oid', obj, key, hw, imp⟩ :=
          viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) hne hc.2.1
        cases obj
        rw [hl] at key
        cases key
        exact ⟨ctr, hw, fun W' u hu => meaning_valOnly G El 0 W' u (imp 0 (by omega) W' u hu)⟩
      · obtain ⟨c', hw, hsc⟩ := optT_present (List.mem_map.mpr ⟨o, hmem, rfl⟩) hc.2.2.1 hl
        exact ⟨c', hw, fun W' u hu => meaning_valOnly G o.type 0 W' u ((hsc 0 (by omega) W' u).1 hu)⟩
    · intro hl
      rcases hb with (⟨⟨g, El⟩, hmem, rfl⟩ | ⟨⟨g, El⟩, hmem, hne, rfl⟩) | ⟨o, hmem, rfl⟩
      · obtain ⟨l', c', hl', _⟩ := hrec g (meaning G El)
          (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩)
        rw [hl] at hl'
        cases hl'
      · obtain ⟨flds', loc, ctr, oid', obj, key, _⟩ :=
          viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) hne hc.2.1
        cases obj
        rw [hl] at key
        cases key
      · exact optT_no_proto (List.mem_map.mpr ⟨o, hmem, rfl⟩) hc.2.2.1 hl
  | dict a bs vs ds os ms ks cs =>
    obtain ⟨d, hd, hidx⟩ := List.any_eq_true.mp hb
    simp only [stringIndex, Bool.and_eq_true, beq_iff_eq] at hidx
    obtain ⟨hstr, hkey⟩ := hidx
    have hadm : d.1.Admits fld := by
      rw [hstr]; cases fld with
      | str _ => trivial
      | sym _ => simp at hkey
    obtain ⟨-, -, ⟨hds, hcs⟩, -⟩ := hc
    -- Each index the clause states is a view or a cell over the object:
    -- an object with no prototype whose string keys hold the index's values.
    have hview : dictViewT d.1 (meaning G d.2) (n+1) W v := by
      rcases List.mem_append.mp hd with hd | hd
      · exact hds d hd
      · exact dictCellT_view (hcs d hd)
    obtain ⟨flds, oid, hvf, hproto, hkeys⟩ := hview
    subst hvf
    refine ⟨flds, oid, rfl, fun l hl => ?_, fun _ => hproto.1⟩
    obtain ⟨c', hw, hag⟩ := hkeys fld l hl hadm
    exact ⟨c', hw, fun W' u hu => meaning_valOnly G d.2 0 W' u (hag 0 (by omega) W' u hu)⟩
  | _ => simp at hb

/-- A read of a field that may be optional: it records a read link that also
covers the absent key, where it gave `undefined`. -/
theorem optionalRead_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ k i fld Ref A ρ n W h}
    (ht : HasTyUsing G images Γ (.readAt fld (.var i)) A) (hi : Γ[i]? = some Ref)
    (hr : optionalOperand (expand G Ref) fld = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readFrame k i fld true) (push v ρ) h') n W h
      (.readAt fld (ρ i)) := by
  cases n with
  | zero => trivial
  | succ n =>
    obtain ⟨flds, oid, hl, hpres, habs⟩ := optionalOperand_sound hr (he.2 i Ref hi)
    have hs : Safe (excOf G) (meaning G A) (n+1) W h (.readAt fld (ρ i)) := by
      simpa [instantiate] using ht.sound (n+1) W h ρ he hw hh
    rw [hl] at hs ⊢
    have out : ∀ u, HeapLinks.ReadGave flds fld h u →
        HeapKnowledge.Holds (readFrame k i fld true) (push u ρ) h := by
      intro u hu
      have hout := HeapKnowledge.shift_holds (v := u) hk
      refine ⟨hout.1,hout.2.1,?_,hout.2.2.2⟩
      intro link hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
        simp only [Bool.false_eq_true, ite_false, ite_true]
        exact ⟨flds, .absent, oid, (HeapLinks.aliases_eq hk.2.2.1 hj).trans hl, hu⟩
      · exact hout.2.2.1 link hm
    cases hlk : flds.lookup fld with
    | some l =>
      obtain ⟨c, hc, hvals⟩ := hpres l hlk
      obtain ⟨u,hu,hmm⟩ := hh.2 l c hc
      have hval := hvals _ u (hmm 0 (by omega))
      apply one_step rfl hval (.readField hlk hu) _ hs
      exact out u (by simp [HeapLinks.ReadGave, hlk, hu])
    | none =>
      apply one_step rfl rfl (.readMissing hlk (habs hlk)) _ hs
      exact out .undef (by simp [HeapLinks.ReadGave, hlk, habs hlk])

theorem value_sound {G : NormalGraph ι} {Γ k i R A ρ n W h}
    (hr : valuesAt G Γ k i = some R) (hc : includes G A R = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (withResult (copy k i) R) (push v ρ) h') n W h (ρ i) := by
  have hv := valuesAt_sound hr he hk
  have hval : isVal (ρ i) = true := ValueSets.ValueSet.mem_isVal hv
  exact HeapObservations.value hval (includes_sound hc hv n W)
    (result_holds (copy_holds hk) hv)

/-- A read link from `i`, or a slot an alias link equates with it, through
`fld` to `y`: the link a read records. -/
def linksField (k : Knowledge) (i y : Nat) (fld : PropKey) : Bool :=
  k.links.any fun g => (HeapLinks.aliases k.links i).contains g.cell && g.value == y &&
    !g.alias && g.field == fld

/-- **A linked read.** Where a read link says the object in `i` holds the
value of `y` at its field, the read gives that value, which has `y`'s type. -/
theorem linkedRead_sound {G : NormalGraph ι} {Γ k i y fld B A ρ n W h}
    (hl : linksField k i y fld = true) (hB : Γ[y]? = some B)
    (hsub : FamLe (meaning G B) (meaning G A))
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (copy k y) (push v ρ) h') n W h (.readAt fld (ρ i)) := by
  obtain ⟨g,hg,hm⟩ := List.any_eq_true.mp hl
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.contains_iff_mem] at hm
  obtain ⟨⟨⟨hal,hv⟩,ha⟩,hf⟩ := hm
  have hc : ρ g.cell = ρ i := HeapLinks.aliases_eq hk.2.2.1 hal
  have hgl := hk.2.2.1 g hg
  simp only [ha, Bool.false_eq_true, if_false] at hgl
  have hread : ∃ flds c oid, ρ i = .objAt flds c oid ∧ ReadGave flds fld h (ρ y) := by
    split at hgl
    · obtain ⟨flds,c,oid,ho,hr⟩ := hgl
      exact ⟨flds,c,oid,hc ▸ ho,hf ▸ hv ▸ hr⟩
    · obtain ⟨flds,c,oid,l,ho,hlk,hl⟩ := hgl
      exact ⟨flds,c,oid,hc ▸ ho,ReadGave.present (hf ▸ hlk) (hv ▸ hl)⟩
  obtain ⟨flds,c,oid,ho,hr⟩ := hread
  have hty := he.2 y B hB
  have hval := (meaning_value hty).1
  cases n with
  | zero => trivial
  | succ n =>
    rw [ho]
    exact .inr ⟨trunc n (Nat.le_succ n) W, h, ρ y, WExt_refl _, WorldAdm_trunc _ hw, hr.step,
      HeapOk_trunc n W h hh,
      HeapObservations.value hval (hsub _ _ _ ((meaning_adm G B).down n W _ hty)) (copy_holds hk)⟩

/-- Ordinary calls and arbitrary expressions retain immutable snapshots, but no
heap observation without a specific proved effect rule. -/
def ordinaryOutput (k : Knowledge) : Knowledge :=
  ⟨[],HeapFacts.shift k.values,HeapLinks.stable (HeapKnowledge.shift k).links,HeapSeparation.shift k.separation⟩

theorem ordinary_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {subtyping : BodySubtyping G} {Γ k t A ρ n W h}
    (ht : HasTyUsing G images (subtyping := subtyping) Γ t A) (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (ordinaryOutput k) (push v ρ) h') n W h (instantiate 0 ρ t) := by
  apply of_value_property _ (ht.sound n W h ρ he hw hh)
  intro _ _ heap v _
  exact ⟨holds_nil _ _,(HeapKnowledge.shift_holds (v := v) hk).2.1,
    HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := v) hk).2.2.1,
    (HeapKnowledge.shift_holds (v := v) hk).2.2.2⟩

/-- The named fields, invariant fields and readonly views, of every
record-typed slot: the locations a fresh allocation is known to differ from,
read off the context's contracts. A slot of a union of records has the fields
every one of them names. -/
def contractFields [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) : List (Nat × PropKey) :=
  Γ.zipIdx.flatMap fun (A, s) => match (expand G A).head? with
    | some c => (clauseKeys c).eraseDups.filterMap fun f =>
        if fieldOperand (expand G A) f then some (s, f) else none
    | none => []

theorem contractFields_mem [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {s f}
    (hm : (s, f) ∈ contractFields G Γ) :
    ∃ Ref, Γ[s]? = some Ref ∧ fieldOperand (expand G Ref) f = true := by
  obtain ⟨⟨A,s'⟩,hA,hsel⟩ := List.mem_flatMap.mp hm
  simp only at hsel
  split at hsel
  · obtain ⟨g,_,hg⟩ := List.mem_filterMap.mp hsel
    split at hg
    · rename_i hf
      cases hg
      exact ⟨A, List.mem_zipIdx_iff_getElem?.mp hA, hf⟩
    · cases hg
  · simp at hsel

/-- Allocation retains facts about old cells and records the fresh object: one
assertion per field whose initializer is known to hold a supported primitive
predicate (`Rs`). Its locations are fresh, so every own location of it is
separated from every contract field (`others`) of the context's `n` slots,
whatever it holds: one separation fact (`HeapSeparation.allocate`). -/
def allocOutput (k : Knowledge) (Rs : List (PropKey × ValueSets.ValueSet)) (n : Nat)
    (others : List (Nat × PropKey)) : Knowledge :=
  ⟨(Rs.map fun p => (⟨0,p.2,p.1⟩ : Fact)) ++ HeapFacts.shift k.cells, HeapFacts.shift k.values,
    (HeapKnowledge.shift k).links, HeapSeparation.allocate k.separation n others⟩

theorem slots_snd_ge : ∀ {base : Nat} {ns : List PropKey} {l : Nat},
    l ∈ (slots base ns).map Prod.snd → base ≤ l
  | _, [], _, h => by simp [slots] at h
  | base, f :: fs, l, h => by
    simp only [slots, List.map_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ base) (slots_snd_ge h)

/-- A fresh object's own locations lie past the old heap's end; a contract
field of a slot holds a heap value, so it lies below it. -/
theorem fresh_apart [DecidableEq ι] {G : NormalGraph ι} {Γ ρ n W h} {ns : List PropKey} {code : CallCode} {oid : Nat}
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h) :
    ∀ s g, (s, g) ∈ contractFields G Γ →
      HeapSeparation.Apart (push (.objAt (slots h.length ns) code oid) ρ) 0 none (s + 1) g := by
  intro s g hm l l' hl hl'
  obtain ⟨Ref,hidx,hfo⟩ := contractFields_mem hm
  obtain ⟨_,flds1,code0,oid0,l1,c1,hl0,hfd1,hlookup,_⟩ := fieldOperand_sound hfo (he.2 s Ref hidx)
  obtain ⟨u,hu,_⟩ := hh.2 l1 c1 hlookup
  have hlt : l1 < h.length := List.getElem?_eq_some_iff.mp hu |>.1
  have hge : h.length ≤ l := slots_snd_ge (by simpa [push, HeapSeparation.At] using hl)
  simp only [push, hl0, HeapSeparation.At, List.mem_singleton, exists_eq_left] at hl'
  have : l' = l1 := Option.some.inj (hl'.symm.trans hfd1)
  omega

/-- The slots a fresh allocation's initializers stand in, with the field each
one fills. Nothing else can frame facts: every initializer must already be a
value this state knows about. -/
def allocationParts : List PropKey → List Tm → Option (List (PropKey × Nat))
  | [], [] => some []
  | f :: fs, .var i :: as => (allocationParts fs as).map ((f, i) :: ·)
  | _, _ => none

def allocationSlots : Tm → Option (List (PropKey × Nat))
  | .makeAt _ ns inits => allocationParts ns inits
  | _ => none

/-- What the initializers are known to hold, field by field, where that is a
supported primitive predicate; a field whose initializer is not has no fact. -/
def allocationFacts (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge)
    (slots : List (PropKey × Nat)) : List (PropKey × ValueSets.ValueSet) :=
  slots.filterMap fun p => (valuesAt G Γ k p.2).map (p.1, ·)

theorem allocationParts_eq : ∀ {ns inits parts}, allocationParts ns inits = some parts →
    ns = parts.map Prod.fst ∧ inits = parts.map fun p => Tm.var p.2 := by
  intro ns
  induction ns with
  | nil => intro inits parts h; cases inits <;> simp_all [allocationParts]
  | cons f fs ih =>
    intro inits parts h
    cases inits with
    | nil => simp [allocationParts] at h
    | cons a as =>
      cases a <;> simp only [allocationParts] at h
      all_goals try simp at h
      rename_i i
      cases hr : allocationParts fs as with
      | none => rw [hr] at h; simp at h
      | some rest =>
        rw [hr] at h
        simp only [Option.some.injEq] at h
        obtain ⟨a, ha, rfl⟩ := h
        subst ha
        obtain ⟨h1,h2⟩ := ih hr
        subst h1; subst h2
        simp

theorem allocationSlots_eq {t : Tm} {parts : List (PropKey × Nat)}
    (h : allocationSlots t = some parts) :
    ∃ code, t = .makeAt code (parts.map Prod.fst) (parts.map fun p => .var p.2) := by
  unfold allocationSlots at h
  split at h
  · rename_i code ns inits
    obtain ⟨h1,h2⟩ := allocationParts_eq h
    exact ⟨code, by rw [h1, h2]⟩
  · simp at h

theorem alloc_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k A ρ n W h} {code : CallCode}
    {parts : List (PropKey × Nat)}
    (hnd : (parts.map Prod.fst).Nodup)
    (hin : ∀ p ∈ parts, p.2 < Γ.length)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hh : HeapOk n W h)
    (hs : Safe (excOf G) (meaning G A) n W h
      (.makeAt code (parts.map Prod.fst) (parts.map fun p => ρ p.2))) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds
        (allocOutput k (allocationFacts G Γ k parts) Γ.length (contractFields G Γ))
        (push v ρ) h')
      n W h (.makeAt code (parts.map Prod.fst) (parts.map fun p => ρ p.2)) := by
  have hval : ∀ p ∈ parts, isVal (ρ p.2) = true := fun p hp =>
    (meaning_value (he.2 p.2 _ (List.getElem?_eq_getElem (hin p hp)))).1
  have hvals : ∀ v ∈ parts.map (fun p => ρ p.2), isVal v = true := by
    intro v hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    exact hval p hp
  apply one_step rfl rfl (.makeFields hvals (by simp)) _ hs
  have hshift := HeapKnowledge.shift_holds
    (v := Tm.objAt (slots h.length (parts.map Prod.fst)) code
      (h.length + (parts.map fun p => ρ p.2).length)) hk
  refine ⟨?_, hshift.2.1, ?_⟩
  · intro f hf
    simp only [allocOutput] at hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hf
      obtain ⟨p,hp,hpq⟩ := List.mem_filterMap.mp hq
      obtain ⟨R,hR,rfl⟩ := Option.map_eq_some_iff.mp hpq
      obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
      have hq := valuesAt_sound hR he hk
      refine ⟨slots h.length (parts.map Prod.fst), code, h.length + (parts.map fun p => ρ p.2).length,
        ρ p.2, rfl, ReadGave.present (l := h.length + i) ?_ ?_, hq⟩
      · have hname : (parts.map Prod.fst)[i]'(by simpa using hi) = p.1 := by simp [hpi]
        rw [← hname]
        exact lookup_slots hnd (by simpa using hi)
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left]
        rw [List.getElem?_eq_getElem (by simpa using hi)]
        simp [hpi]
    · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      obtain ⟨flds,c,oid,v,hl,hrd,hv'⟩ := hk.1 g hg
      exact ⟨flds,c,oid,v,hl,(hrd.alloc_frames _).alloc_frames _,hv'⟩
  · simp only [allocOutput]
    exact ⟨HeapLinks.alloc_frames [.nul] (HeapLinks.alloc_frames (parts.map fun p => ρ p.2) hshift.2.2.1),
      HeapSeparation.allocate_holds hk.2.2.2 (fresh_apart he hh)⟩

theorem slots_lookup_ge {base : Nat} {ns : List PropKey} {f : PropKey} {l : Nat}
    (h : (slots base ns).lookup f = some l) : base ≤ l := by
  induction ns generalizing base with
  | nil => simp [slots] at h
  | cons g ns ih =>
    simp only [slots, List.lookup] at h
    split at h
    · cases h; exact Nat.le_refl _
    · have := ih h; omega

/-- An object allocated past the heap's end keeps what was known of the old
heap, and its own locations are separated from every contract field of the
context's record-typed slots. -/
theorem fresh_holds [DecidableEq ι] {G : NormalGraph ι} {Γ k ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hh : HeapOk n W h)
    (ns : List PropKey) (vs : List Val) (code : CallCode) :
    HeapKnowledge.Holds (allocOutput k [] Γ.length (contractFields G Γ))
      (push (.objAt (slots h.length ns) code oid) ρ) (h ++ vs ++ [.nul]) := by
  have hshift := HeapKnowledge.shift_holds (v := Tm.objAt (slots h.length ns) code oid) hk
  refine ⟨?_, hshift.2.1, HeapLinks.alloc_frames [.nul] (HeapLinks.alloc_frames vs hshift.2.2.1),
    HeapSeparation.allocate_holds hk.2.2.2 (fresh_apart he hh)⟩
  intro f hf
  simp only [allocOutput, List.map_nil, List.nil_append] at hf
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  obtain ⟨flds,c,oid,v,hl,hrd,hv'⟩ := hk.1 g hg
  exact ⟨flds,c,oid,v,hl,(hrd.alloc_frames _).alloc_frames _,hv'⟩

/-- A merge of two values reads the heap and allocates a fresh object: what
was known of the heap stays known, and the new object's fields are distinct
from the context's contract fields, as a literal's are (`alloc_sound`). -/
theorem merge_alloc_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k A ρ n W h}
    {d : List PropKey} {a b : Tm}
    (hva : isVal a = true) (hvb : isVal b = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hh : HeapOk n W h)
    (hs : Safe (excOf G) (meaning G A) n W h (.merge d a b)) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (allocOutput k [] Γ.length (contractFields G Γ)) (push v ρ) h')
      n W h (.merge d a b) := by
  cases n with
  | zero => trivial
  | succ p =>
    rcases hs with (⟨hval,_⟩ | hr) | ⟨U,h1,t1,hx,hu,step,hh1,hs1⟩
    · simp [isVal] at hval
    · obtain ⟨v, hr, _⟩ := hr
      cases hr with
      | mergeC1 hr => rw [raises_not_val hr] at hva; contradiction
      | mergeC2 _ hr => rw [raises_not_val hr] at hvb; contradiction
    · cases step with
      | mergeC1 s => exact absurd s (value_no_step hva)
      | mergeC2 _ s => exact absurd s (value_no_step hvb)
      | mergeV _ _ hparts =>
        refine Or.inr ⟨U, h, _, hx, hu, .mergeV hva hvb hparts, hh1, ?_⟩
        refine one_step rfl rfl (.makeFields ?vals (by simp)) (fresh_holds he hk hh _ _ _) hs1
        case vals =>
          intro v hv
          obtain ⟨e, hm, rfl⟩ := List.mem_map.mp hv
          rcases mergeParts_vals hparts e hm with h1 | ⟨-, h2⟩ | ⟨u, h3⟩
          · rw [h1]; rfl
          · exact h2
          · rw [h3]; rfl

/-- An allocation at a computed key, of two values, allocates a fresh
object: what was known of the heap stays known, and the new object's field is
distinct from the context's contract fields, as a literal's are. -/
theorem makeKey_alloc_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k A ρ n W h}
    {a b : Tm}
    (hva : isVal a = true) (hvb : isVal b = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hh : HeapOk n W h)
    (hs : Safe (excOf G) (meaning G A) n W h (.makeKey a b)) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (allocOutput k [] Γ.length (contractFields G Γ)) (push v ρ) h')
      n W h (.makeKey a b) := by
  cases n with
  | zero => trivial
  | succ p =>
    rcases hs with (⟨hval,_⟩ | hr) | ⟨U,h1,t1,hx,hu,step,hh1,hs1⟩
    · simp [isVal] at hval
    · obtain ⟨v, hr, _⟩ := hr
      cases hr with
      | makeKeyC1 hr => rw [raises_not_val hr] at hva; contradiction
      | makeKeyC2 _ hr => rw [raises_not_val hr] at hvb; contradiction
    · cases step with
      | makeKeyC1 s => exact absurd s (value_no_step hva)
      | makeKeyC2 _ s => exact absurd s (value_no_step hvb)
      | makeKeyV _ hf =>
        refine Or.inr ⟨U, h, _, hx, hu, .makeKeyV hvb hf, hh1, ?_⟩
        exact one_step rfl rfl (.makeFields (by simpa using hvb) (by simp))
          (fresh_holds he hk hh _ _ _) hs1

/-- A write forgets old cell observations, except those about locations known
to be distinct from the written one, establishes its new contents where the
written value is a known primitive (`R`), and retains immutable values
already read into slots. -/
def writeOutput (k : Knowledge) (i : Nat) (fld : PropKey) (R : Option ValueSets.ValueSet) : Knowledge :=
  ⟨(R.map fun R => (HeapLinks.aliases k.links i).map (fun j => (⟨j+1,R,fld⟩ : Fact))).getD [] ++
      (k.cells.filter fun f => HeapSeparation.apartBy (Partitions.cls (LinkClasses.closure k.links)) k.separation i fld f.slot f.field).map
        (fun f => {f with slot := f.slot + 1}),
    ⟨0,{ nul := true },valueField⟩ :: HeapFacts.shift k.values,
    HeapLinks.stable (HeapKnowledge.shift k).links, HeapSeparation.shift k.separation⟩

theorem write_inv {f h a b h' t} (ha : isVal a = true) (hb : isVal b = true)
    (hs : Step h (.writeAt f a b) h' t) :
    ∃ flds c oid l, a = .objAt flds c oid ∧ flds.lookup f = some l ∧ l < h.length ∧
      h' = h.set l b ∧ t = .nul := by
  cases hs with
  | writeC1 hs => exact False.elim (value_no_step ha hs)
  | writeC2 _ hs => exact False.elim (value_no_step hb hs)
  | writeField _ hf hl => exact ⟨_,_,_,_,rfl,hf,hl,rfl,rfl⟩

/-- The ordinary typing proof guarantees a writable location. An old observation
is unnecessary: the postcondition depends only on the value being written. -/
theorem write_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ k i j fld R A ρ n W h}
    (ht : HasTyUsing G images Γ (.writeAt fld (.var i) (.var j)) A) (hi : i < Γ.length) (hj : j < Γ.length)
    (hr : valuesAt G Γ k j = R)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (writeOutput k i fld R) (push v ρ) h')
      n W h (.writeAt fld (ρ i) (ρ j)) := by
  have hvv : isVal (ρ j) = true :=
    (meaning_value (he.2 j Γ[j] (List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩))).1
  have hiv := (meaning_value (he.2 i Γ[i] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))).1
  have hs : Safe (excOf G) (meaning G A) n W h (.writeAt fld (ρ i) (ρ j)) := by
    simpa [instantiate] using ht.sound n W h ρ he hw hh
  cases n with
  | zero => trivial
  | succ n =>
    have step := hs
    rcases step with (⟨hbad,_⟩ | ⟨_,hr,_⟩) | ⟨U,h',t',_,_,step,_,_⟩
    · contradiction
    · cases hr with
      | writeC1 hr => rw [raises_not_val hr] at hiv; contradiction
      | writeC2 _ hr => rw [raises_not_val hr] at hvv; contradiction
    · obtain ⟨flds,c,oid,l,hl,hfd,hlt,_,_⟩ := write_inv hiv hvv step
      rw [hl] at hs ⊢
      apply one_step rfl rfl (.writeField hvv hfd hlt) _ hs
      refine ⟨?_,?_,HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := .nul) hk).2.2.1,
        (HeapKnowledge.shift_holds (v := .nul) hk).2.2.2⟩
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · cases hR : R with
          | none => simp [hR] at hf
          | some R' =>
            rw [hR] at hf
            have hv := valuesAt_sound (hR ▸ hr) he hk
            obtain ⟨slot,hs,rfl⟩ := List.mem_map.mp (by simpa using hf)
            have heq := HeapLinks.aliases_eq hk.2.2.1 hs
            exact ⟨flds,c,oid,ρ j,heq.trans hl,ReadGave.present hfd (write_new hlt),hv⟩
        · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
          have hg := List.mem_filter.mp hg
          obtain ⟨flds0,c0,oid0,u,hs0,hrd,hb'⟩ := hk.1 g hg.1
          refine ⟨flds0,c0,oid0,u,?_,?_,hb'⟩
          · simpa [push] using hs0
          · unfold ReadGave at hrd ⊢
            cases hfd0 : flds0.lookup g.field with
            | none => rw [hfd0] at hrd; exact hrd
            | some l0 =>
              rw [hfd0] at hrd
              have hne : l ≠ l0 := HeapSeparation.apartBy_sound (fun _ _ hy => (LinkClasses.gen_sound hk.2.2.1 (LinkClasses.mem_cls_closure.mp hy)).symm) hg.2 hk.2.2.2 hl hfd hs0 hfd0
              simpa only [List.getElem?_set_ne hne] using hrd
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · rfl
        · exact (HeapKnowledge.shift_holds (v := .nul) hk).2.1 f hf

export Purity (pureTerm pure_step)

theorem pure_instantiate {G : NormalGraph ι} {Γ t ρ n W} {d : Nat}
    (hp : pureTerm t = true) (hc : checkScope (Γ.length + d) t = true)
    (he : EnvOk G Γ ρ n W) : pureTerm (instantiate d ρ t) = true := by
  induction t using Tm.induct generalizing d <;>
    simp_all [pureTerm,isVal,instantiate,checkScope,Nat.add_assoc]
  case var i =>
    split
    · rfl
    · have hi : i - d < Γ.length := by omega
      have hv := (meaning_value (he.2 (i-d) Γ[i-d] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))).1
      cases h : ρ (i-d) <;> simp_all [pureTerm,isVal]

/-- Any heap predicate that survives heap extension can be framed across a
checked pure computation. -/
theorem pure_frame {T Q} : ∀ {n W h t}, Safe Ξ T n W h t → pureTerm t = true →
    (∀ h', h.IsPrefix h' → ∀ v, Q h' v) → SafePost Ξ T Q n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs hp hq
    rcases hs with (⟨hv,ht⟩ | hr) | ⟨U,h',t',hx,hu,step,hh,hs⟩
    · exact Or.inl (Or.inl ⟨hv,ht,hq h (List.prefix_refl h) t⟩)
    · exact Or.inl (Or.inr hr)
    · obtain ⟨hpre,hp'⟩ := pure_step step hp
      exact Or.inr ⟨U,_,t',hx,hu,step,hh,ih hs hp' fun h'' hh'' v => hq h'' (hpre.trans hh'') v⟩

/-- A variable copy records the observation justified by its current facts
or its value type, retaining the copy's equality and read links. -/
def copyValue (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (i : Nat) : Knowledge :=
  match valuesAt G Γ k i with
  | some R => withResult (copy k i) R
  | none => copy k i

theorem copyValue_holds {G : NormalGraph ι} {Γ k i ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) :
    HeapKnowledge.Holds (copyValue G Γ k i) (push (ρ i) ρ) h := by
  unfold copyValue
  split
  · rename_i R hr
    exact result_holds (copy_holds hk) (valuesAt_sound hr he hk)
  · exact copy_holds hk

def pureOutput (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Tm → Knowledge
  | .var i => copyValue G Γ k i
  | .nul => withResult (HeapKnowledge.shift k) { nul := true }
  | .undef => withResult (HeapKnowledge.shift k) { undef := true }
  | .tru => withResult (HeapKnowledge.shift k) { tru := true }
  | .fls => withResult (HeapKnowledge.shift k) { fls := true }
  | _ => HeapKnowledge.shift k

theorem pure_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ k t A ρ n W h}
    (ht : HasTyUsing G images Γ t A) (hp : pureTerm t = true)
    (hc : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (pureOutput G Γ k t) (push v ρ) h')
      n W h (instantiate 0 ρ t) := by
  have hs := ht.sound n W h ρ he hw hh
  have hpClosed := pure_instantiate (d := 0) hp hc he
  cases t <;> simp only [pureTerm,isVal] at hp
  case var i =>
    have hi : i < Γ.length := by simpa [checkScope] using hc
    have hv := meaning_value (he.2 i Γ[i] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))
    simpa [instantiate,pureOutput] using
      refine_value hv.1 (copyValue_holds he hk) (show Safe (excOf G) (meaning G A) n W h (ρ i) by simpa [instantiate] using hs)
  all_goals first
    | exact pure_frame hs hpClosed (fun _ hpre _ => by
        obtain ⟨vs, rfl⟩ := hpre
        exact HeapKnowledge.shift_holds (HeapKnowledge.alloc_frames vs hk))
    | exact refine_value rfl (result_holds (HeapKnowledge.shift_holds hk) rfl) hs
    | exact refine_value rfl (HeapKnowledge.shift_holds hk) hs

export Purity (readTerm read_step read_value)

/-- A heap that meets an admissible world, above level zero, holds values:
every location has a contract, and a contract admits only values. -/
theorem heap_values {n W h} (hw : WorldAdm W) (hh : HeapOk (n+1) W h) :
    ∀ (l : Nat) (v : Tm), h[l]? = some v → isVal v = true := by
  intro l v hl
  have hlt : l < (toList W).length := by
    have := (List.getElem?_eq_some_iff.mp hl).1; rw [← hh.1]; exact this
  obtain ⟨c, hc⟩ : ∃ c, lookup W l = some c :=
    ⟨_, by simp only [lookup]; exact List.getElem?_eq_getElem hlt⟩
  obtain ⟨u, hu, hmem⟩ := hh.2 l c hc
  rw [hl] at hu; cases hu
  exact (hw l c hc).2 0 (by omega) _ v (hmem 0 (by omega))

theorem read_instantiate {G : NormalGraph ι} {Γ t ρ n W} {d : Nat}
    (hp : readTerm t = true) (hc : checkScope (Γ.length + d) t = true)
    (he : EnvOk G Γ ρ n W) : readTerm (instantiate d ρ t) = true := by
  induction t using Tm.induct generalizing d <;>
    simp_all [readTerm,isVal,instantiate,checkScope]
  case var i =>
    split
    · rfl
    · have hi : i - d < Γ.length := by omega
      have hv := (meaning_value (he.2 (i-d) Γ[i-d] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))).1
      exact read_value hv

theorem operand_instantiate {G : NormalGraph ι} {Γ t ρ n W} {d : Nat}
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

theorem init_instantiate {G : NormalGraph ι} {Γ t ρ n W} {d : Nat}
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

/-- **Inspections keep the heap.** A read changes no location and an
allocation appends fresh ones, so the heap an inspection ends with extends the
one it starts from, and a predicate of every extension holds where it ends. -/
theorem inspect_frame {T Q} : ∀ {n W h t}, Safe Ξ T n W h t → Purity.inspectTerm t = true →
    WorldAdm W → HeapOk n W h → (∀ h' v, h.IsPrefix h' → Q h' v) → SafePost Ξ T Q n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs hp hw hh hq
    rcases hs with (⟨hv,ht⟩ | hr) | ⟨U,h',t',hx,hu,step,hh',hs⟩
    · exact Or.inl (Or.inl ⟨hv,ht,hq h t (List.prefix_refl h)⟩)
    · exact Or.inl (Or.inr hr)
    · obtain ⟨hpre, hp'⟩ := Purity.inspect_step step hp (heap_values hw hh)
      exact Or.inr ⟨U,h',t',hx,hu,step,hh',ih hs hp' hu hh' (fun h'' v he => hq h'' v (hpre.trans he))⟩

/-- Every heap fact survives an extension of the heap. -/
theorem knowledge_extend {k : Knowledge} {ρ h h'} (hk : HeapKnowledge.Holds k ρ h)
    (hpre : h.IsPrefix h') : HeapKnowledge.Holds k ρ h' := by
  obtain ⟨vs, rfl⟩ := hpre
  exact HeapKnowledge.alloc_frames vs hk

theorem reading_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ k t A ρ n W h}
    (ht : HasTyUsing G images Γ t A) (hp : Purity.inspectTerm t = true)
    (hc : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (HeapKnowledge.shift k) (push v ρ) h')
      n W h (instantiate 0 ρ t) :=
  inspect_frame (ht.sound n W h ρ he hw hh) (inspect_instantiate (d := 0) hp (by simpa using hc) he) hw hh
    (fun _ _ hpre => knowledge_extend (HeapKnowledge.shift_holds hk) hpre)

/-- Creating graph code allocates a fresh bag without running its code or
invalidating knowledge about existing cells: its captures are slots, already
values. -/
theorem graphCreation_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {Γ k arity E K start caps kind rest A ρ n W h}
    (ht : HasTyUsing G images Γ (.makeFn (.graph arity E K start caps kind rest) .nul) A) (he : EnvOk G Γ ρ n W)
    (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (HeapKnowledge.shift k) (push v ρ) h')
      n W h (instantiate 0 ρ (.makeFn (.graph arity E K start caps kind rest) .nul)) := by
  have hs := ht.sound n W h ρ he hw hh
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hv, _⟩ | ⟨_,hr,_⟩) | ⟨U,h',t',hx,hu,step,hh',hs'⟩
    · simp [instantiate,isVal] at hv
    · simp only [instantiate, instantiateArgs_eq_map, List.map] at hr
      cases hr with | makeArg hg _ hr => obtain ⟨rfl, rfl⟩ := singleton_get hg; cases hr
    · simp only [instantiate, instantiateArgs_eq_map, List.map] at step hs' ⊢
      obtain ⟨rfl,rfl⟩ := makeFn_step_inv rfl step
      exact Or.inr ⟨U,_,_,hx,hu,step,hh',
        refine_value rfl (HeapKnowledge.shift_holds (HeapKnowledge.alloc_frame (HeapKnowledge.alloc_frame hk))) hs'⟩

/-- The field an operation names, read off the term rather than supplied by the
producer, so evidence cannot claim a fact about a field the program never
touched. -/
def readSlot : Tm → Option (PropKey × Nat)
  | .readAt f (.var i) => some (f, i)
  | _ => none

def writeSlots : Tm → Option (PropKey × Nat × Nat)
  | .writeAt f (.var i) (.var v) => some (f, i, v)
  | _ => none

theorem readSlot_eq {t f i} (h : readSlot t = some (f, i)) : t = .readAt f (.var i) := by
  unfold readSlot at h
  split at h <;> simp_all

/-- A merge of two slots, which allocates the object it copies into, or an
allocation at one slot's key holding the other's value. -/
def mergeSlots : Tm → Option (List PropKey × Nat × Nat)
  | .merge d (.var a) (.var b) => some (d, a, b)
  | .makeKey (.var a) (.var b) => some ([], a, b)
  | _ => none

theorem mergeSlots_eq {t d a b} (h : mergeSlots t = some (d, a, b)) :
    t = .merge d (.var a) (.var b) ∨ t = .makeKey (.var a) (.var b) := by
  unfold mergeSlots at h
  split at h <;> simp_all

/-- A store allocated from value slots: its elements' fresh locations lie past
the heap's end, so what was known of the heap stays known. -/
def storeSlots : Tm → Option (List Nat)
  | .arrLit inits => ProgramCertificates.varSlots inits
  | _ => none

theorem storeSlots_eq {t slots} (h : storeSlots t = some slots) :
    t = .arrLit (slots.map .var) := by
  unfold storeSlots at h
  split at h
  · rw [ProgramCertificates.varSlots_eq h]
  · simp at h

/-- A store of values takes one fresh location per element, past the heap's
end: every fact about the old heap, and every link, still holds. -/
theorem store_alloc_sound [DecidableEq ι] {G : NormalGraph ι} {k A ρ n W h}
    {vs : List Tm} (hvals : ∀ v ∈ vs, isVal v = true)
    (hk : HeapKnowledge.Holds k ρ h)
    (hs : Safe (excOf G) (meaning G A) n W h (.arrLit vs)) :
    SafePost (excOf G) (meaning G A)
      (fun h' v => HeapKnowledge.Holds (HeapKnowledge.shift k) (push v ρ) h')
      n W h (.arrLit vs) :=
  one_step rfl rfl (.arrAlloc hvals)
    (HeapKnowledge.shift_holds (HeapKnowledge.alloc_frames vs hk)) hs

theorem writeSlots_eq {t f i v} (h : writeSlots t = some (f, i, v)) :
    t = .writeAt f (.var i) (.var v) := by
  unfold writeSlots at h
  split at h <;> simp_all

/-- An expression's derivation checked, or, where `tree` is false, taken as
given: search selects a step for a derivation it built itself, which the
final check validates. -/
@[nospecialize] def treeChecked [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (e : ProgramCertificates.Evidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) (tree : Bool) :
    ProgramCertificates.CheckResult ι Unit :=
  if tree then checkTreeResult G images e codes sums else pure ()

@[simp] theorem treeChecked_true [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (e : ProgramCertificates.Evidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    treeChecked G images e codes sums true = checkTreeResult G images e codes sums := rfl

/-- A typed expression establishes an output only when its metadata checks pass. -/
@[nospecialize] def checkedOutput [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (e : ProgramCertificates.Evidence ι) (metadata : Bool) (out : Knowledge)
    (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) (tree : Bool := true) :
    ProgramCertificates.CheckResult ι Knowledge :=
  (CheckResult.ofBool metadata).bind fun _ => (treeChecked G images e codes sums tree).map fun _ => out

theorem checkedOutput_value [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (e : ProgramCertificates.Evidence ι) (metadata : Bool) (out : Knowledge) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) :
    (checkedOutput G images e metadata out codes sums).value =
      if metadata && checkTreeUsing G images e codes sums then some out else none := by
  rw [checkedOutput, treeChecked_true, CheckResult.value_bind_const, CheckResult.accepted_ofBool,
    CheckResult.value_map_const]
  cases metadata <;> simp [checkTreeUsing]

/-- The successful result is the guaranteed postcondition in the result-pushed
frame. Subtype comparisons retain unfinished work through the step validation. -/
@[nospecialize] def checkStepResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (k : Knowledge) (step : StepEvidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) (tree : Bool := true) :
    ProgramCertificates.CheckResult ι Knowledge :=
  match step with
  | .ordinary e =>
    checkedOutput G images e (decide (claim e = j ∧ checkScope j.context.length j.term = true))
      (ordinaryOutput k) codes sums tree
  | .pure e =>
    checkedOutput G images e (decide (claim e = j ∧ checkScope j.context.length j.term = true ∧
      pureTerm j.term = true)) (pureOutput G j.context k j.term) codes sums tree
  | .reading e =>
    checkedOutput G images e (decide (claim e = j ∧ checkScope j.context.length j.term = true ∧
      Purity.inspectTerm j.term = true)) (HeapKnowledge.shift k) codes sums tree
  | .created e =>
    (CheckResult.ofBool (decide (claim e = j ∧ checkScope j.context.length j.term = true))).bind fun _ =>
    (treeChecked G images e codes sums tree).bind fun _ =>
      CheckResult.fromOption (match j.term with
        | .makeFn (.graph _ _ _ _ _ _ _) .nul => some (HeapKnowledge.shift k)
        | _ => none)
  | .typedRead i e =>
    match readSlot j.term with
    | some (fld, i') =>
      (checkedOutput G images e (decide (claim e = j ∧ i' = i ∧
        (j.context[i]?).any (fun Ref => fieldOperand (expand G Ref) fld))) (readFrame k i fld) codes sums tree).orElse fun _ =>
        checkedOutput G images e (decide (claim e = j ∧ i' = i ∧
          (j.context[i]?).any (fun Ref => optionalOperand (expand G Ref) fld))) (readFrame k i fld true) (fun _ => false) sums tree
    | none => failure
  | .observedRead i R =>
    CheckResult.fromOption (match readSlot j.term with
      | some (fld, i') =>
        if i' = i ∧ i < j.context.length ∧
          (HeapKnowledge.cellBy k (HeapLinks.aliases k.links) i fld).any (·.le R) ∧ includes G j.type R = true
        then some (readOutput k i fld R (!(j.context[i]?).any (fun Ref => fieldOperand (expand G Ref) fld))) else none
      | none => none)
  | .slicedRead tag q i e p =>
    match readSlot j.term with
    | some (fld, i') =>
      (CheckResult.ofBool (decide ((claim e).context = j.context ∧ (claim e).term = j.term ∧ i' = i ∧
        (j.context[i]?).any (fun Ref => fieldOperand (expand G Ref) fld || optionalOperand (expand G Ref) fld) ∧
        (HeapKnowledge.cellBy k (HeapLinks.aliases k.links) i fld).any (·.answers tag q)))).bind fun _ =>
      (treeChecked G images e codes sums tree).bind fun _ =>
      (BranchRefinement.checkObservedSubResult G images (claim e).type j.type (.tag tag q) p).map
        fun _ => readFrame k i fld (!(j.context[i]?).any (fun Ref => fieldOperand (expand G Ref) fld))
    | none => failure
  | .knownValue i R =>
    CheckResult.fromOption (if j.term = .var i ∧ i < j.context.length ∧
      valuesAt G j.context k i = some R ∧ includes G j.type R = true
      then some (withResult (copy k i) R) else none)
  | .linkedRead i y p =>
    match readSlot j.term, j.context[y]? with
    | some (fld, i'), some B =>
      (CheckResult.ofBool (decide (i' = i ∧ linksField k i y fld = true))).bind fun _ =>
        (ProgramCertificates.checkSubtypeUsing G images B j.type p).map fun _ => copy k y
    | _, _ => failure
  | .allocated e =>
    match allocationSlots j.term with
    | some slots =>
      checkedOutput G images e (decide (claim e = j ∧ checkScope j.context.length j.term = true ∧
        (slots.map Prod.fst).Nodup ∧ ∀ p ∈ slots, p.2 < j.context.length))
        (allocOutput k (allocationFacts G j.context k slots) j.context.length (contractFields G j.context)) codes sums tree
    | none =>
      match mergeSlots j.term with
      | some (_, a, b) =>
        checkedOutput G images e (decide (claim e = j ∧ a < j.context.length ∧ b < j.context.length))
          (allocOutput k [] j.context.length (contractFields G j.context)) codes sums tree
      | none =>
        match storeSlots j.term with
        | some slots =>
          checkedOutput G images e (decide (claim e = j ∧ ∀ i ∈ slots, i < j.context.length))
            (HeapKnowledge.shift k) codes sums tree
        | none => failure
  | .written i v R e =>
    match writeSlots j.term with
    | some (fld, i', v') =>
      checkedOutput G images e (decide (claim e = j ∧ i' = i ∧ v' = v ∧ i < j.context.length ∧
        v < j.context.length ∧ valuesAt G j.context k v = R)) (writeOutput k i fld R) codes sums tree
    | none => failure

@[nospecialize] def checkStepUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (k : Knowledge) (step : StepEvidence ι) (codes : CodeEntry ι → Bool := fun _ => false)
    (sums : List (ReadSummary ι) := []) : Option Knowledge :=
  (checkStepResult G images j k step codes sums).value

private theorem guard_conjunction (p q : Prop) [Decidable p] [Decidable q] (r : Option α) :
    (if p then if q then r else none else none) = if p ∧ q then r else none := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

private theorem option_choice (p : Prop) [Decidable p] (a : α) (b : Unit → Option α) :
    (if p then some a else none).orElse b = if p then some a else b () := by
  by_cases hp : p <;> simp [hp, Option.orElse]

/-- The postcondition projection has exactly the existing step premises. -/
theorem checkStepUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (k : Knowledge) (step : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    checkStepUsing G images j k step codes sums =
  match step with
  | .ordinary e =>
    if claim e = j ∧ checkScope j.context.length j.term = true ∧ checkTreeUsing G images e codes sums = true
    then some (ordinaryOutput k) else none
  | .pure e =>
    if claim e = j ∧ checkScope j.context.length j.term = true ∧
        checkTreeUsing G images e codes sums = true ∧ pureTerm j.term = true
    then some (pureOutput G j.context k j.term) else none
  | .reading e =>
    if claim e = j ∧ checkScope j.context.length j.term = true ∧
        checkTreeUsing G images e codes sums = true ∧ Purity.inspectTerm j.term = true
    then some (HeapKnowledge.shift k) else none
  | .created e =>
    if claim e = j ∧ checkScope j.context.length j.term = true ∧ checkTreeUsing G images e codes sums = true then
      match j.term with
      | .makeFn (.graph _ _ _ _ _ _ _) .nul => some (HeapKnowledge.shift k)
      | _ => none
    else none
  | .typedRead i e =>
    match readSlot j.term with
    | some (fld, i') =>
      if claim e = j ∧ checkTreeUsing G images e codes sums = true ∧ i' = i ∧
          (j.context[i]?).any (fun Ref => fieldOperand (expand G Ref) fld)
      then some (readFrame k i fld)
      else if claim e = j ∧ checkTreeUsing G images e (sums := sums) = true ∧ i' = i ∧
          (j.context[i]?).any (fun Ref => optionalOperand (expand G Ref) fld)
      then some (readFrame k i fld true) else none
    | none => none
  | .observedRead i R =>
    match readSlot j.term with
    | some (fld, i') =>
      if i' = i ∧ i < j.context.length ∧
          (HeapKnowledge.cellBy k (HeapLinks.aliases k.links) i fld).any (·.le R) ∧ includes G j.type R = true
      then some (readOutput k i fld R (!(j.context[i]?).any (fun Ref => fieldOperand (expand G Ref) fld))) else none
    | none => none
  | .slicedRead tag q i e p =>
    match readSlot j.term with
    | some (fld, i') =>
      if (claim e).context = j.context ∧ (claim e).term = j.term ∧ checkTreeUsing G images e codes sums = true ∧ i' = i ∧
          (j.context[i]?).any (fun Ref => fieldOperand (expand G Ref) fld || optionalOperand (expand G Ref) fld) ∧
          (HeapKnowledge.cellBy k (HeapLinks.aliases k.links) i fld).any (·.answers tag q) ∧
          BranchRefinement.checkObservedSubUsing G images (claim e).type j.type (.tag tag q) p = true
      then some (readFrame k i fld (!(j.context[i]?).any (fun Ref => fieldOperand (expand G Ref) fld))) else none
    | none => none
  | .knownValue i R =>
    if j.term = .var i ∧ i < j.context.length ∧
        valuesAt G j.context k i = some R ∧ includes G j.type R = true
    then some (withResult (copy k i) R) else none
  | .linkedRead i y p =>
    match readSlot j.term, j.context[y]? with
    | some (fld, i'), some B =>
      if i' = i ∧ linksField k i y fld = true ∧ PositiveCertificates.checkUsing G images B j.type p = true
      then some (copy k y) else none
    | _, _ => none
  | .allocated e =>
    match allocationSlots j.term with
    | some slots =>
      if claim e = j ∧ checkScope j.context.length j.term = true ∧ checkTreeUsing G images e codes sums = true ∧
          (slots.map Prod.fst).Nodup ∧ ∀ p ∈ slots, p.2 < j.context.length
      then some (allocOutput k (allocationFacts G j.context k slots) j.context.length
        (contractFields G j.context)) else none
    | none =>
      match mergeSlots j.term with
      | some (_, a, b) =>
        if claim e = j ∧ checkTreeUsing G images e codes sums = true ∧ a < j.context.length ∧ b < j.context.length
        then some (allocOutput k [] j.context.length (contractFields G j.context)) else none
      | none =>
        match storeSlots j.term with
        | some slots =>
          if claim e = j ∧ checkTreeUsing G images e codes sums = true ∧ ∀ i ∈ slots, i < j.context.length
          then some (HeapKnowledge.shift k) else none
        | none => none
  | .written i v R e =>
    match writeSlots j.term with
    | some (fld, i', v') =>
      if claim e = j ∧ checkTreeUsing G images e codes sums = true ∧ i' = i ∧ v' = v ∧
          i < j.context.length ∧ v < j.context.length ∧
          valuesAt G j.context k v = R
      then some (writeOutput k i fld R) else none
    | none => none := by
  cases step <;> simp only [checkStepUsing, checkStepResult, checkedOutput_value,
    CheckResult.value_bind_const,
    CheckResult.accepted_ofBool,
    CheckResult.fromOption, checkTreeUsing, Bool.and_eq_true, decide_eq_true_eq]
  all_goals repeat' first
    | simp_all only [guard_conjunction, option_choice, CheckResult.value_failure,
        checkedOutput_value, CheckResult.value_bind_const, CheckResult.value_map_const,
        CheckResult.value_orElse, CheckResult.accepted_ofBool,
        BranchRefinement.checkObservedSubResult_accepted,
        ProgramCertificates.checkSubtypeUsing_accepted,
        checkTreeUsing, Bool.and_eq_true, decide_eq_true_eq, and_assoc, and_left_comm, and_comm]
    | split
  all_goals (try simp_all) <;> congr

theorem checkStep_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {j k e out}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} (hc : checkStepUsing G images j k e codes sums = some out)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _)
    (hsums : SummariesSound G images sums := by exact Verification.ProgramCertificates.summariesSound_none _ _)
    {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds out (push v ρ) h')
      n W h (instantiate 0 ρ j.term) := by
  cases e with
  | ordinary e =>
    simp only [checkStepUsing_eq] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,_,ht⟩ := hp
      have typed := checkTreeUsing_sound e ht hcodes hsums
      rw [hj] at typed
      cases hc
      exact ordinary_sound typed he hk hw hh
    · contradiction
  | pure e =>
    simp only [checkStepUsing_eq] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,scope,ht,hpure⟩ := hp
      have typed := checkTreeUsing_sound e ht hcodes hsums
      rw [hj] at typed
      cases hc
      exact pure_sound typed hpure scope he hk hw hh
    · contradiction
  | reading e =>
    simp only [checkStepUsing_eq] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,scope,ht,hread⟩ := hp
      have typed := checkTreeUsing_sound e ht hcodes hsums
      rw [hj] at typed
      cases hc
      exact reading_sound typed hread scope he hk hw hh
    · contradiction
  | created e =>
    simp only [checkStepUsing_eq] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,_,ht⟩ := hp
      have typed := checkTreeUsing_sound e ht hcodes hsums
      rw [hj] at typed
      split at hc
      · rename_i arity E K start caps kind rest hb
        cases hc
        rw [hb] at typed ⊢
        exact graphCreation_sound typed he hk hw hh
      · contradiction
    · contradiction
  | typedRead i e =>
    simp only [checkStepUsing_eq] at hc
    split at hc
    · rename_i fld i' hslot
      split at hc
      · rename_i hp
        obtain ⟨hj,ht,rfl,hr⟩ := hp
        have term := readSlot_eq hslot
        cases hi : j.context[i']? with
        | none => simp [hi] at hr
        | some Ref =>
          have hrep : fieldOperand (expand G Ref) fld = true := by simpa [hi] using hr
          have typed := checkTreeUsing_sound e ht hcodes hsums
          rw [hj,term] at typed
          cases hc
          rw [term]
          simpa [instantiate] using typedRead_sound typed hi hrep he hk hw hh
      · split at hc
        · rename_i hp
          obtain ⟨hj,ht,rfl,hr⟩ := hp
          have term := readSlot_eq hslot
          cases hi : j.context[i']? with
          | none => simp [hi] at hr
          | some Ref =>
            have hrep : optionalOperand (expand G Ref) fld = true := by simpa [hi] using hr
            have typed := checkTreeUsing_sound e ht (hsums := hsums)
            rw [hj,term] at typed
            cases hc
            rw [term]
            simpa [instantiate] using optionalRead_sound typed hi hrep he hk hw hh
        · contradiction
    · contradiction
  | observedRead i R =>
    simp only [checkStepUsing_eq] at hc
    split at hc
    · rename_i fld i' hslot
      split at hc
      · rename_i hp
        obtain ⟨rfl,_,hcell,hi⟩ := hp
        have hm := cellHolds hk hcell
        have term := readSlot_eq hslot
        cases hc
        rw [term]
        cases hr : j.context[i']? with
        | some Ref =>
          by_cases hfo : fieldOperand (expand G Ref) fld = true
          · simpa [instantiate, hr, hfo] using presentRead_sound hm hi hr hfo he hk hw hh
          · simpa [instantiate, hr, hfo] using read_sound hm hi he hk hw hh
        | none => simpa [instantiate, hr] using read_sound hm hi he hk hw hh
      · contradiction
    · contradiction
  | slicedRead tag q i e p =>
    simp only [checkStepUsing_eq] at hc
    split at hc
    · rename_i fld i' hslot
      split at hc
      · rename_i hp
        obtain ⟨hctx,hterm,ht,rfl,hr,hf,hsub⟩ := hp
        have term := readSlot_eq hslot
        cases hi : j.context[i']? with
        | none => simp [hi] at hr
        | some Ref =>
          have hrep : fieldOperand (expand G Ref) fld = true ∨ optionalOperand (expand G Ref) fld = true := by
            simpa [hi] using hr
          obtain ⟨C, hC, hfc⟩ := HeapKnowledge.any_some hf
          have hm := HeapKnowledge.cellBy_holds hk (HeapKnowledge.aliases_class hk.2.2.1) hC
          have typed := checkTreeUsing_sound e ht hcodes hsums
          have hj : claim e = ⟨j.context,j.term,(claim e).type⟩ := by
            cases hce : claim e; simp_all
          rw [hj,term] at typed
          cases hc
          rw [term]
          simp only [hi, Option.any_some]
          by_cases hfo : fieldOperand (expand G Ref) fld = true
          · have hs := slicedRead_sound (typedRead_sound typed hi hfo he hk hw hh) hm hfc
              (BranchRefinement.checkObservedSub_sound hsub) hk
            simpa [instantiate, hfo] using hs
          · have hopt := hrep.resolve_left hfo
            have hs := slicedRead_sound (optionalRead_sound typed hi hopt he hk hw hh) hm hfc
              (BranchRefinement.checkObservedSub_sound hsub) hk
            simpa [instantiate, hfo] using hs
      · contradiction
    · contradiction
  | knownValue i R =>
    simp only [checkStepUsing_eq] at hc
    split at hc
    · rename_i hp
      obtain ⟨ht,_,hr,hi⟩ := hp
      cases hc
      rw [ht]
      simpa [instantiate] using value_sound hr hi he hk
    · contradiction
  | linkedRead i y p =>
    simp only [checkStepUsing_eq] at hc
    split at hc
    · rename_i fld i' B hslot hB
      split at hc
      · rename_i hp
        obtain ⟨rfl,hl,hs⟩ := hp
        cases hc
        rw [readSlot_eq hslot]
        simpa [instantiate] using
          linkedRead_sound hl hB (PositiveCertificates.acceptedUsing hs) he hk hw hh
      · contradiction
    · contradiction
  | allocated e =>
    simp only [checkStepUsing_eq] at hc
    split at hc
    · rename_i slots hslots
      split at hc
      · rename_i hp
        obtain ⟨hj,_,ht,hnd,hin⟩ := hp
        have typed := checkTreeUsing_sound e ht hcodes hsums
        rw [hj] at typed
        obtain ⟨code, term⟩ := allocationSlots_eq hslots
        cases hc
        rw [term] at typed ⊢
        have hs := typed.sound n W h ρ he hw hh
        cases code
        all_goals
          simp only [instantiate, instantiateArgs_eq_map, List.map_map,
            Function.comp_def] at hs ⊢
        all_goals exact alloc_sound hnd hin he hk hh hs
      · contradiction
    · split at hc
      · rename_i d a b hmerge
        split at hc
        · rename_i hp
          obtain ⟨hj,ht,ha,hb⟩ := hp
          have typed := checkTreeUsing_sound e ht hcodes hsums
          rw [hj] at typed
          have hva := (meaning_value (he.2 a _ (List.getElem?_eq_getElem ha))).1
          have hvb := (meaning_value (he.2 b _ (List.getElem?_eq_getElem hb))).1
          cases hc
          rcases mergeSlots_eq hmerge with term | term
          · rw [term] at typed ⊢
            have hs := typed.sound n W h ρ he hw hh
            simp only [instantiate] at hs ⊢
            exact merge_alloc_sound hva hvb he hk hh hs
          · rw [term] at typed ⊢
            have hs := typed.sound n W h ρ he hw hh
            simp only [instantiate] at hs ⊢
            exact makeKey_alloc_sound hva hvb he hk hh hs
        · contradiction
      · split at hc
        · rename_i slots hstore
          split at hc
          · rename_i hp
            obtain ⟨hj,ht,hin⟩ := hp
            have typed := checkTreeUsing_sound e ht hcodes hsums
            rw [hj] at typed
            have term := storeSlots_eq hstore
            cases hc
            rw [term] at typed ⊢
            have hs := typed.sound n W h ρ he hw hh
            simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def] at hs ⊢
            refine store_alloc_sound ?_ hk hs
            intro v hv
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
            exact (meaning_value (he.2 i _ (List.getElem?_eq_getElem (hin i hi)))).1
          · contradiction
        · contradiction
  | written i v R e =>
    simp only [checkStepUsing_eq] at hc
    split at hc
    · rename_i fld i' v' hslots
      split at hc
      · rename_i hp
        obtain ⟨hj,ht,rfl,rfl,hi,hv,hr⟩ := hp
        have term := writeSlots_eq hslots
        have typed := checkTreeUsing_sound e ht hcodes hsums
        rw [hj] at typed
        rw [term] at typed
        cases hc
        rw [term]
        simpa [instantiate] using write_sound typed hi hv hr he hk hw hh
      · contradiction
    · contradiction

/-! ### Stable links (HOST-FAMILIES.md, "Stable links")

A read link through a member every clause of its receiver's type states a
stable key holds through every step: the key reads one way for the object's
life, a location whose contract admits one value, which every heap a run
reaches holds there, or an absent key of an object without a prototype. -/

/-- Every clause of `A` states `fld` a stable key. -/
def stableField (G : NormalGraph ι) (A : Ty ι) (fld : PropKey) : Bool :=
  G.plainTy A && !(expand G A).isEmpty && (expand G A).all fun c => c.stableKeys.contains fld

theorem stableField_at {G : NormalGraph ι} {A : Ty ι} {fld : PropKey} {n W v}
    (hs : stableField G A fld = true) (hv : meaning G A n W v) :
    ∃ (flds : List (PropKey × Nat)) (oid : Nat),
      v = .objAt flds .absent oid ∧ StableAt W flds fld := by
  simp only [stableField, Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨⟨hplain, -⟩, hall⟩ := hs
  obtain ⟨c, hc, hsem, -⟩ := (expand_sem G A hplain n W v).mp hv
  exact semWithArgs_stable hsem (List.contains_iff_mem.mp (hall c hc))

/-- The read links a step keeps through its every effect: those through a
member every clause of the receiver's type states stable, optional links
among them. -/
def stableLinks (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : HeapLinks.Links :=
  k.links.filter fun g => !g.alias &&
    match Γ[g.cell]? with
    | some A => stableField G A g.field
    | none => false

/-- The cell facts a step keeps through its every effect: those of a read
through a member every clause of the receiver's type states stable, whose
reading the object keeps for its life. -/
def stableCells (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Facts :=
  k.cells.filter fun f =>
    match Γ[f.slot]? with
    | some A => stableField G A f.field
    | none => false

/-- A step's output with the input's stable links and stable cell facts,
past the result slot, each once. -/
def withStable (G : NormalGraph ι) (Γ : List (Ty ι)) (k out : Knowledge) : Knowledge :=
  { out with
    cells := out.cells ++
      (HeapFacts.shift (stableCells G Γ k)).filter fun f => !out.cells.contains f
    links := out.links ++
      (HeapLinks.pull (stableLinks G Γ k) (fun i => [i+1])).filter fun g => !out.links.contains g }

/-- What a kept link says of a heap: a read link's meaning in `HeapLinks.Holds`. -/
private def LinkAt (ρ : Env) (h : Heap) (g : HeapLinks.Link) : Prop :=
  if g.optional then ∃ flds c oid, ρ g.cell = .objAt flds c oid ∧ ReadGave flds g.field h (ρ g.value)
  else ∃ flds c oid l, ρ g.cell = .objAt flds c oid ∧ flds.lookup g.field = some l ∧ h[l]? = some (ρ g.value)

/-- Either form of a read link is a read the object gave. -/
private theorem LinkAt.read {ρ h g} (hg : LinkAt ρ h g) :
    ∃ flds c oid, ρ g.cell = .objAt flds c oid ∧ ReadGave flds g.field h (ρ g.value) := by
  unfold LinkAt at hg
  split at hg
  · exact hg
  · obtain ⟨flds, c, oid, l, hcell, hl, hv⟩ := hg
    exact ⟨flds, c, oid, hcell, ReadGave.present hl hv⟩

private theorem LinkAt.of_read {ρ h g flds c oid} (hcell : ρ g.cell = .objAt flds c oid)
    (hr : ReadGave flds g.field h (ρ g.value)) (hpresent : g.optional = false → (flds.lookup g.field).isSome) :
    LinkAt ρ h g := by
  unfold LinkAt
  split
  · exact ⟨flds, c, oid, hcell, hr⟩
  · rename_i ho
    have hs := hpresent (by simpa using ho)
    cases hl : flds.lookup g.field with
    | none => rw [hl] at hs; cases hs
    | some l =>
      have hv : h[l]? = some (ρ g.value) := by simpa [ReadGave, hl] using hr
      exact ⟨flds, c, oid, l, hcell, hl, hv⟩

private theorem stable_frames {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {ρ n W h t}
    {T : Fam} {Q : Post} (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hh : HeapOk n W h) :
    ∀ (S : HeapLinks.Links), (∀ g ∈ S, g ∈ stableLinks G Γ k) →
      SafePost (excOf G) T Q n W h t →
      SafePost (excOf G) T (fun h' v => Q h' v ∧ ∀ g ∈ S, LinkAt ρ h' g) n W h t := by
  intro S
  induction S with
  | nil =>
    intro _ hs
    exact consequence (fun _ _ _ h => h) (fun _ _ hq => ⟨hq, fun _ hg => by cases hg⟩) hs
  | cons g S ih =>
    intro hS hs
    have rest := ih (fun x hx => hS x (List.mem_cons_of_mem _ hx)) hs
    have hg := hS g List.mem_cons_self
    simp only [stableLinks, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hg
    obtain ⟨hmem, ha, hty⟩ := hg
    have hlink : LinkAt ρ h g := by
      have := hk.2.2.1 g hmem
      simp only [ha, Bool.false_eq_true, if_false] at this
      unfold LinkAt
      exact this
    obtain ⟨flds, c, oid, hcell, hr⟩ := hlink.read
    have hpresent : g.optional = false → (flds.lookup g.field).isSome := by
      intro ho
      unfold LinkAt at hlink
      simp only [ho, Bool.false_eq_true, if_false] at hlink
      obtain ⟨flds', c', oid', l, hcell', hl, -⟩ := hlink
      rw [hcell] at hcell'
      cases hcell'
      simp [hl]
    split at hty
    · rename_i A hA
      obtain ⟨flds', oid', hcell', hst⟩ := stableField_at hty (he.2 g.cell A hA)
      rw [hcell] at hcell'
      cases hcell'
      refine consequence (fun _ _ _ h => h) (fun h' u hq => ?_)
        (ReadGave.stable_frame hst hh hr rest)
      obtain ⟨⟨hq, hall⟩, hr'⟩ := hq
      refine ⟨hq, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact LinkAt.of_read hcell hr' hpresent
      · exact hall x hx
    · cases hty

private theorem stable_cell_frames {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {ρ n W h t}
    {T : Fam} {Q : Post} (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hh : HeapOk n W h) :
    ∀ (S : Facts), (∀ f ∈ S, f ∈ stableCells G Γ k) →
      SafePost (excOf G) T Q n W h t →
      SafePost (excOf G) T (fun h' v => Q h' v ∧ HeapFacts.Holds S ρ h') n W h t := by
  intro S
  induction S with
  | nil =>
    intro _ hs
    exact consequence (fun _ _ _ h => h) (fun _ _ hq => ⟨hq, fun _ hf => by cases hf⟩) hs
  | cons f S ih =>
    intro hS hs
    have rest := ih (fun x hx => hS x (List.mem_cons_of_mem _ hx)) hs
    have hf := hS f List.mem_cons_self
    simp only [stableCells, List.mem_filter] at hf
    obtain ⟨hmem, hty⟩ := hf
    obtain ⟨flds, c, oid, u, hcell, hr, hatom⟩ := hk.1 f hmem
    split at hty
    · rename_i A hA
      obtain ⟨flds', oid', hcell', hst⟩ := stableField_at hty (he.2 f.slot A hA)
      rw [hcell] at hcell'
      cases hcell'
      refine consequence (fun _ _ _ h => h) (fun h' _ hq => ?_)
        (ReadGave.stable_frame hst hh hr rest)
      obtain ⟨⟨hq, hall⟩, hr'⟩ := hq
      refine ⟨hq, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨flds, _, oid, u, hcell, hr', hatom⟩
      · exact hall x hx
    · cases hty

/-- **Stable links survive every step.** Whatever a step's postcondition, its
input's stable links and stable cell facts hold of every heap it returns in. -/
theorem withStable_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {k out : Knowledge} {ρ n W h t} {T : Fam}
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hh : HeapOk n W h)
    (hs : SafePost (excOf G) T (fun h' v => HeapKnowledge.Holds out (push v ρ) h') n W h t) :
    SafePost (excOf G) T (fun h' v => HeapKnowledge.Holds (withStable G Γ k out) (push v ρ) h') n W h t := by
  refine consequence (fun _ _ _ h => h) (fun h' v hq => ?_)
    (stable_cell_frames he hk hh (stableCells G Γ k) (fun _ hf => hf)
      (stable_frames he hk hh (stableLinks G Γ k) (fun _ hg => hg) hs))
  obtain ⟨⟨hout, hall⟩, hcells⟩ := hq
  have hS : HeapLinks.Holds (stableLinks G Γ k) ρ h' := by
    intro g hg
    have hg' := hg
    simp only [stableLinks, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hg'
    obtain ⟨-, ha, -⟩ := hg'
    simp only [ha, Bool.false_eq_true, if_false]
    have := hall g hg
    unfold LinkAt at this
    exact this
  have hpull := HeapLinks.pull_holds (pre := fun i => [i+1]) (τ := push v ρ) hS
    (fun i j hj => by simp at hj; subst hj; rfl)
  have hshift := HeapFacts.shift_holds (v := v) hcells
  refine ⟨fun f hf => ?_, hout.2.1, fun g hg => ?_, hout.2.2.2⟩
  · rcases List.mem_append.mp hf with hf | hf
    · exact hout.1 f hf
    · exact hshift f (List.mem_filter.mp hf).1
  rcases List.mem_append.mp hg with hg | hg
  · exact hout.2.2.1 g hg
  · exact hpull g (List.mem_filter.mp hg).1

/-- A checker whose every step also keeps its input's stable links and
stable cell facts. -/
@[nospecialize] def Checker.keepingStable [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums => (base.run j k e codes sums).map (withStable G j.context k)
  select := fun j k e codes sums => (base.select j k e codes sums).map (withStable G j.context k)
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    simp only [CheckResult.map, Option.map_eq_some_iff] at hc
    obtain ⟨out0, h0, rfl⟩ := hc
    exact withStable_sound he hk hh (base.sound h0 hcodes hsums he hk hw hh)

/-- The steps' own rules, without the stable links every step keeps. -/
@[nospecialize] def Checker.steps [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) : Checker G images where
  run := fun j k e codes sums => checkStepResult G images j k e codes sums
  select := fun j k e codes sums => checkStepResult G images j k e codes sums (tree := false)
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    exact checkStep_sound hc hcodes hsums he hk hw hh


/-- Descriptor-aware ordinary expressions use the same heap-forgetting rule
as ordinary calls. Other effect rules retain their existing checks. A read
summary's comparisons are the ordinary checker's, which the body's rule
admits (`ordinary`). -/
@[nospecialize] def Checker.subtypingSteps [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (subtyping : BodySubtyping G)
    (ordinary : ∀ {A B p}, PositiveCertificates.checkUsing G images A B p = true → subtyping.check A B p = true) :
    Checker G images where
  run := fun j k step codes sums => match step with
    | .ordinary e =>
      (CheckResult.ofBool (decide (claim e = j ∧ checkScope j.context.length j.term = true) &&
        checkTreeWith G images subtyping.check e codes sums)).bind fun _ => pure (ordinaryOutput k)
    | step => checkStepResult G images j k step codes sums
  sound := by
    intro j k step out codes sums checked hcodes hsums ρ n W h he hk hw hh
    cases step with
    | ordinary e =>
      simp only [CheckResult.value_bind_const, CheckResult.accepted_ofBool] at checked
      change (if decide (claim e = j ∧ checkScope j.context.length j.term = true) &&
        checkTreeWith G images subtyping.check e codes sums then some (ordinaryOutput k) else none) = some out at checked
      split at checked
      · rename_i tests
        simp only [Bool.and_eq_true, decide_eq_true_eq] at tests
        cases checked
        have typed := checkTreeWith_sound subtyping e tests.2 hcodes hsums ordinary
        rw [tests.1.1] at typed
        exact ordinary_sound typed he hk hw hh
      · cases checked
    | _ => exact checkStep_sound checked hcodes hsums he hk hw hh

/-- Descriptor-aware steps, each keeping its input's stable links. -/
@[nospecialize] def Checker.withSubtyping [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (subtyping : BodySubtyping G)
    (ordinary : ∀ {A B p}, PositiveCertificates.checkUsing G images A B p = true → subtyping.check A B p = true) :
    Checker G images :=
  (Checker.subtypingSteps G images subtyping ordinary).keepingStable

end Verification.HeapExpressionRules
