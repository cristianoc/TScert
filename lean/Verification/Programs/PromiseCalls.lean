import Verification.Programs.ExpressionEffects
import Verification.Programs.IndexWrites
import Verification.Semantics.SurvivalSeparation
import Verification.Programs.FrameChecks

/-! # Promises between slots

A call at a promise signature (`CallEffects.Effect.guards`, `.asserts`)
establishes a type for its promised actual: where its result is `true`, or
wherever it returns. A graph carries such a fact between nodes as an
implication between two immutable slots, `test = true ⟹ target : T`; a node's
expression establishes facts about its own result as yields. A branch on the
result consumes them, and a return under a promise goal states them of the
argument. Types are world-indexed, so each fact holds at the state's world and
is carried, like an environment's types, by transfer to later worlds. -/
namespace Verification.PromiseCalls
variable {ε : Verification.HeapKnowledge.EntryState}
open ProgramTyping ProgramCertificates PositiveGraphs PositiveRules HeapObservations BranchRefinement
open CallEffects (Effect Arrow Contract)
open PositiveCertificates (InstanceImageCheck)

/-- Where the slot `test` holds `true`, the slot `target` holds a value of `type`. -/
structure Implication (ι : Type) where
  test : Nat
  target : Nat
  type : Ty ι
  deriving DecidableEq, Hashable, Repr

/-- What a node's result promises of a slot of the node's entry: its type,
where the result is `true` (`conditional`), where it is `false` (`onFalse`),
or wherever the expression returns. A tag test's yield carries the evidence
that the test's slice is within it. -/
structure Yield (ι : Type) where
  conditional : Bool
  target : Nat
  type : Ty ι
  evidence : Option (PositiveCertificates.SubtypeChoices ι) := none
  onFalse : Bool := false

section
variable {ι : Type}

def ImpliesOk (G : NormalGraph ι) (xs : List (Implication ι)) (ρ : Env) (n : Nat) (W : WorldT n) : Prop :=
  ∀ x ∈ xs, ρ x.test = .tru → meaning G x.type n W (ρ x.target)

/-- The yields of a result `u`, over the entry environment `ρ`. -/
def YieldsOk (G : NormalGraph ι) (ys : List (Yield ι)) (ρ : Env) : Fam := fun n W u =>
  ∀ y ∈ ys, (y.conditional = true → u = .tru) → (y.onFalse = true → u = .fls) →
    meaning G y.type n W (ρ y.target)

theorem meaning_within [DecidableEq ι] {G : NormalGraph ι} {A B : Ty ι} (h : within A B = true) {n W v}
    (hv : meaning G A n W v) : meaning G B n W v := by
  obtain ⟨a, ha, hv⟩ := hv
  exact ⟨a, within_mem h ha, hv⟩

theorem ImpliesOk.transfer {G : NormalGraph ι} {xs ρ n W} (h : ImpliesOk G xs ρ n W)
    (j : Nat) (hj : j ≤ n) (U : WorldT j) (hx : WExt (trunc j hj W) U) : ImpliesOk G xs ρ j U :=
  fun x hx' ht => (meaning_adm G x.type).mono j _ U hx _
    ((meaning_adm G x.type).down_le n j hj W _ (h x hx' ht))

theorem YieldsOk.transfer {G : NormalGraph ι} {ys ρ n W u} (h : YieldsOk G ys ρ n W u)
    (j : Nat) (hj : j ≤ n) (U : WorldT j) (hx : WExt (trunc j hj W) U) : YieldsOk G ys ρ j U u :=
  fun y hy hc hf => (meaning_adm G y.type).mono j _ U hx _
    ((meaning_adm G y.type).down_le n j hj W _ (h y hy hc hf))

theorem ImpliesOk.nil (G : NormalGraph ι) (ρ : Env) (n : Nat) (W : WorldT n) : ImpliesOk G [] ρ n W := by
  intro x hx; cases hx

/-- The facts a result's yields establish: every yield where the result
answered `true`, else the unconditional ones; where it answered `false`
(`falsified`), also those stated of that answer. -/
def yieldFacts (ys : List (Yield ι)) (answered : Bool) (falsified : Bool := false) : List (Nat × Ty ι) :=
  ys.filterMap fun y => if (!y.onFalse || falsified) && (!y.conditional || answered) then some (y.target, y.type) else none

theorem yieldFacts_holds {G : NormalGraph ι} {ys : List (Yield ι)} {ρ n W u} {answered falsified : Bool}
    (hy : YieldsOk G ys ρ n W u) (ha : answered = true → u = .tru) (hfl : falsified = true → u = .fls) :
    ∀ f ∈ yieldFacts ys answered falsified, meaning G f.2 n W (ρ f.1) := by
  intro f hf
  obtain ⟨y, hy', he⟩ := List.mem_filterMap.mp hf
  split at he
  · rename_i hc
    cases he
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
    refine hy y hy' (fun hcond => ?_) (fun hneg => ?_)
    · rcases hc.2 with h | h
      · rw [hcond] at h; cases h
      · exact ha h
    · rcases hc.1 with h | h
      · rw [hneg] at h; cases h
      · exact hfl h
  · cases he

/-- A context with the slots of `facts`, past `shift` slots, refined: each
at the fact's type filtered by its own (`BranchRefinement.factFilter`). -/
@[nospecialize] def refineBy [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (facts : List (Nat × Ty ι)) (shift : Nat) :
    List (Ty ι) :=
  facts.foldl (fun Δ f => match Δ[f.1 + shift]? with
    | some A => Δ.set (f.1 + shift) (BranchRefinement.factFilter G A f.2)
    | none => Δ) Γ

theorem envOk_set {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W i T}
    (h : EnvOk G Γ ρ n W) (hT : meaning G T n W (ρ i)) : EnvOk G (Γ.set i T) ρ n W := by
  refine ⟨h.1, fun k A hk => ?_⟩
  rw [List.getElem?_set] at hk
  split at hk
  · rename_i heq
    subst heq
    split at hk
    · cases hk; exact hT
    · cases hk
  · exact h.2 k A hk

/-- A context refined by facts its values meet, given a heap meeting the
world: the meet's exclusions read the heap's field contents. -/
theorem envOk_refineBy [DecidableEq ι] {G : NormalGraph ι} {ρ n W shift} {h : Heap} (hh : HeapOk (n+1) W h) :
    ∀ {Γ : List (Ty ι)} {facts : List (Nat × Ty ι)}, EnvOk G Γ ρ (n+1) W →
      (∀ f ∈ facts, meaning G f.2 (n+1) W (ρ (f.1 + shift))) → EnvOk G (refineBy G Γ facts shift) ρ (n+1) W
  | _, [], he, _ => he
  | Γ, f :: fs, he, hf => by
    simp only [PromiseCalls.refineBy, List.foldl_cons]
    have step : EnvOk G (match Γ[f.1 + shift]? with
        | some A => Γ.set (f.1 + shift) (BranchRefinement.factFilter G A f.2)
        | none => Γ) ρ (n+1) W := by
      split
      · rename_i A hA
        exact envOk_set he (BranchRefinement.factFilter_sound (he.2 _ A hA) (hf f (by simp)) hh)
      · exact he
    exact envOk_refineBy hh step (fun g hg => hf g (by simp [hg]))

/-! ## Refinement by integer facts

A slot a step's facts state a safe integer (`HeapKnowledge.intSlot`) is read
within the clause `int` (docs/drafts/integer-types.md, "The bridge"): its
type's meet with `int` lies there, so a plain type not already within the
safe integers is read at the graph's `int` label, whose row is checked to be
that one clause. -/

/-- The graph's `int` label, its row checked to be the one clause `int`. -/
def intLabel (G : NormalGraph ι) : Option ι :=
  G.intLabel.filter fun l => match G l with
    | [.int] => true
    | _ => false

/-- Whether a fact stating a slot's value a safe integer refines its type
`A`: a plain type not already within the safe integers
(`IndexWrites.intClause`). Its meet with `int` lies within `int`, which the
refinement reads it at; a parameter, scheme or meet row keeps its type. -/
def intRefinable (G : NormalGraph ι) (A : Ty ι) : Bool :=
  G.plainTy A && !(PositiveRules.expand G A).all IndexWrites.intClause

/-- Whether a tag fact refines `A`: a plain type not already answering `tag` with `q`. -/
def tagRefinable (G : NormalGraph ι) (A : Ty ι) (tag : Tag) (q : Bool) : Bool :=
  G.plainTy A && !(PositiveRules.expand G A).all fun c => tagClause tag c == some q

/-- One slot's type refined by the safe-integer and nullish-exclusion facts
`as` establish for slot `i`. -/
def slotRefine (G : NormalGraph ι) (as : List HeapKnowledge.IndexAtom) (i : Nat) (A : Ty ι) : Ty ι :=
  let A0 := match intLabel G with
    | some L => if HeapKnowledge.intSlot as i && intRefinable G A then [L] else A
    | none => A
  let A1 := if HeapKnowledge.slotGuardTag as i .notNull && tagRefinable G A0 .isNul false then
    BranchRefinement.tagSlice G A0 .isNul false else A0
  if HeapKnowledge.slotGuardTag as i .notUndef && tagRefinable G A1 .isUndef false then
    BranchRefinement.tagSlice G A1 .isUndef false else A1

/-- **A context refined by integer and nullish-exclusion facts**: each slot
refined by `slotRefine`. -/
def intRefine (G : NormalGraph ι) (Γ : List (Ty ι)) (as : List HeapKnowledge.IndexAtom) : List (Ty ι) :=
  Γ.mapIdx (slotRefine G as)

/-- Whether `D` is `A` refined by some subset of the integer and
nullish-exclusion facts `as` establish for slot `i`. -/
def slotRefines [DecidableEq ι] (G : NormalGraph ι) (as : List HeapKnowledge.IndexAtom) (i : Nat) (A D : Ty ι) : Bool :=
  if D == A then true
  else if (match intLabel G with | some L => D == [L] && HeapKnowledge.intSlot as i | none => false) then true
  else
    let nN := HeapKnowledge.slotGuardTag as i .notNull
    let nU := HeapKnowledge.slotGuardTag as i .notUndef
    let sN := BranchRefinement.tagSlice G A .isNul false
    let sU := BranchRefinement.tagSlice G A .isUndef false
    (nN && D == sN) || (nU && D == sU) || (nN && nU && D == BranchRefinement.tagSlice G sN .isUndef false)

/-- Whether `Δ` is `Γ` refined by integer and nullish-exclusion facts: as long,
each slot its type in `Γ` or a proved refinement of it in `as`. -/
def intRefines [DecidableEq ι] (G : NormalGraph ι) (Γ Δ : List (Ty ι)) (as : List HeapKnowledge.IndexAtom) : Bool :=
  Δ.length == Γ.length && (List.range Δ.length).all fun i =>
    match Γ[i]?, Δ[i]? with
    | some A, some D => slotRefines G as i A D
    | _, _ => false

theorem intLabel_meaning {G : NormalGraph ι} {L : ι} (hL : intLabel G = some L) {n W b}
    (hb : SafeIntegers.safeIntOfBits b ≠ none) : meaning G [L] n W (.num b) := by
  unfold intLabel at hL
  obtain ⟨-, hrow⟩ := Option.filter_eq_some_iff.mp hL
  have hG : G L = [.int] := by
    split at hrow
    · assumption
    · cases hrow
  refine expand_sem_mpr ⟨.int, by simp [clausesOf, hG], ?_,
    builtinInvariant_of_withoutInvariant (by simp [PositiveNormalization.Clause.carriesInvariant]) _ _ _⟩
  simpa [PositiveNormalization.semWithArgs, PositiveNormalization.intT] using hb

theorem intSlot_meaning {G : NormalGraph ι} {L : ι} (hL : intLabel G = some L)
    {as : List HeapKnowledge.IndexAtom} {ρ : Env} {h : Heap} (hk : HeapKnowledge.IndexHolds ε as ρ h)
    {i : Nat} (hi : HeapKnowledge.intSlot as i = true) {n W} : meaning G [L] n W (ρ i) := by
  have hv := HeapKnowledge.intSlot_sound hk hi
  cases hρ : ρ i with
  | num b =>
    rw [hρ] at hv
    exact intLabel_meaning hL (by simpa [HeapKnowledge.intValue, Option.isSome_iff_ne_none] using hv)
  | _ => rw [hρ] at hv; simp [HeapKnowledge.intValue] at hv

private theorem tagHolds_isNul_of_ne {v : Val} (h : v ≠ .nul) : tagHolds .isNul v = false := by
  cases v <;> simp_all [tagHolds]

private theorem tagHolds_isUndef_of_ne {v : Val} (h : v ≠ .undef) : tagHolds .isUndef v = false := by
  cases v <;> simp_all [tagHolds]

private theorem slotRefine_meaning {G : NormalGraph ι} {as bs : List HeapKnowledge.IndexAtom}
    {i : Nat} {A : Ty ι} {ρ : Env} {h : Heap} {n W}
    (hint : HeapKnowledge.intSlot as i = true → HeapKnowledge.intSlot bs i = true)
    (htag : ∀ t, HeapKnowledge.slotGuardTag as i t = true → HeapKnowledge.slotGuardTag bs i t = true)
    (hA : meaning G A n W (ρ i)) (hk : HeapKnowledge.IndexHolds ε bs ρ h) :
    meaning G (slotRefine G as i A) n W (ρ i) := by
  unfold slotRefine
  dsimp only
  have hA0 : meaning G (match intLabel G with
      | some L => if HeapKnowledge.intSlot as i && intRefinable G A then [L] else A
      | none => A) n W (ρ i) := by
    cases hL : intLabel G with
    | none => exact hA
    | some L =>
      dsimp only
      split
      · rename_i hc
        exact intSlot_meaning hL hk (hint (Bool.and_eq_true_iff.mp hc).1)
      · exact hA
  generalize (match intLabel G with
      | some L => if HeapKnowledge.intSlot as i && intRefinable G A then [L] else A
      | none => A) = A0 at hA0 ⊢
  have hA1 : meaning G (if HeapKnowledge.slotGuardTag as i .notNull && tagRefinable G A0 .isNul false then
      BranchRefinement.tagSlice G A0 .isNul false else A0) n W (ρ i) := by
    split
    · rename_i hc
      have hne := HeapKnowledge.slotGuardTag_sound hk (htag .notNull (Bool.and_eq_true_iff.mp hc).1)
      exact BranchRefinement.tagSlice_sound hA0 (.inl (tagHolds_isNul_of_ne hne))
    · exact hA0
  generalize (if HeapKnowledge.slotGuardTag as i .notNull && tagRefinable G A0 .isNul false then
      BranchRefinement.tagSlice G A0 .isNul false else A0) = A1 at hA1 ⊢
  split
  · rename_i hc
    have hne := HeapKnowledge.slotGuardTag_sound hk (htag .notUndef (Bool.and_eq_true_iff.mp hc).1)
    exact BranchRefinement.tagSlice_sound hA1 (.inl (tagHolds_isUndef_of_ne hne))
  · exact hA1

/-- **The refined context types the environment** where the atoms hold. -/
theorem envOk_intRefine {G : NormalGraph ι} {Γ : List (Ty ι)} {as : List HeapKnowledge.IndexAtom}
    {ρ : Env} {h : Heap} {n W} (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.IndexHolds ε as ρ h) :
    EnvOk G (intRefine G Γ as) ρ n W := by
  refine ⟨he.1, fun i A hA => ?_⟩
  rw [intRefine, List.getElem?_mapIdx] at hA
  cases hB : Γ[i]? with
  | none => rw [hB] at hA; cases hA
  | some B =>
    rw [hB] at hA
    simp only [Option.map_some, Option.some.injEq] at hA
    subst hA
    exact slotRefine_meaning id (fun _ h => h) (he.2 i B hB) hk

/-- **A context the check accepts as refined types the environment** where
the atoms hold. -/
theorem envOk_intRefines [DecidableEq ι] {G : NormalGraph ι} {Γ Δ : List (Ty ι)} {as : List HeapKnowledge.IndexAtom}
    {ρ : Env} {h : Heap} {n W} (hr : intRefines G Γ Δ as = true) (he : EnvOk G Γ ρ n W)
    (hk : HeapKnowledge.IndexHolds ε as ρ h) : EnvOk G Δ ρ n W := by
  simp only [intRefines, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hr
  refine ⟨he.1, fun i D hD => ?_⟩
  have hi : i < Δ.length := (List.getElem?_eq_some_iff.mp hD).1
  have hΓ : i < Γ.length := hr.1 ▸ hi
  have hA : Γ[i]? = some Γ[i] := List.getElem?_eq_getElem hΓ
  have hc := hr.2 i hi
  rw [hA, hD] at hc
  dsimp only at hc
  have hm := he.2 i _ hA
  have htags : ∀ {A : Ty ι}, meaning G A n W (ρ i) →
      (HeapKnowledge.slotGuardTag as i .notNull && D == BranchRefinement.tagSlice G A .isNul false ||
       HeapKnowledge.slotGuardTag as i .notUndef && D == BranchRefinement.tagSlice G A .isUndef false ||
       HeapKnowledge.slotGuardTag as i .notNull && HeapKnowledge.slotGuardTag as i .notUndef &&
         D == BranchRefinement.tagSlice G (BranchRefinement.tagSlice G A .isNul false) .isUndef false) = true →
      meaning G D n W (ρ i) := by
    intro A hA ht
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at ht
    rcases ht with (⟨hnN, hEq⟩ | ⟨hnU, hEq⟩) | ⟨⟨hnN, hnU⟩, hEq⟩
    · subst hEq
      exact BranchRefinement.tagSlice_sound hA (.inl (tagHolds_isNul_of_ne (HeapKnowledge.slotGuardTag_sound hk hnN)))
    · subst hEq
      exact BranchRefinement.tagSlice_sound hA (.inl (tagHolds_isUndef_of_ne (HeapKnowledge.slotGuardTag_sound hk hnU)))
    · subst hEq
      exact BranchRefinement.tagSlice_sound
        (BranchRefinement.tagSlice_sound hA (.inl (tagHolds_isNul_of_ne (HeapKnowledge.slotGuardTag_sound hk hnN))))
        (.inl (tagHolds_isUndef_of_ne (HeapKnowledge.slotGuardTag_sound hk hnU)))
  unfold slotRefines at hc
  by_cases hEq : (D == Γ[i]) = true
  · rw [beq_iff_eq.mp hEq]; exact hm
  · simp only [hEq] at hc
    cases hLb : intLabel G with
    | none =>
      rw [hLb] at hc
      simp only [Bool.false_eq_true, ite_false] at hc
      exact htags hm hc
    | some L =>
      rw [hLb] at hc
      by_cases hL : (D == [L] && HeapKnowledge.intSlot as i) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at hL
        rw [hL.1]
        exact intSlot_meaning hLb hk hL.2
      · simp only [hL] at hc
        exact htags hm hc

/-- The unconditional atoms that state a slot a safe integer or guard tag, as
`intSlot` and `slotGuardTag` read them. -/
def intAtoms (as : List HeapKnowledge.IndexAtom) : List HeapKnowledge.IndexAtom :=
  as.filter fun a => a.cond.isNone && (match a.fact with
    | .int _ | .length _ _ | .linear _ => true
    | _ => !(HeapKnowledge.atomGuardTags a.fact).isEmpty)

/-- Knowledge `k` with the atoms of `k₀` stating safe integers or slot guard
tags: a writing step's facts over every location, with the facts its context
was refined by (`checkedStep`). -/
def withInts (k k₀ : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge :=
  { k with indices := k.indices ++ intAtoms k₀.indices }

theorem intSlot_intAtoms (as : List HeapKnowledge.IndexAtom) (i : Nat) :
    HeapKnowledge.intSlot (intAtoms as) i = HeapKnowledge.intSlot as i := by
  unfold HeapKnowledge.intSlot intAtoms
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨a, ha, h⟩; exact ⟨a, (List.mem_filter.mp ha).1, h⟩
  · rintro ⟨a, ha, h⟩
    refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, h⟩
    simp only [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    obtain ⟨-, h2⟩ := h
    split at h2 <;> simp_all

theorem slotGuardTag_intAtoms (as : List HeapKnowledge.IndexAtom) (i : Nat) (t : HeapKnowledge.GuardTag) :
    HeapKnowledge.slotGuardTag (intAtoms as) i t = HeapKnowledge.slotGuardTag as i t := by
  unfold HeapKnowledge.slotGuardTag intAtoms
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨a, ha, h⟩; exact ⟨a, (List.mem_filter.mp ha).1, h⟩
  · rintro ⟨a, ha, h⟩
    refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, h⟩
    simp only [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    obtain ⟨-, h2⟩ := h
    obtain ⟨p, hp, -⟩ := List.any_eq_true.mp h2
    have hne : !(HeapKnowledge.atomGuardTags a.fact).isEmpty = true := by
      cases hts : HeapKnowledge.atomGuardTags a.fact with
      | nil => rw [hts] at hp; cases hp
      | cons _ _ => rfl
    cases hf : a.fact <;> simp only [hf] at hne ⊢ <;> first | rfl | exact hne

theorem intSlot_withInts (k k₀ : HeapKnowledge.Knowledge) (i : Nat) :
    (HeapKnowledge.intSlot k₀.indices i = true → HeapKnowledge.intSlot (withInts k k₀).indices i = true) ∧
    (∀ t, HeapKnowledge.slotGuardTag k₀.indices i t = true →
      HeapKnowledge.slotGuardTag (withInts k k₀).indices i t = true) := by
  constructor
  · intro h
    simp only [withInts, HeapKnowledge.intSlot, List.any_append, Bool.or_eq_true] at h ⊢
    right
    have := intSlot_intAtoms k₀.indices i
    simp only [HeapKnowledge.intSlot] at this
    rw [this]; exact h
  · intro t h
    simp only [withInts, HeapKnowledge.slotGuardTag, List.any_append, Bool.or_eq_true] at h ⊢
    right
    have := slotGuardTag_intAtoms k₀.indices i t
    simp only [HeapKnowledge.slotGuardTag] at this
    rw [this]; exact h

theorem holds_withInts {k k₀ : HeapKnowledge.Knowledge} {ρ : Env} {h : Heap}
    (hk : HeapKnowledge.Holds k ε ρ h) (hk₀ : HeapKnowledge.Holds k₀ ε ρ h) :
    HeapKnowledge.Holds (withInts k k₀) ε ρ h := by
  refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, fun a ha hc => ?_⟩
  rcases List.mem_append.mp ha with ha | ha
  · exact hk.2.2.2.2.2 a ha hc
  · exact hk₀.2.2.2.2.2 a (List.mem_filter.mp ha).1 hc

theorem holds_of_withInts {k k₀ : HeapKnowledge.Knowledge} {ρ : Env} {h : Heap}
    (hk : HeapKnowledge.Holds (withInts k k₀) ε ρ h) : HeapKnowledge.Holds k ε ρ h :=
  ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1,
    fun a ha hc => hk.2.2.2.2.2 a (List.mem_append_left _ ha) hc⟩

/-- **A context refined by the integer and tag facts of `as` types the
environment wherever atoms `bs` stating each of them hold.** -/
theorem envOk_intRefine_of {G : NormalGraph ι} {Γ : List (Ty ι)} {as bs : List HeapKnowledge.IndexAtom}
    {ρ : Env} {h : Heap} {n W}
    (hsub : ∀ i, (HeapKnowledge.intSlot as i = true → HeapKnowledge.intSlot bs i = true) ∧
      (∀ t, HeapKnowledge.slotGuardTag as i t = true → HeapKnowledge.slotGuardTag bs i t = true))
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.IndexHolds ε bs ρ h) :
    EnvOk G (intRefine G Γ as) ρ n W := by
  refine ⟨he.1, fun i A hA => ?_⟩
  rw [intRefine, List.getElem?_mapIdx] at hA
  cases hB : Γ[i]? with
  | none => rw [hB] at hA; cases hA
  | some B =>
    rw [hB] at hA
    simp only [Option.map_some, Option.some.injEq] at hA
    subst hA
    exact slotRefine_meaning (hsub i).1 (hsub i).2 (he.2 i B hB) hk

theorem intRefines_self [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (as : List HeapKnowledge.IndexAtom) :
    intRefines G Γ Γ as = true := by
  simp only [intRefines, beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range]
  intro i hi
  rw [List.getElem?_eq_getElem hi]
  simp [slotRefines]

theorem intRefine_length (G : NormalGraph ι) (Γ : List (Ty ι)) (as : List HeapKnowledge.IndexAtom) :
    (intRefine G Γ as).length = Γ.length := by
  simp [intRefine]

/-- The implications a state establishes on an edge, in its own slots: the
entry's, and, where the result is pushed into slot 0, the result's
conditional yields as implications on it. -/
def edgeImplications (xs : List (Implication ι)) (ys : List (Yield ι)) (pushed : Bool) : List (Implication ι) :=
  if pushed then
    xs.map (fun x => ⟨x.test + 1, x.target + 1, x.type⟩) ++
      ys.filterMap (fun y => if y.conditional && !y.onFalse then some ⟨0, y.target + 1, y.type⟩ else none)
  else xs

theorem edgeImplications_holds {G : NormalGraph ι} {xs : List (Implication ι)} {ys ρ n W u}
    (hx : ImpliesOk G xs ρ n W) (hy : YieldsOk G ys ρ n W u) :
    ImpliesOk G (edgeImplications xs ys true) (push u ρ) n W := by
  intro x hm ht
  simp only [edgeImplications, ↓reduceIte, List.mem_append, List.mem_map, List.mem_filterMap] at hm
  rcases hm with ⟨x', hx', rfl⟩ | ⟨y, hy', he⟩
  · exact hx x' hx' ht
  · split at he
    · rename_i hc
      cases he
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      exact hy y hy' (fun _ => ht) (fun hf => by rw [hc.2] at hf; cases hf)
    · cases he

/-! ### The tags of a strict comparison

A strict comparison `x === y` is, where it answers `true`, a membership test
of `x` against tags read off `y`'s type: each clause of the type has tags one
of which holds of every value strictly equal to a member of the clause
(`equalityTagsOf_sound`). Where `y`'s type is one value up to strict
equality, it is, where it answers `false`, the failing test of that value's
tag (`singletonTag_sound`). PROGRAM-TYPING.md, "A strict comparison". -/

section EqualityTags
open PositiveNormalization

theorem numberEqual_symm (a b : UInt64) : numberEqual a b = numberEqual b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [numberEqual, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
  constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨h2, h1⟩, h3.imp Eq.symm And.symm⟩

/-- `Number::equal` is transitive: NaN equals nothing, and the zeros equal
each other only. -/
theorem numberEqual_trans {a b c : UInt64} (h1 : numberEqual a b = true) (h2 : numberEqual b c = true) :
    numberEqual a c = true := by
  simp only [numberEqual, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at *
  obtain ⟨⟨ha, -⟩, h1⟩ := h1
  obtain ⟨⟨-, hc⟩, h2⟩ := h2
  refine ⟨⟨ha, hc⟩, ?_⟩
  rcases h1 with rfl | ⟨za, zb⟩ <;> rcases h2 with rfl | ⟨zb', zc⟩
  · exact .inl rfl
  · exact .inr ⟨zb', zc⟩
  · exact .inr ⟨za, zb⟩
  · exact .inr ⟨za, zc⟩

/-- Two primitives the same value: the same term other than a number, or
two numbers `Number::equal` relates. -/
theorem sameValue_true {u v : Tm} (h : sameValue u v = true) :
    (u = v ∧ ∀ b, v ≠ .num b) ∨ ∃ x y, u = .num x ∧ v = .num y ∧ numberEqual x y = true := by
  unfold sameValue at h
  split at h
  all_goals first
    | exact .inl ⟨rfl, by simp⟩
    | exact .inr ⟨_, _, rfl, rfl, h⟩
    | (simp only [beq_iff_eq] at h; subst h; exact .inl ⟨rfl, by simp⟩)
    | cases h

theorem sameValue_comm (u v : Tm) : sameValue u v = sameValue v u := by
  have one : ∀ {u v : Tm}, sameValue u v = true → sameValue v u = true := by
    intro u v h
    rcases sameValue_true h with ⟨rfl, -⟩ | ⟨x, y, rfl, rfl, hxy⟩
    · exact h
    · simpa [sameValue, numberEqual_symm] using hxy
  exact Bool.eq_iff_iff.mpr ⟨one, one⟩

private theorem nonprim_value {a : Tm} (hv : isVal a = true) (hp : isPrim a = false) :
    (∃ fs c i, a = .objAt fs c i) ∨ (∃ l, a = .arr l) ∨ ∃ f cs, a = .viewSpine f cs := by
  cases a <;> simp_all [isVal, isPrim]

/-- (E3) Strict equality is symmetric. -/
theorem strictEquals_comm (a b : Tm) : strictEquals a b = strictEquals b a := by
  unfold strictEquals
  rw [Bool.and_comm (isVal a), Bool.or_comm (isPrim a), sameValue_comm a b]
  split
  · rfl
  · split
    · rfl
    · rename_i hv hp
      simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, Bool.or_eq_true, not_or,
        Bool.not_eq_true] at hv hp
      rcases nonprim_value hv.1 hp.1 with ⟨fs, c, i, rfl⟩ | ⟨l, rfl⟩ | ⟨f, cs, rfl⟩ <;>
      rcases nonprim_value hv.2 hp.2 with ⟨fs', c', j, rfl⟩ | ⟨l', rfl⟩ | ⟨f', cs', rfl⟩ <;>
      first | rfl | exact congrArg some (Bool.eq_iff_iff.mpr ⟨fun h => beq_iff_eq.mpr (beq_iff_eq.mp h).symm,
        fun h => beq_iff_eq.mpr (beq_iff_eq.mp h).symm⟩)

/-- Two values strictly equal: a primitive the other is the same value of,
or two objects of one identity. -/
theorem strictEquals_true {u v : Tm} (h : strictEquals u v = some true) :
    (isPrim v = true ∧ sameValue u v = true) ∨ ∃ fs c i fs' c', u = .objAt fs c i ∧ v = .objAt fs' c' i := by
  unfold strictEquals at h
  split at h
  · cases h
  · split at h
    · rename_i hp
      simp only [Option.some.injEq] at h
      refine .inl ⟨?_, h⟩
      rcases sameValue_true h with ⟨rfl, -⟩ | ⟨x, y, -, rfl, -⟩
      · simpa using hp
      · rfl
    · split at h <;> simp_all

/-- **The tags of a clause** under strict equality: one of them holds of
every value strictly equal to a member of the clause. A primitive clause's
are its kind's test or its literals' equality tests; an object clause's are
`isRef` and `isFun`, since strict equality compares objects by identity alone
and every object passes one of the two, by its call code; a spine's are none,
since strict equality answers `false` or nothing of one; `top` and `source`,
which hold every value, have none to state. -/
def equalityTagsOf {α : Type} : Clause α → Option (List Tag)
  | .nul => some [.isNul]
  | .undef => some [.isUndef]
  | .bool => some [.isBool]
  | .boolLit b => some [.boolEq b]
  | .num => some [.isNum]
  | .int => some [.isNum]
  | .numLit k => some [.numEq k]
  | .numIn S => some (S.map .numEq)
  | .str => some [.isStr]
  | .strLit s => some [.strEq s]
  | .strIn S => some (S.map .strEq)
  | .bigint => some [.isBigint]
  | .bigintLit i => some [.bigintEq i]
  | .symbol => some [.isSymbol]
  | .symbolLit _ => some [.isSymbol]
  | .refs .. => some [.isRef, .isFun]
  | .dict .. => some [.isRef, .isFun]
  | .arrs .. => some [.isRef, .isFun]
  | .callable .. => some [.isRef, .isFun]
  | .ctors .. => some [.isRef, .isFun]
  | .view .. => some [.isRef, .isFun]
  | .list .. => some []
  | .pack .. => some []
  | .top => none
  | .source => none

private theorem prim_shape {v : Tm} (h : isPrim v = true) : valueShape v ∈ [0, 1, 4, 5, 6, 9, 10] := by
  cases v <;> simp_all [isPrim, valueShape]

private theorem objAt_shape (fs : List (PropKey × Nat)) (cd : CallCode) (i : Nat) :
    valueShape (.objAt fs cd i) ∈ [2, 3, 11, 13] := by
  cases cd with
  | graph _ _ _ _ _ kind _ _ => cases kind <;> simp [valueShape]
  | _ => simp [valueShape]

private theorem objAt_tags (fs : List (PropKey × Nat)) (cd : CallCode) (i : Nat) :
    ∃ t ∈ [Tag.isRef, .isFun], tagHolds t (.objAt fs cd i) = true := by
  cases cd <;> simp [tagHolds]

/-- (E1) for one clause: a value strictly equal to a member of a clause
passes one of the clause's tags. -/
theorem equalityTagsOf_sound {α : Type} {Ξ : Fam} {X : α → Fam} {P : α → ArgFam} {c : Clause α}
    {S : List Tag} {n W} {u v : Tm} (hS : equalityTagsOf c = some S) (hv : semWithArgs Ξ X P c n W v)
    (heq : strictEquals u v = some true) : ∃ t ∈ S, tagHolds t u = true := by
  by_cases htop : c = .top
  · subst htop; cases hS
  by_cases hsrc : c = .source
  · subst hsrc; cases hS
  have hsh := semWithArgs_shape htop hsrc hv
  rcases strictEquals_true heq with ⟨hp, hs⟩ | ⟨fs, cd, i, fs', c', rfl, rfl⟩
  · have hps := prim_shape hp
    rcases sameValue_true hs with ⟨rfl, hnn⟩ | ⟨x, y, rfl, rfl, hxy⟩
    · cases c <;> simp only [equalityTagsOf, Option.some.injEq] at hS <;> (first | subst hS | cases hS) <;>
        (try (rw [hsh] at hps; simp [shape] at hps; done))
      case nul => cases hv; exact ⟨.isNul, by simp, rfl⟩
      case bool => rcases hv with rfl | rfl <;> exact ⟨.isBool, by simp, rfl⟩
      case boolLit b => cases hv; exact ⟨.boolEq b, by simp, by cases b <;> rfl⟩
      case num => obtain ⟨b, rfl⟩ := hv; exact absurd rfl (hnn b)
      case numLit k => cases hv; exact absurd rfl (hnn k)
      case undef => cases hv; exact ⟨.isUndef, by simp, rfl⟩
      case str => obtain ⟨s, rfl⟩ := hv; exact ⟨.isStr, by simp, rfl⟩
      case strLit s => cases hv; exact ⟨.strEq s, by simp, by simp [tagHolds]⟩
      case bigint => obtain ⟨i, rfl⟩ := hv; exact ⟨.isBigint, by simp, rfl⟩
      case symbol => obtain ⟨i, rfl⟩ := hv; exact ⟨.isSymbol, by simp, rfl⟩
      case bigintLit i => cases hv; exact ⟨.bigintEq i, by simp, by simp [tagHolds]⟩
      case symbolLit i => cases hv; exact ⟨.isSymbol, by simp, rfl⟩
      case numIn bs => obtain ⟨b, -, rfl⟩ := hv; exact absurd rfl (hnn b)
      case strIn ss => obtain ⟨s, hs', rfl⟩ := hv; exact ⟨.strEq s, List.mem_map.mpr ⟨s, hs', rfl⟩, by simp [tagHolds]⟩
      case int => obtain ⟨b, rfl, -⟩ := hv; exact absurd rfl (hnn b)
    · cases c <;> simp only [equalityTagsOf, Option.some.injEq] at hS <;> (first | subst hS | cases hS) <;>
        (try (simp [valueShape, shape] at hsh; done))
      case num => exact ⟨.isNum, by simp, rfl⟩
      case int => exact ⟨.isNum, by simp, rfl⟩
      case numLit k => cases hv; exact ⟨.numEq y, by simp, hxy⟩
      case numIn bs => obtain ⟨b, hb, hb'⟩ := hv; cases hb'; exact ⟨.numEq y, List.mem_map.mpr ⟨y, hb, rfl⟩, hxy⟩
  · have ho := objAt_shape fs' c' i
    cases c <;> simp only [equalityTagsOf, Option.some.injEq] at hS <;> (first | subst hS | cases hS) <;>
      first
        | exact objAt_tags fs cd i
        | (rw [hsh] at ho; simp [shape] at ho)

/-- Whether a test reads the prototype chain: `key in o` alone. -/
def tagReadsProto : Tag → Bool
  | .hasKey _ => true
  | _ => false

theorem tagHoldsIn_of_readsProto {t : Tag} (ht : tagReadsProto t = false) (h : Heap) (v : Tm) :
    tagHoldsIn h t v = tagHolds t v := by
  cases t <;> first | rfl | simp [tagReadsProto] at ht

theorem equalityTagsOf_readsProto {α : Type} {c : Clause α} {S : List Tag} (hS : equalityTagsOf c = some S) :
    ∀ t ∈ S, tagReadsProto t = false := by
  cases c <;> simp only [equalityTagsOf, Option.some.injEq, reduceCtorEq] at hS <;> subst hS <;>
    simp [tagReadsProto]

/-- Two tags with the same holders: number equality tests of `Number::equal`
values, which ignores the sign of zero, or the same test. -/
def sameHolders : Tag → Tag → Bool
  | .numEq a, .numEq b => numberEqual a b
  | a, b => a == b

theorem sameHolders_holds {t t' : Tag} {u : Tm} (hs : sameHolders t t' = true)
    (ht : tagHolds t u = true) : tagHolds t' u = true := by
  unfold sameHolders at hs
  split at hs
  · cases u <;> simp only [tagHolds] at ht ⊢
    all_goals first | exact numberEqual_trans ht hs | cases ht
  · rw [beq_iff_eq] at hs; subst hs; exact ht

/-- A list of tags, one of each class of `sameHolders`: `numEq(+0)` and
`numEq(−0)` are one. -/
def dedupTags : List Tag → List Tag
  | [] => []
  | t :: ts => if (dedupTags ts).any (sameHolders t) then dedupTags ts else t :: dedupTags ts

theorem mem_dedupTags {t : Tag} : ∀ {ts : List Tag}, t ∈ dedupTags ts → t ∈ ts
  | [], h => h
  | s :: ts, h => by
    unfold dedupTags at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_dedupTags h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_dedupTags h)

theorem dedupTags_holds {u : Tm} : ∀ {ts : List Tag} {t : Tag}, t ∈ ts → tagHolds t u = true →
    ∃ t' ∈ dedupTags ts, tagHolds t' u = true
  | s :: ts, t, hm, ht => by
    unfold dedupTags
    rcases List.mem_cons.mp hm with rfl | hm
    · split
      · rename_i hany
        obtain ⟨t', ht', hs⟩ := List.any_eq_true.mp hany
        exact ⟨t', ht', sameHolders_holds hs ht⟩
      · exact ⟨t, List.mem_cons_self, ht⟩
    · obtain ⟨t', ht', h'⟩ := dedupTags_holds hm ht
      split
      · exact ⟨t', ht', h'⟩
      · exact ⟨t', List.mem_cons_of_mem _ ht', h'⟩

/-- The tags of a list of clauses: each clause's, where every clause has them. -/
def equalityTagsAll {α : Type} : List (Clause α) → Option (List Tag)
  | [] => some []
  | c :: cs => match equalityTagsOf c, equalityTagsAll cs with
    | some a, some b => some (a ++ b)
    | _, _ => none

theorem equalityTagsAll_mem {α : Type} : ∀ {cs : List (Clause α)} {S : List Tag} {c : Clause α},
    equalityTagsAll cs = some S → c ∈ cs → ∃ Sc, equalityTagsOf c = some Sc ∧ ∀ t ∈ Sc, t ∈ S
  | d :: cs, S, c, h, hc => by
    unfold equalityTagsAll at h
    split at h
    · rename_i a b ha hb
      cases h
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨a, ha, fun t ht => List.mem_append_left _ ht⟩
      · obtain ⟨Sc, hSc, hsub⟩ := equalityTagsAll_mem hb hc
        exact ⟨Sc, hSc, fun t ht => List.mem_append_right _ (hsub t ht)⟩
    · cases h

theorem equalityTagsAll_readsProto {α : Type} : ∀ {cs : List (Clause α)} {S : List Tag},
    equalityTagsAll cs = some S → ∀ t ∈ S, tagReadsProto t = false
  | [], S, h, t, ht => by cases h; cases ht
  | d :: cs, S, h, t, ht => by
    unfold equalityTagsAll at h
    split at h
    · rename_i a b ha hb
      cases h
      rcases List.mem_append.mp ht with ht | ht
      · exact equalityTagsOf_readsProto ha t ht
      · exact equalityTagsAll_readsProto hb t ht
    · cases h

/-- **The tags of a type** under strict equality: its clauses' tags, one per
class of `sameHolders`, where every label of the type is a clause row; none
otherwise, since a parameter's members are no clause's. -/
def equalityTags (G : NormalGraph ι) (B : Ty ι) : Option (List Tag) :=
  if G.plainTy B then (equalityTagsAll (expand G B)).map dedupTags else none

theorem equalityTags_readsProto {G : NormalGraph ι} {B : Ty ι} {S : List Tag}
    (hS : equalityTags G B = some S) : ∀ t ∈ S, tagReadsProto t = false := by
  unfold equalityTags at hS
  split at hS
  · obtain ⟨S', hS', rfl⟩ := Option.map_eq_some_iff.mp hS
    exact fun t ht => equalityTagsAll_readsProto hS' t (mem_dedupTags ht)
  · cases hS

/-- (E1) A value strictly equal to a member of a type passes one of the
type's tags. -/
theorem equalityTags_sound {G : NormalGraph ι} {B : Ty ι} {S : List Tag} {n W} {u v : Tm}
    (hS : equalityTags G B = some S) (hv : meaning G B n W v)
    (heq : strictEquals u v = some true) : ∃ t ∈ S, tagHolds t u = true := by
  unfold equalityTags at hS
  split at hS
  · rename_i hp
    obtain ⟨S', hS', rfl⟩ := Option.map_eq_some_iff.mp hS
    obtain ⟨c, hc, hcv, -⟩ := (expand_sem G B hp n W v).mp hv
    obtain ⟨Sc, hSc, hsub⟩ := equalityTagsAll_mem hS' hc
    obtain ⟨t, ht, hu⟩ := equalityTagsOf_sound hSc hcv heq
    exact dedupTags_holds (hsub t ht) hu
  · cases hS

/-- **The tag of a singleton type**: the equality test of the one value, up
to strict equality, every member of the type is: `null`, `undefined`, a
number (`Number::equal` relates every literal of the type to the first, so
both zeros are one), a string, a Boolean or a bigint. -/
def singletonTag (G : NormalGraph ι) (A : Ty ι) : Option Tag :=
  if !G.plainTy A then none else
  match splitSets (expand G A) with
  | [.nul] => some .isNul
  | [.undef] => some .isUndef
  | .numLit bits :: cs =>
    if cs.all (fun c => match c with | .numLit b => numberEqual bits b | _ => false)
    then some (.numEq bits) else none
  | [.strLit s] => some (.strEq s)
  | [.boolLit b] => some (.boolEq b)
  | [.bigintLit i] => some (.bigintEq i)
  | _ => none

theorem singletonTag_readsProto {G : NormalGraph ι} {A : Ty ι} {t : Tag}
    (ht : singletonTag G A = some t) : tagReadsProto t = false := by
  unfold singletonTag at ht
  split at ht
  · cases ht
  · split at ht <;> (try split at ht) <;> first | (cases ht; rfl) | cases ht

/-- (E2) A value strictly unequal to a member of a singleton type fails the
type's tag. -/
theorem singletonTag_sound {G : NormalGraph ι} {B : Ty ι} {t : Tag} {n W} {u v : Tm}
    (ht : singletonTag G B = some t) (hv : meaning G B n W v)
    (hne : strictEquals u v = some false) : tagHolds t u = false := by
  unfold singletonTag at ht
  split at ht
  · cases ht
  rename_i hp
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hp
  obtain ⟨c, hc, hcv, -⟩ := (expand_sem G B hp n W v).mp hv
  obtain ⟨e, he, hev⟩ := (elements_sem _ _ _ c n W v).mpr hcv
  have hmem : e ∈ splitSets (expand G B) := List.mem_flatMap.mpr ⟨c, hc, he⟩
  cases hu : tagHolds t u
  · rfl
  exfalso
  revert hne
  split at ht
  · rename_i hs; rw [hs] at hmem; cases ht
    simp at hmem; subst hmem; cases hev
    cases u <;> simp [tagHolds] at hu; simp [strictEquals, isVal, isPrim, sameValue]
  · rename_i hs; rw [hs] at hmem; cases ht
    simp at hmem; subst hmem; cases hev
    cases u <;> simp [tagHolds] at hu; simp [strictEquals, isVal, isPrim, sameValue]
  · rename_i bits cs hs; rw [hs] at hmem
    split at ht
    · rename_i hall
      cases ht
      cases u <;> simp only [tagHolds, reduceCtorEq] at hu
      rename_i x
      have hb : ∃ b, v = .num b ∧ numberEqual bits b = true := by
        rcases List.mem_cons.mp hmem with rfl | hm
        · cases hev; refine ⟨bits, rfl, ?_⟩
          simp only [numberEqual, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hu ⊢
          simp_all
        · have := List.all_eq_true.mp hall e hm
          cases e <;> simp only [reduceCtorEq] at this
          cases hev; exact ⟨_, rfl, this⟩
      obtain ⟨b, rfl, hb⟩ := hb
      simp [strictEquals, isVal, isPrim, sameValue, numberEqual_trans hu hb]
    · cases ht
  · rename_i s hs; rw [hs] at hmem; cases ht
    simp at hmem; subst hmem; cases hev
    cases u <;> simp [tagHolds] at hu; subst hu; simp [strictEquals, isVal, isPrim, sameValue]
  · rename_i b hs; rw [hs] at hmem; cases ht
    simp at hmem; subst hmem; cases hev
    cases b <;> cases u <;> simp [tagHolds] at hu <;> simp [strictEquals, isVal, isPrim, sameValue]
  · rename_i i hs; rw [hs] at hmem; cases ht
    simp at hmem; subst hmem; cases hev
    cases u <;> simp [tagHolds] at hu; subst hu; simp [strictEquals, isVal, isPrim, sameValue]
  · cases ht

end EqualityTags

variable [DecidableEq ι]

/-- A target implication follows on an edge mapping `m`: one the source
states, at the slots the mapping reads, at a type within the target's; the
source's own type of the target slot, within it; or none at all, where the
source's tested slot never holds `true`. -/
def impliesFollows (G : NormalGraph ι) (Γ : List (Ty ι)) (xs : List (Implication ι))
    (m : PointClaims.Mapping) (x : Implication ι) : Bool :=
  xs.any (fun y => y.test == PointClaims.slot m x.test && y.target == PointClaims.slot m x.target &&
    within y.type x.type) ||
  (Γ[PointClaims.slot m x.target]?).any (fun A => within A x.type) ||
  (Γ[PointClaims.slot m x.test]?).any (fun A => impossible G A (.boolean true))

/-- `impliesFollows` as the compiled verifier runs it (`impliesFollows_eq_fast`):
the mapped test and target slots read once. -/
def impliesFollowsFast (G : NormalGraph ι) (Γ : List (Ty ι)) (xs : List (Implication ι))
    (m : PointClaims.Mapping) (x : Implication ι) : Bool :=
  let test := PointClaims.slot m x.test
  let target := PointClaims.slot m x.target
  xs.any (fun y => y.test == test && y.target == target && within y.type x.type) ||
  (Γ[target]?).any (fun A => within A x.type) ||
  (Γ[test]?).any (fun A => impossible G A (.boolean true))

@[csimp] theorem impliesFollows_eq_fast : @impliesFollows = @impliesFollowsFast := rfl

def impliesCheck (G : NormalGraph ι) (Γ : List (Ty ι)) (xs : List (Implication ι))
    (m : PointClaims.Mapping) (targets : List (Implication ι)) : Bool :=
  targets.all (impliesFollows G Γ xs m)

theorem impliesCheck_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {xs m targets ρ n W}
    (hc : impliesCheck G Γ xs m targets = true) (he : EnvOk G Γ ρ n W) (hx : ImpliesOk G xs ρ n W) :
    ImpliesOk G targets (PointClaims.mapEnv m ρ) n W := by
  intro x hm ht
  have hf := List.all_eq_true.mp hc x hm
  change ρ (PointClaims.slot m x.test) = .tru at ht
  change meaning G x.type n W (ρ (PointClaims.slot m x.target))
  simp only [impliesFollows, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    Option.any_eq_true] at hf
  rcases hf with (⟨y, hy, ⟨htest, htarget⟩, hw⟩ | ⟨A, hA, hw⟩) | ⟨A, hA, himp⟩
  · rw [← htarget]
    exact meaning_within hw (hx y hy (htest ▸ ht))
  · exact meaning_within hw (he.2 _ A hA)
  · exact (impossible_sound himp (he.2 _ A hA) (show Observation.holds (.boolean true) _ from ht)).elim

/-- The slots of a state's environment holding the promised argument. -/
def ArgumentsOk (sources : List Nat) (ρ : Env) (v0 : Tm) : Prop := ∀ p ∈ sources, ρ p = v0

/-- A target's argument slots are ones the mapping reads from source slots
holding it. -/
def argFollows (sources : List Nat) (m : PointClaims.Mapping) (targets : List Nat) : Bool :=
  targets.all fun p => sources.contains (PointClaims.slot m p)

theorem argFollows_sound {sources m targets ρ v0} (hc : argFollows sources m targets = true)
    (hs : ArgumentsOk sources ρ v0) : ArgumentsOk targets (PointClaims.mapEnv m ρ) v0 := by
  intro p hp
  exact hs _ (List.contains_iff_mem.mp (List.all_eq_true.mp hc p hp))

/-! ### Slots holding one value

An alias link of the heap knowledge relates two slots holding the same value
(`HeapLinks.Holds`): an implication about one is about the other, and the
promised argument in one is in the other. -/

/-- The slots alias links relate, both ways. -/
def aliasPairs (links : HeapLinks.Links) : List (Nat × Nat) :=
  links.flatMap fun g => if g.alias then [(g.cell, g.value), (g.value, g.cell)] else []

theorem aliasPairs_holds {links : HeapLinks.Links} {ρ h} (hl : HeapLinks.Holds links ρ h) :
    ∀ q ∈ aliasPairs links, ρ q.1 = ρ q.2 := by
  intro q hq
  obtain ⟨g, hg, hq⟩ := List.mem_flatMap.mp hq
  have hh := hl g hg
  split at hq
  · rename_i hc
    simp only [hc, ↓reduceIte] at hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hh
    · exact hh.symm
  · cases hq

/-- The slots holding a slot's value by alias links, the slot included: the
set `known` grown by every partner of its members, `fuel` times. -/
def aliasesOf (pairs : List (Nat × Nat)) : Nat → List Nat → List Nat
  | 0, known => known
  | fuel + 1, known =>
    let grown := (known ++ pairs.filterMap fun q => if known.contains q.1 then some q.2 else none).eraseDups
    if grown.length == known.length then known else aliasesOf pairs fuel grown

theorem aliasesOf_holds {pairs : List (Nat × Nat)} {ρ : Env} {v : Tm} (hp : ∀ q ∈ pairs, ρ q.1 = ρ q.2) :
    ∀ fuel known, (∀ j ∈ known, ρ j = v) → ∀ j ∈ aliasesOf pairs fuel known, ρ j = v := by
  intro fuel
  induction fuel with
  | zero => intro known hk j hj; exact hk j hj
  | succ fuel ih =>
    intro known hk j hj
    simp only [aliasesOf] at hj
    split at hj
    · exact hk j hj
    · refine ih _ (fun k hk' => ?_) j hj
      rcases List.mem_append.mp (List.mem_eraseDups.mp hk') with hk' | hk'
      · exact hk k hk'
      · obtain ⟨q, hq, he⟩ := List.mem_filterMap.mp hk'
        split at he
        · rename_i hc
          cases he
          rw [← hp q hq]
          exact hk q.1 (List.contains_iff_mem.mp hc)
        · cases he

/-- Implications and argument slots at every slot the links say holds the
same value. -/
def aliasImplications (links : HeapLinks.Links) (xs : List (Implication ι)) : List (Implication ι) :=
  let pairs := aliasPairs links
  (xs.flatMap fun x => (aliasesOf pairs pairs.length [x.test]).flatMap fun t =>
    (aliasesOf pairs pairs.length [x.target]).map fun a => ⟨t, a, x.type⟩).eraseDups

def aliasSources (links : HeapLinks.Links) (sources : List Nat) : List Nat :=
  let pairs := aliasPairs links
  aliasesOf pairs pairs.length sources.eraseDups

theorem aliasImplications_holds {links : HeapLinks.Links} {xs : List (Implication ι)} {ρ h n W G}
    (hl : HeapLinks.Holds links ρ h) (hx : ImpliesOk G xs ρ n W) :
    ImpliesOk G (aliasImplications links xs) ρ n W := by
  intro y hy ht
  simp only [aliasImplications] at hy
  obtain ⟨x, hx', hy⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hy)
  obtain ⟨t, htm, hy⟩ := List.mem_flatMap.mp hy
  obtain ⟨a, ham, rfl⟩ := List.mem_map.mp hy
  have hpairs := aliasPairs_holds hl
  have ht' := aliasesOf_holds (v := ρ x.test) hpairs _ _ (by simp) t htm
  have ha' := aliasesOf_holds (v := ρ x.target) hpairs _ _ (by simp) a ham
  change ρ t = .tru at ht
  change meaning G x.type n W (ρ a)
  rw [ha']
  exact hx x hx' (by rw [← ht', ht])

theorem aliasSources_holds {links : HeapLinks.Links} {sources : List Nat} {ρ h v0}
    (hl : HeapLinks.Holds links ρ h) (hs : ArgumentsOk sources ρ v0) :
    ArgumentsOk (aliasSources links sources) ρ v0 := by
  intro p hp
  simp only [aliasSources] at hp
  exact aliasesOf_holds (aliasPairs_holds hl) _ _ (fun j hj => hs j (List.mem_eraseDups.mp hj)) p hp

/-! ### Implications compared by their slots

`impliesCheck` compares each target implication with every source one. The
compiled checker reads the source implications by their tested and target
slots instead (`impliesCheckIndexed`), each repeated one once or more: the
same answer (`impliesCheck_eq_indexed`). -/

/-- `aliasImplications` with each implication as often as the aliases give it. -/
def aliasImplicationsAll (links : HeapLinks.Links) (xs : List (Implication ι)) : List (Implication ι) :=
  let pairs := aliasPairs links
  xs.flatMap fun x => (aliasesOf pairs pairs.length [x.test]).flatMap fun t =>
    (aliasesOf pairs pairs.length [x.target]).map fun a => ⟨t, a, x.type⟩

/-- The types the implications `xs` state at each tested and target slot. -/
def implicationIndex (xs : List (Implication ι)) : Std.HashMap (Nat × Nat) (List (Ty ι)) :=
  xs.foldl (fun m y => m.insert (y.test, y.target) (y.type :: m.getD (y.test, y.target) [])) {}

omit [DecidableEq ι] in
theorem implicationIndex_any_foldl (P : Ty ι → Bool) (k : Nat × Nat) :
    ∀ (xs : List (Implication ι)) (m : Std.HashMap (Nat × Nat) (List (Ty ι))),
      ((xs.foldl (fun m y => m.insert (y.test, y.target) (y.type :: m.getD (y.test, y.target) [])) m).getD
          k []).any P =
        ((m.getD k []).any P || xs.any fun y => (y.test, y.target) == k && P y.type)
  | [], m => by simp
  | y :: ys, m => by
    rw [List.foldl_cons, implicationIndex_any_foldl P k ys, Std.HashMap.getD_insert]
    by_cases h : (y.test, y.target) = k
    · subst h
      simp only [beq_self_eq_true, ↓reduceIte, List.any_cons, Bool.true_and]
      cases P y.type <;> simp
    · have h' : ((y.test, y.target) == k) = false := by simpa using h
      simp only [h', Bool.false_eq_true, ↓reduceIte, List.any_cons, Bool.false_and, Bool.false_or]

omit [DecidableEq ι] in
theorem implicationIndex_any (P : Ty ι → Bool) (xs : List (Implication ι)) (a b : Nat) :
    ((implicationIndex xs).getD (a, b) []).any P = xs.any fun y => y.test == a && y.target == b && P y.type := by
  rw [implicationIndex, implicationIndex_any_foldl]
  simp only [Std.HashMap.getD_empty, List.any_nil, Bool.false_or]
  congr 1

/-- `impliesFollows`, the source implications read by their slots. -/
def impliesFollowsIndexed (G : NormalGraph ι) (Γ : List (Ty ι)) (index : Std.HashMap (Nat × Nat) (List (Ty ι)))
    (m : PointClaims.Mapping) (x : Implication ι) : Bool :=
  ((index.getD (PointClaims.slot m x.test, PointClaims.slot m x.target) []).any fun A => within A x.type) ||
  (Γ[PointClaims.slot m x.target]?).any (fun A => within A x.type) ||
  (Γ[PointClaims.slot m x.test]?).any (fun A => impossible G A (.boolean true))

/-- `impliesCheck` at a link's aliases, the source implications read by
their slots. -/
def impliesCheckIndexed (G : NormalGraph ι) (Γ : List (Ty ι)) (links : HeapLinks.Links)
    (xs : List (Implication ι)) (m : PointClaims.Mapping) (targets : List (Implication ι)) : Bool :=
  let index := implicationIndex (aliasImplicationsAll links xs)
  targets.all (impliesFollowsIndexed G Γ index m)

theorem impliesCheck_eq_indexed (G : NormalGraph ι) (Γ : List (Ty ι)) (links : HeapLinks.Links)
    (xs : List (Implication ι)) (m : PointClaims.Mapping) (targets : List (Implication ι)) :
    impliesCheck G Γ (aliasImplications links xs) m targets = impliesCheckIndexed G Γ links xs m targets := by
  simp only [impliesCheck, impliesCheckIndexed]
  congr 1
  funext x
  simp only [impliesFollows, impliesFollowsIndexed, implicationIndex_any]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, aliasImplications, List.mem_eraseDups, aliasImplicationsAll]

/-- Facts about slots past `shift`, at every slot the links say holds the
same value: what refining a context by them may state. -/
def aliasFacts (links : HeapLinks.Links) (facts : List (Nat × Ty ι)) (shift : Nat) : List (Nat × Ty ι) :=
  let pairs := aliasPairs links
  facts.flatMap fun f => (aliasesOf pairs pairs.length [f.1 + shift]).map (·, f.2)

omit [DecidableEq ι] in
theorem aliasFacts_holds {G : NormalGraph ι} {links : HeapLinks.Links} {facts : List (Nat × Ty ι)}
    {shift : Nat} {ρ h n W} (hl : HeapLinks.Holds links ρ h)
    (hf : ∀ f ∈ facts, meaning G f.2 n W (ρ (f.1 + shift))) :
    ∀ f ∈ aliasFacts links facts shift, meaning G f.2 n W (ρ (f.1 + 0)) := by
  intro f hm
  obtain ⟨g, hg, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
  rw [Nat.add_zero, aliasesOf_holds (v := ρ (g.1 + shift)) (aliasPairs_holds hl) _ _ (by simp) k hk]
  exact hf g hg

/-! ### Yields of a slot read and of a tag test -/

/-- A tag test's yield about the object the tested value was read from: a
current read link says field `f` of the object in `y.target` holds the tested
slot's value, and the object's arms whose field answers the test so
(`fieldSlice`) are within the yield's type, by the yield's evidence. -/
@[nospecialize] def fieldYield (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι))
    (links : HeapLinks.Links) (y : Yield ι) (i : Nat) (tag : Tag) (q : Bool) : Bool :=
  (Γ[i]?).isSome &&
  links.any fun g => !g.alias && !g.optional && g.value == i && g.cell == y.target &&
    match Γ[g.cell]?, y.evidence with
    | some A, some p => PositiveCertificates.checkUsing G images (fieldSlice G A g.field tag q) y.type p
    | _, _ => false

theorem fieldYield_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ links y i tag q}
    (hf : fieldYield G images Γ links y i tag q = true) {ρ m W h}
    (he : EnvOk G Γ ρ (m+1) W) (hh : HeapOk (m+1) W h) (hl : HeapLinks.Holds links ρ h)
    (htag : tagHoldsIn h tag (ρ i) = q) : meaning G y.type (m+1) W (ρ y.target) := by
  unfold fieldYield at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨g, hg, hc⟩ := List.any_eq_true.mp hf.2
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨ha, ho⟩, hv⟩, hcell⟩, hp⟩ := hc
  split at hp
  · rename_i A p hA _
    have hlink := hl g hg
    simp only [ha, ho, Bool.false_eq_true, ite_false] at hlink
    obtain ⟨flds, c, oid, l, hobj, hlk, hu⟩ := hlink
    have hs := fieldSlice_sound (he.2 g.cell A hA) hh hobj hlk hu
      (tagHolds_of_heap (hv ▸ htag))
    rw [← hcell]
    exact PositiveCertificates.acceptedUsing hp _ _ _ hs
  · cases hp

/-! ### Yields of a membership test -/

/-- The test of a value against a finite list of tags, in order: `true`
where one of them holds of it, else `false` (`member_run`). -/
def memberOn (tags : List Tag) (x : Tm) : Tm :=
  tags.foldr (fun t rest => .ite (.test t x) .tru rest) .fls

/-- The tags and the slot of a membership test of a slot's value, of one tag
or more. -/
def memberParts : Tm → Option (List Tag × Nat)
  | .ite (.test t (.var i)) .tru rest =>
    match rest with
    | .fls => some ([t], i)
    | _ => match memberParts rest with
      | some (ts, j) => if i == j then some (t :: ts, i) else none
      | none => none
  | _ => none

/-- Whether a term is the membership test of the slot `i`'s value against
the tags `ts`, in order (`memberOn`). -/
def isMemberOn : List Tag → Nat → Tm → Bool
  | [], _, .fls => true
  | t :: ts, i, .ite (.test t' (.var j)) .tru rest => t == t' && i == j && isMemberOn ts i rest
  | _, _, _ => false

theorem isMemberOn_sound : ∀ {ts : List Tag} {i : Nat} {t : Tm}, isMemberOn ts i t = true →
    t = memberOn ts (.var i) := by
  intro ts
  induction ts with
  | nil =>
    intro i t h
    unfold isMemberOn at h
    split at h <;> first | rfl | simp_all
  | cons t ts ih =>
    intro i e h
    unfold isMemberOn at h
    split at h
    · simp_all
    · rename_i t' j rest heq
      simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, h⟩ := h
      rw [ih h]
      rfl
    · simp_all

/-- What a membership test's answer `q` leaves of a type, by a slice of one
tag: where it answered `true`, the labels one tag's passing slice keeps;
where `false`, those every tag's failing slice keeps, one after another. -/
def memberSlice (slice : Ty ι → Tag → Bool → Ty ι) (A : Ty ι) (ts : List Tag) (q : Bool) : Ty ι :=
  if q then (ts.flatMap fun t => slice A t true).eraseDups else ts.foldl (fun B t => slice B t false) A

/-- What a membership test's answer `q` leaves of a slot's type: by each tag's
slice (`memberSlice`), and where it answered `false`, less the labels the
whole set covers (`uncovered`, PROGRAM-TYPING.md, "A membership test"). -/
def memberSlotSlice (G : NormalGraph ι) (A : Ty ι) (ts : List Tag) (q : Bool) : Ty ι :=
  if q then memberSlice (tagSlice G) A ts true
  else BranchRefinement.uncovered G (memberSlice (tagSlice G) A ts false) ts

/-- What a membership test's answer `q` of an object's field `f` leaves of
the object's type: by each tag's field slice, and where it answered `false`,
less the arms the whole set covers and with an arm partly covered at a stable
key read as a label of `candidates` (`uncoveredField`, member-split). -/
def memberFieldSlice (G : NormalGraph ι) (A : Ty ι) (f : PropKey) (ts : List Tag) (q : Bool)
    (candidates : Ty ι) : Ty ι :=
  if q then memberSlice (fun B t q => fieldSlice G B f t q) A ts true
  else BranchRefinement.uncoveredField G (memberSlice (fun B t q => fieldSlice G B f t q) A ts false) f ts candidates

/-- `memberFieldSlice` as a check reads it: the function, or the function's
values at the keys a check meets, read from a table (`FieldSlices.eq_direct`). -/
structure FieldSlices (G : NormalGraph ι) where
  slice : Ty ι → PropKey → List Tag → Bool → Ty ι → Ty ι
  slice_eq : slice = memberFieldSlice G

@[nospecialize] def FieldSlices.direct (G : NormalGraph ι) : FieldSlices G := ⟨memberFieldSlice G, rfl⟩

theorem FieldSlices.eq_direct {G : NormalGraph ι} (s : FieldSlices G) : s = FieldSlices.direct G := by
  cases s with
  | mk f h => subst h; rfl

/-- What a tag test's answer `q` leaves of slot `i`'s type is within the
yield's type, by the yield's evidence (`ObservedSub`): the single-tag rule,
which narrows a family to the singleton it is tested against. -/
@[nospecialize] def observedTag (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι))
    (y : Yield ι) (i : Nat) (tag : Tag) (q : Bool) : Bool :=
  match Γ[i]?, y.evidence with
  | some A, some p => checkObservedSubUsing G images A y.type (.tag tag q) p
  | _, _ => false

/-- A membership test's yield (`memberOn`) about the tested slot, or about
the object a current read link says its value was read from: where the test
answered `q`, the labels `memberSlice` keeps of the slot's or the object's
type are within the yield's type, by the yield's evidence. Where it answered
`true`, also where each tag's own rule gives the yield's type, of the slot
(`observedTag`) or of the object (`fieldYield`): whichever tag holds gives
it. A yield of `true` is conditional; one of `false` is stated of that answer
(`onFalse`). -/
@[nospecialize] def memberYield (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι))
    (links : HeapLinks.Links) (y : Yield ι) (ts : List Tag) (i : Nat)
    (slices : FieldSlices G := FieldSlices.direct G) : Bool :=
  y.conditional == !y.onFalse && (Γ[i]?).isSome &&
  ((match y.evidence with
  | none => false
  | some p =>
    (y.target == i && match Γ[i]? with
      | some A => PositiveCertificates.checkUsing G images (memberSlotSlice G A ts !y.onFalse) y.type p
      | none => false) ||
    links.any fun g => !g.alias && !g.optional && g.value == i && g.cell == y.target &&
      match Γ[g.cell]? with
      | some A => PositiveCertificates.checkUsing G images
          (slices.slice A g.field ts (!y.onFalse) y.type) y.type p
      | none => false) ||
  (!y.onFalse && ts.all fun t =>
    y.target == i && observedTag G images Γ y i t true || fieldYield G images Γ links y i t true))

/-- Whether a yield follows from a node's membership test (`memberYield`). -/
@[nospecialize] def memberFollows (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι))
    (links : HeapLinks.Links) (t : Tm) (y : Yield ι) (slices : FieldSlices G := FieldSlices.direct G) : Bool :=
  match memberParts t with
  | some (ts, i) => isMemberOn ts i t && memberYield G images Γ links y ts i slices
  | none => false

/-- **A strict comparison's yield** (`x_a === x_b`) about slot `a`, or about
the object a current read link says its value was read from: that of a
membership test of `a` against the tags of `b`'s type (`equalityTags`) where
it answered `true`, and against the tag of `b`'s singleton type
(`singletonTag`) where it answered `false` (PROGRAM-TYPING.md, "A strict
comparison"). -/
@[nospecialize] def comparisonYield (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι))
    (links : HeapLinks.Links) (y : Yield ι) (a b : Nat) (slices : FieldSlices G := FieldSlices.direct G) : Bool :=
  match Γ[b]? with
  | some B => (if y.onFalse then (singletonTag G B).map ([·]) else equalityTags G B).any
      fun ts => memberYield G images Γ links y ts a slices
  | none => false

/-- One yield of a node's expression, without a call: a slot read, whose value
is the slot's, yields what an implication on the slot states; a tag test of a
slot, read as a Boolean, yields where it answers `true` what its observation
leaves of the slot, or of the object the slot's value was read from
(`fieldYield`); a strict comparison of two slots yields what a membership
test of either does (`comparisonYield`). -/
@[nospecialize] def yieldFollows (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι))
    (xs : List (Implication ι)) (links : HeapLinks.Links) (t : Tm)
    (slices : FieldSlices G := FieldSlices.direct G) (y : Yield ι) : Bool :=
  memberFollows G images Γ links t y slices || match t with
  | .var i => y.conditional && (Γ[i]?).isSome &&
      xs.any fun x => x.test == i && x.target == y.target && within x.type y.type
  | .ite (.test tag (.var i)) .tru .fls => y.conditional &&
      (y.target == i && observedTag G images Γ y i tag true || fieldYield G images Γ links y i tag true)
  | .ite (.test tag (.var i)) .fls .tru => y.conditional &&
      (y.target == i && observedTag G images Γ y i tag false || fieldYield G images Γ links y i tag false)
  | .arith .eq (.var i) (.var j) =>
      comparisonYield G images Γ links y i j slices || comparisonYield G images Γ links y j i slices
  | _ => false

/-- A safe run, strengthened by a property of every value it returns at a
world reached from its own: the property holds of the values the run's own
derivation reaches. -/
theorem conj_reached {T : Fam} {Q : Post} {P : (k : Nat) → WorldT k → Tm → Prop} :
    ∀ {n W h t}, SafePost Ξ T Q n W h t →
      (∀ k (hk : k ≤ n) (U : WorldT k), WExt (trunc k hk W) U → ∀ m h' u,
        Steps m h t h' u → isVal u = true → P k U u) →
      SafePost Ξ (fun k U u => T k U u ∧ P k U u) Q n W h t := by
  intro n
  induction n with
  | zero => intros; assumption
  | succ n ih =>
    intro W h t hs hp
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, ht, hq⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, ⟨ht, hp (n+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) 0 h t
        .refl hv⟩, hq⟩)
    · exact .inl (.inr hth)
    · refine .inr ⟨U, h', t', hx, hu, step, hh, ih hs fun k hk V hV m h'' u run hval => ?_⟩
      apply hp k (by omega) V _ (m+1) h'' u (.next step run) hval
      have he := WExt_trunc hk hx
      rw [trunc_trunc] at he
      exact WExt_trans he hV

/-- A tag test read as a Boolean returns at once, in its heap. -/
theorem test_ite_run {h tag v h' u m} {yes no : Tm} (hv : isVal v = true)
    (hyes : isVal yes = true) (hno : isVal no = true)
    (run : Steps m h (.ite (.test tag v) yes no) h' u) (hu : isVal u = true) :
    u = (if tagHoldsIn h tag v then yes else no) := by
  cases run with
  | refl => simp [isVal] at hu
  | next st run =>
    cases st with
    | iteC st =>
      cases st with
      | testC st => exact absurd st (value_no_step hv)
      | testV _ =>
        cases run with
        | refl => split at hu <;> simp [isVal] at hu
        | next st run =>
          split at st
          · cases st with
            | iteC st => exact absurd st (value_no_step rfl)
            | iteT => cases run with
              | refl => simp_all
              | next st _ => exact absurd st (value_no_step hyes)
          · cases st with
            | iteC st => exact absurd st (value_no_step rfl)
            | iteF => cases run with
              | refl => simp_all
              | next st _ => exact absurd st (value_no_step hno)

theorem steps_value {h v h' u m} (hv : isVal v = true) (run : Steps m h v h' u) : u = v := by
  cases run with
  | refl => rfl
  | next st _ => exact absurd st (value_no_step hv)

/-- (E4) A strict comparison of two values returns at once, in its heap, the
Boolean `strictEquals` answers. -/
theorem eq_run {h v w h' u m} (hv : isVal v = true) (hw : isVal w = true)
    (run : Steps m h (.arith .eq v w) h' u) (hu : isVal u = true) :
    h' = h ∧ ∃ q, strictEquals v w = some q ∧ u = boolVal q := by
  cases run with
  | refl => simp [isVal] at hu
  | next st run =>
    cases st with
    | arithC1 s => exact absurd s (value_no_step hv)
    | arithC2 _ s => exact absurd s (value_no_step hw)
    | arithV hb =>
      simp only [binop, ↓reduceIte, Option.map_eq_some_iff] at hb
      obtain ⟨q, hq, rfl⟩ := hb
      cases run with
      | refl => exact ⟨rfl, q, hq, rfl⟩
      | next st _ => exact absurd st (value_no_step (by cases q <;> rfl))
    | arithThrow ht => simp [binopThrows] at ht

theorem instantiate_memberOn (ρ : Env) (i : Nat) :
    ∀ ts : List Tag, instantiate 0 ρ (memberOn ts (.var i)) = memberOn ts (ρ i)
  | [] => rfl
  | t :: ts => by
    simp only [memberOn, List.foldr_cons] at *
    have := instantiate_memberOn ρ i ts
    simp only [memberOn] at this
    simp [instantiate, this]

/-- A membership test of a value returns at once, in its heap: `true` where
one of its tags holds of the value there, `false` where none does. -/
theorem member_run {h : Heap} {v : Tm} (hv : isVal v = true) : ∀ {ts : List Tag} {m h' u},
    Steps m h (memberOn ts v) h' u → isVal u = true →
    (u = .tru ∧ ∃ t ∈ ts, tagHoldsIn h t v = true) ∨ (u = .fls ∧ ∀ t ∈ ts, tagHoldsIn h t v = false)
  | [], _, _, _, run, _ => by
    have := steps_value (v := .fls) rfl run
    exact .inr ⟨this, by simp⟩
  | t :: ts, _, _, _, run, hu => by
    simp only [memberOn, List.foldr_cons] at run
    cases run with
    | refl => simp [isVal] at hu
    | next st run =>
      cases st with
      | iteC st =>
        cases st with
        | testC st => exact absurd st (value_no_step hv)
        | testV _ =>
          cases run with
          | refl => split at hu <;> simp [isVal] at hu
          | next st run =>
            split at st
            · rename_i hq
              cases st with
              | iteC st => exact absurd st (value_no_step rfl)
              | iteT => exact .inl ⟨steps_value rfl run, t, by simp, hq⟩
            · rename_i hq
              cases st with
              | iteC st => exact absurd st (value_no_step rfl)
              | iteF =>
                rcases member_run hv (ts := ts) run hu with ⟨hu', t', ht', hq'⟩ | ⟨hu', hall⟩
                · exact .inl ⟨hu', t', by simp [ht'], hq'⟩
                · refine .inr ⟨hu', fun t' ht' => ?_⟩
                  rcases List.mem_cons.mp ht' with rfl | ht'
                  · simpa using hq
                  · exact hall t' ht'

omit [DecidableEq ι] in
theorem memberSlice_sound [DecidableEq ι] {slice : Ty ι → Tag → Bool → Ty ι} {M : Ty ι → Prop}
    {Q : Tag → Bool → Prop} (hmono : ∀ {A B : Ty ι}, (∀ a ∈ A, a ∈ B) → M A → M B)
    (hs : ∀ {B t q}, M B → Q t q → M (slice B t q)) {q : Bool} :
    ∀ {A : Ty ι} {ts : List Tag}, M A →
      (q = true → ∃ t ∈ ts, Q t true) → (q = false → ∀ t ∈ ts, Q t false) → M (memberSlice slice A ts q) := by
  intro A ts hA hyes hno
  cases q with
  | true =>
    obtain ⟨t, ht, hQ⟩ := hyes rfl
    simp only [memberSlice, ↓reduceIte]
    exact hmono (fun a ha => List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨t, ht, ha⟩)) (hs hA hQ)
  | false =>
    have hall := hno rfl
    simp only [memberSlice, Bool.false_eq_true, ↓reduceIte]
    clear hyes hno
    induction ts generalizing A with
    | nil => exact hA
    | cons t ts ih =>
      simp only [List.foldl_cons]
      exact ih (hs hA (hall t (by simp))) (fun t' ht' => hall t' (by simp [ht']))

theorem memberYield_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ links y ts i}
    (hf : memberYield G images Γ links y ts i = true) {ρ m W h} {u : Tm}
    (he : EnvOk G Γ ρ (m+1) W) (hh : HeapOk (m+1) W h) (hl : HeapLinks.Holds links ρ h)
    (hrun : (u = .tru ∧ ∃ t ∈ ts, tagHoldsIn h t (ρ i) = true) ∨ (u = .fls ∧ ∀ t ∈ ts, tagHoldsIn h t (ρ i) = false))
    (hcond : y.conditional = true → u = .tru) (hneg : y.onFalse = true → u = .fls) :
    meaning G y.type (m+1) W (ρ y.target) := by
  unfold memberYield at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨hq, -⟩, hp⟩ := hf
  -- The answer the yield is about, and what the run says of it.
  have hyes : (!y.onFalse) = true → ∃ t ∈ ts, tagHoldsIn h t (ρ i) = true := by
    intro ho
    have hu : u = .tru := hcond (by rw [hq]; exact ho)
    rcases hrun with ⟨_, h1⟩ | ⟨hf', _⟩
    · exact h1
    · rw [hu] at hf'; cases hf'
  have hno : (!y.onFalse) = false → ∀ t ∈ ts, tagHoldsIn h t (ρ i) = false := by
    intro ho
    have hu : u = .fls := hneg (by simpa using ho)
    rcases hrun with ⟨ht', _⟩ | ⟨_, h1⟩
    · rw [hu] at ht'; cases ht'
    · exact h1
  rw [Bool.or_eq_true] at hp
  rcases hp with hp | hnew
  rotate_left
  · -- Each tag's own rule: the tag that holds gives the yield's type.
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true,
      Bool.or_eq_true, beq_iff_eq] at hnew
    obtain ⟨hon, hall⟩ := hnew
    obtain ⟨t, ht, htag⟩ := hyes (by simp [hon])
    rcases hall t ht with ⟨rfl, hob⟩ | hfy
    · unfold observedTag at hob
      split at hob
      · rename_i A p hA _
        exact checkObservedSub_sound hob (m+1) W _ (he.2 _ A hA) (tagHolds_of_heap htag)
      · cases hob
    · exact fieldYield_sound hfy he hh hl htag
  split at hp
  · cases hp
  · rename_i p _
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    rcases hp with ⟨rfl, hc⟩ | hc
    · split at hc
      · rename_i A hA
        have hs := memberSlice_sound (slice := tagSlice G) (M := fun B => meaning G B (m+1) W (ρ y.target))
          (Q := fun t q => tagHolds t (ρ y.target) = q ∨ protoFree t (ρ y.target) = false)
          (fun hsub ⟨a, ha, hv⟩ => ⟨a, hsub a ha, hv⟩) (fun hB hQ => tagSlice_sound hB hQ)
          (q := !y.onFalse) (ts := ts) (he.2 _ A hA)
          (fun ho => (hyes ho).imp fun t ⟨ht, hq'⟩ => ⟨ht, tagHolds_of_heap hq'⟩)
          (fun ho t ht => tagHolds_of_heap (hno ho t ht))
        -- Where every tag answered `false`, a covered label holds no value.
        have hs' : meaning G (memberSlotSlice G A ts !y.onFalse) (m+1) W (ρ y.target) := by
          unfold memberSlotSlice
          cases hq : (!y.onFalse)
          · rw [hq] at hs
            exact BranchRefinement.uncovered_sound hs (fun t ht => tagHolds_of_heap (hno hq t ht))
          · rw [hq] at hs
            exact hs
        exact PositiveCertificates.acceptedUsing hc _ _ _ hs'
      · cases hc
    · obtain ⟨g, hg, hc⟩ := List.any_eq_true.mp hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨ha, ho⟩, hv⟩, hcell⟩, hp'⟩ := hc
      split at hp'
      · rename_i A hA
        have hlink := hl g hg
        simp only [ha, ho, Bool.false_eq_true, ite_false] at hlink
        obtain ⟨flds, c, oid, l, hobj, hlk, hu⟩ := hlink
        have hs := memberSlice_sound (slice := fun B t q => fieldSlice G B g.field t q)
          (M := fun B => meaning G B (m+1) W (ρ g.cell))
          (Q := fun t q => tagHolds t (ρ g.value) = q ∨ protoFree t (ρ g.value) = false)
          (fun hsub ⟨a, ha, hv⟩ => ⟨a, hsub a ha, hv⟩) (fun hB hQ => fieldSlice_sound hB hh hobj hlk hu hQ)
          (q := !y.onFalse) (ts := ts) (he.2 _ A hA)
          (fun ho => (hyes ho).imp fun t ⟨ht, hq'⟩ => ⟨ht, tagHolds_of_heap (hv ▸ hq')⟩)
          (fun ho t ht => tagHolds_of_heap (hv ▸ hno ho t ht))
        -- Where every tag answered `false`, an arm the set covers holds no
        -- object, and one it partly covers at a stable key is its rest.
        have hs' : meaning G (memberFieldSlice G A g.field ts (!y.onFalse) y.type) (m+1) W (ρ g.cell) := by
          unfold memberFieldSlice
          cases hq : (!y.onFalse)
          · rw [hq] at hs
            exact BranchRefinement.uncoveredField_sound hs hh hobj hlk hu
              (fun t ht => tagHolds_of_heap (hv ▸ hno hq t ht))
          · rw [hq] at hs
            exact hs
        rw [← hcell]
        exact PositiveCertificates.acceptedUsing hp' _ _ _ hs'
      · cases hp'


private theorem option_any_some {α : Type} {p : α → Bool} {o : Option α} (h : o.any p = true) :
    ∃ x, o = some x ∧ p x = true := by
  cases o <;> simp_all

/-- A strict comparison's yield holds where the comparison answered: its
answer, by (E1) where `true` and (E2) where `false`, is a membership test's
(`memberYield_sound`). -/
theorem comparisonYield_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ links y a b}
    (hf : comparisonYield G images Γ links y a b = true) {ρ m W h} {u : Tm}
    (he : EnvOk G Γ ρ (m+1) W) (hh : HeapOk (m+1) W h) (hl : HeapLinks.Holds links ρ h)
    (hq : ∃ q, strictEquals (ρ a) (ρ b) = some q ∧ u = boolVal q)
    (hcond : y.conditional = true → u = .tru) (hneg : y.onFalse = true → u = .fls) :
    meaning G y.type (m+1) W (ρ y.target) := by
  unfold comparisonYield at hf
  split at hf
  · rename_i B hB
    obtain ⟨ts, hts, hm⟩ := option_any_some hf
    obtain ⟨q, hq, rfl⟩ := hq
    have hcy : y.conditional = !y.onFalse := by
      unfold memberYield at hm
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      exact hm.1.1
    cases hon : y.onFalse
    · rw [hon] at hts hcy
      simp only [Bool.false_eq_true, ↓reduceIte] at hts
      have hu := hcond (by simpa using hcy)
      have hq' : q = true := by cases q <;> simp_all [boolVal]
      subst hq'
      obtain ⟨t, ht, htag⟩ := equalityTags_sound hts (he.2 b B hB) hq
      refine memberYield_sound hm he hh hl (.inl ⟨hu, t, ht, ?_⟩) hcond hneg
      rw [tagHoldsIn_of_readsProto (equalityTags_readsProto hts t ht)]
      exact htag
    · rw [hon] at hts
      simp only [↓reduceIte, Option.map_eq_some_iff] at hts
      obtain ⟨t, hst, rfl⟩ := hts
      have hu := hneg hon
      have hq' : q = false := by cases q <;> simp_all [boolVal]
      subst hq'
      have htag := singletonTag_sound hst (he.2 b B hB) hq
      refine memberYield_sound hm he hh hl (.inr ⟨hu, fun t' ht' => ?_⟩) hcond hneg
      rw [List.mem_singleton.mp ht', tagHoldsIn_of_readsProto (singletonTag_readsProto hst)]
      exact htag
  · cases hf

/-- The slots a strict comparison's yield reads hold values. -/
theorem comparisonYield_slots {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ links y a b}
    (hf : comparisonYield G images Γ links y a b = true) :
    (∃ A, Γ[a]? = some A) ∧ ∃ B, Γ[b]? = some B := by
  unfold comparisonYield at hf
  split at hf
  · rename_i B hB
    obtain ⟨ts, -, hm⟩ := option_any_some hf
    unfold memberYield at hm
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hm
    exact ⟨hm.1.2, B, hB⟩
  · cases hf

theorem yieldFollows_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ xs links t} {ys : List (Yield ι)}
    (hc : ys.all (yieldFollows G images Γ xs links t) = true) {ρ n W h} {T : Fam} {Q : Post}
    (he : EnvOk G Γ ρ n W) (hx : ImpliesOk G xs ρ n W) (hh : HeapOk n W h)
    (hl : HeapLinks.Holds links ρ h)
    (hs : SafePost (excOf G) T Q n W h (instantiate 0 ρ t)) :
    SafePost (excOf G) (fun k U u => T k U u ∧ YieldsOk G ys ρ k U u) Q n W h (instantiate 0 ρ t) := by
  cases n with
  | zero => exact hs
  | succ m =>
  apply conj_reached hs
  intro k hk U hU r h' u run hu y hy hcond _hneg
  have he' := he.transfer k hk U hU
  have hx' := hx.transfer k hk U hU
  have hf := List.all_eq_true.mp hc y hy
  -- The object's slice, at the run's own level, carried to the reached world.
  have later : ∀ {B : Ty ι} {v}, meaning G B (m+1) W v → meaning G B k U v := fun hv =>
    (meaning_adm G _).mono k _ U hU _ ((meaning_adm G _).down_le (m+1) k hk W _ hv)
  unfold yieldFollows at hf
  simp only [Bool.or_eq_true] at hf
  rcases hf with hm | hf
  · unfold memberFollows at hm
    split at hm
    · rename_i ts i _
      simp only [Bool.and_eq_true] at hm
      obtain ⟨hshape, hm⟩ := hm
      have hval : isVal (ρ i) = true := by
        unfold memberYield at hm
        simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hm
        obtain ⟨⟨_, A, hA⟩, -⟩ := hm
        exact (meaning_value (he.2 i A hA)).1
      have run' : Steps r h (memberOn ts (ρ i)) h' u := by
        rw [← instantiate_memberOn, ← isMemberOn_sound hshape]
        simpa using run
      exact later (memberYield_sound hm he hh hl (member_run hval run' hu) hcond _hneg)
    · cases hm
  split at hf
  · rename_i i
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hf
    obtain ⟨⟨hcy, A, hA⟩, x, hxm, ⟨htest, htarget⟩, hw⟩ := hf
    have hval : isVal (ρ i) = true := (meaning_value (he.2 i A hA)).1
    have hui : u = ρ i := steps_value hval (by simpa [instantiate] using run)
    have htru := hcond hcy
    rw [← htarget]
    exact meaning_within hw (hx' x hxm (by rw [htest, ← hui, htru]))
  · rename_i tag i
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hf
    obtain ⟨hcy, ⟨rfl, hob⟩ | hfy⟩ := hf
    · unfold observedTag at hob
      split at hob
      · rename_i A p hA _
        have hval : isVal (ρ y.target) = true := (meaning_value (he.2 _ A hA)).1
        have hu' := test_ite_run hval rfl rfl (by simpa [instantiate] using run) hu
        have htag : tagHoldsIn h tag (ρ y.target) = true := by
          cases htg : tagHoldsIn h tag (ρ y.target) <;> simp_all
        exact checkObservedSub_sound hob k U _ (he'.2 _ A hA) (tagHolds_of_heap htag)
      · cases hob
    · have hval : isVal (ρ i) = true := by
        unfold fieldYield at hfy
        simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hfy
        obtain ⟨⟨A, hA⟩, -⟩ := hfy
        exact (meaning_value (he.2 i A hA)).1
      have hu' := test_ite_run hval rfl rfl (by simpa [instantiate] using run) hu
      have htag : tagHoldsIn h tag (ρ i) = true := by
        cases htg : tagHoldsIn h tag (ρ i) <;> simp_all
      exact later (fieldYield_sound hfy he hh hl htag)
  · rename_i tag i
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hf
    obtain ⟨hcy, ⟨rfl, hob⟩ | hfy⟩ := hf
    · unfold observedTag at hob
      split at hob
      · rename_i A p hA _
        have hval : isVal (ρ y.target) = true := (meaning_value (he.2 _ A hA)).1
        have hu' := test_ite_run hval rfl rfl (by simpa [instantiate] using run) hu
        have htag : tagHoldsIn h tag (ρ y.target) = false := by
          cases htg : tagHoldsIn h tag (ρ y.target) <;> simp_all
        exact checkObservedSub_sound hob k U _ (he'.2 _ A hA) (tagHolds_of_heap htag)
      · cases hob
    · have hval : isVal (ρ i) = true := by
        unfold fieldYield at hfy
        simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hfy
        obtain ⟨⟨A, hA⟩, -⟩ := hfy
        exact (meaning_value (he.2 i A hA)).1
      have hu' := test_ite_run hval rfl rfl (by simpa [instantiate] using run) hu
      have htag : tagHoldsIn h tag (ρ i) = false := by
        cases htg : tagHoldsIn h tag (ρ i) <;> simp_all
      exact later (fieldYield_sound hfy he hh hl htag)
  · rename_i i j
    have hslots : ∀ {a b}, comparisonYield G images Γ links y a b = true → isVal (ρ a) = true ∧ isVal (ρ b) = true :=
      fun hc => by
        obtain ⟨⟨A, hA⟩, B, hB⟩ := comparisonYield_slots hc
        exact ⟨(meaning_value (he.2 _ A hA)).1, (meaning_value (he.2 _ B hB)).1⟩
    have hrun : ∀ {a b}, comparisonYield G images Γ links y a b = true →
        ∃ q, strictEquals (ρ i) (ρ j) = some q ∧ u = boolVal q := fun hc => by
      have ⟨hvi, hvj⟩ : isVal (ρ i) = true ∧ isVal (ρ j) = true := by
        simp only [Bool.or_eq_true] at hf
        rcases hf with hc' | hc'
        · exact hslots hc'
        · exact (hslots hc').symm
      exact (eq_run hvi hvj (by simpa [instantiate] using run) hu).2
    simp only [Bool.or_eq_true] at hf
    rcases hf with hc | hc
    · exact later (comparisonYield_sound hc he hh hl (hrun hc) hcond _hneg)
    · obtain ⟨q, hq, hu'⟩ := hrun hc
      exact later (comparisonYield_sound hc he hh hl ⟨q, by rw [strictEquals_comm]; exact hq, hu'⟩ hcond _hneg)
  · cases hf

/-! ### A call at a promise signature -/

/-- Whether a type holds `undefined`: by a clause of `undefined`, or of every
value (`top`, `source`). -/
def admitsUndef (G : NormalGraph ι) (A : Ty ι) : Bool :=
  (expand G A).any fun c => match c with | .undef | .top | .source => true | _ => false

omit [DecidableEq ι] in
/-- What the built-ins ask of a clause holds of `undefined`, which is no object. -/
theorem builtinInvariant_undef (G : NormalGraph ι) (X : List ι → Fam) (c : PositiveNormalization.Clause (List ι)) (n W) :
    builtinInvariant G X c n W .undef := by
  unfold builtinInvariant
  cases G.builtins <;> (cases c.carriesInvariant <;> simp only [Bool.false_eq_true, ↓reduceIte])
  · intro flds oid h; cases h
  · intro flds oid h; cases h

omit [DecidableEq ι] in
theorem admitsUndef_sound {G : NormalGraph ι} {A : Ty ι} (h : admitsUndef G A = true) (n W) :
    meaning G A n W .undef := by
  obtain ⟨c, hc, ht⟩ := List.any_eq_true.mp h
  refine expand_sem_mpr ⟨c, expand_sub hc, ?_, builtinInvariant_undef G _ c n W⟩
  cases c <;> simp_all [PositiveNormalization.semWithArgs, PositiveNormalization.topT,
    PositiveNormalization.sourceT, undefT, isVal, isSourceVal, Scoped]

/-- The promise a call node's evidence states of its actual: the evidence is a
call at a signature of its callee (`app`), every operand evaluated, and the
callee's type holds, beside that signature, a promise signature with the same
receiver and parameters, whose promised actual is the slot `a`. The promise's
effect, the slot and the promise's type. -/
@[nospecialize] def promiseOf (G : NormalGraph ι) : Evidence ι → Option (Effect × Nat × Ty ι)
  | .node j (.app _) ps =>
    if ps.all (fun p => ExpressionEffects.valueTerm (claim p).term &&
        checkScope (claim p).context.length (claim p).term) then
      match j.term, ps.map claim with
      | .invoke _ _ args, jf :: jr :: jas =>
        match expand G jf.type with
        | [.arrs L _] => L.findSome? fun s =>
          if s.receiver = jr.type ∧ s.arguments = jas.map Sequent.type ∧ s.effect.requires = none ∧
              s.effect.pre = [] then
            match s.effect.promise with
            | some (.guards p) | some (.asserts p) => match args[p]? with
              | some (.var a) => some (s.effect, a, s.result)
              | _ => none
            | _ => none
          else none
        | _ => none
      | _, _ => none
    else none
  | _ => none

/-- A promise node's yields and result: each yield is the promise's slot, at a
type the promise's is within, conditional for a type guard's; the result's type
holds `true` and `false` for a type guard, `undefined` for an assertion
function. -/
def promiseYields (G : NormalGraph ι) (A : Ty ι) (effect : Effect) (a : Nat) (T : Ty ι)
    (ys : List (Yield ι)) : Bool :=
  (match effect.promise with
    | some (.guards _) => booleanMember G A true && booleanMember G A false
    | some (.asserts _) => admitsUndef G A
    | none => false) &&
  ys.all fun y => y.target == a && within T y.type &&
    (match effect.promise with | some (.guards _) => y.conditional | _ => true)

/-- Whether a signature's effect keeps the contents of every location a
call starts with on a normal return: its normal exit's frame
(`Effect.frame`) is included in the empty effect
(`Footprint.keepsHeap`; PROGRAM-TYPING.md, "A call that keeps the heap"). -/
def keepsHeap (e : Effect) : Bool := Footprints.Footprint.keepsHeap e.frame

/-- The heap facts of a call's entry kept on a normal return of a call at a
promise signature: every one where its effect keeps the heap (`call-keep`),
else those no call changes. -/
def promiseOutput (effect : Effect) (k : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge :=
  if keepsHeap effect then HeapKnowledge.shift k else HeapExpressionRules.ordinaryOutput k

/-- A transition within the frame of an effect keeping the heap ends in an
extension of the heap it starts in. -/
theorem keepsHeap_prefix {e : Effect} (hk : keepsHeap e = true) {r : Tm} {args : List Tm} {before after : Heap}
    (hcat : Footprints.ClassOk Footprints.intrinsicClasses (CallEffects.callEnv r args) before)
    (hp : e.within r args before after) : before.IsPrefix after := by
  exact Footprints.Footprint.keepsHeap_prefix hk hcat hp

theorem promiseOutput_holds {effect : Effect} {k : HeapKnowledge.Knowledge} {ρ : Env} {h h' : Heap}
    {r : Tm} {args : List Tm} {v : Tm} (hk : HeapKnowledge.Holds k ε ρ h)
    (hcat : Footprints.ClassOk Footprints.intrinsicClasses (CallEffects.callEnv r args) h)
    (hp : effect.within r args h h') :
    HeapKnowledge.Holds (promiseOutput effect k) ε (push v ρ) h' := by
  unfold promiseOutput
  split
  · rename_i hkeep
    exact HeapKnowledge.shift_holds (HeapExpressionRules.knowledge_extend hk (keepsHeap_prefix hkeep hcat hp))
  · exact HeapExpressionRules.ordinaryOutput_holds hk v h'

/-- What the ordinary output states holds wherever a promise call's output
holds: it keeps less. -/
theorem promiseOutput_ordinary {effect : Effect} {k : HeapKnowledge.Knowledge} {τ : Env} {h : Heap}
    (hk : HeapKnowledge.Holds (promiseOutput effect k) ε τ h) :
    HeapKnowledge.Holds (HeapExpressionRules.ordinaryOutput k) ε τ h := by
  unfold promiseOutput at hk
  split at hk
  · exact Footprints.heapFree_le hk
  · exact hk

/-- **A call at a promise signature** returns where the promise holds: its
callee meets the promise signature it holds beside the one the call is
checked at, at the same receiver and actuals, so the call's own run is one the
promise is about (`CallEffects.call_safe`). The result meets the claim's type,
and the facts kept are those its effect keeps (`promiseOutput`). -/
theorem promiseCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {e : Evidence ι}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {effect a T} {ys : List (Yield ι)}
    (hp : promiseOf G e = some (effect, a, T))
    (ht : checkTreeUsing G images e codes sums = true) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums)
    (hy : promiseYields G (claim e).type effect a T ys = true)
    {k ρ n W h} (he : EnvOk G (claim e).context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ (claim e).term)) :
    SafePost (excOf G) (fun m U u => meaning G (claim e).type m U u ∧ YieldsOk G ys ρ m U u)
      (fun h' v => HeapKnowledge.Holds (promiseOutput effect k) ε (push v ρ) h') n W h
      (instantiate 0 ρ (claim e).term) := by
  rcases e with ⟨⟨Γ, t, A⟩, r, ps⟩
  simp only [claim] at he hy href ⊢
  cases r <;> try (simp only [promiseOf] at hp; contradiction)
  rename_i r0
  simp only [promiseOf] at hp
  split at hp
  case isFalse => contradiction
  rename_i hvals
  simp only [List.all_eq_true, Bool.and_eq_true] at hvals
  simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
  have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
    intro p hm
    obtain ⟨e, heq, rfl⟩ := List.mem_map.mp hm
    exact checkTreeUsing_sound e (ht.2 ⟨e, heq⟩ (by simp)) hcodes hsums
  have hvals' : ∀ p ∈ ps.map claim, ExpressionEffects.valueTerm p.term = true ∧
      checkScope p.context.length p.term = true := by
    intro p hm
    obtain ⟨e, heq, rfl⟩ := List.mem_map.mp hm
    exact hvals e heq
  have hlocal := ht.1
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
  have refsOf := ExpressionEffects.invoke_refs htf htr hargs hundef href
  cases n with
  | zero => exact href
  | succ n =>
    have member : ∀ p ∈ jf::jr::jas, meaning G p.type (n+1) W (instantiate 0 ρ p.term) := by
      intro p hp
      exact safe_value_mem (values p hp) ((typed' p hp).sound _ _ h ρ he hw hh (refsOf p hp))
    have hf := ((represents_raw hF (n+1) W _) (member jf (by simp))).1
    have hpw := hf.2 _ (List.mem_map_of_mem hs)
    simp only [CallEffects.Arrow.map, CallEffects.Contract.map] at hpw
    have hArgs := ExpressionEffects.argument_values (ps := jas)
      (fun p hp => typed' p (by simp [hp])) (fun p hp => values p (by simp [hp])) he hw hh
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
      (by simpa [htf, htr, instantiate, instantiateArgs_eq_map] using href)
    have hterm : instantiate 0 ρ (.invoke f rv args) = .invoke (instantiate 0 ρ jf.term)
        (instantiate 0 ρ jr.term) (args.map (instantiate 0 ρ)) := by
      simp [instantiate, instantiateArgs_eq_map, htf, htr]
    rw [hterm]
    have hsel : s.effect = effect := by
      revert hsome
      split <;> (try split) <;> intro hsome <;> simp_all
    refine consequence (fun m U u hu => ?_)
      (fun h' v hq => promiseOutput_holds hk
        (Footprints.intrinsicClasses_ok hh (CallEffects.callEnv_rootsOk
          (RefsOk_invoke.mp (by simpa [htf, htr, instantiate, instantiateArgs_eq_map] using href)).2.1
          (RefsOk_invoke.mp (by simpa [htf, htr, instantiate, instantiateArgs_eq_map] using href)).2.2))
        (hsel ▸ Effect.callPost_within hq)) hs'
    clear hsel
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

/-- Whether every value of a type is `undefined`. -/
def onlyUndef (G : NormalGraph ι) (A : Ty ι) : Bool :=
  G.plainTy A && (expand G A).all fun c => match c with | .undef => true | _ => false

omit [DecidableEq ι] in
theorem onlyUndef_sound {G : NormalGraph ι} {A : Ty ι} {n W v}
    (h : onlyUndef G A = true) (hv : meaning G A n W v) : v = .undef := by
  simp only [onlyUndef, Bool.and_eq_true] at h
  rw [expand_sem G A h.1] at hv
  obtain ⟨c, hc, hv, -⟩ := hv
  have h := List.all_eq_true.mp h.2 c hc
  cases c <;> simp_all [PositiveNormalization.semWithArgs, undefT]

/-! ### A call that keeps the heap (PROGRAM-TYPING.md, "A call that keeps the heap")

A call whose selected signature's footprint is within the empty one, its
receiver's spine included, returns normally in an extension of the heap it
started in, so every heap fact of its entry still holds there (`call-keep`).
A call at a promise signature keeps them only where the promise signature's
effect keeps the heap too, as its node's check (`checkYields`) requires. -/

/-- Whether an ordinary step's evidence is a call `call-keep` applies to: at
the sequent `j`, at a selected signature keeping the heap, its derivation
checked, and, at a promise signature, that signature's effect keeping the
heap as well. -/
@[nospecialize] def keepsCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) : Bool :=
  match e with
  | .ordinary p =>
    decide (claim p = j) && ExpressionEffects.selectedCallWithin .empty p &&
      (match promiseOf G p with | some (effect, _, _) => keepsHeap effect | none => true) &&
      checkTreeUsing G images p codes sums
  | _ => false

theorem keepsCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : keepsCall G images j e codes sums = true) (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {k : HeapKnowledge.Knowledge} {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds (HeapKnowledge.shift k) ε (push v ρ) h') n W h (instantiate 0 ρ j.term) := by
  unfold keepsCall at hc
  split at hc
  · rename_i p
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨rfl, hsel⟩, -⟩, ht⟩ := hc
    refine consequence (fun _ _ _ hv => hv) (fun h' v hq => ?_)
      (ExpressionEffects.selectedCall_sound p ht hsel hcodes hsums he hw hh href)
    exact HeapKnowledge.shift_holds (Footprints.knowledge_frame_empty hk hq)
  · contradiction

/-! ### A call allocating its result (PROGRAM-TYPING.md, "A call allocating its result")

A call keeping the heap whose signature states `freshObject` returns an object
every own location of which lies past the heap the call started in, while
every contract field of a slot of the call's context lies in it: its result
is separated from those fields, as an allocation's is (`call-fresh`). -/

/-- Whether an ordinary step's evidence is a call `call-fresh` applies to: at
the sequent `j`, its operands values, at a selected signature keeping the heap
and stating a fresh object, its derivation checked. -/
@[nospecialize] def freshCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) : Bool :=
  match e with
  | .ordinary p =>
    decide (claim p = j) && ExpressionEffects.selectedOperands p &&
      (match ExpressionEffects.selectedEffect p with
        | some eff => keepsHeap eff && eff.schema.normal.freshObjectResult
        | none => false) &&
      checkTreeUsing G images p codes sums
  | _ => false

/-- The knowledge after a call allocating its result: every fact of the entry,
and the result's separation from the context's contract fields. -/
def freshOutput (G : NormalGraph ι) (Γ : List (Ty ι)) (k : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge :=
  HeapExpressionRules.allocOutput k [] Γ.length (HeapExpressionRules.contractFields G Γ)

/-- A fresh object's own locations lie past the old heap's end; a contract
field of a slot holds a heap value, so it lies below it. -/
theorem freshObject_apart {G : NormalGraph ι} {Γ ρ n W h} {v : Tm}
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h) (hv : Footprints.FreshObjectAt h.length v) :
    ∀ s g, (s, g) ∈ HeapExpressionRules.contractFields G Γ →
      HeapSeparation.Apart (push v ρ) 0 none (s + 1) g := by
  intro s g hm l l' hl hl'
  obtain ⟨Ref,hidx,hfo⟩ := HeapExpressionRules.contractFields_mem hm
  obtain ⟨_,flds1,code0,oid0,l1,c1,hl0,hfd1,hlookup,_⟩ :=
    HeapExpressionRules.fieldOperand_sound hfo (he.2 s Ref hidx)
  obtain ⟨u,hu,_⟩ := hh.1.2 l1 c1 hlookup
  have hlt : l1 < h.length := List.getElem?_eq_some_iff.mp hu |>.1
  obtain ⟨⟨fs, c, oid, rfl⟩, hown⟩ := hv
  have hge : h.length ≤ l := hown l (by simpa [push, HeapSeparation.At, Footprints.ownOf, Footprints.fieldsOf] using hl)
  simp only [push, hl0, HeapSeparation.At, List.mem_singleton, exists_eq_left] at hl'
  have : l' = l1 := Option.some.inj (hl'.symm.trans hfd1)
  omega

theorem freshCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : freshCall G images j e codes sums = true) (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {k : HeapKnowledge.Knowledge} {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds (freshOutput G j.context k) ε (push v ρ) h') n W h (instantiate 0 ρ j.term) := by
  unfold freshCall at hc
  split at hc
  · rename_i p
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨rfl, hops⟩, hsel⟩, ht⟩ := hc
    split at hsel
    · rename_i eff heff
      simp only [Bool.and_eq_true] at hsel
      obtain ⟨hkeep, hfo⟩ := hsel
      refine consequence (fun _ _ _ hv => hv) (fun h' v hq => ?_)
        (ExpressionEffects.selected_sound p ht hops heff hcodes hsums he hw hh href)
      have hfresh := Effect.callPost_freshObject hfo hq
      have hshift := HeapKnowledge.shift_holds (v := v)
        (HeapExpressionRules.knowledge_extend hk (keepsHeap_prefix hkeep
          (Footprints.intrinsicClasses_ok hh (ExpressionEffects.callEnv_rootsOk_of_refs href))
          (Effect.callPost_within hq)))
      refine ⟨?_, hshift.2.1, hshift.2.2.1,
        HeapSeparation.allocate_holds hk.2.2.2.1 (freshObject_apart he hh hfresh), hshift.2.2.2.2⟩
      simpa [freshOutput, HeapExpressionRules.allocOutput, HeapKnowledge.shift] using hshift.1
    · cases hsel
  · contradiction

/-! ### A call changing only its receiver's own locations (PROGRAM-TYPING.md, "A call changing only its receiver")

A call whose normal exit's frame has an entry at its receiver's own value
locations, and whose other entries are included in the empty effect
(`Footprint.keepsHeap_outside`), changes no location a fact names that a
separation fact keeps apart from every own location of the receiver
(`call-own`). -/

/-- The receiver's own field locations: the region of a frame's entry that
`call-own` reads as changed. -/
def receiverFieldsValues : Footprints.Region := .fields 0

/-- **Whether a frame changes only its receiver's own value locations**: it
has an entry at them, and its entries at every other region are included in
the empty effect. -/
def ownOnly (Φ : Footprints.Footprint) : Bool :=
  Φ.any (fun x => x.1 == receiverFieldsValues) && (Φ.without receiverFieldsValues).keepsHeap

/-- The receiver slot of an ordinary step's evidence that `call-own` applies
to: at the sequent `j`, its operands values, at a selected signature whose
normal exit's frame changes only its receiver's own value locations
(`ownOnly`), its derivation checked, its receiver a slot. -/
@[nospecialize] def ownCallChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) : Bool :=
  match e with
  | .ordinary p =>
    decide (claim p = j) && ExpressionEffects.selectedOperands p &&
      (match ExpressionEffects.selectedEffect p with
        | some eff => ownOnly eff.schema.normal.frame
        | none => false) &&
      checkTreeUsing G images p codes sums
  | _ => false

/-- The slot a call's receiver is, where it is one. -/
def receiverSlot : Tm → Option Nat
  | .invoke _ (.var i) _ => some i
  | _ => none

@[nospecialize] def ownCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) : Option Nat :=
  if ownCallChecked G images j e codes sums then receiverSlot j.term else none

/-- The facts a call changing only the own locations of the slot `i` keeps:
each cell fact and read link about a field separated from every own location
of `i`, every alias link, every value fact and the separation. -/
def ownKept (k : HeapKnowledge.Knowledge) (i : Nat) : HeapKnowledge.Knowledge :=
  ⟨k.cells.filter (fun f => HeapSeparation.apartAll k.separation i f.slot f.field), k.values,
    k.links.filter (fun g => g.alias || HeapSeparation.apartAll k.separation i g.cell g.field), k.separation, [],
    HeapKnowledge.keptIndices HeapKnowledge.Changes.top (fun s g => HeapSeparation.apartAll k.separation i s (.str g))
      k.indices⟩

def ownOutput (k : HeapKnowledge.Knowledge) (i : Nat) : HeapKnowledge.Knowledge :=
  HeapKnowledge.shift (ownKept k i)

/-- A field read gives what it gave before where its location keeps its
contents. -/
theorem readGave_kept {flds field h h' u} (hr : HeapFacts.ReadGave flds field h u)
    (hkeep : ∀ l, flds.lookup field = some l → ∀ v, h[l]? = some v → h'[l]? = some v) :
    HeapFacts.ReadGave flds field h' u := by
  unfold HeapFacts.ReadGave at hr ⊢
  cases hl : flds.lookup field with
  | none => simpa [hl] using hr
  | some l => simp only [hl] at hr ⊢; exact hkeep l hl u hr

theorem ownKept_holds {k : HeapKnowledge.Knowledge} {i : Nat} {ρ : Env} {h h' : Heap}
    (hk : HeapKnowledge.Holds k ε ρ h)
    (hkeep : ∀ l, l ∉ Footprints.ownOf (ρ i) → ∀ v, h[l]? = some v → h'[l]? = some v) :
    HeapKnowledge.Holds (ownKept k i) ε ρ h' := by
  have away : ∀ {s g flds c oid l}, HeapSeparation.apartAll k.separation i s g = true →
      ρ s = .objAt flds c oid → flds.lookup g = some l → l ∉ Footprints.ownOf (ρ i) := by
    intro s g flds c oid l ha hs hl hm
    have hat : HeapSeparation.At none (ρ i) l := by
      unfold Footprints.ownOf Footprints.fieldsOf at hm
      unfold HeapSeparation.At
      split at hm <;> simp_all
    exact HeapSeparation.apartAll_sound ha hk.2.2.2.1 hat hs hl rfl
  refine ⟨?_, hk.2.1, ?_, hk.2.2.2.1, HeapKnowledge.elemsHolds_nil _ _,
    HeapKnowledge.keptIndices_holds hk.2.2.2.2.2
      (HeapKnowledge.Changes.top_holds h h')
      (fun s g fs cd o l v hap hs hl hv => hkeep l (away hap hs hl) v hv)⟩
  · intro f hf
    obtain ⟨hf, ha⟩ := List.mem_filter.mp hf
    obtain ⟨flds,c,oid,u,hs,hr,hm⟩ := hk.1 f hf
    exact ⟨flds,c,oid,u,hs,readGave_kept hr (fun l hl v hv => hkeep l (away ha hs hl) v hv),hm⟩
  · intro g hg
    obtain ⟨hg, ha⟩ := List.mem_filter.mp hg
    have hh := hk.2.2.1 g hg
    cases hal : g.alias
    · simp only [hal, Bool.false_or] at ha
      cases ho : g.optional
      · simp only [hal, ho, Bool.false_eq_true, ite_false] at hh ⊢
        obtain ⟨flds,c,oid,l,hs,hl,hv⟩ := hh
        exact ⟨flds,c,oid,l,hs,hl,hkeep l (away ha hs hl) _ hv⟩
      · simp only [hal, ho, Bool.false_eq_true, ite_false, ite_true] at hh ⊢
        obtain ⟨flds,c,oid,hs,hr⟩ := hh
        exact ⟨flds,c,oid,hs,readGave_kept hr (fun l hl v hv => hkeep l (away ha hs hl) v hv)⟩
    · simp only [hal, ite_true] at hh ⊢
      exact hh

theorem ownCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {i : Nat}
    (hc : ownCall G images j e codes sums = some i) (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {k : HeapKnowledge.Knowledge} {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds (ownOutput k i) ε (push v ρ) h') n W h (instantiate 0 ρ j.term) := by
  unfold ownCall at hc
  split at hc
  · rename_i hcond
    unfold ownCallChecked at hcond
    split at hcond
    · rename_i p
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨hj, hops⟩, hsel⟩, ht⟩ := hcond
      subst hj
      have hterm : ∃ f args, (claim p).term = .invoke f (.var i) args := by
        revert hc
        cases hT : (claim p).term <;> simp only [receiverSlot] <;> intro hc <;> try cases hc
        rename_i f r args
        cases r <;> first | (cases hc; exact ⟨f, args, rfl⟩) | cases hc
      obtain ⟨f, args, hterm⟩ := hterm
      split at hsel
      · rename_i eff heff
        simp only [ownOnly, Bool.and_eq_true] at hsel
        obtain ⟨-, hkeep⟩ := hsel
        refine consequence (fun _ _ _ hv => hv) (fun h' v hq => ?_)
          (ExpressionEffects.selected_sound p ht hops heff hcodes hsums he hw hh href)
        have hw' := Effect.callPost_within hq
        rw [hterm] at hw'
        simp only [ExpressionEffects.receiverOf, instantiate] at hw'
        refine HeapKnowledge.shift_holds (ownKept_holds hk fun l hl u hu => ?_)
        refine Footprints.Footprint.keepsHeap_outside (Φ := eff.schema.normal.frame) hkeep
          (by
            have hcat := Footprints.intrinsicClasses_ok hh (ExpressionEffects.callEnv_rootsOk_of_refs href)
            rw [hterm] at hcat
            simpa [ExpressionEffects.receiverOf, instantiate] using hcat)
          hw' ?_ hu
        simp only [receiverFieldsValues, Footprints.Region.mem, CallEffects.callEnv, ite_eq_left]
        have hown : ∀ x, ¬ (x, l) ∈ Footprints.fieldsOf (ρ i) := by
          simpa [List.contains_iff_mem, Footprints.ownOf] using hl
        simp only [Nat.not_lt_zero, ite_false, Nat.sub_zero]
        cases hc' : (Footprints.fieldLocs (ρ i)).contains l
        · rfl
        · obtain ⟨⟨k, l'⟩, hkl, he⟩ := List.mem_map.mp (Footprints.fieldLocs_own (List.contains_iff_mem.mp hc'))
          cases he
          exact absurd hkl (hown k)
      · cases hsel
    · cases hcond
  · cases hc

/-! ### A call promising its receiver's elements (FOOTPRINTS.md, "The elements fact")

A call keeping the heap whose selected signature promises its receiver's
elements (`elements R`) returns `true` only where every present element of
the array its receiver slot holds satisfies `R`: its output keeps every fact
of its entry and adds that atom, conditional on its result
(`call-elements`). -/

/-- Whether every value of a type is a Boolean. -/
def onlyBool (G : NormalGraph ι) (A : Ty ι) : Bool :=
  G.plainTy A && (expand G A).all fun c => match c with | .boolLit _ => true | _ => false

omit [DecidableEq ι] in
theorem onlyBool_sound {G : NormalGraph ι} {A : Ty ι} {n W v}
    (h : onlyBool G A = true) (hv : meaning G A n W v) : v = .tru ∨ v = .fls := by
  simp only [onlyBool, Bool.and_eq_true] at h
  rw [expand_sem G A h.1] at hv
  obtain ⟨c, hc, hv, -⟩ := hv
  have h := List.all_eq_true.mp h.2 c hc
  cases c <;> simp_all [PositiveNormalization.semWithArgs]

/-- A safe run whose postcondition holds of each value it returns where the
value meets the result's type. -/
theorem post_with_type {Ξ T : Fam} {Q Q' : Post} (hq : ∀ k W h v, T k W v → Q h v → Q' h v) :
    ∀ {n W h t}, SafePost Ξ T Q n W h t → SafePost Ξ T Q' n W h t := by
  intro n
  induction n with
  | zero => intros; assumption
  | succ n ih =>
    intro W h t hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, ht, hq'⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, ht, hq _ _ _ _ ht hq'⟩)
    · exact .inl (.inr hth)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, ih hs⟩

theorem receiverSlot_term {t : Tm} {x : Nat} (h : receiverSlot t = some x) :
    ∃ f args, t = .invoke f (.var x) args := by
  unfold receiverSlot at h
  split at h
  · cases h; exact ⟨_, _, rfl⟩
  · cases h

/-- The derivation a step's evidence carries beside its kind, for the kinds
whose check reads it alone: ordinary, pure, reading and created steps. -/
def stepProof : HeapExpressionRules.StepEvidence ι → Option (Evidence ι)
  | .ordinary p | .pure p | .reading p | .created p => some p
  | _ => none

/-- The receiver slot and predicate of an ordinary step's evidence that
`call-elements` applies to: at the sequent `j`, its operands values, at a
selected signature keeping the heap and promising its receiver's elements,
its derivation checked, its receiver a slot. -/
@[nospecialize] def elementsCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    Option (Nat × CallEffects.ElemPred) :=
  match stepProof e with
  | some p =>
    if decide (claim p = j) && ExpressionEffects.selectedOperands p && checkTreeUsing G images p codes sums &&
        onlyBool G j.type then
      match ExpressionEffects.selectedEffect p, receiverSlot j.term with
      | some eff, some x => if keepsHeap eff then eff.schema.normal.elementsWhenTrue.head?.map fun R => (x, R) else none
      | _, _ => none
    else none
  | _ => none

/-- `elementsCall` as the compiled verifier runs it (`elementsCall_eq_fast`):
the atom it would add read first, the sequent, operands, result type and
derivation checked only where there is one. -/
def elementsCallFast (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    Option (Nat × CallEffects.ElemPred) :=
  match stepProof e with
  | some p =>
    match ExpressionEffects.selectedEffect p, receiverSlot j.term with
    | some eff, some x =>
      if keepsHeap eff then
        match eff.schema.normal.elementsWhenTrue.head? with
        | some R =>
          if decide (claim p = j) && ExpressionEffects.selectedOperands p && onlyBool G j.type &&
              checkTreeUsing G images p codes sums then some (x, R) else none
        | none => none
      else none
    | _, _ => none
  | _ => none

@[csimp] theorem elementsCall_eq_fast : @elementsCall = @elementsCallFast := by
  funext ι _ G images j e codes sums
  unfold elementsCall elementsCallFast
  split
  · rename_i p _
    cases ExpressionEffects.selectedEffect p <;> cases receiverSlot j.term <;>
      cases decide (claim p = j) <;> cases ExpressionEffects.selectedOperands p <;>
      cases onlyBool G j.type <;> cases checkTreeUsing G images p codes sums <;> simp
    all_goals (split <;> (try split) <;> simp_all)
  · rfl

/-- The knowledge after a call promising its receiver's elements: every fact
of the entry, and the atom on the receiver's slot, conditional on the result. -/
def elementsOutput (k : HeapKnowledge.Knowledge) (x : Nat) (R : CallEffects.ElemPred) : HeapKnowledge.Knowledge :=
  { HeapKnowledge.shift k with elems := ⟨x + 1, R, some 0, false⟩ :: (HeapKnowledge.shift k).elems }

theorem elementsCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {x : Nat} {R : CallEffects.ElemPred}
    (hc : elementsCall G images j e codes sums = some (x, R)) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums)
    {k : HeapKnowledge.Knowledge} {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds (elementsOutput k x R) ε (push v ρ) h') n W h (instantiate 0 ρ j.term) := by
  unfold elementsCall at hc
  split at hc
  · rename_i p _
    by_cases hcond : (decide (claim p = j) && ExpressionEffects.selectedOperands p &&
        checkTreeUsing G images p codes sums && onlyBool G j.type) = true
    · rw [ite_eq_left hcond] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨rfl, hops⟩, ht⟩, hbool⟩ := hcond
      cases hsel : ExpressionEffects.selectedEffect p with
      | none => simp [hsel] at hc
      | some eff =>
        cases hrs : receiverSlot (claim p).term with
        | none => simp [hsel, hrs] at hc
        | some x' =>
          simp only [hsel, hrs] at hc
          by_cases hkeep : keepsHeap eff = true
          · rw [ite_eq_left hkeep] at hc
            obtain ⟨R', hR', hpair⟩ := Option.map_eq_some_iff.mp hc
            simp only [Prod.mk.injEq] at hpair
            obtain ⟨rfl, rfl⟩ := hpair
            obtain ⟨f, args, hterm⟩ := receiverSlot_term hrs
            refine post_with_type (fun m U h' v hT hq => ?_)
              (ExpressionEffects.selected_sound p ht hops hsel hcodes hsums he hw hh href)
            have hb := onlyBool_sound hbool hT
            have hs := HeapKnowledge.shift_holds (v := v)
              (HeapExpressionRules.knowledge_extend hk (keepsHeap_prefix hkeep
                (Footprints.intrinsicClasses_ok hh (ExpressionEffects.callEnv_rootsOk_of_refs href))
                (Effect.callPost_within hq)))
            refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, hs.2.2.2.2.2⟩
            intro a ha hcond
            rcases List.mem_cons.mp ha with rfl | ha
            · have hv : v = .tru := by
                have ht := hcond 0 rfl
                simp only [push] at ht
                rcases hb with rfl | rfl
                · rfl
                · simp [tagHolds] at ht
              have hel := Effect.callPost_elements (List.mem_of_mem_head? hR') hv hq
              rw [hterm] at hel
              simpa [ExpressionEffects.receiverOf, instantiate, push] using hel
            · exact hs.2.2.2.2.1 a ha hcond
          · rw [ite_eq_right hkeep] at hc; cases hc
    · rw [ite_eq_right hcond] at hc; cases hc
  · cases hc

/-! ### A call at a precondition on its receiver's elements

A call whose selected signature requires its receiver's elements to satisfy
`R` is safe where its receiver slot's class has an unconditional atom with a
predicate within `R`: the atom gives the precondition (`call-requires`). -/

/-- Whether the knowledge states, of a slot's class, that its array's present
elements satisfy a predicate within `R`. -/
def atomFor (k : HeapKnowledge.Knowledge) (x : Nat) (R : CallEffects.ElemPred) : Bool :=
  k.elems.any fun a => a.cond.isNone && (HeapLinks.aliases k.links x).contains a.slot && a.pred.le R

theorem atomFor_sound {k : HeapKnowledge.Knowledge} {x R ρ h} (hc : atomFor k x R = true)
    (hk : HeapKnowledge.Holds k ε ρ h) : CallEffects.ElemsAt R (ρ x) h := by
  obtain ⟨a, ha, hm⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.contains_iff_mem] at hm
  obtain ⟨⟨hnone, hal⟩, hle⟩ := hm
  have hat := hk.2.2.2.2.1 a ha fun b hb => by rw [hnone] at hb; cases hb
  rw [HeapLinks.aliases_eq hk.2.2.1 hal] at hat
  exact hat.mono hle

/-- The slots a list of terms names, where each is a slot. -/
def varSlots : List Tm → Option (List Nat)
  | [] => some []
  | .var a :: t => (varSlots t).map (a :: ·)
  | _ :: _ => none

theorem varSlots_get {args : List Tm} {as : List Nat} (h : varSlots args = some as) (ρ : Env) :
    as.length = args.length ∧ ∀ q < as.length, (args.map (instantiate 0 ρ)).getD q .undef = ρ (as.getD q 0) := by
  induction args generalizing as with
  | nil => simp only [varSlots, Option.some.injEq] at h; subst h; simp
  | cons t rest ih =>
    cases t <;> simp only [varSlots, Option.map_eq_some_iff, reduceCtorEq] at h
    rename_i a
    obtain ⟨bs, hbs, rfl⟩ := h
    obtain ⟨hl, hg⟩ := ih hbs
    refine ⟨by simp [hl], fun q hq => ?_⟩
    cases q with
    | zero => simp [instantiate]
    | succ q => simpa using hg q (by simpa using hq)

/-- The slots a call's positions hold: its receiver's, then its actuals', each
a slot (`CallEffects.callEnv`'s positions); and whether the receiver is a
slot. A receiver that is no slot, such as the `undefined` of a plain
function's call, holds position `0` at slot `0`, which a precondition then
may not name. -/
def callSlots : Tm → Option (Bool × List Nat)
  | .invoke _ (.var r) args => (varSlots args).map fun as => (true, r :: as)
  | .invoke _ _ args => (varSlots args).map fun as => (false, 0 :: as)
  -- A construction's receiver is `undefined` (`ExpressionEffects.receiverOf`).
  | .construct _ args => (varSlots args).map fun as => (false, 0 :: as)
  | _ => none

theorem callSlots_env {t : Tm} {recv : Bool} {slots : List Nat} (hs : callSlots t = some (recv, slots)) (ρ : Env) :
    ∀ p < slots.length, (p ≠ 0 ∨ recv = true) → PointClaims.mapEnv (some slots) ρ p =
      CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t))
        (ExpressionEffects.actualsOf (instantiate 0 ρ t)) p := by
  intro p hp hrecv
  cases t <;> simp only [callSlots, reduceCtorEq] at hs
  case construct f args =>
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hs
    obtain ⟨as, has, rfl, rfl⟩ := hs
    cases p with
    | zero => simp at hrecv
    | succ q =>
      obtain ⟨hl, hg⟩ := varSlots_get has ρ
      simp only [List.length_cons] at hp
      simp only [PointClaims.mapEnv, PointClaims.slot, ExpressionEffects.actualsOf, instantiate,
        instantiateArgs_eq_map, CallEffects.callEnv, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
        List.getElem?_cons_succ]
      rw [hg q (by omega)]
      simp [List.getD_eq_getElem?_getD]
  rename_i f r args
  have core : ∀ (as : List Nat), varSlots args = some as → ∀ (y : Nat) (q : Nat), q + 1 < (y :: as).length →
      PointClaims.mapEnv (some (y :: as)) ρ (q + 1) =
        CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ (.invoke f r args)))
          (ExpressionEffects.actualsOf (instantiate 0 ρ (.invoke f r args))) (q + 1) := by
    intro as has y q hq
    obtain ⟨hl, hg⟩ := varSlots_get has ρ
    simp only [List.length_cons] at hq
    simp only [PointClaims.mapEnv, PointClaims.slot, ExpressionEffects.actualsOf, instantiate,
      instantiateArgs_eq_map, CallEffects.callEnv, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
      List.getElem?_cons_succ]
    rw [hg q (by omega)]
    simp [List.getD_eq_getElem?_getD]
  cases r <;> simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hs
  case var x =>
    obtain ⟨as, has, -, rfl⟩ := hs
    cases p with
    | zero => simp [PointClaims.mapEnv, PointClaims.slot, ExpressionEffects.receiverOf, instantiate,
        CallEffects.callEnv]
    | succ q => exact core as has x q hp
  all_goals
    obtain ⟨as, has, rfl, rfl⟩ := hs
    cases p with
    | zero => simp at hrecv
    | succ q => exact core as has 0 q hp

/-- Whether a derivation is a call `call-requires` applies to: the local call
rule at a selected signature stating a precondition, its operands values, its
premises' derivations checked; the elements precondition's atom on its
receiver slot, and each fact of the precondition on the call's values
following from the knowledge at the slots its positions hold. -/
def preconditionHolds (k : HeapKnowledge.Knowledge) (eff : Effect) (t : Tm) : Bool :=
  (eff.requires.isSome || !eff.pre.isEmpty) &&
  (match eff.requires with
    | none => true
    | some R => match receiverSlot t with
      | some x => atomFor k x R
      | none => false) &&
  (eff.pre.isEmpty || match callSlots t with
    | some (recv, slots) =>
        eff.pre.all (fun F => F.toNow.slots.all (fun p => p < slots.length && (p != 0 || recv))) &&
        HeapKnowledge.indicesCheckWith (HeapKnowledge.guardTags k) (HeapLinks.aliases k.links) k.links k.indices
          (eff.pre.map fun F => ⟨F.toNow, none, false⟩) (some slots)
    | none => false)

theorem preconditionHolds_sound {k : HeapKnowledge.Knowledge} {eff : Effect} {t : Tm} {ρ h}
    (hc : preconditionHolds k eff t = true) (hk : HeapKnowledge.Holds k ε ρ h) :
    eff.Requires (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h := by
  simp only [preconditionHolds, Bool.and_eq_true, Bool.or_eq_true] at hc
  obtain ⟨⟨-, hreq⟩, hpre⟩ := hc
  refine ⟨fun R hR => ?_, fun F hF => ?_⟩
  · rw [hR] at hreq
    simp only at hreq
    split at hreq
    · rename_i x hx
      obtain ⟨f, args, hterm⟩ := receiverSlot_term hx
      rw [hterm]
      simpa [ExpressionEffects.receiverOf, instantiate] using atomFor_sound hreq hk
    · cases hreq
  · rcases hpre with hnil | hpre
    · simp only [List.isEmpty_iff] at hnil; rw [hnil] at hF; cases hF
    · split at hpre
      · rename_i recv slots hs
        simp only [Bool.and_eq_true, List.all_eq_true] at hpre
        obtain ⟨hin, hchk⟩ := hpre
        have hheld := HeapKnowledge.indicesCheckWith_sound (HeapKnowledge.guardTags_sound hk)
          (fun x y hy => HeapLinks.aliases_eq hk.2.2.1 hy) hk.2.2.1 hchk
          hk.2.2.2.2.2 ⟨F.toNow, none, false⟩ (List.mem_map_of_mem (f := fun F => (⟨F.toNow, none, false⟩ : HeapKnowledge.IndexAtom)) hF)
          (fun b hb => by cases hb)
        refine (CallEffects.Effect.pre_toNow ε _ h).mpr ((HeapKnowledge.IndexFact.holdsAt_congr fun s hs' => ?_).mp hheld)
        have hp := hin F hF s hs'
        simp only [decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hp
        exact callSlots_env hs ρ s hp.1 hp.2
      · simp at hpre

@[nospecialize] def requiresApp (G : NormalGraph ι) (images : InstanceImageCheck G)
    (k : HeapKnowledge.Knowledge) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    Evidence ι → Bool
  | .node j (.app eff) ps =>
    (ps.all fun p => ExpressionEffects.valueTerm (claim p).term && checkScope (claim p).context.length (claim p).term) &&
    decide (LocalUsing G images j (.app eff) (ps.map claim) codes (sums := sums) (allowRequires := true)) &&
    ps.attach.all (fun p => checkTreeUsing G images p.val codes sums) &&
    preconditionHolds (HeapKnowledge.unguardedByTypes G j.context k) eff j.term
  -- A construction at a construct signature stating a precondition, alike.
  | .node j (.construct eff) ps =>
    (ps.all fun p => ExpressionEffects.valueTerm (claim p).term && checkScope (claim p).context.length (claim p).term) &&
    decide (LocalUsing G images j (.construct eff) (ps.map claim) codes (sums := sums) (allowRequires := true)) &&
    ps.attach.all (fun p => checkTreeUsing G images p.val codes sums) &&
    preconditionHolds (HeapKnowledge.unguardedByTypes G j.context k) eff j.term
  | _ => false

/-- `requiresApp` as the compiled verifier runs it (`requiresApp_eq_fast`):
whether the signature states a precondition read first. -/
def requiresAppFast (G : NormalGraph ι) (images : InstanceImageCheck G)
    (k : HeapKnowledge.Knowledge) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    Evidence ι → Bool
  | .node j (.app eff) ps =>
    (eff.requires.isSome || !eff.pre.isEmpty) &&
    (ps.all fun p => ExpressionEffects.valueTerm (claim p).term && checkScope (claim p).context.length (claim p).term) &&
    decide (LocalUsing G images j (.app eff) (ps.map claim) codes (sums := sums) (allowRequires := true)) &&
    ps.attach.all (fun p => checkTreeUsing G images p.val codes sums) &&
    preconditionHolds (HeapKnowledge.unguardedByTypes G j.context k) eff j.term
  | .node j (.construct eff) ps =>
    (eff.requires.isSome || !eff.pre.isEmpty) &&
    (ps.all fun p => ExpressionEffects.valueTerm (claim p).term && checkScope (claim p).context.length (claim p).term) &&
    decide (LocalUsing G images j (.construct eff) (ps.map claim) codes (sums := sums) (allowRequires := true)) &&
    ps.attach.all (fun p => checkTreeUsing G images p.val codes sums) &&
    preconditionHolds (HeapKnowledge.unguardedByTypes G j.context k) eff j.term
  | _ => false

@[csimp] theorem requiresApp_eq_fast : @requiresApp = @requiresAppFast := by
  funext ι _ G images k codes sums p
  unfold requiresApp requiresAppFast
  split
  · rename_i eff _
    unfold preconditionHolds
    generalize (eff.requires.isSome || !eff.pre.isEmpty) = g
    cases g <;> simp
  · rename_i eff _
    unfold preconditionHolds
    generalize (eff.requires.isSome || !eff.pre.isEmpty) = g
    cases g <;> simp
  · rfl

/-- Such a call, or its subsumption. -/
@[nospecialize] def requiresTree (G : NormalGraph ι) (images : InstanceImageCheck G)
    (k : HeapKnowledge.Knowledge) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    Evidence ι → Bool
  | .node j (.sub c) [p] =>
    decide (LocalUsing G images j (.sub c) [claim p] codes (sums := sums)) && requiresApp G images k codes sums p
  | p => requiresApp G images k codes sums p

theorem requiresApp_sound {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (p : Evidence ι) (hc : requiresApp G images k codes sums p = true) {eff : Effect}
    (hsel : ExpressionEffects.selectedEffect p = some eff) {ρ n W h} (he : EnvOk G (claim p).context ρ n W)
    (hk : HeapKnowledge.Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ (claim p).term)) :
    SafePost (excOf G) (meaning G (claim p).type)
      (eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term))
        (ExpressionEffects.actualsOf (instantiate 0 ρ (claim p).term)) h) n W h
      (instantiate 0 ρ (claim p).term) := by
  obtain ⟨j, r, ps⟩ := p
  cases r with
  | app eff' =>
      simp only [ExpressionEffects.selectedEffect, Option.some.injEq] at hsel
      subst hsel
      simp only [requiresApp, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hvals, hl⟩, ht⟩, hreq⟩ := hc
      simp only [claim] at he href ⊢
      have hq := preconditionHolds_sound hreq (HeapKnowledge.unguardedByTypes_holds he hk) (ρ := ρ)
      have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound q (List.all_eq_true.mp ht ⟨q, hq⟩ (List.mem_attach _ _)) hcodes hsums
      have values : ∀ p ∈ ps.map claim, ExpressionEffects.valueTerm p.term = true ∧
          checkScope p.context.length p.term = true := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        simpa only [Bool.and_eq_true] using List.all_eq_true.mp hvals q hq
      exact (ExpressionEffects.call_local_sound hl typed values he hw hh hq href).post
  | construct eff' =>
      simp only [ExpressionEffects.selectedEffect, Option.some.injEq] at hsel
      subst hsel
      simp only [requiresApp, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hvals, hl⟩, ht⟩, hreq⟩ := hc
      simp only [claim] at he href ⊢
      have hq := preconditionHolds_sound hreq (HeapKnowledge.unguardedByTypes_holds he hk) (ρ := ρ)
      have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound q (List.all_eq_true.mp ht ⟨q, hq⟩ (List.mem_attach _ _)) hcodes hsums
      have values : ∀ p ∈ ps.map claim, ExpressionEffects.valueTerm p.term = true ∧
          checkScope p.context.length p.term = true := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        simpa only [Bool.and_eq_true] using List.all_eq_true.mp hvals q hq
      exact (ExpressionEffects.construct_local_requires_sound hl typed values he hw hh hq href).post
  | _ => simp [requiresApp] at hc

/-- `call-requires` also bounds the heap a throw leaves, where its signature
states so (`excPost`). -/
theorem requiresApp_sound_exc {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (p : Evidence ι) (hc : requiresApp G images k codes sums p = true) {eff : Effect}
    (hsel : ExpressionEffects.selectedEffect p = some eff) {ρ n W h} (he : EnvOk G (claim p).context ρ n W)
    (hk : HeapKnowledge.Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ (claim p).term)) :
    SafePostExc (excOf G) (meaning G (claim p).type)
      (eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term))
        (ExpressionEffects.actualsOf (instantiate 0 ρ (claim p).term)) h)
      (eff.callExc (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term)) (ExpressionEffects.actualsOf (instantiate 0 ρ (claim p).term)) h) n W h
      (instantiate 0 ρ (claim p).term) := by
  obtain ⟨j, r, ps⟩ := p
  cases r with
  | app eff' =>
      simp only [ExpressionEffects.selectedEffect, Option.some.injEq] at hsel
      subst hsel
      simp only [requiresApp, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hvals, hl⟩, ht⟩, hreq⟩ := hc
      simp only [claim] at he href ⊢
      have hq := preconditionHolds_sound hreq (HeapKnowledge.unguardedByTypes_holds he hk) (ρ := ρ)
      have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound q (List.all_eq_true.mp ht ⟨q, hq⟩ (List.mem_attach _ _)) hcodes hsums
      have values : ∀ p ∈ ps.map claim, ExpressionEffects.valueTerm p.term = true ∧
          checkScope p.context.length p.term = true := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        simpa only [Bool.and_eq_true] using List.all_eq_true.mp hvals q hq
      exact ExpressionEffects.call_local_sound hl typed values he hw hh hq href
  | construct eff' =>
      simp only [ExpressionEffects.selectedEffect, Option.some.injEq] at hsel
      subst hsel
      simp only [requiresApp, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hvals, hl⟩, ht⟩, hreq⟩ := hc
      simp only [claim] at he href ⊢
      have hq := preconditionHolds_sound hreq (HeapKnowledge.unguardedByTypes_holds he hk) (ρ := ρ)
      have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound q (List.all_eq_true.mp ht ⟨q, hq⟩ (List.mem_attach _ _)) hcodes hsums
      have values : ∀ p ∈ ps.map claim, ExpressionEffects.valueTerm p.term = true ∧
          checkScope p.context.length p.term = true := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        simpa only [Bool.and_eq_true] using List.all_eq_true.mp hvals q hq
      exact ExpressionEffects.construct_local_requires_sound hl typed values he hw hh hq href
  | _ => simp [requiresApp] at hc

theorem requiresApp_selected {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (p : Evidence ι) (hc : requiresApp G images k codes sums p = true) :
    ∃ eff, ExpressionEffects.selectedEffect p = some eff := by
  obtain ⟨j, r, ps⟩ := p
  cases r with
  | app eff' => exact ⟨_, rfl⟩
  | construct eff' => exact ⟨_, rfl⟩
  | _ => simp [requiresApp] at hc

theorem requiresTree_sound {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (p : Evidence ι) (hc : requiresTree G images k codes sums p = true) :
    ∃ eff, ExpressionEffects.selectedEffect p = some eff ∧ ∀ {ρ n W h}, EnvOk G (claim p).context ρ n W →
    HeapKnowledge.Holds k ε ρ h → WorldAdm W → HeapOk n W h → RefsOk W (instantiate 0 ρ (claim p).term) →
    SafePost (excOf G) (meaning G (claim p).type)
      (eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term))
        (ExpressionEffects.actualsOf (instantiate 0 ρ (claim p).term)) h) n W h
      (instantiate 0 ρ (claim p).term) := by
  by_cases hs : ∃ j c q, p = .node j (.sub c) [q]
  · obtain ⟨j, c, q, rfl⟩ := hs
    simp only [requiresTree, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hl, hc⟩ := hc
    obtain ⟨eff, hsel⟩ := requiresApp_selected q hc
    refine ⟨eff, by simpa [ExpressionEffects.selectedEffect] using hsel, fun {ρ n W h} he hk hw hh href => ?_⟩
    obtain ⟨hctx, hterm, hsub⟩ := hl
    have ih := requiresApp_sound hcodes hsums q hc hsel (ρ := ρ) (n := n) (W := W) (h := h)
      (by rw [hctx]; exact he) hk hw hh (by simp only [claim] at href; rw [hterm]; exact href)
    rw [hterm] at ih
    exact consequence (fun j W v hv => PositiveCertificates.acceptedUsing hsub j W v hv) (fun _ _ hp => hp) ih
  · have happ : requiresApp G images k codes sums p = true := by
      obtain ⟨j, r, ps⟩ := p
      cases r <;> try (simpa [requiresTree] using hc)
      rcases ps with _ | ⟨q, _ | ⟨q', qs⟩⟩
      · simpa [requiresTree] using hc
      · exact absurd ⟨j, _, q, rfl⟩ hs
      · simpa [requiresTree] using hc
    obtain ⟨eff, hsel⟩ := requiresApp_selected p happ
    exact ⟨eff, hsel, fun he hk hw hh href => requiresApp_sound hcodes hsums p happ hsel he hk hw hh href⟩

theorem requiresTree_sound_exc {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (p : Evidence ι) (hc : requiresTree G images k codes sums p = true) :
    ∃ eff, ExpressionEffects.selectedEffect p = some eff ∧ ∀ {ρ n W h}, EnvOk G (claim p).context ρ n W →
    HeapKnowledge.Holds k ε ρ h → WorldAdm W → HeapOk n W h → RefsOk W (instantiate 0 ρ (claim p).term) →
    SafePostExc (excOf G) (meaning G (claim p).type)
      (eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term))
        (ExpressionEffects.actualsOf (instantiate 0 ρ (claim p).term)) h)
      (eff.callExc (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term)) (ExpressionEffects.actualsOf (instantiate 0 ρ (claim p).term)) h) n W h
      (instantiate 0 ρ (claim p).term) := by
  by_cases hs : ∃ j c q, p = .node j (.sub c) [q]
  · obtain ⟨j, c, q, rfl⟩ := hs
    simp only [requiresTree, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hl, hc⟩ := hc
    obtain ⟨eff, hsel⟩ := requiresApp_selected q hc
    refine ⟨eff, by simpa [ExpressionEffects.selectedEffect] using hsel, fun {ρ n W h} he hk hw hh href => ?_⟩
    obtain ⟨hctx, hterm, hsub⟩ := hl
    have ih := requiresApp_sound_exc hcodes hsums q hc hsel (ρ := ρ) (n := n) (W := W) (h := h)
      (by rw [hctx]; exact he) hk hw hh (by simp only [claim] at href; rw [hterm]; exact href)
    rw [hterm] at ih
    exact SafePostExc.consequence_below' (fun _ _ _ _ hv => hv)
      (fun j _ W v hv => PositiveCertificates.acceptedUsing hsub j W v hv) (fun _ _ hp => hp) (fun _ hp => hp) ih
  · have happ : requiresApp G images k codes sums p = true := by
      obtain ⟨j, r, ps⟩ := p
      cases r <;> try (simpa [requiresTree] using hc)
      rcases ps with _ | ⟨q, _ | ⟨q', qs⟩⟩
      · simpa [requiresTree] using hc
      · exact absurd ⟨j, _, q, rfl⟩ hs
      · simpa [requiresTree] using hc
    obtain ⟨eff, hsel⟩ := requiresApp_selected p happ
    exact ⟨eff, hsel, fun he hk hw hh href => requiresApp_sound_exc hcodes hsums p happ hsel he hk hw hh href⟩

/-- Whether an ordinary step's evidence is a call `call-requires` applies to. -/
@[nospecialize] def requiresCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (k : HeapKnowledge.Knowledge) (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) : Bool :=
  match e with
  | .ordinary p =>
    decide (claim p = j) && requiresTree G images k codes sums p
  | _ => false

/-- The inner result type of a call derivation, past an outer coercion. -/
def innerCallType (p : Evidence ι) : Ty ι := match p with
  | .node _ (.sub _) [q] => (claim q).type
  | _ => (claim p).type

/-- Nullish exclusions the selected signature's own result type guarantees on
slot `0` (the call's result), kept when an outer coercion widens that type. -/
def callResultGuardAtoms (G : NormalGraph ι) (p : Evidence ι) : List HeapKnowledge.IndexAtom :=
  let R := innerCallType p
  if !G.plainTy R then [] else
  let cs := PositiveRules.expand G R
  (if cs.all (fun c => tagClause .isNul c == some false) then
    [{ fact := .guarded 0 [] .notNull (.linear (.le [] (-1))) }] else []) ++
  (if cs.all (fun c => tagClause .isUndef c == some false) then
    [{ fact := .guarded 0 [] .notUndef (.linear (.le [] (-1))) }] else [])

omit [DecidableEq ι] in
theorem callResultGuardAtoms_holds {G : NormalGraph ι} {p : Evidence ι} {ρ : Env} {h : Heap} {n W v}
    (hv : meaning G (innerCallType p) n W v) :
    HeapKnowledge.IndexHolds ε (callResultGuardAtoms G p) (push v ρ) h := by
  intro a ha _
  unfold callResultGuardAtoms at ha
  by_cases hp : G.plainTy (innerCallType p) = true
  · simp only [hp, Bool.not_true, Bool.false_eq_true, ite_false] at ha
    rcases List.mem_append.mp ha with ha | ha
    · by_cases hcs : (PositiveRules.expand G (innerCallType p)).all (fun c => tagClause .isNul c == some false) = true
      · simp only [hcs, ite_true, List.mem_singleton] at ha; subst ha
        refine ⟨v, rfl, .inl ?_⟩
        intro hEq; subst hEq
        have hans : Answers G (innerCallType p) .isNul false :=
          ⟨hp, fun c hc => beq_iff_eq.mp (List.all_eq_true.mp hcs c hc)⟩
        have := answers_sound hans hv
        simp [tagHolds] at this
      · simp only [hcs] at ha; cases ha
    · by_cases hcs : (PositiveRules.expand G (innerCallType p)).all (fun c => tagClause .isUndef c == some false) = true
      · simp only [hcs, ite_true, List.mem_singleton] at ha; subst ha
        refine ⟨v, rfl, .inl ?_⟩
        intro hEq; subst hEq
        have hans : Answers G (innerCallType p) .isUndef false :=
          ⟨hp, fun c hc => beq_iff_eq.mp (List.all_eq_true.mp hcs c hc)⟩
        have := answers_sound hans hv
        simp [tagHolds] at this
      · simp only [hcs] at ha; cases ha
  · have hpf : G.plainTy (innerCallType p) = false := Bool.eq_false_iff.mpr hp
    simp only [hpf, Bool.not_false, ite_true] at ha; cases ha

private theorem safePost_withVal {Ξ T U : Fam} {Q R : Post}
    (hsub : ∀ k W v, T k W v → U k W v)
    (hpost : ∀ k W h v, T k W v → Q h v → R h v) :
    ∀ {n W h t}, SafePost Ξ T Q n W h t → SafePost Ξ U R n W h t
  | 0, _, _, _, hs => hs
  | _ + 1, _, _, _, ⟨href, hstep⟩ =>
    ⟨href, match hstep with
      | .inl (.inl ⟨hv, ht, hq⟩) => .inl (.inl ⟨hv, hsub _ _ _ ht, hpost _ _ _ _ ht hq⟩)
      | .inl (.inr hth) => .inl (.inr hth)
      | .inr ⟨W', h', t', hx, ha, st, hh, hs⟩ =>
        .inr ⟨W', h', t', hx, ha, st, hh, safePost_withVal hsub hpost hs⟩⟩

/-- The knowledge after a call at a precondition: every fact where its
signature keeps the heap, else those no call changes, together with any nullish
exclusions the selected signature's own result type guarantees on slot `0`. -/
def requiresOutput (G : NormalGraph ι) (e : HeapExpressionRules.StepEvidence ι) (k : HeapKnowledge.Knowledge) :
    HeapKnowledge.Knowledge :=
  match e with
  | .ordinary p =>
    let base := match ExpressionEffects.selectedEffect p with
      | some eff => promiseOutput eff k
      | none => HeapExpressionRules.ordinaryOutput k
    { base with indices := base.indices ++ callResultGuardAtoms G p }
  | _ => HeapExpressionRules.ordinaryOutput k

theorem requiresCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k : HeapKnowledge.Knowledge} {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hc : requiresCall G images j k e codes sums = true) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds (requiresOutput G e k) ε (push v ρ) h') n W h (instantiate 0 ρ j.term) := by
  unfold requiresCall at hc
  split at hc
  · rename_i p
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨rfl, hc⟩ := hc
    have hfin : ∀ {eff : Effect} {R : Ty ι} (hsel : ExpressionEffects.selectedEffect p = some eff)
        (hR : innerCallType p = R) (hsub : ∀ k' W' v', meaning G R k' W' v' → meaning G (claim p).type k' W' v'),
        SafePost (excOf G) (meaning G R)
          (eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term))
            (ExpressionEffects.actualsOf (instantiate 0 ρ (claim p).term)) h) n W h
          (instantiate 0 ρ (claim p).term) →
        SafePost (excOf G) (meaning G (claim p).type)
          (fun h' v => HeapKnowledge.Holds (requiresOutput G (.ordinary p) k) ε (push v ρ) h') n W h
          (instantiate 0 ρ (claim p).term) := by
      intro eff R hsel hR hsub hs
      refine safePost_withVal hsub (fun k' W' h' v hv hp => ?_) hs
      simp only [requiresOutput, hsel]
      have hpo := promiseOutput_holds (v := v) hk
        (Footprints.intrinsicClasses_ok hh (ExpressionEffects.callEnv_rootsOk_of_refs href))
        (Effect.callPost_within hp)
      exact ⟨hpo.1, hpo.2.1, hpo.2.2.1, hpo.2.2.2.1, hpo.2.2.2.2.1,
        fun a ha hc => (List.mem_append.mp ha).elim (hpo.2.2.2.2.2 a · hc)
          (callResultGuardAtoms_holds (hR ▸ hv) a · hc)⟩
    by_cases hs : ∃ j0 c q, p = .node j0 (.sub c) [q]
    · obtain ⟨j0, c, q, rfl⟩ := hs
      simp only [requiresTree, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hctx, hterm, hsub⟩, hc⟩ := hc
      obtain ⟨eff, hsel⟩ := requiresApp_selected q hc
      have ih := requiresApp_sound hcodes hsums q hc hsel (ρ := ρ) (n := n) (W := W) (h := h)
        (by rw [hctx]; exact he) hk hw hh (by simp only [claim] at href; rw [hterm]; exact href)
      rw [hterm] at ih
      exact hfin (by simpa [ExpressionEffects.selectedEffect] using hsel) rfl
        (fun k' W' v' hv => PositiveCertificates.acceptedUsing hsub k' W' v' hv) ih
    · have happ : requiresApp G images k codes sums p = true := by
        obtain ⟨j0, r, ps⟩ := p
        cases r <;> try (simpa [requiresTree] using hc)
        rcases ps with _ | ⟨q, _ | ⟨q', qs⟩⟩
        · simpa [requiresTree] using hc
        · exact absurd ⟨j0, _, q, rfl⟩ hs
        · simpa [requiresTree] using hc
      obtain ⟨eff, hsel⟩ := requiresApp_selected p happ
      have hR : innerCallType p = (claim p).type := by
        obtain ⟨j0, r, ps⟩ := p
        cases r <;> try rfl
        rcases ps with _ | ⟨q, _ | ⟨q', qs⟩⟩
        · rfl
        · exact absurd ⟨j0, _, q, rfl⟩ hs
        · rfl
      exact hfin hsel hR (fun _ _ _ hv => hv) (requiresApp_sound hcodes hsums p happ hsel he hk hw hh href)
  · cases hc

/-! ### A call stating a postcondition (PROGRAM-TYPING.md, "Reads below the length")

A call whose selected signature states index facts at its normal exit (`ExitSchema.facts`)
returns normally in a heap where each holds at the return's positions: the
result, and the call's receiver and actuals. Renamed to the slots after the
return, the result's slot `0` and each position's slot one higher, each fact
naming slots alone is an atom of the knowledge after the call (`call-ensures`). -/

/-- The slot after a return that a return's position names, where a slot holds
it: `0` the result; `p + 1` the call's position `p`, held by the slot `slots`
gives it, one higher past the result; a receiver that is no slot holds none. -/
def ensuresSlot (recv : Bool) (slots : List Nat) : Nat → Option Nat
  | 0 => some 0
  | p + 1 => if p < slots.length ∧ (p ≠ 0 ∨ recv = true) then some (PointClaims.slot (some slots) p + 1) else none

/-- The atoms a normal return of the call `t` at `eff` states, at the slots
after the return: each result fact naming no entry term every position of
which a slot holds, renamed (`call-ensures`). A fact naming an entry term
relates the states before and after the call, and enters the caller's facts
by composition (`ensuresComposed`). -/
def ensuresAtoms (eff : Effect) (t : Tm) : List HeapKnowledge.IndexAtom :=
  match callSlots t with
  | some (recv, slots) => HeapKnowledge.mapIndices (ensuresSlot recv slots)
      ((eff.schema.normal.facts.filter (·.entrySlots.isEmpty)).map fun F => { fact := F })
  | none => []

theorem ensuresAtoms_holds {eff : Effect} {t : Tm} {ρ : Env} {h' : Heap} {v : Tm}
    (hp : ∀ F ∈ eff.schema.normal.facts, F.entrySlots = [] →
      F.HoldsAt ε (CallEffects.ensuresEnv v (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h') :
    HeapKnowledge.IndexHolds ε (ensuresAtoms eff t) (push v ρ) h' := by
  unfold ensuresAtoms
  split
  · rename_i recv slots hs
    refine HeapKnowledge.mapIndices_holds (ρ := CallEffects.ensuresEnv v (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t))) (fun s t' hst => ?_) ?_
    · cases s with
      | zero =>
        simp only [ensuresSlot, Option.some.injEq] at hst
        subst hst
        rfl
      | succ p =>
        simp only [ensuresSlot] at hst
        split at hst
        · rename_i hc
          simp only [Option.some.injEq] at hst
          subst hst
          have he := callSlots_env hs ρ p hc.1 hc.2
          simp only [PointClaims.mapEnv] at he
          simp only [push, CallEffects.ensuresEnv, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
          exact he
        · cases hst
    · intro a ha _
      obtain ⟨F, hF, rfl⟩ := List.mem_map.mp ha
      obtain ⟨hF, he⟩ := List.mem_filter.mp hF
      exact hp F hF (by simpa using he)
  · exact HeapKnowledge.indexHolds_nil _ _

/-- The change of a call growing its receiver's spine (`ReceiverGrows`):
no object or number altered, every spine grown. -/
def growChanges : HeapKnowledge.Changes := ⟨false, false, .grow⟩

theorem receiverGrows_changes {r : Tm} {h h' : Heap} (hg : CallEffects.ReceiverGrows r h h') :
    growChanges.Holds h h' := by
  refine ⟨fun l v hv ha => ?_, fun hs => by simp [growChanges] at hs, fun _ l ls hls => ?_⟩
  · rcases hg l v hv with hk | ⟨-, ls, ls', rfl, -⟩
    · exact hk
    · simp [growChanges, HeapKnowledge.Changes.alters] at ha
  · rcases hg l _ hls with hk | ⟨-, ls₀, ls', he, hls', hle, hmax⟩
    · exact ⟨ls, hk, Nat.le_refl _, id⟩
    · cases he; exact ⟨ls', hls', hle.length_le, fun _ => hmax⟩

/-- **The first fields a call growing the receiver slot `i`'s spine keeps**:
each field of a slot that the one disjointness check of the call's entry
(`knowledgeQuery`) separates from `i`'s spine field. A growth changes no
location but the receiver's spine. -/
def growFirst (k : HeapKnowledge.Knowledge) (t : Tm) : Nat → String → Bool :=
  match receiverSlot t with
  | some i => fun s g => (Footprints.knowledgeQuery k).disjoint (.field s (.str g)) (.field i arraySpineKey)
  | none => fun _ _ => false

theorem growFirst_kept {k : HeapKnowledge.Knowledge} {t : Tm} {ρ : Env} {h h' : Heap} {nw : Nat} {W : WorldT nw}
    (hk : HeapKnowledge.Holds k ε ρ h) (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hg : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h') :
    HeapKnowledge.FirstKept (growFirst k t) ρ h h' := by
  intro s g fs cd o l v hf hs hl hv
  cases hi : receiverSlot t with
  | none => simp [growFirst, hi] at hf
  | some i =>
    simp only [growFirst, hi] at hf
    obtain ⟨f, args, rfl⟩ := receiverSlot_term hi
    rcases hg l v hv with hk' | ⟨hst, -⟩
    · exact hk'
    · simp only [ExpressionEffects.receiverOf, instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hst
      exact (Footprints.knowledgeQuery_sound hk hok hρ _ _ l (List.getElem?_eq_some_iff.mp hv).1 hf
        (by simp [Footprints.Region.mem, hs, Footprints.fieldsOf, hl])
        (by simpa [Footprints.Region.mem] using Footprints.spineOf_lookup hst)).elim

/-! The check answers every pair the allocations' separations and the
region facts answered for a growth: a field of a slot apart from every own
location of the receiver (`HeapSeparation.apartAll`), or from its spine
field in either orientation (`HeapSeparation.apart`), and a slot's spine
whose array the check keeps apart from the receiver's
(`IndexWrites.apartFrom`). -/

theorem growFirst_apartAll {k : HeapKnowledge.Knowledge} {f : Tm} {i : Nat} {args : List Tm} {s : Nat} {g : String}
    (ha : HeapSeparation.apartAll k.separation i s (.str g) = true) :
    growFirst k (.invoke f (.var i) args) s g = true := by
  simp only [HeapSeparation.apartAll, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at ha
  obtain ⟨⟨hid, hsd⟩, a, ham, ⟨hsl, hfl⟩, hkey⟩ := ha
  obtain ⟨p, hp, hpk⟩ := List.any_eq_true.mp hkey
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hpk
  obtain ⟨hp1, hg⟩ := hpk
  have hmem : Footprints.SepFact.locs i none s (.str g) ∈ Footprints.separationFacts k.separation := by
    simp only [Footprints.separationFacts, List.mem_flatMap, List.mem_map]
    refine ⟨a, ham, p, hp, .str g, hg, ?_⟩
    rw [hfl, hp1]; congr 1 <;> omega
  simp only [growFirst, receiverSlot, Footprints.knowledgeQuery]
  rw [Footprints.SepEvidence.query_symm]
  exact Footprints.SepEvidence.query_fact _ (f := .locs i none s (.str g))
    (by simp [Footprints.knowledgeEvidence, hmem])
    (by simp [Footprints.SepEvidence.byFact, Footprints.fieldSite, Footprints.slotsOf_self, HeapSeparation.covers])

theorem growFirst_apart {k : HeapKnowledge.Knowledge} {f : Tm} {i : Nat} {args : List Tm} {s : Nat} {g : String}
    (ha : HeapSeparation.apart k.separation i arraySpineKey s (.str g) = true) :
    growFirst k (.invoke f (.var i) args) s g = true := by
  simp only [HeapSeparation.apart, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.or_eq_true,
    beq_iff_eq] at ha
  obtain ⟨⟨hid, hsd⟩, a, ham, hcase⟩ := ha
  simp only [growFirst, receiverSlot, Footprints.knowledgeQuery]
  rcases hcase with ⟨⟨hsl, hc⟩, hkey⟩ | ⟨⟨hsl, hc⟩, hkey⟩
  · obtain ⟨p, hp, hpk⟩ := List.any_eq_true.mp hkey
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hpk
    obtain ⟨hp1, hg⟩ := hpk
    have hmem : Footprints.SepFact.locs i a.fields s (.str g) ∈ Footprints.separationFacts k.separation := by
      simp only [Footprints.separationFacts, List.mem_flatMap, List.mem_map]
      refine ⟨a, ham, p, hp, .str g, hg, ?_⟩
      rw [hp1]; congr 1 <;> omega
    rw [Footprints.SepEvidence.query_symm]
    exact Footprints.SepEvidence.query_fact _ (f := .locs i a.fields s (.str g))
      (by simp [Footprints.knowledgeEvidence, hmem])
      (by simp [Footprints.SepEvidence.byFact, Footprints.fieldSite, Footprints.slotsOf_self, hc])
  · obtain ⟨p, hp, hpk⟩ := List.any_eq_true.mp hkey
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hpk
    obtain ⟨hp1, hg⟩ := hpk
    have hmem : Footprints.SepFact.locs s a.fields i arraySpineKey ∈ Footprints.separationFacts k.separation := by
      simp only [Footprints.separationFacts, List.mem_flatMap, List.mem_map]
      refine ⟨a, ham, p, hp, arraySpineKey, hg, ?_⟩
      rw [hp1]; congr 1 <;> omega
    exact Footprints.SepEvidence.query_fact _ (f := .locs s a.fields i arraySpineKey)
      (by simp [Footprints.knowledgeEvidence, hmem])
      (by simp [Footprints.SepEvidence.byFact, Footprints.fieldSite, Footprints.slotsOf_self, hc])

theorem growFirst_apartFrom {k : HeapKnowledge.Knowledge} {f : Tm} {i : Nat} {args : List Tm} {s : Nat}
    (ha : IndexWrites.apartFrom k i s = true) :
    growFirst k (.invoke f (.var i) args) s "[]" = true := by
  simp only [IndexWrites.apartFrom, Bool.and_eq_true] at ha
  simp only [growFirst, receiverSlot, Footprints.knowledgeQuery] at ha ⊢
  rw [Footprints.SepEvidence.query_symm]
  exact ha.1.1.1

/-! ### A call's frame at the caller's slots -/

/-- The caller's slot holding a call position's value: `0` the receiver, `p`
the `p`-th actual, each a slot of the caller. -/
def actualSlot (t : Tm) (p : Nat) : Option Nat :=
  match t with
  | .invoke _ r args =>
    if p = 0 then (match r with | .var j => some j | _ => none)
    else match args[p - 1]? with
      | some (.var j) => some j
      | _ => none
  | _ => none

theorem actualSlot_sound {t : Tm} {p j : Nat} (h : actualSlot t p = some j) (ρ : Env) :
    CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t)) p = ρ j := by
  cases t <;> simp only [actualSlot, reduceCtorEq] at h
  rename_i f r args
  simp only [CallEffects.callEnv, ExpressionEffects.receiverOf, ExpressionEffects.actualsOf, instantiate]
  by_cases hp : p = 0
  · subst hp
    simp only [ite_true] at h ⊢
    cases r <;> simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    simp [instantiate]
  · simp only [hp, ite_false] at h ⊢
    cases ha : args[p - 1]? with
    | none => rw [ha] at h; cases h
    | some a =>
      rw [ha] at h
      cases a <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      rw [List.getD_eq_getElem?_getD, instantiateArgs_eq_map, List.getElem?_map, ha]
      simp [instantiate]

/-- **A call's frame at the caller's slots** (`Effect.frame` read at the
call's positions, `Footprint.renameM`): each position the caller passes a
slot at reads as that slot, any other position's regions widen to every
location. -/
def callerFrame (eff : Effect) (t : Tm) : Footprints.Footprint := (eff.frame.renameM (actualSlot t)).byClass

/-- The call's frame at the caller's slots bounds the call. -/
theorem callerFrame_post {eff : Effect} {t : Tm} {ρ : Env} {h h' : Heap}
    (hw : eff.within (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h') :
    Footprints.Post (callerFrame eff t) ρ h h' :=
  (Footprints.Post.renameM (fun _ _ hij => (actualSlot_sound hij ρ).symm) hw).byClass

/-- **The separation query at a call**: the entry knowledge's separation
evidence combined with type-disjoint array spine apartness (`typeSpineQuery`). -/
@[nospecialize] def callQuery (G : NormalGraph ι) (Γ : List (Ty ι)) (k : HeapKnowledge.Knowledge) :
    Footprints.SepQuery :=
  (Footprints.knowledgeQuery k).or (HeapExpressionRules.typeSpineQuery G Γ)

theorem callQuery_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {k : HeapKnowledge.Knowledge}
    {ρ : Env} {nw : Nat} {W : WorldT (nw + 4)} {h : Heap}
    (he : EnvOk G Γ ρ (nw + 4) W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ) :
    (callQuery G Γ k).Sound ρ h :=
  Footprints.SepQuery.or_sound (Footprints.knowledgeQuery_sound hk hok hρ)
    (HeapExpressionRules.typeSpineQuery_sound he hok hρ)

/-- Whether a call growing its receiver's spine keeps the spine of `(s, p)`:
the call's separation query separates `(s, p)["[]"]` from the receiver's `"[]"`. -/
@[nospecialize] def growSpineKept (G : NormalGraph ι) (Γ : List (Ty ι)) (k : HeapKnowledge.Knowledge)
    (t : Tm) (s : Nat) (p : List String) : Bool :=
  match receiverSlot t with
  | some i => (callQuery G Γ k).disjoint (.path s p arraySpineKey) (.field i arraySpineKey)
  | none => false

theorem growSpineKept_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {k : HeapKnowledge.Knowledge}
    {t : Tm} {s : Nat} {p : List String} {ρ : Env} {nw : Nat} {W : WorldT (nw + 4)} {h h' : Heap}
    (he : EnvOk G Γ ρ (nw + 4) W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hg : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (hkept : growSpineKept G Γ k t s p = true) {w : Val} {st : Nat} {ls : List (Option Nat)}
    (hw : HeapKnowledge.readPath h (ρ s) p = some w) (hsp : Footprints.spineOf w = some st)
    (hls : h[st]? = some (.arr ls)) : h'[st]? = some (.arr ls) := by
  cases hi : receiverSlot t with
  | none => simp [growSpineKept, hi] at hkept
  | some i =>
    simp only [growSpineKept, hi] at hkept
    obtain ⟨f, args, rfl⟩ := receiverSlot_term hi
    rcases hg st _ hls with hk' | ⟨hst, -⟩
    · exact hk'
    · simp only [ExpressionEffects.receiverOf, instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hst
      exact (callQuery_sound he hk hok hρ _ _ st (List.getElem?_eq_some_iff.mp hls).1 hkept
        (by simp [Footprints.Region.mem, hw, Footprints.spineOf_lookup hsp])
        (by simpa [Footprints.Region.mem] using Footprints.spineOf_lookup hst)).elim

/-- Whether a call growing its receiver's spine keeps the element spines of
`(s, p)`: the call's separation query separates `elemSpines s p` from the
receiver's `"[]"`. -/
@[nospecialize] def growElemSpinesKept (G : NormalGraph ι) (Γ : List (Ty ι)) (k : HeapKnowledge.Knowledge)
    (t : Tm) (s : Nat) (p : List String) : Bool :=
  match receiverSlot t with
  | some i => (callQuery G Γ k).disjoint (.elemSpines s p) (.field i arraySpineKey)
  | none => false

theorem growElemSpinesKept_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {k : HeapKnowledge.Knowledge}
    {t : Tm} {s : Nat} {p : List String} {ρ : Env} {nw : Nat} {W : WorldT (nw + 4)} {h h' : Heap}
    (he : EnvOk G Γ ρ (nw + 4) W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hg : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (hkept : growElemSpinesKept G Γ k t s p = true)
    {w v : Val} {st j l stv : Nat} {ls : List (Option Nat)} {uv : Val}
    (hw : HeapKnowledge.readPath h (ρ s) p = some w) (hel : HeapKnowledge.elementsOf w = some st)
    (hls : h[st]?.bind spineEntries = some ls) (hl : ls[j]? = some (some l))
    (hv : h[l]? = some v) (hsv : Footprints.spineOf v = some stv) (huv : h[stv]? = some uv) :
    h'[stv]? = some uv := by
  cases hi : receiverSlot t with
  | none => simp [growElemSpinesKept, hi] at hkept
  | some i =>
    simp only [growElemSpinesKept, hi] at hkept
    obtain ⟨f, args, rfl⟩ := receiverSlot_term hi
    rcases hg stv uv huv with hk' | ⟨hsp_i, -⟩
    · exact hk'
    · exfalso
      simp only [ExpressionEffects.receiverOf, instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hsp_i
      have hcells : some l ∈ Footprints.spineCells h w :=
        Footprints.elementsOf_entries_sub hel (by simp [Footprints.entriesAt, hls, List.mem_of_getElem? hl])
      have hmem_elem : (Footprints.Region.elemSpines s p).mem ρ h stv = true := by
        simp only [Footprints.Region.mem, hw, List.any_eq_true]
        refine ⟨some l, hcells, ?_⟩
        simp only [hv, beq_iff_eq]
        exact Footprints.spineOf_lookup hsv
      exact callQuery_sound he hk hok hρ _ _ stv (List.getElem?_eq_some_iff.mp huv).1 hkept hmem_elem
        (by simpa [Footprints.Region.mem] using Footprints.spineOf_lookup hsp_i)

/-- **A call's fact kept by its frame** (the note's Frame): the fact has a support that every entry of the call's frame at the
caller's slots (`callerFrame`) respects under the query of the call's entry
(`IndexFact.keeps`, FOOTPRINTS.md "Support and respect") or under the call's
type-disjoint spine query (`callQuery`); where a support or the evidence is
missing the check fails. -/
@[nospecialize] def frameKeeps (G : NormalGraph ι) (Γ : List (Ty ι)) (stable : Nat → String → Bool)
    (arrayPath : Nat → List String → Bool) (eff : Effect) (t : Tm) (k : HeapKnowledge.Knowledge)
    (a : HeapKnowledge.IndexAtom) : Bool :=
  let c : Footprints.ReadContext := { (Footprints.ReadContext.ofFirst stable) with arrayPath }
  a.fact.keepsUnder k c (callerFrame eff t) [] || a.fact.keeps (callQuery G Γ k) c (callerFrame eff t)

/-- **A call's cell facts kept by its frame** (the note's Frame, at cell
facts): those of the call's entry whose support in the call's read context
(`FactKind.supportIn` at `ReadContext.ofFirst stable`: the field location
they read at `keep`, left out where the call keeps that first field), the
call's frame at the caller's slots respects under the entry's query
(`respects`, the note's Definition "Respect"), renamed past the result. -/
def frameCells (stable : Nat → String → Bool) (eff : Effect) (t : Tm) (k : HeapKnowledge.Knowledge) :
    HeapFacts.Facts :=
  let q := Footprints.knowledgeQuery k
  let c := Footprints.ReadContext.ofFirst stable
  let Φ := callerFrame eff t
  (k.cells.filter fun f => Footprints.respects q
    ((Footprints.FactKind.cell f).supportIn c) Φ).map
    fun f => { f with slot := f.slot + 1 }

/-- **The frame keeps the cell facts it respects** (the note's Theorem
"Tolerant frame", `frame_step` at cell facts, under the call's read
context): each holds on the call's normal return, past the result. -/
theorem frameCells_holds {stable : Nat → String → Bool} {eff : Effect} {t : Tm} {k : HeapKnowledge.Knowledge}
    {ρ : Env} {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT nw} (hk : HeapKnowledge.Holds k ε ρ h)
    (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v)
    (hstable : HeapKnowledge.FirstKept stable ρ h h') :
    HeapFacts.Holds (frameCells stable eff t k) (push v ρ) h' := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
  obtain ⟨hfm, hr⟩ := List.mem_filter.mp hf
  have hF : (Footprints.FactKind.cell f).Holds ρ h := fun f' hf' => by
    rw [List.mem_singleton.mp hf']; exact hk.1 f hfm
  obtain ⟨flds, c, oid, w, hρs, hrd, hm⟩ :=
    Footprints.frame_step (D := Footprints.heaps) (m := 0)
      (Footprints.FactKind.supportsIn (.ofFirst stable) (.cell f)) hr
      (Footprints.knowledgeQuery_sound hk hok hρ)
      (callerFrame_post (CallEffects.Effect.callPost_within hq)) trivial
      (Footprints.ReadContext.ofFirst_holds hstable) hF f (List.mem_singleton_self _)
  exact ⟨flds, c, oid, w, by simpa [push] using hρs, hrd, hm⟩

/-- **A call's read links kept by its frame** (the note's Frame, at read
links): those of the call's entry whose support in the call's read context
(`FactKind.supportIn` at `ReadContext.ofFirst stable`: the field location
they read at `keep`, left out where the call keeps that first field), the
call's frame at the caller's slots respects under the entry's query
(`respects`, the note's Definition "Respect"), renamed past the result. -/
def frameLinks (stable : Nat → String → Bool) (eff : Effect) (t : Tm) (k : HeapKnowledge.Knowledge) :
    HeapLinks.Links :=
  let q := Footprints.knowledgeQuery k
  let c := Footprints.ReadContext.ofFirst stable
  let Φ := callerFrame eff t
  (k.links.filter fun g => !g.alias && Footprints.respects q
    ((Footprints.FactKind.link g).supportIn c) Φ).map
    fun g => { g with cell := g.cell + 1, value := g.value + 1 }

/-- **The frame keeps the read links it respects** (the note's Theorem
"Tolerant frame", `frame_step` at read links, under the call's read
context): each holds on the call's normal return, past the result. -/
theorem frameLinks_holds {stable : Nat → String → Bool} {eff : Effect} {t : Tm} {k : HeapKnowledge.Knowledge}
    {ρ : Env} {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT nw} (hk : HeapKnowledge.Holds k ε ρ h)
    (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v)
    (hstable : HeapKnowledge.FirstKept stable ρ h h') :
    HeapLinks.Holds (frameLinks stable eff t k) (push v ρ) h' := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  obtain ⟨hgm, hr⟩ := List.mem_filter.mp hg0
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hr
  have hF : (Footprints.FactKind.link g0).Holds ρ h := fun g' hg' => by
    rw [List.mem_singleton.mp hg']; exact hk.2.2.1 g0 hgm
  have hres :=
    Footprints.frame_step (D := Footprints.heaps) (m := 0)
      (Footprints.FactKind.supportsIn (.ofFirst stable) (.link g0)) hr.2
      (Footprints.knowledgeQuery_sound hk hok hρ)
      (callerFrame_post (CallEffects.Effect.callPost_within hq)) trivial
      (Footprints.ReadContext.ofFirst_holds hstable) hF g0 (List.mem_singleton_self _)
  simpa [push] using hres

/-- The change of a typed array's element write: spines keep their lengths,
nothing else changes. -/
def writeChanges : HeapKnowledge.Changes := CallEffects.ElementWrite.changes .spines

/-! ### The normal exit's postconditions a call's Entry rules read

Each derived rule of the note's Entry at a call is triggered by the
postconditions it needs among the normal exit's postconditions of the
signature's schema (`Effect.schema`, stated once for every arity): the
receiver spine's frame and extension, the append of the actuals, the views'
growth, View-Write at an element type's format with its precondition's
facts. The contract each rule's soundness reads is derived from those
formulas at the call (`Effect.callPost_spineGrows`,
`Effect.callPost_appends`, `Effect.callPost_viewGrowth`,
`Effect.callPost_exactWrite`). -/

/-- The normal exit's postconditions of a call's signature, as its schema
states them. -/
def callPosts (eff : Effect) : List Parity.FormulaSchema := eff.schema.normal.ensures

/-- The normal exit states the receiver's spine's frame `{receiver spine:
any}` and its extension (`spineExtends`): together, its growth
(`receiverGrows_iff`). -/
def statesExtension (eff : Effect) : Bool :=
  (callPosts eff).contains (.transition [(.field 0 arraySpineKey, .any)]) &&
    (callPosts eff).contains (.operation (.spineExtends 0))

/-- The normal exit states the append of the actuals to the receiver
(`push` of the actuals from position `1` on). -/
def statesAppend (eff : Effect) : Bool :=
  (callPosts eff).contains (.operation (.push 0 1 (.restFrom 1)))

/-- The normal exit states the views' growth, `{views: grow}`, a typed
array's element write's frame (`Kinds.ViewWrite.frame_iff`). -/
def statesViewGrowth (eff : Effect) : Bool :=
  (callPosts eff).contains (.transition [(.cls .views, .grow)])

/-- The element type of the exact element write the normal exit states:
View-Write at a format, and each fact of its element type's precondition
read at the entry. -/
def exactWriteOf (eff : Effect) : Option CallEffects.ElementKind :=
  (callPosts eff).findSome? fun F => match F with
    | .operation (.viewWrite 1 2 3 (some f)) =>
      if (CallEffects.ElementKind.ofFormat f).preFacts.all fun G => (callPosts eff).contains (.operation (.fact .before 0 G))
      then some (CallEffects.ElementKind.ofFormat f) else none
    | _ => none

theorem statesExtension_grows {eff : Effect} (h : statesExtension eff = true) {r : Tm} {args : List Tm}
    {before after : Heap} {v : Tm} (hp : eff.callPost r args before after v) :
    CallEffects.ReceiverGrows r before after := by
  simp only [statesExtension, Bool.and_eq_true, List.contains_iff_mem] at h
  exact CallEffects.Effect.callPost_spineGrows h.1 h.2 hp

theorem statesAppend_appends {eff : Effect} (h : statesAppend eff = true) {r : Tm} {args : List Tm}
    {before after : Heap} {v : Tm} (hp : eff.callPost r args before after v) :
    CallEffects.ReceiverAppends r args before after :=
  CallEffects.Effect.callPost_appends (List.contains_iff_mem.mp h) hp

theorem statesViewGrowth_changes {eff : Effect} (h : statesViewGrowth eff = true) {r : Tm} {args : List Tm}
    {before after : Heap} {v : Tm} (hp : eff.callPost r args before after v) :
    writeChanges.Holds before after :=
  CallEffects.Effect.callPost_viewGrowth (List.contains_iff_mem.mp h) hp

theorem exactWriteOf_exact {eff : Effect} {k : CallEffects.ElementKind} (h : exactWriteOf eff = some k) {r : Tm}
    {args : List Tm} {before after : Heap} {v : Tm} (hp : eff.callPost r args before after v) :
    CallEffects.ExactWrite k args before after ∧ CallEffects.ExactPre k args := by
  obtain ⟨F, hF, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · rename_i f
    split at hk
    · rename_i hall
      cases hk
      refine CallEffects.Effect.callPost_exactWrite (k := CallEffects.ElementKind.ofFormat f) ?_ ?_ hp
      · rw [CallEffects.ElementKind.format_ofFormat]; exact hF
      · intro G hG
        exact List.contains_iff_mem.mp (List.all_eq_true.mp hall G hG)
    · cases hk
  · cases hk

/-- **An admitted contract's exact write is established by its caller**
(proved): where the contract was admitted (`Effect.exactWritesRequired`, the
effect reader's check), the range facts the exact write reads (`ExactPre`)
hold at every call meeting its precondition; a contract read from a
document states no range its callers do not establish. -/
theorem exactWriteOf_requires {eff : Effect} {k : CallEffects.ElementKind} (h : exactWriteOf eff = some k)
    (hadm : eff.exactWritesRequired = true) {r : Tm} {args : List Tm} {heap : Heap}
    (hq : eff.Requires r args heap) : CallEffects.ExactPre k args := by
  obtain ⟨F, hF, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · rename_i f
    split at hk
    · cases hk
      exact CallEffects.ElementKind.exactPre_of_requires (CallEffects.Effect.exactWrite_pre hadm hF) hq
    · cases hk
  · cases hk

/-- The heap-reading atoms of a call's entry its normal exit keeps, renamed
past the result (`Changes.ofClosed`, ARITHMETIC.md, "Linear facts"): each
atom its frame keeps (`frameKeeps`, the note's Frame); none where its frame
keeps the heap, whose output keeps every atom (`call-keep`). -/
@[nospecialize] def effectKept (G : NormalGraph ι) (Γ : List (Ty ι)) (stable : Nat → String → Bool)
    (arrayPath : Nat → List String → Bool) (eff : Effect) (t : Tm) (k : HeapKnowledge.Knowledge) :
    List HeapKnowledge.IndexAtom :=
  if keepsHeap eff then [] else
  let c : Footprints.ReadContext := { (Footprints.ReadContext.ofFirst stable) with arrayPath }
  let Φ := callerFrame eff t
  let ctx := Footprints.KeepsUnderCtx.ofKnowledge k
  let callQ := Thunk.mk fun _ => callQuery G Γ k
  HeapKnowledge.shiftIndices (k.indices.filter fun a =>
    !a.fact.envOnly && (a.fact.keepsUnderCtx ctx k c Φ [] || a.fact.keeps callQ.get c Φ))

theorem effectKept_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {stable : Nat → String → Bool}
    {arrayPath : Nat → List String → Bool} {eff : Effect} {t : Tm} {k : HeapKnowledge.Knowledge}
    {ρ : Env} {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT (nw + 4)}
    (he : EnvOk G Γ ρ (nw + 4) W) (hk : HeapKnowledge.Holds k ε ρ h) (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v)
    (hst : HeapKnowledge.FirstKept stable ρ h h')
    (harr : ∀ x p w st, arrayPath x p = true → HeapKnowledge.readPath h (ρ x) p = some w →
      HeapKnowledge.elementsOf w = some st →
      Footprints.spineOf w = some st ∧ ∀ ls, h[st]?.bind spineEntries = some ls → h[st]? = some (.arr ls)) :
    HeapKnowledge.IndexHolds ε (effectKept G Γ stable arrayPath eff t k) (push v ρ) h' := by
  have hw := CallEffects.Effect.callPost_within hq
  unfold effectKept
  split
  · exact HeapKnowledge.indexHolds_nil _ _
  · refine HeapKnowledge.shiftIndices_holds fun a ha hcd => ?_
    obtain ⟨ha, hkeep⟩ := List.mem_filter.mp ha
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hkeep
    have hF := hk.2.2.2.2.2 a ha hcd
    rcases hkeep.2 with hku | hkq
    · exact Footprints.IndexFact.keepsUnderCtx_sound (c := { (Footprints.ReadContext.ofFirst stable) with arrayPath }) hk hok hρ
          (callerFrame_post hw) ⟨(Footprints.ReadContext.ofFirst_holds hst).1, harr⟩ a.fact [] (by simp) hku hF
    · exact Footprints.IndexFact.keeps_sound hkq (callQuery_sound he hk hok hρ)
          (callerFrame_post hw) ⟨(Footprints.ReadContext.ofFirst_holds hst).1, harr⟩ hF

/-! ### Quantified facts across a growth (ARITHMETIC.md, "Quantified clauses") -/

open HeapKnowledge in
/-- Every element cell listed by a spine keeps its exact contents across a
growth: in a well-formed heap, an element cell has role `.elem` and never
holds an array spine, so `ReceiverGrows` leaves it untouched. -/
private theorem elemCell_grown {h h' : Heap} {r : Tm} {nw : Nat} {W : WorldT nw}
    {sto : Nat} {ls : List (Option Nat)} {i l : Nat} {v : Val}
    (hok : HeapOk nw W h) (hg : CallEffects.ReceiverGrows r h h')
    (hls : h[sto]?.bind spineEntries = some ls) (hl : ls[i]? = some (some l)) (hv : h[l]? = some v) :
    h'[l]? = some v := by
  rcases hg l v hv with hk' | ⟨-, ls0, -, rfl, -⟩
  · exact hk'
  · have hke : K W .elem l := (hok.kinds.2.2 sto ls hls l (List.mem_of_getElem? hl)).1
    simp only [K, kindAt, Option.map_eq_some_iff] at hke
    obtain ⟨role, hrole, hkrole⟩ := hke
    obtain ⟨u, hu, hsh⟩ := hok.2 l role hrole
    rw [hv] at hu; cases hu
    cases role with
    | spine f => cases f <;> simp [Role.kind] at hkrole
    | _ => simp_all [Role.kind, Shape, Cat, isSourceVal]

open HeapKnowledge in
/-- Whether a call growing its receiver's spine keeps a guard target at an old
index: an empty element path (and, for a parallel array, a shift whose terms
are kept by the growth). -/
def growTargetKept (first : Nat → String → Bool) : ElemTarget → Bool
  | .self ep => ep.isEmpty
  | .parallel _ _ sh ep => ep.isEmpty && sh.keptBy growChanges first

open HeapKnowledge in
/-- Whether a call growing its receiver's spine keeps a body variable's value at
an old index (and at the newly appended slot `pushed`, when given), using
`growElemSpinesKept` / `growSpineKept` to keep element `.length` reads whose
spines are apart from the receiver's spine. -/
@[nospecialize] def growBoundKept (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge)
    (t : Tm) (s : Nat) (p : List String) (first : Nat → String → Bool) (pushed : Option Nat := none) : Bound → Bool
  | .index | .elem => true
  | .project kd ep => (Term.now kd 0 ep).keptBy growChanges (fun _ _ => false) ||
      (kd == .length && ep.isEmpty && growElemSpinesKept G Γ k t s p &&
        match pushed with | none => true | some x => growSpineKept G Γ k t x [])
  | .parallel s' p' sh kd ep => sh.keptBy growChanges first &&
      ((Term.now kd 0 ep).keptBy growChanges (fun _ _ => false) ||
        (kd == .length && ep.isEmpty && growElemSpinesKept G Γ k t s' p'))
  | .free tm => tm.keptBy growChanges first
  | .offset _ => false

open HeapKnowledge in
/-- Whether a call growing its receiver's spine only grows (never shrinks) a
body variable's value at an old index: free lengths, projected lengths, and
parallel element lengths whose shift is kept. -/
def growBoundGrown (first : Nat → String → Bool) : Bound → Bool
  | .project kd ep => (Term.now kd 0 ep).grownBy growChanges (fun _ _ => false)
  | .parallel _ _ sh kd ep => sh.keptBy growChanges first &&
      (Term.now kd 0 ep).grownBy growChanges (fun _ _ => false)
  | .free tm => tm.grownBy growChanges first
  | _ => false

open HeapKnowledge in
/-- Whether a call growing its receiver's spine keeps a quantified body clause
over `(s, p)` at existing indices (and at the newly appended slot `pushed`, when given). -/
@[nospecialize] def growBodyKept (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge)
    (t : Tm) (s : Nat) (p : List String) (first : Nat → String → Bool) (pushed : Option Nat := none) : BodyClause → Bool
  | .clause F => LinearClause.monotone (growBoundKept G Γ k t s p first pushed) (growBoundGrown first) F
  | .guarded tgt _ b => growTargetKept first tgt && growBodyKept G Γ k t s p first pushed b
  | .either A B => growBodyKept G Γ k t s p first pushed A && growBodyKept G Γ k t s p first pushed B

open HeapKnowledge in
private theorem shift_eval_grown {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {r : Tm}
    (hg : CallEffects.ReceiverGrows r h h') (hf : FirstKept first ρ h h')
    {sh : IndexShift} {i j : Nat} (hk : sh.keptBy growChanges first = true)
    (he : sh.eval ε ρ h i = some j) : sh.eval ε ρ h' i = some j := by
  have hc := receiverGrows_changes hg
  have hdef : ∀ (ts : Linear.Form Term),
      (ts.all fun p => p.1.keptBy growChanges first) = true →
      (ts.all fun p => (termValue ε ρ h p.1).isSome) = true →
      (ts.all fun p => (termValue ε ρ h' p.1).isSome) = true ∧
      Linear.Form.eval (termValuation ε ρ h') ts = Linear.Form.eval (termValuation ε ρ h) ts := by
    intro ts
    induction ts with
    | nil => intro _ _; simp [Linear.Form.eval]
    | cons p ts ih =>
      intro hkt hall
      simp only [List.all_cons, Bool.and_eq_true] at hkt hall
      obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hall.1
      have hz' := termValue_kept (ε := ε) hc hf hkt.1 hz
      obtain ⟨hd, hev⟩ := ih hkt.2 hall.2
      exact ⟨by simp [hz', hd], by simp [Linear.Form.eval, termValuation, hz, hz', hev]⟩
  simp only [IndexShift.eval] at he ⊢
  split at he
  · rename_i hall
    obtain ⟨hd, hev⟩ := hdef sh.terms hk hall
    simp only [hd, ↓reduceIte, hev]
    exact he
  · cases he

open HeapKnowledge in
private theorem spine_grown_prefix {h h' : Heap} {r : Tm} {st : Nat} {ls : List (Option Nat)}
    (hg : CallEffects.ReceiverGrows r h h') (hls : h[st]?.bind spineEntries = some ls) :
    ∃ ls', h'[st]?.bind spineEntries = some ls' ∧ ls <+: ls' := by
  obtain ⟨u, hu, hue⟩ := Option.bind_eq_some_iff.mp hls
  rcases hg st u hu with hk | ⟨-, ls0, ls', rfl, hls', hp, -⟩
  · exact ⟨ls, by rw [hk]; exact hue, List.prefix_refl ls⟩
  · simp only [spineEntries, Option.some.injEq] at hue; subst hue
    exact ⟨ls', by rw [hls']; rfl, hp⟩

open HeapKnowledge in
/-- An element guard target kept by a growth (`growTargetKept`) reads the
same value at every old index. -/
private theorem elemTarget_grown {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {r : Tm}
    {nw : Nat} {W : WorldT nw} {sto : Nat} {ls ls' : List (Option Nat)} (i : Nat)
    (hok : HeapOk nw W h) (hg : CallEffects.ReceiverGrows r h h') (hf : FirstKept first ρ h h')
    (hls : h[sto]?.bind spineEntries = some ls) (hp : ls <+: ls') :
    ∀ (t : ElemTarget), growTargetKept first t = true → ∀ w, t.read ε ρ h ls i = some w → t.read ε ρ h' ls' i = some w := by
  intro t ht w hw
  have hc := receiverGrows_changes hg
  cases t with
  | self ep =>
    simp only [growTargetKept, List.isEmpty_iff] at ht
    subst ht
    obtain ⟨tail, rfl⟩ := hp
    simp only [ElemTarget.read] at hw ⊢
    split at hw
    · rename_i l hl
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1, hl]
      obtain ⟨v, hv, hrg⟩ := Option.bind_eq_some_iff.mp hw
      exact Option.bind_eq_some_iff.mpr ⟨v, elemCell_grown hok hg hls hl hv, hrg⟩
    · cases hw
  | parallel s' p' sh ep =>
    simp only [growTargetKept, Bool.and_eq_true, List.isEmpty_iff] at ht
    obtain ⟨rfl, hshK⟩ := ht
    simp only [ElemTarget.read] at hw ⊢
    cases hsh : sh.eval ε ρ h i with
    | none => simp [hsh] at hw
    | some j =>
      simp only [hsh] at hw
      rw [shift_eval_grown hg hf hshK hsh]
      cases hrp : readPath h (ρ s') p' with
      | none => simp [hrp] at hw
      | some arr =>
        simp only [hrp] at hw
        cases hel : elementsOf arr with
        | none => simp [hel] at hw
        | some st2 =>
          simp only [hel] at hw
          have harr : growChanges.alters arr = false := by
            cases arr <;> simp_all [elementsOf, growChanges, Changes.alters]
          rw [readPath_kept hc p' (ρ s') arr hrp (Or.inr harr) (fun _ => rfl)]
          dsimp only
          rw [hel]
          dsimp only
          cases hls2 : h[st2]?.bind spineEntries with
          | none => simp [hls2] at hw
          | some ls2 =>
            simp only [hls2] at hw
            obtain ⟨ls2', hls2', ⟨tail2, rfl⟩⟩ := spine_grown_prefix hg hls2
            rw [hls2']
            dsimp only
            split at hw
            · rename_i l hl
              rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1, hl]
              obtain ⟨v, hv, hrg⟩ := Option.bind_eq_some_iff.mp hw
              exact Option.bind_eq_some_iff.mpr ⟨v, elemCell_grown hok hg hls2 hl hv, hrg⟩
            · cases hw

open HeapKnowledge in
/-- What a body variable denotes at an index a growth keeps: the index and
the element there, each the same, and each projection, parallel element, or
free term kept or grown as `growBoundKept` / `growBoundGrown` allow. -/
theorem boundValue_grown {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {t : Tm}
    {s : Nat} {p : List String} {first : Nat → String → Bool} {pushed : Option Nat} {ρ : Env} {h h' : Heap}
    {nw : Nat} {W : WorldT (nw + 4)} {w_r : Val} {sto : Nat} {ls ls' : List (Option Nat)} (i : Nat)
    (he : EnvOk G Γ ρ (nw + 4) W) (hk : Holds k ε ρ h)
    (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hg : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (hf : FirstKept first ρ h h')
    (hwr : readPath h (ρ s) p = some w_r) (hsto : elementsOf w_r = some sto)
    (hls : h[sto]?.bind spineEntries = some ls) (hp : ls <+: ls') :
    (∀ x n, growBoundKept G Γ k t s p first pushed x = true → boundValue ε ρ h ls i x = some n →
      boundValue ε ρ h' ls' i x = some n) ∧
    (∀ x n, growBoundGrown first x = true → boundValue ε ρ h ls i x = some n →
      ∃ n', boundValue ε ρ h' ls' i x = some n' ∧ n ≤ n') := by
  have hc := receiverGrows_changes hg
  obtain ⟨tail, rfl⟩ := hp
  refine ⟨fun x n hkx hx => ?_, fun x n hgx hx => ?_⟩
  · cases x with
    | index => exact hx
    | offset _ => simp [growBoundKept] at hkx
    | free tm => exact termValue_kept (ε := ε) hc hf hkx hx
    | elem =>
      simp only [boundValue, elementInt] at hx ⊢
      split at hx
      · rename_i l hl
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1, hl]
        simp only [Option.bind_eq_some_iff] at hx ⊢
        obtain ⟨w, hw, hwn⟩ := hx
        exact ⟨w, elemCell_grown hok hg hls hl hw, hwn⟩
      · cases hx
    | project kd ep =>
      simp only [boundValue] at hx ⊢
      split at hx
      · rename_i l hl
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1, hl]
        obtain ⟨w, hw, hwn⟩ := Option.bind_eq_some_iff.mp hx
        refine Option.bind_eq_some_iff.mpr ⟨w, elemCell_grown hok hg hls hl hw, ?_⟩
        simp only [growBoundKept, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hkx
        rcases hkx with htk | ⟨⟨⟨rfl, rfl⟩, hsp⟩, -⟩
        · exact termValue_kept (ε := ε) hc firstKept_none htk hwn
        · simp only [termValue, termAt, readPath, kindValue, Option.bind_some] at hwn ⊢
          obtain ⟨stv, lsv, hsv, hlsv, rfl, hmax⟩ := lengthOf_spine hwn
          exact lengthOf_of_spine hsv (growElemSpinesKept_sound he hk hok hρ hg hsp hwr hsto hls hl hw hsv hlsv) hmax
      · cases hx
    | parallel s' p' sh kd ep =>
      simp only [growBoundKept, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.isEmpty_iff] at hkx
      obtain ⟨hshK, hkdK⟩ := hkx
      simp only [boundValue] at hx ⊢
      cases hsh : sh.eval ε ρ h i with
      | none => simp [hsh] at hx
      | some j =>
        simp only [hsh] at hx
        rw [shift_eval_grown hg hf hshK hsh]
        cases hrp : readPath h (ρ s') p' with
        | none => simp [hrp] at hx
        | some arr =>
          simp only [hrp] at hx
          cases hel : elementsOf arr with
          | none => simp [hel] at hx
          | some st2 =>
            simp only [hel] at hx
            have harr : growChanges.alters arr = false := by
              cases arr <;> simp_all [elementsOf, growChanges, Changes.alters]
            rw [readPath_kept hc p' (ρ s') arr hrp (Or.inr harr) (fun _ => rfl)]
            dsimp only
            rw [hel]
            dsimp only
            cases hls2 : h[st2]?.bind spineEntries with
            | none => simp [hls2] at hx
            | some ls2 =>
              simp only [hls2] at hx
              obtain ⟨ls2', hls2', ⟨tail2, rfl⟩⟩ := spine_grown_prefix hg hls2
              rw [hls2']
              dsimp only
              split at hx
              · rename_i l hl
                rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1, hl]
                obtain ⟨w, hw, hwn⟩ := Option.bind_eq_some_iff.mp hx
                refine Option.bind_eq_some_iff.mpr ⟨w, elemCell_grown hok hg hls2 hl hw, ?_⟩
                rcases hkdK with htk | ⟨⟨rfl, rfl⟩, hsp⟩
                · exact termValue_kept (ε := ε) hc firstKept_none htk hwn
                · simp only [termValue, termAt, readPath, kindValue, Option.bind_some] at hwn ⊢
                  obtain ⟨stv, lsv, hsv, hlsv, rfl, hmax⟩ := lengthOf_spine hwn
                  exact lengthOf_of_spine hsv (growElemSpinesKept_sound he hk hok hρ hg hsp hrp hel hls2 hl hw hsv hlsv) hmax
              · cases hx
  · cases x with
    | index | elem | offset _ => simp [growBoundGrown] at hgx
    | free tm => exact termValue_grown (ε := ε) hc hf hgx hx
    | project kd ep =>
      simp only [boundValue] at hx ⊢
      split at hx
      · rename_i l hl
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1, hl]
        obtain ⟨w, hw, hwn⟩ := Option.bind_eq_some_iff.mp hx
        obtain ⟨n', hn', hle⟩ := termValue_grown (ε := ε) hc firstKept_none hgx hwn
        exact ⟨n', Option.bind_eq_some_iff.mpr ⟨w, elemCell_grown hok hg hls hl hw, hn'⟩, hle⟩
      · cases hx
    | parallel s' p' sh kd ep =>
      simp only [growBoundGrown, Bool.and_eq_true] at hgx
      obtain ⟨hshK, hkdG⟩ := hgx
      simp only [boundValue] at hx ⊢
      cases hsh : sh.eval ε ρ h i with
      | none => simp [hsh] at hx
      | some j =>
        simp only [hsh] at hx
        rw [shift_eval_grown hg hf hshK hsh]
        cases hrp : readPath h (ρ s') p' with
        | none => simp [hrp] at hx
        | some arr =>
          simp only [hrp] at hx
          cases hel : elementsOf arr with
          | none => simp [hel] at hx
          | some st2 =>
            simp only [hel] at hx
            have harr : growChanges.alters arr = false := by
              cases arr <;> simp_all [elementsOf, growChanges, Changes.alters]
            rw [readPath_kept hc p' (ρ s') arr hrp (Or.inr harr) (fun _ => rfl)]
            dsimp only
            rw [hel]
            dsimp only
            cases hls2 : h[st2]?.bind spineEntries with
            | none => simp [hls2] at hx
            | some ls2 =>
              simp only [hls2] at hx
              obtain ⟨ls2', hls2', ⟨tail2, rfl⟩⟩ := spine_grown_prefix hg hls2
              rw [hls2']
              dsimp only
              split at hx
              · rename_i l hl
                rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1, hl]
                obtain ⟨w, hw, hwn⟩ := Option.bind_eq_some_iff.mp hx
                obtain ⟨n', hn', hle⟩ := termValue_grown (ε := ε) hc firstKept_none hkdG hwn
                exact ⟨n', Option.bind_eq_some_iff.mpr ⟨w, elemCell_grown hok hg hls2 hl hw, hn'⟩, hle⟩
              · cases hx

open HeapKnowledge in
private theorem growBodyKept_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {t : Tm}
    {s : Nat} {p : List String} {first : Nat → String → Bool} {pushed : Option Nat} {ρ : Env} {h h' : Heap}
    {nw : Nat} {W : WorldT (nw + 4)} {w_r : Val} {sto : Nat} {ls ls' : List (Option Nat)} (i : Nat)
    (he : EnvOk G Γ ρ (nw + 4) W) (hk : Holds k ε ρ h)
    (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hg : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (hf : FirstKept first ρ h h')
    (hwr : readPath h (ρ s) p = some w_r) (hsto : elementsOf w_r = some sto)
    (hls : h[sto]?.bind spineEntries = some ls) (hp : ls <+: ls') :
    ∀ {B : BodyClause}, growBodyKept G Γ k t s p first pushed B = true →
      B.HoldsAt ε ρ h ls i → B.HoldsAt ε ρ h' ls' i
  | .clause F, hbk, hF => by
    obtain ⟨hkv, hgv⟩ := boundValue_grown (pushed := pushed) i he hk hok hρ hg hf hwr hsto hls hp
    exact LinearClause.holdsAt_monotone hkv hgv hbk hF
  | .guarded tgt g b, hbk, hB => by
    simp only [growBodyKept, Bool.and_eq_true] at hbk
    have ht := elemTarget_grown (ε := ε) i hok hg hf hls hp tgt hbk.1
    rcases hB with ⟨w, hw, hg0⟩ | ⟨hpres, hb⟩
    · exact .inl ⟨w, ht w hw, hg0⟩
    · exact .inr ⟨fun hne => let ⟨w, hw⟩ := hpres hne; ⟨w, ht w hw⟩,
        growBodyKept_holds (pushed := pushed) i he hk hok hρ hg hf hwr hsto hls hp hbk.2 hb⟩
  | .either A B, hbk, hB => by
    simp only [growBodyKept, Bool.and_eq_true] at hbk
    exact hB.imp (growBodyKept_holds (pushed := pushed) i he hk hok hρ hg hf hwr hsto hls hp hbk.1)
      (growBodyKept_holds (pushed := pushed) i he hk hok hρ hg hf hwr hsto hls hp hbk.2)

open HeapKnowledge in
/-- **A growth keeps a quantified fact whose bound and body it keeps**
(`every-grow`): the array its path reads is the same object, whose spine is
the receiver's, extended with its old elements at their indices, or one the
growth keeps. -/
theorem every_grown {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {t : Tm}
    {first : Nat → String → Bool} {ρ : Env} {h h' : Heap}
    {nw : Nat} {W : WorldT (nw + 4)}
    (he : EnvOk G Γ ρ (nw + 4) W) (hk : Holds k ε ρ h)
    (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hg : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (hf : FirstKept first ρ h h')
    {s : Nat} {p : List String} {st0 st1 : IndexBound} {body : List BodyClause}
    (hst0 : ∀ m, st0.eval ε ρ h = some m → st0.eval ε ρ h' = some m)
    (hst1 : ∀ n, st1.eval ε ρ h = some n → st1.eval ε ρ h' = some n)
    (hb : body.all (growBodyKept G Γ k t s p first) = true)
    (hF : (IndexFact.every s p st0 st1 body).HoldsAt ε ρ h) : (IndexFact.every s p st0 st1 body).HoldsAt ε ρ h' := by
  obtain ⟨w, sto, ls, m0, n, hw, hsto, hls, hm0, hn, hall⟩ := hF
  have hc := receiverGrows_changes hg
  have hwa : growChanges.alters w = false := by
    cases w <;> simp_all [elementsOf, growChanges, Changes.alters]
  obtain ⟨ls', hls', hp⟩ := spine_grown_prefix hg hls
  refine ⟨w, sto, ls', m0, n, readPath_kept hc p (ρ s) w hw (Or.inr hwa) (fun _ => rfl), hsto, hls',
    hst0 m0 hm0, hst1 n hn, fun i hlo hi B hB => ?_⟩
  exact growBodyKept_holds i he hk hok hρ hg hf hw hsto hls hp (List.all_eq_true.mp hb B hB) (hall i hlo hi B hB)

open HeapKnowledge in
/-- A checked non-`undefined` read of parallel array `(s', p')` at `|i| + sh`,
used when extending a quantified invariant across `i.push(a)`. -/
@[nospecialize] def appendParallelSlot (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge)
    (i s' : Nat) (p' : List String) (sh : IndexShift) : Option Nat := do
  let a ← k.indices.find? fun a => a.cond.isNone && match a.fact with
    | .element _ y j =>
      (Footprints.slotsOf k.links s' p').contains y &&
      shiftEqWith (· == .length i) (knownOf k.indices) k.indices j (sh.addTerm (.length i))
    | _ => false
  match a.fact with
  | .element r' _ _ =>
    if (HeapExpressionRules.valuesAt G Γ k r').any (onlyTag · .notUndef) then some r' else none
  | _ => none

open HeapKnowledge in
/-- What a body variable of a quantified fact over the slot `i`'s array
denotes at the value of the slot `a` appended to it: the index its old
length, the element the slot's value, a parallel read its non-`undefined`
element witness at `|i| + sh`, a term itself. -/
@[nospecialize] def appendTerm (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (i a : Nat) :
    Bound → Option Term
  | .index => some (.length i)
  | .elem => some (.value a)
  | .offset _ => none
  | .project kd ep => some (Term.now kd a ep)
  | .parallel s' p' sh kd ep =>
    (appendParallelSlot G Γ k i s' p' sh).map fun r' => Term.now kd r' ep
  | .free t => some t

open HeapKnowledge in
/-- Value of a bound variable at the newly appended index `ls_len` with appended
slot `a`, read in the pre-call heap `h`. -/
def appendedBoundVal (ε : EntryState) (ρ : Env) (h : Heap) (ls_len a : Nat) : Bound → Option Int
  | .index => some (ls_len : Int)
  | .elem => intValue (ρ a)
  | .offset _ => none
  | .project kd ep => termValue ε (fun _ => ρ a) h (Term.now kd 0 ep)
  | .parallel s' p' sh kd ep => boundValue ε ρ h [] ls_len (.parallel s' p' sh kd ep)
  | .free t => termValue ε ρ h t

open HeapKnowledge in
/-- Whether a body clause holds of the value in slot `a` at the old length
`ls_len` of the array in slot `i` in the pre-call heap `h`. -/
def AppendedHolds (ε : EntryState) (ρ : Env) (h : Heap) (ls_len a : Nat) : BodyClause → Prop
  | .clause F => F.HoldsAt (appendedBoundVal ε ρ h ls_len a)
  | .guarded (.self ep) g b =>
    ∃ w, readGuard h (ρ a) ep = some w ∧ (g.holds w ∨ AppendedHolds ε ρ h ls_len a b)
  | .guarded (.parallel s' p' sh ep) g b =>
    ∃ w, (ElemTarget.parallel s' p' sh ep).read ε ρ h [] ls_len = some w ∧
      (g.holds w ∨ AppendedHolds ε ρ h ls_len a b)
  | .either A B => AppendedHolds ε ρ h ls_len a A ∨ AppendedHolds ε ρ h ls_len a B

open HeapKnowledge in
/-- Transport an `AppendedHolds` proof from the pre-call heap `h` to the
newly appended index `ls.length` of `ls'` in the post-call heap `h'`. -/
private theorem appendedHolds_post {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {t : Tm}
    {s : Nat} {p : List String} {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {x : Nat}
    {nw : Nat} {W : WorldT (nw + 4)} {w_r : Val} {sto : Nat} {ls ls' : List (Option Nat)} {l : Nat}
    (he : EnvOk G Γ ρ (nw + 4) W) (hk : Holds k ε ρ h)
    (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hg : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (hf : FirstKept first ρ h h')
    (hwr : readPath h (ρ s) p = some w_r) (hsto : elementsOf w_r = some sto)
    (hls : h[sto]?.bind spineEntries = some ls) (hp : ls <+: ls')
    (hl : ls'[ls.length]? = some (some l)) (hlv : h'[l]? = some (ρ x)) :
    ∀ {B : BodyClause}, growBodyKept G Γ k t s p first (some x) B = true →
      AppendedHolds ε ρ h ls.length x B → B.HoldsAt ε ρ h' ls' ls.length
  | .clause F, hbF, hnew => by
    have hc := receiverGrows_changes hg
    obtain ⟨hkv, hgv⟩ := boundValue_grown (pushed := some x) ls.length he hk hok hρ hg hf hwr hsto hls hp
    refine LinearClause.holdsAt_monotone (val := appendedBoundVal ε ρ h ls.length x)
      (fun y n hky hy => ?_) (fun y n hgy hy => ?_) hbF hnew
    · cases y with
      | index => exact hy
      | offset _ => simp [growBoundKept] at hky
      | elem =>
        simp only [appendedBoundVal] at hy
        simp only [boundValue, elementInt, hl, hlv, Option.bind_some, hy]
      | project kd ep =>
        simp only [appendedBoundVal] at hy
        simp only [growBoundKept, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hky
        rcases hky with htk | ⟨⟨⟨rfl, rfl⟩, -⟩, hxsp⟩
        · simp only [boundValue, hl, hlv, Option.bind_some]
          exact termValue_kept (ε := ε) hc firstKept_none htk hy
        · simp only [termValue, termAt, readPath, kindValue, Option.bind_some] at hy
          obtain ⟨stx, lsx, hsx, hlsx, rfl, hmax⟩ := lengthOf_spine hy
          simp only [boundValue, hl, hlv, Option.bind_some, termValue, termAt, readPath, kindValue]
          exact lengthOf_of_spine hsx (growSpineKept_sound he hk hok hρ hg hxsp rfl hsx hlsx) hmax
      | parallel s' p' sh kd ep =>
        exact hkv (.parallel s' p' sh kd ep) n hky hy
      | free tm => exact termValue_kept (ε := ε) hc hf hky hy
    · cases y with
      | index | elem | offset _ => simp [growBoundGrown] at hgy
      | project kd ep =>
        simp only [appendedBoundVal] at hy
        obtain ⟨n', hn', hle⟩ := termValue_grown (ε := ε) hc firstKept_none hgy hy
        exact ⟨n', by simp only [boundValue, hl, hlv, Option.bind_some, hn'], hle⟩
      | parallel s' p' sh kd ep =>
        exact hgv (.parallel s' p' sh kd ep) n hgy hy
      | free tm => exact termValue_grown (ε := ε) hc hf hgy hy
  | .guarded tgt g b, hbF, hnew => by
    simp only [growBodyKept, Bool.and_eq_true] at hbF
    cases tgt with
    | self ep =>
      simp only [growTargetKept, List.isEmpty_iff] at hbF
      obtain ⟨rfl, hb⟩ := hbF
      obtain ⟨w, hw, hor⟩ := hnew
      simp only [readGuard, Option.some.injEq] at hw
      subst hw
      have hread : (ElemTarget.self []).read ε ρ h' ls' ls.length = some (ρ x) := by
        simp [ElemTarget.read, hl, hlv, readGuard]
      rcases hor with htg | hrest
      · exact .inl ⟨ρ x, hread, htg⟩
      · exact .inr ⟨fun _ => ⟨ρ x, hread⟩, appendedHolds_post he hk hok hρ hg hf hwr hsto hls hp hl hlv hb hrest⟩
    | parallel s' p' sh ep =>
      obtain ⟨w, hw, hor⟩ := hnew
      have hread : (ElemTarget.parallel s' p' sh ep).read ε ρ h' ls' ls.length = some w :=
        elemTarget_grown ls.length hok hg hf hls hp (.parallel s' p' sh ep) hbF.1 w hw
      rcases hor with htg | hrest
      · exact .inl ⟨w, hread, htg⟩
      · exact .inr ⟨fun _ => ⟨w, hread⟩, appendedHolds_post he hk hok hρ hg hf hwr hsto hls hp hl hlv hbF.2 hrest⟩
  | .either A B, hbF, hnew => by
    simp only [growBodyKept, Bool.and_eq_true] at hbF
    exact hnew.imp (appendedHolds_post he hk hok hρ hg hf hwr hsto hls hp hl hlv hbF.1)
      (appendedHolds_post he hk hok hρ hg hf hwr hsto hls hp hl hlv hbF.2)

open HeapKnowledge in
/-- **An append extends a quantified fact over the receiver's array by the
appended value** (`every-push`): where the slot `x`'s value is appended to the
slot `i`'s array (read via any path `(s, p)` resolving to `ρ i`), the fact over
its whole length holds after it where each body clause holds of the appended
value at the old length (`AppendedHolds`), and the growth keeps each body clause
(`growBodyKept`). -/
theorem every_appended {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {f : Tm}
    {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {s i x : Nat}
    {p : List String} {st0 st1 : IndexBound} {nw : Nat} {W : WorldT (nw + 4)}
    (he : EnvOk G Γ ρ (nw + 4) W) (hk : Holds k ε ρ h)
    (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hg : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ (.invoke f (.var i) [.var x]))) h h')
    (ha : CallEffects.ReceiverAppends (ρ i) [ρ x] h h')
    (hf : FirstKept first ρ h h') (hvx : isVal (ρ x) = true)
    (hsp : readPath h (ρ s) p = some (ρ i))
    (hst0 : ∀ m, st0.eval ε ρ h = some m → st0.eval ε ρ h' = some m)
    (hst1 : st1 = IndexBound.ofTerm (Term.now .length s p) ∨ st1 = IndexBound.ofTerm (Term.length i))
    {body : List BodyClause} (hb : body.all (growBodyKept G Γ k (.invoke f (.var i) [.var x]) s p first (some x)) = true)
    (hnew : ∀ ls_len : Nat, termValue ε ρ h (.length i) = some (ls_len : Int) → ∀ B ∈ body, AppendedHolds ε ρ h ls_len x B)
    (hF : (IndexFact.every s p st0 st1 body).HoldsAt ε ρ h) :
    (IndexFact.every s p st0 st1 body).HoldsAt ε ρ h' := by
  have hgi : CallEffects.ReceiverGrows (ρ i) h h' := by
    simpa [ExpressionEffects.receiverOf, instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] using hg
  obtain ⟨w, sto, ls, m0, n, hw, hsto, hls, hm0, hn, hall⟩ := hF
  rw [hsp] at hw; cases hw
  have hlen_i : termValue ε ρ h (.length i) = some n := by
    rcases hst1 with rfl | rfl
    · simp only [IndexBound.ofTerm, IndexBound.eval, Option.map_eq_some_iff, Int.add_zero] at hn
      obtain ⟨v, hv, rfl⟩ := hn
      simpa [Term.length, Term.now, termValue, termAt, readPath, hsp] using hv
    · simp only [IndexBound.ofTerm, IndexBound.eval, Option.map_eq_some_iff, Int.add_zero] at hn
      obtain ⟨v, hv, rfl⟩ := hn; exact hv
  have hlen_raw : lengthOf h (ρ i) = some n := by simpa only [termValue_length] using hlen_i
  obtain ⟨sto2, ls2, hs2, hls2, rfl, -⟩ := lengthOf_spine hlen_raw
  rw [elementsOf_spine hs2] at hsto
  cases hsto
  rw [hls2] at hls
  have hll : ls = ls2 := by simpa [spineEntries] using hls.symm
  subst hll
  obtain ⟨ls', hls', hlen, hel⟩ := ha (by simpa using hvx) sto ls hs2 hls2
  obtain ⟨l, hl, hlv, -⟩ := hel 0 (ρ x) rfl
  simp only [Nat.add_zero] at hl
  obtain ⟨hp, hmax⟩ : ls <+: ls' ∧ ls'.length ≤ maxArrayLength := by
    rcases hgi sto _ hls2 with hk0 | ⟨-, ls0, ls1, he0, hls1, hp, hm⟩
    · rw [hk0] at hls'; cases hls'; simp at hlen
    · cases he0; rw [hls1] at hls'; cases hls'; exact ⟨hp, hm⟩
  have hc := receiverGrows_changes hgi
  have hwa : growChanges.alters (ρ i) = false := by
    cases hρi : ρ i <;> rw [hρi] at hs2 <;> simp_all [Footprints.spineOf, Footprints.fieldsOf, growChanges, Changes.alters]
  have hsp' : readPath h' (ρ s) p = some (ρ i) :=
    readPath_kept hc p (ρ s) (ρ i) hsp (Or.inr hwa) (fun _ => rfl)
  have hlen_i' : termValue ε ρ h' (.length i) = some (ls'.length : Int) := by
    simp only [termValue_length]; exact lengthOf_of_spine hs2 hls' hmax
  have hn' : st1.eval ε ρ h' = some (ls'.length : Int) := by
    rcases hst1 with rfl | rfl
    · have : termValue ε ρ h' (Term.now .length s p) = some (ls'.length : Int) := by
        simpa [Term.length, Term.now, termValue, termAt, readPath, hsp'] using hlen_i'
      simp [IndexBound.ofTerm, IndexBound.eval, this]
    · simp [IndexBound.ofTerm, IndexBound.eval, hlen_i']
  refine ⟨ρ i, sto, ls', m0, ls'.length, hsp', elementsOf_spine hs2, by rw [hls']; rfl, hst0 m0 hm0, hn',
    fun j hlo hj B hB => ?_⟩
  have hbF := List.all_eq_true.mp hb B hB
  by_cases hj' : j < ls.length
  · exact growBodyKept_holds (pushed := some x) j he hk hok hρ hg hf hsp (elementsOf_spine hs2) (by rw [hls2]; rfl) hp
      hbF (hall j hlo (by exact_mod_cast hj') B hB)
  · have hjl : j = ls.length := by simp only [List.length_singleton] at hlen; omega
    subst hjl
    exact appendedHolds_post he hk hok hρ hg hf hsp (elementsOf_spine hs2) (by rw [hls2]; rfl) hp hl hlv hbF
      (hnew ls.length hlen_i B hB)

open HeapKnowledge in
/-- Linear facts about the parallel array element at `(s', p')[|i| + sh]`,
extracted from unconditional `atIndex` facts in `k.indices` whose array path
matches `(s', p')` and whose index equals `|i| + sh`. -/
def appendParallelAtIndex (k : Knowledge) (i s' : Nat) (p' : List String) (sh : IndexShift) :
    List (Linear.Fact Bound) :=
  let K := knownOf k.indices
  k.indices.filterMap fun a =>
    if a.cond.isNone then match a.fact with
    | .atIndex s'' p'' jIdx none (.atom H) =>
      if ((s'' == s' && p'' == p') || (p''.isEmpty && (Footprints.slotsOf k.links s' p').contains s'')) &&
          shiftEqWith (· == .length i) K k.indices jIdx (sh.addTerm (.length i)) then
        H.mapVars fun
          | .project kd ep => some (.parallel s' p' sh kd ep)
          | .elem => some (.parallel s' p' sh .value [])
          | .free t => some (.free t)
          | _ => none
      else none
    | _ => none
    else none

open HeapKnowledge in
/-- Map a body variable for linear discharge at `i.push(a)`, keeping
unresolved parallel array projections as `.parallel` bounds so `atIndex`
witnesses (`appendParallelAtIndex`) can discharge them alongside `k.indices`. -/
@[nospecialize] def appendTermOrKeep (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (i a : Nat) :
    Bound → Option Bound
  | .index => some (.free (.length i))
  | .elem => some (.free (.value a))
  | .offset _ => none
  | .project kd ep => some (.free (Term.now kd a ep))
  | .parallel s' p' sh kd ep =>
    match appendParallelSlot G Γ k i s' p' sh with
    | some r' => some (.free (Term.now kd r' ep))
    | none => some (.parallel s' p' sh kd ep)
  | .free t => some (.free t)

local instance : LT HeapKnowledge.Bound := ⟨fun a b => HeapKnowledge.boundBefore a b = true⟩
local instance : DecidableRel (α := HeapKnowledge.Bound) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (HeapKnowledge.boundBefore a b = true))

open HeapKnowledge in
/-- Discharge a linear body atom at `i.push(a)` using both `k.indices` and
unconditional `atIndex` witnesses for any parallel array projections. -/
@[nospecialize] def appendedLinearViaAtIndex (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (i a : Nat)
    (F : Linear.Fact Bound) : Bool :=
  match F.mapVars (appendTermOrKeep G Γ k i a) with
  | none => false
  | some F' =>
    let parFacts := F'.vars.flatMap fun
      | .parallel s' p' sh _ _ => appendParallelAtIndex k i s' p' sh
      | _ => []
    if parFacts.isEmpty then false
    else
      F'.vars.all (fun
        | .free t => t == Term.length i || termDefined k.indices t
        | v@(.parallel _ _ _ _ _) => parFacts.any fun H => H.vars.contains v
        | _ => false) &&
      Linear.entailsWith ((linearRaw k.indices).map (renameFact Bound.free) ++ parFacts)
        ((rangesRaw k.indices).map (renameFact Bound.free)) F'

open HeapKnowledge in
/-- Whether the knowledge `k` and context `Γ` establish a body clause of the
value in slot `a` appended to the array in slot `i`: a guarded clause whose
guard holds of `a` or the parallel element witness at `|i| + sh` (via
`guardTags`, `valuesAt`, or an unguarded `atIndex` witness) or whose body
holds, a disjunction where either arm holds, or a linear atom whose mapped
variables are defined and entailed. -/
@[nospecialize] def appendedBody (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (i a : Nat) :
    BodyClause → Bool
  | .guarded (.self ep) g b =>
    (ep.isEmpty && (guardTags k a [] g || (HeapExpressionRules.valuesAt G Γ k a).any (onlyTag · g))) ||
    (ep.length == 1 && guardTags k a ep g) ||
    (ep.isEmpty && appendedBody G Γ k i a b)
  | .guarded (.parallel s' p' sh ep) g b =>
    match appendParallelSlot G Γ k i s' p' sh with
    | some r' =>
      (ep.isEmpty && (guardTags k r' [] g || (HeapExpressionRules.valuesAt G Γ k r').any (onlyTag · g))) ||
      (ep.length == 1 && guardTags k r' ep g) ||
      (ep.isEmpty && appendedBody G Γ k i a b)
    | none =>
      ep.isEmpty &&
      (appendParallelAtIndex k i s' p' sh).any (fun H => H.vars.any fun
        | .parallel _ _ _ _ _ => true
        | _ => false) &&
      appendedBody G Γ k i a b
  | .either A B => appendedBody G Γ k i a A || appendedBody G Γ k i a B
  | .clause (.either A B) =>
    appendedBody G Γ k i a (.clause A) || appendedBody G Γ k i a (.clause B)
  | .clause (.atom F) =>
    match F.mapVars (appendTerm G Γ k i a) with
    | some G' => G'.vars.all (fun t => t == Term.length i || termDefined k.indices t) && entailsKnown k.indices G'
    | none => appendedLinearViaAtIndex G Γ k i a F

open HeapKnowledge in
omit [DecidableEq ι] in
private theorem appendParallelSlot_read {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge}
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} {i s' r' ls_len : Nat} {p' : List String} {sh : IndexShift}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h)
    (hlen : termValue ε ρ h (.length i) = some (ls_len : Int))
    (hslot : appendParallelSlot G Γ k i s' p' sh = some r') :
    ∃ j arr st ls2 l, sh.eval ε ρ h ls_len = some j ∧
      readPath h (ρ s') p' = some arr ∧ elementsOf arr = some st ∧
      h[st]?.bind spineEntries = some ls2 ∧ ls2[j]? = some (some l) ∧ h[l]? = some (ρ r') := by
  simp only [appendParallelSlot, Option.bind_eq_bind, Option.bind_eq_some_iff] at hslot
  obtain ⟨at_, hfind, hmap_r⟩ := hslot
  have hc := List.find?_some hfind
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
  obtain ⟨hcond, hc⟩ := hc
  have hat := hk.2.2.2.2.2 at_ (List.mem_of_find?_eq_some hfind) (fun b hb => by rw [hcond] at hb; cases hb)
  cases hf : at_.fact with
  | element r1 y jIdx =>
    simp only [hf] at hmap_r hc hat
    split at hmap_r
    · rename_i hnu
      simp only [Option.some.injEq] at hmap_r; subst hmap_r
      have hneUndef : ρ r1 ≠ .undef := by
        cases hV : HeapExpressionRules.valuesAt G Γ k r1 with
        | none => rw [hV] at hnu; cases hnu
        | some V =>
          rw [hV] at hnu
          simp only [Option.any_some] at hnu
          exact onlyTag_mem hnu (HeapExpressionRules.valuesAt_sound hV he hk)
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hpath, hjeq⟩ := hc
      obtain ⟨st2, ls2, j0, hel2, hls2, hj0, hlt2, hpres2, hhole2⟩ := hat
      have hsh := shiftEqWith_eval (knownOf_holds hk.2.2.2.2.2) hk.2.2.2.2.2
        (fun t ht => by rw [beq_iff_eq.mp ht]; simp [hlen]) hjeq (i := 0)
      rw [hj0, IndexShift.eval_addTerm hlen] at hsh
      have hrp : readPath h (ρ s') p' = some (ρ y) :=
        Footprints.slotsOf_read hk.2.2.1 (List.contains_iff_mem.mp hpath)
      cases hlj : ls2[j0]? with
      | none => exact absurd (List.getElem?_eq_none_iff.mp hlj) (by omega)
      | some o =>
        cases o with
        | none => exact absurd (hhole2 hlj) hneUndef
        | some l => exact ⟨j0, ρ y, st2, ls2, l, hsh.symm, hrp, hel2, hls2, hlj, hpres2 l hlj⟩
    · cases hmap_r
  | _ => simp [hf] at hmap_r

open HeapKnowledge in
omit [DecidableEq ι] in
private theorem appendParallelAtIndex_sound {k : Knowledge}
    {ρ : Env} {h : Heap} {i s' a ls_len : Nat} {p' : List String} {sh : IndexShift}
    (hk : Holds k ε ρ h) (hlen : termValue ε ρ h (.length i) = some (ls_len : Int))
    {H' : Linear.Fact Bound} (hH' : H' ∈ appendParallelAtIndex k i s' p' sh) :
    FactAt (appendedBoundVal ε ρ h ls_len a) H' ∧
    (H'.vars.any (fun | .parallel _ _ _ _ _ => true | _ => false) = true →
      ∃ w, (ElemTarget.parallel s' p' sh []).read ε ρ h [] ls_len = some w) := by
  simp only [appendParallelAtIndex, List.mem_filterMap] at hH'
  obtain ⟨at_, hatMem, hmap⟩ := hH'
  split at hmap
  · rename_i hcond
    have hat := hk.2.2.2.2.2 at_ hatMem (fun b hb => by rw [Option.isNone_iff_eq_none.mp hcond] at hb; cases hb)
    split at hmap
    · rename_i s'' p'' jIdx H hf
      split at hmap
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.isEmpty_iff, List.contains_iff_mem] at hc
        obtain ⟨hpath, hjeq⟩ := hc
        rw [hf] at hat
        obtain ⟨w, sto, ls2, j0, hw, hsto, hls2, hj0, hlt2, hH⟩ := hat
        have hrp : readPath h (ρ s') p' = some w := by
          rcases hpath with ⟨rfl, rfl⟩ | ⟨rfl, hmem⟩
          · exact hw
          · simp only [readPath, Option.some.injEq] at hw
            rw [← hw]
            exact Footprints.slotsOf_read hk.2.2.1 hmem
        have hsh : sh.eval ε ρ h ls_len = some j0 := by
          have h0 := shiftEqWith_eval (knownOf_holds hk.2.2.2.2.2) hk.2.2.2.2.2
            (fun t ht => by rw [beq_iff_eq.mp ht]; simp [hlen]) hjeq (i := 0)
          rw [hj0, IndexShift.eval_addTerm hlen] at h0
          exact h0.symm
        have hholds : FactAt (appendedBoundVal ε ρ h ls_len a) H' := by
          refine (factAt_mapVars hmap fun v _ u hu => ?_).mpr hH
          cases v with
          | project kd ep =>
            cases hu
            simp only [appendedBoundVal, boundValue, hsh, hrp, hsto, hls2]
          | elem =>
            cases hu
            simp only [appendedBoundVal, boundValue, elementInt, hsh, hrp, hsto, hls2]
            cases ls2[j0]? with
            | none => rfl
            | some o =>
              cases o with
              | none => rfl
              | some l =>
                cases h[l]? with
                | none => rfl
                | some val => simp [termValue, termAt, readPath, kindValue]
          | free t => cases hu; rfl
          | index | offset _ | parallel _ _ _ _ _ => cases hu
        refine ⟨hholds, fun hany => ?_⟩
        obtain ⟨v', hv', hpar⟩ := List.any_eq_true.mp hany
        obtain ⟨v, hv, hvu⟩ := Linear.Fact.mapVars_vars hmap v' hv'
        have hvDef := hH.1 v hv
        cases v with
        | project kd ep =>
          simp only [boundValue] at hvDef
          cases hlj : ls2[j0]? with
          | none => simp [hlj] at hvDef
          | some o =>
            cases o with
            | none => simp [hlj] at hvDef
            | some l =>
              cases hlv : h[l]? with
              | none => simp [hlj, hlv] at hvDef
              | some val =>
                exact ⟨val, by simp [ElemTarget.read, hsh, hrp, hsto, hls2, hlj, hlv, readGuard]⟩
        | elem =>
          simp only [boundValue, elementInt] at hvDef
          cases hlj : ls2[j0]? with
          | none => simp [hlj] at hvDef
          | some o =>
            cases o with
            | none => simp [hlj] at hvDef
            | some l =>
              cases hlv : h[l]? with
              | none => simp [hlj, hlv] at hvDef
              | some val =>
                exact ⟨val, by simp [ElemTarget.read, hsh, hrp, hsto, hls2, hlj, hlv, readGuard]⟩
        | free t => cases hvu; simp at hpar
        | index | offset _ | parallel _ _ _ _ _ => cases hvu
      · cases hmap
    · cases hmap
  · cases hmap

open HeapKnowledge in
omit [DecidableEq ι] in
theorem appendedBody_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge}
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} {i a ls_len : Nat}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h)
    (hlen : termValue ε ρ h (Term.length i) = some (ls_len : Int)) :
    ∀ {B : BodyClause}, appendedBody G Γ k i a B = true → AppendedHolds ε ρ h ls_len a B
  | .either A B, hF => by
    simp only [appendedBody, Bool.or_eq_true] at hF
    exact hF.imp (appendedBody_sound he hk hlen) (appendedBody_sound he hk hlen)
  | .guarded (.self ep) g b, hF => by
    simp only [appendedBody, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hF
    rcases hF with (⟨rfl, hgt | hval⟩ | ⟨hlen1, hgt⟩) | ⟨rfl, hb⟩
    · obtain ⟨v, hv, hg⟩ := guardTags_sound hk a [] g hgt
      simp only [readGuard, Option.some.injEq] at hv; subst hv
      exact ⟨ρ a, rfl, .inl hg⟩
    · cases hv : HeapExpressionRules.valuesAt G Γ k a with
      | none => rw [hv] at hval; cases hval
      | some V =>
        rw [hv] at hval
        exact ⟨ρ a, rfl, .inl (onlyTag_mem hval (HeapExpressionRules.valuesAt_sound hv he hk))⟩
    · obtain ⟨v, hv, hg⟩ := guardTags_sound hk a ep g hgt
      exact ⟨v, hv, .inl hg⟩
    · exact ⟨ρ a, rfl, .inr (appendedBody_sound he hk hlen hb)⟩
  | .guarded (.parallel s' p' sh ep) g b, hF => by
    simp only [appendedBody] at hF
    cases hps : appendParallelSlot G Γ k i s' p' sh with
    | none =>
      rw [hps] at hF
      simp only [Bool.and_eq_true, List.isEmpty_iff, List.any_eq_true] at hF
      obtain ⟨⟨rfl, ⟨H', hH', hpar⟩⟩, hb⟩ := hF
      obtain ⟨w, hw⟩ := (appendParallelAtIndex_sound (a := a) hk hlen hH').2 (List.any_eq_true.mpr hpar)
      exact ⟨w, hw, .inr (appendedBody_sound he hk hlen hb)⟩
    | some r' =>
      rw [hps] at hF
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hF
      obtain ⟨j, arr, st2, ls2, l, hsh, hrp, hel2, hls2, hlj, hlv⟩ := appendParallelSlot_read he hk hlen hps
      have hreadBase : ∀ w, readGuard h (ρ r') ep = some w →
          (ElemTarget.parallel s' p' sh ep).read ε ρ h [] ls_len = some w := by
        intro w hw; simp [ElemTarget.read, hsh, hrp, hel2, hls2, hlj, hlv, hw]
      rcases hF with (⟨rfl, hgt | hval⟩ | ⟨hlen1, hgt⟩) | ⟨rfl, hb⟩
      · obtain ⟨v, hv, hg⟩ := guardTags_sound hk r' [] g hgt
        simp only [readGuard, Option.some.injEq] at hv; subst hv
        exact ⟨ρ r', hreadBase (ρ r') rfl, .inl hg⟩
      · cases hv : HeapExpressionRules.valuesAt G Γ k r' with
        | none => rw [hv] at hval; cases hval
        | some V =>
          rw [hv] at hval
          exact ⟨ρ r', hreadBase (ρ r') rfl, .inl (onlyTag_mem hval (HeapExpressionRules.valuesAt_sound hv he hk))⟩
      · obtain ⟨v, hv, hg⟩ := guardTags_sound hk r' ep g hgt
        exact ⟨v, hreadBase v hv, .inl hg⟩
      · exact ⟨ρ r', hreadBase (ρ r') rfl, .inr (appendedBody_sound he hk hlen hb)⟩
  | .clause (.either A B), hF => by
    simp only [appendedBody, Bool.or_eq_true] at hF
    rcases hF with hA | hB
    · exact .inl (appendedBody_sound he hk hlen hA)
    · exact .inr (appendedBody_sound he hk hlen hB)
  | .clause (.atom F), hF => by
    simp only [appendedBody] at hF
    cases hG : F.mapVars (appendTerm G Γ k i a) with
    | some G' =>
      rw [hG] at hF
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hF
      obtain ⟨hd, hent⟩ := hF
      refine (factAt_mapVars (val' := termValue ε ρ h) hG fun y _ t ht => ?_).mp
        ⟨fun t ht => ?_, entailsKnown_sound hk.2.2.2.2.2 hent⟩
      · cases y with
        | index => simp only [appendTerm, Option.some.injEq] at ht; subst ht; exact hlen
        | elem => simp only [appendTerm, Option.some.injEq] at ht; subst ht; simp [appendedBoundVal, termValue_value]
        | offset _ => simp [appendTerm] at ht
        | project kd ep =>
          simp only [appendTerm, Option.some.injEq] at ht; subst ht
          simp [appendedBoundVal, termValue, termAt]
        | parallel s' p' sh kd ep =>
          simp only [appendTerm, Option.map_eq_some_iff] at ht
          obtain ⟨r', hr', rfl⟩ := ht
          obtain ⟨j, arr, st2, ls2, l, hsh, hrp, hel2, hls2, hlj, hlv⟩ := appendParallelSlot_read he hk hlen hr'
          simp [appendedBoundVal, boundValue, hsh, hrp, hel2, hls2, hlj, hlv, termValue, termAt]
        | free tm => simp only [appendTerm, Option.some.injEq] at ht; subst ht; rfl
      · rcases hd t ht with rfl | hdt
        · simp [hlen]
        · exact termDefined_sound hk.2.2.2.2.2 hdt
    | none =>
      rw [hG] at hF
      unfold appendedLinearViaAtIndex at hF
      cases hF' : F.mapVars (appendTermOrKeep G Γ k i a) with
      | none => rw [hF'] at hF; cases hF
      | some F' =>
        rw [hF'] at hF
        dsimp only at hF
        split at hF
        · cases hF
        · simp only [Bool.and_eq_true, List.all_eq_true] at hF
          obtain ⟨hdef, hent⟩ := hF
          have hparHolds : ∀ H' ∈ (F'.vars.flatMap fun
              | .parallel s' p' sh _ _ => appendParallelAtIndex k i s' p' sh
              | _ => []), FactAt (appendedBoundVal ε ρ h ls_len a) H' := by
            intro H' hH'
            obtain ⟨v, _, hH'⟩ := List.mem_flatMap.mp hH'
            cases v with
            | parallel s' p' sh _ _ => exact (appendParallelAtIndex_sound hk hlen hH').1
            | index | elem | offset _ | project _ _ | free _ => cases hH'
          have hlin : ∀ G ∈ (linearRaw k.indices).map (renameFact Bound.free) ++ (F'.vars.flatMap fun
              | .parallel s' p' sh _ _ => appendParallelAtIndex k i s' p' sh
              | _ => []), G.Holds (fun x => (appendedBoundVal ε ρ h ls_len a x).getD 0) := by
            intro G hG'
            rcases List.mem_append.mp hG' with hG' | hG'
            · obtain ⟨G0, hG0, rfl⟩ := List.mem_map.mp hG'
              exact (Linear.Fact.holds_mapVars (renameFact_mapVars Bound.free G0) fun x _ y hy => by
                cases hy; rfl).mpr (linearRaw_holds hk.2.2.2.2.2 G0 hG0)
            · exact (hparHolds G hG').2
          have hrng : ∀ G ∈ (rangesRaw k.indices).map (renameFact Bound.free),
              G.Holds (fun x => (appendedBoundVal ε ρ h ls_len a x).getD 0) := by
            intro G hG'
            obtain ⟨G0, hG0, rfl⟩ := List.mem_map.mp hG'
            exact (Linear.Fact.holds_mapVars (renameFact_mapVars Bound.free G0) fun x _ y hy => by
              cases hy; rfl).mpr (rangesRaw_holds hk.2.2.2.2.2 G0 hG0)
          have hF'Holds : FactAt (appendedBoundVal ε ρ h ls_len a) F' := by
            refine ⟨fun v hv => ?_, Linear.entailsWith_sound hent hlin hrng⟩
            have hdv := hdef v hv
            cases v with
            | free t =>
              rcases Bool.or_eq_true_iff.mp hdv with heq | hdt
              · rw [beq_iff_eq.mp heq]; simp [appendedBoundVal, hlen]
              · exact termDefined_sound hk.2.2.2.2.2 hdt
            | parallel s' p' sh kd ep =>
              obtain ⟨H', hH', hmem⟩ := List.any_eq_true.mp hdv
              exact (hparHolds H' hH').1 (.parallel s' p' sh kd ep) (List.contains_iff_mem.mp hmem)
            | index | elem | offset _ | project _ _ => cases hdv
          refine (factAt_mapVars hF' fun y _ u hu => ?_).mp hF'Holds
          cases y with
          | index => cases hu; exact hlen
          | elem => cases hu; simp [appendedBoundVal, termValue_value]
          | offset _ => cases hu
          | project kd ep => cases hu; simp [appendedBoundVal, termValue, termAt]
          | parallel s' p' sh kd ep =>
            simp only [appendTermOrKeep] at hu
            cases hps : appendParallelSlot G Γ k i s' p' sh with
            | some r' =>
              rw [hps] at hu; cases hu
              obtain ⟨j, arr, st2, ls2, l, hsh, hrp, hel2, hls2, hlj, hlv⟩ := appendParallelSlot_read he hk hlen hps
              simp [appendedBoundVal, boundValue, hsh, hrp, hel2, hls2, hlj, hlv, termValue, termAt]
            | none => rw [hps] at hu; cases hu; rfl
          | free tm => cases hu; rfl

open HeapKnowledge in
@[nospecialize] def growIndexBoundKept [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge)
    (t : Tm) (b : IndexBound) : Bool :=
  match b.base with
  | none => true
  | some st =>
    st.keptBy growChanges (growFirst k t) ||
      (st.kind == .length && !st.atEntry && growSpineKept G Γ k t st.slot st.path)

open HeapKnowledge in
/-- Whether a call growing its receiver's spine keeps a quantified atom of
its entry `k`: each body clause kept by the growth (`growBodyKept`), and
its bound kept (`every-grow`, including via `growSpineKept` from `spineApart`
or type-disjoint array spines) or, for the call `i.push(x)` of one value
actual, the fact over `i`'s array (at any path resolving to `i`), each body
clause established of the appended value at the old length (`every-push`). -/
@[nospecialize] def everyGrown (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (t : Tm) (a : IndexAtom) : Bool :=
  match a.fact with
  | .every s p st0 st1 body =>
    growIndexBoundKept G Γ k t st0 &&
    ((body.all (growBodyKept G Γ k t s p (growFirst k t)) && growIndexBoundKept G Γ k t st1) ||
      match t with
      | .invoke _ (.var i) [.var x] =>
        decide (x < Γ.length) && (Footprints.slotsOf k.links s p).contains i &&
        (st1 == IndexBound.ofTerm (Term.now .length s p) || st1 == IndexBound.ofTerm (Term.length i)) &&
        body.all (growBodyKept G Γ k t s p (growFirst k t) (some x)) &&
        body.all (appendedBody G Γ k i x)
      | _ => false)
  | _ => false

open HeapKnowledge in
/-- Find an integer slot `idx` in `k` known equal to `i`'s current length
(`|i| = idx`), so `i.push(x)` can run `IndexWrites.denseAppendAtomsCore` to
emit `element x i idx` and preserve/extend parallel quantified invariants. -/
def findOldLenSlot (k : Knowledge) (i : Nat) : Option Nat :=
  let K := knownOf k.indices
  (definedTerms k.indices).findSome? fun t =>
    if t.kind == .value && t.path.isEmpty && !t.atEntry &&
        intSlot k.indices t.slot &&
        K.entails (.le [(.value t.slot, 1), (.length i, -1)] 0) &&
        K.entails (.le [(.length i, 1), (.value t.slot, -1)] 0)
    then some t.slot else none

/-- The quantified atoms of a call's entry `k` its growth of its receiver's
spine keeps or extends (`everyGrown`), together with dense-append parallel
invariants (`IndexWrites.denseAppendAtomsCore`) when a single-value `push` has
a slot holding the old length (`findOldLenSlot`), renamed past the result; none
of a call growing nothing. A derived rule of the note's Entry at the normal
exit's growth and append postconditions (`spineExtends`, `push`). -/
@[nospecialize] def appendKept (G : NormalGraph ι) (Γ : List (Ty ι)) (eff : Effect) (t : Tm)
    (k : HeapKnowledge.Knowledge) : List HeapKnowledge.IndexAtom :=
  if statesExtension eff && statesAppend eff then
    let dense := match t with
      | .invoke _ (.var i) [.var x] =>
        if decide (x < Γ.length) && HeapKnowledge.termDefined k.indices (.length i) then
          match findOldLenSlot k i with
          | some idx => IndexWrites.denseAppendAtomsCore G Γ k i idx x
          | none => []
        else []
      | _ => []
    HeapKnowledge.shiftIndices (k.indices.filter (everyGrown G Γ k t) ++ dense)
  else []

open HeapKnowledge in
private theorem growIndexBoundKept_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {t : Tm} {k : Knowledge}
    {ρ : Env} {h h' : Heap} {nw : Nat} {W : WorldT (nw + 4)} {b : IndexBound} {z : Int}
    (he : EnvOk G Γ ρ (nw + 4) W) (hk : Holds k ε ρ h) (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hgrow : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (hf : FirstKept (growFirst k t) ρ h h')
    (hbk : growIndexBoundKept G Γ k t b = true) (hb : b.eval ε ρ h = some z) :
    b.eval ε ρ h' = some z := by
  cases b with
  | mk base offset =>
    cases base with
    | none => exact hb
    | some st =>
      simp only [IndexBound.eval, Option.map_eq_some_iff] at hb ⊢
      obtain ⟨v, hv, rfl⟩ := hb
      simp only [growIndexBoundKept, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hbk
      rcases hbk with hst | ⟨⟨hkind, hatE⟩, hsp_kept⟩
      · exact ⟨v, termValue_kept (receiverGrows_changes hgrow) hf hst hv, rfl⟩
      · refine ⟨v, ?_, rfl⟩
        simp only [termValue, termAt, hatE, Bool.false_eq_true, ite_false, hkind, Option.bind_eq_some_iff] at hv ⊢
        obtain ⟨w, hw, hkw⟩ := hv
        obtain ⟨sto, ls, hsp, hls, rfl, hmax⟩ := lengthOf_spine hkw
        have hc := receiverGrows_changes hgrow
        have hwa : growChanges.alters w = false := by
          cases w <;> simp_all [Footprints.spineOf, Footprints.fieldsOf, growChanges, Changes.alters]
        have hw' := readPath_kept hc st.path (ρ st.slot) w hw (Or.inr hwa) (fun _ => rfl)
        have hls' := growSpineKept_sound he hk hok hρ hgrow hsp_kept hw hsp hls
        exact ⟨w, hw', lengthOf_of_spine hsp hls' hmax⟩

open HeapKnowledge in
theorem appendKept_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {eff : Effect} {t : Tm} {k : Knowledge}
    {ρ : Env} {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT (nw + 4)}
    (hv : ∀ i, i < Γ.length → isVal (ρ i) = true)
    (he : EnvOk G Γ ρ (nw + 4) W) (hk : Holds k ε ρ h) (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v) :
    IndexHolds ε (appendKept G Γ eff t k) (push v ρ) h' := by
  unfold appendKept
  split
  · rename_i hgr
    simp only [Bool.and_eq_true] at hgr
    have hgrow := statesExtension_grows hgr.1 hq
    have happ := statesAppend_appends hgr.2 hq
    have hf := growFirst_kept hk hok hρ hgrow
    refine shiftIndices_holds fun a ha hcd => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨ha, hkept⟩ := List.mem_filter.mp ha
      have hF := hk.2.2.2.2.2 a ha hcd
      unfold everyGrown at hkept
      split at hkept
      · rename_i s p st0 st1 body hfa
        rw [hfa] at hF ⊢
        simp only [Bool.and_eq_true, Bool.or_eq_true] at hkept
        obtain ⟨hst0, ⟨hb, hst1⟩ | hpush⟩ := hkept
        · exact every_grown he hk hok hρ hgrow hf
            (fun _ hm => growIndexBoundKept_sound he hk hok hρ hgrow hf hst0 hm)
            (fun _ hn => growIndexBoundKept_sound he hk hok hρ hgrow hf hst1 hn) hb hF
        · have hst0_ev : ∀ m, st0.eval ε ρ h = some m → st0.eval ε ρ h' = some m :=
            fun _ hm => growIndexBoundKept_sound he hk hok hρ hgrow hf hst0 hm
          cases t with
          | invoke fn r args =>
            cases r with
            | var i =>
              cases args with
              | cons a0 rest =>
                cases a0 with
                | var x =>
                  cases rest with
                  | nil =>
                    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem, beq_iff_eq] at hpush
                    obtain ⟨⟨⟨⟨hxlt, hslot⟩, hst_eq⟩, hbk⟩, hbody⟩ := hpush
                    simp only [ExpressionEffects.receiverOf, ExpressionEffects.actualsOf, instantiate, instantiateArgs,
                      Nat.not_lt_zero, ite_false, Nat.sub_zero] at happ hf
                    have hsp := Footprints.slotsOf_read hk.2.2.1 hslot
                    exact every_appended he hk hok hρ hgrow happ hf (hv x hxlt) hsp hst0_ev hst_eq hbk
                      (fun ls_len hlen B hB => appendedBody_sound he hk hlen (List.all_eq_true.mp hbody B hB)) hF
                  | cons _ _ => simp at hpush
                | _ => simp at hpush
              | nil => simp at hpush
            | _ => simp at hpush
          | _ => simp at hpush
      · cases hkept
    · -- Dense-append parallel invariants via `IndexWrites.denseAppendAtomsCore`
      cases t with
      | invoke fn r args =>
        cases r with
        | var i =>
          cases args with
          | cons a0 rest =>
            cases a0 with
            | var x =>
              cases rest with
              | nil =>
                dsimp only at ha
                split at ha
                case isFalse => cases ha
                rename_i hcond
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
                obtain ⟨hxlt, hlenDef⟩ := hcond
                cases hfind : findOldLenSlot k i with
                | none => rw [hfind] at ha; cases ha
                | some idx =>
                  rw [hfind] at ha
                  simp only [ExpressionEffects.receiverOf, ExpressionEffects.actualsOf, instantiate, instantiateArgs,
                    Nat.not_lt_zero, ite_false, Nat.sub_zero] at hgrow happ
                  obtain ⟨m0, hm0⟩ := Option.isSome_iff_exists.mp (termDefined_sound hk.2.2.2.2.2 hlenDef)
                  obtain ⟨target, ls, hsp, hls, rfl, -⟩ := lengthOf_spine (by simpa only [termValue_length] using hm0)
                  unfold findOldLenSlot at hfind
                  obtain ⟨_, t0, _, _, ht0, -⟩ := List.findSome?_eq_some_iff.mp hfind
                  split at ht0
                  case isFalse => cases ht0
                  rename_i hidxC
                  simp only [Option.some.injEq] at ht0; subst ht0
                  simp only [Bool.and_eq_true] at hidxC
                  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hint⟩, hle1⟩, hle2⟩ := hidxC
                  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (intSlot_sound hk.2.2.2.2.2 hint)
                  have hK : (knownOf k.indices).Holds (termValuation ε ρ h) := knownOf_holds hk.2.2.2.2.2
                  have hz_eq : z = (ls.length : Int) := by
                    have h1 := Linear.Known.entails_sound hK hle1
                    have h2 := Linear.Known.entails_sound hK hle2
                    simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, termValue_value, hz, hm0,
                      Option.getD_some] at h1 h2
                    omega
                  subst hz_eq
                  obtain ⟨b, hb, hsi⟩ : ∃ b, ρ t0.slot = .num b ∧ SafeIntegers.SafeInt b (ls.length : Int) := by
                    cases hρs : ρ t0.slot <;> rw [hρs] at hz <;> simp [intValue] at hz
                    exact ⟨_, rfl, SafeIntegers.safeIntOfBits_sound hz⟩
                  obtain ⟨ls', hls', hlen', hel⟩ := happ (by simpa using hv x hxlt) target ls hsp hls
                  obtain ⟨fresh, hfresh_get, hfresh_val, -⟩ := hel 0 (ρ x) rfl
                  simp only [Nat.add_zero] at hfresh_get
                  obtain ⟨hpre, hmax'⟩ : ls <+: ls' ∧ ls'.length ≤ maxArrayLength := by
                    rcases hgrow target _ hls with hk' | ⟨-, ls0, ls1, heq, hls1, hp, hm⟩
                    · rw [hk'] at hls'; cases hls'; simp at hlen'
                    · cases heq; rw [hls1] at hls'; cases hls'; exact ⟨hp, hm⟩
                  have hls'_eq : ls' = placeAt ls ls.length fresh := by
                    apply List.ext_getElem?
                    intro j
                    rw [placeAt_getElem?]
                    by_cases hj : j = ls.length
                    · subst hj; simp [hfresh_get]
                    · simp only [hj, ite_false]
                      by_cases hjlt : j < ls.length
                      · simp only [hjlt, ite_true]
                        obtain ⟨tail, rfl⟩ := hpre
                        rw [List.getElem?_append_left hjlt]
                      · simp only [hjlt, ite_false]
                        have hnot : ¬ j < ls.length + 1 := by omega
                        have hge : ls'.length ≤ j := by simp only [List.length_singleton] at hlen'; omega
                        simp [hnot, List.getElem?_eq_none hge]
                  have htl : target < h.length := (List.getElem?_eq_some_iff.mp hls).1
                  have hda : IndexWrites.DenseAppendHeap h h' target fresh ls (ρ x) := by
                    refine ⟨htl, hls, by rwa [← hls'_eq], hfresh_val, fun l hlt hne => ?_⟩
                    cases hl : h[l]? with
                    | none => exact absurd (List.getElem?_eq_none_iff.mp hl) (by omega)
                    | some u =>
                      rcases hgrow l u hl with hk' | ⟨hsp2, -⟩
                      · exact hk'
                      · rw [hsp] at hsp2; cases hsp2; exact absurd rfl hne
                  have htarg : roleAt W target = some (.spine .array) := by
                    obtain ⟨flds, cd, oid, hoi⟩ : ∃ flds cd oid, ρ i = .objAt flds cd oid := by
                      cases hρi : ρ i <;> rw [hρi] at hsp <;> simp [Footprints.spineOf, Footprints.fieldsOf] at hsp
                      exact ⟨_, _, _, rfl⟩
                    have hfl : flds.lookup arraySpineKey = some target := by
                      simpa [Footprints.spineOf, Footprints.fieldsOf, hoi] using hsp
                    have hmem_ref : Ref.slot arraySpineKey target ∈ refs (.objAt flds cd oid) := by
                      cases cd <;> simp [refs, objRefs, PositiveRules.mem_of_lookup hfl]
                    have hsr : SlotRole arraySpineKey (roleAt W target) :=
                      (hρ i) (.slot arraySpineKey target) (by rw [hoi]; exact hmem_ref)
                    rcases hr : roleAt W target with _ | role
                    · rw [hr] at hsr; cases hsr
                    · rw [hr] at hsr
                      cases role with
                      | spine f => cases f with | array => rfl | view => simp [SlotRole] at hsr
                      | _ => simp [SlotRole] at hsr
                  exact IndexWrites.denseAppendAtomsCore_holds hda htarg (hls'_eq ▸ hmax') he hk hok hρ hsp hb hsi a ha hcd
              | cons _ _ => cases ha
            | _ => cases ha
          | nil => cases ha
        | _ => cases ha
      | _ => cases ha
  · exact indexHolds_nil _ _

open HeapKnowledge in
/-- Exact length on a normal append of value actuals. -/
theorem appended_length {ρ : Env} {h h' : Heap} {i : Nat} {args : List Tm} {n : Int}
    (hg : CallEffects.ReceiverGrows (ρ i) h h')
    (ha : CallEffects.ReceiverAppends (ρ i) args h h')
    (hv : ∀ a ∈ args, isVal a = true) (hn : termValue ε ρ h (.length i) = some n) :
    termValue ε ρ h' (.length i) = some (n + args.length) := by
  simp only [termValue_length] at hn ⊢
  obtain ⟨s, ls, hs, hls, rfl, hm⟩ := lengthOf_spine hn
  obtain ⟨ls', hls', hlen, -⟩ := ha hv s ls hs hls
  have hm' : ls'.length ≤ maxArrayLength := by
    rcases hg s _ hls with hk | ⟨-, ls0, ls1, he, hls1, -, hmax⟩
    · rw [hk] at hls'; cases hls'; exact hm
    · cases he; rw [hls1] at hls'; cases hls'; exact hmax
  have hl := lengthOf_of_spine hs hls' hm'
  simpa [hlen] using hl

open HeapKnowledge in
omit [DecidableEq ι] in
/-- An array slot's length is defined as a non-negative integer at any positive
budget (`IndexWrites.arraySlot`). -/
private theorem arraySlot_length {G : NormalGraph ι} {Γ : List (Ty ι)} {j : Nat} {ρ n W h}
    (hc : IndexWrites.arraySlot G Γ j = true) (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h) :
    ∃ m : Nat, termValue ε ρ h (.length j) = some (m : Int) := by
  unfold IndexWrites.arraySlot at hc
  split at hc; case h_2 => cases hc
  rename_i R hR
  split at hc; case h_2 => cases hc
  rename_i fs vs os ms ks st hexp
  split at hc; case h_2 => cases hc
  rename_i S hS
  split at hc; case h_2 => cases hc
  rename_i T hT
  have hsem := (ProgramTyping.represents_raw (show ProgramTyping.Represents G R (.refs fs [] vs os ms ks st) from hexp) _ W _) (he.2 j R hR)
  obtain ⟨flds, l, c, oid, hobj, hf, hlc, hag⟩ : ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr (n + 1)) (oid : Nat),
      ρ j = .objAt flds .absent oid ∧ flds.lookup arraySpineKey = some l ∧ lookup W l = some c ∧
      ∀ (i : Nat) (hi : i < n + 1) (W' : WorldT i) (u : Val), c i hi W' u → meaning G S i W' u := by
    cases hfs : (Stored.views fs).lookup arraySpineKey with
    | some S' =>
      rw [hfs] at hS
      simp only [Option.orElse_some, Option.some.injEq] at hS
      subst hS
      obtain ⟨_, hm⟩ := Stored.mem_views.mp (PositiveRules.mem_of_lookup hfs)
      obtain ⟨flds, l, c, oid, hobj, hf, hlc, hag⟩ := recT_at
        (ReferenceConjunctions.mem_famsOf.mpr ⟨S', hm, rfl⟩) hsem.1.1
      exact ⟨flds, l, c, oid, hobj, hf, hlc, fun i hi W' u hu => (hag i hi W' u).mp hu⟩
    | none =>
      rw [hfs] at hS
      simp only [Option.orElse_none] at hS
      exact viewsT_at (ReferenceConjunctions.mem_viewsOf.mpr ⟨S, PositiveRules.mem_of_lookup hS, rfl⟩)
        (by simp [arraySpineKey, lengthKey]) hsem.2.1
  obtain ⟨w, hwv, hwc⟩ := hh.1.2 l c hlc
  have hspine : meaning G S n (trunc n (Nat.le_succ n) W) w := hag n (by omega) _ _ (hwc n (by omega))
  obtain ⟨ls, rfl, -, -, hmax, -⟩ := (ProgramTyping.represents_raw (show ProgramTyping.Represents G S (.list T []) from hT) _ _ _ hspine).1
  refine ⟨ls.length, ?_⟩
  simp only [termValue_length]
  exact lengthOf_of_spine (by simp [hobj, Footprints.spineOf, Footprints.fieldsOf, hf]) hwv hmax

open HeapKnowledge in
/-- The floor of a length the facts `as` state defined or the context `Γ` types
as an array, `0 ≤ |x|`: a fact of the entry, every array's length a natural
number. -/
@[nospecialize] def lengthFloor (G : NormalGraph ι) (Γ : List (Ty ι)) (as : List IndexAtom) (i : Nat) :
    List (Linear.Fact Term) :=
  if termDefined as (.length i) || IndexWrites.arraySlot G Γ i then [.le [(.length i, -1)] 0] else []

open HeapKnowledge in
omit [DecidableEq ι] in
theorem lengthFloor_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {as : List IndexAtom} {i : Nat}
    {ρ : Env} {n : Nat} {W : WorldT (n + 1)} {h : Heap}
    (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h) (has : IndexHolds ε as ρ h) :
    ∀ F ∈ lengthFloor G Γ as i, (IndexFact.linear F).HoldsAt ε ρ h := by
  intro F hF
  unfold lengthFloor at hF
  split at hF
  · rename_i hd
    simp only [List.mem_singleton] at hF
    subst hF
    have ⟨m, hm, hm0⟩ : ∃ m : Int, termValue ε ρ h (.length i) = some m ∧ 0 ≤ m := by
      rcases Bool.or_eq_true_iff.mp hd with htd | harr
      · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (termDefined_sound has htd)
        have hm0 : 0 ≤ m := by
          obtain ⟨_, ls, _, _, rfl, _⟩ := lengthOf_spine (by simpa only [termValue_length] using hm)
          omega
        exact ⟨m, hm, hm0⟩
      · obtain ⟨m, hm⟩ := arraySlot_length (ε := ε) harr he hh
        exact ⟨(m : Int), hm, by omega⟩
    refine ⟨fun t ht => ?_, ?_⟩
    · simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_singleton] at ht
      subst ht
      simp [hm]
    · simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hm, Option.getD_some]
      omega
  · cases hF

open HeapKnowledge in
/-- **Rule Entry's premises at a push** (`push-append`): at the call `t`
appending the slots `args` to the receiver slot `i`, where its normal exit
states the receiver's growth and the append (`statesExtension`,
`statesAppend`), `old(Σ)` the entry's unconditional linear facts and the
floor of the receiver's length (`lengthFloor`), the terms the growth keeps
(`keptOf growChanges`), and the relation of the exact postcondition
`|x| = old(|x|) + count` (`IndexWrites.lengthGrowth`) with the growth of
each other term (`growth`). -/
@[nospecialize] def appendEntry (G : NormalGraph ι) (Γ : List (Ty ι)) (eff : Effect) (t : Tm) (k : Knowledge) :
    Option Entry :=
  match t with
  | .invoke _ (.var i) args =>
    if statesExtension eff && statesAppend eff && IndexWrites.appendSlots Γ.length args then
      let pre := IndexWrites.unconditionalLinear k.indices ++ lengthFloor G Γ k.indices i
      some ⟨IndexWrites.keptOf growChanges (growFirst k t), pre,
        (IndexWrites.lengthGrowth i args.length).join (growth (IndexWrites.grownOf growChanges (growFirst k t)) pre)⟩
    else none
  | _ => none

open HeapKnowledge in
omit [DecidableEq ι] in
/-- Rule Entry's premises hold at a push (proved): the entry's facts hold
before the call, and its normal exit's postconditions state the growth and
the append of value actuals. -/
theorem appendEntry_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {eff : Effect} {t : Tm} {k : Knowledge}
    {E : Entry} {ρ : Env} {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT (nw + 1)}
    (hE : appendEntry G Γ eff t k = some E) (hv : ∀ i, i < Γ.length → isVal (ρ i) = true)
    (he : EnvOk G Γ ρ (nw + 1) W) (hk : Holds k ε ρ h) (hok : HeapOk (nw + 1) W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v) :
    E.Holds ε ρ h ρ h' := by
  unfold appendEntry at hE
  split at hE
  · rename_i f i args
    split at hE
    · rename_i hc
      cases hE
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hex, ha⟩, hs⟩ := hc
      have hgrow := statesExtension_grows hex hq
      have happ := statesAppend_appends ha hq
      have hf := growFirst_kept hk hok hρ hgrow
      simp only [ExpressionEffects.receiverOf, ExpressionEffects.actualsOf, instantiate, Nat.not_lt_zero,
        ite_false, Nat.sub_zero] at hgrow happ
      refine ⟨fun F hF => ?_, IndexWrites.keptOf_sound (receiverGrows_changes hgrow) hf,
        StepRelation.join_holds (IndexWrites.lengthGrowth_holds fun m hm => ?_)
          (growth_holds (IndexWrites.grownOf_sound (receiverGrows_changes hgrow) hf))⟩
      · rcases List.mem_append.mp hF with hF | hF
        · exact IndexWrites.unconditionalLinear_holds hk.2.2.2.2.2 F hF
        · exact lengthFloor_holds he hok hk.2.2.2.2.2 F hF
      · have hl := appended_length hgrow happ (IndexWrites.appendSlots_values hv hs) hm
        simpa [instantiateArgs_eq_map] using hl
    · cases hE
  · cases hE

open HeapKnowledge in
/-- **The facts a push carries** (`push-append`): rule Entry's consequences
at a push (`appendEntry`), renamed past the result: the unconditional linear
facts of the call's entry, each term the growth keeps read after it, the
receiver's length `count` longer, and the length at least `count` where the
entry states it defined or `Γ` types it an array. -/
@[nospecialize] def linearAppendKept (G : NormalGraph ι) (Γ : List (Ty ι)) (eff : Effect) (t : Tm) (k : Knowledge) :
    List IndexAtom :=
  match appendEntry G Γ eff t k with
  | some E => shiftIndices (E.consequences.map fun F => { fact := .linear F })
  | none => []

open HeapKnowledge in
omit [DecidableEq ι] in
theorem linearAppendKept_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {eff : Effect} {t : Tm} {k : Knowledge}
    {ρ : Env} {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT (nw + 1)}
    (hv : ∀ i, i < Γ.length → isVal (ρ i) = true) (he : EnvOk G Γ ρ (nw + 1) W) (hk : Holds k ε ρ h)
    (hok : HeapOk (nw + 1) W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v) :
    IndexHolds ε (linearAppendKept G Γ eff t k) (push v ρ) h' := by
  unfold linearAppendKept
  split
  · rename_i E hE
    refine shiftIndices_holds fun a ha _ => ?_
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp ha
    exact entry_sound (appendEntry_holds hE hv he hk hok hρ hq) F hF
  · exact indexHolds_nil _ _

/-! ### Quantified facts across a typed array's element write (ARITHMETIC.md, "Quantified clauses") -/


open HeapKnowledge in
/-- Whether the atoms `as` state a body fact of the value of the slot `x`
written at the index the slot `i` holds: the fact with the index read as `i`
and the element as `x`, each term defined and kept by the write. -/
def writtenBody (as : List IndexAtom) (i x : Nat) : BodyClause → Bool
  | .guarded _ _ _ => false
  | .either A B => writtenBody as i x A || writtenBody as i x B
  | .clause (.either _ _) => false
  | .clause (.atom F) => (F.vars.all fun v => match v with | .offset _ | .parallel _ _ _ _ _ => false | _ => true) &&
    match F.mapVars (some ∘ Bound.inst i x) with
    | some G => G.vars.all (fun t => termDefined as t && t.keptBy writeChanges (fun _ _ => false)) && entailsKnown as G
    | none => false

open HeapKnowledge in
/-- Exact `atIndex` equalities established at the written index `i` of a typed
array `b` by `b[i] = x`: the element equals `x`, and each active bitmask
`M ∈ IndexWrites.masksOf k.indices` of the element equals `bitMask(M, x)`,
as well as `x` itself when `M` is a low-bit mask with `0 ≤ x ≤ M` and the
exact masked constant when `x` is a known nonnegative int32 constant. -/
def writeAtIndexAtoms (k : Knowledge) (b i x : Nat) : List IndexAtom :=
  let K := knownOf k.indices
  let mkEq (bd : Bound) (t : Term) : List IndexAtom :=
    [{ fact := .atIndex b [] (.ofSlot i) none (.atom (.le [(bd, 1), (.free t, -1)] 0)) },
     { fact := .atIndex b [] (.ofSlot i) none (.atom (.le [(.free t, 1), (bd, -1)] 0)) }]
  let mkConst (bd : Bound) (c : Int) : List IndexAtom :=
    [{ fact := .atIndex b [] (.ofSlot i) none (.atom (.le [(bd, 1)] c)) },
     { fact := .atIndex b [] (.ofSlot i) none (.atom (.le [(bd, -1)] (-c))) }]
  let xConst := IndexWrites.knownConstant k x
  mkEq .elem (.value x) ++
    (IndexWrites.masksOf k.indices).flatMap fun M =>
      let bd := Bound.project (.bitMask M) []
      mkEq bd (.now (.bitMask M) x []) ++
      (if (M &&& (M + 1)) == 0 && K.entails (.le [(.value x, -1)] 0) &&
          K.entails (.le [(.value x, 1)] (M : Int)) then
        mkEq bd (.value x)
      else []) ++
      (match xConst with
       | some c =>
         if 0 ≤ c && c < 2 ^ 31 then mkConst bd ((c.toNat &&& M : Nat) : Int) else []
       | none => [])

open HeapKnowledge in
/-- Whether `kd` is a valid numeric/bitmask projection directly defined on any
integer value `ek.Takes v`. -/
def isValidViewMask : Term.Kind → Bool
  | .value => true
  | .bitMask m => decide (m < 2 ^ 31)
  | _ => false

open HeapKnowledge in
/-- Look up a slot `f` known equal to `(s', p')[i]` before a view write, either
from an `element f y i` atom (`parallelSlot`) or an `atIndex` equality to a
slot (`atIndexTermOrConst`). -/
def preWriteViewSlot (K : Linear.Known Term) (ls : HeapLinks.Links) (as : List IndexAtom)
    (s' : Nat) (p' : List String) (i : Nat) : Option Nat :=
  match parallelSlot K ls as s' p' i with
  | some f => some f
  | none =>
    match atIndexTermOrConst K ls as s' p' i .value with
    | some (.inl t) => if !t.atEntry && t.kind == .value && t.path.isEmpty then some t.slot else none
    | _ => none

open HeapKnowledge in
/-- Whether an exact typed-array write `b[i] = x` keeps a quantified fact over
an ordinary (non-view) array `(s, p)` whose body reads `b` in parallel: every
non-view location is untouched by `{all-views: grow}`, and at `b` either `i`
lies outside the quantified interval `[start, stop)` or `x`
preserves every numeric/bitmask projection of `b[i]` compared to a pre-write
read (`preWriteViewSlot`, covering disjoint-bit OR updates `flags[i] |= 0x8`). -/
@[nospecialize] def everyParallelViewWritten (G : NormalGraph ι) (Γ : List (Ty ι))
    (k : Knowledge) (b i x : Nat) (a : IndexAtom) : Bool :=
  match a.fact with
  | .every s p start stop body =>
    let K := knownOf k.indices
    let iB := IndexBound.ofTerm (.value i)
    HeapExpressionRules.arrayPathOf G Γ s p &&
      intSlot k.indices i &&
      body.all (fun B =>
        B.targets.all (fun
          | .self _ => true
          | .parallel s' p' _ _ => HeapExpressionRules.arrayPathOf G Γ s' p') &&
        B.vars.all (fun
          | .parallel s' p' sh kd ep =>
            HeapExpressionRules.arrayPathOf G Γ s' p' ||
              (sh.isZero && ep.isEmpty && isValidViewMask kd && readsPath k.links s' p' b)
          | _ => true)) &&
      (K.entails (stop.leFact iB) || K.entails (iB.leFact start 1) ||
        body.all fun B => B.vars.all fun
          | .parallel s' p' _ kd [] =>
            if !HeapExpressionRules.arrayPathOf G Γ s' p' && readsPath k.links s' p' b then
              match preWriteViewSlot K k.links k.indices s' p' i with
              | some f =>
                K.entails (.le [(Term.now kd x [], 1), (Term.now kd f [], -1)] 0) &&
                K.entails (.le [(Term.now kd f [], 1), (Term.now kd x [], -1)] 0)
              | none => false
            else true
          | _ => true)
  | _ => false

open HeapKnowledge in
/-- Whether an exact write `b[i] = x` of a typed array keeps a quantified
atom of its entry `k` (`every-write`): over the view of `b`'s class, its path
empty, its bound and body kept by the write, and the index at or past the
bound, or each body fact stated of `x` at `i`. -/
def everyWritten (k : Knowledge) (b i x : Nat) (a : IndexAtom) : Bool :=
  match a.fact with
  | .every s [] st0 st1 body =>
    let iB := IndexBound.ofTerm (.value i)
    (s == b || (HeapLinks.aliases k.links b).contains s) &&
      st0.keptBy writeChanges (fun _ _ => false) &&
      st1.keptBy writeChanges (fun _ _ => false) &&
      body.all (bodyClauseKeptBy writeChanges (fun _ _ => false)) &&
      intSlot k.indices i &&
      (entailsKnown k.indices (st1.leFact iB) || entailsKnown k.indices (iB.leFact st0 1) ||
        body.all (writtenBody k.indices i x))
  | _ => false

open HeapKnowledge in
/-- A prefix ending at a known term after the written index. The old interval
covers every smaller index above `st0`, and the written value satisfies the body. -/
def writtenPrefix (k : Knowledge) (b i x : Nat) (a : IndexAtom) (next : Term) : Option IndexAtom :=
  match a.fact with
  | .every s [] st0 st1 body =>
    let iB := IndexBound.ofTerm (.value i)
    if (s == b || (HeapLinks.aliases k.links b).contains s) &&
        st0.keptBy writeChanges (fun _ _ => false) &&
        termDefined k.indices next && next.keptBy writeChanges (fun _ _ => false) &&
        body.all (bodyClauseKeptBy writeChanges (fun _ _ => false)) &&
        entailsKnown k.indices (.le [(next, 1), (.value i, -1)] 1) &&
        entailsKnown k.indices (iB.leFact st1) &&
        body.all (writtenBody k.indices i x)
    then some { a with fact := .every s [] st0 (IndexBound.ofTerm next) body } else none
  | _ => none

/-- The quantified and indexed atoms of a call's entry `k` an exact element
write keeps or produces (`everyWritten`, `writtenPrefix`,
`everyParallelViewWritten`, `writeAtIndexAtoms`), renamed past the result; none
of any other call. A derived rule of the note's Entry at View-Write's
postcondition. -/
@[nospecialize] def writeKept (G : NormalGraph ι) (Γ : List (Ty ι)) (eff : Effect) (t : Tm)
    (k : HeapKnowledge.Knowledge) : List HeapKnowledge.IndexAtom :=
  match t with
  | .invoke _ _ [.var b, .var i, .var x] =>
    if statesViewGrowth eff && (exactWriteOf eff).isSome then
    let i := HeapKnowledge.pick (HeapLinks.aliases k.links) (HeapKnowledge.intSlot k.indices) i
    let x := HeapKnowledge.pick (HeapLinks.aliases k.links) (HeapKnowledge.intSlot k.indices) x
    HeapKnowledge.shiftIndices (k.indices.filter (everyWritten k b i x) ++
      k.indices.filter (everyParallelViewWritten G Γ k b i x) ++
      writeAtIndexAtoms k b i x ++
      (k.indices.filter fun a => match a.fact with | .every _ [] _ _ _ => true | _ => false).flatMap fun a =>
        (HeapKnowledge.definedTerms k.indices).eraseDups.filterMap fun next =>
          if HeapKnowledge.entailsKnown k.indices (.le [(.value i, 1), (next, -1)] (-1))
          then writtenPrefix k b i x a next else none)
    else []
  | _ => []

open HeapKnowledge in
private theorem writtenBody_sound {ρ : Env} {h h' : Heap} {i x i0 l : Nat} {ls' : List (Option Nat)}
    {as : List IndexAtom} {k : CallEffects.ElementKind}
    (he : IndexHolds ε as ρ h) (hc : writeChanges.Holds h h')
    (hki : intValue (ρ i) = some (i0 : Int))
    (hl : ls'[i0]? = some (some l)) (hlv : h'[l]? = some (k.convert (ρ x))) :
    ∀ {B : BodyClause}, writtenBody as i x B = true → B.HoldsAt ε ρ h' ls' i0
  | .guarded _ _ _, hwb => by simp [writtenBody] at hwb
  | .either A B, hwb => by
    simp only [writtenBody, Bool.or_eq_true] at hwb
    exact hwb.imp (writtenBody_sound he hc hki hl hlv) (writtenBody_sound he hc hki hl hlv)
  | .clause (.either _ _), hwb => by simp [writtenBody] at hwb
  | .clause (.atom F), hwb => by
    simp only [writtenBody, Bool.and_eq_true] at hwb
    obtain ⟨hvalid, hwb⟩ := hwb
    cases hG : F.mapVars (some ∘ Bound.inst i x) with
    | some G =>
      rw [hG] at hwb
      simp only [Bool.and_eq_true, List.all_eq_true] at hwb
      obtain ⟨hd, hent⟩ := hwb
      have hG0 : (IndexFact.linear G).HoldsAt ε ρ h :=
        ⟨fun t ht => termDefined_sound he (hd t ht).1, entailsKnown_sound he hent⟩
      have hG1 := IndexFact.holdsAt_kept hc firstKept_none
        (by simp only [IndexFact.keptBy, Bool.or_eq_true]; exact .inl (List.all_eq_true.mpr fun t ht => (hd t ht).2))
        hG0
      refine (factAt_mapVars (val' := termValue ε ρ h') hG fun y hy t ht => ?_).mp hG1
      simp only [Function.comp_apply, Option.some.injEq] at ht
      subst ht
      cases y with
      | index => simp only [Bound.inst, termValue_value, hki, boundValue]
      | elem => simp only [Bound.inst, termValue_value, boundValue, elementInt, hl, hlv, Option.bind_some,
          CallEffects.ElementKind.intValue_convert]
      | offset d => have := List.all_eq_true.mp hvalid (.offset d) hy; simp at this
      | parallel s p sh kd ep => have := List.all_eq_true.mp hvalid (.parallel s p sh kd ep) hy; simp at this
      | project kd p => simp only [Bound.inst, boundValue, hl, hlv, Option.bind_some, termValue, termAt, Bool.false_eq_true, ite_false,
          CallEffects.ElementKind.readPath_convert]
      | free t => rfl
    | none => simp [hG] at hwb

open HeapKnowledge in
/-- **An exact element write keeps a quantified fact over its view**
(`every-write`): each element at another index is the same location, holding
the same number; the element at the index is the written value, which meets
the body or lies outside `[st0, st1)`. -/
theorem every_written {ρ : Env} {h h' : Heap} {b i x s : Nat} {st0 st1 : IndexBound} {body : List BodyClause}
    {as : List IndexAtom} (he : IndexHolds ε as ρ h) (hs : ρ s = ρ b)
    (hc : writeChanges.Holds h h') {k : CallEffects.ElementKind}
    (hx : CallEffects.ExactWrite k [ρ b, ρ i, ρ x] h h' ∧ CallEffects.ExactPre k [ρ b, ρ i, ρ x])
    (hst0 : st0.keptBy writeChanges (fun _ _ => false) = true)
    (hst1 : st1.keptBy writeChanges (fun _ _ => false) = true)
    (hb : body.all (bodyClauseKeptBy writeChanges (fun _ _ => false)) = true)
    (hnew : (entailsKnown as (st1.leFact (.ofTerm (.value i))) = true ∨
             entailsKnown as ((IndexBound.ofTerm (.value i)).leFact st0 1) = true) ∨
            body.all (writtenBody as i x) = true)
    (hF : (IndexFact.every s [] st0 st1 body).HoldsAt ε ρ h) : (IndexFact.every s [] st0 st1 body).HoldsAt ε ρ h' := by
  obtain ⟨w, sto, ls, m0, n, hw, hsto, hls, hm0, hn, hall⟩ := hF
  simp only [readPath, Option.some.injEq] at hw
  subst hw
  obtain ⟨ls', kb, i0, hls', hkb, hi0, hj, l, hl, hlv⟩ := hx.1.taken hx.2 sto ls (by simpa [hs] using hsto) hls
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hkb hlv
  have hki : intValue (ρ i) = some (i0 : Int) := by rw [hkb]; exact intValue_num hi0
  have hiEval : (IndexBound.ofTerm (.value i)).eval ε ρ h = some (i0 : Int) := by
    simp [IndexBound.ofTerm, IndexBound.eval, termValue_value, hki]
  have hm0' := IndexBound.eval_kept hc firstKept_none hst0 hm0
  have hn' := IndexBound.eval_kept hc firstKept_none hst1 hn
  refine ⟨ρ s, sto, ls', m0, n, rfl, hsto, hls', hm0', hn', fun j hlo hj' B hB => ?_⟩
  have hbF := List.all_eq_true.mp hb B hB
  by_cases hji : j = i0
  · subst hji
    rcases hnew with (hent | hent) | hbody
    · have := IndexBound.leFact_sound hn hiEval (entailsKnown_sound he hent); omega
    · have := IndexBound.leFact_sound hiEval hm0 (entailsKnown_sound he hent); omega
    · exact writtenBody_sound he hc hki hl hlv (List.all_eq_true.mp hbody B hB)
  · refine BodyClause.holdsAt_monotone (fun t ht w hw => ?_) (fun y m hky hy => ?_) (fun y m hgy hy => ?_) hbF (hall j hlo hj' B hB)
    · cases t with
      | parallel _ _ _ _ => simp [ElemTarget.keptBy] at ht
      | self ep =>
        simp only [ElemTarget.keptBy, List.isEmpty_iff] at ht; subst ht
        simp only [ElemTarget.read] at hw ⊢
        split at hw
        · rename_i l' hl'
          obtain ⟨u, hu, hrg⟩ := Option.bind_eq_some_iff.mp hw
          simp only [readGuard, Option.some.injEq] at hrg; subst hrg
          obtain ⟨l'', hl'', hu'⟩ := hj j hji l' u hl' hu
          simp [hl'', hu', readGuard]
        · cases hw
    · cases y with
      | index => exact hy
      | elem =>
        simp only [boundValue, elementInt] at hy ⊢
        split at hy
        · rename_i l' hl'
          obtain ⟨u, hu, hum⟩ := Option.bind_eq_some_iff.mp hy
          obtain ⟨l'', hl'', hu'⟩ := hj j hji l' u hl' hu
          simp only [hl'', hu', Option.bind_some, hum]
        · cases hy
      | project k p =>
        simp only [boundValue] at hy ⊢
        split at hy
        · rename_i l' hl'
          obtain ⟨u, hu, hum⟩ := Option.bind_eq_some_iff.mp hy
          obtain ⟨l'', hl'', hu'⟩ := hj j hji l' u hl' hu
          rw [hl'']
          exact Option.bind_eq_some_iff.mpr ⟨u, hu', termValue_kept (ε := ε) hc firstKept_none hky hum⟩
        · cases hy
      | parallel _ _ _ _ _ | offset _ => simp [Bound.keptBy] at hky
      | free t => exact termValue_kept (ε := ε) hc firstKept_none hky hy
    · cases y with
      | index | elem | parallel _ _ _ _ _ | offset _ => simp [Bound.grownBy] at hgy
      | project _ _ | free _ => simp [Bound.grownBy, Term.grownBy, writeChanges, CallEffects.ElementWrite.changes] at hgy

open HeapKnowledge in
/-- **An exact element write establishes a prefix through its index**
Every target index other than the written index belongs to the old interval;
the written index holds the value checked against the body. -/
theorem every_written_prefix {ρ : Env} {h h' : Heap} {b i x s : Nat} {st0 st1 : IndexBound} {next : Term}
    {body : List BodyClause} {as : List IndexAtom} (he : IndexHolds ε as ρ h) (hs : ρ s = ρ b)
    (hc : writeChanges.Holds h h') {k : CallEffects.ElementKind}
    (hx : CallEffects.ExactWrite k [ρ b, ρ i, ρ x] h h' ∧ CallEffects.ExactPre k [ρ b, ρ i, ρ x])
    (hst0 : st0.keptBy writeChanges (fun _ _ => false) = true)
    (hnext : termDefined as next = true)
    (hcover : entailsKnown as (.le [(next, 1), (.value i, -1)] 1) = true)
    (hstart : entailsKnown as ((IndexBound.ofTerm (.value i)).leFact st1) = true)
    (hst : next.keptBy writeChanges (fun _ _ => false) = true)
    (hb : body.all (bodyClauseKeptBy writeChanges (fun _ _ => false)) = true)
    (hbody : body.all (writtenBody as i x) = true)
    (hF : (IndexFact.every s [] st0 st1 body).HoldsAt ε ρ h) :
    (IndexFact.every s [] st0 (IndexBound.ofTerm next) body).HoldsAt ε ρ h' := by
  obtain ⟨w, sto, ls, m0, n, hw, hsto, hls, hm0, hn, hall⟩ := hF
  simp only [readPath, Option.some.injEq] at hw
  subst hw
  obtain ⟨ls', kb, i0, hls', hkb, hi0, hj, l, hl, hlv⟩ := hx.1.taken hx.2 sto ls (by simpa [hs] using hsto) hls
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hkb hlv
  have hki : intValue (ρ i) = some (i0 : Int) := by rw [hkb]; exact intValue_num hi0
  have hiEval : (IndexBound.ofTerm (.value i)).eval ε ρ h = some (i0 : Int) := by
    simp [IndexBound.ofTerm, IndexBound.eval, termValue_value, hki]
  obtain ⟨n', hn0⟩ := Option.isSome_iff_exists.mp (termDefined_sound he hnext)
  have hm0' := IndexBound.eval_kept hc firstKept_none hst0 hm0
  have hn' := termValue_kept hc firstKept_none hst hn0
  have hcoverage := entailsKnown_sound he hcover
  have hbegin := IndexBound.leFact_sound hiEval hn (entailsKnown_sound he hstart)
  simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hn0, termValue_value, hki,
    Option.getD_some] at hcoverage
  refine ⟨ρ s, sto, ls', m0, n', rfl, hsto, hls', hm0', by simp [IndexBound.ofTerm, IndexBound.eval, hn'],
    fun j hlo hj' B hB => ?_⟩
  have hbF := List.all_eq_true.mp hb B hB
  by_cases hji : j = i0
  · subst hji
    exact writtenBody_sound he hc hki hl hlv (List.all_eq_true.mp hbody B hB)
  · refine BodyClause.holdsAt_monotone (fun t ht w hw => ?_) (fun y m hky hy => ?_) (fun y m hgy hy => ?_) hbF (hall j hlo (by omega) B hB)
    · cases t with
      | parallel _ _ _ _ => simp [ElemTarget.keptBy] at ht
      | self ep =>
        simp only [ElemTarget.keptBy, List.isEmpty_iff] at ht; subst ht
        simp only [ElemTarget.read] at hw ⊢
        split at hw
        · rename_i l' hl'
          obtain ⟨u, hu, hrg⟩ := Option.bind_eq_some_iff.mp hw
          simp only [readGuard, Option.some.injEq] at hrg; subst hrg
          obtain ⟨l'', hl'', hu'⟩ := hj j hji l' u hl' hu
          simp [hl'', hu', readGuard]
        · cases hw
    · cases y with
      | index => exact hy
      | elem =>
        simp only [boundValue, elementInt] at hy ⊢
        split at hy
        · rename_i l' hl'
          obtain ⟨u, hu, hum⟩ := Option.bind_eq_some_iff.mp hy
          obtain ⟨l'', hl'', hu'⟩ := hj j hji l' u hl' hu
          simp only [hl'', hu', Option.bind_some, hum]
        · cases hy
      | project k p =>
        simp only [boundValue] at hy ⊢
        split at hy
        · rename_i l' hl'
          obtain ⟨u, hu, hum⟩ := Option.bind_eq_some_iff.mp hy
          obtain ⟨l'', hl'', hu'⟩ := hj j hji l' u hl' hu
          rw [hl'']
          exact Option.bind_eq_some_iff.mpr ⟨u, hu', termValue_kept (ε := ε) hc firstKept_none hky hum⟩
        · cases hy
      | parallel _ _ _ _ _ | offset _ => simp [Bound.keptBy] at hky
      | free t => exact termValue_kept (ε := ε) hc firstKept_none hky hy
    · cases y with
      | index | elem | parallel _ _ _ _ _ | offset _ => simp [Bound.grownBy] at hgy
      | project _ _ | free _ => simp [Bound.grownBy, Term.grownBy, writeChanges, CallEffects.ElementWrite.changes] at hgy

open HeapKnowledge in
private theorem nonView_readPath {n : Nat} {W : WorldT n} {h h' : Heap}
    (hok : HeapOk n W h)
    (hnv : ∀ (l : Nat) (u : Val), h[l]? = some u → (∀ f cs, u ≠ Tm.viewSpine f cs) → h'[l]? = some u) :
    ∀ {p : List String} {v w : Val}, RefsOk W v → readPath h v p = some w → readPath h' v p = some w
  | [], _, _, _, hr => hr
  | f :: q, v, w, hv, hr => by
    cases v with
    | objAt fs cd oid =>
      simp only [readPath] at hr ⊢
      cases hlk : fs.lookup (.str f) with
      | none => simp [hlk] at hr
      | some l =>
        simp only [hlk] at hr ⊢
        cases hu : h[l]? with
        | none => simp [hu] at hr
        | some u =>
          simp only [hu] at hr
          have hmem_ref : Ref.slot (.str f) l ∈ refs (.objAt fs cd oid) := by
            cases cd <;> simp [refs, objRefs, PositiveRules.mem_of_lookup hlk]
          have hsr : SlotRole (.str f) (roleAt W l) := hv _ hmem_ref
          obtain ⟨r, hrw⟩ : ∃ r, roleAt W l = some r := by
            cases hr : roleAt W l with
            | none => rw [hr] at hsr; cases hsr
            | some r => exact ⟨r, rfl⟩
          obtain ⟨u', hu', hsh⟩ := hok.2 l r hrw
          rw [hu] at hu'; cases hu'
          have hne : ∀ fmt cs, u ≠ Tm.viewSpine fmt cs := by
            intro fmt cs heq; subst heq
            cases r with
            | spine sf => cases sf with
              | array => obtain ⟨_, h⟩ := hsh.1; cases h
              | view _ _ => rw [hrw] at hsr; exact hsr
            | _ => simp [Shape, Cat, isSourceVal] at hsh
          rw [hnv l u hu hne]
          exact nonView_readPath hok hnv hsh.2 hr
    | _ => simp [readPath] at hr

open HeapKnowledge in
private theorem nonView_readGuard {n : Nat} {W : WorldT n} {h h' : Heap}
    (hok : HeapOk n W h)
    (hnv : ∀ (l : Nat) (u : Val), h[l]? = some u → (∀ f cs, u ≠ Tm.viewSpine f cs) → h'[l]? = some u) :
    ∀ {p : List String} {v w : Val}, RefsOk W v → readGuard h v p = some w → readGuard h' v p = some w
  | [], _, _, _, hr => hr
  | f :: q, v, w, hv, hr => by
    cases v with
    | objAt fs cd oid =>
      simp only [readGuard] at hr ⊢
      cases hlk : fs.lookup (.str f) with
      | none =>
        simp only [hlk] at hr ⊢
        split at hr
        · rename_i hpr
          simp only [hpr, ite_true]
          exact nonView_readGuard hok hnv (fun _ h => by simp [refs] at h) hr
        · cases hr
      | some l =>
        simp only [hlk] at hr ⊢
        cases hu : h[l]? with
        | none => simp [hu] at hr
        | some u =>
          simp only [hu] at hr
          have hmem_ref : Ref.slot (.str f) l ∈ refs (.objAt fs cd oid) := by
            cases cd <;> simp [refs, objRefs, PositiveRules.mem_of_lookup hlk]
          have hsr : SlotRole (.str f) (roleAt W l) := hv _ hmem_ref
          obtain ⟨r, hrw⟩ : ∃ r, roleAt W l = some r := by
            cases hr : roleAt W l with
            | none => rw [hr] at hsr; cases hsr
            | some r => exact ⟨r, rfl⟩
          obtain ⟨u', hu', hsh⟩ := hok.2 l r hrw
          rw [hu] at hu'; cases hu'
          have hne : ∀ fmt cs, u ≠ Tm.viewSpine fmt cs := by
            intro fmt cs heq; subst heq
            cases r with
            | spine sf => cases sf with
              | array => obtain ⟨_, h⟩ := hsh.1; cases h
              | view _ _ => rw [hrw] at hsr; exact hsr
            | _ => simp [Shape, Cat, isSourceVal] at hsh
          rw [hnv l u hu hne]
          exact nonView_readGuard hok hnv hsh.2 hr
    | _ => simp [readGuard] at hr

open HeapKnowledge in
private theorem nonView_termValue {n : Nat} {W : WorldT n} {ρ : Env} {h h' : Heap}
    (hok : HeapOk n W h) (hρ : RootsOk W ρ)
    (hnv : ∀ (l : Nat) (u : Val), h[l]? = some u → (∀ f cs, u ≠ Tm.viewSpine f cs) → h'[l]? = some u)
    {t : Term} {z : Int} (ht : termValue ε ρ h t = some z) :
    termValue ε ρ h' t = some z := by
  obtain ⟨kd, s, p, ent⟩ := t
  cases ent with
  | true => exact termValue_entry_some rfl ht
  | false =>
    rw [termValue_now rfl] at ht ⊢
    simp only [termAt, Option.bind_eq_some_iff] at ht ⊢
    obtain ⟨w, hrp, hkv⟩ := ht
    refine ⟨w, nonView_readPath hok hnv (hρ s) hrp, ?_⟩
    cases kd with
    | value | strLength | view | bitMask _ => exact hkv
    | length =>
      obtain ⟨st, ls, hsp, hls, rfl, hmax⟩ := lengthOf_spine hkv
      exact lengthOf_of_spine hsp (hnv st (.arr ls) hls fun _ _ h => by cases h) hmax

open HeapKnowledge in
omit [DecidableEq ι] in
private theorem arraySlot_spine {G : NormalGraph ι} {Γ : List (Ty ι)} {j : Nat} {ρ n W h}
    (hc : IndexWrites.arraySlot G Γ j = true) (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h) :
    ∃ st ls, Footprints.spineOf (ρ j) = some st ∧ h[st]? = some (.arr ls) := by
  unfold IndexWrites.arraySlot at hc
  split at hc; case h_2 => cases hc
  rename_i R hR
  split at hc; case h_2 => cases hc
  rename_i fs vs os ms ks st hexp
  split at hc; case h_2 => cases hc
  rename_i S hS
  split at hc; case h_2 => cases hc
  rename_i T hT
  have hsem := (ProgramTyping.represents_raw (show ProgramTyping.Represents G R (.refs fs [] vs os ms ks st) from hexp) _ W _) (he.2 j R hR)
  obtain ⟨flds, l, c, oid, hobj, hf, hlc, hag⟩ : ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr (n + 1)) (oid : Nat),
      ρ j = .objAt flds .absent oid ∧ flds.lookup arraySpineKey = some l ∧ lookup W l = some c ∧
      ∀ (i : Nat) (hi : i < n + 1) (W' : WorldT i) (u : Val), c i hi W' u → meaning G S i W' u := by
    cases hfs : (Stored.views fs).lookup arraySpineKey with
    | some S' =>
      rw [hfs] at hS
      simp only [Option.orElse_some, Option.some.injEq] at hS
      subst hS
      obtain ⟨_, hm⟩ := Stored.mem_views.mp (PositiveRules.mem_of_lookup hfs)
      obtain ⟨flds, l, c, oid, hobj, hf, hlc, hag⟩ := recT_at
        (ReferenceConjunctions.mem_famsOf.mpr ⟨S', hm, rfl⟩) hsem.1.1
      exact ⟨flds, l, c, oid, hobj, hf, hlc, fun i hi W' u hu => (hag i hi W' u).mp hu⟩
    | none =>
      rw [hfs] at hS
      simp only [Option.orElse_none] at hS
      exact viewsT_at (ReferenceConjunctions.mem_viewsOf.mpr ⟨S, PositiveRules.mem_of_lookup hS, rfl⟩)
        (by simp [arraySpineKey, lengthKey]) hsem.2.1
  obtain ⟨w, hwv, hwc⟩ := hh.1.2 l c hlc
  have hspine : meaning G S n (trunc n (Nat.le_succ n) W) w := hag n (by omega) _ _ (hwc n (by omega))
  obtain ⟨ls, rfl, -⟩ := (ProgramTyping.represents_raw (show ProgramTyping.Represents G S (.list T []) from hT) _ _ _ hspine).1
  exact ⟨l, ls, by simp [hobj, Footprints.spineOf, Footprints.fieldsOf, hf], hwv⟩

open HeapKnowledge in
private theorem exactPre_view_spine {ek : CallEffects.ElementKind} {b i x : Nat} {ρ : Env} {nw : Nat}
    {W : WorldT nw} {h : Heap} (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hp : CallEffects.ExactPre ek [ρ b, ρ i, ρ x]) :
    ∃ (sto : Nat) (cs : List Nat), elementsOf (ρ b) = some sto ∧ h[sto]?.bind spineEntries = some (cs.map some) := by
  obtain ⟨-, bi, i0, N, -, -, hN, -⟩ := hp
  simp only [List.getD_cons_zero] at hN
  obtain ⟨fs, oid, sto, f, Nn, hvb, rfl, -⟩ := viewLengthOf_inv hN
  have hrv : RefsOk W (.viewAt fs oid sto f Nn) := hvb ▸ hρ b
  have hsel := RefsOk.view_selects hrv h
  have hmem : Ref.view sto f Nn (fs.lookup arraySpineKey).isNone ∈ refs (.viewAt fs oid sto f Nn) := by
    simp [refs]
  have hrole : roleAt W sto = some (.spine (.view f Nn)) := (hrv _ hmem).2
  obtain ⟨u, hu, hsh⟩ := hok.2 sto (.spine (.view f Nn)) hrole
  obtain ⟨cs, rfl, -⟩ := hsh.1
  exact ⟨sto, cs, by rw [hvb]; exact hsel.1, by simp [hu, spineEntries]⟩

open HeapKnowledge in
private theorem writeAtIndexAtoms_holds {ek : CallEffects.ElementKind} {k : Knowledge} {b i x : Nat}
    {ρ : Env} {nw : Nat} {W : WorldT nw} {h h' : Heap}
    (hk : Holds k ε ρ h) (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hx : CallEffects.ExactWrite ek [ρ b, ρ i, ρ x] h h' ∧ CallEffects.ExactPre ek [ρ b, ρ i, ρ x]) :
    IndexHolds ε (writeAtIndexAtoms k b i x) ρ h' := by
  obtain ⟨sto, cs, hel, hls⟩ := exactPre_view_spine hok hρ hx.2
  obtain ⟨ls', kb, i0, hls', hkb, hi0, -, l, hl, hlv⟩ := hx.1.taken hx.2 sto (cs.map some) hel hls
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hkb hlv
  have hki : intValue (ρ i) = some (i0 : Int) := by rw [hkb]; exact intValue_num hi0
  have hi0_lt : i0 < ls'.length := (List.getElem?_eq_some_iff.mp hl).1
  obtain ⟨bx, ix, hbx, hsx, -⟩ := hx.2.1
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hbx
  have hix : intValue (ρ x) = some ix := by rw [hbx]; exact intValue_num hsx
  have hK : (knownOf k.indices).Holds (termValuation ε ρ h) := knownOf_holds hk.2.2.2.2.2
  have mk_pair : ∀ (bd : Bound) (t : Term) (z : Int),
      boundValue ε ρ h' ls' i0 bd = some z → termValue ε ρ h' t = some z →
      ∀ a ∈ ([{ fact := .atIndex b [] (.ofSlot i) none (.atom (.le [(bd, 1), (.free t, -1)] 0)) },
              { fact := .atIndex b [] (.ofSlot i) none (.atom (.le [(.free t, 1), (bd, -1)] 0)) }] : List IndexAtom),
        a.fact.HoldsAt ε ρ h' := by
    intro bd t z hbd ht a ha
    have hbd_some : (boundValue ε ρ h' ls' i0 bd).isSome := by rw [hbd]; rfl
    have ht_some : (boundValue ε ρ h' ls' i0 (.free t)).isSome := by simp [boundValue, ht]
    have hft : boundValue ε ρ h' ls' i0 (.free t) = some z := ht
    rcases List.mem_cons.mp ha with rfl | ha
    · refine ⟨ρ b, sto, ls', i0, rfl, hel, hls', IndexShift.eval_ofSlot.mpr hki, hi0_lt,
        fun y hy => ?_, by simp only [Linear.Fact.Holds, Linear.Form.eval, hbd, hft, Option.getD_some]; omega⟩
      simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> assumption
    · simp only [List.mem_singleton] at ha; subst ha
      refine ⟨ρ b, sto, ls', i0, rfl, hel, hls', IndexShift.eval_ofSlot.mpr hki, hi0_lt,
        fun y hy => ?_, by simp only [Linear.Fact.Holds, Linear.Form.eval, hbd, hft, Option.getD_some]; omega⟩
      simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> assumption
  have mk_const : ∀ (bd : Bound) (c : Int),
      boundValue ε ρ h' ls' i0 bd = some c →
      ∀ a ∈ ([{ fact := .atIndex b [] (.ofSlot i) none (.atom (.le [(bd, 1)] c)) },
              { fact := .atIndex b [] (.ofSlot i) none (.atom (.le [(bd, -1)] (-c))) }] : List IndexAtom),
        a.fact.HoldsAt ε ρ h' := by
    intro bd c hbd a ha
    have hbd_some : (boundValue ε ρ h' ls' i0 bd).isSome := by rw [hbd]; rfl
    rcases List.mem_cons.mp ha with rfl | ha
    · refine ⟨ρ b, sto, ls', i0, rfl, hel, hls', IndexShift.eval_ofSlot.mpr hki, hi0_lt,
        fun y hy => by simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_singleton] at hy; subst hy; exact hbd_some,
        by simp only [Linear.Fact.Holds, Linear.Form.eval, hbd, Option.getD_some]; omega⟩
    · simp only [List.mem_singleton] at ha; subst ha
      refine ⟨ρ b, sto, ls', i0, rfl, hel, hls', IndexShift.eval_ofSlot.mpr hki, hi0_lt,
        fun y hy => by simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_singleton] at hy; subst hy; exact hbd_some,
        by simp only [Linear.Fact.Holds, Linear.Form.eval, hbd, Option.getD_some]; omega⟩
  intro a ha _
  unfold writeAtIndexAtoms at ha
  dsimp only at ha
  rcases List.mem_append.mp ha with ha | ha
  · exact mk_pair .elem (.value x) ix
      (by simp only [boundValue, elementInt, hl, hlv, Option.bind_some, CallEffects.ElementKind.intValue_convert, hix])
      (by simp [termValue_value, hix]) a ha
  · obtain ⟨M, hM, ha⟩ := List.mem_flatMap.mp ha
    have hMlt : M < 2 ^ 31 := IndexWrites.masksOf_lt hM
    have hbm : bitMaskOf M (ρ x) = some (intAnd (toInt32 bx) M) := by
      simp [hbx, bitMaskOf, hMlt]
    have hbd_bm : boundValue ε ρ h' ls' i0 (.project (.bitMask M) []) = some (intAnd (toInt32 bx) M) := by
      simp only [boundValue, hl, hlv, Option.bind_some, termValue, termAt, Bool.false_eq_true, ite_false,
        readPath, Option.bind_some, kindValue, CallEffects.ElementKind.bitMaskOf_convert, hbm]
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact mk_pair (.project (.bitMask M) []) (.now (.bitMask M) x []) (intAnd (toInt32 bx) M)
          hbd_bm (by simp [termValue, termAt, readPath, kindValue, hbm]) a ha
      · split at ha
        · rename_i hlow
          simp only [Bool.and_eq_true, beq_iff_eq] at hlow
          obtain ⟨⟨hmask, hge0⟩, hleM⟩ := hlow
          have h1 := Linear.Known.entails_sound hK hge0
          have h2 := Linear.Known.entails_sound hK hleM
          simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, termValue_value, hix, Option.getD_some] at h1 h2
          have hti : toInt32 bx = ix := SafeIntegers.toInt32_small hsx (by omega) (by omega)
          have heq : intAnd (toInt32 bx) M = ix := by
            rw [hti]; exact IndexNumbers.intAnd_lowMask hmask (by omega) (by omega)
          exact mk_pair (.project (.bitMask M) []) (.value x) ix (heq ▸ hbd_bm) (by simp [termValue_value, hix]) a ha
        · cases ha
    · cases hkc : IndexWrites.knownConstant k x with
      | none => simp only [hkc] at ha; cases ha
      | some c =>
        simp only [hkc] at ha
        split at ha
        · rename_i hcr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcr
          have hix_c : ix = c := by
            have hval := IndexWrites.knownConstant_sound hkc hk
            simp only [valuation, hix, Option.getD_some] at hval
            exact hval
          subst hix_c
          have hti : toInt32 bx = ix := SafeIntegers.toInt32_small hsx (by omega) hcr.2
          have heq : intAnd (toInt32 bx) M = ((ix.toNat &&& M : Nat) : Int) := by
            rw [hti]; exact IndexNumbers.intAnd_of_nonneg hcr.1
          exact mk_const (.project (.bitMask M) []) ((ix.toNat &&& M : Nat) : Int) (heq ▸ hbd_bm) a ha
        · cases ha

open HeapKnowledge in
private theorem arrayPath_spine_kept {G : NormalGraph ι} {Γ : List (Ty ι)}
    {x st : Nat} {p : List String} {w : Val} {ls : List (Option Nat)}
    {ρ : Env} {nw : Nat} {W : WorldT (nw + 1)} {h h' : Heap}
    (he : EnvOk G Γ ρ (nw + 1) W) (hok : HeapOk (nw + 1) W h) (hρ : RootsOk W ρ)
    (hnv : ∀ (l : Nat) (u : Val), h[l]? = some u → (∀ f cs, u ≠ Tm.viewSpine f cs) → h'[l]? = some u)
    (hap : HeapExpressionRules.arrayPathOf G Γ x p = true)
    (hrp : readPath h (ρ x) p = some w) (hel : elementsOf w = some st)
    (hls : h[st]?.bind spineEntries = some ls) :
    readPath h' (ρ x) p = some w ∧ h'[st]?.bind spineEntries = some ls := by
  have hsp : Footprints.spineOf w = some st := (HeapExpressionRules.arrayPathOf_sound he hok hρ x p w st hap hrp hel).1
  have hrp' : readPath h' (ρ x) p = some w := nonView_readPath hok hnv (hρ x) hrp
  have hrw : RefsOk W w := by
    clear hap hel hls hsp hrp'
    induction p generalizing w with
    | nil => simp only [readPath, Option.some.injEq] at hrp; subst hrp; exact hρ x
    | cons f q ih =>
      -- pull refs through `readPath` step by step
      have step : ∀ {u : Val} {q' : List String} {v : Val}, RefsOk W u → readPath h u q' = some v → RefsOk W v := by
        intro u q'
        induction q' generalizing u with
        | nil => intro v hu h0; simp only [readPath, Option.some.injEq] at h0; subst h0; exact hu
        | cons g gs ihg =>
          intro v hu h0
          cases u with
          | objAt fs cd oid =>
            simp only [readPath] at h0
            cases hlk : fs.lookup (.str g) with
            | none => simp [hlk] at h0
            | some l =>
              simp only [hlk] at h0
              cases hlu : h[l]? with
              | none => simp [hlu] at h0
              | some u' =>
                simp only [hlu] at h0
                exact ihg (hok.refs_at hlu) h0
          | _ => simp [readPath] at h0
      exact step (hρ x) hrp
  obtain ⟨u, hu, hspu⟩ := Option.bind_eq_some_iff.mp hls
  have hne_view : ∀ f cs, u ≠ Tm.viewSpine f cs := by
    intro f cs heq; subst heq
    cases w with
    | objAt fs cd oid =>
      simp only [Footprints.spineOf, Footprints.fieldsOf] at hsp
      have hmem : Ref.slot arraySpineKey st ∈ refs (.objAt fs cd oid) := by
        cases cd <;> simp [refs, objRefs, PositiveRules.mem_of_lookup hsp]
      have hsr : SlotRole arraySpineKey (roleAt W st) := hrw _ hmem
      cases hro : roleAt W st with
      | none => rw [hro] at hsr; cases hsr
      | some role =>
        rw [hro] at hsr
        cases role with
        | spine fl =>
          cases fl with
          | array =>
            obtain ⟨u', hu', hsh⟩ := hok.2 st (.spine .array) hro
            rw [hu] at hu'; cases hu'
            obtain ⟨_, h, -⟩ := hsh.1
          | view _ _ => simp [SlotRole] at hsr
        | _ => simp [SlotRole] at hsr
    | _ => simp [Footprints.spineOf, Footprints.fieldsOf] at hsp
  exact ⟨hrp', by rw [hnv st u hu hne_view]; exact hspu⟩

open HeapKnowledge in
private theorem every_parallel_view_written {G : NormalGraph ι} {Γ : List (Ty ι)}
    {k : Knowledge} {b i x s : Nat} {p : List String} {start stop : IndexBound} {body : List BodyClause}
    {ρ : Env} {nw : Nat} {W : WorldT (nw + 1)} {h h' : Heap} {ek : CallEffects.ElementKind}
    (he : EnvOk G Γ ρ (nw + 1) W) (hk : Holds k ε ρ h) (hok : HeapOk (nw + 1) W h) (hρ : RootsOk W ρ)
    (hnv : ∀ (l : Nat) (u : Val), h[l]? = some u → (∀ f cs, u ≠ Tm.viewSpine f cs) → h'[l]? = some u)
    (hx : CallEffects.ExactWrite ek [ρ b, ρ i, ρ x] h h' ∧ CallEffects.ExactPre ek [ρ b, ρ i, ρ x])
    (hchk : everyParallelViewWritten G Γ k b i x { fact := .every s p start stop body } = true)
    (hF : (IndexFact.every s p start stop body).HoldsAt ε ρ h) :
    (IndexFact.every s p start stop body).HoldsAt ε ρ h' := by
  simp only [everyParallelViewWritten, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at hchk
  obtain ⟨⟨⟨hs_arr, -⟩, hbody_ok⟩, hcase⟩ := hchk
  obtain ⟨w, st_s, ls_s, m0, n, hw, hel_s, hls_s, hm0, hn, hall⟩ := hF
  obtain ⟨hw', hls_s'⟩ := arrayPath_spine_kept he hok hρ hnv hs_arr hw hel_s hls_s
  have hbound : ∀ (bd : IndexBound) (z : Int), bd.eval ε ρ h = some z → bd.eval ε ρ h' = some z := by
    intro bd z hb
    cases bd with
    | mk bs off =>
      cases bs with
      | none => exact hb
      | some t =>
        simp only [IndexBound.eval, Option.map_eq_some_iff] at hb ⊢
        obtain ⟨u, hu, rfl⟩ := hb
        exact ⟨u, nonView_termValue hok hρ hnv hu, rfl⟩
  obtain ⟨sto_b, cs_b, hel_b, hls_b⟩ := exactPre_view_spine hok hρ hx.2
  obtain ⟨ls_b', kb, i0, hls_b', hkb, hi0, hjb, lb, hlb, hlbv⟩ := hx.1.taken hx.2 sto_b (cs_b.map some) hel_b hls_b
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hkb hlbv
  have hki : intValue (ρ i) = some (i0 : Int) := by rw [hkb]; exact intValue_num hi0
  have hK : (knownOf k.indices).Holds (termValuation ε ρ h) := knownOf_holds hk.2.2.2.2.2
  have hcell_kept : ∀ {st0 l0 : Nat} {ls0 : List (Option Nat)} {u : Val},
      h[st0]?.bind spineEntries = some ls0 → some l0 ∈ ls0 → h[l0]? = some u → h'[l0]? = some u := by
    intro st0 l0 ls0 u hls0 hmem hu
    obtain ⟨hrole, -⟩ := hok.entries_cells hls0 hmem
    obtain ⟨u', hu', hsh⟩ := hok.2 l0 _ hrole
    rw [hu] at hu'; cases hu'
    exact hnv l0 u hu fun _ _ heq => by subst heq; simp [Shape, Cat, isSourceVal] at hsh
  have hiEval : (IndexBound.ofTerm (.value i)).eval ε ρ h = some (i0 : Int) := by
    simp [IndexBound.ofTerm, IndexBound.eval, termValue_value, hki]
  refine ⟨w, st_s, ls_s, m0, n, hw', hel_s, hls_s', hbound _ _ hm0, hbound _ _ hn, fun j hlo hj B hB => ?_⟩
  obtain ⟨htgts, hvars⟩ := hbody_ok B hB
  refine BodyClause.holdsAt_frame (fun t ht w0 hw0 => ?_) (fun y hy z hz => ?_) (hall j hlo hj B hB)
  · have htk := htgts t ht
    cases t with
    | self ep =>
      simp only [ElemTarget.read] at hw0 ⊢
      cases hl0 : ls_s[j]? with
      | none => simp [hl0] at hw0
      | some o =>
        cases o with
        | none => simp [hl0] at hw0
        | some l0 =>
          simp only [hl0] at hw0 ⊢
          obtain ⟨u, hu, hrg⟩ := Option.bind_eq_some_iff.mp hw0
          exact Option.bind_eq_some_iff.mpr ⟨u, hcell_kept hls_s (List.mem_of_getElem? hl0) hu,
            nonView_readGuard hok hnv (hok.refs_at hu) hrg⟩
    | parallel s' p' sh ep =>
      simp only [ElemTarget.read] at hw0 ⊢
      cases hsh : sh.eval ε ρ h j with
      | none => simp [hsh] at hw0
      | some jj =>
      simp only [hsh] at hw0
      rw [IndexShift.eval_frame (fun _ _ _ hz0 => nonView_termValue hok hρ hnv hz0) hsh]
      cases hrp : readPath h (ρ s') p' with
      | none => simp [hrp] at hw0
      | some a' =>
        simp only [hrp] at hw0
        cases hel' : elementsOf a' with
        | none => simp [hel'] at hw0
        | some st' =>
          simp only [hel'] at hw0
          cases hls' : h[st']?.bind spineEntries with
          | none => simp [hls'] at hw0
          | some ls' =>
            simp only [hls'] at hw0
            obtain ⟨hrp', hls''⟩ := arrayPath_spine_kept he hok hρ hnv htk hrp hel' hls'
            simp only [hrp', hel', hls'']
            cases hl0 : ls'[jj]? with
            | none => simp [hl0] at hw0
            | some o =>
              cases o with
              | none => simp [hl0] at hw0
              | some l0 =>
                simp only [hl0] at hw0 ⊢
                obtain ⟨u, hu, hrg⟩ := Option.bind_eq_some_iff.mp hw0
                exact Option.bind_eq_some_iff.mpr ⟨u, hcell_kept hls' (List.mem_of_getElem? hl0) hu,
                  nonView_readGuard hok hnv (hok.refs_at hu) hrg⟩
  · have hvk := hvars y hy
    cases y with
    | index => exact hz
    | elem =>
      simp only [boundValue, elementInt] at hz ⊢
      cases hl0 : ls_s[j]? with
      | none => simp [hl0] at hz
      | some o =>
        cases o with
        | none => simp [hl0] at hz
        | some l0 =>
          simp only [hl0] at hz ⊢
          obtain ⟨u, hu, hiu⟩ := Option.bind_eq_some_iff.mp hz
          exact Option.bind_eq_some_iff.mpr ⟨u, hcell_kept hls_s (List.mem_of_getElem? hl0) hu, hiu⟩
    | offset d =>
      simp only [boundValue, elementInt] at hz ⊢
      cases hl0 : ls_s[j + d]? with
      | none => simp [hl0] at hz
      | some o =>
        cases o with
        | none => simp [hl0] at hz
        | some l0 =>
          simp only [hl0] at hz ⊢
          obtain ⟨u, hu, hiu⟩ := Option.bind_eq_some_iff.mp hz
          exact Option.bind_eq_some_iff.mpr ⟨u, hcell_kept hls_s (List.mem_of_getElem? hl0) hu, hiu⟩
    | free t => exact nonView_termValue hok hρ hnv hz
    | project kd ep =>
      simp only [boundValue] at hz ⊢
      cases hl0 : ls_s[j]? with
      | none => simp [hl0] at hz
      | some o =>
        cases o with
        | none => simp [hl0] at hz
        | some l0 =>
          simp only [hl0] at hz ⊢
          obtain ⟨u, hu, htu⟩ := Option.bind_eq_some_iff.mp hz
          refine Option.bind_eq_some_iff.mpr ⟨u, hcell_kept hls_s (List.mem_of_getElem? hl0) hu, ?_⟩
          exact nonView_termValue hok (fun _ => hok.refs_at hu) hnv htu
    | parallel s' p' sh kd ep =>
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at hvk
      rcases hvk with hs'_arr | ⟨⟨⟨hsz, rfl⟩, hkd⟩, hreads⟩
      · simp only [boundValue] at hz ⊢
        cases hsh : sh.eval ε ρ h j with
        | none => simp [hsh] at hz
        | some jj =>
        simp only [hsh] at hz
        rw [IndexShift.eval_frame (fun _ _ _ hz0 => nonView_termValue hok hρ hnv hz0) hsh]
        cases hrp : readPath h (ρ s') p' with
        | none => simp [hrp] at hz
        | some a' =>
          simp only [hrp] at hz
          cases hel' : elementsOf a' with
          | none => simp [hel'] at hz
          | some st' =>
            simp only [hel'] at hz
            cases hls' : h[st']?.bind spineEntries with
            | none => simp [hls'] at hz
            | some ls' =>
              simp only [hls'] at hz
              obtain ⟨hrp', hls''⟩ := arrayPath_spine_kept he hok hρ hnv hs'_arr hrp hel' hls'
              simp only [hrp', hel', hls'']
              cases hl0 : ls'[jj]? with
              | none => simp [hl0] at hz
              | some o =>
                cases o with
                | none => simp [hl0] at hz
                | some l0 =>
                  simp only [hl0] at hz ⊢
                  obtain ⟨u, hu, htu⟩ := Option.bind_eq_some_iff.mp hz
                  refine Option.bind_eq_some_iff.mpr ⟨u, hcell_kept hls' (List.mem_of_getElem? hl0) hu, ?_⟩
                  exact nonView_termValue hok (fun _ => hok.refs_at hu) hnv htu
      · have hsh0 := IndexShift.eq_zero_of_isZero hsz
        subst hsh0
        simp only [boundValue, IndexShift.eval_zero] at hz ⊢
        cases hrp_b : readPath h (ρ s') p' with
        | none => simp [hrp_b] at hz
        | some wb =>
          have hwb : wb = ρ b := readsPath_eq hk.2.2.1 hreads hrp_b
          subst hwb
          have hrp_b' : readPath h' (ρ s') p' = some (ρ b) := nonView_readPath hok hnv (hρ s') hrp_b
          simp only [hrp_b, hrp_b', hel_b, hls_b, hls_b'] at hz ⊢
          by_cases hji : j = i0
          · subst hji
            rcases hcase with (hst_le | hst_ge) | hpar
            · have := IndexBound.leFact_sound hn hiEval (Linear.Known.entails_sound hK hst_le); omega
            · have := IndexBound.leFact_sound hiEval hm0 (Linear.Known.entails_sound hK hst_ge); omega
            · by_cases hsp_arr : HeapExpressionRules.arrayPathOf G Γ s' p' = true
              · obtain ⟨_, hls_b_kept⟩ := arrayPath_spine_kept he hok hρ hnv hsp_arr hrp_b hel_b hls_b
                rw [hls_b'] at hls_b_kept; cases hls_b_kept
                cases hl0 : (cs_b.map some)[j]? with
                | none => simp [hl0] at hz
                | some o =>
                  cases o with
                  | none => simp [hl0] at hz
                  | some l0 =>
                    simp only [hl0] at hz ⊢
                    obtain ⟨u, hu, htu⟩ := Option.bind_eq_some_iff.mp hz
                    exact Option.bind_eq_some_iff.mpr ⟨u, hcell_kept hls_b (List.mem_of_getElem? hl0) hu,
                      nonView_termValue hok (fun _ => hok.refs_at hu) hnv htu⟩
              · have hsp_f : HeapExpressionRules.arrayPathOf G Γ s' p' = false := Bool.eq_false_iff.mpr hsp_arr
                have hpar_all := hpar B hB (.parallel s' p' .zero kd []) hy
                simp only [hsp_f, Bool.not_false, hreads, and_self, ite_true] at hpar_all
                cases hpre : preWriteViewSlot (knownOf k.indices) k.links k.indices s' p' i with
                | none => rw [hpre] at hpar_all; cases hpar_all
                | some f =>
                  rw [hpre] at hpar_all
                  obtain ⟨hx_le_f, hf_le_x⟩ := Bool.and_eq_true_iff.mp hpar_all
                  have htf : termValue ε ρ h (Term.now kd f []) = some z := by
                    unfold preWriteViewSlot at hpre
                    cases hps : parallelSlot (knownOf k.indices) k.links k.indices s' p' i with
                    | some f0 =>
                      rw [hps] at hpre; cases hpre
                      have hpr := parallelSlot_read0 hK hk.2.2.1 hk.2.2.2.2.2 hki hps hrp_b hel_b hls_b
                      cases hl0 : (cs_b.map some)[j]? with
                      | none => simp [hl0] at hz
                      | some o =>
                        cases o with
                        | none => simp [hl0] at hz
                        | some l0 =>
                          simp only [hl0] at hz
                          obtain ⟨u, hu, htu⟩ := Option.bind_eq_some_iff.mp hz
                          have huf : u = ρ f := by
                            have := hpr.2.1 l0 hl0; rw [hu] at this; cases this; rfl
                          subst huf
                          simpa [termValue, termAt, readPath] using htu
                    | none =>
                      rw [hps] at hpre
                      cases hat : atIndexTermOrConst (knownOf k.indices) k.links k.indices s' p' i .value with
                      | none => rw [hat] at hpre; cases hpre
                      | some r0 =>
                        rw [hat] at hpre
                        cases r0 with
                        | inr _ => cases hpre
                        | inl t =>
                          simp only at hpre
                          split at hpre
                          · rename_i htv_cond
                            simp only [Option.some.injEq] at hpre; subst hpre
                            simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_iff] at htv_cond
                            obtain ⟨⟨hte, htk⟩, htp⟩ := htv_cond
                            have ht_eq : t = .value t.slot := by
                              cases t; simp only at hte htk htp; subst hte; subst htk; subst htp; rfl
                            obtain ⟨zv, hzv_t, hzv_b⟩ := atIndexTermOrConst_read hK hk.2.2.1 hk.2.2.2.2.2 hrp_b hel_b hls_b hki hat
                            rw [ht_eq, termValue_value] at hzv_t
                            cases hl0 : (cs_b.map some)[j]? with
                            | none => simp [hl0] at hz
                            | some o =>
                              cases o with
                              | none => simp [hl0] at hz
                              | some l0 =>
                                simp only [hl0] at hz
                                obtain ⟨u, hu, htu⟩ := Option.bind_eq_some_iff.mp hz
                                simp only [boundValue, hl0, hu, Option.bind_some, termValue, termAt,
                                  Bool.false_eq_true, ite_false, readPath, kindValue] at hzv_b
                                obtain ⟨bf, hbf, hsf⟩ : ∃ bf, ρ t.slot = .num bf ∧ SafeIntegers.SafeInt bf zv := by
                                  cases hρf : ρ t.slot <;> rw [hρf] at hzv_t <;> simp [intValue] at hzv_t
                                  exact ⟨_, rfl, SafeIntegers.safeIntOfBits_sound hzv_t⟩
                                obtain ⟨bu, hbu, hsu⟩ : ∃ bu, u = .num bu ∧ SafeIntegers.SafeInt bu zv := by
                                  cases u <;> simp [intValue] at hzv_b
                                  exact ⟨_, rfl, SafeIntegers.safeIntOfBits_sound hzv_b⟩
                                subst hbu
                                simp only [termValue, termAt, Bool.false_eq_true, ite_false, readPath, Option.bind_some] at htu ⊢
                                cases kd with
                                | value =>
                                  simp only [kindValue] at htu ⊢
                                  rw [hbf, intValue_num hsf]
                                  rw [intValue_num hsu] at htu; exact htu
                                | bitMask m =>
                                  simp only [isValidViewMask, decide_eq_true_eq] at hkd
                                  simp only [kindValue, bitMaskOf, hbf, hkd, ite_true] at htu ⊢
                                  rw [SafeIntegers.toInt32_safe hsf, ← SafeIntegers.toInt32_safe hsu]
                                  exact htu
                                | length | view | strLength => simp [isValidViewMask] at hkd
                          · cases hpre
                  obtain ⟨bx, ix, hbx, hsx, -⟩ := hx.2.1
                  simp only [List.getD_cons_succ, List.getD_cons_zero] at hbx
                  have htx_ex : ∃ zx, termValue ε ρ h (Term.now kd x []) = some zx := by
                    cases kd with
                    | value => exact ⟨ix, by simp [termValue, termAt, readPath, kindValue, hbx, intValue_num hsx]⟩
                    | bitMask m =>
                      simp only [isValidViewMask, decide_eq_true_eq] at hkd
                      exact ⟨intAnd (toInt32 bx) m,
                        by simp [termValue, termAt, readPath, kindValue, bitMaskOf, hbx, hkd]⟩
                    | length | view | strLength => simp [isValidViewMask] at hkd
                  obtain ⟨zx, hzx⟩ := htx_ex
                  have hzeq : zx = z := by
                    have h1 := Linear.Known.entails_sound hK hx_le_f
                    have h2 := Linear.Known.entails_sound hK hf_le_x
                    simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hzx, htf, Option.getD_some] at h1 h2
                    omega
                  subst hzeq
                  simp only [hlb, hlbv, Option.bind_some, termValue, termAt, Bool.false_eq_true, ite_false,
                    readPath, Option.bind_some]
                  simp only [termValue, termAt, Bool.false_eq_true, ite_false, readPath, Option.bind_some] at hzx
                  cases kd with
                  | value => simpa [kindValue, CallEffects.ElementKind.intValue_convert] using hzx
                  | bitMask m => simpa [kindValue, CallEffects.ElementKind.bitMaskOf_convert] using hzx
                  | length | view | strLength => simp [isValidViewMask] at hkd
          · cases hl0 : (cs_b.map some)[j]? with
            | none => simp [hl0] at hz
            | some o =>
              cases o with
              | none => simp [hl0] at hz
              | some l0 =>
                simp only [hl0] at hz
                obtain ⟨u, hu, htu⟩ := Option.bind_eq_some_iff.mp hz
                obtain ⟨l', hl', hu'⟩ := hjb j hji l0 u hl0 hu
                simp only [hl', hu', Option.bind_some, termValue, termAt, Bool.false_eq_true, ite_false,
                  readPath, Option.bind_some] at htu ⊢
                cases kd with
                | value | bitMask _ => exact htu
                | length | view | strLength => simp [isValidViewMask] at hkd

open HeapKnowledge in
theorem writeKept_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {eff : Effect} {t : Tm} {k : Knowledge}
    {ρ : Env} {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT (nw + 1)}
    (he : EnvOk G Γ ρ (nw + 1) W) (hk : Holds k ε ρ h) (hok : HeapOk (nw + 1) W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v) :
    IndexHolds ε (writeKept G Γ eff t k) (push v ρ) h' := by
  unfold writeKept
  split
  · rename_i f r b i x
    split
    rotate_left
    · exact indexHolds_nil _ _
    rename_i hse
    simp only [Bool.and_eq_true] at hse
    obtain ⟨ek, hw⟩ := Option.isSome_iff_exists.mp hse.2
    have hx := exactWriteOf_exact hw hq
    have hc : writeChanges.Holds h h' := statesViewGrowth_changes hse.1 hq
    have hnv : ∀ l (u : Val), h[l]? = some u → (∀ f cs, u ≠ Tm.viewSpine f cs) → h'[l]? = some u :=
      CallEffects.Effect.callPost_nonView_kept (List.contains_iff_mem.mp hse.1) hq
    simp only [ExpressionEffects.actualsOf, instantiate, instantiateArgs, Nat.not_lt_zero, ite_false,
      Nat.sub_zero] at hx
    have hi := pick_eq (fun a b hab => HeapLinks.aliases_eq hk.2.2.1 hab)
      (p := intSlot k.indices) i
    have hv := pick_eq (fun a b hab => HeapLinks.aliases_eq hk.2.2.1 hab)
      (p := intSlot k.indices) x
    have hx' : CallEffects.ExactWrite ek [ρ b,
        ρ (pick (HeapLinks.aliases k.links) (intSlot k.indices) i),
        ρ (pick (HeapLinks.aliases k.links) (intSlot k.indices) x)] h h' ∧ CallEffects.ExactPre ek [ρ b,
        ρ (pick (HeapLinks.aliases k.links) (intSlot k.indices) i),
        ρ (pick (HeapLinks.aliases k.links) (intSlot k.indices) x)] := by
      simpa only [hi, hv] using hx
    clear hx
    have hx := hx'
    refine shiftIndices_holds fun a ha hcd => ?_
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨ha, hkept⟩ := List.mem_filter.mp ha
          have hF := hk.2.2.2.2.2 a ha hcd
          unfold everyWritten at hkept
          split at hkept
          · rename_i s st0 st1 body hfa
            rw [hfa] at hF ⊢
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hkept
            obtain ⟨⟨⟨⟨⟨hcls, hst0⟩, hst1⟩, hb⟩, -⟩, hnew⟩ := hkept
            have hs : ρ s = ρ b := by
              rcases hcls with rfl | hm
              · rfl
              · exact HeapLinks.aliases_eq hk.2.2.1 hm
            exact every_written hk.2.2.2.2.2 hs hc hx hst0 hst1 hb hnew hF
          · cases hkept
        · obtain ⟨ha, hkept⟩ := List.mem_filter.mp ha
          have hF := hk.2.2.2.2.2 a ha hcd
          unfold everyParallelViewWritten at hkept
          split at hkept
          · rename_i s p st0 st1 body hfa
            rw [hfa] at hF ⊢
            exact every_parallel_view_written he hk hok hρ hnv hx (by simpa [everyParallelViewWritten] using hkept) hF
          · cases hkept
      · exact writeAtIndexAtoms_holds hk hok hρ hx a ha hcd
    · obtain ⟨a0, ha0, ha⟩ := List.mem_flatMap.mp ha
      have ha0 := (List.mem_filter.mp ha0).1
      obtain ⟨next, -, hnext⟩ := List.mem_filterMap.mp ha
      split at hnext <;> try contradiction
      unfold writtenPrefix at hnext
      split at hnext
      · rename_i s st0 st1 body hfact
        dsimp only at hnext
        split at hnext
        · rename_i hcheck
          cases hnext
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hcheck
          obtain ⟨⟨⟨⟨⟨⟨⟨hcls, hst0⟩, hd⟩, hst⟩, hb⟩, hcover⟩, hstart⟩, hbody⟩ := hcheck
          have hs : ρ s = ρ b := by
            rcases hcls with rfl | hm
            · rfl
            · exact HeapLinks.aliases_eq hk.2.2.1 hm
          have hF := hk.2.2.2.2.2 a0 ha0 hcd
          rw [hfact] at hF
          exact every_written_prefix hk.2.2.2.2.2 hs hc hx hst0 hd hcover hstart hst hb hbody hF
        · cases hnext
      · cases hnext
  · exact indexHolds_nil _ _

/-! ### Rule Call: a two-state postcondition in the caller's facts

A callee's post fact naming an entry term `old(t)` relates the caller's state
just before the call (the callee's entry, `Effect.callPost`) and the state after
it. The caller's facts after the call are composed (`HeapKnowledge.compose`)
from its facts before the call, at its own entry state, and that relation:
each callee entry term is the caller's term before the call at the slot
holding its position, each current term the caller's after it at the
return's slot (`ensuresSlot`). -/

/-- The caller's slot holding a call's position `p` at its entry: the
receiver's where it is a slot, each actual's (`callSlots`). -/
def entryPositionSlot (recv : Bool) (slots : List Nat) (p : Nat) : Option Nat :=
  if p < slots.length ∧ (p ≠ 0 ∨ recv = true) then some (PointClaims.slot (some slots) p) else none

open HeapKnowledge in
/-- A callee's post term as a variable of the call's step: an entry term
`old(⟨k, p, q⟩)` is the caller's term `⟨k, s, q⟩` before the call, `s` the
slot holding position `p`; a current term the caller's after it, at the
return's slot. -/
def callVar (recv : Bool) (slots : List Nat) (t : Term) : Option StepVar :=
  if t.atEntry then (entryPositionSlot recv slots t.slot).map fun s => .before (.now t.kind s t.path)
  else (ensuresSlot recv slots t.slot).map fun s => .after (.now t.kind s t.path)

/-- A call's actuals are its positions past the receiver. -/
theorem callSlots_length {t : Tm} {recv : Bool} {slots : List Nat} (hs : callSlots t = some (recv, slots)) (ρ : Env) :
    (ExpressionEffects.actualsOf (instantiate 0 ρ t)).length + 1 = slots.length := by
  cases t <;> simp only [callSlots, reduceCtorEq] at hs
  case construct f args =>
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hs
    obtain ⟨as, has, -, rfl⟩ := hs
    simp [ExpressionEffects.actualsOf, instantiate, instantiateArgs_eq_map, (varSlots_get has ρ).1]
  case invoke f r args =>
    have : ∃ as, varSlots args = some as ∧ slots.length = as.length + 1 := by
      cases r <;> simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hs <;>
        obtain ⟨as, has, -, rfl⟩ := hs <;> exact ⟨as, has, by simp⟩
    obtain ⟨as, has, hl⟩ := this
    simp [ExpressionEffects.actualsOf, instantiate, instantiateArgs_eq_map, hl, (varSlots_get has ρ).1]

open HeapKnowledge in
/-- A term whose slot holds `undefined` denotes no integer. -/
theorem termAt_undef {ρ : Env} {h : Heap} {t : Term} (hu : ρ t.slot = .undef) : termAt ρ h t = none := by
  obtain ⟨k, s, p, a⟩ := t
  simp only at hu
  cases p with
  | nil => cases k <;> simp [termAt, hu, readPath, kindValue, intValue, lengthOf, viewLengthOf, strLengthOf,
      bitMaskOf, Footprints.spineOf, Footprints.fieldsOf]
  | cons f q => simp [termAt, hu, readPath]

open HeapKnowledge in
/-- Whether a callee's post term reads a position its call passes nothing
at: an entry term's position, or a current term's past the result. -/
def absentAt (slots : List Nat) (t : Term) : Bool :=
  (t.atEntry || t.slot != 0) && decide (slots.length ≤ (if t.atEntry then t.slot else t.slot - 1))

/-- Whether a post's current slot is a position past the call's, which the
return gives `undefined`. -/
def absentSlot (slots : List Nat) (s : Nat) : Bool := s != 0 && decide (slots.length ≤ s - 1)

open HeapKnowledge in
/-- A post term reading a position the call passes nothing at denotes no
integer at the callee's entry and return (proved). -/
theorem absentAt_none {t : Tm} {recv : Bool} {slots : List Nat} (hs : callSlots t = some (recv, slots))
    {ρ : Env} {h h' : Heap} {v : Tm} {x : Term} (hxa : absentAt slots x = true) :
    termValue ⟨CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t)), h⟩ (CallEffects.ensuresEnv v
      (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h' x = none := by
  have hlen := callSlots_length hs ρ
  simp only [absentAt, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hxa
  obtain ⟨hne, hle⟩ := hxa
  cases he : x.atEntry
  · rw [termValue_now he, termAt_undef]
    have h0 : x.slot ≠ 0 := by rcases hne with h | h <;> simp_all
    simp only [he, Bool.false_eq_true, ite_false] at hle
    simp only [CallEffects.ensuresEnv, h0, ite_false, CallEffects.callEnv]
    rw [ite_eq_right (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  · rw [termValue_atEntry he, termAt_undef]
    simp only [he, ite_true] at hle
    simp only [CallEffects.callEnv]
    rw [ite_eq_right (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- A post's current slot past the call's positions holds `undefined` at the
return (proved). -/
theorem absentSlot_undef {t : Tm} {recv : Bool} {slots : List Nat} (hs : callSlots t = some (recv, slots))
    {ρ : Env} {v : Tm} {s : Nat} (ha : absentSlot slots s = true) :
    CallEffects.ensuresEnv v (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t)) s = .undef := by
  have hlen := callSlots_length hs ρ
  simp only [absentSlot, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at ha
  obtain ⟨h0, hle⟩ := ha
  simp only [CallEffects.ensuresEnv, h0, ite_false, CallEffects.callEnv]
  rw [ite_eq_right (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

open HeapKnowledge in
/-- **The relation a call's postcondition states** between the caller's
state before the call and after it: each linear post fact naming an entry
term, its terms read by `callVar`; each term it names defined, before the
call and after it (a post fact that holds defines its terms,
`IndexFact.defines_holds`). A fact
reading a position the call passes nothing at reads `undefined` there,
which denotes no integer: it never holds, and its relation is `0 ≤ -1`. -/
def callRelation (eff : Effect) (t : Tm) : StepRelation :=
  match callSlots t with
  | some (recv, slots) =>
    let facts := eff.schema.normal.facts.filterMap fun F => match F with
      | .linear G => if G.vars.any (·.atEntry) then
          if G.vars.any (absentAt slots) then some (.le [] (-1)) else G.mapVars (callVar recv slots)
        else none
      | _ => none
    { facts, defined := (facts.flatMap (·.vars)).filterMap (fun
        | .after u => some u
        | .before _ => none),
      definedBefore := (facts.flatMap (·.vars)).filterMap fun
        | .before u => some u
        | .after _ => none }
  | none => { facts := [] }

open HeapKnowledge in
theorem ensuresSlot_env {t : Tm} {recv : Bool} {slots : List Nat} (hs : callSlots t = some (recv, slots)) {ρ : Env}
    {v : Tm} {j s : Nat} (hj : ensuresSlot recv slots j = some s) :
    push v ρ s = CallEffects.ensuresEnv v (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t)) j := by
  cases j with
  | zero =>
    simp only [ensuresSlot, Option.some.injEq] at hj
    subst hj
    rfl
  | succ p =>
    simp only [ensuresSlot] at hj
    split at hj
    · rename_i hc
      simp only [Option.some.injEq] at hj
      subst hj
      have he := callSlots_env hs ρ p hc.1 hc.2
      simp only [PointClaims.mapEnv] at he
      simp only [push, CallEffects.ensuresEnv, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      exact he
    · cases hj

open HeapKnowledge in
/-- A post term's variable at a call denotes what the term denotes at the
callee's entry and return (proved): an entry term the caller's term before
the call at the slot holding its position, a current term the caller's after
it. -/
theorem callVar_val {t : Tm} {recv : Bool} {slots : List Nat} (hs : callSlots t = some (recv, slots))
    {ρ : Env} {h h' : Heap} {v : Tm} {x : Term} {y : StepVar} (hy : callVar recv slots x = some y) :
    StepVar.val ε ρ h (push v ρ) h' y =
      termValue ⟨CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t))
        (ExpressionEffects.actualsOf (instantiate 0 ρ t)), h⟩ (CallEffects.ensuresEnv v
        (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h' x := by
  unfold callVar at hy
  split at hy
  · rename_i he
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hy
    unfold entryPositionSlot at hs'
    split at hs'
    · rename_i hc
      cases hs'
      have henv := callSlots_env hs ρ x.slot hc.1 hc.2
      simp only [PointClaims.mapEnv] at henv
      simp only [StepVar.val, termValue, he, ite_true, Bool.false_eq_true, ite_false, termAt, henv]
    · cases hs'
  · rename_i he
    have he : x.atEntry = false := by simpa using he
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hy
    have henv := ensuresSlot_env (v := v) (ρ := ρ) hs hs'
    simp only [StepVar.val, termValue, he, Bool.false_eq_true, ite_false, termAt, henv]

open HeapKnowledge in
/-- **The relation a call's postcondition states holds of the call's step**
(proved): where its facts hold at the callee's entry `⟨callEnv r args, h⟩`
and return, the relation holds from `ρ, h` to `push v ρ, h'` at the caller's
entry state `ε`. -/
theorem callRelation_holds {eff : Effect} {t : Tm} {ρ : Env} {h h' : Heap} {v : Tm}
    (hp : ∀ F ∈ eff.schema.normal.facts, F.HoldsAt ⟨CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t)), h⟩ (CallEffects.ensuresEnv v (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h') :
    (callRelation eff t).Holds ε ρ h (push v ρ) h' := by
  unfold callRelation
  split
  · rename_i recv slots hs
    -- Each variable a post term maps to denotes what the term denotes at the callee's states.
    have hvar : ∀ (x : Term) (y : StepVar), callVar recv slots x = some y →
        StepVar.value ε ρ h (push v ρ) h' y =
          termValuation ⟨CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t))
            (ExpressionEffects.actualsOf (instantiate 0 ρ t)), h⟩ (CallEffects.ensuresEnv v
            (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h' x ∧
        (∀ u, y = .after u → termValue ε (push v ρ) h' u =
          termValue ⟨CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t))
            (ExpressionEffects.actualsOf (instantiate 0 ρ t)), h⟩ (CallEffects.ensuresEnv v
            (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h' x) := by
      intro x y hy
      unfold callVar at hy
      split at hy
      · rename_i he
        obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hy
        refine ⟨?_, fun u hu => by cases hu⟩
        unfold entryPositionSlot at hs'
        split at hs'
        · rename_i hc
          cases hs'
          have henv := callSlots_env hs ρ x.slot hc.1 hc.2
          simp only [PointClaims.mapEnv] at henv
          simp only [StepVar.value, termValuation, termValue, he, ite_true, Bool.false_eq_true, ite_false, termAt, henv]
        · cases hs'
      · rename_i he
        have he : x.atEntry = false := by simpa using he
        obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hy
        have henv := ensuresSlot_env (v := v) (ρ := ρ) hs hs'
        have heq : termValue ε (push v ρ) h' (.now x.kind s' x.path) =
            termValue ⟨CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t))
              (ExpressionEffects.actualsOf (instantiate 0 ρ t)), h⟩ (CallEffects.ensuresEnv v
              (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h' x := by
          simp only [termValue, he, Bool.false_eq_true, ite_false, termAt, henv]
        refine ⟨by simp only [StepVar.value, termValuation, heq], fun u hu => ?_⟩
        cases hu
        exact heq
    -- Each relation fact is a post fact's image.
    -- A post fact reading an absent position never holds.
    have habsent : ∀ G, IndexFact.linear G ∈ eff.schema.normal.facts → G.vars.any (absentAt slots) = true → False := by
      intro G hG ha
      obtain ⟨x, hx, hxa⟩ := List.any_eq_true.mp ha
      have hd := (hp _ hG).1 x hx
      rw [absentAt_none hs hxa] at hd
      cases hd
    -- Each relation fact is a post fact's image, or `0 ≤ -1` of one that never holds.
    have hfact : ∀ F ∈ eff.schema.normal.facts.filterMap (fun F => match F with
        | .linear G => if G.vars.any (·.atEntry) then
            if G.vars.any (absentAt slots) then some (.le [] (-1)) else G.mapVars (callVar recv slots)
          else none
        | _ => none), ∃ G, IndexFact.linear G ∈ eff.schema.normal.facts ∧
          (G.mapVars (callVar recv slots) = some F ∨ G.vars.any (absentAt slots) = true) := by
      intro F hF
      obtain ⟨F0, hF0, hm⟩ := List.mem_filterMap.mp hF
      split at hm
      · rename_i G
        split at hm
        · split at hm
          · rename_i ha; exact ⟨G, hF0, .inr ha⟩
          · exact ⟨G, hF0, .inl hm⟩
        · cases hm
      · cases hm
    refine ⟨fun F hF _ => ?_, fun _ u hu => ?_, fun u hu => ?_⟩
    · obtain ⟨G, hG, hm | ha⟩ := hfact F hF
      · exact (Linear.Fact.holds_mapVars hm fun x _ y hy => (hvar x y hy).1).mpr (hp _ hG).2
      · exact (habsent G hG ha).elim
    · obtain ⟨y, hy, hyu⟩ := List.mem_filterMap.mp hu
      obtain ⟨F, hF, hy⟩ := List.mem_flatMap.mp hy
      cases y with
      | before _ => cases hyu
      | after u' =>
        cases hyu
        obtain ⟨G, hG, hm | ha⟩ := hfact F hF
        · obtain ⟨x, hx, hxy⟩ := Linear.Fact.mapVars_vars hm _ hy
          rw [(hvar x _ hxy).2 _ rfl]
          exact (hp _ hG).1 x hx
        · exact (habsent G hG ha).elim
    · obtain ⟨y, hy, hyu⟩ := List.mem_filterMap.mp hu
      obtain ⟨F, hF, hy⟩ := List.mem_flatMap.mp hy
      cases y with
      | after _ => cases hyu
      | before u' =>
        cases hyu
        obtain ⟨G, hG, hm | ha⟩ := hfact F hF
        · obtain ⟨x, hx, hxy⟩ := Linear.Fact.mapVars_vars hm _ hy
          have hval := callVar_val (ε := ε) (ρ := ρ) (h := h) (h' := h') (v := v) hs hxy
          simp only [StepVar.val] at hval
          rw [hval]
          exact IndexFact.defines_holds (hp _ hG) x hx
        · exact (habsent G hG ha).elim
  · exact ⟨fun F hF => (by cases hF), fun _ u hu => (by cases hu), fun u hu => (by cases hu)⟩

open HeapKnowledge in
/-- **Whether a call keeps the value of a term of the caller**: its frame at
the caller's slots respects the term's support at `keep` under the query of
the call's entry (`Term.support`, `respects`, the note's Frame). -/
def callKeeps (stable : Nat → String → Bool) (eff : Effect) (t : Tm) (k : Knowledge) (u : Term) : Bool :=
  Footprints.respects (Footprints.knowledgeQuery k) (u.support (.ofFirst stable) .keep) (callerFrame eff t)

open HeapKnowledge in
/-- A term of the caller the call keeps, read after the return one slot
higher. -/
def callKept (stable : Nat → String → Bool) (eff : Effect) (t : Tm) (k : Knowledge) (u : Term) : Option Term :=
  if callKeeps stable eff t k u then some (u.mapM' (· + 1)) else none

open HeapKnowledge in
/-- A term of the caller the call grows: its frame respects the term's
support at `grow`; read after the return one slot higher. -/
def callGrown (stable : Nat → String → Bool) (eff : Effect) (t : Tm) (k : Knowledge) (u : Term) : Option Term :=
  if Footprints.respects (Footprints.knowledgeQuery k) (u.support (.ofFirst stable) .grow) (callerFrame eff t)
  then some (u.mapM' (· + 1)) else none

open HeapKnowledge in
theorem callKept_sound {stable : Nat → String → Bool} {eff : Effect} {t : Tm} {k : Knowledge} {ρ : Env} {h h' : Heap} {v : Tm}
    {nw : Nat} {W : WorldT nw} (hk : Holds k ε ρ h) (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v)
    (hst : FirstKept stable ρ h h') :
    ∀ u u' n, callKept stable eff t k u = some u' → termValue ε ρ h u = some n → termValue ε (push v ρ) h' u' = some n := by
  intro u u' n hu hn
  unfold callKept at hu
  split at hu
  · rename_i hc
    cases hu
    rw [termValue_mapM' fun _ => rfl]
    unfold callKeeps at hc
    exact Footprints.frame_step (D := Footprints.heaps) (m := 0)
      (Footprints.Term.supports_keep (ε := ε) (.ofFirst stable) u n) hc
      (Footprints.knowledgeQuery_sound hk hok hρ) (callerFrame_post (CallEffects.Effect.callPost_within hq)) trivial
      (Footprints.ReadContext.ofFirst_holds hst) hn
  · cases hu

open HeapKnowledge in
theorem callGrown_sound {stable : Nat → String → Bool} {eff : Effect} {t : Tm} {k : Knowledge} {ρ : Env} {h h' : Heap} {v : Tm}
    {nw : Nat} {W : WorldT nw} (hk : Holds k ε ρ h) (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v)
    (hst : FirstKept stable ρ h h') :
    ∀ u u' n, callGrown stable eff t k u = some u' → termValue ε ρ h u = some n →
      ∃ n', termValue ε (push v ρ) h' u' = some n' ∧ n ≤ n' := by
  intro u u' n hu hn
  unfold callGrown at hu
  split at hu
  · rename_i hc
    cases hu
    rw [termValue_mapM' fun _ => rfl]
    exact Footprints.frame_step (D := Footprints.heaps) (m := 0)
      (Footprints.Term.supports_grow (ε := ε) (.ofFirst stable) u n) hc
      (Footprints.knowledgeQuery_sound hk hok hρ) (callerFrame_post (CallEffects.Effect.callPost_within hq)) trivial
      (Footprints.ReadContext.ofFirst_holds hst) ⟨n, hn, Int.le_refl n⟩
  · cases hu

open HeapKnowledge in
/-- **The relational context of a call's composition**: the relation its
callee's two-state postcondition states (`callRelation`) and the one its
change states of each term of the caller's facts it grows (`growth`); the
terms it keeps are read after it by `callKept`. -/
def callContext (stable : Nat → String → Bool) (eff : Effect) (t : Tm) (k0 : Knowledge) : StepRelation :=
  (callRelation eff t).join (growth (callGrown stable eff t k0) (IndexWrites.unconditionalLinear k0.indices))

open HeapKnowledge in
theorem callContext_holds {stable : Nat → String → Bool} {eff : Effect} {t : Tm} {k0 : Knowledge} {ρ : Env}
    {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT nw} (hk0 : Holds k0 ε ρ h) (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v)
    (hstable : FirstKept stable ρ h h') :
    (callContext stable eff t k0).Holds ε ρ h (push v ρ) h' :=
  StepRelation.join_holds (callRelation_holds fun _ hF => CallEffects.Effect.callPost_ensures hF hq) (growth_holds (callGrown_sound hk0 hok hρ hq hstable))

open HeapKnowledge in
/-- **Rule Entry's premises at a call** stating a two-state postcondition:
`old(Σ)` the entry's unconditional linear facts, the terms its frame keeps
(`callKept`, the note's Frame), and the relation of its postcondition and
of the terms its frame grows (`callContext`). -/
def callEntry (stable : Nat → String → Bool) (eff : Effect) (t : Tm) (k0 : Knowledge) : Entry :=
  ⟨callKept stable eff t k0, IndexWrites.unconditionalLinear k0.indices, callContext stable eff t k0⟩

open HeapKnowledge in
/-- Rule Entry's premises hold at a call (proved): the entry's facts hold
before it, its frame bounds it, and its normal exit's postconditions hold. -/
theorem callEntry_holds {stable : Nat → String → Bool} {eff : Effect} {t : Tm} {k0 : Knowledge} {ρ : Env}
    {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT nw} (hk0 : Holds k0 ε ρ h) (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v)
    (hstable : FirstKept stable ρ h h') :
    (callEntry stable eff t k0).Holds ε ρ h (push v ρ) h' :=
  ⟨IndexWrites.unconditionalLinear_holds hk0.2.2.2.2.2, callKept_sound hk0 hok hρ hq hstable,
    callContext_holds hk0 hok hρ hq hstable⟩

open HeapKnowledge in
/-- **Rule Entry's consequences in the caller** at a call stating a
two-state postcondition (`callEntry`): its linear consequences
(`Entry.consequences`), and each other post fact composed with the same
premises form by form (`Composer.fact`), each position the call passes
nothing at read as `undefined`: every post fact but a linear one naming an
entry term (`callRelation`'s) and one naming none whose every slot the
return holds (`ensuresAtoms`'). -/
def ensuresComposed (stable : Nat → String → Bool) (eff : Effect) (t : Tm) (k0 : Knowledge) : List IndexAtom :=
  (if (callRelation eff t).facts.isEmpty then [] else
  (callEntry stable eff t k0).consequences.map fun F => { fact := .linear F }) ++
  match callSlots t with
  | some (recv, slots) =>
    let matching := eff.schema.normal.facts.filter fun F => match F with
      | .linear G => !G.vars.any (·.atEntry) && (F.mapM (ensuresSlot recv slots)).isNone
      | _ => !F.entrySlots.isEmpty || (F.mapM (ensuresSlot recv slots)).isNone
    if matching.isEmpty then [] else
    let P : Composer := ⟨callEntry stable eff t k0, callVar recv slots, ensuresSlot recv slots, absentAt slots,
      absentSlot slots⟩
    (matching.flatMap P.fact).map fun F => { fact := F }
  | none => []

open HeapKnowledge in
theorem ensuresComposed_holds {stable : Nat → String → Bool} {eff : Effect} {t : Tm} {k0 : Knowledge} {ρ : Env}
    {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT nw} (hk0 : Holds k0 ε ρ h) (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v)
    (hstable : FirstKept stable ρ h h') :
    IndexHolds ε (ensuresComposed stable eff t k0) (push v ρ) h' := by
  have hE := callEntry_holds hk0 hok hρ hq hstable
  intro a ha _
  unfold ensuresComposed at ha
  rcases List.mem_append.mp ha with ha | ha
  · split at ha
    · cases ha
    · obtain ⟨F, hF, rfl⟩ := List.mem_map.mp ha
      exact entry_sound hE F hF
  · split at ha
    · rename_i recv slots hs
      dsimp only at ha
      split at ha
      · cases ha
      · obtain ⟨G, hG, rfl⟩ := List.mem_map.mp ha
        obtain ⟨F, hF, hGF⟩ := List.mem_flatMap.mp hG
        have hsound : Composer.Sound ⟨callEntry stable eff t k0, callVar recv slots, ensuresSlot recv slots,
            absentAt slots, absentSlot slots⟩ ε
            ⟨CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)), h⟩
            ρ h (push v ρ) (CallEffects.ensuresEnv v (ExpressionEffects.receiverOf (instantiate 0 ρ t))
              (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h' :=
          ⟨hE, fun _ _ hx => callVar_val hs hx, fun _ _ hx => ensuresSlot_env hs hx,
            fun _ hx => absentAt_none hs hx, fun _ hx => absentSlot_undef hs hx⟩
        exact Composer.fact_holds hsound (CallEffects.Effect.callPost_ensures (List.mem_filter.mp hF).1 hq) G hGF
    · cases ha

/-- The alias links a call's return-alias postconditions (`IndexFact.same 0 (p + 1)`
or `.same (p + 1) 0` in `eff.schema.normal.facts`) give: when a normal exit
states `result = callPos p` and position `p` is a slot `a`, slot `0` (the
result) aliases slot `a + 1`. -/
def sameLinks (eff : Effect) (t : Tm) : HeapLinks.Links :=
  match t with
  | .invoke _ r args =>
    eff.schema.normal.facts.filterMap fun F =>
      let pos? : Option Nat := match F with
        | .same 0 (p + 1) | .same (p + 1) 0 => some p
        | _ => none
      pos?.bind fun p =>
        let slot? : Option Nat := match p with
          | 0 => match r with | .var a => some a | _ => none
          | k + 1 => match args[k]? with | some (.var a) => some a | _ => none
        slot?.map fun a => ⟨0, a + 1, true, .str "", false⟩
  | _ => []

private theorem sameLinks_holds {eff : Effect} {t : Tm} {ρ : Env} {h h' : Heap} {v : Tm}
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v) :
    HeapLinks.Holds (sameLinks eff t) (push v ρ) h' := by
  intro g hg
  cases t with
  | invoke f r args =>
    simp only [sameLinks] at hg
    obtain ⟨F, hF, hFm⟩ := List.mem_filterMap.mp hg
    have hFholds : F.HoldsAt ⟨CallEffects.callEnv (instantiate 0 ρ r) (args.map (instantiate 0 ρ)), h⟩
        (CallEffects.ensuresEnv v (instantiate 0 ρ r) (args.map (instantiate 0 ρ))) h' := by
      have hinst : ExpressionEffects.receiverOf (instantiate 0 ρ (.invoke f r args)) = instantiate 0 ρ r ∧
          ExpressionEffects.actualsOf (instantiate 0 ρ (.invoke f r args)) = args.map (instantiate 0 ρ) := by
        simp [ExpressionEffects.receiverOf, ExpressionEffects.actualsOf, instantiate, instantiateArgs_eq_map]
      have := CallEffects.Effect.callPost_ensures hF hq
      rwa [hinst.1, hinst.2] at this
    have go : ∀ p, v = CallEffects.callEnv (instantiate 0 ρ r) (args.map (instantiate 0 ρ)) p →
        ((match p with
          | 0 => match r with | .var a => some a | _ => none
          | k + 1 => match args[k]? with | some (.var a) => some a | _ => none).map
          fun a => (⟨0, a + 1, true, .str "", false⟩ : HeapLinks.Link)) = some g →
        HeapLinks.Holds [g] (push v ρ) h' := by
      intro p hv hm
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hm
      have hpa : CallEffects.callEnv (instantiate 0 ρ r) (args.map (instantiate 0 ρ)) p = ρ a := by
        cases p with
        | zero =>
          cases r <;> simp at ha
          subst ha; rfl
        | succ k =>
          dsimp only at ha
          cases hak : args[k]? with
          | none => simp [hak] at ha
          | some tk =>
            rw [hak] at ha
            cases tk <;> simp at ha
            subst ha
            simp [CallEffects.callEnv, List.getD_eq_getElem?_getD, hak, instantiate]
      intro g' hg'
      simp only [List.mem_singleton] at hg'
      subst hg'
      simpa [push, hpa] using hv
    cases F with
    | same x y =>
      cases x with
      | zero =>
        cases y with
        | zero => simp at hFm
        | succ p =>
          simp only [HeapKnowledge.IndexFact.HoldsAt, CallEffects.ensuresEnv] at hFholds
          exact go p hFholds hFm g (List.mem_singleton_self g)
      | succ p =>
        cases y with
        | zero =>
          simp only [HeapKnowledge.IndexFact.HoldsAt, CallEffects.ensuresEnv] at hFholds
          exact go p hFholds.symm hFm g (List.mem_singleton_self g)
        | succ _ => simp at hFm
    | _ => simp at hFm
  | _ => simp [sameLinks] at hg

/-- Spine separations a call stating a fresh array result (`ExitSchema.freshResult`)
establishes: its result's spine lies at or past the pre-call heap's end, so it
differs from the spine of every bare array slot in `Γ`, and from the spine of
every existing field-rooted path `(s, p)` in `IndexWrites.indexPaths` whose path
read is respected by the call's frame. -/
def freshCallSpineApart (stable : Nat → String → Bool) (G : NormalGraph ι) (Γ : List (Ty ι))
    (eff : Effect) (t : Tm) (k0 : HeapKnowledge.Knowledge) : List HeapKnowledge.IndexAtom :=
  if !eff.schema.normal.freshResult then [] else
  let q := Footprints.knowledgeQuery k0
  let F := callerFrame eff t
  let fieldPaths := (IndexWrites.indexPaths Γ.length k0).filterMap fun (s, p) =>
    if p.isEmpty || Footprints.respects q (Footprints.pathReads (.ofFirst stable) s .keep [] p) F then
      some { fact := .spineApart 0 [] (s + 1) p }
    else none
  let bareArrays := ((List.range Γ.length).filter (IndexWrites.arraySlot G Γ)).map fun s =>
    { fact := .spineApart 0 [] (s + 1) [] }
  let elemPaths := (IndexWrites.indexPaths Γ.length k0).filterMap fun (s, p) =>
    if (p.isEmpty || Footprints.respects q (Footprints.pathReads (.ofFirst stable) s .keep [] p) F) &&
        Footprints.respects q [(.spine s p, .keep), (.pathCells s p, .keep)] F then
      some { fact := .elemSpineApart 0 [] (s + 1) p }
    else none
  let bareElemArrays := ((List.range Γ.length).filter (IndexWrites.arraySlot G Γ)).filterMap fun s =>
    if Footprints.respects q [(.spine s [], .keep), (.pathCells s [], .keep)] F then
      some { fact := .elemSpineApart 0 [] (s + 1) [] }
    else none
  fieldPaths ++ bareArrays ++ elemPaths ++ bareElemArrays

omit [DecidableEq ι] in
private theorem freshCallSpineApart_holds {stable : Nat → String → Bool} {G : NormalGraph ι} {Γ : List (Ty ι)}
    {eff : Effect} {t : Tm} {k0 : HeapKnowledge.Knowledge} {ρ : Env} {h h' : Heap} {v : Tm}
    {nw : Nat} {W : WorldT nw} (hk0 : HeapKnowledge.Holds k0 ε ρ h)
    (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v)
    (hstable : HeapKnowledge.FirstKept stable ρ h h') :
    HeapKnowledge.IndexHolds ε (freshCallSpineApart stable G Γ eff t k0) (push v ρ) h' := by
  unfold freshCallSpineApart
  split
  · exact HeapKnowledge.indexHolds_nil _ _
  · rename_i hfr
    have hfr' : eff.schema.normal.freshResult = true := by simpa using hfr
    obtain ⟨lu, hlu, hge⟩ := CallEffects.Effect.callPost_fresh hfr' hq
    have hqSound := Footprints.knowledgeQuery_sound hk0 hok hρ
    have hpost := callerFrame_post (CallEffects.Effect.callPost_within hq)
    have helemApart : ∀ {s : Nat} {p : List String} {w : Val},
        HeapKnowledge.readPath h (ρ s) p = some w → HeapKnowledge.readPath h' (ρ s) p = some w →
        RefsOk W w →
        Footprints.Supported [(.spine s p, .keep), (.pathCells s p, .keep)] ρ h h' →
        HeapKnowledge.PathElemSpinesApart h' v [] (ρ s) p := by
      intro s p w hw hw' hrb hsup
      refine ⟨v, w, rfl, hw', fun st hel => ?_⟩
      obtain ⟨_, ls, hls, hcs⟩ := IndexWrites.refsOk_elements_elem_lt hok hrb hel
      obtain ⟨u0, hu0, hue⟩ := Option.bind_eq_some_iff.mp hls
      have hspMem : (Footprints.Region.spine s p).mem ρ h st = true := by
        simp [Footprints.Region.mem, hw, hel]
      obtain ⟨u', hu', hku⟩ := hsup (.spine s p, .keep) (by simp) st u0 hspMem hu0
      simp only [Footprints.Change.Holds] at hku; subst hku
      refine ⟨ls, by rw [hu']; exact hue, fun c hc => ?_⟩
      obtain ⟨e, _, he, heRef⟩ := hcs c hc
      have hcMem : (Footprints.Region.pathCells s p).mem ρ h c = true := by
        have ho : some c ∈ Footprints.entriesAt h (some st) := by simp [Footprints.entriesAt, hls, hc]
        simpa [Footprints.Region.mem, hw, List.contains_iff_mem] using Footprints.elementsOf_entries_sub hel ho
      obtain ⟨e', he', hke⟩ := hsup (.pathCells s p, .keep) (by simp) c e hcMem he
      simp only [Footprints.Change.Holds] at hke; subst hke
      refine ⟨e', he', fun s1 se hs1 hse => ?_⟩
      rw [hlu] at hs1; cases hs1
      have hlt := IndexWrites.refsOk_spineOf_lt hok heRef hse
      omega
    intro a ha _
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨⟨s, p⟩, hmem, hm⟩ := List.mem_filterMap.mp ha
          dsimp only at hm
          split at hm
          · rename_i hcond
            simp only [Option.some.injEq] at hm
            subst hm
            obtain ⟨w, hw⟩ := IndexWrites.indexPaths_defined hmem hk0
            have hw' : HeapKnowledge.readPath h' (ρ s) p = some w := by
              rcases Bool.or_eq_true_iff.mp hcond with hp | hr
              · have hp' : p = [] := List.isEmpty_iff.mp hp
                subst hp'
                simpa [HeapKnowledge.readPath] using hw
              · have hsup := Footprints.respect_sound hr hqSound hpost
                exact Footprints.pathReads_sound (Footprints.ReadContext.ofFirst_holds hstable) p []
                  hsup (Footprints.keeps_keep w) rfl rfl hw
            refine ⟨v, w, rfl, hw', fun s1 s2 hs1 hs2 => ?_⟩
            rw [hlu] at hs1; cases hs1
            have hrb := IndexWrites.refsOk_readPath_extend hok [] (hρ s) (by simpa using hw)
            have hlt := IndexWrites.refsOk_spineOf_lt hok hrb hs2
            omega
          · cases hm
        · obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha
          refine ⟨v, ρ s, rfl, rfl, fun s1 s2 hs1 hs2 => ?_⟩
          rw [hlu] at hs1; cases hs1
          have hlt := IndexWrites.refsOk_spineOf_lt hok (hρ s) hs2
          omega
      · obtain ⟨⟨s, p⟩, hmem, hm⟩ := List.mem_filterMap.mp ha
        dsimp only at hm
        split at hm
        · rename_i hcond
          simp only [Option.some.injEq] at hm; subst hm
          simp only [Bool.and_eq_true] at hcond
          obtain ⟨hpath, hsc⟩ := hcond
          obtain ⟨w, hw⟩ := IndexWrites.indexPaths_defined hmem hk0
          have hw' : HeapKnowledge.readPath h' (ρ s) p = some w := by
            rcases Bool.or_eq_true_iff.mp hpath with hp | hr
            · have hp' : p = [] := List.isEmpty_iff.mp hp
              subst hp'; simpa [HeapKnowledge.readPath] using hw
            · have hsup := Footprints.respect_sound hr hqSound hpost
              exact Footprints.pathReads_sound (Footprints.ReadContext.ofFirst_holds hstable) p []
                hsup (Footprints.keeps_keep w) rfl rfl hw
          have hrb := IndexWrites.refsOk_readPath_extend hok [] (hρ s) (by simpa using hw)
          exact helemApart hw hw' hrb (Footprints.respect_sound hsc hqSound hpost)
        · cases hm
    · obtain ⟨s, -, hm⟩ := List.mem_filterMap.mp ha
      split at hm
      · rename_i hsc
        simp only [Option.some.injEq] at hm; subst hm
        exact helemApart (p := []) rfl rfl (hρ s) (Footprints.respect_sound hsc hqSound hpost)
      · cases hm

/-- Region separations a call stating a fresh array region
(`ExitSchema.freshRegionResult`) establishes: its result's spine and every
present element cell lie at or past the pre-call heap's end, so its region is
apart from every bare array slot in `Γ` and every existing field-rooted path
`(s, p)` in `IndexWrites.indexPaths` whose path read and spine are respected by
the call's frame. -/
def freshCallApart (stable : Nat → String → Bool) (G : NormalGraph ι) (Γ : List (Ty ι))
    (eff : Effect) (t : Tm) (k0 : HeapKnowledge.Knowledge) : List HeapKnowledge.IndexAtom :=
  if !eff.schema.normal.freshRegionResult then [] else
  let q := Footprints.knowledgeQuery k0
  let F := callerFrame eff t
  let fieldPaths := (IndexWrites.indexPaths Γ.length k0).filterMap fun (s, p) =>
    if HeapKnowledge.termDefined k0.indices (.now .length s p) &&
        (p.isEmpty || Footprints.respects q (Footprints.pathReads (.ofFirst stable) s .keep [] p) F) &&
        Footprints.respects q [(.path s p arraySpineKey, .keep)] F then
      some { fact := .apart 0 [] (s + 1) p }
    else none
  let bareArrays := ((List.range Γ.length).filter (IndexWrites.arraySlot G Γ)).filterMap fun s =>
    if Footprints.respects q [(.field s arraySpineKey, .keep)] F then
      some { fact := .apart 0 [] (s + 1) [] }
    else none
  fieldPaths ++ bareArrays

omit [DecidableEq ι] in
private theorem freshCallApart_holds {stable : Nat → String → Bool} {G : NormalGraph ι} {Γ : List (Ty ι)}
    {eff : Effect} {t : Tm} {k0 : HeapKnowledge.Knowledge} {ρ : Env} {h h' : Heap} {v : Tm}
    {nw : Nat} {W : WorldT (nw + 4)} (he : EnvOk G Γ ρ (nw + 4) W) (hk0 : HeapKnowledge.Holds k0 ε ρ h)
    (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v)
    (hstable : HeapKnowledge.FirstKept stable ρ h h') :
    HeapKnowledge.IndexHolds ε (freshCallApart stable G Γ eff t k0) (push v ρ) h' := by
  unfold freshCallApart
  split
  · exact HeapKnowledge.indexHolds_nil _ _
  · rename_i hfr
    have hfr' : eff.schema.normal.freshRegionResult = true := by simpa using hfr
    obtain ⟨lu, lsu, hlu, hge, hlsu, hcells⟩ := CallEffects.Effect.callPost_freshRegion hfr' hq
    have hvReg : HeapKnowledge.RegionOf h' v (some lu) lsu := .inr ⟨lu, rfl, hlu, hlsu⟩
    have hvAbove : ∀ l, HeapKnowledge.InRegion (some lu) lsu l → h.length ≤ l := by
      intro l hl
      rcases hl with hl | hl
      · cases hl; exact hge
      · exact hcells l hl
    have hqSound := Footprints.knowledgeQuery_sound hk0 hok hρ
    have hpost := callerFrame_post (CallEffects.Effect.callPost_within hq)
    have hapartOf : ∀ {s : Nat} {p : List String} {w : Val} {st : Nat},
        HeapKnowledge.readPath h (ρ s) p = some w → RefsOk W w → Footprints.spineOf w = some st →
        Footprints.Supported [(.path s p arraySpineKey, .keep)] ρ h h' →
        HeapKnowledge.RegionsApart h' v w := by
      intro s p w st hw hrb hsp hsup
      obtain ⟨_, hstLt, ls, hls, hc⟩ := IndexWrites.refsOk_spine_region hok hrb hsp
      have hmem : (Footprints.Region.path s p arraySpineKey).mem ρ h st = true := by
        simp only [Footprints.Region.mem, hw]
        simpa using Footprints.spineOf_lookup hsp
      obtain ⟨u', hu', hke⟩ := hsup _ (List.mem_singleton_self _) st _ hmem hls
      simp only [Footprints.Change.Holds] at hke; subst hke
      refine ⟨some lu, lsu, some st, ls, hvReg, .inr ⟨st, rfl, hsp, hu'⟩, fun l hl m hm => ?_⟩
      have hlge := hvAbove l hl
      rcases hm with hm | hm
      · cases hm; omega
      · have := (hc m hm).2; omega
    intro a ha _
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨⟨s, p⟩, hmem, hm⟩ := List.mem_filterMap.mp ha
      dsimp only at hm
      split at hm
      · rename_i hcond
        simp only [Option.some.injEq] at hm; subst hm
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨hdef, hpath⟩, hspResp⟩ := hcond
        obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (HeapKnowledge.termDefined_sound hk0.2.2.2.2.2 hdef)
        simp only [HeapKnowledge.termValue, HeapKnowledge.termAt, Bool.false_eq_true, ite_false,
          Option.bind_eq_some_iff] at hz
        obtain ⟨w, hw, hlenW⟩ := hz
        obtain ⟨st, _, hsp, -, -, -⟩ := HeapKnowledge.lengthOf_spine hlenW
        have hw' : HeapKnowledge.readPath h' (ρ s) p = some w := by
          rcases Bool.or_eq_true_iff.mp hpath with hp | hr
          · have hp' : p = [] := List.isEmpty_iff.mp hp
            subst hp'; simpa [HeapKnowledge.readPath] using hw
          · have hsup := Footprints.respect_sound hr hqSound hpost
            exact Footprints.pathReads_sound (Footprints.ReadContext.ofFirst_holds hstable) p []
              hsup (Footprints.keeps_keep w) rfl rfl hw
        have hrb := IndexWrites.refsOk_readPath_extend hok [] (hρ s) (by simpa using hw)
        have hsup := Footprints.respect_sound hspResp hqSound hpost
        exact ⟨v, w, rfl, hw', hapartOf hw hrb hsp hsup⟩
      · cases hm
    · obtain ⟨s, hs, hm⟩ := List.mem_filterMap.mp ha
      split at hm
      · rename_i hresp
        simp only [Option.some.injEq] at hm; subst hm
        have hArr : IndexWrites.arraySlot G Γ s = true := (List.mem_filter.mp hs).2
        obtain ⟨st, _, hsp, -, -, -⟩ := IndexWrites.arraySlot_region hArr he hok
        have hsup : Footprints.Supported [(.path s [] arraySpineKey, .keep)] ρ h h' := by
          have h0 := Footprints.respect_sound hresp hqSound hpost
          intro e he' l u hmem hu
          simp only [List.mem_singleton] at he'; subst he'
          exact h0 (.field s arraySpineKey, .keep) (List.mem_singleton_self _) l u
            (by simpa [Footprints.Region.mem, HeapKnowledge.readPath] using hmem) hu
        exact ⟨v, ρ s, rfl, rfl, hapartOf (p := []) rfl (hρ s) hsp hsup⟩
      · cases hm

/-- Element witnesses for each slot argument appended by `i.push(x_0, ..., x_{k-1})`:
`i[i.length - (k - m)] === x_m` in the post-call environment (slots shifted by 1). -/
def pushElemAt (i total : Nat) : Nat → List Tm → List HeapKnowledge.IndexAtom
  | _, [] => []
  | m, .var x :: rest =>
    { fact := .element (x + 1) (i + 1) ⟨[(.length (i + 1), 1)], -((total - m : Nat) : Int)⟩ } ::
      pushElemAt i total (m + 1) rest
  | m, _ :: rest => pushElemAt i total (m + 1) rest

@[nospecialize] def pushElemAtoms (G : NormalGraph ι) (Γ : List (Ty ι)) (eff : Effect) (t : Tm)
    (k0 : HeapKnowledge.Knowledge) : List HeapKnowledge.IndexAtom :=
  if statesExtension eff && statesAppend eff then
    match t with
    | .invoke _ (.var i) args =>
      if IndexWrites.appendSlots Γ.length args && !args.isEmpty &&
          (IndexWrites.arraySlot G Γ i || HeapKnowledge.termDefined k0.indices (.length i)) then
        pushElemAt i args.length 0 args
      else []
    | _ => []
  else []

open HeapKnowledge in
private theorem pushElemAt_mem {i total : Nat} :
    ∀ {m : Nat} {xs : List Tm} {a : IndexAtom},
      a ∈ pushElemAt i total m xs →
      ∃ j x, xs[j]? = some (.var x) ∧
        a = { fact := .element (x + 1) (i + 1) ⟨[(.length (i + 1), 1)], -((total - (m + j) : Nat) : Int)⟩ } := by
  intro m xs
  induction xs generalizing m with
  | nil => intro a hm; cases hm
  | cons t rest ih =>
    intro a hm
    cases t with
    | var x =>
      simp only [pushElemAt, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨0, x, rfl, by simp⟩
      · obtain ⟨j, x', hget, rfl⟩ := ih hm
        refine ⟨j + 1, x', hget, ?_⟩
        have heq : m + 1 + j = m + (j + 1) := by omega
        rw [heq]
    | _ =>
      simp only [pushElemAt] at hm
      obtain ⟨j, x', hget, rfl⟩ := ih hm
      refine ⟨j + 1, x', hget, ?_⟩
      have heq : m + 1 + j = m + (j + 1) := by omega
      rw [heq]

open HeapKnowledge in
omit [DecidableEq ι] in
private theorem pushElemAtoms_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {eff : Effect} {t : Tm}
    {k0 : Knowledge} {ρ : Env} {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT (nw + 4)}
    (hv : ∀ i, i < Γ.length → isVal (ρ i) = true)
    (he : EnvOk G Γ ρ (nw + 4) W) (hk0 : Holds k0 ε ρ h) (hok : HeapOk (nw + 4) W h)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v) :
    IndexHolds ε (pushElemAtoms G Γ eff t k0) (push v ρ) h' := by
  unfold pushElemAtoms
  split
  · rename_i hgr
    simp only [Bool.and_eq_true] at hgr
    have hgrow := statesExtension_grows hgr.1 hq
    have happ := statesAppend_appends hgr.2 hq
    cases t with
    | invoke f recv args =>
      cases recv with
      | var i =>
        dsimp only
        split
        · rename_i hcond
          simp only [Bool.and_eq_true, Bool.or_eq_true] at hcond
          obtain ⟨⟨hslots, -⟩, hlenDef⟩ := hcond
          simp only [ExpressionEffects.receiverOf, ExpressionEffects.actualsOf, instantiate,
            Nat.not_lt_zero, ite_false, Nat.sub_zero] at hgrow happ
          have hlen_args : (instantiateArgs 0 ρ args).length = args.length := by simp
          have hargs_vals : ∀ u ∈ instantiateArgs 0 ρ args, isVal u = true :=
            IndexWrites.appendSlots_values hv hslots
          have ⟨n0, hn0⟩ : ∃ n0 : Nat, termValue ε ρ h (.length i) = some (n0 : Int) := by
            rcases hlenDef with harr | htd
            · exact arraySlot_length harr he hok
            · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (termDefined_sound hk0.2.2.2.2.2 htd)
              obtain ⟨_, ls, _, _, rfl, _⟩ := lengthOf_spine (by simpa only [termValue_length] using hm)
              exact ⟨ls.length, hm⟩
          obtain ⟨st, ls, hsp, hls, hlenEq, _⟩ := lengthOf_spine (by simpa only [termValue_length] using hn0)
          obtain ⟨ls', hls', hlen', hel'⟩ := happ hargs_vals st ls hsp hls
          have hlen_after : termValue ε ρ h' (.length i) = some ((ls.length + args.length : Nat) : Int) := by
            have ha := appended_length (ε := ε) hgrow happ hargs_vals hn0
            rw [hlen_args] at ha
            have : (n0 : Int) + (args.length : Int) = ((ls.length + args.length : Nat) : Int) := by omega
            rwa [this] at ha
          intro a ha _
          obtain ⟨j, x, hjx, rfl⟩ := pushElemAt_mem ha
          have hjlt : j < args.length := (List.getElem?_eq_some_iff.mp hjx).1
          have hinst_j : (instantiateArgs 0 ρ args)[j]? = some (ρ x) := by
            simp [hjx, instantiate]
          obtain ⟨l, hl, hlv, _⟩ := hel' j (ρ x) hinst_j
          have hlen_push : termValue ε (push v ρ) h' (.length (i + 1)) = some ((ls.length + args.length : Nat) : Int) := by
            simpa [Term.length, Term.now, termValue, termAt, push] using hlen_after
          have heval : (⟨[(.length (i + 1), 1)], -((args.length - (0 + j) : Nat) : Int)⟩ : IndexShift).eval ε (push v ρ) h' 0 =
              some (ls.length + j) := by
            simp only [IndexShift.eval, List.all_cons, List.all_nil, Bool.and_true, hlen_push, Option.isSome_some,
              ↓reduceIte, Linear.Form.eval, termValuation, Option.getD_some]
            have hpos : (0 : Int) ≤ ((0 : Nat) : Int) + (1 * ((ls.length + args.length : Nat) : Int) + 0) +
                -((args.length - (0 + j) : Nat) : Int) := by omega
            simp only [hpos, ↓reduceIte]
            congr 1
            omega
          refine ⟨st, ls', ls.length + j, by simpa [push] using elementsOf_spine hsp,
            by rw [hls']; rfl, heval, by omega, ?_, ?_⟩
          · intro l' hl'; rw [hl] at hl'; cases hl'; simpa [push] using hlv
          · intro hno; rw [hl] at hno; cases hno
        · exact indexHolds_nil _ _
      | _ => exact indexHolds_nil _ _
    | _ => exact indexHolds_nil _ _
  · exact indexHolds_nil _ _

open HeapKnowledge in
/-- Quantified facts over the receiver copied onto the fresh result at slot `0`
by a heap-preserving shallow-copy call (`Array.prototype.slice()`). -/
@[nospecialize] def shallowCopyKept (G : NormalGraph ι) (Γ : List (Ty ι)) (eff : Effect) (t : Tm)
    (k0 : Knowledge) : List IndexAtom :=
  if !(keepsHeap eff && eff.schema.normal.shallowCopyResult) then []
  else match receiverSlot t with
    | none => []
    | some r =>
      if !HeapExpressionRules.arrayPathOf G Γ r [] then []
      else k0.indices.flatMap fun a =>
        if a.cond.isSome then []
        else match a.fact with
          | .every s p start stop body =>
            if !(Footprints.slotsOf k0.links s p).contains r then []
            else match (IndexFact.every s p start stop body).mapM (fun i => some (i + 1)) with
              | some (.every _ _ start' stop' body') =>
                let base : IndexAtom := { fact := .every 0 [] start' stop' body' }
                if stop == IndexBound.ofTerm (Term.now .length s p) || stop == IndexBound.ofTerm (Term.length r) then
                  [base, { fact := .every 0 [] start' (IndexBound.ofTerm (.length 0)) body' }]
                else [base]
              | _ => []
          | _ => []

open HeapKnowledge in
private theorem readPath_mono {h h' : Heap} (hext : ∀ (l : Nat) u, h[l]? = some u → h'[l]? = some u) :
    ∀ {p : List String} {u w : Val}, readPath h u p = some w → readPath h' u p = some w
  | [], _, _, hr => hr
  | f :: q, u, w, hr => by
    cases u with
    | objAt fs cd oid =>
      simp only [readPath] at hr ⊢
      cases hlk : fs.lookup (.str f) with
      | none => simp [hlk] at hr
      | some l =>
        simp only [hlk] at hr ⊢
        cases hlu : h[l]? with
        | none => simp [hlu] at hr
        | some v =>
          simp only [hlu] at hr
          rw [hext l v hlu]
          exact readPath_mono hext hr
    | _ => simp [readPath] at hr

open HeapKnowledge in
private theorem readGuard_mono {h h' : Heap} (hext : ∀ (l : Nat) u, h[l]? = some u → h'[l]? = some u) :
    ∀ {p : List String} {u w : Val}, readGuard h u p = some w → readGuard h' u p = some w
  | [], _, _, hr => hr
  | f :: q, u, w, hr => by
    cases u with
    | objAt fs cd oid =>
      simp only [readGuard] at hr ⊢
      cases hlk : fs.lookup (.str f) with
      | none =>
        simp only [hlk] at hr ⊢
        by_cases hproto : fs.lookup CallArguments.protoField = none
        · simp only [hproto, ↓reduceIte] at hr ⊢
          exact readGuard_mono hext hr
        · simp only [hproto, ↓reduceIte] at hr; cases hr
      | some l =>
        simp only [hlk] at hr ⊢
        cases hlu : h[l]? with
        | none => simp [hlu] at hr
        | some v =>
          simp only [hlu] at hr
          rw [hext l v hlu]
          exact readGuard_mono hext hr
    | _ => simp [readGuard] at hr

open HeapKnowledge in
private theorem termValue_mono {ρ : Env} {h h' : Heap} (hext : ∀ (l : Nat) u, h[l]? = some u → h'[l]? = some u)
    {t : Term} {z : Int} (ht : termValue ε ρ h t = some z) : termValue ε ρ h' t = some z := by
  cases hae : t.atEntry
  · rw [termValue_now hae] at ht ⊢
    simp only [termAt, Option.bind_eq_some_iff] at ht ⊢
    obtain ⟨w, hw, hkv⟩ := ht
    refine ⟨w, readPath_mono hext hw, ?_⟩
    cases hkd : t.kind with
    | value | strLength | view | bitMask _ => rw [hkd] at hkv; exact hkv
    | length =>
      rw [hkd] at hkv
      obtain ⟨st, ls, hsp, hls, rfl, hmax⟩ := lengthOf_spine hkv
      exact lengthOf_of_spine hsp (hext st (.arr ls) hls) hmax
  · rwa [termValue_entry_invariant (ρ' := ρ) (h' := h) hae]

open HeapKnowledge in
private theorem shift_eval_mono {ρ : Env} {h h' : Heap} (hext : ∀ (l : Nat) u, h[l]? = some u → h'[l]? = some u)
    {sh : IndexShift} {i j : Nat} (hsh : sh.eval ε ρ h i = some j) : sh.eval ε ρ h' i = some j := by
  have hdef : ∀ (ts : Linear.Form Term),
      (ts.all fun p => (termValue ε ρ h p.1).isSome) = true →
      (ts.all fun p => (termValue ε ρ h' p.1).isSome) = true ∧
      Linear.Form.eval (termValuation ε ρ h') ts = Linear.Form.eval (termValuation ε ρ h) ts := by
    intro ts
    induction ts with
    | nil => intro _; simp [Linear.Form.eval]
    | cons p ts ih =>
      intro hall
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hall.1
      have hz' := termValue_mono hext hz
      obtain ⟨hd, hev⟩ := ih hall.2
      exact ⟨by simp [hz', hd], by simp [Linear.Form.eval, termValuation, hz, hz', hev]⟩
  simp only [IndexShift.eval] at hsh ⊢
  split at hsh
  · rename_i hall
    obtain ⟨hd, hev⟩ := hdef sh.terms hall
    simp only [hd, ↓reduceIte, hev]
    exact hsh
  · cases hsh

open HeapKnowledge in
private theorem bodyClause_shallowCopy {ρ : Env} {h h' : Heap} {ls₁ ls₂ : List (Option Nat)} {j : Nat}
    (hext : ∀ (l : Nat) u, h[l]? = some u → h'[l]? = some u)
    (hcopy : ∀ i < ls₁.length, (ls₁[i]? = some none ∧ ls₂[i]? = some none) ∨
      ∃ l₁ l₂ u, ls₁[i]? = some (some l₁) ∧ ls₂[i]? = some (some l₂) ∧ h[l₁]? = some u ∧ h'[l₂]? = some u) :
    ∀ {B : BodyClause}, B.HoldsAt ε ρ h ls₁ j → B.HoldsAt ε ρ h' ls₂ j := by
  have hcell : ∀ (m : Nat) (l₁ : Nat) (u : Val), ls₁[m]? = some (some l₁) → h[l₁]? = some u →
      ∃ l₂, ls₂[m]? = some (some l₂) ∧ h'[l₂]? = some u := by
    intro m l₁ u hl₁ hu
    have hm : m < ls₁.length := (List.getElem?_eq_some_iff.mp hl₁).1
    rcases hcopy m hm with ⟨hno, _⟩ | ⟨l₁', l₂, u', hl₁', hl₂', hu₁', hu₂'⟩
    · rw [hl₁] at hno; cases hno
    · rw [hl₁] at hl₁'; cases hl₁'
      rw [hu] at hu₁'; cases hu₁'
      exact ⟨l₂, hl₂', hu₂'⟩
  intro B
  induction B with
  | clause C =>
    intro hC
    refine LinearClause.holdsAt_extend (fun b _ z hz => ?_) hC
    cases b with
    | index => exact hz
    | free tm => exact termValue_mono hext hz
    | elem =>
      simp only [boundValue, elementInt] at hz ⊢
      split at hz
      · rename_i l₁ hl₁
        obtain ⟨u, hu, hi⟩ := Option.bind_eq_some_iff.mp hz
        obtain ⟨l₂, hl₂, hu₂⟩ := hcell j l₁ u hl₁ hu
        simp [hl₂, hu₂, hi]
      · cases hz
    | offset d =>
      simp only [boundValue, elementInt] at hz ⊢
      split at hz
      · rename_i l₁ hl₁
        obtain ⟨u, hu, hi⟩ := Option.bind_eq_some_iff.mp hz
        obtain ⟨l₂, hl₂, hu₂⟩ := hcell (j + d) l₁ u hl₁ hu
        simp [hl₂, hu₂, hi]
      · cases hz
    | project kd ep =>
      simp only [boundValue] at hz ⊢
      split at hz
      · rename_i l₁ hl₁
        obtain ⟨u, hu, htz⟩ := Option.bind_eq_some_iff.mp hz
        obtain ⟨l₂, hl₂, hu₂⟩ := hcell j l₁ u hl₁ hu
        simp only [hl₂, hu₂, Option.bind_some]
        exact termValue_mono hext htz
      · cases hz
    | parallel s' p' sh kd ep =>
      simp only [boundValue] at hz ⊢
      cases hsh : sh.eval ε ρ h j with
      | none => simp [hsh] at hz
      | some m =>
        simp only [hsh] at hz
        rw [shift_eval_mono hext hsh]
        cases hrp : readPath h (ρ s') p' with
        | none => simp [hrp] at hz
        | some arr =>
          simp only [hrp] at hz
          rw [readPath_mono hext hrp]
          cases hel : elementsOf arr with
          | none => simp [hel] at hz
          | some st =>
            simp only [hel] at hz ⊢
            cases hls : h[st]?.bind spineEntries with
            | none => simp [hls] at hz
            | some ls' =>
              simp only [hls] at hz
              obtain ⟨u, hu, hue⟩ := Option.bind_eq_some_iff.mp hls
              rw [hext st u hu]
              simp only [Option.bind_some, hue]
              split at hz
              · rename_i l₁ hl₁
                obtain ⟨u₁, hu₁, htz⟩ := Option.bind_eq_some_iff.mp hz
                rw [hext l₁ u₁ hu₁]
                exact termValue_mono hext htz
              · cases hz
  | guarded tgt g b ih =>
    intro hB
    have hread : ∀ w, tgt.read ε ρ h ls₁ j = some w → tgt.read ε ρ h' ls₂ j = some w := by
      intro w hw
      cases tgt with
      | self ep =>
        simp only [ElemTarget.read] at hw ⊢
        split at hw
        · rename_i l₁ hl₁
          obtain ⟨u, hu, hrg⟩ := Option.bind_eq_some_iff.mp hw
          obtain ⟨l₂, hl₂, hu₂⟩ := hcell j l₁ u hl₁ hu
          simp only [hl₂, hu₂, Option.bind_some]
          exact readGuard_mono hext hrg
        · cases hw
      | parallel s' p' sh ep =>
        simp only [ElemTarget.read] at hw ⊢
        cases hsh : sh.eval ε ρ h j with
        | none => simp [hsh] at hw
        | some m =>
          simp only [hsh] at hw
          rw [shift_eval_mono hext hsh]
          cases hrp : readPath h (ρ s') p' with
          | none => simp [hrp] at hw
          | some arr =>
            simp only [hrp] at hw
            rw [readPath_mono hext hrp]
            cases hel : elementsOf arr with
            | none => simp [hel] at hw
            | some st =>
              simp only [hel] at hw ⊢
              cases hls : h[st]?.bind spineEntries with
              | none => simp [hls] at hw
              | some ls' =>
                simp only [hls] at hw
                obtain ⟨u, hu, hue⟩ := Option.bind_eq_some_iff.mp hls
                rw [hext st u hu]
                simp only [Option.bind_some, hue]
                split at hw
                · rename_i l₁ hl₁
                  obtain ⟨u₁, hu₁, hrg⟩ := Option.bind_eq_some_iff.mp hw
                  rw [hext l₁ u₁ hu₁]
                  exact readGuard_mono hext hrg
                · cases hw
    rcases hB with ⟨w, hw, hg⟩ | ⟨hpres, hb⟩
    · exact .inl ⟨w, hread w hw, hg⟩
    · exact .inr ⟨fun hne => let ⟨w, hw⟩ := hpres hne; ⟨w, hread w hw⟩, ih hb⟩
  | either A B ihA ihB =>
    intro hB
    exact hB.imp ihA ihB

open HeapKnowledge in
private theorem shallowCopyKept_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {eff : Effect} {t : Tm}
    {k0 : Knowledge} {ρ : Env} {h h' : Heap} {v : Tm} {nw : Nat} {W : WorldT (nw + 4)}
    (he : EnvOk G Γ ρ (nw + 4) W) (hk0 : Holds k0 ε ρ h) (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hcat : Footprints.ClassOk Footprints.intrinsicClasses
      (CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v) :
    IndexHolds ε (shallowCopyKept G Γ eff t k0) (push v ρ) h' := by
  unfold shallowCopyKept
  split
  · exact indexHolds_nil _ _
  rename_i hcond
  have ⟨hkh, hsc⟩ : keepsHeap eff = true ∧ eff.schema.normal.shallowCopyResult = true := by
    simpa [Bool.and_eq_true] using hcond
  have hext : ∀ (l : Nat) u, h[l]? = some u → h'[l]? = some u := by
    have hpre : h <+: h' := keepsHeap_prefix hkh hcat (CallEffects.Effect.callPost_within hq)
    intro l u hlu
    obtain ⟨tail, rfl⟩ := hpre
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hlu).1, hlu]
  cases hr : receiverSlot t with
  | none => exact indexHolds_nil _ _
  | some r =>
    dsimp only
    split
    · exact indexHolds_nil _ _
    rename_i harr
    have harr' : HeapExpressionRules.arrayPathOf G Γ r [] = true := by simpa using harr
    have hsc_post : CallEffects.ShallowCopy (ρ r) v h h' := by
      have hsc0 := CallEffects.Effect.callPost_shallowCopy hsc hq
      obtain ⟨f, args, rfl⟩ := receiverSlot_term hr
      simpa [ExpressionEffects.receiverOf, instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] using hsc0
    intro atom hatom _
    obtain ⟨a, haMem, hflat⟩ := List.mem_flatMap.mp hatom
    split at hflat
    · cases hflat
    rename_i hacond
    have hac : a.cond = none := by cases h0 : a.cond <;> simp_all
    have haH := hk0.2.2.2.2.2 a haMem (fun b hb => by rw [hac] at hb; cases hb)
    cases haf : a.fact <;> simp only [haf] at hflat <;> try cases hflat
    rename_i s p start stop body
    rw [haf] at haH
    split at hflat
    · cases hflat
    rename_i hslot
    have hslot' : (Footprints.slotsOf k0.links s p).contains r = true := by simpa using hslot
    cases hmap : (IndexFact.every s p start stop body).mapM (fun i => some (i + 1)) with
    | none => rw [hmap] at hflat; cases hflat
    | some mapped =>
      rw [hmap] at hflat
      cases mapped <;> simp only at hflat <;> try cases hflat
      rename_i s' p' start' stop' body'
      obtain ⟨w, st₁, ls₁, m, n, hw, hel₁, hls₁, hstart, hstop, hall⟩ := haH
      have hwr : w = ρ r := by
        rw [Footprints.slotsOf_read hk0.2.2.1 (List.contains_iff_mem.mp hslot')] at hw
        cases hw; rfl
      subst hwr
      obtain ⟨hsp₁, hls₁_arr⟩ := HeapExpressionRules.arrayPathOf_sound he hok hρ r [] (ρ r) st₁ harr' rfl hel₁
      obtain ⟨st₂, ls₂, hsp₂, hls₂, hlen₂, hcopy⟩ := hsc_post st₁ ls₁ hsp₁ (hls₁_arr ls₁ hls₁)
      obtain ⟨hmapStart, hmapStop, hmapBody⟩ : start.mapM (fun i => some (i + 1)) = some start' ∧
          stop.mapM (fun i => some (i + 1)) = some stop' ∧
          IndexFact.mapBody (fun i => some (i + 1)) body = some body' := by
        simp only [IndexFact.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq, IndexFact.every.injEq] at hmap
        obtain ⟨_, -, start0, hs0, stop0, hst0, body0, hbd0, -, -, rfl, rfl, rfl⟩ := hmap
        exact ⟨hs0, hst0, hbd0⟩
      have hbmono : ∀ (b : IndexBound) (z : Int), b.eval ε ρ h = some z → b.eval ε ρ h' = some z := by
        intro b z hb
        cases b with
        | mk bs off =>
          cases bs with
          | none => exact hb
          | some tb =>
            simp only [IndexBound.eval, Option.map_eq_some_iff] at hb ⊢
            obtain ⟨u, hu, rfl⟩ := hb
            exact ⟨u, termValue_mono hext hu, rfl⟩
      have hstart' : start'.eval ε (push v ρ) h' = some m := by
        rw [IndexBound.eval_mapM hmapStart (fun _ _ j hj => by cases hj; rfl)]; exact hbmono _ _ hstart
      have hstop' : stop'.eval ε (push v ρ) h' = some n := by
        rw [IndexBound.eval_mapM hmapStop (fun _ _ j hj => by cases hj; rfl)]; exact hbmono _ _ hstop
      have hall' : ∀ j : Nat, m ≤ (j : Int) → (j : Int) < n → ∀ B' ∈ body', B'.HoldsAt ε (push v ρ) h' ls₂ j := by
        intro j hlo hj B' hB'
        obtain ⟨B, hB, hBm⟩ := (IndexFact.mapBody_pairs hmapBody).1 B' hB'
        have h1 : B.HoldsAt ε ρ h' ls₂ j := bodyClause_shallowCopy hext hcopy (hall j hlo hj B hB)
        exact (BodyClause.holdsAt_mapM hBm (fun x _ y hy => by cases hy; rfl)).mpr h1
      split at hflat
      · rename_i hstLen
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hflat
        rcases hflat with rfl | rfl
        · exact ⟨v, st₂, ls₂, m, n, rfl, elementsOf_spine hsp₂, by rw [hls₂]; rfl, hstart', hstop', hall'⟩
        · have hlen_r : lengthOf h (ρ r) = some n := by
            rcases Bool.or_eq_true_iff.mp hstLen with h1 | h2
            · rw [beq_iff_eq.mp h1] at hstop
              simp only [IndexBound.ofTerm, IndexBound.eval, Option.map_eq_some_iff, Int.add_zero] at hstop
              obtain ⟨v0, hv0, rfl⟩ := hstop
              simpa [Term.now, termValue, termAt, hw, kindValue] using hv0
            · rw [beq_iff_eq.mp h2] at hstop
              simp only [IndexBound.ofTerm, IndexBound.eval, Option.map_eq_some_iff, Int.add_zero] at hstop
              obtain ⟨v0, hv0, rfl⟩ := hstop
              simpa [termValue_length] using hv0
          obtain ⟨st0, ls0, hsp0, hls0, hneq, hmax⟩ := lengthOf_spine hlen_r
          rw [hsp₁] at hsp0; cases hsp0
          rw [hls₁_arr ls₁ hls₁] at hls0; cases hls0
          have hlen_t : termValue ε (push v ρ) h' (.length 0) = some n := by
            simp only [termValue_length, push]
            rw [hneq, ← hlen₂]
            exact lengthOf_of_spine hsp₂ hls₂ (by omega)
          have hlen_v : (IndexBound.ofTerm (.length 0)).eval ε (push v ρ) h' = some n := by
            simp [IndexBound.ofTerm, IndexBound.eval, hlen_t]
          exact ⟨v, st₂, ls₂, m, n, rfl, elementsOf_spine hsp₂, by rw [hls₂]; rfl, hstart', hlen_v, hall'⟩
      · simp only [List.mem_singleton] at hflat
        subst hflat
        exact ⟨v, st₂, ls₂, m, n, rfl, elementsOf_spine hsp₂, by rw [hls₂]; rfl, hstart', hstop', hall'⟩

/-- Knowledge with a call's result-fact atoms added, the atoms, the cell
facts and the read links of its entry `k0` its footprint keeps (`effectKept`,
`frameCells`, `frameLinks`), any return-alias links (`sameLinks`), any fresh
array spine separations (`freshCallSpineApart`), any fresh array region
separations (`freshCallApart`), any push element witnesses (`pushElemAtoms`),
any shallow-copy quantified facts (`shallowCopyKept`), and the quantified
atoms its growth of its receiver's spine keeps or extends (`appendKept`), then
the instances of quantified facts the element reads among them state
(`withElements`). -/
def withEnsures (stable : Nat → String → Bool) (G : NormalGraph ι) (Γ : List (Ty ι)) (eff : Effect) (t : Tm) (k0 k : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge :=
  let kLinks := Std.HashSet.ofList k.links
  HeapKnowledge.dischargeGuards <| HeapKnowledge.withElementsAfter k.indices.length k.links.length
    { k with cells := k.cells ++ (frameCells stable eff t k0).filter (!k.cells.contains ·),
             links := k.links ++ (frameLinks stable eff t k0).filter (!kLinks.contains ·) ++ sameLinks eff t,
             indices := k.indices ++ ensuresAtoms eff t ++ effectKept G Γ stable (HeapExpressionRules.arrayPathOf G Γ) eff t k0 ++ appendKept G Γ eff t k0 ++
        writeKept G Γ eff t k0 ++ linearAppendKept G Γ eff t k0 ++ ensuresComposed stable eff t k0 ++
        freshCallSpineApart stable G Γ eff t k0 ++ freshCallApart stable G Γ eff t k0 ++
        pushElemAtoms G Γ eff t k0 ++ shallowCopyKept G Γ eff t k0 }

theorem withEnsures_holds {stable : Nat → String → Bool} {G : NormalGraph ι} {Γ : List (Ty ι)} {eff : Effect} {t : Tm} {k0 k : HeapKnowledge.Knowledge} {ρ : Env} {h h' : Heap} {v : Tm}
    (hv : ∀ i, i < Γ.length → isVal (ρ i) = true)
    (hk : HeapKnowledge.Holds k ε (push v ρ) h') {nw : Nat} {W : WorldT (nw + 4)} (he : EnvOk G Γ ρ (nw + 4) W) (hk0 : HeapKnowledge.Holds k0 ε ρ h)
    (hok : HeapOk (nw + 4) W h) (hρ : RootsOk W ρ)
    (hcat : Footprints.ClassOk Footprints.intrinsicClasses
      (CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h)
    (hq : eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h' v)
    (hstable : HeapKnowledge.FirstKept stable ρ h h') :
    HeapKnowledge.Holds (withEnsures stable G Γ eff t k0 k) ε (push v ρ) h' := HeapKnowledge.dischargeGuards_holds <| HeapKnowledge.withElementsAfter_holds
  ⟨fun f hf => (List.mem_append.mp hf).elim (hk.1 f)
      (fun hf => frameCells_holds hk0 hok hρ hq hstable f (List.mem_filter.mp hf).1),
    hk.2.1,
    fun g hg => (List.mem_append.mp hg).elim
      (fun hg => (List.mem_append.mp hg).elim (hk.2.2.1 g)
        (fun hg => frameLinks_holds hk0 hok hρ hq hstable g (List.mem_filter.mp hg).1))
      (fun hg => sameLinks_holds hq g hg),
    hk.2.2.2.1, hk.2.2.2.2.1, fun a ha hc => by
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp ha with ha | ha
          · rcases List.mem_append.mp ha with ha | ha
            · rcases List.mem_append.mp ha with ha | ha
              · rcases List.mem_append.mp ha with ha | ha
                · rcases List.mem_append.mp ha with ha | ha
                  · rcases List.mem_append.mp ha with ha | ha
                    · rcases List.mem_append.mp ha with ha | ha
                      · exact hk.2.2.2.2.2 a ha hc
                      · exact ensuresAtoms_holds (fun F hF he => (HeapKnowledge.IndexFact.holdsAt_entry he _).mp
                        (CallEffects.Effect.callPost_ensures hF hq)) a ha hc
                    · exact effectKept_holds he hk0 hok hρ hq hstable (HeapExpressionRules.arrayPathOf_sound he hok hρ) a ha hc
                  · exact appendKept_holds hv he hk0 hok hρ hq a ha hc
                · exact writeKept_holds he hk0 hok hρ hq a ha hc
              · exact linearAppendKept_holds hv he hk0 hok hρ hq a ha hc
            · exact ensuresComposed_holds hk0 hok hρ hq hstable a ha hc
          · exact freshCallSpineApart_holds hk0 hok hρ hq hstable a ha hc
        · exact freshCallApart_holds he hk0 hok hρ hq hstable a ha hc
      · exact pushElemAtoms_holds hv he hk0 hok hq a ha hc
    · exact shallowCopyKept_holds he hk0 hok hρ hcat hq a ha hc⟩

/-- Whether a term is a call or construction (which takes at least 3 small
steps to produce a value). -/
def isCallTerm : Tm → Bool
  | .invoke .. | .construct .. => true
  | _ => false

theorem isCallTerm_instantiate (d : Nat) (ρ : Env) {t : Tm} (h : isCallTerm t = true) :
    isCallTerm (instantiate d ρ t) = true := by
  cases t <;> simp_all [isCallTerm, instantiate]

private theorem nonVal_safePost_le_one {Ξ T : Fam} {Q Q' : Post} :
    ∀ {n : Nat}, n ≤ 1 → ∀ {W : WorldT n} {h : Heap} {t : Tm},
      isVal t = false → SafePost Ξ T Q n W h t → SafePost Ξ T Q' n W h t
  | 0, _, _, _, _, _, hs => hs
  | 1, _, _, _, _, hnv, ⟨hrf, hs⟩ => by
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, -⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs'⟩
    · rw [hnv] at hv; cases hv
    · exact .inl (.inr hth)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, SafePostW.refs hs'⟩
  | n + 2, hn, _, _, _, _, _ => by omega

private theorem goto_safePost_le_two {Ξ T : Fam} {Q Q' : Post} :
    ∀ {n : Nat}, n ≤ 2 → ∀ {W : WorldT n} {h : Heap} {E K start env d comp},
      SafePost Ξ T Q n W h (.goto E K start env d comp) →
      SafePost Ξ T Q' n W h (.goto E K start env d comp)
  | 0, _, _, _, _, _, _, _, _, _, hs => hs
  | n + 1, hn, _, h, _, _, _, _, _, _, ⟨hrf, hs⟩ => by
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, -⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs'⟩
    · simp [isVal] at hv
    · exact .inl (.inr hth)
    · cases step with
      | gotoEnter hE hK =>
        exact .inr ⟨U, h, _, hx, hu, .gotoEnter hE hK, hh,
          nonVal_safePost_le_one (by omega) rfl hs'⟩

private theorem letArr_safePost_le_two {Ξ T : Fam} {Q Q' : Post} :
    ∀ {n : Nat}, n ≤ 2 → ∀ {W : WorldT n} {h : Heap} {inits b},
      SafePost Ξ T Q n W h (.letE (.arrLit inits) b) →
      SafePost Ξ T Q' n W h (.letE (.arrLit inits) b)
  | 0, _, _, _, _, _, hs => hs
  | n + 1, hn, _, _, _, _, ⟨hrf, hs⟩ => by
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, -⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs'⟩
    · simp [isVal] at hv
    · exact .inl (.inr hth)
    · cases step with
      | letV hv => simp [isVal] at hv
      | letC st =>
        exact .inr ⟨U, h', _, hx, hu, .letC st, hh,
          nonVal_safePost_le_one (by omega) rfl hs'⟩

theorem call_safePost_le_three {Ξ T : Fam} {Q Q' : Post} :
    ∀ {n : Nat}, n ≤ 3 → ∀ {W : WorldT n} {h : Heap} {t : Tm},
      isCallTerm t = true → SafePost Ξ T Q n W h t → SafePost Ξ T Q' n W h t
  | 0, _, _, _, _, _, hs => hs
  | n + 1, hn, W, h, t, hcall, ⟨hrf, hs⟩ => by
    have hnv : isVal t = false := by cases t <;> simp [isCallTerm, isVal] at hcall ⊢
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, -⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs'⟩
    · rw [hnv] at hv; cases hv
    · exact .inl (.inr hth)
    · refine .inr ⟨U, h', t', hx, hu, step, hh, ?_⟩
      cases t <;> simp [isCallTerm] at hcall
      · cases step with
        | callL | callRecv | callArg | callBound | callSpread =>
          exact call_safePost_le_three (by omega) rfl hs'
        | callGraph =>
          unfold CallArguments.graphEntry at hs' ⊢
          split at *
          · exact goto_safePost_le_two (by omega) hs'
          · exact letArr_safePost_le_two (by omega) hs'
      · cases step with
        | constructL | constructArg | constructSpread =>
          exact call_safePost_le_three (by omega) rfl hs'
        | constructGraph =>
          unfold CallArguments.graphEntry at hs' ⊢
          split at *
          · exact goto_safePost_le_two (by omega) hs'
          · exact letArr_safePost_le_two (by omega) hs'

/-- Knowledge with the region facts a call growing its receiver's spine keeps
(`IndexWrites.grownRegions`) added, renamed past the result, where its
normal exit states the receiver's growth and the append (`statesExtension`,
`statesAppend`); none otherwise. -/
def withGrown (eff : Effect) (out : HeapKnowledge.Knowledge) (kept : List HeapKnowledge.IndexAtom) :
    HeapKnowledge.Knowledge :=
  if statesExtension eff && statesAppend eff then
    { out with indices := out.indices ++ HeapKnowledge.shiftIndices kept }
  else out

theorem withGrown_grows {eff : Effect} (hg : (statesExtension eff && statesAppend eff) = true) {r : Tm}
    {args : List Tm} {before after : Heap} {v : Tm} (hp : eff.callPost r args before after v) :
    CallEffects.ReceiverGrows r before after :=
  statesExtension_grows (Bool.and_eq_true_iff.mp hg).1 hp

theorem withGrown_appends {eff : Effect} (hg : (statesExtension eff && statesAppend eff) = true) {r : Tm}
    {args : List Tm} {before after : Heap} {v : Tm} (hp : eff.callPost r args before after v) :
    CallEffects.ReceiverAppends r args before after :=
  statesAppend_appends (Bool.and_eq_true_iff.mp hg).2 hp

theorem withGrown_holds {eff : Effect} {out : HeapKnowledge.Knowledge} {kept : List HeapKnowledge.IndexAtom}
    {ρ : Env} {h' : Heap} {v : Tm} (ho : HeapKnowledge.Holds out ε (push v ρ) h')
    (hk : (statesExtension eff && statesAppend eff) = true → HeapKnowledge.IndexHolds ε kept ρ h') :
    HeapKnowledge.Holds (withGrown eff out kept) ε (push v ρ) h' := by
  unfold withGrown
  split
  · rename_i hg
    exact ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.1, ho.2.2.2.2.1,
      IndexWrites.indexHolds_cat ho.2.2.2.2.2 (HeapKnowledge.shiftIndices_holds (hk hg))⟩
  · exact ho

/-- The selected signature of an ordinary step's evidence that `call-ensures`
applies to: at the sequent `j`, a call checked as `selected_sound` or as
`call-requires` admits it, at a selected signature stating a postcondition. -/
@[nospecialize] def ensuresCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (k : HeapKnowledge.Knowledge) (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) : Option Effect :=
  match e with
  | .ordinary p =>
    if isCallTerm j.term && decide (claim p = j) && (ExpressionEffects.selectedOperands p && checkTreeUsing G images p codes sums ||
        requiresTree G images k codes sums p) then
      match ExpressionEffects.selectedEffect p with
      | some eff => if eff.schema.normal.facts.isEmpty && !eff.schema.normal.freshResult && !eff.schema.normal.freshRegionResult && !eff.schema.normal.shallowCopyResult && (effectKept G j.context
          (HeapExpressionRules.stableFirst G j.context) (HeapExpressionRules.arrayPathOf G j.context) eff j.term k).isEmpty && (appendKept G j.context eff j.term k).isEmpty &&
          (writeKept G j.context eff j.term k).isEmpty &&
          (linearAppendKept G j.context eff j.term k).isEmpty && (pushElemAtoms G j.context eff j.term k).isEmpty && (frameCells (HeapExpressionRules.stableFirst G j.context) eff j.term k).isEmpty && (frameLinks (HeapExpressionRules.stableFirst G j.context) eff j.term k).isEmpty && (sameLinks eff j.term).isEmpty then none else some eff
      | none => none
    else none
  | _ => none

/-- `ensuresCall` as the compiled verifier runs it (`ensuresCall_eq_fast`):
the signature's postcondition read first, the sequent and derivation checked
only where it states one. -/
def ensuresCallFast (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (k : HeapKnowledge.Knowledge) (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) : Option Effect :=
  match e with
  | .ordinary p =>
    match ExpressionEffects.selectedEffect p with
    | some eff => if eff.schema.normal.facts.isEmpty && !eff.schema.normal.freshResult && !eff.schema.normal.freshRegionResult && !eff.schema.normal.shallowCopyResult && (effectKept G j.context
          (HeapExpressionRules.stableFirst G j.context) (HeapExpressionRules.arrayPathOf G j.context) eff j.term k).isEmpty && (appendKept G j.context eff j.term k).isEmpty &&
          (writeKept G j.context eff j.term k).isEmpty &&
          (linearAppendKept G j.context eff j.term k).isEmpty && (pushElemAtoms G j.context eff j.term k).isEmpty && (frameCells (HeapExpressionRules.stableFirst G j.context) eff j.term k).isEmpty && (frameLinks (HeapExpressionRules.stableFirst G j.context) eff j.term k).isEmpty && (sameLinks eff j.term).isEmpty then none
      else if isCallTerm j.term && decide (claim p = j) && (ExpressionEffects.selectedOperands p && checkTreeUsing G images p codes sums ||
          requiresTree G images k codes sums p) then some eff else none
    | none => none
  | _ => none

@[csimp] theorem ensuresCall_eq_fast : @ensuresCall = @ensuresCallFast := by
  funext ι _ G images j k e codes sums
  unfold ensuresCall ensuresCallFast
  split
  · rename_i p
    cases ExpressionEffects.selectedEffect p <;> split <;> split <;> simp_all
  · rfl

theorem ensuresCall_isCallTerm {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k : HeapKnowledge.Knowledge} {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {eff : Effect}
    (hc : ensuresCall G images j k e codes sums = some eff) : isCallTerm j.term = true := by
  unfold ensuresCall at hc
  split at hc
  · split at hc
    · rename_i hcond; simp only [Bool.and_eq_true] at hcond; exact hcond.1.1
    · cases hc
  · cases hc

/-- **`call-ensures`**: such a call's normal return meets its selected
signature's postcondition at its receiver and actuals, its `ensures` facts
included. -/
theorem ensuresCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k : HeapKnowledge.Knowledge} {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {eff : Effect}
    (hc : ensuresCall G images j k e codes sums = some eff) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type)
      (eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ j.term))
        (ExpressionEffects.actualsOf (instantiate 0 ρ j.term)) h) n W h (instantiate 0 ρ j.term) := by
  unfold ensuresCall at hc
  split at hc
  · rename_i p
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨_, rfl⟩, hcheck⟩ := hcond
      cases hsel : ExpressionEffects.selectedEffect p with
      | none => simp [hsel] at hc
      | some eff' =>
        simp only [hsel] at hc
        split at hc
        · cases hc
        · cases hc
          rcases hcheck with ⟨hops, ht⟩ | hreq
          · exact ExpressionEffects.selected_sound p ht hops hsel hcodes hsums he hw hh href
          · obtain ⟨eff'', hsel', hs⟩ := requiresTree_sound hcodes hsums p hreq
            rw [hsel] at hsel'
            cases hsel'
            exact hs he hk hw hh href
    · cases hc
  · cases hc

/-! ### A negation of a Boolean slot

`if x then false else true` on the slot `x` steps once, in the heap it starts
in, to the negation of `x`'s Boolean: an atom conditional on `x`'s
truthiness holds conditional on the result's falsiness (`not-elements`). -/

/-- The slot a term negates, where it is `if x then false else true`, the
test of `x` a Boolean's or its truthiness. -/
def negationOf (j : Sequent ι) : Option Nat :=
  match j.term with
  | .ite (.var x) .fls .tru | .ite (.test .truthy (.var x)) .fls .tru =>
    if x < j.context.length then some x else none
  | _ => none

theorem negation_run {Ξ T : Fam} {Q : Post} {v : Tm} (hv : isVal v = true) :
    ∀ {n W h}, SafePost Ξ T Q n W h (.ite v .fls .tru) →
      SafePost Ξ T (fun h' u => Q h' u ∧ h' = h ∧ ((v = .tru ∧ u = .fls) ∨ (v = .fls ∧ u = .tru))) n W h
        (.ite v .fls .tru) := by
  intro n W h hs
  cases n with
  | zero => assumption
  | succ n =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hval, -, -⟩ | ⟨u, hr, -⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · simp [isVal] at hval
    · cases hr with
      | iteC hr => exact absurd (raises_not_val hr) (by simp [hv])
    · refine .inr ⟨U, h', t', hx, hu, step, hh, ?_⟩
      cases step with
      | iteC s => exact absurd s (value_no_step hv)
      | iteT =>
        cases n with
        | zero => assumption
        | succ m =>
          obtain ⟨hrf, hs⟩ := hs
          refine ⟨hrf, ?_⟩
          rcases hs with (⟨hval, ht, hq⟩ | ⟨u, hr, -⟩) | ⟨U', h'', t'', -, -, step', -, -⟩
          · exact .inl (.inl ⟨hval, ht, hq, rfl, .inl ⟨rfl, rfl⟩⟩)
          · exact absurd (raises_not_val hr) (by simp [isVal])
          · exact absurd step' (value_no_step (by simp [isVal]))
      | iteF =>
        cases n with
        | zero => assumption
        | succ m =>
          obtain ⟨hrf, hs⟩ := hs
          refine ⟨hrf, ?_⟩
          rcases hs with (⟨hval, ht, hq⟩ | ⟨u, hr, -⟩) | ⟨U', h'', t'', -, -, step', -, -⟩
          · exact .inl (.inl ⟨hval, ht, hq, rfl, .inr ⟨rfl, rfl⟩⟩)
          · exact absurd (raises_not_val hr) (by simp [isVal])
          · exact absurd step' (value_no_step (by simp [isVal]))

theorem negation_test_run {Ξ T : Fam} {Q : Post} {v : Tm} (hv : isVal v = true) :
    ∀ {n W h}, SafePost Ξ T Q n W h (.ite (.test .truthy v) .fls .tru) →
      SafePost Ξ T (fun h' u => Q h' u ∧ h' = h ∧
        ((tagHolds .truthy v = true ∧ u = .fls) ∨ (tagHolds .truthy v = false ∧ u = .tru))) n W h
        (.ite (.test .truthy v) .fls .tru) := by
  intro n W h hs
  cases n with
  | zero => assumption
  | succ n =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hval, -, -⟩ | ⟨u, hr, -⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · simp [isVal] at hval
    · cases hr with
      | iteC hr => cases hr with
        | testC hr => exact absurd (raises_not_val hr) (by simp [hv])
    · cases step with
      | iteC step =>
        cases step with
        | testC s => exact absurd s (value_no_step hv)
        | testV _ =>
          have hb : isVal (if tagHoldsIn h .truthy v then Tm.tru else .fls) = true := by
            split <;> rfl
          have hp : tagHoldsIn h .truthy v = tagHolds .truthy v := tagHoldsIn_of_protoFree (by simp [protoFree])
          refine .inr ⟨U, h, _, hx, hu, .iteC (.testV hv), hh, ?_⟩
          refine HeapObservations.weaken (fun h'' u hq => ⟨hq.1, hq.2.1, ?_⟩) (negation_run hb hs)
          rw [hp] at hq
          cases ht : tagHolds .truthy v
          · rw [ht] at hq
            rcases hq.2.2 with ⟨h1, -⟩ | ⟨-, h2⟩
            · cases h1
            · exact .inr ⟨rfl, h2⟩
          · rw [ht] at hq
            rcases hq.2.2 with ⟨-, h2⟩ | ⟨h1, -⟩
            · exact .inl ⟨rfl, h2⟩
            · cases h1

/-- The atoms on the negated slot's class, restated on the result with the
opposite condition. -/
def negatedAtoms (k : HeapKnowledge.Knowledge) (x : Nat) : List HeapKnowledge.ElemAtom :=
  (k.elems.filter fun a => a.cond.any fun c => (HeapLinks.aliases k.links x).contains c).map fun a =>
    { a with slot := a.slot + 1, cond := some 0, negated := !a.negated }

theorem negatedAtoms_holds {k : HeapKnowledge.Knowledge} {x : Nat} {ρ h u}
    (hk : HeapKnowledge.Holds k ε ρ h)
    (hu : (tagHolds .truthy (ρ x) = true ∧ u = .fls) ∨ (tagHolds .truthy (ρ x) = false ∧ u = .tru)) :
    HeapKnowledge.ElemsHolds (negatedAtoms k x) (push u ρ) h := by
  intro a ha hc
  obtain ⟨b, hb', rfl⟩ := List.mem_map.mp ha
  obtain ⟨hbm, hbc⟩ := List.mem_filter.mp hb'
  have hcu := hc 0 rfl
  simp only [push] at hcu
  cases hcb : b.cond with
  | none => rw [hcb] at hbc; simp at hbc
  | some c =>
    rw [hcb] at hbc
    simp only [Option.any_some, List.contains_iff_mem] at hbc
    have hrc : ρ c = ρ x := HeapLinks.aliases_eq hk.2.2.1 hbc
    have := hk.2.2.2.2.1 b hbm fun c' hc' => by
      rw [hcb] at hc'; cases hc'
      rw [hrc]
      rcases hu with ⟨hx, hu⟩ | ⟨hx, hu⟩
      · rw [hu] at hcu; rw [hx]; cases hn : b.negated <;> simp_all [tagHolds]
      · rw [hu] at hcu; rw [hx]; cases hn : b.negated <;> simp_all [tagHolds]
    simpa [push] using this

/-- The index atoms on the negated slot's class, restated on the result with
the opposite condition: the polarity of the condition flips, the fact stays. -/
def negatedIndices (k : HeapKnowledge.Knowledge) (x : Nat) : List HeapKnowledge.IndexAtom :=
  (k.indices.filter fun a => a.cond.any fun c => (HeapLinks.aliases k.links x).contains c).map fun a =>
    { a with fact := a.fact.map (· + 1), cond := some 0, negated := !a.negated }

theorem negatedIndices_holds {k : HeapKnowledge.Knowledge} {x : Nat} {ρ h u}
    (hk : HeapKnowledge.Holds k ε ρ h)
    (hu : (tagHolds .truthy (ρ x) = true ∧ u = .fls) ∨ (tagHolds .truthy (ρ x) = false ∧ u = .tru)) :
    HeapKnowledge.IndexHolds ε (negatedIndices k x) (push u ρ) h := by
  intro a ha hc
  obtain ⟨b, hb', rfl⟩ := List.mem_map.mp ha
  obtain ⟨hbm, hbc⟩ := List.mem_filter.mp hb'
  have hcu := hc 0 rfl
  simp only [push] at hcu
  cases hcb : b.cond with
  | none => rw [hcb] at hbc; simp at hbc
  | some c =>
    rw [hcb] at hbc
    simp only [Option.any_some, List.contains_iff_mem] at hbc
    have hrc : ρ c = ρ x := HeapLinks.aliases_eq hk.2.2.1 hbc
    have := hk.2.2.2.2.2 b hbm fun c' hc' => by
      rw [hcb] at hc'; cases hc'
      rw [hrc]
      rcases hu with ⟨hx, hu⟩ | ⟨hx, hu⟩
      · rw [hu] at hcu; rw [hx]; cases hn : b.negated <;> simp_all [tagHolds]
      · rw [hu] at hcu; rw [hx]; cases hn : b.negated <;> simp_all [tagHolds]
    exact (HeapKnowledge.IndexFact.holdsAt_map (fun s _ => rfl)).mpr this

theorem negation_bool {u v : Tm} (h : (v = .tru ∧ u = .fls) ∨ (v = .fls ∧ u = .tru)) :
    (tagHolds .truthy v = true ∧ u = .fls) ∨ (tagHolds .truthy v = false ∧ u = .tru) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

section Keeps
open HeapExpressionRules (StepEvidence KeepsPost)

/-! ## The calls the pass frames -/

/-- A call promising its receiver's elements keeps the heap: its selected
signature does (`keepsHeap_prefix`). -/
theorem elementsCall_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {x : Nat}
    {R : CallEffects.ElemPred} (hc : elementsCall G images j e codes sums = some (x, R))
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) : KeepsPost G j ρ n W h := by
  unfold elementsCall at hc
  split at hc
  · rename_i p _
    by_cases hcond : (decide (claim p = j) && ExpressionEffects.selectedOperands p &&
        checkTreeUsing G images p codes sums && onlyBool G j.type) = true
    · rw [ite_eq_left hcond] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨rfl, hops⟩, ht⟩, -⟩ := hcond
      cases hsel : ExpressionEffects.selectedEffect p with
      | none => simp [hsel] at hc
      | some eff =>
        cases hrs : receiverSlot (claim p).term with
        | none => simp [hsel, hrs] at hc
        | some x' =>
          simp only [hsel, hrs] at hc
          by_cases hkeep : keepsHeap eff = true
          · exact post_with_type
              (fun _ _ _ _ _ hq => ⟨Footprints.Closed.holds_empty.mpr (keepsHeap_prefix hkeep
                (Footprints.intrinsicClasses_ok hh (ExpressionEffects.callEnv_rootsOk_of_refs href))
                (CallEffects.Effect.callPost_within hq)), trivial⟩)
              (ExpressionEffects.selected_sound p ht hops hsel hcodes hsums he hw hh href)
          · rw [ite_eq_right hkeep] at hc; cases hc
    · rw [ite_eq_right hcond] at hc; cases hc
  · cases hc

/-- A call at a precondition the step's facts establish, whose selected
signature keeps the heap, keeps the heap (`requiresTree_sound`). -/
theorem requiresCall_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {kE : HeapKnowledge.Knowledge} {p : ProgramCertificates.Evidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : requiresCall G images j kE (.ordinary p) codes sums = true)
    (hkeep : (ExpressionEffects.selectedEffect p).any keepsHeap = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds kE ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) : KeepsPost G j ρ n W h := by
  simp only [requiresCall, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨rfl, hc⟩ := hc
  obtain ⟨eff, hsel, hs⟩ := requiresTree_sound hcodes hsums p hc
  simp only [hsel, Option.any_some] at hkeep
  exact post_with_type
    (fun _ _ _ _ _ hq => ⟨Footprints.Closed.holds_empty.mpr (keepsHeap_prefix hkeep
      (Footprints.intrinsicClasses_ok hh (ExpressionEffects.callEnv_rootsOk_of_refs href))
      (CallEffects.Effect.callPost_within hq)), trivial⟩)
    (hs he hk hw hh href)

/-- **A call the pass keeps the heap across (`keepsCall`)** has
its normal exit within `{values: keep, spines: keep}`: its selected signature
is within the empty footprint (`ExpressionEffects.selectedCall_sound`). -/
theorem keepsCall_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : keepsCall G images j e codes sums = true) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums) {ρ n W h} (he : EnvOk G j.context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type) (fun h' _ => Footprints.Closed.empty.Holds h h' ∧ True) n W h
      (instantiate 0 ρ j.term) := by
  unfold keepsCall at hc
  split at hc
  · rename_i p
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨rfl, hsel⟩, -⟩, ht⟩ := hc
    exact post_with_type (fun _ _ _ _ _ hq => ⟨hq, trivial⟩)
      (ExpressionEffects.selectedCall_sound p ht hsel hcodes hsums he hw hh href)
  · contradiction

/-- A call allocating its result (`freshCall`) has its normal
exit within `{values: keep, spines: keep}`: its selected signature keeps the
heap (`keepsHeap_prefix`). -/
theorem freshCall_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : freshCall G images j e codes sums = true) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums) {ρ n W h} (he : EnvOk G j.context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type) (fun h' _ => Footprints.Closed.empty.Holds h h' ∧ True) n W h
      (instantiate 0 ρ j.term) := by
  unfold freshCall at hc
  split at hc
  · rename_i p
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨rfl, hops⟩, hsel⟩, ht⟩ := hc
    split at hsel
    · rename_i eff heff
      simp only [Bool.and_eq_true] at hsel
      exact post_with_type
        (fun _ _ _ _ _ hq => ⟨Footprints.Closed.holds_empty.mpr (keepsHeap_prefix hsel.1
          (Footprints.intrinsicClasses_ok hh (ExpressionEffects.callEnv_rootsOk_of_refs href))
          (CallEffects.Effect.callPost_within hq)), trivial⟩)
        (ExpressionEffects.selected_sound p ht hops heff hcodes hsums he hw hh href)
    · cases hsel
  · contradiction

end Keeps

end
end Verification.PromiseCalls

namespace Verification.HeapExpressionRules
variable {ε : Verification.HeapKnowledge.EntryState}
open ProgramCertificates PositiveGraphs HeapObservations
open PositiveCertificates (InstanceImageCheck)

/-- A checker whose steps negating a Boolean slot restate the atoms
conditional on it with the opposite condition (`PromiseCalls.negationOf`);
every step is otherwise `base`'s. -/
@[nospecialize] def Checker.negatingSlots [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    match PromiseCalls.negationOf j with
    | some x => (base.run j k e codes sums).map fun out =>
        { out with
            elems := out.elems ++ PromiseCalls.negatedAtoms k x
            indices := out.indices ++ PromiseCalls.negatedIndices k x }
    | none => base.run j k e codes sums
  select := fun j k e codes sums =>
    match PromiseCalls.negationOf j with
    | some x => (base.select j k e codes sums).map fun out =>
        { out with
            elems := out.elems ++ PromiseCalls.negatedAtoms k x
            indices := out.indices ++ PromiseCalls.negatedIndices k x }
    | none => base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hρ
    split at hc
    · rename_i x hx
      simp only [CheckResult.map, Option.map_eq_some_iff] at hc
      obtain ⟨out0, hrun, rfl⟩ := hc
      have hs := base.sound hrun hcodes hsums he hk hw hh href hρ
      have hterm : (j.term = .ite (.var x) .fls .tru ∨ j.term = .ite (.test .truthy (.var x)) .fls .tru) ∧
          x < j.context.length := by
        unfold PromiseCalls.negationOf at hx
        split at hx
        · rename_i y hy
          split at hx
          · cases hx; exact ⟨.inl hy, by assumption⟩
          · cases hx
        · rename_i y hy
          split at hx
          · cases hx; exact ⟨.inr hy, by assumption⟩
          · cases hx
        · cases hx
      have hxv : isVal (ρ x) = true :=
        (ProgramTyping.meaning_value (he.2 x _ (List.getElem?_eq_getElem hterm.2))).1
      have finish : ∀ h' u, HeapKnowledge.Holds out0 ε (push u ρ) h' ∧ h' = h ∧
          ((tagHolds .truthy (ρ x) = true ∧ u = .fls) ∨ (tagHolds .truthy (ρ x) = false ∧ u = .tru)) →
          HeapKnowledge.Holds { out0 with
            elems := out0.elems ++ PromiseCalls.negatedAtoms k x
            indices := out0.indices ++ PromiseCalls.negatedIndices k x } ε (push u ρ) h' := by
        intro h' u hq
        obtain ⟨hq, rfl, hu⟩ := hq
        exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, fun a ha hc => by
          rcases List.mem_append.mp ha with ha | ha
          · exact hq.2.2.2.2.1 a ha hc
          · exact PromiseCalls.negatedAtoms_holds hk hu a ha hc, fun a ha hc => by
          rcases List.mem_append.mp ha with ha | ha
          · exact hq.2.2.2.2.2 a ha hc
          · exact PromiseCalls.negatedIndices_holds hk hu a ha hc⟩
      rcases hterm.1 with ht | ht
      · have hinst : instantiate 0 ρ j.term = .ite (ρ x) .fls .tru := by
          rw [ht]; simp [instantiate]
        rw [hinst] at hs ⊢
        exact HeapObservations.weaken (fun h' u hq =>
          finish h' u ⟨hq.1, hq.2.1, PromiseCalls.negation_bool hq.2.2⟩) (PromiseCalls.negation_run hxv hs)
      · have hinst : instantiate 0 ρ j.term = .ite (.test .truthy (ρ x)) .fls .tru := by
          rw [ht]; simp [instantiate]
        rw [hinst] at hs ⊢
        exact HeapObservations.weaken (fun h' u hq => finish h' u hq) (PromiseCalls.negation_test_run hxv hs)
    · exact base.sound hc hcodes hsums he hk hw hh href hρ

  normal := base.normal
  normal_sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hn
    split at hc
    · simp only [CheckResult.map, Option.map_eq_some_iff] at hc
      obtain ⟨out0, hrun, -⟩ := hc
      exact base.normal_sound hrun hcodes hsums he hk hw hh href hn
    · exact base.normal_sound hc hcodes hsums he hk hw hh href hn

/-- A checker whose ordinary steps that are calls keeping the heap keep every
heap fact of their entry (`PromiseCalls.keepsCall`); every other step is
`base`'s. -/
@[nospecialize] def Checker.keepingCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    if PromiseCalls.keepsCall G images j e codes sums then pure (HeapKnowledge.shift k) else base.run j k e codes sums
  select := fun j k e codes sums =>
    if PromiseCalls.keepsCall G images j e codes sums then pure (HeapKnowledge.shift k) else base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hρ
    split at hc
    · rename_i hkeep
      cases hc
      exact PromiseCalls.keepsCall_sound hkeep hcodes hsums he hk hw hh href
    · exact base.sound hc hcodes hsums he hk hw hh href hρ
  normal := fun j k e codes sums =>
    if PromiseCalls.keepsCall G images j e codes sums then .empty else base.normal j k e codes sums
  normal_sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hn
    split at hc
    · rename_i hkeep
      exact PromiseCalls.keepsCall_keeps hkeep hcodes hsums he hw hh href
    · rename_i hkeep
      rw [ite_eq_right hkeep] at hn
      exact base.normal_sound hc hcodes hsums he hk hw hh href hn

/-- A checker whose ordinary steps that are calls keeping the heap and
allocating their result keep every heap fact of their entry and separate the
result from the context's contract fields (`PromiseCalls.freshCall`); every
other step is `base`'s. -/
@[nospecialize] def Checker.allocatingCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    if PromiseCalls.freshCall G images j e codes sums then pure (PromiseCalls.freshOutput G j.context k)
    else base.run j k e codes sums
  select := fun j k e codes sums =>
    if PromiseCalls.freshCall G images j e codes sums then pure (PromiseCalls.freshOutput G j.context k)
    else base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hρ
    split at hc
    · rename_i hfresh
      cases hc
      exact PromiseCalls.freshCall_sound hfresh hcodes hsums he hk hw hh href
    · exact base.sound hc hcodes hsums he hk hw hh href hρ
  normal := fun j k e codes sums =>
    if PromiseCalls.freshCall G images j e codes sums then .empty else base.normal j k e codes sums
  normal_sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hn
    split at hc
    · rename_i hfresh
      exact PromiseCalls.freshCall_keeps hfresh hcodes hsums he hw hh href
    · rename_i hfresh
      rw [ite_eq_right hfresh] at hn
      exact base.normal_sound hc hcodes hsums he hk hw hh href hn

/-- A checker whose ordinary steps that are calls changing only their
receiver's own locations keep the heap facts separated from them
(`PromiseCalls.ownCall`); every other step is `base`'s. -/
@[nospecialize] def Checker.keepingOwnCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    match PromiseCalls.ownCall G images j e codes sums with
    | some i => pure (PromiseCalls.ownOutput k i)
    | none => base.run j k e codes sums
  select := fun j k e codes sums =>
    match PromiseCalls.ownCall G images j e codes sums with
    | some i => pure (PromiseCalls.ownOutput k i)
    | none => base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hρ
    split at hc
    · rename_i i hown
      cases hc
      exact PromiseCalls.ownCall_sound hown hcodes hsums he hk hw hh href
    · exact base.sound hc hcodes hsums he hk hw hh href hρ
  normal := fun j k e codes sums => match PromiseCalls.ownCall G images j e codes sums with
    | some _ => .top
    | none => base.normal j k e codes sums
  normal_sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hn
    split at hc
    · rename_i i hown
      simp only [hown] at hn
      exact absurd hn Footprints.Closed.top_ne_empty
    · rename_i hown
      simp only [hown] at hn
      exact base.normal_sound hc hcodes hsums he hk hw hh href hn

/-- A checker whose ordinary steps that are calls promising their receiver's
elements add that atom (`PromiseCalls.elementsCall`); every other step is
`base`'s. -/
@[nospecialize] def Checker.elementCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    match PromiseCalls.elementsCall G images j e codes sums with
    | some (x, R) => pure (PromiseCalls.elementsOutput k x R)
    | none => base.run j k e codes sums
  select := fun j k e codes sums =>
    match PromiseCalls.elementsCall G images j e codes sums with
    | some (x, R) => pure (PromiseCalls.elementsOutput k x R)
    | none => base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hρ
    split at hc
    · rename_i x R hel
      cases hc
      exact PromiseCalls.elementsCall_sound hel hcodes hsums he hk hw hh href
    · exact base.sound hc hcodes hsums he hk hw hh href hρ
  normal := fun j k e codes sums => match PromiseCalls.elementsCall G images j e codes sums with
    | some _ => .empty
    | none => base.normal j k e codes sums
  normal_sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hn
    split at hc
    · rename_i x R hel
      exact PromiseCalls.elementsCall_keeps hel hcodes hsums he hw hh href
    · rename_i hel
      simp only [hel] at hn
      exact base.normal_sound hc hcodes hsums he hk hw hh href hn

/-- A checker whose ordinary steps that are calls at a precondition on their
receiver's elements are checked against the entry's atoms
(`PromiseCalls.requiresCall`); every other step is `base`'s. -/
@[nospecialize] def Checker.requiringCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    if PromiseCalls.requiresCall G images j k e codes sums then pure (PromiseCalls.requiresOutput G e k)
    else base.run j k e codes sums
  select := fun j k e codes sums =>
    if PromiseCalls.requiresCall G images j k e codes sums then pure (PromiseCalls.requiresOutput G e k)
    else base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hρ
    split at hc
    · rename_i hreq
      cases hc
      exact PromiseCalls.requiresCall_sound hreq hcodes hsums he hk hw hh href
    · exact base.sound hc hcodes hsums he hk hw hh href hρ
  normal := fun j k e codes sums =>
    if PromiseCalls.requiresCall G images j k e codes sums then
      (match e with
        | .ordinary p => if (ExpressionEffects.selectedEffect p).any PromiseCalls.keepsHeap then .empty else .top
        | _ => .top)
    else base.normal j k e codes sums
  normal_sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hn
    split at hc
    · rename_i hreq
      rw [ite_eq_left hreq] at hn
      cases e with
      | ordinary p =>
        dsimp only at hn
        split at hn
        · rename_i hkeep
          exact PromiseCalls.requiresCall_keeps hreq hkeep hcodes hsums he hk hw hh href
        · exact absurd hn Footprints.Closed.top_ne_empty
      | _ => exact absurd hn Footprints.Closed.top_ne_empty
    · rename_i hreq
      rw [ite_eq_right hreq] at hn
      exact base.normal_sound hc hcodes hsums he hk hw hh href hn

/-- A checker whose ordinary steps that are calls stating a postcondition add
their atoms to what `base` gives the step (`PromiseCalls.ensuresCall`); every
other step is `base`'s. -/
@[nospecialize] def Checker.ensuringCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    match PromiseCalls.ensuresCall G images j k e codes sums with
    | some eff => (base.run j k e codes sums).map fun out => PromiseCalls.withGrown eff
        (PromiseCalls.withEnsures (HeapExpressionRules.stableFirst G j.context) G j.context eff j.term k out) (IndexWrites.grownRegions G j.context k j.term)
    | none => base.run j k e codes sums
  select := fun j k e codes sums =>
    match PromiseCalls.ensuresCall G images j k e codes sums with
    | some eff => (base.select j k e codes sums).map fun out => PromiseCalls.withGrown eff
        (PromiseCalls.withEnsures (HeapExpressionRules.stableFirst G j.context) G j.context eff j.term k out) (IndexWrites.grownRegions G j.context k j.term)
    | none => base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hρ
    split at hc
    · rename_i eff hens
      simp only [CheckResult.map, Option.map_eq_some_iff] at hc
      obtain ⟨out0, hrun, rfl⟩ := hc
      have hs := base.sound hrun hcodes hsums he hk hw hh href hρ
      by_cases hn : n ≤ 3
      · exact PromiseCalls.call_safePost_le_three hn
          (PromiseCalls.isCallTerm_instantiate 0 ρ (PromiseCalls.ensuresCall_isCallTerm hens)) hs
      · obtain ⟨nw, rfl⟩ : ∃ nw, n = nw + 4 := ⟨n - 4, by omega⟩
        have hp := PromiseCalls.ensuresCall_sound hens hcodes hsums he hk hw hh href
        exact HeapObservations.weaken (fun h' v hq' => let hq := hq'.1; PromiseCalls.withGrown_holds
          (PromiseCalls.withEnsures_holds (fun i hi => (ProgramTyping.meaning_value (he.2 i _ (List.getElem?_eq_getElem hi))).1) hq.1 he hk
            hh hρ (Footprints.intrinsicClasses_ok hh (ExpressionEffects.callEnv_rootsOk_of_refs href)) hq.2 hq'.2)
          (fun hgr => IndexWrites.grownRegions_holds he hh hk hρ (PromiseCalls.withGrown_grows hgr hq.2)
            (PromiseCalls.withGrown_appends hgr hq.2)))
          (HeapExpressionRules.stableFirst_frame he hw hh
            (HeapObservations.cross_upto (nw + 4) (fun _ _ _ _ _ _ _ _ hb _ => hb) W W h _ hh hh hs hp))
    · exact base.sound hc hcodes hsums he hk hw hh href hρ
  normal := base.normal
  normal_sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hn
    split at hc
    · simp only [CheckResult.map, Option.map_eq_some_iff] at hc
      obtain ⟨out0, hrun, -⟩ := hc
      exact base.normal_sound hrun hcodes hsums he hk hw hh href hn
    · exact base.normal_sound hc hcodes hsums he hk hw hh href hn

/-- **A qualified body's checker**: its descriptor-aware steps
(`Checker.subtypingSteps`) under the call layers of `Checker.ordinary`, so a
call states the same normal effect in a qualified body as in an ordinary one,
each step keeping its input's stable links. -/
@[nospecialize] def Checker.withSubtyping [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (subtyping : ProgramTyping.BodySubtyping G)
    (ordinary : ∀ {A B p}, PositiveCertificates.checkUsing G images A B p = true → subtyping.check A B p = true) :
    Checker G images :=
  (Checker.subtypingSteps G images subtyping ordinary).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls
    |>.elementCalls.keepingStable

/-- The steps' rules, a call keeping the heap keeping every heap fact, a call
allocating its result separating it, a call changing only its receiver's own
locations keeping the facts separated from them, a call stating a postcondition
adding their atoms, the index atoms a step states and the write at a checked
index (`IndexWrites`), each keeping its input's stable links. -/
@[nospecialize] def Checker.ordinary [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) : Checker G images :=
  (Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls
    |>.negatingSlots.indexing.boundedWrites.keepingStable

end Verification.HeapExpressionRules
