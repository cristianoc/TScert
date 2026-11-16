import Verification.Programs.IndexWrites
import Verification.Semantics.ParityDerivations

/-! # The pass's arithmetic atoms read as parity conclusions

Interpretation lemmas for the migration of the pass's arithmetic producers
(`IndexWrites.linearAtoms`) to the parity derivation rules
(`ParityDerivations`): each list of atoms a producer emits on a step's
result holds exactly where the conclusion of the corresponding rule holds,
the result at slot `0` of the exit valuation and an input slot `x` at slot
`x + 1`. A producer's operand form `F + c` over input slots is the rule's
form `slotForm F` over the exit's terms.

- `valueAtoms` (a sum, a difference, a product with a constant factor) is
  `integerOperation`'s `valueFacts`.
- `bitAtoms .shr` and `bitAtoms .bitAnd` are `shiftRight`'s and `mask`'s
  facts.
- `concatAtoms` is `stringConcat`'s facts.
- `pastSafeAtoms` (the sum at a string length plus one) is
  `lengthSuccessor`'s guarded conclusion.
- The length read of a string is `stringLengthRead`'s facts.

And the exact postconditions of writes hold of the calculus's runs: a normal
run of an element write below its spine's length meets `lengthsKept`
(`ExpressionEffects.elem_var_write_length`, the note's Write-In), and one of
a checked write meets `boundedWrite` (`IndexWrites.boundedWrite_spine`,
Write-End's length). -/
namespace Verification.Parity.Bridges
open Verification HeapKnowledge IndexWrites

variable {ε : EntryState}

/-- An operand form over input slots, over the exit's terms. -/
def slotForm (F : Linear.Form Nat) : Linear.Form Term := valueForm (shiftForm F)

theorem slotForm_scale (F : Linear.Form Nat) (k : Int) : slotForm (F.scale k) = (slotForm F).scale k := by
  simp [slotForm, valueForm, shiftForm, Linear.Form.scale, Function.comp_def]

theorem slotForm_append (F G : Linear.Form Nat) : slotForm (F ++ G) = slotForm F ++ slotForm G := by
  simp [slotForm, valueForm, shiftForm]

/-- An index atom list without conditions holds where each fact does. -/
theorem indexHolds_uncond {as : List IndexAtom} (hc : ∀ a ∈ as, a.cond = none) {η : Env} {h : Heap} :
    IndexHolds ε as η h ↔ ∀ a ∈ as, a.fact.HoldsAt ε η h := by
  constructor
  · intro hh a ha; exact hh a ha fun b hb => by rw [hc a ha] at hb; cases hb
  · intro hh a ha _; exact hh a ha

/-- A linear index fact over current terms is the fact at the terms' values. -/
theorem linear_holdsAt_iff {G : Linear.Fact Term} (hG : ∀ t ∈ G.vars, t.atEntry = false) {η : Env} {h : Heap} :
    (IndexFact.linear G).HoldsAt ε η h ↔ FactAt (termAt η h) G := by
  have hv : ∀ t ∈ G.vars, termValue ε η h t = termAt η h t := fun t ht => termValue_now (hG t ht)
  simp only [IndexFact.HoldsAt, FactAt]
  constructor
  · rintro ⟨hd, hh⟩
    refine ⟨fun t ht => by rw [← hv t ht]; exact hd t ht, (Linear.Fact.holds_congr fun t ht => ?_).mp hh⟩
    simp only [termValuation, hv t ht]
  · rintro ⟨hd, hh⟩
    refine ⟨fun t ht => by rw [hv t ht]; exact hd t ht, (Linear.Fact.holds_congr fun t ht => ?_).mp hh⟩
    simp only [termValuation, hv t ht]

/-- The value facts of `valueFact`: every term reads the current state. -/
theorem valueFact_current (G : Linear.Fact Nat) : ∀ t ∈ (valueFact G).vars, t.atEntry = false := by
  intro t ht
  rw [vars_valueFact] at ht
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp ht
  rfl

variable {arena : AssertionArena} {s : TwoState} {u : Val} {ρ : Env}

theorem int_iff (hs : s.afterEnv = push u ρ) :
    (IndexFact.int 0).HoldsAt ε (push u ρ) s.after.h ↔ Holds arena s (safeFact (.var 0)) := by
  show (intValue (push u ρ 0)).isSome ↔ (termAt s.afterEnv s.after.h (Term.now .value 0 [])).isSome
  rw [hs]; rfl

theorem linear_iff (hs : s.afterEnv = push u ρ) (G : Linear.Fact Nat) :
    (IndexFact.linear (valueFact G)).HoldsAt ε (push u ρ) s.after.h ↔ Holds arena s (lin (valueFact G)) := by
  rw [linear_holdsAt_iff (valueFact_current G), holds_lin, hs]

private theorem valueFact_le (F : Linear.Form Nat) (d : Int) : valueFact (.le F d) = .le (valueForm F) d := rfl

/-- **`valueAtoms` is `integerOperation`'s conclusion.** -/
theorem valueAtoms_iff (hs : s.afterEnv = push u ρ) (F : Linear.Form Nat) (c : Int) :
    IndexHolds ε (valueAtoms F c) (push u ρ) s.after.h ↔ Holds arena s (valueFacts (.var 0) (slotForm F) c) := by
  rw [indexHolds_uncond (by simp [valueAtoms])]
  simp only [valueAtoms, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [int_iff hs, linear_iff hs, linear_iff hs]
  simp only [valueFacts, exactTermFacts, conj, Holds, and_true, valueFact_le, valueForm, List.map_cons,
    ← slotForm_scale]
  rfl

/-- **`bitAtoms .shr` is `shiftRight`'s conclusion.** -/
theorem shrAtoms_iff (hs : s.afterEnv = push u ρ) (F : Linear.Form Nat) (c d : Int) :
    IndexHolds ε (bitAtoms .shr F c d) (push u ρ) s.after.h ↔ Holds arena s (shrFacts (.var 0) (slotForm F) c d) := by
  rw [indexHolds_uncond (by simp [bitAtoms])]
  simp only [bitAtoms, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [int_iff hs, linear_iff hs, linear_iff hs, linear_iff hs]
  simp only [shrFacts, conj, Holds, and_true, valueFact_le, valueForm, List.map_cons, ← slotForm_scale]
  rfl

/-- **`bitAtoms .bitAnd` is `mask`'s conclusion.** -/
theorem maskAtoms_iff (hs : s.afterEnv = push u ρ) (F : Linear.Form Nat) (c d : Int) :
    IndexHolds ε (bitAtoms .bitAnd F c d) (push u ρ) s.after.h ↔ Holds arena s (maskFacts (.var 0) (slotForm F) c d) := by
  rw [indexHolds_uncond (by simp [bitAtoms])]
  simp only [bitAtoms, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [int_iff hs, linear_iff hs, linear_iff hs, linear_iff hs]
  simp only [maskFacts, conj, Holds, and_true, valueFact_le, valueForm, List.map_cons, ← slotForm_scale]
  rfl

/-- **`concatAtoms` is `stringConcat`'s conclusion.** -/
theorem concatAtoms_iff (hs : s.afterEnv = push u ρ) (a b : Nat) :
    IndexHolds ε (concatAtoms a b) (push u ρ) s.after.h ↔ Holds arena s (concatFacts (.var (a + 1)) (.var (b + 1)) (.var 0)) := by
  rw [indexHolds_uncond (by simp [concatAtoms])]
  simp only [concatAtoms, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [linear_holdsAt_iff (by simp [Linear.Fact.vars, Term.strLength]),
    linear_holdsAt_iff (by simp [Linear.Fact.vars, Term.strLength])]
  simp only [concatFacts, conj, Holds, and_true]
  rw [← hs]
  exact and_congr (factAt_tag s .after _).symm (factAt_tag s .after _).symm

/-- **A string's length read** (the pass's atoms on `lenOf` of a string
slot `x`) is `stringLengthRead`'s conclusion. -/
theorem lengthReadAtoms_iff (hs : s.afterEnv = push u ρ) (x : Nat) :
    IndexHolds ε [⟨.int 0, none, false⟩, ⟨.linear (.le [(.value 0, 1), (.strLength (x + 1), -1)] 0), none, false⟩,
        ⟨.linear (.le [(.value 0, -1), (.strLength (x + 1), 1)] 0), none, false⟩] (push u ρ) s.after.h ↔
      Holds arena s (lengthReadFacts (.var (x + 1)) (.var 0)) := by
  rw [indexHolds_uncond (by simp)]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [int_iff hs, linear_holdsAt_iff (by simp [Linear.Fact.vars, Term.strLength, Term.value]),
    linear_holdsAt_iff (by simp [Linear.Fact.vars, Term.strLength, Term.value])]
  simp only [lengthReadFacts, conj, Holds, and_true]
  rw [← hs]
  exact and_congr Iff.rfl (and_congr (factAt_tag s .after _).symm (factAt_tag s .after _).symm)

/-- **`pastSafeAtoms` is `lengthSuccessor`'s guarded conclusion**: each of
the producer's alternatives `fact ∨ pastSafe(result)` holds exactly where
`pastSafe(y) ∨ (safeInt(y) ∧ y = F + c)` does. -/
theorem pastSafeAtoms_iff (hv : arena.Valid) (hs : s.afterEnv = push u ρ) (F : Linear.Form Nat) (c : Int)
    {g pg e e₀ e' e₁ e₂ : AssertionRef}
    (hg : arena.nodes[g.index]? = some (.guarded pg e)) (hpg : arena.nodes[pg.index]? = some (.atom (.pastSafe (.var 0))))
    (he : arena.nodes[e.index]? = some (.and e₀ e')) (he₀ : arena.nodes[e₀.index]? = some (.atom (.safeInt (.var 0))))
    (he' : arena.nodes[e'.index]? = some (.and e₁ e₂))
    (he₁ : arena.nodes[e₁.index]? = some (.atom (.linear (exactTermFacts (.var 0) (slotForm F) c).1)))
    (he₂ : arena.nodes[e₂.index]? = some (.atom (.linear (exactTermFacts (.var 0) (slotForm F) c).2))) :
    IndexHolds ε (pastSafeAtoms F c) (push u ρ) s.after.h ↔ Holds arena s (.at .after g) := by
  rw [indexHolds_uncond (by simp [pastSafeAtoms, valueAtoms])]
  simp only [pastSafeAtoms, valueAtoms, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IndexFact.HoldsAt]
  have hps : (push u ρ 0 = .num SafeIntegers.pastSafeBits) ↔
      Sat arena s.afterEnv s.mark s.after pg := by
    rw [sat_atom hpg, hs]; simp [Atom.Holds, Path.read, Path.var, readPath]
  have hint : (intValue (push u ρ 0)).isSome ↔ Sat arena s.afterEnv s.mark s.after e₀ := by
    rw [sat_atom he₀, hs]; simp [Atom.Holds, Path.read, Path.var, readPath]
  have hrest : (IndexFact.linear (valueFact (.le ((0, 1) :: shiftForm (F.scale (-1))) c))).HoldsAt ε (push u ρ) s.after.h ∧
      (IndexFact.linear (valueFact (.le ((0, -1) :: shiftForm F) (-c)))).HoldsAt ε (push u ρ) s.after.h ↔
      Sat arena s.afterEnv s.mark s.after e' := by
    rw [sat_and hv he', sat_atom he₁, sat_atom he₂, linear_iff (arena := arena) hs, linear_iff (arena := arena) hs,
      holds_lin, holds_lin]
    simp only [valueFact_le, valueForm, List.map_cons, exactTermFacts, ← slotForm_scale]
    rfl
  change _ ↔ Sat arena s.afterEnv s.mark s.after g
  rw [sat_guarded hv hg, sat_and hv he, ← hps, ← hint, ← hrest]
  show ((intValue (push u ρ 0)).isSome ∨ _) ∧ _ ↔ _
  constructor
  · rintro ⟨h0, h1, h2⟩
    by_cases hp : push u ρ 0 = .num SafeIntegers.pastSafeBits
    · exact .inl hp
    · exact .inr ⟨h0.resolve_right hp, h1.resolve_right hp, h2.resolve_right hp⟩
  · rintro (hp | ⟨h0, h1, h2⟩)
    · exact ⟨.inr hp, .inr hp, .inr hp⟩
    · exact ⟨.inl h0, .inl h1, .inl h2⟩

/-! ## The exact postconditions of writes, of the calculus's runs -/

open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower HeapObservations ProgramCertificates

open TolerantFrames in
/-- A normal run of a term whose safety carries a postcondition ends, with
budget left, in an admissible state meeting it (`TolerantFrames.run_normal`). -/
theorem post_of_run {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {s : IndexedHeap} {t v : Tm} {h' : Heap} {k : Nat}
    (hsafe : SafePostExc Ξ T Q R s.n s.W s.h t) (hst : Steps k s.h t h' v) (hv : isVal v = true) (hk : k < s.n) :
    ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ Q h' v :=
  let ⟨s', ha, he, _, _, hq⟩ := run_normal hsafe hst hv hk
  ⟨s', ha, he, hq⟩

open TolerantFrames ExpressionEffects in
/-- **Write-In's post of the calculus's run**: a normal run of an element
write below its spine's length ends where `lengthsKept` holds. -/
theorem lengthsKept_of_run {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)}
    {i j k : Nat} {Ref : Ty ι} {Ξ T : Fam} {ρ : Env} {s : IndexedHeap} {flds : List (PropKey × Nat)}
    {cd : CallCode} {oid fl : Nat} {ls0 : List (Option Nat)} {b0 : UInt64} {idx : Nat}
    (hk : k < Γ.length) (hj : j < Γ.length) (hi : Γ[i]? = some Ref)
    (hst : spineFieldEvery G (expand G Ref) arraySpineKey = true)
    (hoi : ρ i = .objAt flds cd oid) (hfl : flds.lookup arraySpineKey = some fl) (hls0 : s.h[fl]? = some (.arr ls0))
    (hb0 : ρ j = .num b0) (hidx : indexOfBits b0 = some idx) (hlt : idx < ls0.length)
    (he : EnvOk G Γ ρ s.n s.W)
    (hs : Safe Ξ T s.n s.W s.h (instantiate 0 ρ (.writeAt arraySpineKey (.var i) (.setElem (.readAt arraySpineKey (.var i)) (.var j) (.var k)))))
    {steps : Nat} {h' : Heap} {v : Tm}
    (hrun : Steps steps s.h (instantiate 0 ρ (.writeAt arraySpineKey (.var i) (.setElem (.readAt arraySpineKey (.var i)) (.var j) (.var k)))) h' v)
    (hv : isVal v = true) (hb : steps < s.n) {x x' : Nat} {η η' : Env} {m : Nat} (hη : η' x' = η x) :
    ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ (OperationPostF.lengthsKept x x').Holds ⟨η, η', m, s, s'⟩ := by
  obtain ⟨s', ha, hh, hq⟩ :=
    post_of_run (elem_var_write_length hk hj hi hst hoi hfl hls0 hb0 hidx hlt he s.ok hs) hrun hv hb
  exact ⟨s', ha, hh, by subst hh; exact hq, hη⟩

open TolerantFrames in
/-- **Write-End's post of the calculus's run**: a normal run of a checked
write ends where `boundedWrite` holds, at the write's own valuation. -/
theorem boundedWrite_of_run {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : PositiveCertificates.InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) {ρ : Env} {s : IndexedHeap}
    (he : EnvOk G j.context ρ s.n s.W) (hk : HeapKnowledge.Holds k ε ρ s.h)
    (href : RefsOk s.W (instantiate 0 ρ j.term))
    {steps : Nat} {h' : Heap} {u : Tm} (hrun : Steps steps s.h (instantiate 0 ρ j.term) h' u)
    (hu : isVal u = true) (hb : steps < s.n) {x' : Nat} {η' : Env} {m : Nat} (hη : η' x' = ρ a) :
    ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ (OperationPostF.boundedWrite a i x').Holds ⟨ρ, η', m, s, s'⟩ := by
  obtain ⟨s', ha, hh, hq⟩ := post_of_run (SafePostExc.of_post (R := fun _ => True) (fun _ => trivial)
    (boundedWrite_spine hc he hk s.adm s.ok href)) hrun hu hb
  exact ⟨s', ha, hh, by subst hh; exact hq, hη⟩

end Verification.Parity.Bridges
