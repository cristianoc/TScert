import Verification.Semantics.ExitPosts

/-! # The conjunction of two specifications per exit

Two specifications of one call conjoin exit by exit (the note *Tolerant
frames*, §6, rule Conj, at one call): at an instantiated specification the
conjunction keeps the first frame, and the second as the postcondition
`.transition` beside the postconditions of both (`ExitSpec.meet`,
`ExitSpec.holds_meet`). At a call the two schemas are instantiated at its
arity and conjoined there (`meetAt`, `meetAt_exitPost`); both endpoints are
the call's, so no condition on worlds is needed.

A schema is instantiated at an entry scope wide enough for its transports
(`Exits.callInstantiation`). A transport whose default image is the next
exit slot (`TransportSchema.shift = 1`) states, beyond its replacements,
that an entry position is the exit position one higher, which every call's
two-state interpretation satisfies (`callState`). Instantiated at a wider
scope such a schema means the same (`instantiate_completion`), so two
schemas with only such transports conjoin as one schema (`Exits.meet`,
`Exits.exitPost_meet`). For other transports the conjunction is taken at
the call (`meetAt`). -/
namespace Verification.CallEffects
open Verification Footprints Parity TolerantFrames

/-! ## Conjunction at a call -/

/-- **The conjunction of two exit specifications**: the first's frame, its
postconditions, the second's frame as a transition, and the second's
postconditions. -/
def ExitSpec.meet (a b : ExitSpec) : ExitSpec :=
  ⟨a.frame, a.ensures ++ (.transition b.frame :: b.ensures)⟩

/-- **The conjunction holds where both specifications hold.** -/
theorem ExitSpec.holds_meet (a b : ExitSpec) (arena : AssertionArena) (s : TwoState) :
    (a.meet b).Holds arena s ↔ a.Holds arena s ∧ b.Holds arena s := by
  simp only [ExitSpec.Holds, ExitSpec.meet, List.mem_append, List.mem_cons]
  constructor
  · rintro ⟨hf, he⟩
    exact ⟨⟨hf, fun F hF => he F (.inl hF)⟩, ⟨he _ (.inr (.inl rfl)), fun F hF => he F (.inr (.inr hF))⟩⟩
  · rintro ⟨⟨hf, ha⟩, hb, hbe⟩
    refine ⟨hf, fun F hF => ?_⟩
    rcases hF with hF | rfl | hF
    · exact ha F hF
    · exact hb
    · exact hbe F hF

/-- **Two schemas conjoined at a call of `n` actuals**, each instantiated at
its own entry scope. -/
def meetAt (x y : Exits ExitSchema) (n : Nat) : Exits ExitSpec :=
  ⟨(x.atArity n).normal.meet (y.atArity n).normal, (x.atArity n).exceptional.meet (y.atArity n).exceptional⟩

/-- **The conjunction at a call is both guarantees**, on either exit. -/
theorem meetAt_exitPost (x y : Exits ExitSchema) (c : Completion) (r : Tm) (args : List Tm)
    (s s' : IndexedHeap) (v : Tm) :
    ((meetAt x y args.length).get c).Holds AssertionArena.empty (callState r args v s.h.length s s') ↔
      x.exitPost c r args s s' v ∧ y.exitPost c r args s s' v := by
  cases c <;> exact ExitSpec.holds_meet _ _ _ _

/-! ## Completion of a schema's entry scope -/

/-- Whether every transport of a formula has the next exit slot as its
default image. -/
def _root_.Verification.Parity.FormulaF.canonical {S : Type} : FormulaF S TransportSchema → Bool
  | .transport t => t.shift == 1
  | .and F G => F.canonical && G.canonical
  | _ => true

/-- Whether every transport of an exit schema has the next exit slot as its
default image. -/
def ExitSchema.canonicalTransports (q : ExitSchema) : Bool := q.ensures.all (·.canonical)

/-- **Whether every transport of both exits has the next exit slot as its
default image**: the schemas whose entry scope widens without changing their
meaning (`instantiate_completion`). -/
def Exits.canonicalTransports (x : Exits ExitSchema) : Bool :=
  x.normal.canonicalTransports && x.exceptional.canonicalTransports

/-- A two-state interpretation reading entry position `i` at exit position
`i + 1`: a call's. -/
def _root_.Verification.Parity.TwoState.Shifted (s : TwoState) : Prop := ∀ i, s.afterEnv (i + 1) = s.beforeEnv i

theorem callState_shifted (r : Tm) (args : List Tm) (v : Tm) (m : Nat) (s s' : IndexedHeap) :
    (callState r args v m s s').Shifted := fun _ => rfl

private theorem lookup_lt_foldr {l : List (Nat × Witness)} {i : Nat} {w : Witness} (h : l.lookup i = some w) :
    i < l.foldr (fun p k => max (p.1 + 1) k) 0 := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    simp only [List.foldr_cons]
    by_cases hp : i = p.1
    · omega
    · have hne : (i == p.1) = false := by simp [hp]
      simp only [List.lookup, hne] at h
      have := ih h
      omega

theorem TransportSchema.lookup_lt {t : TransportSchema} {i : Nat} {w : Witness} (h : t.overrides.lookup i = some w) :
    i < t.slots :=
  lookup_lt_foldr h

theorem TransportSchema.images_getElem (t : TransportSchema) (N i : Nat) :
    (t.instantiate N).images[i]? = if i < N then some (match t.overrides.lookup i with
      | some w => w
      | none => .path ⟨i + t.shift, []⟩) else none := by
  simp only [TransportSchema.instantiate, List.getElem?_toArray, List.getElem?_map]
  by_cases hi : i < N
  · rw [List.getElem?_range hi, if_pos hi]; rfl
  · rw [List.getElem?_eq_none (by simpa using hi), if_neg hi]; rfl

private theorem holds_widen {t : TransportSchema} (ht : t.shift = 1) {N N' : Nat} (hs : t.slots ≤ N) (hN : N ≤ N')
    {target source : Env} (hsh : ∀ i, source (i + 1) = target i) (boxed : Bool) (h : Heap) :
    ({ t.instantiate N' with boxed := boxed } : Substitution).Holds target source h ↔
      ({ t.instantiate N with boxed := boxed } : Substitution).Holds target source h := by
  have hwiden : ∀ i, i < N → ({ t.instantiate N' with boxed := boxed } : Substitution).image i =
      ({ t.instantiate N with boxed := boxed } : Substitution).image i := by
    intro i hi
    unfold Substitution.image
    simp only
    rw [TransportSchema.images_getElem, TransportSchema.images_getElem, if_pos hi, if_pos (by omega)]
    rfl
  constructor
  · intro hθ i w hw
    have hi : i < N := by
      unfold Substitution.image at hw
      simp only at hw
      rw [TransportSchema.images_getElem] at hw
      by_cases hi : i < N
      · exact hi
      · rw [if_neg hi] at hw; cases hw
    exact hθ i w (by rw [hwiden i hi]; exact hw)
  · intro hθ i w hw
    by_cases hi : i < N
    · exact hθ i w (by rw [← hwiden i hi]; exact hw)
    · have hiN' : i < N' := by
        unfold Substitution.image at hw
        simp only at hw
        rw [TransportSchema.images_getElem] at hw
        by_cases hi' : i < N'
        · exact hi'
        · rw [if_neg hi'] at hw; cases hw
      unfold Substitution.image at hw
      simp only at hw
      rw [TransportSchema.images_getElem, if_pos hiN'] at hw
      have hl : t.overrides.lookup i = none := by
        cases hl : t.overrides.lookup i with
        | none => rfl
        | some w => exact absurd (TransportSchema.lookup_lt hl) (by omega)
      simp only [hl, ht] at hw
      split at hw
      · cases hw
      · cases hw
        show Path.read source h ⟨i + 1, []⟩ = some (target i)
        rw [Path.read_nil rfl, hsh]

/-- **A canonical transport means the same at a wider entry scope**, at a
two-state interpretation reading each entry position at the next exit
position. -/
theorem TransportSchema.holdsAt_widen {t : TransportSchema} (ht : t.shift = 1) {N N' : Nat} (hs : t.slots ≤ N)
    (hN : N ≤ N') {s : TwoState} (hsh : s.Shifted) :
    (t.instantiate N').HoldsAt s.beforeEnv s.afterEnv s.after ↔ (t.instantiate N).HoldsAt s.beforeEnv s.afterEnv s.after := by
  have hsh' : ∀ i, s.afterEnv (i + 1) = s.beforeEnv i := hsh
  unfold Substitution.HoldsAt Substitution.box
  have h1 := holds_widen ht hs hN hsh' (t.instantiate N').boxed
  have h2 := holds_widen ht hs hN hsh' true
  exact and_congr (h1 s.after.h) (forall_congr' fun s' => imp_congr_right fun _ => h2 s'.h)

/-- The entry scope a formula is instantiated at. -/
private def instAt (n N : Nat) (F : FormulaSchema) : Formula :=
  F.map (WitnessSeq.instantiate n) (TransportSchema.instantiate · N)

private theorem formula_widen {F : FormulaSchema} (hc : F.canonical = true) {n N N' : Nat} (hs : F.slots ≤ N)
    (hN : N ≤ N') (arena : AssertionArena) {s : TwoState} (hsh : s.Shifted) :
    Holds arena s (instAt n N' F) ↔ Holds arena s (instAt n N F) := by
  induction F with
  | transport t =>
    simp only [FormulaF.canonical, beq_iff_eq] at hc
    exact TransportSchema.holdsAt_widen hc hs hN hsh
  | and F G ihF ihG =>
    simp only [FormulaF.canonical, Bool.and_eq_true] at hc
    simp only [FormulaF.slots, Nat.max_le] at hs
    exact and_congr (ihF hc.1 hs.1) (ihG hc.2 hs.2)
  | _ => exact Iff.rfl

private theorem slots_le_of_mem_list {l : List FormulaSchema} {F : FormulaSchema} (hF : F ∈ l) :
    F.slots ≤ l.foldr (fun F k => max F.slots k) 0 := by
  induction l with
  | nil => cases hF
  | cons G l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hF with rfl | hF
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hF) (Nat.le_max_right _ _)

private theorem slots_le_of_mem {q : ExitSchema} {F : FormulaSchema} (hF : F ∈ q.ensures) : F.slots ≤ q.slots :=
  slots_le_of_mem_list hF

/-- **A canonical exit schema means the same at a wider entry scope.** -/
theorem ExitSchema.holds_widen {q : ExitSchema} (hq : q.canonicalTransports = true) {ι ι' : CallInstantiation}
    (hn : ι'.actualCount = ι.actualCount) (hs : q.slots ≤ ι.entrySlots) (hN : ι.entrySlots ≤ ι'.entrySlots)
    (arena : AssertionArena) {s : TwoState} (hsh : s.Shifted) :
    (q.instantiate ι').Holds arena s ↔ (q.instantiate ι).Holds arena s := by
  simp only [ExitSpec.Holds, ExitSchema.instantiate, List.forall_mem_map]
  refine and_congr Iff.rfl (forall_congr' fun F => imp_congr_right fun hF => ?_)
  have hc : F.canonical = true := List.all_eq_true.mp hq F hF
  have := formula_widen hc (n := ι.actualCount) (Nat.le_trans (slots_le_of_mem hF) hs) hN arena hsh
  unfold instAt at this
  unfold instantiateFormula
  rw [hn]
  exact this

theorem Exits.canonicalTransports_get {x : Exits ExitSchema} (hx : x.canonicalTransports = true) (c : Completion) :
    (x.get c).canonicalTransports = true := by
  simp only [Exits.canonicalTransports, Bool.and_eq_true] at hx
  cases c
  · exact hx.1
  · exact hx.2

theorem Exits.slots_get (x : Exits ExitSchema) (c : Completion) : (x.get c).slots ≤ x.slots := by
  cases c
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

/-- **Scope completion** (the note's Call, a transport over every entry
slot): a schema whose transports are canonical, instantiated at a call's
arity and any entry scope containing its own, states what it states at its
own scope. -/
theorem instantiate_completion {x : Exits ExitSchema} (hx : x.canonicalTransports = true) {c : Completion}
    {r : Tm} {args : List Tm} {v : Tm} {m : Nat} {s s' : IndexedHeap} {N : Nat}
    (hN : max (args.length + 1) x.slots ≤ N) :
    ((x.get c).instantiate ⟨args.length, N, Nat.le_trans (Nat.le_max_left _ _) hN⟩).Holds AssertionArena.empty
        (callState r args v m s s') ↔
      ((x.atArity args.length).get c).Holds AssertionArena.empty (callState r args v m s s') := by
  rw [Exits.atArity, Exits.get_map]
  exact ExitSchema.holds_widen (ι := x.callInstantiation args.length)
    (ι' := ⟨args.length, N, Nat.le_trans (Nat.le_max_left _ _) hN⟩) (Exits.canonicalTransports_get hx c) rfl
    (Nat.le_trans (Exits.slots_get x c) (Nat.le_max_right _ _)) hN _ (callState_shifted r args v m s s')

/-! ## Conjunction of schemas -/

/-- **The conjunction of two exit schemas.** -/
def ExitSchema.meet (a b : ExitSchema) : ExitSchema :=
  ⟨a.frame, a.ensures ++ (.transition b.frame :: b.ensures)⟩

theorem ExitSchema.instantiate_meet (a b : ExitSchema) (ι : CallInstantiation) :
    (a.meet b).instantiate ι = (a.instantiate ι).meet (b.instantiate ι) := by
  simp only [ExitSchema.meet, ExitSchema.instantiate, ExitSpec.meet, List.map_append, List.map_cons]
  rfl

private theorem foldr_slots_append (a b : List FormulaSchema) :
    (a ++ b).foldr (fun (F : FormulaSchema) k => max F.slots k) 0 =
      max (a.foldr (fun (F : FormulaSchema) k => max F.slots k) 0) (b.foldr (fun (F : FormulaSchema) k => max F.slots k) 0) := by
  induction a with
  | nil => simp
  | cons F t ih => simp only [List.cons_append, List.foldr_cons, ih, Nat.max_assoc]

theorem ExitSchema.slots_meet (a b : ExitSchema) : (a.meet b).slots = max a.slots b.slots := by
  simp only [ExitSchema.slots, ExitSchema.meet, foldr_slots_append, List.foldr_cons]
  show max _ (max 0 _) = _
  rw [Nat.zero_max]

theorem ExitSchema.canonical_meet {a b : ExitSchema} (ha : a.canonicalTransports = true)
    (hb : b.canonicalTransports = true) : (a.meet b).canonicalTransports = true := by
  simp only [ExitSchema.canonicalTransports] at ha hb
  simp only [ExitSchema.canonicalTransports, ExitSchema.meet, List.all_append, List.all_cons, ha, hb]
  rfl

/-- **The conjunction of two signatures' schemas**, exit by exit. -/
def Exits.meet (x y : Exits ExitSchema) : Exits ExitSchema :=
  ⟨x.normal.meet y.normal, x.exceptional.meet y.exceptional⟩

theorem Exits.get_meet (x y : Exits ExitSchema) (c : Completion) : (x.meet y).get c = (x.get c).meet (y.get c) := by
  cases c <;> rfl

theorem Exits.canonical_meet {x y : Exits ExitSchema} (hx : x.canonicalTransports = true)
    (hy : y.canonicalTransports = true) : (x.meet y).canonicalTransports = true := by
  simp only [Exits.canonicalTransports, Bool.and_eq_true] at hx hy ⊢
  exact ⟨ExitSchema.canonical_meet hx.1 hy.1, ExitSchema.canonical_meet hx.2 hy.2⟩

/-- **The conjunction of two canonical schemas is both guarantees**, on
either exit (the note, rule Conj, at one call). -/
theorem Exits.exitPost_meet {x y : Exits ExitSchema} (hx : x.canonicalTransports = true)
    (hy : y.canonicalTransports = true) {c : Completion} {r : Tm} {args : List Tm} {s s' : IndexedHeap} {v : Tm} :
    (x.meet y).exitPost c r args s s' v ↔ x.exitPost c r args s s' v ∧ y.exitPost c r args s s' v := by
  have hslots : (x.meet y).slots = max x.slots y.slots := by
    simp only [Exits.slots, Exits.meet, ExitSchema.slots_meet]
    omega
  unfold Exits.exitPost
  rw [Exits.atArity, Exits.get_map, Exits.get_meet, ExitSchema.instantiate_meet, ExitSpec.holds_meet]
  refine and_congr ?_ ?_
  · rw [← instantiate_completion hx (N := (x.meet y).callInstantiation args.length |>.entrySlots)
      (by show _ ≤ max _ _; rw [hslots]; omega)]
    rfl
  · rw [← instantiate_completion hy (N := (x.meet y).callInstantiation args.length |>.entrySlots)
      (by show _ ≤ max _ _; rw [hslots]; omega)]
    rfl

end Verification.CallEffects
