import Verification.Programs.HeapExpressionRules
import Verification.Semantics.IndexNumbers

/-! # Writes at a checked index

The index facts (`HeapKnowledge.IndexAtom`) and the write they admit
(PROGRAM-TYPING.md, "Writes at a checked index"). A guard
`(k & m) !== k || k > xs.length`, `m` a mask whose `ToInt32` is a natural
below `2^31`, states them in four steps: the conjunction is an index
(`index-mask`), strict equality with an index is one where it answers `true`
(`index-equal`), the read of a store's length a read link names is that
array's length (`length-observed`), and a comparison of an index with that
length bounds it on the answer giving `k ≤ length` (`bound-compare`). Each is
a layer of `Checker.ordinary` adding ats to the output its base step's
check gives. The write `x.[] := x.[]⟦k ↦ v⟧` on a homogeneous writable array
is safe where `bound(x, k)` holds (`setElem-bounded`): it lands on a present
element or appends, and leaves no hole. -/
namespace Verification.IndexWrites
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower
open HeapObservations HeapKnowledge ProgramCertificates
open PositiveCertificates (InstanceImageCheck)

variable {ι : Type}

/-! ## The runs the facts are read from -/

/-- A thrown value reaches no value: any postcondition holds of it. -/
theorem throw_post {Ξ T : Fam} {Q Q' : Post} {v : Tm} (hv : isVal v = true) :
    ∀ {n W h}, SafePost Ξ T Q n W h (.throw v) → SafePost Ξ T Q' n W h (.throw v) := by
  intro n W h hs
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hval, -, -⟩ | hr) | ⟨U, h', t', -, -, step, -, -⟩
    · simp [isVal] at hval
    · exact .inl (.inr hr)
    · cases step with
      | throwC s => exact absurd s (value_no_step hv)

/-- An operator on two values gives, where it returns, the value `binop`
gives, in the heap it started in. -/
theorem arith_run {Ξ T : Fam} {Q : Post} {op : Arith} {a b : Tm} (ha : isVal a = true) (hb : isVal b = true) :
    ∀ {n W h}, SafePost Ξ T Q n W h (.arith op a b) →
      SafePost Ξ T (fun h' u => Q h' u ∧ h' = h ∧ binop op a b = some u) n W h (.arith op a b) := by
  intro n W h hs
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hval, -, -⟩ | ⟨u, hr, -⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · simp [isVal] at hval
    · cases hr with
      | arithC1 hr => exact absurd (raises_not_val hr) (by simp [ha])
      | arithC2 _ hr => exact absurd (raises_not_val hr) (by simp [hb])
    · refine .inr ⟨U, h', t', hx, hu, step, hh, ?_⟩
      cases step with
      | arithC1 s => exact absurd s (value_no_step ha)
      | arithC2 _ s => exact absurd s (value_no_step hb)
      | arithV hv =>
        cases n with
        | zero => trivial
        | succ m =>
          rcases hs with (⟨hval, ht, hq⟩ | ⟨u, hr, -⟩) | ⟨U', h'', t'', -, -, step', -, -⟩
          · exact .inl (.inl ⟨hval, ht, hq, rfl, hv⟩)
          · exact absurd (raises_not_val hr) (by simp [(binop_values hv).2.2])
          · exact absurd step' (value_no_step (binop_values hv).2.2)
      | arithThrow _ => exact throw_post rfl hs

/-- A store's length gives, where it returns, the number of its entries, in
the heap it started in. -/
theorem len_run {Ξ T : Fam} {Q : Post} {ls : List (Option Nat)} :
    ∀ {n W h}, SafePost Ξ T Q n W h (.lenOf (.arr ls)) →
      SafePost Ξ T (fun h' u => Q h' u ∧ h' = h ∧ u = .num (bitsOfNat ls.length)) n W h (.lenOf (.arr ls)) := by
  intro n W h hs
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hval, -, -⟩ | ⟨u, hr, -⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · simp [isVal] at hval
    · cases hr with
      | lenC hr => exact absurd (raises_not_val hr) (by simp [isVal])
    · refine .inr ⟨U, h', t', hx, hu, step, hh, ?_⟩
      cases step with
      | lenC s => exact absurd s (value_no_step rfl)
      | lenV =>
        cases n with
        | zero => trivial
        | succ m =>
          rcases hs with (⟨hval, ht, hq⟩ | ⟨u, hr, -⟩) | ⟨U', h'', t'', -, -, step', -, -⟩
          · exact .inl (.inl ⟨hval, ht, hq, rfl, rfl⟩)
          · exact absurd (raises_not_val hr) (by simp [isVal])
          · exact absurd step' (value_no_step rfl)

/-! ## What the knowledge states of a slot -/

/-- Whether an unconditional at states that a slot of `a`'s class holds an index. -/
def indexed (k : Knowledge) (a : Nat) : Bool :=
  k.indices.any fun atom => atom.cond.isNone && match atom.fact with
    | .index i => (HeapLinks.aliases k.links a).contains i
    | _ => false

theorem indexed_sound {k : Knowledge} {a : Nat} {ρ h} (hc : indexed k a = true) (hk : Holds k ρ h) :
    ∃ b i, ρ a = .num b ∧ indexOfBits b = some i := by
  obtain ⟨atom, ha, hm⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hnone, hf⟩ := hm
  have hat := hk.2.2.2.2.2 atom ha fun b hb => by rw [hnone] at hb; cases hb
  cases hfact : atom.fact with
  | index i =>
    rw [hfact] at hf hat
    simp only [List.contains_iff_mem] at hf
    rw [← HeapLinks.aliases_eq hk.2.2.1 hf]
    exact hat
  | length _ _ => rw [hfact] at hf; cases hf
  | bound _ _ => rw [hfact] at hf; cases hf
  | int _ => rw [hfact] at hf; cases hf
  | linear _ => rw [hfact] at hf; cases hf

/-- The arrays whose store's length a slot of `n`'s class holds, by unconditional ats. -/
def lengthsOf (k : Knowledge) (n : Nat) : List Nat :=
  k.indices.filterMap fun atom => if atom.cond.isNone then
    match atom.fact with
    | .length x n' => if (HeapLinks.aliases k.links n).contains n' then some x else none
    | _ => none
  else none

theorem lengthsOf_sound {k : Knowledge} {n x : Nat} {ρ h} (hx : x ∈ lengthsOf k n) (hk : Holds k ρ h) :
    ∃ s ls, Footprints.storeOf (ρ x) = some s ∧ h[s]? = some (.arr ls) ∧ ρ n = .num (bitsOfNat ls.length) ∧
      ls.length ≤ maxArrayLength := by
  obtain ⟨atom, ha, hm⟩ := List.mem_filterMap.mp hx
  split at hm
  · rename_i hnone
    have hat := hk.2.2.2.2.2 atom ha fun b hb => by
      rw [Option.isNone_iff_eq_none.mp hnone] at hb; cases hb
    cases hfact : atom.fact with
    | length x' n' =>
      rw [hfact] at hm hat
      simp only at hm
      split at hm
      · rename_i hal
        cases hm
        simp only [List.contains_iff_mem] at hal
        rw [← HeapLinks.aliases_eq hk.2.2.1 hal]
        exact hat
      · cases hm
    | index _ => rw [hfact] at hm; cases hm
    | bound _ _ => rw [hfact] at hm; cases hm
    | int _ => rw [hfact] at hm; cases hm
    | linear _ => rw [hfact] at hm; cases hm
  · cases hm

/-- The arrays a slot of `s`'s class was read from as their store: read links
at the store field. -/
def storeReaders (k : Knowledge) (s : Nat) : List Nat :=
  k.links.filterMap fun g => if !g.alias && !g.optional && g.field == arrayStoreKey &&
    (HeapLinks.aliases k.links s).contains g.value then some g.cell else none

theorem storeReaders_sound {k : Knowledge} {s x : Nat} {ρ h} (hx : x ∈ storeReaders k s) (hk : Holds k ρ h) :
    ∃ l, Footprints.storeOf (ρ x) = some l ∧ h[l]? = some (ρ s) := by
  obtain ⟨g, hg, hm⟩ := List.mem_filterMap.mp hx
  split at hm
  · rename_i hc
    cases hm
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem] at hc
    obtain ⟨⟨⟨hal, hopt⟩, hfld⟩, hval⟩ := hc
    have hl := hk.2.2.1 g hg
    simp only [hal, hopt, Bool.false_eq_true, if_false] at hl
    obtain ⟨flds, c, oid, l, hcell, hf, hl⟩ := hl
    refine ⟨l, ?_, ?_⟩
    · rw [hcell]; simp only [Footprints.storeOf, Footprints.fieldsOf]; rw [← hfld]; exact hf
    · rw [hl, HeapLinks.aliases_eq hk.2.2.1 hval]
  · cases hm

/-- Whether every value a slot may hold, by its type and the knowledge, is a
number whose `ToInt32` is a natural below `2^31`: one of finitely many such
number literals and nothing else. -/
def maskSlot [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (m : Nat) : Bool :=
  match HeapExpressionRules.valuesAt G Γ k m with
  | some V => match V.num with
    | .these bs => ({ V with num := .none } == ValueSets.ValueSet.bot) &&
        bs.all fun b => decide (0 ≤ toInt32 b) && decide (toInt32 b < 2 ^ 31)
    | .allBut _ => false
  | none => false

theorem maskSlot_sound [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {m : Nat} {ρ n W h}
    (hc : maskSlot G Γ k m = true) (he : EnvOk G Γ ρ n W) (hk : Holds k ρ h) :
    ∃ (b : UInt64) (M : Nat), ρ m = .num b ∧ toInt32 b = (M : Int) ∧ M < 2 ^ 31 := by
  unfold maskSlot at hc
  split at hc
  · rename_i V hV
    have hmem := HeapExpressionRules.valuesAt_sound hV he hk
    split at hc
    · rename_i bs hbs
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hbot, hall⟩ := hc
      cases hv : ρ m with
      | num b =>
        rw [hv] at hmem
        simp only [ValueSets.ValueSet.mem, hbs, ValueSets.Lit.mem, List.contains_iff_mem] at hmem
        obtain ⟨h0, h1⟩ := hall b hmem
        exact ⟨b, (toInt32 b).toNat, rfl, by omega, by omega⟩
      | _ =>
        all_goals
          rw [hv] at hmem
          have h1 := congrArg ValueSets.ValueSet.nul hbot
          have h2 := congrArg ValueSets.ValueSet.undef hbot
          have h3 := congrArg ValueSets.ValueSet.tru hbot
          have h4 := congrArg ValueSets.ValueSet.fls hbot
          have h5 := congrArg ValueSets.ValueSet.sym hbot
          have h6 := congrArg ValueSets.ValueSet.arr hbot
          have h7 := congrArg ValueSets.ValueSet.str hbot
          have h8 := congrArg ValueSets.ValueSet.big hbot
          have h9 := congrArg ValueSets.ValueSet.obj hbot
          simp only [ValueSets.ValueSet.bot] at h1 h2 h3 h4 h5 h6 h7 h8 h9
          simp [ValueSets.ValueSet.mem, h1, h2, h3, h4, h5, h6, h7, h8, h9, ValueSets.Lit.mem, ValueSets.Lit.none,
            ValueSets.Obj.mem] at hmem
    · cases hc
  · cases hc

/-- Whether a slot's type is a store: one list contract. -/
def storeSlot (G : NormalGraph ι) (Γ : List (Ty ι)) (s : Nat) : Bool :=
  match Γ[s]? with
  | some S => match expand G S with
    | [.list _ []] => true
    | _ => false
  | none => false

theorem storeSlot_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {s : Nat} {ρ n W}
    (hc : storeSlot G Γ s = true) (he : EnvOk G Γ ρ n W) : ∃ ls, ρ s = .arr ls ∧ ls.length ≤ maxArrayLength := by
  unfold storeSlot at hc
  split at hc
  · rename_i S hS
    split at hc
    · rename_i T hT
      obtain ⟨ls, hls, -, -, hmax, -⟩ := ((represents_raw (c := .list T []) hT n W (ρ s)) (he.2 s S hS)).1
      exact ⟨ls, hls, hmax⟩
    · cases hc
  · cases hc

/-! ## The atoms a step states -/

/-- The answer of `op` on which an index on the left (`left`) or on the right
is at most the other operand (`IndexNumbers.boundAnswer`). -/
def boundAnswerOf (op : Arith) (left : Bool) : Option Bool :=
  if IndexNumbers.boundAnswer op left true then some true
  else if IndexNumbers.boundAnswer op left false then some false else none

theorem boundAnswerOf_sound {op : Arith} {left q : Bool} (h : boundAnswerOf op left = some q) :
    IndexNumbers.boundAnswer op left q = true := by
  unfold boundAnswerOf at h
  split at h
  · cases h; assumption
  · split at h
    · cases h; assumption
    · cases h

/-- The index atoms a step on slots states of its result, slot `0`, every
other slot one higher: the length of a store a read link names
(`length-observed`), an index from a conjunction with a mask (`index-mask`),
an index equal to one (`index-equal`, where the equality answers `true`),
and an index bounded by a length (`bound-compare`, on the answer giving it). -/
def stepAtoms [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Tm → List IndexAtom
  | .lenOf (.var s) =>
    if storeSlot G Γ s then (storeReaders k s).map fun x => ⟨.length (x + 1) 0, none, false⟩ else []
  | .arith op (.var a) (.var b) =>
    if a < Γ.length ∧ b < Γ.length then
      match op with
      | .bitAnd => if maskSlot G Γ k a || maskSlot G Γ k b then [⟨.index 0, none, false⟩] else []
      | .eq =>
        (if indexed k a then [⟨.index (b + 1), some 0, false⟩] else []) ++
        (if indexed k b then [⟨.index (a + 1), some 0, false⟩] else [])
      | op =>
        (match boundAnswerOf op true with
         | some q => if indexed k a then (lengthsOf k b).map fun x => ⟨.bound (x + 1) (a + 1), some 0, !q⟩ else []
         | none => []) ++
        (match boundAnswerOf op false with
         | some q => if indexed k b then (lengthsOf k a).map fun x => ⟨.bound (x + 1) (b + 1), some 0, !q⟩ else []
         | none => [])
    else []
  | _ => []

theorem binop_bitAnd {a b u : Tm} (h : binop .bitAnd a b = some u) :
    ∃ x y, a = .num x ∧ b = .num y ∧ u = .num (arithBits .bitAnd x y) := by
  unfold binop at h
  simp only [reduceCtorEq, if_false, Arith.relational, Bool.false_eq_true] at h
  split at h <;> simp_all [bigintArith] <;> exact absurd h.1 (by decide)

theorem binop_relational {op : Arith} {x y : UInt64} {u : Tm} (hop : op.relational = true)
    (h : binop op (.num x) (.num y) = some u) : u = boolVal (relationHolds op (doubleOrder x y)) := by
  unfold binop at h
  have hne : op ≠ .eq := by rintro rfl; simp [Arith.relational] at hop
  have hnl : op ≠ .looseEq := by rintro rfl; simp [Arith.relational] at hop
  simp only [hne, hnl, if_false, hop, if_true, relationalValue, relNumeric, Option.bind_some,
    numericRelation, Option.some.injEq] at h
  exact h.symm

theorem truthy_boolVal {r q : Bool} (h : tagHolds .truthy (boolVal r) = q) : r = q := by
  cases r <;> cases q <;> simp_all [boolVal, tagHolds]

theorem stepAtoms_shape [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {t : Tm}
    (h : stepAtoms G Γ k t ≠ []) :
    (∃ s, t = .lenOf (.var s)) ∨ (∃ op a b, t = .arith op (.var a) (.var b)) := by
  unfold stepAtoms at h
  split at h
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, _, _, rfl⟩
  · exact absurd rfl h

theorem stepAtoms_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {t : Tm}
    {Ξ T : Fam} {Q : Post} {ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ρ h) (hs : SafePost Ξ T Q n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds (stepAtoms G Γ k t) (push u ρ) h') n W h
      (instantiate 0 ρ t) := by
  have hval : ∀ i, i < Γ.length → isVal (ρ i) = true := fun i hi =>
    (meaning_value (he.2 i _ (List.getElem?_eq_getElem hi))).1
  by_cases hnil : stepAtoms G Γ k t = []
  · rw [hnil]; exact weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _⟩) hs
  rcases stepAtoms_shape hnil with ⟨s, rfl⟩ | ⟨op, a, b, rfl⟩
  · -- `length-observed`
    simp only [stepAtoms]
    split
    · rename_i hst
      obtain ⟨ls, hls, hmax⟩ := storeSlot_sound hst he
      simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero, hls] at hs ⊢
      refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (len_run hs)
      obtain ⟨-, rfl, rfl⟩ := hq
      intro atom ha _
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨l, hl, hh⟩ := storeReaders_sound hx hk
      exact ⟨l, ls, hl, by rw [hh, hls], rfl, hmax⟩
    · exact weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _⟩) hs
  · simp only [stepAtoms]
    split
    · rename_i hab
      have ha := hval a hab.1
      have hb := hval b hab.2
      simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero] at hs ⊢
      refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (arith_run ha hb hs)
      obtain ⟨-, rfl, hu⟩ := hq
      split
      · -- `index-mask`
        split
        · rename_i hm
          intro atom hat _
          simp only [List.mem_singleton] at hat
          subst hat
          obtain ⟨x, y, hx, hy, rfl⟩ := binop_bitAnd hu
          rcases Bool.or_eq_true_iff.mp hm with hm | hm
          · obtain ⟨b', M, hb', hM, hlt⟩ := maskSlot_sound hm he hk
            rw [hx] at hb'; cases hb'
            obtain ⟨r, hr⟩ := IndexNumbers.mask_bitAnd_index y hM hlt
            exact ⟨_, r, rfl, hr⟩
          · obtain ⟨b', M, hb', hM, hlt⟩ := maskSlot_sound hm he hk
            rw [hy] at hb'; cases hb'
            obtain ⟨r, hr⟩ := IndexNumbers.bitAnd_index x hM hlt
            exact ⟨_, r, rfl, hr⟩
        · exact indexHolds_nil _ _
      · -- `index-equal`
        intro atom hat hcond
        have hc := hcond 0
        simp only [binop, if_true, Option.map_eq_some_iff] at hu
        obtain ⟨r, hr, rfl⟩ := hu
        rcases List.mem_append.mp hat with hat | hat
        · split at hat
          · rename_i hi
            simp only [List.mem_singleton] at hat
            subst hat
            have hr' : r = true := truthy_boolVal (hc rfl)
            subst hr'
            obtain ⟨x, i, hx, hix⟩ := indexed_sound hi hk
            rw [hx] at hr
            obtain ⟨y, hy, hiy⟩ := IndexNumbers.strictEquals_index hr hix
            exact ⟨y, i, by simpa [push] using hy, hiy⟩
          · cases hat
        · split at hat
          · rename_i hi
            simp only [List.mem_singleton] at hat
            subst hat
            have hr' : r = true := truthy_boolVal (hc rfl)
            subst hr'
            obtain ⟨x, i, hx, hix⟩ := indexed_sound hi hk
            rw [hx] at hr
            obtain ⟨y, hy, hiy⟩ := IndexNumbers.strictEquals_index_swap hr hix
            exact ⟨y, i, by simpa [push] using hy, hiy⟩
          · cases hat
      · -- `bound-compare`
        intro atom hat hcond
        have hc := hcond 0
        rcases List.mem_append.mp hat with hat | hat
        · split at hat
          · rename_i q hq
            split at hat
            · rename_i hi
              obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hat
              have hrel : op.relational = true := by
                have := boundAnswerOf_sound hq
                cases op <;> cases q <;> simp [IndexNumbers.boundAnswer, Arith.relational] at this ⊢
              obtain ⟨x, i, hx, hix⟩ := indexed_sound hi hk
              obtain ⟨s, ls, hs', hls, hb', -⟩ := lengthsOf_sound hx' hk
              rw [hx, hb'] at hu
              have hu' := binop_relational hrel hu
              have hcq := hc rfl
              simp only [push, hu', Bool.not_not] at hcq
              have hle := IndexNumbers.le_of_relation hix (boundAnswerOf_sound hq) (truthy_boolVal hcq)
              exact ⟨s, ls, x, i, by simpa [push] using hs', hls, by simpa [push] using hx, hix, hle⟩
            · cases hat
          · cases hat
        · split at hat
          · rename_i q hq
            split at hat
            · rename_i hi
              obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hat
              have hrel : op.relational = true := by
                have := boundAnswerOf_sound hq
                cases op <;> cases q <;> simp [IndexNumbers.boundAnswer, Arith.relational] at this ⊢
              obtain ⟨x, i, hx, hix⟩ := indexed_sound hi hk
              obtain ⟨s, ls, hs', hls, hb', -⟩ := lengthsOf_sound hx' hk
              rw [hx, hb'] at hu
              have hu' := binop_relational hrel hu
              have hcq := hc rfl
              simp only [push, hu', Bool.not_not] at hcq
              have hle := IndexNumbers.le_of_relation_swap hix (boundAnswerOf_sound hq) (truthy_boolVal hcq)
              exact ⟨s, ls, x, i, by simpa [push] using hs', hls, by simpa [push] using hx, hix, hle⟩
            · cases hat
          · cases hat
    · exact weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _⟩) hs

/-! ## The linear atoms a step states

A step on safe integers states the integer facts of its result (PROGRAM-TYPING.md,
"Linear facts"): a literal its value, a copy its equality with the copied
slot, a store's length its range `0 ≤ n ≤ 2^32 - 1`, a sum or a difference its
value where the knowledge bounds it within the safe integers, and a comparison
its outcome on each answer. An operand is a slot the knowledge states a safe
integer, or a literal that is one; its value is a linear form plus a constant. -/

/-- The largest safe integer, `2^53 - 1`. -/
def maxSafe : Int := 2 ^ 53 - 1

/-- An operand's value as a linear form over the input slots plus a constant. -/
def operandForm (k : Knowledge) : Tm → Option (Linear.Form × Int)
  | .var a => if intSlot k.indices a then some ([(a, 1)], 0) else none
  | .num b => (SafeIntegers.safeIntOfBits b).map fun i => ([], i)
  | _ => none

/-- Whether a term is a slot of the context or a literal number. -/
def operandIn (Γ : List (Ty ι)) : Tm → Bool
  | .var x => decide (x < Γ.length)
  | .num _ => true
  | _ => false

/-- A form over the input slots, read over the output slots, one higher. -/
def shiftForm (F : Linear.Form) : Linear.Form := F.map fun (x, c) => (x + 1, c)

/-- The atoms stating that the result, slot 0, is the value of `F + c` over the
input slots, a safe integer. -/
def valueAtoms (F : Linear.Form) (c : Int) : List IndexAtom :=
  [⟨.int 0, none, false⟩, ⟨.linear (.le ((0, 1) :: shiftForm (F.scale (-1))) c), none, false⟩,
    ⟨.linear (.le ((0, -1) :: shiftForm F) (-c)), none, false⟩]

/-- The atoms of a comparison's two answers, on the result slot 0, of operands
whose difference is `D + c`: the fact each answer gives, conditional on it. -/
def compareAtoms (op : Arith) (D : Linear.Form) (c : Int) : List IndexAtom :=
  let pos := shiftForm D
  let neg := shiftForm (D.scale (-1))
  -- (fact on `true`, fact on `false`)
  let facts : Option (Linear.Fact × Linear.Fact) := match op with
    | .lt => some (.le pos (-1 - c), .le neg c)
    | .le => some (.le pos (-c), .le neg (c - 1))
    | .gt => some (.le neg (c - 1), .le pos (-c))
    | .ge => some (.le neg c, .le pos (-1 - c))
    | _ => none
  match facts with
  | some (t, f) => [⟨.linear t, some 0, false⟩, ⟨.linear f, some 0, true⟩]
  | none => []

/-- The linear atoms a step on slots states of its result. -/
def linearAtoms (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Tm → List IndexAtom
  | .num b => match SafeIntegers.safeIntOfBits b with
    | some i => valueAtoms [] i
    | none => []
  | .var a => if a < Γ.length ∧ intSlot k.indices a = true then valueAtoms [(a, 1)] 0 else []
  | .lenOf (.var s) =>
    if storeSlot G Γ s then
      [⟨.int 0, none, false⟩, ⟨.linear (.le [(0, -1)] 0), none, false⟩,
        ⟨.linear (.le [(0, 1)] maxArrayLength), none, false⟩]
    else []
  | .arith op a b =>
    if operandIn Γ a && operandIn Γ b then
      match operandForm k a, operandForm k b with
      | some (fa, ca), some (fb, cb) =>
        let sum := fun (F : Linear.Form) (c : Int) =>
          if Linear.entails (linearFacts k.indices) (.le F (maxSafe - c)) &&
              Linear.entails (linearFacts k.indices) (.le (F.scale (-1)) (maxSafe + c)) then valueAtoms F c else []
        match op with
        | .add => sum (fa ++ fb) (ca + cb)
        | .sub => sum (fa ++ fb.scale (-1)) (ca - cb)
        | .lt | .le | .gt | .ge => compareAtoms op (fa ++ fb.scale (-1)) (ca - cb)
        | _ => []
      | _, _ => []
    else []
  | _ => []

theorem eval_shiftForm (F : Linear.Form) (u : Val) (ρ : Env) :
    Linear.Form.eval (valuation (push u ρ)) (shiftForm F) = Linear.Form.eval (valuation ρ) F := by
  induction F with
  | nil => rfl
  | cons p t ih => obtain ⟨x, c⟩ := p; simp only [shiftForm, List.map_cons, Linear.Form.eval] at ih ⊢; rw [ih]; rfl

theorem shiftForm_vars (F : Linear.Form) : (shiftForm F).map (·.1) = (F.map (·.1)).map (· + 1) := by
  simp [shiftForm, Function.comp_def]

theorem scale_vars (k : Int) (F : Linear.Form) : (F.scale k).map (·.1) = F.map (·.1) := by
  simp [Linear.Form.scale, Function.comp_def]

/-- What an operand denotes: a value whose safe integer is `F + c` at the input slots. -/
theorem operandForm_sound {k : Knowledge} {t : Tm} {F : Linear.Form} {c : Int} {ρ h}
    (ho : operandForm k t = some (F, c)) (hk : Holds k ρ h) :
    (∀ x ∈ F.map (·.1), (intValue (ρ x)).isSome) ∧
      ∃ b, instantiate 0 ρ t = .num b ∧ SafeIntegers.SafeInt b (Linear.Form.eval (valuation ρ) F + c) := by
  cases t with
  | var a =>
    simp only [operandForm] at ho
    split at ho
    · rename_i hi
      cases ho
      have hs := intSlot_sound hk.2.2.2.2.2 hi
      obtain ⟨i, hi'⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨b, hb, hsafe⟩ := intValue_safe hi'
      refine ⟨by simp [hs], b, by simp [instantiate, hb], ?_⟩
      simp only [Linear.Form.eval, valuation, hi', Option.getD_some]
      simpa using hsafe
    · cases ho
  | num b =>
    simp only [operandForm, Option.map_eq_some_iff, Prod.mk.injEq] at ho
    obtain ⟨i, hi, rfl, rfl⟩ := ho
    exact ⟨by simp, b, rfl, by simpa [Linear.Form.eval] using SafeIntegers.safeIntOfBits_sound hi⟩
  | _ => simp [operandForm] at ho

theorem valueAtoms_holds {F : Linear.Form} {c : Int} {ρ h} {b : UInt64}
    (hF : ∀ x ∈ F.map (·.1), (intValue (ρ x)).isSome)
    (hb : SafeIntegers.SafeInt b (Linear.Form.eval (valuation ρ) F + c)) :
    IndexHolds (valueAtoms F c) (push (.num b) ρ) h := by
  have h0 : valuation (push (.num b) ρ) 0 = Linear.Form.eval (valuation ρ) F + c := by
    simp [valuation, push, intValue_num hb]
  have hi0 : (intValue (push (.num b) ρ 0)).isSome := by simp [push, intValue_num hb]
  have hvars : ∀ x ∈ (shiftForm F).map (·.1), (intValue (push (.num b) ρ x)).isSome := by
    rw [shiftForm_vars]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    simpa [push] using hF y hy
  intro a ha _
  simp only [valueAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact hi0
  · refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Linear.Fact.vars, List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hi0
      · rw [shiftForm_vars, scale_vars, ← shiftForm_vars] at hx; exact hvars x hx
    · show Linear.Form.eval _ _ ≤ c
      simp only [Linear.Form.eval, eval_shiftForm, Linear.Form.eval_scale, h0]
      omega
  · refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Linear.Fact.vars, List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hi0
      · exact hvars x hx
    · show Linear.Form.eval _ _ ≤ -c
      simp only [Linear.Form.eval, eval_shiftForm, h0]
      omega

/-- A value term runs to itself in the heap it started in. -/
theorem value_run {Ξ T : Fam} {Q : Post} {v : Tm} (hv : isVal v = true) :
    ∀ {n W h}, SafePost Ξ T Q n W h v → SafePost Ξ T (fun h' u => Q h' u ∧ h' = h ∧ u = v) n W h v := by
  intro n W h hs
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hval, ht, hq⟩ | hr) | ⟨U, h', t', -, -, step, -, -⟩
    · exact .inl (.inl ⟨hval, ht, hq, rfl, rfl⟩)
    · exact absurd hr (val_not_thrown hv)
    · exact absurd step (value_no_step hv)

theorem binop_num_arith {op : Arith} {x y : UInt64} {u : Tm} (hop : op = .add ∨ op = .sub)
    (h : binop op (.num x) (.num y) = some u) : u = .num (arithBits op x y) := by
  rcases hop with rfl | rfl <;> simp [binop, Arith.relational] at h <;> exact h.symm

theorem storeSlot_bound {G : NormalGraph ι} {Γ : List (Ty ι)} {s : Nat} {ρ n W}
    (hc : storeSlot G Γ s = true) (he : EnvOk G Γ ρ n W) : ∃ ls, ρ s = .arr ls ∧ ls.length ≤ maxArrayLength :=
  storeSlot_sound hc he

theorem operandIn_value {Γ : List (Ty ι)} {t : Tm} {ρ : Env} (hval : ∀ i, i < Γ.length → isVal (ρ i) = true)
    (h : operandIn Γ t = true) : isVal (instantiate 0 ρ t) = true := by
  cases t <;> simp_all [operandIn, instantiate, isVal]

/-- What an answer of a comparison of two integers states of their difference. -/
def answerHolds : Arith → Bool → Int → Prop
  | .lt, true, d => d ≤ -1
  | .lt, false, d => -d ≤ 0
  | .le, true, d => d ≤ 0
  | .le, false, d => -d ≤ -1
  | .gt, true, d => -d ≤ -1
  | .gt, false, d => d ≤ 0
  | .ge, true, d => -d ≤ 0
  | .ge, false, d => d ≤ -1
  | _, _, _ => True

theorem answer_sound (op : Arith) (i j : Int) :
    answerHolds op (relationHolds op (some (compare i j))) (i - j) := by
  rcases Int.lt_trichotomy i j with hl | rfl | hl
  · rw [Int.compare_eq_lt.mpr hl]; cases op <;> simp [answerHolds, relationHolds] <;> omega
  · rw [Int.compare_eq_eq.mpr rfl]; cases op <;> simp [answerHolds, relationHolds]
  · rw [Int.compare_eq_gt.mpr hl]; cases op <;> simp [answerHolds, relationHolds] <;> omega

/-- The facts a comparison's answer gives, conditional on the answer. -/
theorem compareAtoms_holds {op : Arith} {D : Linear.Form} {c : Int} {ρ h} {x y : UInt64} {i j : Int}
    (hD : ∀ z ∈ D.map (·.1), (intValue (ρ z)).isSome)
    (hdiff : Linear.Form.eval (valuation ρ) D + c = i - j)
    (hx : SafeIntegers.SafeInt x i) (hy : SafeIntegers.SafeInt y j) :
    IndexHolds (compareAtoms op D c) (push (boolVal (relationHolds op (doubleOrder x y))) ρ) h := by
  rw [SafeIntegers.doubleOrder_safe hx hy]
  generalize hr : relationHolds op (some (compare i j)) = r
  have hans : answerHolds op r (i - j) := hr ▸ answer_sound op i j
  have hvars : ∀ (F : Linear.Form), F.map (·.1) = D.map (·.1) →
      ∀ z ∈ (shiftForm F).map (·.1), (intValue (push (boolVal r) ρ z)).isSome := by
    intro F hF z hz
    rw [shiftForm_vars, hF] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    simpa [push] using hD w hw
  have hpos := hvars D rfl
  have hneg := hvars (D.scale (-1)) (scale_vars _ _)
  have ep : Linear.Form.eval (valuation (push (boolVal r) ρ)) (shiftForm D) = i - j - c := by
    rw [eval_shiftForm]; omega
  have en : Linear.Form.eval (valuation (push (boolVal r) ρ)) (shiftForm (D.scale (-1))) = -(i - j - c) := by
    rw [eval_shiftForm, Linear.Form.eval_scale]; omega
  intro a ha hc
  have hq := hc 0
  have hb : ∀ q : Bool, tagHolds .truthy (push (boolVal r) ρ 0) = q → r = q := by
    intro q hq'; cases r <;> cases q <;> simp_all [push, boolVal, tagHolds]
  cases op <;> simp only [compareAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
    first
    | (rcases ha with rfl | rfl
       · have := hb true (hq rfl); subst this
         exact ⟨fun z hz => by first | exact hpos z hz | exact hneg z hz, by
           show _ ≤ _; first | (rw [ep]; simp only [answerHolds] at hans; omega) | (rw [en]; simp only [answerHolds] at hans; omega)⟩
       · have := hb false (hq rfl); subst this
         exact ⟨fun z hz => by first | exact hpos z hz | exact hneg z hz, by
           show _ ≤ _; first | (rw [ep]; simp only [answerHolds] at hans; omega) | (rw [en]; simp only [answerHolds] at hans; omega)⟩)
    | exact absurd ha (by simp)

theorem binop_num_relational {op : Arith} {x y : UInt64} {u : Tm} (hop : op.relational = true)
    (h : binop op (.num x) (.num y) = some u) : u = boolVal (relationHolds op (doubleOrder x y)) :=
  binop_relational hop h

/-- **The linear atoms a step states hold of its result.** -/
theorem linearAtoms_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {t : Tm}
    {Ξ T : Fam} {Q : Post} {ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ρ h) (hs : SafePost Ξ T Q n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds (linearAtoms G Γ k t) (push u ρ) h') n W h
      (instantiate 0 ρ t) := by
  have hval : ∀ i, i < Γ.length → isVal (ρ i) = true := fun i hi =>
    (meaning_value (he.2 i _ (List.getElem?_eq_getElem hi))).1
  have none_case : SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds [] (push u ρ) h') n W h (instantiate 0 ρ t) :=
    weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _⟩) hs
  cases t with
  | num b =>
    simp only [linearAtoms]
    split
    · rename_i i hi
      simp only [instantiate] at hs ⊢
      refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (value_run rfl hs)
      obtain ⟨-, -, rfl⟩ := hq
      exact valueAtoms_holds (by simp) (by simpa [Linear.Form.eval] using SafeIntegers.safeIntOfBits_sound hi)
    · exact none_case
  | var a =>
    simp only [linearAtoms]
    split
    · rename_i hc
      obtain ⟨ha, hi⟩ := hc
      simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero] at hs ⊢
      refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (value_run (hval a ha) hs)
      obtain ⟨-, -, rfl⟩ := hq
      have hs' := intSlot_sound hk.2.2.2.2.2 hi
      obtain ⟨i, hi'⟩ := Option.isSome_iff_exists.mp hs'
      obtain ⟨b, hb, hsafe⟩ := intValue_safe hi'
      rw [hb]
      refine valueAtoms_holds (by simp [hs']) ?_
      simpa [Linear.Form.eval, valuation, hi'] using hsafe
    · exact none_case
  | lenOf a =>
    cases a with
    | var s =>
      simp only [linearAtoms]
      split
      · rename_i hst
        obtain ⟨ls, hls, hmax⟩ := storeSlot_bound hst he
        simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero, hls] at hs ⊢
        refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (len_run hs)
        obtain ⟨-, -, rfl⟩ := hq
        have hsafe : SafeIntegers.SafeInt (bitsOfNat ls.length) (ls.length : Int) :=
          ⟨by simp [maxArrayLength] at hmax ⊢; omega, .inl ⟨by omega, by simp⟩⟩
        have h0 : intValue (push (.num (bitsOfNat ls.length)) ρ 0) = some (ls.length : Int) := intValue_num hsafe
        have hv0 : valuation (push (.num (bitsOfNat ls.length)) ρ) 0 = ls.length := by simp [valuation, h0]
        intro atom hat _
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hat
        rcases hat with rfl | rfl | rfl
        · show (intValue _).isSome; rw [h0]; rfl
        · refine ⟨by simp [Linear.Fact.vars, h0], ?_⟩
          show Linear.Form.eval _ _ ≤ _; simp [Linear.Form.eval, hv0]
        · refine ⟨by simp [Linear.Fact.vars, h0], ?_⟩
          show Linear.Form.eval _ _ ≤ _; simp [Linear.Form.eval, hv0]; simpa [maxArrayLength] using hmax
      · exact none_case
    | _ => simp only [linearAtoms]; exact none_case
  | arith op a b =>
    simp only [linearAtoms]
    split
    · rename_i hin
      simp only [Bool.and_eq_true] at hin
      have ha := operandIn_value hval hin.1
      have hb := operandIn_value hval hin.2
      split
      · rename_i fa ca fb cb hfa hfb
        obtain ⟨hva, xa, hxa, hsa⟩ := operandForm_sound hfa hk
        obtain ⟨hvb, xb, hxb, hsb⟩ := operandForm_sound hfb hk
        simp only [instantiate] at hs ⊢
        refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (arith_run ha hb hs)
        obtain ⟨-, -, hu⟩ := hq
        rw [hxa, hxb] at hu
        have hlin := linearFacts_holds hk.2.2.2.2.2
        have hsum : ∀ (F : Linear.Form) (c : Int) (v : Int) (bits : UInt64) {h'' : Heap},
            (∀ x ∈ F.map (·.1), (intValue (ρ x)).isSome) →
            Linear.Form.eval (valuation ρ) F + c = v →
            ((v.natAbs < 2 ^ 53) → SafeIntegers.SafeInt bits v) →
            IndexHolds ((if Linear.entails (linearFacts k.indices) (.le F (maxSafe - c)) &&
              Linear.entails (linearFacts k.indices) (.le (F.scale (-1)) (maxSafe + c)) then valueAtoms F c else []))
              (push (.num bits) ρ) h'' := by
          intro F c v bits h'' hF hv hsafe
          split
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            have h1 : Linear.Form.eval (valuation ρ) F ≤ maxSafe - c := Linear.entails_sound hc.1 hlin
            have h2 : Linear.Form.eval (valuation ρ) (F.scale (-1)) ≤ maxSafe + c := Linear.entails_sound hc.2 hlin
            rw [Linear.Form.eval_scale] at h2
            refine valueAtoms_holds hF ?_
            rw [hv]; apply hsafe; simp only [maxSafe] at h1 h2; omega
          · exact indexHolds_nil _ _
        have hvars : ∀ (G' : Linear.Form), G'.map (·.1) = (fa ++ fb).map (·.1) →
            ∀ x ∈ G'.map (·.1), (intValue (ρ x)).isSome := by
          intro G' hG x hx
          rw [hG, List.map_append] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hva x hx
          · exact hvb x hx
        split
        · -- add
          rw [binop_num_arith (.inl rfl) hu]
          exact hsum (fa ++ fb) (ca + cb)
            ((Linear.Form.eval (valuation ρ) fa + ca) + (Linear.Form.eval (valuation ρ) fb + cb)) _
            (hvars (fa ++ fb) rfl)
            (by rw [Linear.Form.eval_append]; omega)
            (fun hr => SafeIntegers.add_safe hsa hsb hr)
        · -- sub
          rw [binop_num_arith (.inr rfl) hu]
          exact hsum (fa ++ fb.scale (-1)) (ca - cb)
            ((Linear.Form.eval (valuation ρ) fa + ca) - (Linear.Form.eval (valuation ρ) fb + cb)) _
            (hvars (fa ++ fb.scale (-1)) (by simp only [List.map_append, scale_vars]))
            (by rw [Linear.Form.eval_append, Linear.Form.eval_scale]; omega)
            (fun hr => SafeIntegers.sub_safe hsa hsb hr)
        all_goals first
          | (rename_i hop
             rw [binop_num_relational (by first | rfl) hu]
             exact compareAtoms_holds (hvars (fa ++ fb.scale (-1)) (by simp only [List.map_append, scale_vars]))
               (i := Linear.Form.eval (valuation ρ) fa + ca) (j := Linear.Form.eval (valuation ρ) fb + cb)
               (by rw [Linear.Form.eval_append, Linear.Form.eval_scale]; omega) hsa hsb)
          | exact indexHolds_nil _ _
      · exact none_case
    · exact none_case
  | _ => simp only [linearAtoms]; exact none_case

/-! ## The write at a checked index -/

/-- **A write at an index at most the store's length** (`setElem-bounded`).
The object `obj` is a record whose store field, invariant, holds a
homogeneous writable store; that store, at its location now, has `ls`, and
`b` is an index `i ≤ |ls|`. The write reads the store, lands on a present
element or appends (`setElem_store_safe`), and writes the store it yields,
which meets the field's contract, back. -/
theorem boundedWrite_safe [DecidableEq ι] {Ξ : Fam} {G : NormalGraph ι} {R S E : Ty ι}
    {fs vs : List (PropKey × Ty ι)} {os : List (OptionalField (Ty ι))} {ms : List (MethodMembers.Sig (Ty ι))}
    {ks : List KeyBound} {st : List PropKey} {pr : ArrayPresence}
    (hr : Represents G R (.refs fs [] vs os ms ks st)) (hm : (arrayStoreKey, S) ∈ fs)
    (hS : Represents G S (.list ⟨[], [], some E, false, pr⟩ []))
    {obj vv : Tm} {s : Nat} {ls : List (Option Nat)} {b : UInt64} {i : Nat} {n : Nat} {W : WorldT n} {h : Heap}
    (hobj : meaning G R n W obj) (hs : Footprints.storeOf obj = some s) (hl : h[s]? = some (.arr ls))
    (hb : indexOfBits b = some i) (hi : i ≤ ls.length)
    (hv : meaning G E n W vv) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe Ξ nulT n W h (.writeAt arrayStoreKey obj (.setElem (.readAt arrayStoreKey obj) (.num b) vv)) := by
  obtain ⟨flds, l, c, oid, rfl, hf, hlc, hag⟩ :=
    recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨S, hm, rfl⟩) ((represents_raw hr n W _) hobj).1.1
  have hsl : s = l := by
    simp only [Footprints.storeOf, Footprints.fieldsOf] at hs
    rw [hf] at hs; cases hs; rfl
  subst hsl
  have hvval := (meaning_value hv).1
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨w, hwv, hwc⟩ := hh.2 s c hlc
    rw [hl] at hwv; cases hwv
    have hstore : meaning G S p (trunc p (Nat.le_succ p) W) (.arr ls) := (hag p (by omega) _ _).mp (hwc p (by omega))
    have hv' : meaning G E p (trunc p (Nat.le_succ p) W) vv := (meaning_adm G E).down_le (p + 1) p (by omega) W vv hv
    have hpos : positionTy (⟨[], [], some E, false, pr⟩ : Tuple (Ty ι)) i = some E := by
      simp [positionTy]
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, _, WExt_refl _, WorldAdm_trunc _ hw,
      .writeC2 rfl (.setC1 (.readField hf hl)), HeapOk_trunc p W h hh, ?_⟩
    apply Safe_bind (.writeAt arrayStoreKey (.objAt flds .absent oid)) (Step.writeC2 rfl) (Raises.writeC2 rfl)
      p _ h _ (WorldAdm_trunc _ hw) (HeapOk_trunc p W h hh)
      (setElem_store_safe hS rfl hpos hb hi hstore (WorldAdm_trunc _ hw) (HeapOk_trunc p W h hh) hvval hv')
    intro j hj U hx hu heap av hok hav ha'
    have hobjp : meaning G R p (trunc p (Nat.le_succ p) W) (.objAt flds .absent oid) :=
      (meaning_adm G R).down_le (p + 1) p (by omega) W _ hobj
    have hobj' : meaning G R j U (.objAt flds .absent oid) :=
      (meaning_adm G R).mono j _ U hx _ ((meaning_adm G R).down_le p j hj _ _ hobjp)
    obtain ⟨flds', l', c', oid', heq, hf', hl', hag'⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨S, hm, rfl⟩) ((represents_raw hr j U _) hobj').1.1
    cases heq
    exact write_rule (meaning_adm G S) j U heap l' av hav hu hok hf' hl' hag' ha'

/-- Whether an unconditional atom bounds a slot of `i`'s class by the store of
an array of `a`'s class. -/
def boundAtom (k : Knowledge) (a i : Nat) : Bool :=
  k.indices.any fun atom => atom.cond.isNone && match atom.fact with
    | .bound x i' => (HeapLinks.aliases k.links a).contains x && (HeapLinks.aliases k.links i).contains i'
    | _ => false

theorem boundAtom_sound {k : Knowledge} {a i : Nat} {ρ h} (hc : boundAtom k a i = true) (hk : Holds k ρ h) :
    ∃ s ls b idx, Footprints.storeOf (ρ a) = some s ∧ h[s]? = some (.arr ls) ∧ ρ i = .num b ∧
      indexOfBits b = some idx ∧ idx ≤ ls.length := by
  obtain ⟨atom, ha, hm⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hnone, hf⟩ := hm
  have hat := hk.2.2.2.2.2 atom ha fun b hb => by rw [hnone] at hb; cases hb
  cases hfact : atom.fact with
  | bound x i' =>
    rw [hfact] at hf hat
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hf
    rw [← HeapLinks.aliases_eq hk.2.2.1 hf.1, ← HeapLinks.aliases_eq hk.2.2.1 hf.2]
    exact hat
  | index _ => rw [hfact] at hf; cases hf
  | length _ _ => rw [hfact] at hf; cases hf
  | int _ => rw [hfact] at hf; cases hf
  | linear _ => rw [hfact] at hf; cases hf

/-- Whether the linear facts bound a slot of `i`'s class by the length of the
store of an array of `a`'s class: an unconditional length atom `length(x, n)`,
`int(i)` and `int(n)`, and the facts entail `0 ≤ i ≤ n` and `i ≤ 2^32 - 2`. -/
def linearBound (k : Knowledge) (a i : Nat) : Bool :=
  intSlot k.indices i && k.indices.any fun atom => atom.cond.isNone && match atom.fact with
    | .length x n => (HeapLinks.aliases k.links a).contains x && intSlot k.indices n &&
        Linear.entails (linearFacts k.indices) (.le [(i, -1)] 0) &&
        Linear.entails (linearFacts k.indices) (.le [(i, 1), (n, -1)] 0) &&
        Linear.entails (linearFacts k.indices) (.le [(i, 1)] (maxArrayLength - 1))
    | _ => false

theorem indexOfBits_safe {b : UInt64} {j : Int} (hb : SafeIntegers.SafeInt b j) (h0 : 0 ≤ j)
    (h1 : j < maxArrayLength) : indexOfBits b = some j.toNat := by
  rcases hb.2 with ⟨-, he⟩ | ⟨hle, he⟩
  · have : b = bitsOfNat j.natAbs := UInt64.toNat_inj.mp he
    have hm : ((maxArrayLength : Nat) : Int) = 4294967295 := rfl
    have h1' : j < 4294967295 := by omega
    rw [this, IndexNumbers.indexOfBits_bitsOfNat (by omega)]
    congr 1; omega
  · have hj : j = 0 := by omega
    subst hj
    have : b = 0x8000000000000000 := UInt64.toNat_inj.mp (by rw [he]; simp [SafeIntegers.bitsOfNat_zero])
    subst this; rfl

theorem linearBound_sound {k : Knowledge} {a i : Nat} {ρ h} (hc : linearBound k a i = true) (hk : Holds k ρ h) :
    ∃ s ls b idx, Footprints.storeOf (ρ a) = some s ∧ h[s]? = some (.arr ls) ∧ ρ i = .num b ∧
      indexOfBits b = some idx ∧ idx ≤ ls.length := by
  simp only [linearBound, Bool.and_eq_true] at hc
  obtain ⟨hi, hany⟩ := hc
  obtain ⟨atom, ha, hm⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hnone, hf⟩ := hm
  have hat := hk.2.2.2.2.2 atom ha fun b hb => by rw [hnone] at hb; cases hb
  have hlin := linearFacts_holds hk.2.2.2.2.2
  cases hfact : atom.fact with
  | length x n =>
    rw [hfact] at hf hat
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hf
    obtain ⟨⟨⟨⟨hx, hn⟩, e1⟩, e2⟩, e3⟩ := hf
    obtain ⟨s, ls, hs, hl, hnv, hmax⟩ := hat
    have f1 := Linear.entails_sound e1 hlin
    have f2 := Linear.entails_sound e2 hlin
    have f3 := Linear.entails_sound e3 hlin
    simp only [Linear.Fact.Holds, Linear.Form.eval] at f1 f2 f3
    -- the length slot's integer is the store's length
    have hL : SafeIntegers.SafeInt (bitsOfNat ls.length) (ls.length : Int) :=
      ⟨by simp [maxArrayLength] at hmax ⊢; omega, .inl ⟨by omega, by simp⟩⟩
    have hvn : valuation ρ n = ls.length := by simp [valuation, hnv, intValue, SafeIntegers.safeIntOfBits_complete hL]
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (intSlot_sound hk.2.2.2.2.2 hi)
    obtain ⟨b, hb, hsafe⟩ := intValue_safe hj
    have hvi : valuation ρ i = j := by simp [valuation, hj]
    rw [hvi, hvn] at f2; rw [hvi] at f1 f3
    refine ⟨s, ls, b, j.toNat, by rw [← HeapLinks.aliases_eq hk.2.2.1 hx]; exact hs, hl, hb,
      indexOfBits_safe hsafe (by omega) (by have hm : ((maxArrayLength : Nat) : Int) = 4294967295 := rfl; omega),
      by omega⟩
  | index _ | bound _ _ | int _ | linear _ => rw [hfact] at hf; simp at hf

/-- Whether a slot of `i`'s class holds an index at most the length of the
store of an array of `a`'s class: a bound atom states it, or the linear facts do. -/
def bounded (k : Knowledge) (a i : Nat) : Bool := boundAtom k a i || linearBound k a i

theorem bounded_sound {k : Knowledge} {a i : Nat} {ρ h} (hc : bounded k a i = true) (hk : Holds k ρ h) :
    ∃ s ls b idx, Footprints.storeOf (ρ a) = some s ∧ h[s]? = some (.arr ls) ∧ ρ i = .num b ∧
      indexOfBits b = some idx ∧ idx ≤ ls.length := by
  rcases Bool.or_eq_true_iff.mp hc with hc | hc
  · exact boundAtom_sound hc hk
  · exact linearBound_sound hc hk

/-- The slots of a write at a run-time index: `x.[] := x.[]⟦k ↦ v⟧`. -/
def boundedSlots : Tm → Option (Nat × Nat × Nat)
  | .writeAt f (.var a) (.setElem (.readAt f' (.var a')) (.var i) (.var v)) =>
    if f = arrayStoreKey ∧ f' = arrayStoreKey ∧ a = a' then some (a, i, v) else none
  | _ => none

theorem boundedSlots_eq {t : Tm} {a i v : Nat} (h : boundedSlots t = some (a, i, v)) :
    t = .writeAt arrayStoreKey (.var a) (.setElem (.readAt arrayStoreKey (.var a)) (.var i) (.var v)) := by
  unfold boundedSlots at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      cases h; rfl
    · cases h
  · cases h

/-- The store's element type of a homogeneous writable array type: its type a
record whose invariant store field holds one list contract of no required
or optional position. -/
def writableElement (G : NormalGraph ι) (R : Ty ι) : Option (Ty ι) :=
  match expand G R with
  | [.refs fs [] _ _ _ _ _] => match fs.lookup arrayStoreKey with
    | some S => match expand G S with
      | [.list ⟨[], [], some E, false, _⟩ []] => some E
      | _ => none
    | none => none
  | _ => none

theorem writableElement_sound {G : NormalGraph ι} {R E : Ty ι} (h : writableElement G R = some E) :
    ∃ fs vs os ms ks st S pr, Represents G R (.refs fs [] vs os ms ks st) ∧ (arrayStoreKey, S) ∈ fs ∧
      Represents G S (.list ⟨[], [], some E, false, pr⟩ []) := by
  unfold writableElement at h
  split at h
  · rename_i fs vs os ms ks st hR
    split at h
    · rename_i S hS
      split at h
      · rename_i pr hE
        cases h
        exact ⟨fs, vs, os, ms, ks, st, S, pr, hR, PositiveRules.mem_of_lookup hS, hE⟩
      · cases h
    · cases h
  · cases h

/-- Whether the write of a step's evidence is admitted (`setElem-bounded`):
its term `x.[] := x.[]⟦k ↦ v⟧` at the evidence's slots, `x` a homogeneous
writable array whose element type the value's type is below by `sub`, the
knowledge bounding `k` by `x`'s store, and its type `null`. -/
@[nospecialize] def boundedWriteCheck [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (j : Sequent ι) (k : Knowledge) (a i v : Nat) (sub : PositiveCertificates.SubtypeChoices ι) : Bool :=
  boundedSlots j.term == some (a, i, v) && decide (i < j.context.length) &&
    (match j.context[a]?, j.context[v]? with
     | some R, some V => match writableElement G R with
       | some E => PositiveCertificates.checkUsing G images V E sub
       | none => false
     | _, _ => false) &&
    bounded k a i && (expand G j.type == [.nul])

theorem boundedWrite_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' u => Holds (HeapExpressionRules.ordinaryOutput k) (push u ρ) h') n W h (instantiate 0 ρ j.term) := by
  simp only [boundedWriteCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hslots, -⟩, htypes⟩, hbd⟩, hnul⟩ := hc
  rw [boundedSlots_eq hslots]
  split at htypes
  · rename_i R V hR hV
    split at htypes
    · rename_i E hE
      obtain ⟨fs, vs, os, ms, ks, st, S, pr, hrep, hm, hS⟩ := writableElement_sound hE
      obtain ⟨s, ls, b, idx, hs, hl, hb, hidx, hle⟩ := bounded_sound hbd hk
      have hv : meaning G E n W (ρ v) := PositiveCertificates.acceptedUsing htypes n W _ (he.2 v V hV)
      have hsafe := boundedWrite_safe (Ξ := excOf G) hrep hm hS (he.2 a R hR) hs hl hidx hle hv hw hh
      simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero, hb]
      apply HeapObservations.of_value_property (fun _ _ _ u _ => ?_)
      · exact Safe_mono n (fun m _ X u hu => (represents_back (c := .nul) hnul m X u) hu) W h _ hsafe
      · exact ⟨HeapFacts.holds_nil _ _, (shift_holds (v := u) hk).2.1,
          HeapLinks.stable_holds (shift_holds (v := u) hk).2.2.1, (shift_holds (v := u) hk).2.2.2.1,
          elemsHolds_nil _ _, indexHolds_nil _ _⟩
    · cases htypes
  · cases htypes

end Verification.IndexWrites

namespace Verification.HeapExpressionRules
open ProgramCertificates PositiveGraphs HeapObservations
open PositiveCertificates (InstanceImageCheck)

theorem indexHolds_append {as bs : List HeapKnowledge.IndexAtom} {ρ h}
    (ha : HeapKnowledge.IndexHolds as ρ h) (hb : HeapKnowledge.IndexHolds bs ρ h) :
    HeapKnowledge.IndexHolds (as ++ bs) ρ h := fun a hm hc =>
  (List.mem_append.mp hm).elim (fun hm => ha a hm hc) (fun hm => hb a hm hc)

/-- A checker whose steps on slots state the index atoms of their result
(`IndexWrites.stepAtoms`: `length-observed`, `index-mask`, `index-equal`,
`bound-compare`) beside what `base` gives; every step is otherwise `base`'s. -/
@[nospecialize] def Checker.indexing [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums => (base.run j k e codes sums).map fun out =>
    { out with indices := out.indices ++ (IndexWrites.stepAtoms G j.context k j.term ++
        IndexWrites.linearAtoms G j.context k j.term) }
  select := fun j k e codes sums => (base.select j k e codes sums).map fun out =>
    { out with indices := out.indices ++ (IndexWrites.stepAtoms G j.context k j.term ++
        IndexWrites.linearAtoms G j.context k j.term) }
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    simp only [CheckResult.map, Option.map_eq_some_iff] at hc
    obtain ⟨out0, hrun, rfl⟩ := hc
    have hs := base.sound hrun hcodes hsums he hk hw hh
    exact weaken (fun h' u hq => ⟨hq.1.1.1, hq.1.1.2.1, hq.1.1.2.2.1, hq.1.1.2.2.2.1, hq.1.1.2.2.2.2.1,
      indexHolds_append hq.1.1.2.2.2.2.2 (indexHolds_append hq.1.2 hq.2)⟩)
      (IndexWrites.linearAtoms_holds he hk (IndexWrites.stepAtoms_holds he hk hs))

/-- A checker whose `boundedWrite` steps are writes at a checked index
(`IndexWrites.boundedWriteCheck`, `setElem-bounded`), keeping no observation
of the heap; every other step is `base`'s. -/
@[nospecialize] def Checker.boundedWrites [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums => match e with
    | .boundedWrite a i v p =>
      if IndexWrites.boundedWriteCheck G images j k a i v p then pure (ordinaryOutput k) else failure
    | _ => base.run j k e codes sums
  select := fun j k e codes sums => match e with
    | .boundedWrite a i v p =>
      if IndexWrites.boundedWriteCheck G images j k a i v p then pure (ordinaryOutput k) else failure
    | _ => base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    split at hc
    · split at hc
      · rename_i hck
        cases hc
        exact IndexWrites.boundedWrite_sound hck he hk hw hh
      · cases hc
    · exact base.sound hc hcodes hsums he hk hw hh

end Verification.HeapExpressionRules
