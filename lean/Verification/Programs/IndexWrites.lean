import Verification.Semantics.StringPostconditions

import Verification.Programs.HeapExpressionRules
import Verification.Programs.ExpressionEffects
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

/-- A finite execution to a value determines its final heap and value. -/
theorem steps_run {Ξ T : Fam} {Q : Post} {h t h' v steps}
    (run : Steps steps h t h' v) (hv : isVal v = true) :
    ∀ {n W}, SafePost Ξ T Q n W h t →
      SafePost Ξ T (fun heap u => Q heap u ∧ heap = h' ∧ u = v) n W h t := by
  induction run with
  | refl =>
    intro n W hs
    cases n with
    | zero => trivial
    | succ n =>
      rcases hs with (⟨hv', ht, hq⟩ | hr) | ⟨_, _, _, _, _, step, _, _⟩
      · exact .inl (.inl ⟨hv', ht, hq, rfl, rfl⟩)
      · exact absurd hr (val_not_thrown hv)
      · exact False.elim (value_no_step hv step)
  | next step run ih =>
    intro n W hs
    cases n with
    | zero => trivial
    | succ n =>
      rcases hs with (⟨hv', _, _⟩ | hr) | ⟨U, h2, t2, hx, hu, step', hh, hs⟩
      · exact False.elim (value_no_step hv' step)
      · exact absurd step hr.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det step step'
        exact .inr ⟨U, _, _, hx, hu, step', hh, ih hv hs⟩

/-- Slot actuals of a fixed call; the context bounds establish values. -/
def appendSlots (n : Nat) : List Tm → Bool
  | [] => true
  | .var i :: ts => decide (i < n) && appendSlots n ts
  | _ => false

theorem appendSlots_values {n : Nat} {ρ : Env}
    (hv : ∀ i, i < n → isVal (ρ i) = true) {args : List Tm}
    (hs : appendSlots n args = true) :
    ∀ a ∈ instantiateArgs 0 ρ args, isVal a = true := by
  induction args with
  | nil => simp [instantiateArgs]
  | cons t args ih =>
    cases t <;> simp only [appendSlots, Bool.false_eq_true] at hs
    all_goals try contradiction
    case var i =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      intro a ha
      simp only [instantiateArgs, instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hv i hs.1
      · exact ih hs.2 a ha


/-- Array literals with value slots have exactly their number of elements. -/
def literalArrayAtoms (n : Nat) (t : Tm) : List IndexAtom :=
  match t with
  | .letE (.arrLit es) (.makeAt .absent [s, p] [.var 0, .var proto]) =>
    if s == arrayStoreKey && p == CallArguments.protoField && decide (proto < n + 1) &&
        appendSlots n es && decide (es.length ≤ maxArrayLength) then
      [{ fact := .linear (.le [(.length 0, 1)] es.length) },
       { fact := .linear (.le [(.length 0, -1)] (-(es.length : Int))) }]
    else []
  | _ => []

theorem literalArrayAtoms_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {Ξ T : Fam} {Q : Post} {ρ n W h t k}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ρ h) (hh : HeapOk n W h) (hs : SafePost Ξ T Q n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds (literalArrayAtoms Γ.length t) (push u ρ) h' ∧
      (if (literalArrayAtoms Γ.length t).isEmpty then True else
        HeapSeparation.Holds (HeapSeparation.allocate k.separation Γ.length
          (HeapExpressionRules.contractFields G Γ)) (push u ρ) ∧
        IndexHolds (shiftIndices k.indices) (push u ρ) h'))
      n W h (instantiate 0 ρ t) := by
  unfold literalArrayAtoms
  split
  · rename_i es s p proto
    split
    · rename_i hp
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
      obtain ⟨⟨⟨⟨rfl, rfl⟩, hproto⟩, hes⟩, hmax⟩ := hp
      let vs := es.map (instantiate 0 ρ)
      have hvs : ∀ v ∈ vs, isVal v = true := by
        simpa only [vs, instantiateArgs_eq_map] using appendSlots_values
          (fun i hi => (meaning_value (he.2 i _ (List.getElem?_eq_getElem hi))).1) hes
      have hlen : vs.length = es.length := by simp [vs]
      let store := Tm.arr (elemSlots h.length vs.length)
      let heap := h ++ vs
      have hstore : isVal store = true := rfl
      have run : Steps 3 h (instantiate 0 ρ (.letE (.arrLit es)
          (.makeAt .absent [arrayStoreKey, CallArguments.protoField] [.var 0, .var proto])))
          (heap ++ [store, (push store ρ) proto] ++ [.nul])
          (.objAt (slots heap.length [arrayStoreKey, CallArguments.protoField]) .absent (heap.length + 2)) := by
        simp only [instantiate, instantiateArgs_eq_map, List.map_cons, List.map_nil]
        apply Steps.next (Step.letC (Step.arrAlloc hvs (by omega)))
        apply Steps.next (Step.letV hstore)
        have hb := instantiate_beta ρ he.1 store
          (.makeAt .absent [arrayStoreKey, CallArguments.protoField] [.var 0, .var proto]) 0
        simp only [instantiate, instantiateArgs_eq_map, List.map_cons, List.map_nil] at hb
        rw [hb]
        simp only [Nat.not_lt_zero, if_false, Nat.sub_zero]
        apply Steps.next (Step.makeFields ?_ rfl) Steps.refl
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hstore
        · cases proto with
          | zero => exact hstore
          | succ i => exact (meaning_value (he.2 i _ (List.getElem?_eq_getElem (by omega)))).1
      refine weaken (fun heap' u hq => ?_) (steps_run run rfl hs)
      obtain ⟨hq, rfl, rfl⟩ := hq
      refine ⟨hq, ?_, ?_⟩
      · have hl : termValue (push (.objAt (slots heap.length [arrayStoreKey, CallArguments.protoField]) .absent (heap.length + 2)) ρ)
            (heap ++ [store, (push store ρ) proto] ++ [.nul]) (.length 0) = some (es.length : Int) := by
          simp [termValue_length, push, lengthOf, Footprints.storeOf, Footprints.fieldsOf, slots,
            store, elemSlots, hlen, hmax, arrayStoreKey, CallArguments.protoField]
        simp only [termValue_length, List.append_assoc, List.cons_append, List.nil_append] at hl
        intro a ha _
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;>
          simp [IndexFact.HoldsAt, Linear.Fact.vars, Linear.Fact.Holds, Linear.Form.eval, termValuation, hl]
      · refine ⟨HeapSeparation.allocate_holds hk.2.2.2.1
          (HeapExpressionRules.fresh_apart_from he hh (by simp [heap])), ?_⟩
        exact indexHolds_extend [.nul] (indexHolds_extend [store, (push store ρ) proto]
          (indexHolds_extend vs (shift_holds hk).2.2.2.2.2))
    · exact weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _, trivial⟩) hs
  · exact weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _, trivial⟩) hs

/-- A string's length gives, where it returns, its count of UTF-16 code
units, at most `maxStringLength`, in the heap it started in: a longer model
string throws (`Step.lenStrThrow`). -/
theorem len_str_run {Ξ T : Fam} {Q : Post} {str : String} :
    ∀ {n W h}, SafePost Ξ T Q n W h (.lenOf (.str str)) →
      SafePost Ξ T (fun h' u => Q h' u ∧ h' = h ∧ u = .num (bitsOfNat (utf16Units str).length) ∧
        (utf16Units str).length ≤ maxStringLength) n W h (.lenOf (.str str)) := by
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
      | lenStr hl =>
        cases n with
        | zero => trivial
        | succ m =>
          rcases hs with (⟨hval, ht, hq⟩ | ⟨u, hr, -⟩) | ⟨U', h'', t'', -, -, step', -, -⟩
          · exact .inl (.inl ⟨hval, ht, hq, rfl, rfl, hl⟩)
          · exact absurd (raises_not_val hr) (by simp [isVal])
          · exact absurd step' (value_no_step rfl)
      | lenStrThrow _ => exact throw_post rfl hs

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
  | bound _ _ _ => rw [hfact] at hf; cases hf
  | int _ => rw [hfact] at hf; cases hf
  | linear _ => rw [hfact] at hf; cases hf
  | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ => rw [hfact] at hf; cases hf

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
    | bound _ _ _ => rw [hfact] at hm; cases hm
    | int _ => rw [hfact] at hm; cases hm
    | linear _ => rw [hfact] at hm; cases hm
    | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ => rw [hfact] at hm; cases hm
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

/-- Whether slot `s` holds a string: its type answers the string test. -/
def stringSlot (G : NormalGraph ι) (Γ : List (Ty ι)) (s : Nat) : Bool :=
  match Γ[s]? with
  | some S => G.plainTy S && (expand G S).all fun c => tagClause .isStr c == some true
  | none => false

/-- The safe integer a slot's type admits alone: a plain type whose one
clause is that number's literal. -/
def litSlot (G : NormalGraph ι) (Γ : List (Ty ι)) (a : Nat) : Option Int :=
  match Γ[a]? with
  | some S => if G.plainTy S then match expand G S with
      | [.numLit b] => SafeIntegers.safeIntOfBits b
      | _ => none else none
  | none => none

theorem litSlot_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {a : Nat} {i : Int} {ρ n W}
    (hc : litSlot G Γ a = some i) (he : EnvOk G Γ ρ n W) : ∃ b, ρ a = .num b ∧ SafeIntegers.SafeInt b i := by
  unfold litSlot at hc
  split at hc
  · rename_i S hS
    split at hc
    · rename_i hp
      split at hc
      · rename_i b hx
        have hm := (expand_sem G S hp n W (ρ a)).mp (he.2 a S hS)
        rw [hx] at hm
        obtain ⟨c, hc', hsem⟩ := hm
        simp only [List.mem_singleton] at hc'
        subst hc'
        exact ⟨b, by simpa [clauseSem, rowSem, semWithArgs] using hsem.1, SafeIntegers.safeIntOfBits_sound hc⟩
      · cases hc
    · cases hc
  · cases hc

theorem stringSlot_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {s : Nat} {ρ n W}
    (hc : stringSlot G Γ s = true) (he : EnvOk G Γ ρ n W) : ∃ str, ρ s = .str str := by
  unfold stringSlot at hc
  split at hc
  · rename_i S hS
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
    have hstr := answers_sound (q := true) ⟨hc.1, hc.2⟩ (he.2 s S hS)
    cases hv : ρ s <;> simp [hv, tagHolds] at hstr
    exact ⟨_, rfl⟩
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
         | some q => if indexed k a then (lengthsOf k b).map fun x => ⟨.bound (x + 1) (a + 1) false, some 0, !q⟩ else []
         | none => []) ++
        (match boundAnswerOf op false with
         | some q => if indexed k b then (lengthsOf k a).map fun x => ⟨.bound (x + 1) (b + 1) false, some 0, !q⟩ else []
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
              exact ⟨s, ls, x, i, by simpa [push] using hs', hls, by simpa [push] using hx, hix, by simpa using hle⟩
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
              exact ⟨s, ls, x, i, by simpa [push] using hs', hls, by simpa [push] using hx, hix, by simpa using hle⟩
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

/-- A constant suggested by a singleton upper bound and checked in both
 directions. Lowering holds literal operands in slots before arithmetic. -/
def knownConstant (k : Knowledge) (a : Nat) : Option Int :=
  match k.indices.findSome? (fun atom => match atom.fact with
    | .linear (.le [(t, 1)] c) => if t == .value a then some c else none
    | _ => none) with
  | none => none
  | some c => if entailsKnown k.indices (valueFact (.le [(a, 1)] c)) &&
      entailsKnown k.indices (valueFact (.le [(a, -1)] (-c))) then some c else none

theorem knownConstant_sound {k : Knowledge} {a : Nat} {c : Int} {ρ h}
    (hc : knownConstant k a = some c) (hk : Holds k ρ h) : valuation ρ a = c := by
  simp only [knownConstant] at hc
  split at hc
  · cases hc
  · split at hc
    · rename_i hb
      simp only [Bool.and_eq_true] at hb
      cases hc
      have h1 := holds_valueFact.mp (entailsKnown_sound hk.2.2.2.2.2 hb.1)
      have h2 := holds_valueFact.mp (entailsKnown_sound hk.2.2.2.2.2 hb.2)
      simp only [Linear.Fact.Holds, Linear.Form.eval] at h1 h2
      omega
    · cases hc

/-- An operand's value as a linear form over the input slots plus a constant. -/
def operandForm (k : Knowledge) (constants : Bool) : Tm → Option (Linear.Form Nat × Int)
  | .var a => if intSlot k.indices a then
      match if constants then knownConstant k a else none with
      | some c => some ([], c)
      | none => some ([(a, 1)], 0)
    else none
  | .num b => (SafeIntegers.safeIntOfBits b).map fun i => ([], i)
  | _ => none

/-- Whether a term is a slot of the context or a literal number. -/
def operandIn (Γ : List (Ty ι)) : Tm → Bool
  | .var x => decide (x < Γ.length)
  | .num _ => true
  | _ => false

/-- A form over the input slots, read over the output slots, one higher. -/
def shiftForm (F : Linear.Form Nat) : Linear.Form Nat := F.map fun (x, c) => (x + 1, c)

/-- The atoms stating that the result, slot 0, is the value of `F + c` over the
input slots, a safe integer. -/
def valueAtoms (F : Linear.Form Nat) (c : Int) : List IndexAtom :=
  [⟨.int 0, none, false⟩, ⟨.linear (valueFact (.le ((0, 1) :: shiftForm (F.scale (-1))) c)), none, false⟩,
    ⟨.linear (valueFact (.le ((0, -1) :: shiftForm F) (-c))), none, false⟩]

/-- Whether a sum is a string's length plus one: one operand a slot the
knowledge states equal to a string's length, the other the constant `1`. -/
def stringLengthPlusOne (k : Knowledge) (fa : Linear.Form Nat) (ca : Int) (fb : Linear.Form Nat) (cb : Int) : Bool :=
  let lengths := k.indices.filterMap fun a => if a.cond.isNone then match a.fact with
    | .linear (.le [(.value y, 1), (.strLength s, -1)] 0) => some (y, s, true)
    | .linear (.le [(.strLength s, -1), (.value y, 1)] 0) => some (y, s, true)
    | .linear (.le [(.value y, -1), (.strLength s, 1)] 0) => some (y, s, false)
    | .linear (.le [(.strLength s, 1), (.value y, -1)] 0) => some (y, s, false)
    | _ => none else none
  let isLength := fun (x : Nat) => lengths.any fun (y, s, up) =>
    up && y == x && lengths.contains (y, s, false)
  let isOne := fun (f : Linear.Form Nat) (c : Int) => match f with
    | [] => c == 1
    | [(y, 1)] => c == 0 && knownConstant k y == some 1
    | _ => false
  match fa with
  | [(x, 1)] => ca == 0 && isLength x && isOne fb cb ||
      (match fb with | [(x', 1)] => cb == 0 && isLength x' && isOne fa ca | _ => false)
  | _ => match fb with | [(x, 1)] => cb == 0 && isLength x && isOne fa ca | _ => false

/-- The atoms of a sum of two nonnegative safe integers bounded by `2^53`:
each atom of the exact sum's (`valueAtoms`), or the result is the double
`2^53` (`IndexFact.pastSafe`, `SafeIntegers.add_two53`). -/
def pastSafeAtoms (F : Linear.Form Nat) (c : Int) : List IndexAtom :=
  (valueAtoms F c).map fun a => { a with fact := .either a.fact (.pastSafe 0) }

/-- The atoms of a comparison's two answers, on the result slot 0, of operands
whose difference is `D + c`: the fact each answer gives, conditional on it. -/
def compareAtoms (op : Arith) (D : Linear.Form Nat) (c : Int) : List IndexAtom :=
  let pos := shiftForm D
  let neg := shiftForm (D.scale (-1))
  -- (fact on `true`, fact on `false`)
  let facts : Option (Linear.Fact Nat × Linear.Fact Nat) := match op with
    | .lt => some (.le pos (-1 - c), .le neg c)
    | .le => some (.le pos (-c), .le neg (c - 1))
    | .gt => some (.le neg (c - 1), .le pos (-c))
    | .ge => some (.le neg c, .le pos (-1 - c))
    | _ => none
  match facts with
  | some (t, f) => [⟨.linear (valueFact t), some 0, false⟩, ⟨.linear (valueFact f), some 0, true⟩]
  | none => []

/-- The atoms of a strict equality's answers, on the result slot 0, of
operands whose difference is `D + c`: `D + c = 0`, as two facts, on `true`,
and `D + c ≠ 0` on `false`. -/
def equalAtoms (D : Linear.Form Nat) (c : Int) : List IndexAtom :=
  [⟨.linear (valueFact (.le (shiftForm D) (-c))), some 0, false⟩,
    ⟨.linear (valueFact (.le (shiftForm (D.scale (-1))) c)), some 0, false⟩,
    ⟨.linear (valueFact (.ne (shiftForm D) (-c))), some 0, true⟩]

/-- A copy of slot `a` restates the atoms conditional on `a` as conditional on
the copy, the result slot 0: the copy holds the same value. -/
def copiedAtoms (k : Knowledge) (a : Nat) : List IndexAtom :=
  (k.indices.filter (·.cond == some a)).filterMap fun atom =>
    (atom.fact.mapM (fun i => some (i + 1))).map fun F => { atom with fact := F, cond := some 0 }

theorem copiedAtoms_holds {k : Knowledge} {a : Nat} {ρ h} (hk : Holds k ρ h) :
    IndexHolds (copiedAtoms k a) (push (ρ a) ρ) h := by
  intro atom' hat hc
  obtain ⟨atom, hat0, hm⟩ := List.mem_filterMap.mp hat
  obtain ⟨hat0, hcond⟩ := List.mem_filter.mp hat0
  simp only [beq_iff_eq] at hcond
  obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp hm
  have hsrc := hk.2.2.2.2.2 atom hat0 (fun b hb => by
    rw [hcond] at hb; cases hb
    simpa [push] using hc 0 rfl)
  exact (IndexFact.holdsAt_mapM hF (fun s _ t ht => by cases ht; rfl)).mpr hsrc

/-- A copy of slot `a` restates the sum rule's atoms on `a`
(`pastSafeAtoms`), unconditional disjunctions whose right side states `a` the
double `2^53`, on the copy, the result slot 0: the copy holds the same value. -/
def pastCopies (k : Knowledge) (a : Nat) : List IndexAtom :=
  k.indices.filterMap fun atom => match atom.cond, atom.fact with
    | none, .either _ (.pastSafe b) => if b == a then
        (atom.fact.mapM (fun i => some (if i == a then 0 else i + 1))).map fun F => { atom with fact := F }
      else none
    | _, _ => none

theorem pastCopies_holds {k : Knowledge} {a : Nat} {ρ h} (hk : Holds k ρ h) :
    IndexHolds (pastCopies k a) (push (ρ a) ρ) h := by
  intro atom' hat hc
  obtain ⟨atom, hat0, hm⟩ := List.mem_filterMap.mp hat
  split at hm
  · rename_i _ b hcn hf
    split at hm
    · obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp hm
      have hsrc := hk.2.2.2.2.2 atom hat0 (fun c hcc => by rw [hcn] at hcc; cases hcc)
      refine (IndexFact.holdsAt_mapM hF (fun s _ t ht => ?_)).mpr hsrc
      cases ht
      by_cases hs : s = a
      · subst hs; simp [push]
      · simp [hs, push]
    · cases hm
  · cases hm

theorem indexHolds_cat {as bs : List IndexAtom} {ρ h}
    (ha : IndexHolds as ρ h) (hb : IndexHolds bs ρ h) : IndexHolds (as ++ bs) ρ h := fun a hm hc =>
  (List.mem_append.mp hm).elim (fun hm => ha a hm hc) (fun hm => hb a hm hc)

/-- The checked range in which signed bitwise conversion preserves an operand. -/
def smallOperand (k : Knowledge) (F : Linear.Form Nat) (c : Int) : Bool :=
  entailsKnown k.indices (valueFact (.le (F.scale (-1)) c)) &&
    entailsKnown k.indices (valueFact (.le F (2 ^ 31 - 1 - c)))

/-- A bitwise result's integer range and its relation to the left operand. -/
def bitAtoms (op : Arith) (F : Linear.Form Nat) (c d : Int) : List IndexAtom :=
  match op with
  | .shr => [⟨.int 0, none, false⟩,
      ⟨.linear (valueFact (.le [(0, -1)] 0)), none, false⟩,
      ⟨.linear (valueFact (.le ((0, 2 ^ d.toNat) :: shiftForm (F.scale (-1))) c)), none, false⟩,
      ⟨.linear (valueFact (.le ((0, -(2 ^ d.toNat)) :: shiftForm F) (2 ^ d.toNat - 1 - c))), none, false⟩]
  | _ => [⟨.int 0, none, false⟩,
      ⟨.linear (valueFact (.le [(0, -1)] 0)), none, false⟩,
      ⟨.linear (valueFact (.le [(0, 1)] d)), none, false⟩,
      ⟨.linear (valueFact (.le ((0, 1) :: shiftForm (F.scale (-1))) c)), none, false⟩]

/-- String-only addition operands whose types establish string membership. -/
@[nospecialize] def concatOperands (G : NormalGraph ι) (Γ : List (Ty ι))
    (op : Arith) : Tm → Tm → Option (Nat × Nat)
  | .var a, .var b => if op == .add && stringSlot G Γ a && stringSlot G Γ b then some (a, b) else none
  | _, _ => none

/-- Exact UTF-16 length on normal return from string addition. -/
def concatAtoms (a b : Nat) : List IndexAtom :=
  [⟨.linear (.le [(.strLength 0, 1), (.strLength (a + 1), -1), (.strLength (b + 1), -1)] 0), none, false⟩,
   ⟨.linear (.le [(.strLength 0, -1), (.strLength (a + 1), 1), (.strLength (b + 1), 1)] 0), none, false⟩]

theorem concatOperands_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {op a b x y}
    (hc : concatOperands G Γ op a b = some (x, y)) :
    op = .add ∧ a = .var x ∧ b = .var y ∧ stringSlot G Γ x = true ∧ stringSlot G Γ y = true := by
  cases a <;> cases b <;> simp only [concatOperands] at hc
  all_goals first | contradiction | skip
  split at hc
  · simp only [Bool.and_eq_true] at *
    cases hc
    rename_i h
    have hop : op = .add := by cases op <;> simp_all (config := { decide := true })
    exact ⟨hop, rfl, rfl, h.1.2, h.2⟩
  · contradiction

/-- The linear atoms a step on slots states of its result. -/
def linearAtoms (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Tm → List IndexAtom
  | .num b => match SafeIntegers.safeIntOfBits b with
    | some i => valueAtoms [] i
    | none => []
  | .var a =>
    (if a < Γ.length ∧ intSlot k.indices a = true then valueAtoms [(a, 1)] 0 else []) ++
      (match litSlot G Γ a with | some i => valueAtoms [] i | none => []) ++
      (if a < Γ.length then copiedAtoms k a ++ pastCopies k a else [])
  | .lenOf (.var s) =>
    if storeSlot G Γ s then
      [⟨.int 0, none, false⟩, ⟨.linear (valueFact (.le [(0, -1)] 0)), none, false⟩,
        ⟨.linear (valueFact (.le [(0, 1)] maxArrayLength)), none, false⟩]
    else if stringSlot G Γ s then
      [⟨.int 0, none, false⟩,
        ⟨.linear (.le [(.value 0, 1), (.strLength (s + 1), -1)] 0), none, false⟩,
        ⟨.linear (.le [(.value 0, -1), (.strLength (s + 1), 1)] 0), none, false⟩]
    else []
  | .arith op a b =>
    match concatOperands G Γ op a b with
    | some (x, y) => concatAtoms x y
    | none =>
      if operandIn Γ a && operandIn Γ b then
        match operandForm k (op == .mul || op == .shr || op == .bitAnd) a, operandForm k (op == .mul || op == .shr || op == .bitAnd) b with
        | some (fa, ca), some (fb, cb) =>
          let sum := fun (F : Linear.Form Nat) (c : Int) =>
            if entailsKnown k.indices (valueFact (.le F (maxSafe - c))) &&
                entailsKnown k.indices (valueFact (.le (F.scale (-1)) (maxSafe + c))) then valueAtoms F c else []
          match op with
          | .add => if !(entailsKnown k.indices (valueFact (.le (fa ++ fb) (maxSafe - (ca + cb)))) &&
                entailsKnown k.indices (valueFact (.le ((fa ++ fb).scale (-1)) (maxSafe + (ca + cb))))) &&
                entailsKnown k.indices (valueFact (.le ((fa ++ fb).scale (-1)) (maxSafe + (ca + cb)))) &&
                entailsKnown k.indices (valueFact (.le (fa ++ fb) (maxSafe + 1 - (ca + cb)))) &&
                entailsKnown k.indices (valueFact (.le (fa.scale (-1)) ca)) &&
                entailsKnown k.indices (valueFact (.le (fb.scale (-1)) cb)) &&
                stringLengthPlusOne k fa ca fb cb then
                pastSafeAtoms (fa ++ fb) (ca + cb)
              else sum (fa ++ fb) (ca + cb)
          | .sub => sum (fa ++ fb.scale (-1)) (ca - cb)
          -- A zero factor gives the constant `0`, a form naming no slot.
          | .mul => if fa = [] then sum (if ca = 0 then [] else fb.scale ca) (ca * cb)
            else if fb = [] then sum (if cb = 0 then [] else fa.scale cb) (ca * cb) else []
          | .shr => if fb = [] ∧ 0 ≤ cb ∧ cb < 32 ∧ smallOperand k fa ca then bitAtoms op fa ca cb else []
          | .bitAnd => if fb = [] ∧ 0 ≤ cb ∧ cb < 2 ^ 31 ∧ smallOperand k fa ca then bitAtoms op fa ca cb else []
          | .lt | .le | .gt | .ge => compareAtoms op (fa ++ fb.scale (-1)) (ca - cb)
          | .eq => equalAtoms (fa ++ fb.scale (-1)) (ca - cb)
          | _ => []
        | _, _ => []
      else []
  | _ => []

theorem eval_shiftForm (F : Linear.Form Nat) (u : Val) (ρ : Env) :
    Linear.Form.eval (valuation (push u ρ)) (shiftForm F) = Linear.Form.eval (valuation ρ) F := by
  induction F with
  | nil => rfl
  | cons p t ih => obtain ⟨x, c⟩ := p; simp only [shiftForm, List.map_cons, Linear.Form.eval] at ih ⊢; rw [ih]; rfl

theorem shiftForm_vars (F : Linear.Form Nat) : (shiftForm F).map (·.1) = (F.map (·.1)).map (· + 1) := by
  simp [shiftForm, Function.comp_def]

theorem scale_vars (k : Int) (F : Linear.Form Nat) : (F.scale k).map (·.1) = F.map (·.1) := by
  simp [Linear.Form.scale, Function.comp_def]

/-- What an operand denotes: a value whose safe integer is `F + c` at the input slots. -/
theorem operandForm_sound {k : Knowledge} {constants : Bool} {t : Tm} {F : Linear.Form Nat} {c : Int} {ρ h}
    (ho : operandForm k constants t = some (F, c)) (hk : Holds k ρ h) :
    (∀ x ∈ F.map (·.1), (intValue (ρ x)).isSome) ∧
      ∃ b, instantiate 0 ρ t = .num b ∧ SafeIntegers.SafeInt b (Linear.Form.eval (valuation ρ) F + c) := by
  cases t with
  | var a =>
    simp only [operandForm] at ho
    split at ho
    · rename_i hi
      have hs := intSlot_sound hk.2.2.2.2.2 hi
      obtain ⟨i, hi'⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨b, hb, hsafe⟩ := intValue_safe hi'
      split at ho
      · rename_i c hc
        cases ho
        have hc' : knownConstant k a = some c := by
          cases constants <;> simp_all
        have he := knownConstant_sound hc' hk
        simp only [valuation, hi', Option.getD_some] at he
        exact ⟨by simp, b, by simp [instantiate, hb], by simpa only [Linear.Form.eval, Int.zero_add, ← he] using hsafe⟩
      · cases ho
        refine ⟨by simp [hs], b, by simp [instantiate, hb], ?_⟩
        simp only [Linear.Form.eval, valuation, hi', Option.getD_some]
        simpa using hsafe
    · cases ho
  | num b =>
    simp only [operandForm, Option.map_eq_some_iff, Prod.mk.injEq] at ho
    obtain ⟨i, hi, rfl, rfl⟩ := ho
    exact ⟨by simp, b, rfl, by simpa [Linear.Form.eval] using SafeIntegers.safeIntOfBits_sound hi⟩
  | _ => simp [operandForm] at ho

theorem valueAtoms_holds {F : Linear.Form Nat} {c : Int} {ρ h} {b : UInt64}
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
  · refine IndexFact.holdsAt_valueFact.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Linear.Fact.vars, List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hi0
      · rw [shiftForm_vars, scale_vars, ← shiftForm_vars] at hx; exact hvars x hx
    · show Linear.Form.eval _ _ ≤ c
      simp only [Linear.Form.eval, eval_shiftForm, Linear.Form.eval_scale, h0]
      omega
  · refine IndexFact.holdsAt_valueFact.mpr ⟨?_, ?_⟩
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

theorem binop_num_arith {op : Arith} {x y : UInt64} {u : Tm} (hop : op = .add ∨ op = .sub ∨ op = .mul)
    (h : binop op (.num x) (.num y) = some u) : u = .num (arithBits op x y) := by
  rcases hop with rfl | rfl | rfl <;> simp [binop, Arith.relational] at h <;> exact h.symm

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
theorem compareAtoms_holds {op : Arith} {D : Linear.Form Nat} {c : Int} {ρ h} {x y : UInt64} {i j : Int}
    (hD : ∀ z ∈ D.map (·.1), (intValue (ρ z)).isSome)
    (hdiff : Linear.Form.eval (valuation ρ) D + c = i - j)
    (hx : SafeIntegers.SafeInt x i) (hy : SafeIntegers.SafeInt y j) :
    IndexHolds (compareAtoms op D c) (push (boolVal (relationHolds op (doubleOrder x y))) ρ) h := by
  rw [SafeIntegers.doubleOrder_safe hx hy]
  generalize hr : relationHolds op (some (compare i j)) = r
  have hans : answerHolds op r (i - j) := hr ▸ answer_sound op i j
  have hvars : ∀ (F : Linear.Form Nat), F.map (·.1) = D.map (·.1) →
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
         exact IndexFact.holdsAt_valueFact.mpr ⟨fun z hz => by first | exact hpos z hz | exact hneg z hz, by
           show _ ≤ _; first | (rw [ep]; simp only [answerHolds] at hans; omega) | (rw [en]; simp only [answerHolds] at hans; omega)⟩
       · have := hb false (hq rfl); subst this
         exact IndexFact.holdsAt_valueFact.mpr ⟨fun z hz => by first | exact hpos z hz | exact hneg z hz, by
           show _ ≤ _; first | (rw [ep]; simp only [answerHolds] at hans; omega) | (rw [en]; simp only [answerHolds] at hans; omega)⟩)
    | exact absurd ha (by simp)

/-- A strict equality's answers of two safe integers give their difference
zero on `true` and nonzero on `false`. -/
theorem equalAtoms_holds {D : Linear.Form Nat} {c : Int} {ρ h} {x y : UInt64} {i j : Int}
    (hD : ∀ z ∈ D.map (·.1), (intValue (ρ z)).isSome)
    (hdiff : Linear.Form.eval (valuation ρ) D + c = i - j)
    (hx : SafeIntegers.SafeInt x i) (hy : SafeIntegers.SafeInt y j) :
    IndexHolds (equalAtoms D c) (push (boolVal (numberEqual x y)) ρ) h := by
  have hvars : ∀ (F : Linear.Form Nat), F.map (·.1) = D.map (·.1) →
      ∀ z ∈ (shiftForm F).map (·.1), (intValue (push (boolVal (numberEqual x y)) ρ z)).isSome := by
    intro F hF z hz
    rw [shiftForm_vars, hF] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    simpa [push] using hD w hw
  intro a ha hc
  have hq := hc 0
  simp only [equalAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · have htrue : numberEqual x y = true := by
      have := hq rfl
      cases hn : numberEqual x y <;> simp_all [push, boolVal, tagHolds]
    have hij := SafeIntegers.numberEqual_safe hx hy htrue
    refine IndexFact.holdsAt_valueFact.mpr ⟨hvars D rfl, ?_⟩
    show Linear.Form.eval _ _ ≤ _
    rw [eval_shiftForm]; omega
  · have htrue : numberEqual x y = true := by
      have := hq rfl
      cases hn : numberEqual x y <;> simp_all [push, boolVal, tagHolds]
    have hij := SafeIntegers.numberEqual_safe hx hy htrue
    refine IndexFact.holdsAt_valueFact.mpr ⟨hvars (D.scale (-1)) (scale_vars _ _), ?_⟩
    show Linear.Form.eval _ _ ≤ _
    rw [eval_shiftForm, Linear.Form.eval_scale]; omega
  · have hfalse : numberEqual x y = false := by
      have := hq rfl
      cases hn : numberEqual x y <;> simp_all [push, boolVal, tagHolds]
    have hij : i ≠ j := fun he => by
      subst he
      rw [SafeIntegers.numberEqual_of_safe hx hy] at hfalse
      cases hfalse
    refine IndexFact.holdsAt_valueFact.mpr ⟨hvars D rfl, ?_⟩
    show Linear.Form.eval _ _ ≠ _
    rw [eval_shiftForm]; omega

theorem binop_num_eq {x y : UInt64} {u : Tm} (h : binop .eq (.num x) (.num y) = some u) :
    u = boolVal (numberEqual x y) := by
  simp [binop, strictEquals, sameValue, isVal, isPrim] at h
  exact h.symm

theorem binop_num_relational {op : Arith} {x y : UInt64} {u : Tm} (hop : op.relational = true)
    (h : binop op (.num x) (.num y) = some u) : u = boolVal (relationHolds op (doubleOrder x y)) :=
  binop_relational hop h

theorem smallOperand_sound {k : Knowledge} {F : Linear.Form Nat} {c : Int} {ρ h}
    (hc : smallOperand k F c = true) (hk : Holds k ρ h) :
    0 ≤ Linear.Form.eval (valuation ρ) F + c ∧ Linear.Form.eval (valuation ρ) F + c < 2 ^ 31 := by
  simp only [smallOperand, Bool.and_eq_true] at hc
  have hlo := holds_valueFact.mp (entailsKnown_sound hk.2.2.2.2.2 hc.1)
  have hhi := holds_valueFact.mp (entailsKnown_sound hk.2.2.2.2.2 hc.2)
  simp only [Linear.Fact.Holds, Linear.Form.eval_scale] at hlo hhi
  omega

theorem resultLinear_holds {F : Linear.Form Nat} {c a r : Int} {ρ h} {b : UInt64}
    (hF : ∀ x ∈ F.map (·.1), (intValue (ρ x)).isSome)
    (hb : SafeIntegers.SafeInt b r) (hle : a * r + Linear.Form.eval (valuation ρ) F ≤ c) :
    IndexFact.HoldsAt (.linear (valueFact (.le ((0, a) :: shiftForm F) c))) (push (.num b) ρ) h := by
  have h0 : intValue (push (.num b) ρ 0) = some r := intValue_num hb
  refine IndexFact.holdsAt_valueFact.mpr ⟨?_, ?_⟩
  · intro x hx
    simp only [Linear.Fact.vars, List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [h0]
    · rw [shiftForm_vars] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      simpa [push] using hF y hy
  · simpa [Linear.Fact.Holds, Linear.Form.eval, eval_shiftForm, valuation, h0] using hle

theorem bitAtoms_holds {op : Arith} {F : Linear.Form Nat} {c d : Int} {ρ h} {x y : UInt64}
    (hF : ∀ a ∈ F.map (·.1), (intValue (ρ a)).isSome)
    (hx : SafeIntegers.SafeInt x (Linear.Form.eval (valuation ρ) F + c))
    (hy : SafeIntegers.SafeInt y d)
    (hi : 0 ≤ Linear.Form.eval (valuation ρ) F + c)
    (hlt : Linear.Form.eval (valuation ρ) F + c < 2 ^ 31)
    (hd : 0 ≤ d) (hop : (op = .shr ∧ d < 32) ∨ (op = .bitAnd ∧ d < 2 ^ 31)) :
    IndexHolds (bitAtoms op F c d) (push (.num (arithBits op x y)) ρ) h := by
  have hneg : ∀ a ∈ (F.scale (-1)).map (·.1), (intValue (ρ a)).isSome := by
    simpa only [scale_vars] using hF
  rcases hop with ⟨rfl, hdk⟩ | ⟨rfl, hdm⟩
  · have hb := SafeIntegers.shr_safe hx hy hi hlt hd hdk
    have hp : (0 : Int) < 2 ^ d.toNat := Int.pow_pos (by decide)
    have hr0 := Int.ediv_nonneg hi (Int.le_of_lt hp)
    have hr := Int.emod_nonneg (Linear.Form.eval (valuation ρ) F + c) (Int.ne_of_gt hp)
    have hrlt := Int.emod_lt_of_pos (Linear.Form.eval (valuation ρ) F + c) hp
    have he := Int.emod_add_mul_ediv (Linear.Form.eval (valuation ρ) F + c) (2 ^ d.toNat)
    intro atom hat _
    simp only [bitAtoms, List.mem_cons, List.not_mem_nil, or_false] at hat
    rcases hat with rfl | rfl | rfl | rfl
    · simp [IndexFact.HoldsAt, push, intValue_num hb]
    · exact resultLinear_holds (F := []) (by simp) hb (by simp [Linear.Form.eval]; omega)
    · apply resultLinear_holds hneg hb
      rw [Linear.Form.eval_scale]; omega
    · apply resultLinear_holds hF hb
      simp only [Int.neg_mul]
      omega
  · obtain ⟨r, hb, hr0, hri, hrm⟩ := SafeIntegers.bitAnd_safe hx hy hi hlt hd hdm
    intro atom hat _
    simp only [bitAtoms, List.mem_cons, List.not_mem_nil, or_false] at hat
    rcases hat with rfl | rfl | rfl | rfl
    · simp [IndexFact.HoldsAt, push, intValue_num hb]
    · exact resultLinear_holds (F := []) (by simp) hb (by simp [Linear.Form.eval]; omega)
    · exact resultLinear_holds (F := []) (by simp) hb (by simpa [Linear.Form.eval] using hrm)
    · apply resultLinear_holds hneg hb
      rw [Linear.Form.eval_scale]; omega

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
    by_cases ha : a < Γ.length
    · simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero, ha, true_and, if_true] at hs ⊢
      refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (value_run (hval a ha) hs)
      obtain ⟨-, rfl, rfl⟩ := hq
      refine indexHolds_cat (indexHolds_cat ?_ ?_) (indexHolds_cat (copiedAtoms_holds hk) (pastCopies_holds hk))
      rotate_left
      · split
        · rename_i i hl
          obtain ⟨b, hb, hsafe⟩ := litSlot_sound hl he
          rw [hb]
          exact valueAtoms_holds (by simp) (by simpa [Linear.Form.eval] using hsafe)
        · exact indexHolds_nil _ _
      split
      · rename_i hi
        have hs' := intSlot_sound hk.2.2.2.2.2 hi
        obtain ⟨i, hi'⟩ := Option.isSome_iff_exists.mp hs'
        obtain ⟨b, hb, hsafe⟩ := intValue_safe hi'
        rw [hb]
        refine valueAtoms_holds (by simp [hs']) ?_
        simpa [Linear.Form.eval, valuation, hi'] using hsafe
      · exact indexHolds_nil _ _
    · have hl : litSlot G Γ a = none := by
        simp [litSlot, List.getElem?_eq_none (show Γ.length ≤ a by omega)]
      simp only [ha, false_and, if_false, List.append_nil, hl]; exact none_case
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
        · refine IndexFact.holdsAt_valueFact.mpr ⟨by simp [Linear.Fact.vars, h0], ?_⟩
          show Linear.Form.eval _ _ ≤ _; simp [Linear.Form.eval, hv0]
        · refine IndexFact.holdsAt_valueFact.mpr ⟨by simp [Linear.Fact.vars, h0], ?_⟩
          show Linear.Form.eval _ _ ≤ _; simp [Linear.Form.eval, hv0]; simpa [maxArrayLength] using hmax
      · split
        · -- `string-length`
          rename_i hst
          obtain ⟨str, hstr⟩ := stringSlot_sound hst he
          simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero, hstr] at hs ⊢
          refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (len_str_run hs)
          obtain ⟨-, rfl, rfl, hmax⟩ := hq
          have hsafe : SafeIntegers.SafeInt (bitsOfNat (utf16Units str).length) ((utf16Units str).length : Int) :=
            ⟨by simp [maxStringLength] at hmax ⊢; omega, .inl ⟨by simp [maxStringLength] at hmax; omega, by simp⟩⟩
          have h0 : intValue (push (.num (bitsOfNat (utf16Units str).length)) ρ 0) =
              some ((utf16Units str).length : Int) := intValue_num hsafe
          have hl : termValue (push (.num (bitsOfNat (utf16Units str).length)) ρ) h' (.strLength (s + 1)) =
              some ((utf16Units str).length : Int) := by
            simp [push, hstr, strLengthOf, hmax]
          have hv0 : termValuation (push (.num (bitsOfNat (utf16Units str).length)) ρ) h' (.value 0) =
              (utf16Units str).length := by simp [termValuation, h0]
          have hv1 : termValuation (push (.num (bitsOfNat (utf16Units str).length)) ρ) h' (.strLength (s + 1)) =
              (utf16Units str).length := by simp only [termValuation, hl, Option.getD_some]
          intro atom hat _
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hat
          rcases hat with rfl | rfl | rfl
          · show (intValue _).isSome; rw [h0]; rfl
          all_goals
            refine ⟨fun t ht => ?_, ?_⟩
            · simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
                or_false] at ht
              rcases ht with rfl | rfl
              · rw [termValue_value, h0]; rfl
              · rw [hl]; rfl
            · show Linear.Form.eval _ _ ≤ _
              simp only [Linear.Form.eval, hv0, hv1]; omega
        · exact none_case
    | _ => simp only [linearAtoms]; exact none_case
  | arith op a b =>
    simp only [linearAtoms]
    split
    · rename_i x y hc
      obtain ⟨rfl, rfl, rfl, hx, hy⟩ := concatOperands_sound hc
      obtain ⟨s, hs0⟩ := stringSlot_sound hx he
      obtain ⟨t, ht0⟩ := stringSlot_sound hy he
      simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero, hs0, ht0] at hs ⊢
      refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (arith_run rfl rfl hs)
      obtain ⟨-, -, hu⟩ := hq
      have hu' : concatString s t = some u := by simpa (config := { decide := true }) [binop, Arith.relational] using hu
      have hlen : (utf16Units (s ++ t)).length = (utf16Units s).length + (utf16Units t).length := by
        simp [utf16Units, String.toList_append]
      have hmax : (utf16Units s).length + (utf16Units t).length ≤ maxStringLength := by
        unfold concatString concatOver at hu'
        split at hu'
        · contradiction
        · rename_i hn; simpa using hn
      obtain rfl := concatString_eq hu'
      have h0 : termValue (push (.str (s ++ t)) ρ) h' (.strLength 0) =
          some ((utf16Units s).length + (utf16Units t).length : Int) := by
        simp [push, strLengthOf, hlen, hmax]
      have hx' : termValue (push (.str (s ++ t)) ρ) h' (.strLength (x + 1)) =
          some ((utf16Units s).length : Int) := by
        simp [push, hs0, strLengthOf, show (utf16Units s).length ≤ maxStringLength by omega]
      have hy' : termValue (push (.str (s ++ t)) ρ) h' (.strLength (y + 1)) =
          some ((utf16Units t).length : Int) := by
        simp [push, ht0, strLengthOf, show (utf16Units t).length ≤ maxStringLength by omega]
      intro atom hat _
      simp only [concatAtoms, List.mem_cons, List.not_mem_nil, or_false] at hat
      rcases hat with rfl | rfl
      all_goals
        refine ⟨fun z hz => ?_, ?_⟩
        · simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl
          · rw [h0]; rfl
          · rw [hx']; rfl
          · rw [hy']; rfl
        · show Linear.Form.eval _ _ ≤ _
          simp only [Linear.Form.eval, termValuation, h0, hx', hy', Option.getD_some]; omega
    ·
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
          have hsum : ∀ (F : Linear.Form Nat) (c : Int) (v : Int) (bits : UInt64) {h'' : Heap},
              (∀ x ∈ F.map (·.1), (intValue (ρ x)).isSome) →
              Linear.Form.eval (valuation ρ) F + c = v →
              ((v.natAbs < 2 ^ 53) → SafeIntegers.SafeInt bits v) →
              IndexHolds ((if entailsKnown k.indices (valueFact (.le F (maxSafe - c))) &&
                entailsKnown k.indices (valueFact (.le (F.scale (-1)) (maxSafe + c))) then valueAtoms F c else []))
                (push (.num bits) ρ) h'' := by
            intro F c v bits h'' hF hv hsafe
            split
            · rename_i hc
              simp only [Bool.and_eq_true] at hc
              have h1 : Linear.Form.eval (valuation ρ) F ≤ maxSafe - c := holds_valueFact.mp (entailsKnown_sound hk.2.2.2.2.2 hc.1)
              have h2 : Linear.Form.eval (valuation ρ) (F.scale (-1)) ≤ maxSafe + c := holds_valueFact.mp (entailsKnown_sound hk.2.2.2.2.2 hc.2)
              rw [Linear.Form.eval_scale] at h2
              refine valueAtoms_holds hF ?_
              rw [hv]; apply hsafe; simp only [maxSafe] at h1 h2; omega
            · exact indexHolds_nil _ _
          have hvars : ∀ (G' : Linear.Form Nat), G'.map (·.1) = (fa ++ fb).map (·.1) →
              ∀ x ∈ G'.map (·.1), (intValue (ρ x)).isSome := by
            intro G' hG x hx
            rw [hG, List.map_append] at hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hva x hx
            · exact hvb x hx
          split
          · -- add
            rw [binop_num_arith (.inl rfl) hu]
            split
            · rename_i hc
              obtain ⟨hc, -⟩ := Bool.and_eq_true_iff.mp hc
              obtain ⟨hc, -⟩ := Bool.and_eq_true_iff.mp hc
              obtain ⟨hc, -⟩ := Bool.and_eq_true_iff.mp hc
              obtain ⟨hc, hc3⟩ := Bool.and_eq_true_iff.mp hc
              obtain ⟨-, hc2⟩ := Bool.and_eq_true_iff.mp hc
              have hn1 := holds_valueFact.mp (entailsKnown_sound hk.2.2.2.2.2 hc2)
              have hn2 := holds_valueFact.mp (entailsKnown_sound hk.2.2.2.2.2 hc3)
              simp only [Linear.Fact.Holds, Linear.Form.eval_scale, Linear.Form.eval_append, maxSafe] at hn1 hn2
              intro a ha hcond
              obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
              by_cases hr : ((Linear.Form.eval (valuation ρ) fa + ca) + (Linear.Form.eval (valuation ρ) fb + cb)).natAbs < 2 ^ 53
              · refine .inl (valueAtoms_holds (hvars (fa ++ fb) rfl) ?_ a0 ha0 hcond)
                rw [Linear.Form.eval_append, show Linear.Form.eval (valuation ρ) fa + Linear.Form.eval (valuation ρ) fb + (ca + cb) =
                  (Linear.Form.eval (valuation ρ) fa + ca) + (Linear.Form.eval (valuation ρ) fb + cb) by omega]
                exact SafeIntegers.add_safe hsa hsb hr
              · exact .inr (by simp only [IndexFact.HoldsAt, push]; rw [SafeIntegers.add_two53 hsa hsb (by omega)])
            · exact hsum (fa ++ fb) (ca + cb)
                ((Linear.Form.eval (valuation ρ) fa + ca) + (Linear.Form.eval (valuation ρ) fb + cb)) _
                (hvars (fa ++ fb) rfl)
                (by rw [Linear.Form.eval_append]; omega)
                (fun hr => SafeIntegers.add_safe hsa hsb hr)
          · -- sub
            rw [binop_num_arith (.inr (.inl rfl)) hu]
            exact hsum (fa ++ fb.scale (-1)) (ca - cb)
              ((Linear.Form.eval (valuation ρ) fa + ca) - (Linear.Form.eval (valuation ρ) fb + cb)) _
              (hvars (fa ++ fb.scale (-1)) (by simp only [List.map_append, scale_vars]))
              (by rw [Linear.Form.eval_append, Linear.Form.eval_scale]; omega)
              (fun hr => SafeIntegers.sub_safe hsa hsb hr)
          · -- multiplication with one constant operand
            rw [binop_num_arith (.inr (.inr rfl)) hu]
            split
            · rename_i hc
              subst fa
              exact hsum (if ca = 0 then [] else fb.scale ca) (ca * cb)
                ((Linear.Form.eval (valuation ρ) [] + ca) * (Linear.Form.eval (valuation ρ) fb + cb)) _
                (by split
                    · simp
                    · simpa only [scale_vars] using hvb)
                (by split
                    · rename_i h0; subst h0; simp [Linear.Form.eval]
                    · simp only [Linear.Form.eval_scale, Linear.Form.eval, Int.zero_add, Int.mul_add])
                (fun hr => SafeIntegers.mul_safe hsa hsb hr)
            · split
              · rename_i hc
                subst fb
                exact hsum (if cb = 0 then [] else fa.scale cb) (ca * cb)
                  ((Linear.Form.eval (valuation ρ) fa + ca) * (Linear.Form.eval (valuation ρ) [] + cb)) _
                  (by split
                      · simp
                      · simpa only [scale_vars] using hva)
                  (by split
                      · rename_i h0; subst h0; simp [Linear.Form.eval]
                      · simp only [Linear.Form.eval_scale, Linear.Form.eval, Int.zero_add, Int.add_mul]
                        rw [Int.mul_comm cb])
                  (fun hr => SafeIntegers.mul_safe hsa hsb hr)
              · exact indexHolds_nil _ _
          · -- signed right shift
            have hu' : u = .num (arithBits .shr xa xb) := by simpa [binop, Arith.relational] using hu.symm
            rw [hu']
            split
            · rename_i hc
              obtain ⟨rfl, hd, hdk, hc⟩ := hc
              have hr := smallOperand_sound hc hk
              exact bitAtoms_holds hva hsa (by simpa [Linear.Form.eval] using hsb) hr.1 hr.2 hd (.inl ⟨rfl, hdk⟩)
            · exact indexHolds_nil _ _
          · -- nonnegative mask
            have hu' : u = .num (arithBits .bitAnd xa xb) := by simpa [binop, Arith.relational] using hu.symm
            rw [hu']
            split
            · rename_i hc
              obtain ⟨rfl, hd, hdm, hc⟩ := hc
              have hr := smallOperand_sound hc hk
              exact bitAtoms_holds hva hsa (by simpa [Linear.Form.eval] using hsb) hr.1 hr.2 hd (.inr ⟨rfl, hdm⟩)
            · exact indexHolds_nil _ _
          all_goals first
            | (rw [binop_num_eq hu]
               exact equalAtoms_holds (hvars (fa ++ fb.scale (-1)) (by simp only [List.map_append, scale_vars]))
                 (i := Linear.Form.eval (valuation ρ) fa + ca) (j := Linear.Form.eval (valuation ρ) fb + cb)
                 (by rw [Linear.Form.eval_append, Linear.Form.eval_scale]; omega) hsa hsb)
            | (rename_i hop
               rw [binop_num_relational (by first | rfl) hu]
               exact compareAtoms_holds (hvars (fa ++ fb.scale (-1)) (by simp only [List.map_append, scale_vars]))
                 (i := Linear.Form.eval (valuation ρ) fa + ca) (j := Linear.Form.eval (valuation ρ) fb + cb)
                 (by rw [Linear.Form.eval_append, Linear.Form.eval_scale]; omega) hsa hsb)
            | exact indexHolds_nil _ _
        · exact none_case
      · exact none_case
  | _ => simp only [linearAtoms]; exact none_case

/-! ## A comparison with a length

A strict comparison of a safe integer `k` with a slot `n` holding the length of
an array `x`'s store states, on the answer giving `k < n`, the facts of `k`
alone that survive the length slot: `k ≤ 2^32 - 2`, and, where the knowledge
entails `0 ≤ k`, the strict `bound(x, k)`: `k` an index below the length. -/

/-- For a strict relational operator, whether the index is the left operand
and the answer on which it is below the other. -/
def strictAnswer : Arith → Option (Bool × Bool)
  | .lt => some (true, true)
  | .ge => some (true, false)
  | .gt => some (false, true)
  | .le => some (false, false)
  | _ => none

theorem strictAnswer_sound {op : Arith} {left q : Bool} (h : strictAnswer op = some (left, q)) (i L : Int) :
    relationHolds op (some (if left then compare i L else compare L i)) = q → i - L ≤ -1 := by
  intro hr
  have ha := answer_sound op (if left then i else L) (if left then L else i)
  cases op <;> simp only [strictAnswer, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp only [if_true, Bool.false_eq_true, if_false] at hr ha <;>
    rw [hr] at ha <;> simp only [answerHolds] at ha <;> omega

/-- The atoms of `i < n` with `n` a length, conditional on the answer `q` of
the result slot 0. -/
def lengthPair (k : Knowledge) (i n : Nat) (q : Bool) : List IndexAtom :=
  match lengthsOf k n with
  | [] => []
  | xs => ⟨.linear (valueFact (.le [(i + 1, 1)] (maxArrayLength - 1))), some 0, !q⟩ ::
      (if entailsKnown k.indices (valueFact (.le [(i, -1)] 0)) then
        xs.map fun x => ⟨.bound (x + 1) (i + 1) true, some 0, !q⟩ else [])

def lengthAtoms (k : Knowledge) (Γ : List (Ty ι)) : Tm → List IndexAtom
  | .arith op (.var a) (.var b) =>
    if a < Γ.length ∧ b < Γ.length then
      match strictAnswer op with
      | some (true, q) => if intSlot k.indices a then lengthPair k a b q else []
      | some (false, q) => if intSlot k.indices b then lengthPair k b a q else []
      | none => []
    else []
  | _ => []

theorem lengthPair_holds {k : Knowledge} {i n : Nat} {q : Bool} {ρ h} {u : Val} {j : Int}
    (hk : Holds k ρ h) (hj : valuation ρ i = j)
    (below : ∀ (ls : List (Option Nat)), ρ n = .num (bitsOfNat ls.length) →
      ls.length ≤ maxArrayLength → tagHolds .truthy u = q → j - ls.length ≤ -1)
    (hb : ∃ bj, ρ i = .num bj ∧ SafeIntegers.SafeInt bj j) :
    IndexHolds (lengthPair k i n q) (push u ρ) h := by
  unfold lengthPair
  split
  · exact indexHolds_nil _ _
  · rename_i xs hxs
    obtain ⟨bj, hbj, hsafe⟩ := hb
    have hlin := linearFacts_holds hk.2.2.2.2.2
    have hm : ((maxArrayLength : Nat) : Int) = 4294967295 := rfl
    intro atom hat hc
    have hq' : atom.cond = some 0 → (atom.negated = !q) → tagHolds .truthy u = q := by
      intro h0 hneg
      have := hc 0 h0; simp only [push, hneg] at this; cases q <;> simpa using this
    rcases List.mem_cons.mp hat with rfl | hat
    · have hq := hq' rfl rfl
      -- `i ≤ 2^32 - 2`, from any length the other operand holds
      obtain ⟨x, hx⟩ : ∃ x, x ∈ lengthsOf k n := by
        cases hl : lengthsOf k n with
        | nil => exact absurd hl hxs
        | cons x _ => exact ⟨x, by simp⟩
      obtain ⟨_, ls, -, -, hn, hmax⟩ := lengthsOf_sound hx hk
      have hlt := below ls hn hmax hq
      have hi : intValue (push u ρ (i + 1)) = some j := by simp [push, hbj, intValue_num hsafe]
      refine IndexFact.holdsAt_valueFact.mpr ⟨by simp [Linear.Fact.vars, hi], ?_⟩
      show Linear.Form.eval _ _ ≤ _
      simp only [Linear.Form.eval, valuation, hi, Option.getD_some]
      simp [maxArrayLength] at hmax; omega
    · split at hat
      · rename_i h0
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hat
        have hq := hq' rfl rfl
        obtain ⟨s, ls, hs, hl, hn, hmax⟩ := lengthsOf_sound hx hk
        have hlt := below ls hn hmax hq
        have f0 : -j ≤ 0 := by
          have := holds_valueFact.mp (entailsKnown_sound hk.2.2.2.2.2 h0)
          simp only [Linear.Fact.Holds, Linear.Form.eval, hj] at this; omega
        exact ⟨s, ls, bj, j.toNat, by simpa [push] using hs, hl, by simpa [push] using hbj,
          HeapKnowledge.indexOfBits_safe hsafe (by omega) (by simp [maxArrayLength] at hmax; omega), by simp; omega⟩
      · cases hat

theorem lengthAtoms_shape {k : Knowledge} {Γ : List (Ty ι)} {t : Tm} (h : lengthAtoms k Γ t ≠ []) :
    ∃ op a b, t = .arith op (.var a) (.var b) := by
  unfold lengthAtoms at h
  split at h
  · exact ⟨_, _, _, rfl⟩
  · exact absurd rfl h

theorem lengthAtoms_holds {k : Knowledge} {Γ : List (Ty ι)} {G : NormalGraph ι} {t : Tm}
    {Ξ T : Fam} {Q : Post} {ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ρ h) (hs : SafePost Ξ T Q n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds (lengthAtoms k Γ t) (push u ρ) h') n W h
      (instantiate 0 ρ t) := by
  have hval : ∀ i, i < Γ.length → isVal (ρ i) = true := fun i hi =>
    (meaning_value (he.2 i _ (List.getElem?_eq_getElem hi))).1
  by_cases hnil : lengthAtoms k Γ t = []
  · rw [hnil]; exact weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _⟩) hs
  obtain ⟨op, a, b, rfl⟩ := lengthAtoms_shape hnil
  simp only [lengthAtoms] at hnil ⊢
  split
  · rename_i hab
    simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero] at hs ⊢
    refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (arith_run (hval a hab.1) (hval b hab.2) hs)
    obtain ⟨-, rfl, hu⟩ := hq
    have pick : ∀ i, intSlot k.indices i = true →
        ∃ j, valuation ρ i = j ∧ ∃ bj, ρ i = .num bj ∧ SafeIntegers.SafeInt bj j := by
      intro i hi
      obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (intSlot_sound hk.2.2.2.2.2 hi)
      obtain ⟨bj, hbj, hsafe⟩ := intValue_safe hj
      exact ⟨j, by simp [valuation, hj], bj, hbj, hsafe⟩
    have hrel : ∀ {l q'}, strictAnswer op = some (l, q') → op.relational = true := by
      intro l q' h; cases op <;> simp_all [strictAnswer, Arith.relational]
    split
    · rename_i q hsa
      split
      · rename_i hint
        obtain ⟨j, hj, bj, hbj, hsafe⟩ := pick a hint
        refine lengthPair_holds hk hj (fun ls hn hmax hq' => ?_) ⟨bj, hbj, hsafe⟩
        have hL : SafeIntegers.SafeInt (bitsOfNat ls.length) (ls.length : Int) :=
          ⟨by simp [maxArrayLength] at hmax ⊢; omega, .inl ⟨by omega, by simp⟩⟩
        rw [hbj, hn] at hu
        rw [binop_relational (hrel hsa) hu, SafeIntegers.doubleOrder_safe hsafe hL] at hq'
        exact strictAnswer_sound hsa j ls.length (by simpa using truthy_boolVal hq')
      · exact indexHolds_nil _ _
    · rename_i q hsa
      split
      · rename_i hint
        obtain ⟨j, hj, bj, hbj, hsafe⟩ := pick b hint
        refine lengthPair_holds hk hj (fun ls hn hmax hq' => ?_) ⟨bj, hbj, hsafe⟩
        have hL : SafeIntegers.SafeInt (bitsOfNat ls.length) (ls.length : Int) :=
          ⟨by simp [maxArrayLength] at hmax ⊢; omega, .inl ⟨by omega, by simp⟩⟩
        rw [hbj, hn] at hu
        rw [binop_relational (hrel hsa) hu, SafeIntegers.doubleOrder_safe hL hsafe] at hq'
        exact strictAnswer_sound hsa j ls.length (by simpa using truthy_boolVal hq')
      · exact indexHolds_nil _ _
    · exact indexHolds_nil _ _
  · exact weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _⟩) hs

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

/-- The complete element-write execution consumes a postcondition for
both possible updates: an existing element cell followed by the store
write, or a fresh cell followed by the store write. -/
theorem elementWrite_post {Ξ T : Fam} {P : Heap → Prop}
    {h : Heap} {flds : List (PropKey × Nat)} {cd : CallCode} {oid target : Nat}
    {xs : List (Option Nat)} {b : UInt64} {value : Val} {n W}
    (hfield : flds.lookup arrayStoreKey = some target)
    (hxs : h[target]? = some (.arr xs)) (hv : isVal value = true)
    (hpresent : ∀ cell, elemLoc xs b = some cell →
      P ((h.set cell value).set target (.arr xs)))
    (hfresh : ∀ i, indexOfBits b = some i → elemLoc xs b = none →
      P ((h ++ [value]).set target (.arr (placeAt xs i h.length))))
    (hs : Safe Ξ T n W h (.writeAt arrayStoreKey (.objAt flds cd oid)
      (.setElem (.readAt arrayStoreKey (.objAt flds cd oid)) (.num b) value))) :
    SafePost Ξ T (fun h' _ => P h') n W h
      (.writeAt arrayStoreKey (.objAt flds cd oid)
        (.setElem (.readAt arrayStoreKey (.objAt flds cd oid)) (.num b) value)) := by
  cases n with
  | zero => trivial
  | succ n1 =>
    rcases hs with (⟨hbad, _⟩ | hr) | ⟨U1, h1, t1, hx1, hu1, step1, hh1, hs1⟩
    · simp [isVal] at hbad
    · exact .inl (.inr hr)
    obtain ⟨u, hu, rfl, rfl⟩ := ExpressionEffects.elem_read_inv hfield step1
    rw [hxs] at hu; cases hu
    refine .inr ⟨U1, h, _, hx1, hu1, step1, hh1, ?_⟩
    cases n1 with
    | zero => trivial
    | succ n2 =>
      rcases hs1 with (⟨hbad, _⟩ | hr) | ⟨U2, h2, t2, hx2, hu2, step2, hh2, hs2⟩
      · simp [isVal] at hbad
      · exact .inl (.inr hr)
      obtain ⟨b', xs', hb, hls, hcase⟩ := ExpressionEffects.elem_set_inv rfl rfl rfl hv step2
      cases hb; cases hls
      rcases hcase with ⟨cell, hc, rfl, rfl⟩ | ⟨i, hi, hn, rfl, rfl⟩
      · exact .inr ⟨U2, _, _, hx2, hu2, step2, hh2,
          (ExpressionEffects.write_back_post hfield (hpresent cell hc) hs2).post⟩
      · exact .inr ⟨U2, _, _, hx2, hu2, step2, hh2,
          (ExpressionEffects.write_back_post hfield (hfresh i hi hn) hs2).post⟩

/-- Whether an unconditional atom bounds a slot of `i`'s class by the store of
an array of `a`'s class, strictly where `strict`. -/
def boundAtom (k : Knowledge) (a i : Nat) (strict : Bool) : Bool :=
  k.indices.any fun atom => atom.cond.isNone && match atom.fact with
    | .bound x i' st => (HeapLinks.aliases k.links a).contains x && (HeapLinks.aliases k.links i).contains i' &&
        (st || !strict)
    | _ => false

theorem boundAtom_sound {k : Knowledge} {a i : Nat} {strict : Bool} {ρ h} (hc : boundAtom k a i strict = true)
    (hk : Holds k ρ h) :
    ∃ s ls b idx, Footprints.storeOf (ρ a) = some s ∧ h[s]? = some (.arr ls) ∧ ρ i = .num b ∧
      indexOfBits b = some idx ∧ idx + (if strict then 1 else 0) ≤ ls.length := by
  obtain ⟨atom, ha, hm⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hnone, hf⟩ := hm
  have hat := hk.2.2.2.2.2 atom ha fun b hb => by rw [hnone] at hb; cases hb
  cases hfact : atom.fact with
  | bound x i' st =>
    rw [hfact] at hf hat
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hf
    obtain ⟨⟨hx, hi⟩, hst⟩ := hf
    rw [← HeapLinks.aliases_eq hk.2.2.1 hx, ← HeapLinks.aliases_eq hk.2.2.1 hi]
    obtain ⟨s, ls, b, idx, hs, hl, hb, hidx, hle⟩ := hat
    exact ⟨s, ls, b, idx, hs, hl, hb, hidx, by cases st <;> cases strict <;> simp_all <;> omega⟩
  | index _ => rw [hfact] at hf; cases hf
  | length _ _ => rw [hfact] at hf; cases hf
  | int _ => rw [hfact] at hf; cases hf
  | linear _ => rw [hfact] at hf; cases hf
  | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ => rw [hfact] at hf; cases hf

/-- Whether the linear facts bound a slot `i` by the length of the store of an
array of `a`'s class (`HeapKnowledge.lengthBound`). -/
def linearBound (k : Knowledge) (a i : Nat) (strict : Bool) : Bool :=
  lengthBound (HeapLinks.aliases k.links a) k.indices i strict

theorem linearBound_sound {k : Knowledge} {a i : Nat} {strict : Bool} {ρ h} (hc : linearBound k a i strict = true)
    (hk : Holds k ρ h) :
    ∃ s ls b idx, Footprints.storeOf (ρ a) = some s ∧ h[s]? = some (.arr ls) ∧ ρ i = .num b ∧
      indexOfBits b = some idx ∧ idx + (if strict then 1 else 0) ≤ ls.length :=
  lengthBound_sound (fun _ hy => HeapLinks.aliases_eq hk.2.2.1 hy) hc hk.2.2.2.2.2

/-- Whether a slot of `i`'s class holds an index at most the length of the
store of an array of `a`'s class: a bound atom states it, or the linear facts do. -/
def bounded (k : Knowledge) (a i : Nat) (strict : Bool) : Bool := boundAtom k a i strict || linearBound k a i strict

theorem bounded_sound {k : Knowledge} {a i : Nat} {strict : Bool} {ρ h} (hc : bounded k a i strict = true)
    (hk : Holds k ρ h) :
    ∃ s ls b idx, Footprints.storeOf (ρ a) = some s ∧ h[s]? = some (.arr ls) ∧ ρ i = .num b ∧
      indexOfBits b = some idx ∧ idx + (if strict then 1 else 0) ≤ ls.length := by
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
    bounded k a i false && (expand G j.type == [.nul])

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
      have hsafe := boundedWrite_safe (Ξ := excOf G) hrep hm hS (he.2 a R hR) hs hl hidx (by simpa using hle) hv hw hh
      simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero, hb]
      apply HeapObservations.of_value_property (fun _ _ _ u _ => ?_)
      · exact Safe_mono n (fun m _ X u hu => (represents_back (c := .nul) hnul m X u) hu) W h _ hsafe
      · exact ⟨HeapFacts.holds_nil _ _, (shift_holds (v := u) hk).2.1,
          HeapLinks.stable_holds (shift_holds (v := u) hk).2.2.1, (shift_holds (v := u) hk).2.2.2.1,
          elemsHolds_nil _ _, envIndices_holds (shift_holds (v := u) hk).2.2.2.2.2 _⟩
    · cases htypes
  · cases htypes

/-- The knowledge after a write below its store's length: what the ordinary
output keeps, and every atom reading stores' lengths alone
(`ExpressionEffects.elem_var_write_length`). -/
def lengthOutput (k : Knowledge) : Knowledge :=
  { HeapExpressionRules.ordinaryOutput k with
    indices := shiftIndices (keptIndices ⟨true, true, .length⟩ (fun _ _ => false) k.indices) }

/-- Whether a checked write keeps every store's length: its index below the
store's length, at a store type every position of which holds source
values. -/
def keepsLengths [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) (k : Knowledge) (a i : Nat) : Bool :=
  bounded k a i true && match j.context[a]? with
    | some R => ExpressionEffects.storeFieldEvery G (expand G R) arrayStoreKey
    | none => false

theorem boundedLength_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) (hkeep : keepsLengths G j k a i = true) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' u => Holds (lengthOutput k) (push u ρ) h') n W h (instantiate 0 ρ j.term) := by
  have hs := boundedWrite_sound hc he hk hw hh
  simp only [boundedWriteCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hslots, hil⟩, htypes⟩, -⟩, -⟩ := hc
  simp only [keepsLengths, Bool.and_eq_true] at hkeep
  obtain ⟨hbd, hst⟩ := hkeep
  split at hst
  case h_2 => cases hst
  rename_i R hR
  have hvl : v < j.context.length := by
    split at htypes
    · rename_i R' V hR' hV; exact (List.getElem?_eq_some_iff.mp hV).1
    · cases htypes
  obtain ⟨s, ls, b, idx, hs0, hl, hb, hidx, hle⟩ := bounded_sound hbd hk
  obtain ⟨flds, cd, oid, hoi⟩ : ∃ flds cd oid, ρ a = .objAt flds cd oid := by
    cases hra : ρ a
    case objAt => exact ⟨_, _, _, rfl⟩
    all_goals rw [hra] at hs0; simp [Footprints.storeOf, Footprints.fieldsOf] at hs0
  have hfl : flds.lookup arrayStoreKey = some s := by
    simpa [Footprints.storeOf, Footprints.fieldsOf, hoi] using hs0
  rw [boundedSlots_eq hslots] at hs ⊢
  have hsafe : Safe (excOf G) (meaning G j.type) n W h
      (instantiate 0 ρ (.writeAt arrayStoreKey (.var a) (.setElem (.readAt arrayStoreKey (.var a)) (.var i) (.var v)))) :=
    HeapObservations.erase hs
  have hp := (ExpressionEffects.elem_var_write_length hvl hil hR hst hoi hfl hl hb hidx (by simp at hle; omega)
    he hh hsafe).post
  refine weaken (fun h' u hq => ?_) hp
  exact ⟨HeapFacts.holds_nil _ _, (shift_holds (v := u) hk).2.1,
    HeapLinks.stable_holds (shift_holds (v := u) hk).2.2.1, (shift_holds (v := u) hk).2.2.2.1,
    elemsHolds_nil _ _, shiftIndices_holds (keptIndices_holds hk.2.2.2.2.2 hq firstKept_none)⟩

/-! ## Element regions (FOOTPRINTS.md, "Element regions")

A region fact `apart(x, y)` keeps the regions of two values apart: an array
object's store cell and listed element cells, or a raw store's cells. An
allocation states it of its result and every array of the context, whose
locations the heap already holds; an element write keeps it where the
written array's region is apart from each side, or is one side and the other
an array of the context; and an element write keeps a quantified fact whose
array, bound and free terms read locations apart from the written region. -/

/-- Whether slot `j`'s type is an array: one record clause whose store field,
written or read only, holds one list contract. -/
def arraySlot (G : NormalGraph ι) (Γ : List (Ty ι)) (j : Nat) : Bool :=
  match Γ[j]? with
  | some R => match expand G R with
    | [.refs fs [] vs _ _ _ _] => match (fs.lookup arrayStoreKey).orElse fun _ => vs.lookup arrayStoreKey with
      | some S => match expand G S with
        | [.list _ []] => true
        | _ => false
      | none => false
    | _ => false
  | none => false

/-- Every cell a store under a tuple contract lists is a location of the world. -/
theorem listT_cells {T : TupleF} {k : Nat} {W : WorldT k} {ls : List (Option Nat)}
    (h : listT T k W (.arr ls)) : ∀ l, some l ∈ ls → ∃ c, lookup W l = some c := by
  obtain ⟨ls', heq, -, -, -, -, hreq, hopt, hrest⟩ := h
  cases heq
  intro l hl
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  by_cases h1 : i < T.required.length
  · obtain ⟨l', c, hl', hw, -⟩ := hreq i _ (List.getElem?_eq_getElem h1)
    rw [hi] at hl'; cases hl'; exact ⟨c, hw⟩
  · by_cases h2 : i < T.required.length + T.optional.length
    · have hk : T.required.length + (i - T.required.length) = i := by omega
      obtain ⟨c, hw, -⟩ := hopt (i - T.required.length) _ l
        (List.getElem?_eq_getElem (by omega)) (by rw [hk]; exact hi)
      exact ⟨c, hw⟩
    · obtain ⟨E, c, -, hw, -⟩ := hrest i l (by omega) hi
      exact ⟨c, hw⟩

/-- An array slot's region lies in the heap: its store cell and every cell
its store lists. -/
theorem arraySlot_region {G : NormalGraph ι} {Γ : List (Ty ι)} {j : Nat} {ρ n W h}
    (hc : arraySlot G Γ j = true) (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h) :
    ∃ st ls, Footprints.storeOf (ρ j) = some st ∧ h[st]? = some (.arr ls) ∧ st < h.length ∧
      ElementsBelow h.length ls := by
  unfold arraySlot at hc
  split at hc
  case h_2 => cases hc
  rename_i R hR
  split at hc
  case h_2 => cases hc
  rename_i fs vs os ms ks st hexp
  split at hc
  case h_2 => cases hc
  rename_i S hS
  split at hc
  case h_2 => cases hc
  rename_i T hT
  have hr : Represents G R (.refs fs [] vs os ms ks st) := hexp
  have hsem := (represents_raw hr _ W _) (he.2 j R hR)
  -- The store field's location, whose contract implies the store's type.
  obtain ⟨flds, l, c, oid, hobj, hf, hlc, hag⟩ : ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr (n + 1)) (oid : Nat),
      ρ j = .objAt flds .absent oid ∧ flds.lookup arrayStoreKey = some l ∧ lookup W l = some c ∧
      ∀ (i : Nat) (hi : i < n + 1) (W' : WorldT i) (u : Val), c i hi W' u → meaning G S i W' u := by
    cases hfs : fs.lookup arrayStoreKey with
    | some S' =>
      rw [hfs] at hS
      simp only [Option.orElse_some, Option.some.injEq] at hS
      subst hS
      obtain ⟨flds, l, c, oid, hobj, hf, hlc, hag⟩ := recT_at
        (ReferenceConjunctions.mem_famsOf.mpr ⟨S', PositiveRules.mem_of_lookup hfs, rfl⟩) hsem.1.1
      exact ⟨flds, l, c, oid, hobj, hf, hlc, fun i hi W' u hu => (hag i hi W' u).mp hu⟩
    | none =>
      rw [hfs] at hS
      simp only [Option.orElse_none] at hS
      exact viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨S, PositiveRules.mem_of_lookup hS, rfl⟩)
        (by simp [arrayStoreKey, lengthKey]) hsem.2.1
  obtain ⟨w, hwv, hwc⟩ := hh.2 l c hlc
  have hstore : meaning G S n (trunc n (Nat.le_succ n) W) w := hag n (by omega) _ _ (hwc n (by omega))
  have hlist := (represents_raw (show Represents G S (.list T []) from hT) _ _ _ hstore).1
  obtain ⟨ls, rfl, -⟩ := hlist
  refine ⟨l, ls, by simp [hobj, Footprints.storeOf, Footprints.fieldsOf, hf], hwv,
    (List.getElem?_eq_some_iff.mp hwv).1, fun l' hl' => ?_⟩
  obtain ⟨c', hc'⟩ := listT_cells ((represents_raw (show Represents G S (.list T []) from hT) _ _ _ hstore).1) l' hl'
  obtain ⟨c0, hc0, -⟩ := lookup_trunc_inv _ W l' c' hc'
  obtain ⟨u, hu, -⟩ := hh.2 l' c0 hc0
  exact (List.getElem?_eq_some_iff.mp hu).1

/-- Two postconditions of one term hold together: its execution is
deterministic. -/
theorem safePost_and {Ξ T : Fam} {Q R : Post} : ∀ {n W W' h t}, SafePost Ξ T Q n W h t →
    SafePost Ξ T R n W' h t → SafePost Ξ T (fun h' u => Q h' u ∧ R h' u) n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W W' h t hq hr
    rcases hq with (⟨hv, ht, hq⟩ | hth) | ⟨U, h1, t1, hx, hu, st1, hh1, hq1⟩
    · rcases hr with (⟨_, _, hr⟩ | hth') | ⟨_, _, _, _, _, st2, _, _⟩
      · exact .inl (.inl ⟨hv, ht, hq, hr⟩)
      · exact absurd hth' (val_not_thrown hv)
      · exact absurd st2 (value_no_step hv)
    · exact .inl (.inr hth)
    · rcases hr with (⟨hv', _, _⟩ | hth') | ⟨U2, h2, t2, _, _, st2, _, hr2⟩
      · exact absurd st1 (value_no_step hv')
      · exact absurd st1 hth'.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st1 st2
        exact .inr ⟨U, h1, t1, hx, hu, st1, hh1, ih hq1 hr2⟩

/-- The slots of a literal's elements, where each is a slot. -/
def slotVars : List Tm → Option (List Nat)
  | [] => some []
  | .var i :: rest => (slotVars rest).map (i :: ·)
  | _ :: _ => none

theorem slotVars_eq {es : List Tm} {is : List Nat} (h : slotVars es = some is) : es = is.map Tm.var := by
  induction es generalizing is with
  | nil => simp only [slotVars, Option.some.injEq] at h; subst h; rfl
  | cons e rest ih =>
    cases e <;> simp only [slotVars, Option.map_eq_some_iff, reduceCtorEq] at h
    obtain ⟨is', h', rfl⟩ := h
    simp [ih h']

/-- The context's array slots. -/
def arrayPartners (G : NormalGraph ι) (Γ : List (Ty ι)) : List Nat :=
  (List.range Γ.length).filter (arraySlot G Γ)

/-- A fresh result's region is apart from every array slot's, one push deeper. -/
def freshApart (G : NormalGraph ι) (Γ : List (Ty ι)) : List IndexAtom :=
  (arrayPartners G Γ).map fun j => { fact := .apart 0 (j + 1) }

/-- The array slots an unconditional atom keeps apart from the raw store in slot 0. -/
def rawPartners (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : List Nat :=
  k.indices.filterMap fun a => if a.cond.isNone then match a.fact with
    | .apart x y =>
      if x == 0 && y != 0 && arraySlot G Γ y then some y
      else if y == 0 && x != 0 && arraySlot G Γ x then some x else none
    | _ => none
    else none

theorem rawPartners_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {y : Nat} {ρ h}
    (hy : y ∈ rawPartners G Γ k) (hk : Holds k ρ h) :
    arraySlot G Γ y = true ∧ RegionsApart h (ρ 0) (ρ y) := by
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hy
  split at hm
  case isFalse => cases hm
  rename_i hn
  have hat := hk.2.2.2.2.2 a ha fun b hb => by rw [Option.isNone_iff_eq_none.mp hn] at hb; cases hb
  split at hm
  case h_2 => cases hm
  rename_i x z hfa
  rw [hfa] at hat
  split at hm
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    cases hm
    obtain ⟨⟨rfl, -⟩, hs⟩ := hc
    exact ⟨hs, hat⟩
  · split at hm
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
      cases hm
      obtain ⟨⟨rfl, -⟩, hs⟩ := hc
      exact ⟨hs, regionsApart_symm hat⟩
    · cases hm

/-- The region facts an allocation states (`region-alloc`): a literal's
store, of slots, apart from every array slot; its combined object allocation
likewise; and an array object holding the raw store in slot 0, apart from
every array slot the raw store is known apart from. -/
def regionAtoms (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Tm → List IndexAtom
  | .arrLit es => match slotVars es with
    | some is => if is.all (· < Γ.length) && decide (is.length ≤ maxArrayLength) then freshApart G Γ else []
    | none => []
  | .makeAt .absent [s, p] [.var 0, .var proto] =>
    if s == arrayStoreKey && p == CallArguments.protoField && decide (proto < Γ.length) && storeSlot G Γ 0 then
      (rawPartners G Γ k).map fun y => { fact := .apart 0 (y + 1) }
    else []
  | .letE (.arrLit es) (.makeAt .absent [s, p] [.var 0, .var proto]) =>
    if s == arrayStoreKey && p == CallArguments.protoField && decide (proto < Γ.length + 1) &&
        appendSlots Γ.length es && decide (es.length ≤ maxArrayLength) then
      freshApart G Γ
    else []
  | _ => []

/-- A region of locations at or past the heap's end is apart from an array
slot's. -/
theorem fresh_apart_slot {G : NormalGraph ι} {Γ : List (Ty ι)} {j : Nat} {ρ n W h} {u : Val} {vs : List Val}
    {s : Option Nat} {xs : List (Option Nat)}
    (hc : arraySlot G Γ j = true) (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h)
    (hu : RegionOf (h ++ vs) u s xs) (habove : ∀ l, InRegion s xs l → h.length ≤ l) :
    RegionsApart (h ++ vs) u (ρ j) := by
  obtain ⟨st, ls, hst, hls, hlt, hbelow⟩ := arraySlot_region hc he hh
  refine ⟨s, xs, some st, ls, hu, .inr ⟨st, rfl, hst, ?_⟩, fun l hl m hm => ?_⟩
  · rw [List.getElem?_append_left hlt]; exact hls
  · have := habove l hl
    rcases hm with hm | hm
    · cases hm; omega
    · have := hbelow m hm; omega

theorem freshApart_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W h} {u : Val} {vs : List Val}
    {s : Option Nat} {xs : List (Option Nat)}
    (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h)
    (hu : RegionOf (h ++ vs) u s xs) (habove : ∀ l, InRegion s xs l → h.length ≤ l) :
    IndexHolds (freshApart G Γ) (push u ρ) (h ++ vs) := by
  intro a ha _
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  have hc : arraySlot G Γ j = true := (List.mem_filter.mp hj).2
  show RegionsApart (h ++ vs) u (ρ j)
  exact fresh_apart_slot hc he hh hu habove

theorem regionAtoms_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {Ξ T : Fam} {Q : Post}
    {ρ n W h t k}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ρ h) (hh : HeapOk n W h)
    (hs : SafePost Ξ T Q n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds (regionAtoms G Γ k t) (push u ρ) h')
      n W h (instantiate 0 ρ t) := by
  cases n with
  | zero => trivial
  | succ n =>
  have hval : ∀ i, i < Γ.length → isVal (ρ i) = true :=
    fun i hi => (meaning_value (he.2 i _ (List.getElem?_eq_getElem hi))).1
  have none_holds : SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds [] (push u ρ) h') (n + 1) W h
      (instantiate 0 ρ t) := weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _⟩) hs
  unfold regionAtoms
  split
  · rename_i es
    split
    · rename_i is his
      split
      · rename_i hc
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hlt, hmax⟩ := hc
        have hes := slotVars_eq his
        subst hes
        have hinst : instantiate 0 ρ (.arrLit (is.map Tm.var)) = .arrLit (is.map ρ) := by
          simp only [instantiate, instantiateArgs_eq_map, List.map_map]
          congr 1
        rw [hinst] at hs ⊢
        have hv : ∀ v ∈ is.map ρ, isVal v = true := by
          intro v hv
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
          exact hval i (hlt i hi)
        have run : Steps 1 h (.arrLit (is.map ρ)) (h ++ is.map ρ)
            (.arr (elemSlots h.length (is.map ρ).length)) :=
          .next (.arrAlloc hv (by simpa using hmax)) .refl
        refine weaken (fun heap u hq => ?_) (steps_run run rfl hs)
        obtain ⟨hq, rfl, rfl⟩ := hq
        refine ⟨hq, freshApart_holds he hh (.inl ⟨rfl, rfl⟩) fun l hl => ?_⟩
        rcases hl with hl | hl
        · cases hl
        · exact elemSlots_above _ _ l hl
      · exact none_holds
    · exact none_holds
  · rename_i s p proto
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨rfl, rfl⟩, hproto⟩, hstore⟩ := hc
      obtain ⟨cells, hcells, -⟩ := storeSlot_sound hstore he
      have hinst : instantiate 0 ρ (.makeAt .absent [arrayStoreKey, CallArguments.protoField] [.var 0, .var proto]) =
          .makeAt .absent [arrayStoreKey, CallArguments.protoField] [ρ 0, ρ proto] := by
        simp [instantiate, instantiateArgs_eq_map]
      rw [hinst] at hs ⊢
      have run : Steps 1 h (.makeAt .absent [arrayStoreKey, CallArguments.protoField] [ρ 0, ρ proto])
          (h ++ [ρ 0, ρ proto] ++ [.nul])
          (.objAt (slots h.length [arrayStoreKey, CallArguments.protoField]) .absent (h.length + 2)) :=
        .next (Step.makeFields (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact hval 0 (by
              cases hΓ : Γ with
              | nil => simp [storeSlot, hΓ] at hstore
              | cons _ _ => simp)
          · exact hval proto hproto) rfl) .refl
      refine weaken (fun heap u hq => ?_) (steps_run run rfl hs)
      obtain ⟨hq, rfl, rfl⟩ := hq
      refine ⟨hq, fun a ha _ => ?_⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      obtain ⟨hcy, hap⟩ := rawPartners_sound hy hk
      obtain ⟨st, ls, hst, hls, hlt, hbelow⟩ := arraySlot_region hcy he hh
      obtain ⟨sa, xs, sb, ys, hra, hrb, hsep⟩ := hap
      obtain ⟨e1, e2⟩ := regionOf_unique hra (.inl ⟨rfl, hcells⟩)
      obtain ⟨e3, e4⟩ := regionOf_unique hrb (.inr ⟨st, rfl, hst, hls⟩)
      rw [e1, e2, e3, e4] at hsep
      have hlen : (h ++ [ρ 0, ρ proto] ++ [Tm.nul])[h.length]? = some (.arr cells) := by
        simp [hcells]
      refine ⟨some h.length, cells, some st, ls,
        .inr ⟨h.length, rfl, by simp [push, Footprints.storeOf, Footprints.fieldsOf, slots], hlen⟩,
        .inr ⟨st, rfl, hst, by rw [List.append_assoc, List.getElem?_append_left hlt]; exact hls⟩,
        fun l hl m hm => ?_⟩
      rcases hl with hl | hl
      · cases hl
        rcases hm with hm | hm
        · cases hm; omega
        · have := hbelow m hm; omega
      · exact hsep l (.inr hl) m hm
    · exact none_holds
  · rename_i es s p proto
    split
    · rename_i hp
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
      obtain ⟨⟨⟨⟨rfl, rfl⟩, hproto⟩, hes⟩, hmax⟩ := hp
      let vs := es.map (instantiate 0 ρ)
      have hvs : ∀ v ∈ vs, isVal v = true := by
        simpa only [vs, instantiateArgs_eq_map] using appendSlots_values
          (fun i hi => (meaning_value (he.2 i _ (List.getElem?_eq_getElem hi))).1) hes
      have hlen : vs.length = es.length := by simp [vs]
      let store := Tm.arr (elemSlots h.length vs.length)
      let heap := h ++ vs
      have hstore : isVal store = true := rfl
      have run : Steps 3 h (instantiate 0 ρ (.letE (.arrLit es)
          (.makeAt .absent [arrayStoreKey, CallArguments.protoField] [.var 0, .var proto])))
          (heap ++ [store, (push store ρ) proto] ++ [.nul])
          (.objAt (slots heap.length [arrayStoreKey, CallArguments.protoField]) .absent (heap.length + 2)) := by
        simp only [instantiate, instantiateArgs_eq_map, List.map_cons, List.map_nil]
        apply Steps.next (Step.letC (Step.arrAlloc hvs (by omega)))
        apply Steps.next (Step.letV hstore)
        have hb := instantiate_beta ρ he.1 store
          (.makeAt .absent [arrayStoreKey, CallArguments.protoField] [.var 0, .var proto]) 0
        simp only [instantiate, instantiateArgs_eq_map, List.map_cons, List.map_nil] at hb
        rw [hb]
        simp only [Nat.not_lt_zero, if_false, Nat.sub_zero]
        apply Steps.next (Step.makeFields ?_ rfl) Steps.refl
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hstore
        · cases proto with
          | zero => exact hstore
          | succ i => exact (meaning_value (he.2 i _ (List.getElem?_eq_getElem (by omega)))).1
      refine weaken (fun heap' u hq => ?_) (steps_run run rfl hs)
      obtain ⟨hq, rfl, rfl⟩ := hq
      refine ⟨hq, ?_⟩
      have hr : RegionOf (h ++ (vs ++ [store, (push store ρ) proto] ++ [.nul]))
          (.objAt (slots heap.length [arrayStoreKey, CallArguments.protoField]) .absent (heap.length + 2))
          (some heap.length) (elemSlots h.length vs.length) := by
        refine .inr ⟨heap.length, rfl, ?_, ?_⟩
        · simp [Footprints.storeOf, Footprints.fieldsOf, slots]
        · rw [show h ++ (vs ++ [store, (push store ρ) proto] ++ [.nul]) =
              heap ++ [store, (push store ρ) proto] ++ [.nul] by simp [heap, List.append_assoc]]
          simp [store]
      have hf := freshApart_holds he hh hr (fun l hl => by
        rcases hl with hl | hl
        · cases hl; simp [heap]
        · exact elemSlots_above _ _ l hl)
      simpa only [heap, List.append_assoc] using hf
    · exact none_holds
  · exact none_holds

/-- Whether an unconditional region fact keeps slot `e`'s region apart from
that of `a`'s alias class. -/
def apartFrom (k : Knowledge) (a e : Nat) : Bool :=
  k.indices.any fun atom => atom.cond.isNone && match atom.fact with
    | .apart x y => ((HeapLinks.aliases k.links a).contains x && y == e) ||
        ((HeapLinks.aliases k.links a).contains y && x == e)
    | _ => false

theorem apartFrom_sound {k : Knowledge} {a e : Nat} {ρ h} (hc : apartFrom k a e = true) (hk : Holds k ρ h) :
    RegionsApart h (ρ a) (ρ e) := by
  obtain ⟨atom, ha, hm⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hnone, hf⟩ := hm
  have hat := hk.2.2.2.2.2 atom ha fun b hb => by rw [hnone] at hb; cases hb
  cases hfact : atom.fact
  case apart x y =>
    rw [hfact] at hf hat
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hf
    rcases hf with ⟨hx, rfl⟩ | ⟨hy, rfl⟩
    · rw [← HeapLinks.aliases_eq hk.2.2.1 hx]; exact hat
    · rw [← HeapLinks.aliases_eq hk.2.2.1 hy]; exact regionsApart_symm hat
  all_goals (rw [hfact] at hf; cases hf)

/-- Whether a term reads, through the heap, only locations apart from the
region of `a`'s class: a slot's value, a string's length, or the length of
an array whose region a fact keeps apart. -/
def termApart (k : Knowledge) (a : Nat) (t : Term) : Bool :=
  t.path.isEmpty && match t.kind with
    | .value | .strLength => true
    | .length => apartFrom k a t.slot
    | .view => false

/-- The facts a write at the store of `a`'s array keeps (`region-write`,
`every-apart-write`): a region fact one of whose sides is the written array and
the other an array slot apart from it, or both of whose sides are apart from
it; and a quantified fact over an array apart from it whose bound and free
terms read nothing of its region. -/
def writeAtoms (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (a : Nat) : List IndexAtom :=
  k.indices.filter fun atom => atom.cond.isNone && match atom.fact with
    | .apart x y =>
      ((HeapLinks.aliases k.links a).contains x && apartFrom k a y && arraySlot G Γ y) ||
      ((HeapLinks.aliases k.links a).contains y && apartFrom k a x && arraySlot G Γ x) ||
      (apartFrom k a x && apartFrom k a y)
    | .every s [] stop body => apartFrom k a s && termApart k a stop &&
        body.all fun F => F.vars.all fun b => match b with
          | .free t => termApart k a t
          | .project _ _ => false
          | _ => true
    | _ => false

/-- What an element write at the store cell `target`, which held `xs`,
leaves: `target` holds a store listing old cells of `xs` and at most the one
fresh cell at the old heap's end; every other old location keeps its value,
but the written element cell, one of `xs`. -/
structure WriteHeap (h h' : Heap) (target : Nat) (xs : List (Option Nat)) (written : Option Nat) : Prop where
  store : ∃ xs', h'[target]? = some (.arr xs') ∧ ∀ l, some l ∈ xs' → some l ∈ xs ∨ l = h.length
  kept : ∀ l, l < h.length → l ≠ target → written ≠ some l → h'[l]? = h[l]?
  cell : ∀ c, written = some c → some c ∈ xs

/-- A region apart from the written one keeps its locations' values. -/
theorem untouched {h h' : Heap} {target : Nat} {xs : List (Option Nat)} {written : Option Nat}
    {u v : Val} (hw : WriteHeap h h' target xs written)
    (hu : RegionOf h u (some target) xs) (ha : RegionsApart h u v) :
    ∃ se ys, RegionOf h v se ys ∧ RegionOf h' v se ys ∧
      ∀ l, InRegion (some target) xs l → ∀ m, InRegion se ys m → l ≠ m := by
  obtain ⟨sa, xs0, se, ys, hra, hre, hsep⟩ := ha
  obtain ⟨e1, e2⟩ := regionOf_unique hra hu
  rw [e1, e2] at hsep
  refine ⟨se, ys, hre, ?_, hsep⟩
  rcases hre with hre | ⟨st, rfl, hst, hys⟩
  · exact .inl hre
  · refine .inr ⟨st, rfl, hst, ?_⟩
    rw [hw.kept st (List.getElem?_eq_some_iff.mp hys).1
      (fun he => hsep target (.inl rfl) st (.inl rfl) he.symm)
      (fun he => hsep st (.inr (hw.cell st he)) st (.inl rfl) rfl)]
    exact hys

/-- A term `termApart` admits denotes after the write what it denoted. -/
theorem termApart_kept {k : Knowledge} {a : Nat} {t : Term} {ρ : Env} {h h' : Heap} {target : Nat}
    {xs : List (Option Nat)} {written : Option Nat} {z : Int}
    (hw : WriteHeap h h' target xs written) (hk : Holds k ρ h)
    (hu : RegionOf h (ρ a) (some target) xs) (hc : termApart k a t = true)
    (ht : termValue ρ h t = some z) : termValue ρ h' t = some z := by
  obtain ⟨kind, x, p⟩ := t
  simp only [termApart, Bool.and_eq_true, List.isEmpty_iff] at hc
  obtain ⟨rfl, hc⟩ := hc
  simp only [termValue_nil] at ht ⊢
  cases kind with
  | value => exact ht
  | strLength => exact ht
  | view => simp at hc
  | length =>
    simp only at hc
    obtain ⟨st, ls, hst, hls, rfl, hmax⟩ := lengthOf_store ht
    obtain ⟨se, ys, hre, hre', -⟩ := untouched hw hu (apartFrom_sound hc hk)
    obtain ⟨e1, e2⟩ := regionOf_unique hre (.inr ⟨st, rfl, hst, hls⟩)
    rw [e1, e2] at hre'
    rcases hre' with ⟨he, -⟩ | ⟨st', he, hst', hls'⟩
    · cases he
    · cases he
      simp only [kindValue, lengthOf, hst, hls', hmax, if_true]

theorem writeAtoms_after [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {a : Nat}
    {ρ n W h h'} {target : Nat} {xs : List (Option Nat)} {written : Option Nat}
    (he : EnvOk G Γ ρ (n + 1) W) (hk : Holds k ρ h) (hh : HeapOk (n + 1) W h)
    (hu : RegionOf h (ρ a) (some target) xs) (hw : WriteHeap h h' target xs written) :
    IndexHolds (writeAtoms G Γ k a) ρ h' := by
  intro atom hm hcond
  obtain ⟨hmem, hsel⟩ := List.mem_filter.mp hm
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hsel
  obtain ⟨hnone, hsel⟩ := hsel
  have hat := hk.2.2.2.2.2 atom hmem fun b hb => by rw [hnone] at hb; cases hb
  obtain ⟨xs', hxs', hcells⟩ := hw.store
  have hwritten : RegionOf h' (ρ a) (some target) xs' := by
    rcases hu with ⟨he, -⟩ | ⟨st, he, hst, -⟩
    · cases he
    · cases he; exact .inr ⟨target, rfl, hst, hxs'⟩
  -- The written array beside an array slot apart from it.
  have side : ∀ x y, x ∈ HeapLinks.aliases k.links a → apartFrom k a y = true → arraySlot G Γ y = true →
      RegionsApart h' (ρ x) (ρ y) := by
    intro x y hx hy hs
    rw [HeapLinks.aliases_eq hk.2.2.1 hx]
    obtain ⟨se, ys, hre, hre', hsep⟩ := untouched hw hu (apartFrom_sound hy hk)
    obtain ⟨st, ls, hst, hls, hlt, hbelow⟩ := arraySlot_region hs he hh
    obtain ⟨e1, e2⟩ := regionOf_unique hre (.inr ⟨st, rfl, hst, hls⟩)
    rw [e1, e2] at hre' hsep
    refine ⟨some target, xs', some st, ls, hwritten, hre', fun l hl m hm => ?_⟩
    rcases hl with hl | hl
    · exact hsep l (.inl hl) m hm
    · rcases hcells l hl with hl | rfl
      · exact hsep l (.inr hl) m hm
      · rcases hm with hm | hm
        · cases hm; omega
        · have := hbelow m hm; omega
  cases hfact : atom.fact
  case apart x y =>
    rw [hfact] at hsel hat
    show RegionsApart h' (ρ x) (ρ y)
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hsel
    rcases hsel with (⟨⟨hx, hy⟩, hs⟩ | ⟨⟨hy, hx⟩, hs⟩) | ⟨hx, hy⟩
    · exact side x y hx hy hs
    · exact regionsApart_symm (side y x hy hx hs)
    · obtain ⟨sx, xs1, hrx, hrx', -⟩ := untouched hw hu (apartFrom_sound hx hk)
      obtain ⟨sy, ys1, hry, hry', -⟩ := untouched hw hu (apartFrom_sound hy hk)
      obtain ⟨sa, xs0, sb, ys0, hra, hrb, hsep⟩ := hat
      obtain ⟨e1, e2⟩ := regionOf_unique hra hrx
      obtain ⟨e3, e4⟩ := regionOf_unique hrb hry
      rw [e1, e2, e3, e4] at hsep
      exact ⟨sx, xs1, sy, ys1, hrx', hry', hsep⟩
  case every s p stop body =>
    rw [hfact] at hsel hat
    cases p with
    | cons _ _ => simp at hsel
    | nil =>
    simp only [Bool.and_eq_true, List.all_eq_true] at hsel
    obtain ⟨⟨hs, hstop⟩, hbody⟩ := hsel
    show (IndexFact.every s [] stop body).HoldsAt ρ h'
    obtain ⟨w, st, ls, z, hwp, hst, hls, hz, hall⟩ := hat
    simp only [readPath, Option.some.injEq] at hwp
    subst hwp
    obtain ⟨se, ys, hre, -, hsep⟩ := untouched hw hu (apartFrom_sound hs hk)
    -- A region is an array's: its elements are its store's.
    have hst0 : Footprints.storeOf (ρ s) = some st := by
      rcases hre with ⟨-, hv⟩ | ⟨st0, -, hs0, -⟩
      · rw [hv] at hst; simp [elementsOf, Footprints.storeOf, Footprints.fieldsOf] at hst
      · rw [elementsOf_store hs0] at hst; cases hst; exact hs0
    obtain ⟨e1, e2⟩ := regionOf_unique hre (.inr ⟨st, rfl, hst0, hls⟩)
    rw [e1, e2] at hsep
    have hkeep : ∀ l, InRegion (some st) ls l → ∀ v, h[l]? = some v → h'[l]? = some v := by
      intro l hl v hv
      rw [hw.kept l (List.getElem?_eq_some_iff.mp hv).1
        (fun he => hsep target (.inl rfl) l hl he.symm)
        (fun he => hsep l (.inr (hw.cell l he)) l hl rfl)]
      exact hv
    apply IndexFact.every_frame ⟨ρ s, st, ls, z, rfl, hst, hls, hz, hall⟩
    · intro w hw'; exact hw'
    · intro w st' ls' hw' hst' hls'
      simp only [readPath, Option.some.injEq] at hw'
      subst hw'
      rw [hst] at hst'; cases hst'
      exact hkeep st (.inl rfl) _ hls'
    · intro z' hz'; exact termApart_kept hw hk hu hstop hz'
    · intro w st' ls' hw' hst' hls' F hF i b hb z' hz'
      simp only [readPath, Option.some.injEq] at hw'
      subst hw'
      rw [hst] at hst'; cases hst'
      rw [hls] at hls'; cases hls'
      cases b with
      | index => exact hz'
      | free t => exact termApart_kept hw hk hu (hbody F hF _ hb) hz'
      | elem => exact elementInt_frame hz' fun l v hl hv => hkeep l (.inr (List.mem_of_getElem? hl)) v hv
      | offset d => exact elementInt_frame hz' fun l v hl hv => hkeep l (.inr (List.mem_of_getElem? hl)) v hv
      | project k p => have := hbody F hF (.project k p) hb; contradiction
  all_goals (rw [hfact] at hsel; cases hsel)

/-- A write at the store of `a`'s array keeps `writeAtoms` (`region-write`,
`every-apart-write`) in each heap it returns in. -/
theorem writeAtoms_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {Ξ T : Fam} {k : Knowledge}
    {a : Nat} {ρ n W h} {flds : List (PropKey × Nat)} {cd : CallCode} {oid target : Nat}
    {xs : List (Option Nat)} {b : UInt64} {value : Val}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ρ h) (hh : HeapOk n W h)
    (hobj : ρ a = .objAt flds cd oid) (hfield : flds.lookup arrayStoreKey = some target)
    (hxs : h[target]? = some (.arr xs)) (hv : isVal value = true)
    (hs : Safe Ξ T n W h (.writeAt arrayStoreKey (.objAt flds cd oid)
      (.setElem (.readAt arrayStoreKey (.objAt flds cd oid)) (.num b) value))) :
    SafePost Ξ T (fun h' _ => IndexHolds (writeAtoms G Γ k a) ρ h') n W h
      (.writeAt arrayStoreKey (.objAt flds cd oid)
        (.setElem (.readAt arrayStoreKey (.objAt flds cd oid)) (.num b) value)) := by
  cases n with
  | zero => trivial
  | succ n =>
  have hu : RegionOf h (ρ a) (some target) xs :=
    .inr ⟨target, rfl, by simp [hobj, Footprints.storeOf, Footprints.fieldsOf, hfield], hxs⟩
  have htl : target < h.length := (List.getElem?_eq_some_iff.mp hxs).1
  apply elementWrite_post hfield hxs hv _ _ hs
  · intro cell hc
    have hm : some cell ∈ xs := by
      unfold elemLoc at hc
      cases hi : indexOfBits b with
      | none => simp [hi] at hc
      | some i =>
        simp only [hi, Option.bind_some] at hc
        cases hl : xs[i]? with
        | none => simp [hl] at hc
        | some o =>
          simp only [hl, Option.bind_some] at hc
          cases hc
          exact List.mem_of_getElem? hl
    refine writeAtoms_after (written := some cell) he hk hh hu ⟨⟨xs, ?_, fun l hl => .inl hl⟩, fun l _ hl hc' => ?_, ?_⟩
    · rw [List.getElem?_set_self (by simpa using htl)]
    · have hne : cell ≠ l := fun he => hc' (by rw [he])
      rw [List.getElem?_set_ne (Ne.symm hl), List.getElem?_set_ne hne]
    · intro c hc'; cases hc'; exact hm
  · intro i _ _
    refine writeAtoms_after (written := none) he hk hh hu
      ⟨⟨placeAt xs i h.length, ?_, fun l hl => ExpressionEffects.placeAt_mem hl⟩, fun l hlt hl _ => ?_, ?_⟩
    · rw [List.getElem?_set_self (by simp; omega)]
    · rw [List.getElem?_set_ne (Ne.symm hl), List.getElem?_append_left hlt]
    · intro c hc'; cases hc'

/-- The output of a write, with the facts it keeps one push deeper. -/
def withWritten (out : Knowledge) (kept : List IndexAtom) : Knowledge :=
  { out with indices := out.indices ++ shiftIndices kept }

theorem withWritten_sound {Ξ T : Fam} {out : Knowledge} {kept : List IndexAtom} {ρ n W h t}
    (hk : SafePost Ξ T (fun h' _ => IndexHolds kept ρ h') n W h t)
    (ho : SafePost Ξ T (fun h' u => Holds out (push u ρ) h') n W h t) :
    SafePost Ξ T (fun h' u => Holds (withWritten out kept) (push u ρ) h') n W h t :=
  weaken (fun _ u hq => ⟨hq.1.1, hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1, hq.1.2.2.2.2.1,
    indexHolds_cat hq.1.2.2.2.2.2 (shiftIndices_holds (v := u) hq.2)⟩) (safePost_and ho hk)

theorem boundedRegions_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' _ => IndexHolds (writeAtoms G j.context k a) ρ h') n W h (instantiate 0 ρ j.term) := by
  have hs := boundedWrite_sound hc he hk hw hh
  simp only [boundedWriteCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hslots, -⟩, htypes⟩, hbd⟩, -⟩ := hc
  have hvl : v < j.context.length := by
    split at htypes
    · rename_i R' V hR' hV; exact (List.getElem?_eq_some_iff.mp hV).1
    · cases htypes
  obtain ⟨s, ls, b, idx, hs0, hl, hb, -, -⟩ := bounded_sound hbd hk
  obtain ⟨flds, cd, oid, hoi⟩ : ∃ flds cd oid, ρ a = .objAt flds cd oid := by
    cases hra : ρ a
    case objAt => exact ⟨_, _, _, rfl⟩
    all_goals rw [hra] at hs0; simp [Footprints.storeOf, Footprints.fieldsOf] at hs0
  have hfl : flds.lookup arrayStoreKey = some s := by
    simpa [Footprints.storeOf, Footprints.fieldsOf, hoi] using hs0
  have hval : isVal (ρ v) = true := (meaning_value (he.2 v _ (List.getElem?_eq_getElem hvl))).1
  rw [boundedSlots_eq hslots] at hs ⊢
  have hsafe := HeapObservations.erase hs
  simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero, hoi, hb] at hsafe ⊢
  exact writeAtoms_holds he hk hh hoi hfl hl hval hsafe

/-- The region facts a call growing its receiver's store keeps
(`region-grow`): each between two array slots, whose regions lie in the old
heap, so the cells the call appends, past its end, are apart from either. -/
def grownRegions (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Tm → List IndexAtom
  | .invoke _ _ args => match slotVars args with
    | some is => if is.all (· < Γ.length) then
        k.indices.filter fun a => a.cond.isNone && match a.fact with
          | .apart x y => arraySlot G Γ x && arraySlot G Γ y
          | _ => false
      else []
    | none => []
  | _ => []

/-- The audited append relation puts every appended cell beyond the input
heap. Together with the unchanged prefix, this supplies the cell premise
of a grown region's separation. -/
theorem appended_cells {r : Tm} {args : List Tm} {h h' : Heap} {s xs ys}
    (ha : CallEffects.ReceiverAppends r args h h')
    (hv : ∀ a ∈ args, isVal a = true)
    (hs : Footprints.storeOf r = some s) (hx : h[s]? = some (.arr xs))
    (hy : h'[s]? = some (.arr ys)) (hp : xs <+: ys) :
    ∀ l, some l ∈ ys → some l ∈ xs ∨ h.length ≤ l := by
  obtain ⟨ys', hy', hlen, hel⟩ := ha hv s xs hs hx
  rw [hy] at hy'; cases hy'
  intro l hl
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  by_cases hold : i < xs.length
  · left
    obtain ⟨tail, rfl⟩ := hp
    rw [List.getElem?_append_left hold] at hi
    exact List.mem_of_getElem? hi
  · right
    have hil : i < ys.length := (List.getElem?_eq_some_iff.mp hi).1
    have hj : i - xs.length < args.length := by omega
    obtain ⟨cell, hcell, _, hfresh⟩ := hel (i - xs.length) args[i - xs.length]
      (List.getElem?_eq_getElem hj)
    have heq : xs.length + (i - xs.length) = i := by omega
    rw [heq, hi] at hcell
    cases hcell
    exact hfresh

/-- An array slot's region after a growth of the receiver's store: the same,
or, where it is the receiver's store, its old cells and appended ones past the
old heap. -/
theorem grown_region {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W h h'} {r : Tm} {args : List Tm} {z : Nat}
    (hc : arraySlot G Γ z = true) (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h)
    (hg : CallEffects.ReceiverGrows r h h') (ha : CallEffects.ReceiverAppends r args h h')
    (hv : ∀ a ∈ args, isVal a = true) :
    ∃ sz zs zs', Footprints.storeOf (ρ z) = some sz ∧ h[sz]? = some (.arr zs) ∧ sz < h.length ∧
      ElementsBelow h.length zs ∧ h'[sz]? = some (.arr zs') ∧
      (zs' = zs ∨ (Footprints.storeOf r = some sz ∧ ∀ l, some l ∈ zs' → some l ∈ zs ∨ h.length ≤ l)) := by
  obtain ⟨sz, zs, hst, hzs, hlt, hbelow⟩ := arraySlot_region hc he hh
  rcases hg sz _ hzs with hk | ⟨hr, ls, ls', he', hls', hp, -⟩
  · exact ⟨sz, zs, zs, hst, hzs, hlt, hbelow, hk, .inl rfl⟩
  · cases he'
    exact ⟨sz, zs, ls', hst, hzs, hlt, hbelow, hls', .inr ⟨hr,
      appended_cells ha hv hr hzs hls' hp⟩⟩

theorem grownRegions_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {t : Tm} {ρ n W h h'}
    (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h) (hk : Holds k ρ h)
    (hg : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (ha : CallEffects.ReceiverAppends (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h') :
    IndexHolds (grownRegions G Γ k t) ρ h' := by
  unfold grownRegions
  split
  case h_2 => exact indexHolds_nil _ _
  rename_i f r args
  split
  case h_2 => exact indexHolds_nil _ _
  rename_i is his
  split
  case isFalse => exact indexHolds_nil _ _
  rename_i hlt
  simp only [List.all_eq_true, decide_eq_true_eq] at hlt
  have hes := slotVars_eq his
  subst hes
  have hv : ∀ a ∈ ExpressionEffects.actualsOf (instantiate 0 ρ (.invoke f r (is.map Tm.var))), isVal a = true := by
    intro a hm
    simp only [ExpressionEffects.actualsOf, instantiate, instantiateArgs_eq_map, List.map_map,
      List.mem_map, Function.comp_apply] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    simp only [Nat.not_lt_zero, if_false, Nat.sub_zero]
    exact (meaning_value (he.2 i _ (List.getElem?_eq_getElem (hlt i hi)))).1
  intro a hm hcond
  obtain ⟨hmem, hsel⟩ := List.mem_filter.mp hm
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hsel
  obtain ⟨hnone, hsel⟩ := hsel
  have hat := hk.2.2.2.2.2 a hmem fun b hb => by rw [hnone] at hb; cases hb
  cases hfact : a.fact
  case apart x y =>
    rw [hfact] at hsel hat
    simp only [Bool.and_eq_true] at hsel
    show RegionsApart h' (ρ x) (ρ y)
    obtain ⟨sx, xs, xs', hsx, hxs, hxlt, hxb, hxs', hxg⟩ := grown_region hsel.1 he hh hg ha hv
    obtain ⟨sy, ys, ys', hsy, hys, hylt, hyb, hys', hyg⟩ := grown_region hsel.2 he hh hg ha hv
    obtain ⟨sa, xs0, sb, ys0, hra, hrb, hsep⟩ := hat
    obtain ⟨e1, e2⟩ := regionOf_unique hra (.inr ⟨sx, rfl, hsx, hxs⟩)
    obtain ⟨e3, e4⟩ := regionOf_unique hrb (.inr ⟨sy, rfl, hsy, hys⟩)
    rw [e1, e2, e3, e4] at hsep
    refine ⟨some sx, xs', some sy, ys', .inr ⟨sx, rfl, hsx, hxs'⟩, .inr ⟨sy, rfl, hsy, hys'⟩,
      fun l hl m hm => ?_⟩
    -- Each new cell is an old one or lies past the old heap, where neither
    -- old region reaches.
    have hxl : InRegion (some sx) xs l ∨ h.length ≤ l := by
      rcases hl with hl | hl
      · exact .inl (.inl hl)
      · rcases hxg with rfl | ⟨-, hc⟩
        · exact .inl (.inr hl)
        · exact (hc l hl).imp .inr id
    have hym : InRegion (some sy) ys m ∨ h.length ≤ m := by
      rcases hm with hm | hm
      · exact .inl (.inl hm)
      · rcases hyg with rfl | ⟨-, hc⟩
        · exact .inl (.inr hm)
        · exact (hc m hm).imp .inr id
    have below : ∀ s cells q, s < h.length → ElementsBelow h.length cells →
        InRegion (some s) cells q → q < h.length := by
      intro s cells q hs hb hq
      rcases hq with hq | hq
      · cases hq; exact hs
      · exact hb q hq
    rcases hxl with hxl | hxl <;> rcases hym with hym | hym
    · exact hsep l hxl m hym
    · have := below sx xs l hxlt hxb hxl; omega
    · have := below sy ys m hylt hyb hym; omega
    · -- Both appended to: both stores the receiver's, the same location.
      rcases hxg with rfl | ⟨hrx, -⟩
      · rcases hl with hl | hl
        · cases hl; omega
        · have := hxb l hl; omega
      rcases hyg with rfl | ⟨hry, -⟩
      · rcases hm with hm | hm
        · cases hm; omega
        · have := hyb m hm; omega
      rw [hrx] at hry
      cases hry
      exact absurd rfl (hsep sx (.inl rfl) sx (.inl rfl))
  all_goals (rw [hfact] at hsel; simp at hsel)

end Verification.IndexWrites

namespace Verification.HeapExpressionRules
open ProgramCertificates PositiveGraphs HeapObservations
open PositiveCertificates (InstanceImageCheck)

theorem indexHolds_append {as bs : List HeapKnowledge.IndexAtom} {ρ h}
    (ha : HeapKnowledge.IndexHolds as ρ h) (hb : HeapKnowledge.IndexHolds bs ρ h) :
    HeapKnowledge.IndexHolds (as ++ bs) ρ h := fun a hm hc =>
  (List.mem_append.mp hm).elim (fun hm => ha a hm hc) (fun hm => hb a hm hc)

/-- Literal allocation states its length and fresh locations and frames old index facts. -/
@[nospecialize] def Checker.emptyArrays [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums => (base.run j k e codes sums).map fun out =>
    { out with indices := out.indices ++ IndexWrites.literalArrayAtoms j.context.length j.term ++
        (if (IndexWrites.literalArrayAtoms j.context.length j.term).isEmpty then [] else HeapKnowledge.shiftIndices k.indices) ++
        IndexWrites.regionAtoms G j.context k j.term
               separation := if (IndexWrites.literalArrayAtoms j.context.length j.term).isEmpty then out.separation
        else HeapSeparation.allocate k.separation j.context.length (contractFields G j.context) }
  select := fun j k e codes sums => (base.select j k e codes sums).map fun out =>
    { out with indices := out.indices ++ IndexWrites.literalArrayAtoms j.context.length j.term ++
        (if (IndexWrites.literalArrayAtoms j.context.length j.term).isEmpty then [] else HeapKnowledge.shiftIndices k.indices) ++
        IndexWrites.regionAtoms G j.context k j.term
               separation := if (IndexWrites.literalArrayAtoms j.context.length j.term).isEmpty then out.separation
        else HeapSeparation.allocate k.separation j.context.length (contractFields G j.context) }
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    simp only [CheckResult.map, Option.map_eq_some_iff] at hc
    obtain ⟨out0, hrun, rfl⟩ := hc
    have hs := base.sound hrun hcodes hsums he hk hw hh
    refine weaken (fun _ _ hr =>
      let hq := hr.1; ⟨hq.1.1, hq.1.2.1, hq.1.2.2.1, ?_,
      hq.1.2.2.2.2.1, indexHolds_append (indexHolds_append (indexHolds_append hq.1.2.2.2.2.2 hq.2.1) ?_) hr.2⟩)
      (IndexWrites.regionAtoms_holds he hk hh (IndexWrites.literalArrayAtoms_holds he hk hh hs))
    · split
      · exact hr.1.1.2.2.2.1
      · have hp := hr.1.2.2
        simp only [*, Bool.false_eq_true, if_false] at hp
        exact hp.1
    · split
      · exact HeapKnowledge.indexHolds_nil _ _
      · have hp := hr.1.2.2
        simp only [*, Bool.false_eq_true, if_false] at hp
        exact hp.2

/-- A checker whose steps on slots state the index atoms of their result
(`IndexWrites.stepAtoms`: `length-observed`, `index-mask`, `index-equal`,
`bound-compare`) beside what `base` gives; every step is otherwise `base`'s. -/
@[nospecialize] def Checker.indexing [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums => (base.emptyArrays.run j k e codes sums).map fun out =>
    { out with indices := out.indices ++ (IndexWrites.stepAtoms G j.context k j.term ++
        IndexWrites.linearAtoms G j.context k j.term ++ IndexWrites.lengthAtoms k j.context j.term) }
  select := fun j k e codes sums => (base.emptyArrays.select j k e codes sums).map fun out =>
    { out with indices := out.indices ++ (IndexWrites.stepAtoms G j.context k j.term ++
        IndexWrites.linearAtoms G j.context k j.term ++ IndexWrites.lengthAtoms k j.context j.term) }
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    simp only [CheckResult.map, Option.map_eq_some_iff] at hc
    obtain ⟨out0, hrun, rfl⟩ := hc
    have hs := base.emptyArrays.sound hrun hcodes hsums he hk hw hh
    exact weaken (fun h' u hq => ⟨hq.1.1.1.1, hq.1.1.1.2.1, hq.1.1.1.2.2.1, hq.1.1.1.2.2.2.1, hq.1.1.1.2.2.2.2.1,
      indexHolds_append hq.1.1.1.2.2.2.2.2 (indexHolds_append (indexHolds_append hq.1.1.2 hq.1.2) hq.2)⟩)
      (IndexWrites.lengthAtoms_holds he hk (IndexWrites.linearAtoms_holds he hk (IndexWrites.stepAtoms_holds he hk hs)))

/-- A checker whose `boundedWrite` steps are writes at a checked index
(`IndexWrites.boundedWriteCheck`, `setElem-bounded`), keeping no observation
of the heap; every other step is `base`'s. -/
@[nospecialize] def Checker.boundedWrites [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums => match e with
    | .boundedWrite a i v p =>
      if IndexWrites.boundedWriteCheck G images j k a i v p then
        pure (IndexWrites.withWritten (if IndexWrites.keepsLengths G j k a i then IndexWrites.lengthOutput k
          else ordinaryOutput k) (IndexWrites.writeAtoms G j.context k a))
      else failure
    | _ => base.run j k e codes sums
  select := fun j k e codes sums => match e with
    | .boundedWrite a i v p =>
      if IndexWrites.boundedWriteCheck G images j k a i v p then
        pure (IndexWrites.withWritten (if IndexWrites.keepsLengths G j k a i then IndexWrites.lengthOutput k
          else ordinaryOutput k) (IndexWrites.writeAtoms G j.context k a))
      else failure
    | _ => base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    split at hc
    · split at hc
      · rename_i hck
        cases hc
        apply IndexWrites.withWritten_sound (IndexWrites.boundedRegions_sound hck he hk hw hh)
        split
        · rename_i hkeep
          exact IndexWrites.boundedLength_sound hck hkeep he hk hw hh
        · exact IndexWrites.boundedWrite_sound hck he hk hw hh
      · cases hc
    · exact base.sound hc hcodes hsums he hk hw hh

end Verification.HeapExpressionRules
