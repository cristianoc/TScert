import Verification.Semantics.StringPostconditions

import Verification.Programs.HeapExpressionRules
import Verification.Semantics.ApartSupport
import Verification.Programs.ExpressionEffects
import Verification.Semantics.IndexNumbers
import Verification.Semantics.ArithmeticRules
import Verification.Semantics.StepRelations
import Verification.Semantics.SurvivalSeparation

/-! # Writes at a checked index

The index facts (`HeapKnowledge.IndexAtom`) and the write they admit
(PROGRAM-TYPING.md, "Writes at a checked index"). A guard
`(k & m) !== k || k > xs.length`, `m` a mask whose `ToInt32` is a natural
below `2^31`, states them in four steps: the conjunction is an index
(`index-mask`), strict equality with an index is one where it answers `true`
(`index-equal`), the read of a spine's length a read link names is that
array's length (`length-observed`), and a comparison of an index with that
length bounds it on the answer giving `k ≤ length` (`bound-compare`). Each is
a layer of `Checker.ordinary` adding ats to the output its base step's
check gives. The write `x.[] := x.[]⟦k ↦ v⟧` on a homogeneous writable array
is safe where `bound(x, k)` holds (`setElem-bounded`): it lands on a present
element or appends, and leaves no hole. -/
namespace Verification.IndexWrites
variable {ε : Verification.HeapKnowledge.EntryState}
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
  | zero => assumption
  | succ n =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
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
  | zero => assumption
  | succ n =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
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
        | zero => assumption
        | succ m =>
          obtain ⟨hrf, hs⟩ := hs
          refine ⟨hrf, ?_⟩
          rcases hs with (⟨hval, ht, hq⟩ | ⟨u, hr, -⟩) | ⟨U', h'', t'', -, -, step', -, -⟩
          · exact .inl (.inl ⟨hval, ht, hq, rfl, hv⟩)
          · exact absurd (raises_not_val hr) (by simp [(binop_values hv).2.2])
          · exact absurd step' (value_no_step (binop_values hv).2.2)
      | arithThrow _ => exact throw_post rfl hs

/-- A spine's length gives, where it returns, the number of its entries, in
the heap it started in. -/
theorem len_run {Ξ T : Fam} {Q : Post} {ls : List (Option Nat)} :
    ∀ {n W h}, SafePost Ξ T Q n W h (.lenOf (.arr ls)) →
      SafePost Ξ T (fun h' u => Q h' u ∧ h' = h ∧ u = .num (bitsOfNat ls.length)) n W h (.lenOf (.arr ls)) := by
  intro n W h hs
  cases n with
  | zero => assumption
  | succ n =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hval, -, -⟩ | ⟨u, hr, -⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · simp [isVal] at hval
    · cases hr with
      | lenC hr => exact absurd (raises_not_val hr) (by simp [isVal])
    · refine .inr ⟨U, h', t', hx, hu, step, hh, ?_⟩
      cases step with
      | lenC s => exact absurd s (value_no_step rfl)
      | lenV =>
        cases n with
        | zero => assumption
        | succ m =>
          obtain ⟨hrf, hs⟩ := hs
          refine ⟨hrf, ?_⟩
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
    | zero => assumption
    | succ n =>
      obtain ⟨hrf, hs⟩ := hs
      refine ⟨hrf, ?_⟩
      rcases hs with (⟨hv', ht, hq⟩ | hr) | ⟨_, _, _, _, _, step, _, _⟩
      · exact .inl (.inl ⟨hv', ht, hq, rfl, rfl⟩)
      · exact absurd hr (val_not_thrown hv)
      · exact False.elim (value_no_step hv step)
  | next step run ih =>
    intro n W hs
    cases n with
    | zero => assumption
    | succ n =>
      obtain ⟨hrf, hs⟩ := hs
      refine ⟨hrf, ?_⟩
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
      simp only [instantiateArgs, instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hv i hs.1
      · exact ih hs.2 a ha


/-- Array literals with value slots have exactly their number of elements. -/
def literalArrayAtoms (n : Nat) (t : Tm) : List IndexAtom :=
  match t with
  | .letE (.arrLit es) (.makeAt .absent [s, p] [.var 0, .var proto]) =>
    if s == arraySpineKey && p == CallArguments.protoField && decide (proto < n + 1) &&
        appendSlots n es && decide (es.length ≤ maxArrayLength) then
      [{ fact := .linear (.le [(.length 0, 1)] es.length) },
       { fact := .linear (.le [(.length 0, -1)] (-(es.length : Int))) }]
    else []
  | _ => []

theorem literalArrayAtoms_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {Ξ T : Fam} {Q : Post} {ρ n W h t k}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) (hh : HeapOk n W h) (hs : SafePost Ξ T Q n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds ε (literalArrayAtoms Γ.length t) (push u ρ) h' ∧
      (if (literalArrayAtoms Γ.length t).isEmpty then True else
        HeapSeparation.Holds (HeapSeparation.allocate k.separation Γ.length
          (HeapExpressionRules.contractFields G Γ)) (push u ρ) ∧
        IndexHolds ε (shiftIndices k.indices) (push u ρ) h'))
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
      let spine := Tm.arr (elemSlots h.length vs.length)
      let heap := h ++ vs
      have hspine : isVal spine = true := rfl
      have run : Steps 3 h (instantiate 0 ρ (.letE (.arrLit es)
          (.makeAt .absent [arraySpineKey, CallArguments.protoField] [.var 0, .var proto])))
          (heap ++ [spine, (push spine ρ) proto] ++ [.nul])
          (.objAt (slots heap.length [arraySpineKey, CallArguments.protoField]) .absent (heap.length + 2)) := by
        simp only [instantiate, instantiateArgs_eq_map, List.map_cons, List.map_nil]
        apply Steps.next (Step.letC (Step.arrAlloc hvs (by omega)))
        apply Steps.next (Step.letV hspine)
        have hb := instantiate_beta ρ he.1 spine
          (.makeAt .absent [arraySpineKey, CallArguments.protoField] [.var 0, .var proto]) 0
        simp only [instantiate, instantiateArgs_eq_map, List.map_cons, List.map_nil] at hb
        rw [hb]
        simp only [Nat.not_lt_zero, ite_false, Nat.sub_zero]
        apply Steps.next (Step.makeFields ?_ rfl) Steps.refl
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hspine
        · cases proto with
          | zero => exact hspine
          | succ i => exact (meaning_value (he.2 i _ (List.getElem?_eq_getElem (by omega)))).1
      refine weaken (fun heap' u hq => ?_) (steps_run run rfl hs)
      obtain ⟨hq, rfl, rfl⟩ := hq
      refine ⟨hq, ?_, ?_⟩
      · have hl : termValue ε (push (.objAt (slots heap.length [arraySpineKey, CallArguments.protoField]) .absent (heap.length + 2)) ρ)
            (heap ++ [spine, (push spine ρ) proto] ++ [.nul]) (.length 0) = some (es.length : Int) := by
          simp [termValue_length, push, lengthOf, Footprints.spineOf, Footprints.fieldsOf, slots,
            spine, elemSlots, hlen, hmax, arraySpineKey, CallArguments.protoField]
        simp only [termValue_length, List.append_assoc, List.cons_append, List.nil_append] at hl
        intro a ha _
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;>
          simp [IndexFact.HoldsAt, Linear.Fact.vars, Linear.Fact.Holds, Linear.Form.eval, termValuation, hl]
      · refine ⟨HeapSeparation.allocate_holds hk.2.2.2.1
          (HeapExpressionRules.fresh_apart_from he hh (by simp [heap])), ?_⟩
        -- The allocation's effect is empty: the tolerant frame at `all`.
        have hkx : Holds k ε ρ (heap ++ [spine, (push spine ρ) proto] ++ [.nul]) := by
          refine Footprints.knowledge_frame_empty hk (Footprints.Closed.holds_empty.mpr ?_)
          simp only [heap, List.append_assoc]; exact List.prefix_append _ _
        exact (shift_holds hkx).2.2.2.2.2
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
  | zero => assumption
  | succ n =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hval, -, -⟩ | ⟨u, hr, -⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · simp [isVal] at hval
    · cases hr with
      | lenC hr => exact absurd (raises_not_val hr) (by simp [isVal])
    · refine .inr ⟨U, h', t', hx, hu, step, hh, ?_⟩
      cases step with
      | lenC s => exact absurd s (value_no_step rfl)
      | lenStr hl =>
        cases n with
        | zero => assumption
        | succ m =>
          obtain ⟨hrf, hs⟩ := hs
          refine ⟨hrf, ?_⟩
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

theorem indexed_sound {k : Knowledge} {a : Nat} {ρ h} (hc : indexed k a = true) (hk : Holds k ε ρ h) :
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
  | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => rw [hfact] at hf; cases hf

/-- The arrays whose spine's length a slot of `n`'s class holds, by unconditional ats. -/
def lengthsOf (k : Knowledge) (n : Nat) : List Nat :=
  k.indices.filterMap fun atom => if atom.cond.isNone then
    match atom.fact with
    | .length x n' => if (HeapLinks.aliases k.links n).contains n' then some x else none
    | _ => none
  else none

theorem lengthsOf_sound {k : Knowledge} {n x : Nat} {ρ h} (hx : x ∈ lengthsOf k n) (hk : Holds k ε ρ h) :
    ∃ s ls, Footprints.spineOf (ρ x) = some s ∧ h[s]? = some (.arr ls) ∧ ρ n = .num (bitsOfNat ls.length) ∧
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
    | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => rw [hfact] at hm; cases hm
  · cases hm

/-- The arrays a slot of `s`'s class was read from as their spine: read links
at the spine field. -/
def spineReaders (k : Knowledge) (s : Nat) : List Nat :=
  k.links.filterMap fun g => if !g.alias && !g.optional && g.field == arraySpineKey &&
    (HeapLinks.aliases k.links s).contains g.value then some g.cell else none

theorem spineReaders_sound {k : Knowledge} {s x : Nat} {ρ h} (hx : x ∈ spineReaders k s) (hk : Holds k ε ρ h) :
    ∃ l, Footprints.spineOf (ρ x) = some l ∧ h[l]? = some (ρ s) := by
  obtain ⟨g, hg, hm⟩ := List.mem_filterMap.mp hx
  split at hm
  · rename_i hc
    cases hm
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem] at hc
    obtain ⟨⟨⟨hal, hopt⟩, hfld⟩, hval⟩ := hc
    have hl := hk.2.2.1 g hg
    simp only [hal, hopt, Bool.false_eq_true, ite_false] at hl
    obtain ⟨flds, c, oid, l, hcell, hf, hl⟩ := hl
    refine ⟨l, ?_, ?_⟩
    · rw [hcell]; simp only [Footprints.spineOf, Footprints.fieldsOf]; rw [← hfld]; exact hf
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
    (hc : maskSlot G Γ k m = true) (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) :
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

/-- Whether a slot's type is a spine: one list contract. -/
def spineSlot (G : NormalGraph ι) (Γ : List (Ty ι)) (s : Nat) : Bool :=
  match Γ[s]? with
  | some S => match expand G S with
    | [.list _ []] => true
    | _ => false
  | none => false

theorem spineSlot_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {s : Nat} {ρ n W}
    (hc : spineSlot G Γ s = true) (he : EnvOk G Γ ρ n W) : ∃ ls, ρ s = .arr ls ∧ ls.length ≤ maxArrayLength := by
  unfold spineSlot at hc
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

/-- Whether a clause holds safe integers alone: the clause `int`, or a
numeric literal or tag set each of whose numbers decodes as a safe integer
(the inclusions of a clause in `int`, `PositiveRules.CoversWith`). -/
def intClause {α : Type} : Clause α → Bool
  | .int => true
  | .numLit b => (SafeIntegers.safeIntOfBits b).isSome
  | .numIn S => S.all fun b => (SafeIntegers.safeIntOfBits b).isSome
  | _ => false

/-- What a slot's type states of its value as an integer: where the type is
plain and each of its clauses holds safe integers alone (`intClause`), that
the value is a safe integer (`some _`), and, where the type is one literal,
the integer it is (`some (some i)`). -/
def typeInt (G : NormalGraph ι) (Γ : List (Ty ι)) (a : Nat) : Option (Option Int) :=
  match Γ[a]? with
  | some S => if G.plainTy S then
      if (expand G S).all intClause then some (match expand G S with
        | [.numLit b] => SafeIntegers.safeIntOfBits b
        | _ => none) else none
    else none
  | none => none

theorem intClause_sound {G : NormalGraph ι} {c : Clause (List ι)} {n W v}
    (hc : intClause c = true) (hv : clauseSem G c n W v) :
    ∃ b, v = .num b ∧ (SafeIntegers.safeIntOfBits b).isSome := by
  replace hv := hv.1
  cases c <;> simp only [intClause, reduceCtorEq] at hc
  case numLit b => exact ⟨b, by simpa [semWithArgs] using hv, hc⟩
  case numIn S =>
    obtain ⟨b, hb, rfl⟩ : ∃ b ∈ S, v = .num b := by simpa [semWithArgs] using hv
    exact ⟨b, rfl, List.all_eq_true.mp hc b hb⟩
  case int =>
    obtain ⟨b, rfl, hb⟩ : ∃ b, v = .num b ∧ SafeIntegers.safeIntOfBits b ≠ none := by
      simpa [semWithArgs, PositiveNormalization.intT] using hv
    exact ⟨b, rfl, Option.isSome_iff_ne_none.mpr hb⟩

/-- **A slot's type states its value a safe integer**, and, at one literal,
that integer. -/
theorem typeInt_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {a : Nat} {r : Option Int} {ρ n W}
    (hc : typeInt G Γ a = some r) (he : EnvOk G Γ ρ n W) :
    (intValue (ρ a)).isSome ∧ ∀ i, r = some i → ∃ b, ρ a = .num b ∧ SafeIntegers.SafeInt b i := by
  unfold typeInt at hc
  split at hc
  · rename_i S hS
    split at hc
    · rename_i hp
      split at hc
      · rename_i hall
        cases hc
        have hm := (expand_sem G S hp n W (ρ a)).mp (he.2 a S hS)
        obtain ⟨c, hcm, hsem⟩ := hm
        obtain ⟨b, hb, hi⟩ := intClause_sound (List.all_eq_true.mp hall c hcm) hsem
        refine ⟨by simp [hb, intValue, hi], fun i hr => ?_⟩
        split at hr
        · rename_i b' hx
          rw [hx] at hcm
          simp only [List.mem_singleton] at hcm
          subst hcm
          exact ⟨b', by simpa [clauseSem, rowSem, semWithArgs] using hsem.1, SafeIntegers.safeIntOfBits_sound hr⟩
        · cases hr
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
other slot one higher: the length of a spine a read link names
(`length-observed`), an index from a conjunction with a mask (`index-mask`),
an index equal to one (`index-equal`, where the equality answers `true`),
and an index bounded by a length (`bound-compare`, on the answer giving it). -/
def stepAtoms [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Tm → List IndexAtom
  | .lenOf (.var s) =>
    if spineSlot G Γ s then (spineReaders k s).map fun x => ⟨.length (x + 1) 0, none, false⟩ else []
  | .arith op (.var a) (.var b) =>
    if a < Γ.length ∧ b < Γ.length then
      match op with
      | .bitAnd => if maskSlot G Γ k a || maskSlot G Γ k b then [⟨.index 0, none, false⟩] else []
      | .eq =>
        (if indexed k a then [⟨.index (b + 1), some 0, false⟩] else []) ++
        (if indexed k b then [⟨.index (a + 1), some 0, false⟩] else [])
      | op =>
        (match boundAnswerOf op true with
         | some q => if indexed k a then (lengthsOf k b).map fun x =>
             ⟨.bound (x + 1) (a + 1) (IndexNumbers.strictBoundAnswer op true q), some 0, !q⟩ else []
         | none => []) ++
        (match boundAnswerOf op false with
         | some q => if indexed k b then (lengthsOf k a).map fun x =>
             ⟨.bound (x + 1) (b + 1) (IndexNumbers.strictBoundAnswer op false q), some 0, !q⟩ else []
         | none => [])
    else []
  | _ => []

theorem binop_bitAnd {a b u : Tm} (h : binop .bitAnd a b = some u) :
    ∃ x y, a = .num x ∧ b = .num y ∧ u = .num (arithBits .bitAnd x y) := by
  unfold binop at h
  simp only [reduceCtorEq, ite_false, Arith.relational, Bool.false_eq_true] at h
  split at h <;> simp_all [bigintArith] <;> exact absurd h.1 (by decide)

theorem binop_relational {op : Arith} {x y : UInt64} {u : Tm} (hop : op.relational = true)
    (h : binop op (.num x) (.num y) = some u) : u = boolVal (relationHolds op (doubleOrder x y)) := by
  unfold binop at h
  have hne : op ≠ .eq := by rintro rfl; simp [Arith.relational] at hop
  have hnl : op ≠ .looseEq := by rintro rfl; simp [Arith.relational] at hop
  simp only [hne, hnl, ite_false, hop, ite_true, relationalValue, relNumeric, Option.bind_some,
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
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) (hs : SafePost Ξ T Q n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds ε (stepAtoms G Γ k t) (push u ρ) h') n W h
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
      obtain ⟨ls, hls, hmax⟩ := spineSlot_sound hst he
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, hls] at hs ⊢
      refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (len_run hs)
      obtain ⟨-, rfl, rfl⟩ := hq
      intro atom ha _
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨l, hl, hh⟩ := spineReaders_sound hx hk
      exact ⟨l, ls, hl, by rw [hh, hls], rfl, hmax⟩
    · exact weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _⟩) hs
  · simp only [stepAtoms]
    split
    · rename_i hab
      have ha := hval a hab.1
      have hb := hval b hab.2
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
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
        simp only [binop, ite_true, Option.map_eq_some_iff] at hu
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
              have hle : i + (if IndexNumbers.strictBoundAnswer op true q then 1 else 0) ≤ ls.length := by
                cases hst : IndexNumbers.strictBoundAnswer op true q
                · exact IndexNumbers.le_of_relation hix (boundAnswerOf_sound hq) (truthy_boolVal hcq)
                · exact IndexNumbers.lt_of_relation hix hst (truthy_boolVal hcq)
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
              have hle : i + (if IndexNumbers.strictBoundAnswer op false q then 1 else 0) ≤ ls.length := by
                cases hst : IndexNumbers.strictBoundAnswer op false q
                · exact IndexNumbers.le_of_relation_swap hix (boundAnswerOf_sound hq) (truthy_boolVal hcq)
                · exact IndexNumbers.lt_of_relation_swap hix hst (truthy_boolVal hcq)
              exact ⟨s, ls, x, i, by simpa [push] using hs', hls, by simpa [push] using hx, hix, hle⟩
            · cases hat
          · cases hat
    · exact weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _⟩) hs

/-! ## The linear atoms a step states

A step on safe integers states the integer facts of its result (ARITHMETIC.md,
"Linear facts"): a literal its value, a copy its equality with the copied
slot, a spine's length its range `0 ≤ n ≤ 2^32 - 1`, a comparison its
outcome on each answer, a string's length plus one its sum or `2^53`, and
an operation of an arithmetic rule (`ArithmeticRules.rules`: a sum, a
difference, a product by a constant and the bitwise rules) the rule's
conclusion where the knowledge entails its premises (`ruleAtoms`). An operand is a slot the knowledge states a safe
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
    (hc : knownConstant k a = some c) (hk : Holds k ε ρ h) : valuation ρ a = c := by
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

theorem copiedAtoms_holds {k : Knowledge} {a : Nat} {ρ h} (hk : Holds k ε ρ h) :
    IndexHolds ε (copiedAtoms k a) (push (ρ a) ρ) h := by
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

theorem pastCopies_holds {k : Knowledge} {a : Nat} {ρ h} (hk : Holds k ε ρ h) :
    IndexHolds ε (pastCopies k a) (push (ρ a) ρ) h := by
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
    (ha : IndexHolds ε as ρ h) (hb : IndexHolds ε bs ρ h) : IndexHolds ε (as ++ bs) ρ h := fun a hm hc =>
  (List.mem_append.mp hm).elim (fun hm => ha a hm hc) (fun hm => hb a hm hc)

/-- The result's form of a rule at a step: the output slot `0` where the
result is a safe integer. -/
def resultSlot : ArithmeticRules.Domain → Option (Linear.Form Nat × Int)
  | .safeInteger => some ([(0, 1)], 0)
  | _ => none

/-- The atom of the result's domain: slot `0` a safe integer. -/
def resultAtoms : ArithmeticRules.Domain → List IndexAtom
  | .safeInteger => [⟨.int 0, none, false⟩]
  | _ => []

/-- **A rule's atoms at a step** (`ArithmeticRules`): the operands read as
`operandForm` reads them, known constants as constants, bound by the rule's
domains and constant; where the knowledge entails each premise at the
input slots, the result's domain and each conclusion at the output slots,
the result at slot `0` and an input slot `x` at `x + 1`. -/
def ruleAtoms (k : Knowledge) (r : ArithmeticRules.ArithRule) (a b : Tm) : List IndexAtom :=
  match r.bind (operandForm k true a) (operandForm k true b) with
  | some (σ, K) =>
    match ArithmeticRules.instantiateAll σ K r.premises,
        ArithmeticRules.instantiateAll ((σ.rename (· + 1)).withResult (resultSlot r.result)) K r.conclusion with
    | some ps, some cs =>
      if ps.all fun G => entailsKnown k.indices (valueFact G) then
        resultAtoms r.result ++ cs.map fun G => ⟨.linear (valueFact G), none, false⟩
      else []
    | _, _ => []
  | none => []

/-- The atoms of every rule of an operator at a step, at its operands in
order and, where the operator commutes (`Arith.commutes`), exchanged. -/
def ruleAtomsOf (k : Knowledge) (op : Arith) (a b : Tm) : List IndexAtom :=
  (ArithmeticRules.rules.filter fun r => decide (r.op = .binary op)).flatMap fun r =>
    ruleAtoms k r a b ++ (if op.commutes then ruleAtoms k r b a else [])

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

/-- The integrality each of the slots `slots` has by its type (`typeInt`):
`int(a)`. -/
def typeAtoms (G : NormalGraph ι) (Γ : List (Ty ι)) (slots : List Nat) : List IndexAtom :=
  slots.filterMap fun a => (typeInt G Γ a).map fun _ => ⟨.int a, none, false⟩

theorem typeAtoms_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {slots : List Nat} {ρ n W h}
    (he : EnvOk G Γ ρ n W) : IndexHolds ε (typeAtoms G Γ slots) ρ h := by
  intro atom hat _
  obtain ⟨a, -, hm⟩ := List.mem_filterMap.mp hat
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hm
  exact (typeInt_sound hr he).1

/-- The knowledge a step reads: the facts over the slots it reads, with
the integrality their types state (`typeAtoms`). -/
def typedKnowledge (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (slots : List Nat) : Knowledge :=
  { k with indices := k.indices ++ typeAtoms G Γ slots }

theorem typedKnowledge_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {slots : List Nat} {ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) : Holds (typedKnowledge G Γ k slots) ε ρ h :=
  ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, indexHolds_cat hk.2.2.2.2.2 (typeAtoms_holds he)⟩

/-- The linear atoms a step on slots states of its result. -/
def linearAtoms (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Tm → List IndexAtom
  | .num b => match SafeIntegers.safeIntOfBits b with
    | some i => valueAtoms [] i
    | none => []
  | .var a =>
    (if a < Γ.length ∧ intSlot k.indices a = true then valueAtoms [(a, 1)] 0 else []) ++
      (match typeInt G Γ a with | some (some i) => valueAtoms [] i | _ => []) ++
      (if a < Γ.length then copiedAtoms k a ++ pastCopies k a else [])
  | .lenOf (.var s) =>
    if spineSlot G Γ s then
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
        (match operandForm k false a, operandForm k false b with
        | some (fa, ca), some (fb, cb) =>
          match op with
          | .add => if !(entailsKnown k.indices (valueFact (.le (fa ++ fb) (maxSafe - (ca + cb)))) &&
                entailsKnown k.indices (valueFact (.le ((fa ++ fb).scale (-1)) (maxSafe + (ca + cb))))) &&
                entailsKnown k.indices (valueFact (.le ((fa ++ fb).scale (-1)) (maxSafe + (ca + cb)))) &&
                entailsKnown k.indices (valueFact (.le (fa ++ fb) (maxSafe + 1 - (ca + cb)))) &&
                entailsKnown k.indices (valueFact (.le (fa.scale (-1)) ca)) &&
                entailsKnown k.indices (valueFact (.le (fb.scale (-1)) cb)) &&
                stringLengthPlusOne k fa ca fb cb then
                pastSafeAtoms (fa ++ fb) (ca + cb)
              else []
          | .lt | .le | .gt | .ge => compareAtoms op (fa ++ fb.scale (-1)) (ca - cb)
          | .eq => equalAtoms (fa ++ fb.scale (-1)) (ca - cb)
          | _ => []
        | _, _ => []) ++ ruleAtomsOf k op a b
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
    (ho : operandForm k constants t = some (F, c)) (hk : Holds k ε ρ h) :
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
    IndexHolds ε (valueAtoms F c) (push (.num b) ρ) h := by
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
  | zero => assumption
  | succ n =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hval, ht, hq⟩ | hr) | ⟨U, h', t', -, -, step, -, -⟩
    · exact .inl (.inl ⟨hval, ht, hq, rfl, rfl⟩)
    · exact absurd hr (val_not_thrown hv)
    · exact absurd step (value_no_step hv)

theorem spineSlot_bound {G : NormalGraph ι} {Γ : List (Ty ι)} {s : Nat} {ρ n W}
    (hc : spineSlot G Γ s = true) (he : EnvOk G Γ ρ n W) : ∃ ls, ρ s = .arr ls ∧ ls.length ≤ maxArrayLength :=
  spineSlot_sound hc he

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
    IndexHolds ε (compareAtoms op D c) (push (boolVal (relationHolds op (doubleOrder x y))) ρ) h := by
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
    IndexHolds ε (equalAtoms D c) (push (boolVal (numberEqual x y)) ρ) h := by
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

theorem resultLinear_holds {F : Linear.Form Nat} {c a r : Int} {ρ h} {b : UInt64}
    (hF : ∀ x ∈ F.map (·.1), (intValue (ρ x)).isSome)
    (hb : SafeIntegers.SafeInt b r) (hle : a * r + Linear.Form.eval (valuation ρ) F ≤ c) :
    IndexFact.HoldsAt ε (.linear (valueFact (.le ((0, a) :: shiftForm F) c))) (push (.num b) ρ) h := by
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

/-- **A rule's atoms hold of a step's result** (`ArithmeticRules.ArithRule.apply`):
the premises the knowledge entails hold at the input slots, so the rule's
conclusion holds at the output slots. -/
theorem ruleAtoms_holds {k : Knowledge} {r : ArithmeticRules.ArithRule} (hr : r ∈ ArithmeticRules.rules)
    {o : Arith} (ho : r.op = .binary o) {a b : Tm} {ρ h h'} {u : Tm} (hk : Holds k ε ρ h)
    (hu : binop o (instantiate 0 ρ a) (instantiate 0 ρ b) = some u) :
    IndexHolds ε (ruleAtoms k r a b) (push u ρ) h' := by
  unfold ruleAtoms
  split
  · rename_i σ K hbind
    split
    · rename_i ps cs hps hcs
      split
      · rename_i hall
        have hop : ∀ (t : Tm) F c, operandForm k true t = some (F, c) →
            ∃ x, instantiate 0 ρ t = .num x ∧ SafeIntegers.SafeInt x (Linear.Form.eval (valuation ρ) F + c) :=
          fun t F c ht => (operandForm_sound ht hk).2
        have hprem : ∀ F ∈ r.premises, ∃ G, F.instantiate σ K = some G ∧ G.Holds (valuation ρ) := by
          intro F hF
          obtain ⟨G, hG, he⟩ := ArithmeticRules.instantiateAll_mem hps F hF
          have hc := List.all_eq_true.mp hall G hG
          exact ⟨G, he, holds_valueFact.mp (entailsKnown_sound hk.2.2.2.2.2 hc)⟩
        obtain ⟨v, y, bits, hσ, rfl, hres, hconc⟩ := ArithmeticRules.ArithRule.apply hr ho hbind
          (fun _ F c hf => hop a F c hf) (fun _ F c hf => hop b F c hf) hu hprem
        -- Every input slot a form names holds a safe integer.
        have hdef : ∀ x f, σ x = some f → ∀ s ∈ f.1.map (·.1), (intValue (ρ s)).isSome := by
          intro x f hx s hs
          obtain ⟨hfl, hfr, hfy⟩ := ArithmeticRules.ArithRule.bind_forms hbind
          cases x
          · exact (operandForm_sound (hfl f hx).2 hk).1 s hs
          · exact (operandForm_sound (hfr f hx).2 hk).1 s hs
          all_goals (rw [hfy _ (by simp) (by simp)] at hx; cases hx)
        have hσ' : ((σ.rename (· + 1)).withResult (resultSlot r.result)).Denotes (valuation (push (.num bits) ρ))
            (ArithmeticRules.resultAt v y) := by
          refine ArithmeticRules.Instance.denotes_withResult (fun x _ F c hx => ?_) (fun F c hy => ?_)
          · simp only [ArithmeticRules.Instance.rename, Option.map_eq_some_iff, Prod.mk.injEq] at hx
            obtain ⟨⟨F₀, c₀⟩, hx0, rfl, rfl⟩ := hx
            rw [← hσ x F₀ c₀ hx0]
            exact congrArg (· + c₀) (eval_shiftForm F₀ (.num bits) ρ)
          · cases hd : r.result <;> rw [hd] at hy hres <;>
              first | (simp [resultSlot] at hy; done) | simp only [resultSlot, Option.some.injEq, Prod.mk.injEq] at hy
            obtain ⟨rfl, rfl⟩ := hy
            simp [Linear.Form.eval, valuation, push, intValue_num (show SafeIntegers.SafeInt bits y from hres)]
        intro atom hat _
        rcases List.mem_append.mp hat with hat | hat
        · cases hd : r.result <;> rw [hd] at hat hres <;>
            first | (simp [resultAtoms] at hat; done) | simp only [resultAtoms, List.mem_singleton] at hat
          subst hat
          simp [IndexFact.HoldsAt, push, intValue_num (show SafeIntegers.SafeInt bits y from hres)]
        · obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hat
          obtain ⟨F, hF, he⟩ := ArithmeticRules.instantiateAll_mem' hcs G hG
          refine IndexFact.holdsAt_valueFact.mpr ⟨fun t ht => ?_, (ArithmeticRules.RuleFact.instantiate_holds hσ' he).mpr (hconc F hF)⟩
          obtain ⟨x, f, c, hx, ht⟩ := ArithmeticRules.RuleFact.instantiate_vars he t ht
          have hfy := (ArithmeticRules.ArithRule.bind_forms hbind).2.2
          cases x with
          | result =>
            cases hd : r.result <;> simp only [ArithmeticRules.Instance.withResult, hd] at hx <;>
              first | (simp [resultSlot] at hx; done) | simp only [resultSlot, Option.some.injEq, Prod.mk.injEq] at hx
            obtain ⟨rfl, rfl⟩ := hx
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at ht
            subst ht
            rw [hd] at hres
            simp [push, intValue_num (show SafeIntegers.SafeInt bits y from hres)]
          | left | right =>
            simp only [ArithmeticRules.Instance.withResult, ArithmeticRules.Instance.rename, Option.map_eq_some_iff,
              Prod.mk.injEq] at hx
            obtain ⟨⟨F₀, c₀⟩, hx0, rfl, rfl⟩ := hx
            simp only [List.map_map, Function.comp_def, List.mem_map] at ht
            obtain ⟨⟨s, _⟩, hs, rfl⟩ := ht
            simpa [push] using hdef _ _ hx0 s (List.mem_map.mpr ⟨_, hs, rfl⟩)
          | third =>
            simp [ArithmeticRules.Instance.withResult, ArithmeticRules.Instance.rename,
              hfy .third (by simp) (by simp)] at hx
          | len z =>
            simp [ArithmeticRules.Instance.withResult, ArithmeticRules.Instance.rename,
              hfy (.len z) (by simp) (by simp)] at hx
      · exact indexHolds_nil _ _
    · exact indexHolds_nil _ _
  · exact indexHolds_nil _ _

/-- The atoms of every rule of the step's operator hold of its result. -/
theorem ruleAtomsOf_holds {k : Knowledge} {op : Arith} {a b : Tm} {ρ h h'} {u : Tm} (hk : Holds k ε ρ h)
    (hu : binop op (instantiate 0 ρ a) (instantiate 0 ρ b) = some u) :
    IndexHolds ε (ruleAtomsOf k op a b) (push u ρ) h' := by
  intro atom hat hc
  obtain ⟨r, hr, hat⟩ := List.mem_flatMap.mp hat
  obtain ⟨hr, hop⟩ := List.mem_filter.mp hr
  have hop' : r.op = .binary op := of_decide_eq_true hop
  rcases List.mem_append.mp hat with hat | hat
  · exact ruleAtoms_holds hr hop' hk hu atom hat hc
  · split at hat
    · rename_i hcomm
      rw [ArithmeticRules.binop_comm hcomm] at hu
      exact ruleAtoms_holds hr hop' hk hu atom hat hc
    · cases hat

/-- **The linear atoms a step states hold of its result.** -/
theorem linearAtoms_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {t : Tm}
    {Ξ T : Fam} {Q : Post} {ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) (hs : SafePost Ξ T Q n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds ε (linearAtoms G Γ k t) (push u ρ) h') n W h
      (instantiate 0 ρ t) := by
  have hval : ∀ i, i < Γ.length → isVal (ρ i) = true := fun i hi =>
    (meaning_value (he.2 i _ (List.getElem?_eq_getElem hi))).1
  have none_case : SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds ε [] (push u ρ) h') n W h (instantiate 0 ρ t) :=
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
    · simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, ha, true_and, ite_true] at hs ⊢
      refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (value_run (hval a ha) hs)
      obtain ⟨-, rfl, rfl⟩ := hq
      refine indexHolds_cat (indexHolds_cat ?_ ?_) (indexHolds_cat (copiedAtoms_holds hk) (pastCopies_holds hk))
      rotate_left
      · split
        · rename_i i hl
          obtain ⟨b, hb, hsafe⟩ := (typeInt_sound hl he).2 i rfl
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
    · have hl : typeInt G Γ a = none := by
        simp [typeInt, List.getElem?_eq_none (show Γ.length ≤ a by omega)]
      simp only [ha, false_and, ite_false, List.append_nil, hl]; exact none_case
  | lenOf a =>
    cases a with
    | var s =>
      simp only [linearAtoms]
      split
      · rename_i hst
        obtain ⟨ls, hls, hmax⟩ := spineSlot_bound hst he
        simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, hls] at hs ⊢
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
        · -- Str-Length
          rename_i hst
          obtain ⟨str, hstr⟩ := stringSlot_sound hst he
          simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, hstr] at hs ⊢
          refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (len_str_run hs)
          obtain ⟨-, rfl, rfl, hmax⟩ := hq
          have hsafe : SafeIntegers.SafeInt (bitsOfNat (utf16Units str).length) ((utf16Units str).length : Int) :=
            ⟨by simp [maxStringLength] at hmax ⊢; omega, .inl ⟨by simp [maxStringLength] at hmax; omega, by simp⟩⟩
          have h0 : intValue (push (.num (bitsOfNat (utf16Units str).length)) ρ 0) =
              some ((utf16Units str).length : Int) := intValue_num hsafe
          have hl : termValue ε (push (.num (bitsOfNat (utf16Units str).length)) ρ) h' (.strLength (s + 1)) =
              some ((utf16Units str).length : Int) := by
            simp [push, hstr, strLengthOf, hmax]
          have hv0 : termValuation ε (push (.num (bitsOfNat (utf16Units str).length)) ρ) h' (.value 0) =
              (utf16Units str).length := by simp [termValuation, h0]
          have hv1 : termValuation ε (push (.num (bitsOfNat (utf16Units str).length)) ρ) h' (.strLength (s + 1)) =
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
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, hs0, ht0] at hs ⊢
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
      have h0 : termValue ε (push (.str (s ++ t)) ρ) h' (.strLength 0) =
          some ((utf16Units s).length + (utf16Units t).length : Int) := by
        simp [push, strLengthOf, hlen, hmax]
      have hx' : termValue ε (push (.str (s ++ t)) ρ) h' (.strLength (x + 1)) =
          some ((utf16Units s).length : Int) := by
        simp [push, hs0, strLengthOf, show (utf16Units s).length ≤ maxStringLength by omega]
      have hy' : termValue ε (push (.str (s ++ t)) ρ) h' (.strLength (y + 1)) =
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
        simp only [instantiate] at hs ⊢
        refine weaken (fun h' u hq => ⟨hq.1, ?_⟩) (arith_run ha hb hs)
        obtain ⟨-, -, hu⟩ := hq
        refine indexHolds_cat ?_ (ruleAtomsOf_holds hk hu)
        split
        · rename_i fa ca fb cb hfa hfb
          obtain ⟨hva, xa, hxa, hsa⟩ := operandForm_sound hfa hk
          obtain ⟨hvb, xb, hxb, hsb⟩ := operandForm_sound hfb hk
          rw [hxa, hxb] at hu
          have hlin := linearFacts_holds hk.2.2.2.2.2
          have hvars : ∀ (G' : Linear.Form Nat), G'.map (·.1) = (fa ++ fb).map (·.1) →
              ∀ x ∈ G'.map (·.1), (intValue (ρ x)).isSome := by
            intro G' hG x hx
            rw [hG, List.map_append] at hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hva x hx
            · exact hvb x hx
          split
          · -- add
            rw [ArithmeticRules.binop_num rfl (by decide) (by decide) hu]
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
        · exact indexHolds_nil _ _
      · exact none_case
  | _ => simp only [linearAtoms]; exact none_case

/-! ## A comparison with a length

A strict comparison of a safe integer `k` with a slot `n` holding the length of
an array `x`'s spine states, on the answer giving `k < n`, the facts of `k`
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
    obtain ⟨rfl, rfl⟩ := h <;> simp only [ite_true, Bool.false_eq_true, ite_false] at hr ha <;>
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
    (hk : Holds k ε ρ h) (hj : valuation ρ i = j)
    (below : ∀ (ls : List (Option Nat)), ρ n = .num (bitsOfNat ls.length) →
      ls.length ≤ maxArrayLength → tagHolds .truthy u = q → j - ls.length ≤ -1)
    (hb : ∃ bj, ρ i = .num bj ∧ SafeIntegers.SafeInt bj j) :
    IndexHolds ε (lengthPair k i n q) (push u ρ) h := by
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
          SafeIntegers.indexOfBits_safe hsafe (by omega) (by simp [maxArrayLength] at hmax; omega), by simp; omega⟩
      · cases hat

theorem lengthAtoms_shape {k : Knowledge} {Γ : List (Ty ι)} {t : Tm} (h : lengthAtoms k Γ t ≠ []) :
    ∃ op a b, t = .arith op (.var a) (.var b) := by
  unfold lengthAtoms at h
  split at h
  · exact ⟨_, _, _, rfl⟩
  · exact absurd rfl h

theorem lengthAtoms_holds {k : Knowledge} {Γ : List (Ty ι)} {G : NormalGraph ι} {t : Tm}
    {Ξ T : Fam} {Q : Post} {ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) (hs : SafePost Ξ T Q n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds ε (lengthAtoms k Γ t) (push u ρ) h') n W h
      (instantiate 0 ρ t) := by
  have hval : ∀ i, i < Γ.length → isVal (ρ i) = true := fun i hi =>
    (meaning_value (he.2 i _ (List.getElem?_eq_getElem hi))).1
  by_cases hnil : lengthAtoms k Γ t = []
  · rw [hnil]; exact weaken (fun _ _ hq => ⟨hq, indexHolds_nil _ _⟩) hs
  obtain ⟨op, a, b, rfl⟩ := lengthAtoms_shape hnil
  simp only [lengthAtoms] at hnil ⊢
  split
  · rename_i hab
    simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
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

/-- **A write at an index at most the spine's length** (`setElem-bounded`).
The object `obj` is a record whose spine field, invariant, holds a
homogeneous writable spine; that spine, at its location now, has `ls`, and
`b` is an index `i ≤ |ls|`. The write reads the spine, lands on a present
element or appends (`setElem_spine_safe`), and writes the spine it yields,
which meets the field's contract, back. -/
theorem boundedWrite_safe [DecidableEq ι] {Ξ : Fam} {G : NormalGraph ι} {R S E : Ty ι}
    {fs : List (Stored (Ty ι))} {vs : List (PropKey × Ty ι)} {os : List (OptionalField (Ty ι))}
    {ms : List (MethodMembers.Sig (Ty ι))}
    {ks : List KeyBound} {st : List PropKey} {pr : ArrayPresence} {sr : StorageRole}
    (hr : Represents G R (.refs fs [] vs os ms ks st)) (hm : (arraySpineKey, sr, S) ∈ fs)
    (hS : Represents G S (.list ⟨[], [], some E, false, pr⟩ []))
    {obj vv : Tm} {s : Nat} {ls : List (Option Nat)} {b : UInt64} {i : Nat} {n : Nat} {W : WorldT n} {h : Heap}
    (hobj : meaning G R n W obj) (hs : Footprints.spineOf obj = some s) (hl : h[s]? = some (.arr ls))
    (hb : indexOfBits b = some i) (hi : i ≤ ls.length)
    (hv : meaning G E n W vv) (hw : WorldAdm W) (hh : HeapOk n W h) (hsrc : isSourceVal vv = true)
    (href : RefsOk W (.writeAt arraySpineKey obj (.setElem (.readAt arraySpineKey obj) (.num b) vv))) :
    Safe Ξ nulT n W h (.writeAt arraySpineKey obj (.setElem (.readAt arraySpineKey obj) (.num b) vv)) := by
  obtain ⟨flds, l, c, oid, rfl, hf, hlc, hag⟩ :=
    recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨S, hm, rfl⟩) ((represents_raw hr n W _) hobj).1.1
  have hsl : s = l := by
    simp only [Footprints.spineOf, Footprints.fieldsOf] at hs
    rw [hf] at hs; cases hs; rfl
  subst hsl
  have hvval := (meaning_value hv).1
  have hC : CtxRefs (Tm.writeAt arraySpineKey (.objAt flds .absent oid)) := by ctx_refs
  cases n with
  | zero => exact href
  | succ p =>
    obtain ⟨w, hwv, hwc⟩ := hh.1.2 s c hlc
    rw [hl] at hwv; cases hwv
    have hspine : meaning G S p (trunc p (Nat.le_succ p) W) (.arr ls) := (hag p (by omega) _ _).mp (hwc p (by omega))
    have hv' : meaning G E p (trunc p (Nat.le_succ p) W) vv := (meaning_adm G E).down_le (p + 1) p (by omega) W vv hv
    have hpos : positionTy (⟨[], [], some E, false, pr⟩ : Tuple (Ty ι)) i = some E := by
      simp [positionTy]
    have hframe : RefsOk (trunc p (Nat.le_succ p) W) (.writeAt arraySpineKey (.objAt flds .absent oid) .undef) :=
      RefsOk_trunc _ (hC.frame (t := .setElem (.readAt arraySpineKey (.objAt flds .absent oid)) (.num b) vv) href)
    have hset : RefsOk (trunc p (Nat.le_succ p) W) (.setElem (.arr ls) (.num b) vv) := by
      have hvr : RefsOk W vv := fun r hr => href r (by simp [refs, hr])
      intro r hr
      simp only [refs, List.mem_append] at hr
      rcases hr with (hr | hr) | hr
      · exact read_value_refs hh hl r hr
      · simp at hr
      · exact RefsOk_trunc _ hvr r hr
    refine ⟨href, Or.inr ⟨trunc p (Nat.le_succ p) W, h, _, WExt_refl _, WorldAdm_trunc _ hw,
      .writeC2 rfl (.setC1 (.readField hf hl)), HeapOk_trunc p W h hh, ?_⟩⟩
    apply Safe_bind (.writeAt arraySpineKey (.objAt flds .absent oid)) (Step.writeC2 rfl) (Raises.writeC2 rfl) hC
      p _ h _ (WorldAdm_trunc _ hw) (HeapOk_trunc p W h hh) hframe
      (setElem_spine_safe hS rfl hpos hb hi hspine (WorldAdm_trunc _ hw) (HeapOk_trunc p W h hh) hvval hv' hsrc hset)
    intro j hj U hx hu heap av hok hav ha' hvr
    have hfin : RefsOk U (.writeAt arraySpineKey (.objAt flds .absent oid) av) :=
      hC.ok hvr (RefsOk_mono hx (RefsOk_trunc _ hframe))
    have hobjp : meaning G R p (trunc p (Nat.le_succ p) W) (.objAt flds .absent oid) :=
      (meaning_adm G R).down_le (p + 1) p (by omega) W _ hobj
    have hobj' : meaning G R j U (.objAt flds .absent oid) :=
      (meaning_adm G R).mono j _ U hx _ ((meaning_adm G R).down_le p j hj _ _ hobjp)
    obtain ⟨flds', l', c', oid', heq, hf', hl', hag'⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨S, hm, rfl⟩) ((represents_raw hr j U _) hobj').1.1
    cases heq
    have hcat : ∀ r, roleAt U l' = some r → Cat r av := by
      intro r hr
      have hslot : RefOk U (.slot arraySpineKey l') := hfin _ (by
        simp only [refs, List.mem_append, objRefs, List.mem_cons, List.mem_map]
        exact .inl (.inr ⟨(arraySpineKey, l'), lookup_mem_pair hf', rfl⟩))
      simp only [RefOk, hr] at hslot
      obtain ⟨ls', rfl, -⟩ := ((represents_raw hS j U av) ha').1
      cases r with
      | spine k =>
        cases k with
        | array => exact ⟨ls', rfl⟩
        | view fm N => simp [SlotRole] at hslot
      | _ => simp [SlotRole] at hslot
    exact write_rule (meaning_adm G S) j U heap l' av hav hu hok hf' hl' hag' ha' hcat hfin

/-- The complete element-write execution consumes a postcondition for
both possible updates: an existing element cell followed by the spine
write, or a fresh cell followed by the spine write. -/
theorem elementWrite_post {Ξ T : Fam} {P : Heap → Prop}
    {h : Heap} {flds : List (PropKey × Nat)} {cd : CallCode} {oid target : Nat}
    {xs : List (Option Nat)} {b : UInt64} {value : Val} {n W}
    (hfield : flds.lookup arraySpineKey = some target)
    (hxs : h[target]? = some (.arr xs)) (hv : isVal value = true)
    (hpresent : ∀ cell, elemLoc xs b = some cell →
      P ((h.set cell value).set target (.arr xs)))
    (hfresh : ∀ i, indexOfBits b = some i → elemLoc xs b = none →
      P ((h ++ [value]).set target (.arr (placeAt xs i h.length))))
    (hs : Safe Ξ T n W h (.writeAt arraySpineKey (.objAt flds cd oid)
      (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) (.num b) value))) :
    SafePost Ξ T (fun h' _ => P h') n W h
      (.writeAt arraySpineKey (.objAt flds cd oid)
        (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) (.num b) value)) := by
  cases n with
  | zero => assumption
  | succ n1 =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hbad, _⟩ | hr) | ⟨U1, h1, t1, hx1, hu1, step1, hh1, hs1⟩
    · simp [isVal] at hbad
    · exact .inl (.inr hr)
    obtain ⟨u, hu, rfl, rfl⟩ := ExpressionEffects.elem_read_inv hfield step1
    rw [hxs] at hu; cases hu
    refine .inr ⟨U1, h, _, hx1, hu1, step1, hh1, ?_⟩
    cases n1 with
    | zero => assumption
    | succ n2 =>
      obtain ⟨hrf, hs1⟩ := hs1
      refine ⟨hrf, ?_⟩
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

/-- Whether an unconditional atom bounds a slot of `i`'s class by the spine of
an array of `a`'s class, strictly where `strict`. -/
def boundAtom (k : Knowledge) (a i : Nat) (strict : Bool) : Bool :=
  k.indices.any fun atom => atom.cond.isNone && match atom.fact with
    | .bound x i' st => (HeapLinks.aliases k.links a).contains x && (HeapLinks.aliases k.links i).contains i' &&
        (st || !strict)
    | _ => false

theorem boundAtom_sound {k : Knowledge} {a i : Nat} {strict : Bool} {ρ h} (hc : boundAtom k a i strict = true)
    (hk : Holds k ε ρ h) :
    ∃ s ls b idx, Footprints.spineOf (ρ a) = some s ∧ h[s]? = some (.arr ls) ∧ ρ i = .num b ∧
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
  | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => rw [hfact] at hf; cases hf

/-- Whether the linear facts bound a slot `i` by the length of the spine of an
array of `a`'s class (`HeapKnowledge.lengthBound`). -/
def linearBound (k : Knowledge) (a i : Nat) (strict : Bool) : Bool :=
  lengthBound (HeapLinks.aliases k.links a) k.indices i strict

theorem linearBound_sound {k : Knowledge} {a i : Nat} {strict : Bool} {ρ h} (hc : linearBound k a i strict = true)
    (hk : Holds k ε ρ h) :
    ∃ s ls b idx, Footprints.spineOf (ρ a) = some s ∧ h[s]? = some (.arr ls) ∧ ρ i = .num b ∧
      indexOfBits b = some idx ∧ idx + (if strict then 1 else 0) ≤ ls.length :=
  lengthBound_sound (fun _ hy => HeapLinks.aliases_eq hk.2.2.1 hy) hc hk.2.2.2.2.2

/-- Whether a slot of `i`'s class holds an index at most the length of the
spine of an array of `a`'s class: a bound atom states it, or the linear facts do. -/
def bounded (k : Knowledge) (a i : Nat) (strict : Bool) : Bool := boundAtom k a i strict || linearBound k a i strict

theorem bounded_sound {k : Knowledge} {a i : Nat} {strict : Bool} {ρ h} (hc : bounded k a i strict = true)
    (hk : Holds k ε ρ h) :
    ∃ s ls b idx, Footprints.spineOf (ρ a) = some s ∧ h[s]? = some (.arr ls) ∧ ρ i = .num b ∧
      indexOfBits b = some idx ∧ idx + (if strict then 1 else 0) ≤ ls.length := by
  rcases Bool.or_eq_true_iff.mp hc with hc | hc
  · exact boundAtom_sound hc hk
  · exact linearBound_sound hc hk

/-- The slots of a write at a run-time index: `x.[] := x.[]⟦k ↦ v⟧`. -/
def boundedSlots : Tm → Option (Nat × Nat × Nat)
  | .writeAt f (.var a) (.setElem (.readAt f' (.var a')) (.var i) (.var v)) =>
    if f = arraySpineKey ∧ f' = arraySpineKey ∧ a = a' then some (a, i, v) else none
  | _ => none

theorem boundedSlots_eq {t : Tm} {a i v : Nat} (h : boundedSlots t = some (a, i, v)) :
    t = .writeAt arraySpineKey (.var a) (.setElem (.readAt arraySpineKey (.var a)) (.var i) (.var v)) := by
  unfold boundedSlots at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      cases h; rfl
    · cases h
  · cases h

/-- The spine's element type of a homogeneous writable array type: its type a
record whose invariant spine field holds one list contract of no required
or optional position. -/
def writableElement (G : NormalGraph ι) (R : Ty ι) : Option (Ty ι) :=
  match expand G R with
  | [.refs fs [] _ _ _ _ _] => match (Stored.views fs).lookup arraySpineKey with
    | some S => match expand G S with
      | [.list ⟨[], [], some E, false, _⟩ []] => some E
      | _ => none
    | none => none
  | _ => none

theorem writableElement_sound {G : NormalGraph ι} {R E : Ty ι} (h : writableElement G R = some E) :
    ∃ fs vs os ms ks st sr S pr, Represents G R (.refs fs [] vs os ms ks st) ∧ (arraySpineKey, sr, S) ∈ fs ∧
      Represents G S (.list ⟨[], [], some E, false, pr⟩ []) := by
  unfold writableElement at h
  split at h
  · rename_i fs vs os ms ks st hR
    split at h
    · rename_i S hS
      split at h
      · rename_i pr hE
        cases h
        obtain ⟨sr, hm⟩ := Stored.mem_views.mp (PositiveRules.mem_of_lookup hS)
        exact ⟨fs, vs, os, ms, ks, st, sr, S, pr, hR, hm, hE⟩
      · cases h
    · cases h
  · cases h

/-- Whether the write of a step's evidence is admitted (`setElem-bounded`):
its term `x.[] := x.[]⟦k ↦ v⟧` at the evidence's slots, `x` a homogeneous
writable array whose element type the value's type is below by `sub` and is
an element's payload (`Payload`), the knowledge bounding `k` by `x`'s spine,
and its type `null`. -/
@[nospecialize] def boundedWriteCheck [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (j : Sequent ι) (k : Knowledge) (a i v : Nat) (sub : PositiveCertificates.SubtypeChoices ι) : Bool :=
  boundedSlots j.term == some (a, i, v) && decide (i < j.context.length) &&
    (match j.context[a]?, j.context[v]? with
     | some R, some V => match writableElement G R with
       | some E => PositiveCertificates.checkUsing G images V E sub && PositiveRules.tyIn G .source E
       | none => false
     | _, _ => false) &&
    bounded k a i false && (expand G j.type == [.nul])

theorem boundedWrite_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' u => Holds (HeapExpressionRules.ordinaryOutput k) ε (push u ρ) h') n W h (instantiate 0 ρ j.term) := by
  simp only [boundedWriteCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hslots, -⟩, htypes⟩, hbd⟩, hnul⟩ := hc
  rw [boundedSlots_eq hslots] at href ⊢
  split at htypes
  · rename_i R V hR hV
    split at htypes
    · rename_i E hE
      obtain ⟨fs, vs, os, ms, ks, st, _, S, pr, hrep, hm, hS⟩ := writableElement_sound hE
      obtain ⟨s, ls, b, idx, hs, hl, hb, hidx, hle⟩ := bounded_sound hbd hk
      have hv : meaning G E n W (ρ v) := PositiveCertificates.acceptedUsing (Bool.and_eq_true _ _ |>.mp htypes).1 n W _ (he.2 v V hV)
      have hsafe := boundedWrite_safe (Ξ := excOf G) hrep hm hS (he.2 a R hR) hs hl hidx (by simpa using hle) hv hw hh
        (tyIn_sound (G.sorted G.env) (Bool.and_eq_true _ _ |>.mp htypes).2 hv).1
        (by simpa [instantiate, hb] using href)
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, hb]
      apply HeapObservations.of_value_property (fun _ _ _ u _ => ?_)
      · exact Safe_mono n (fun m _ X u hu => (represents_back (c := .nul) hnul m X u) hu) W h _ hsafe
      · exact HeapExpressionRules.ordinaryOutput_holds hk u _
    · cases htypes
  · cases htypes

/-- The knowledge after a write below its spine's length: what the ordinary
output keeps, and every atom reading spines' lengths alone or locations
`stable` keeps (`ExpressionEffects.elem_var_write_length`, `stable-first`). -/
def lengthOutput (stable : Nat → String → Bool) (k : Knowledge) : Knowledge :=
  { HeapExpressionRules.ordinaryOutput k with
    indices := shiftIndices (keptIndices ⟨true, true, .length⟩ stable k.indices) }

/-- Whether a checked write keeps every spine's length: its index below the
spine's length, at a spine type every position of which holds source
values. -/
def keepsLengths [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) (k : Knowledge) (a i : Nat) : Bool :=
  bounded k a i true && match j.context[a]? with
    | some R => ExpressionEffects.spineFieldEvery G (expand G R) arraySpineKey
    | none => false

theorem boundedLength_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) (hkeep : keepsLengths G j k a i = true) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' u => Holds (lengthOutput (HeapExpressionRules.stableFirst G j.context) k) ε (push u ρ) h') n W h
        (instantiate 0 ρ j.term) := by
  have hs := boundedWrite_sound hc he hk hw hh href
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
    all_goals rw [hra] at hs0; simp [Footprints.spineOf, Footprints.fieldsOf] at hs0
  have hfl : flds.lookup arraySpineKey = some s := by
    simpa [Footprints.spineOf, Footprints.fieldsOf, hoi] using hs0
  rw [boundedSlots_eq hslots] at hs ⊢
  have hsafe : Safe (excOf G) (meaning G j.type) n W h
      (instantiate 0 ρ (.writeAt arraySpineKey (.var a) (.setElem (.readAt arraySpineKey (.var a)) (.var i) (.var v)))) :=
    HeapObservations.erase hs
  have hp := HeapExpressionRules.stableFirst_frame he hw hh
    (ExpressionEffects.elem_var_write_length hvl hil hR hst hoi hfl hl hb hidx (by simp at hle; omega)
      he hh hsafe).post
  refine weaken (fun h' u hq => ?_) hp
  have ho := HeapExpressionRules.ordinaryOutput_holds hk u h'
  exact ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.1, ho.2.2.2.2.1,
    shiftIndices_holds (keptIndices_holds hk.2.2.2.2.2 hq.1 hq.2)⟩

/-! ## Element regions (FOOTPRINTS.md, "Element regions")

A region fact `apart(x, y)` keeps the regions of two values apart: an array
object's spine cell and listed element cells, or a raw spine's cells. An
allocation states it of its result and every array of the context, whose
locations the heap already holds; an element write keeps it where the
written array's region is apart from each side, or is one side and the other
an array of the context; and an element write keeps a quantified fact whose
array, bound and free terms read locations apart from the written region. -/

/-- Whether slot `j`'s type is an array: one record clause whose spine field,
written or read only, holds one list contract. -/
def arraySlot (G : NormalGraph ι) (Γ : List (Ty ι)) (j : Nat) : Bool :=
  match Γ[j]? with
  | some R => match expand G R with
    | [.refs fs [] vs _ _ _ _] =>
      match ((Stored.views fs).lookup arraySpineKey).orElse fun _ => vs.lookup arraySpineKey with
      | some S => match expand G S with
        | [.list _ []] => true
        | _ => false
      | none => false
    | _ => false
  | none => false

/-- Every cell a spine under a tuple contract lists is a location of the world. -/
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

/-- An array slot's region lies in the heap: its spine cell and every cell
its spine lists. -/
theorem arraySlot_region {G : NormalGraph ι} {Γ : List (Ty ι)} {j : Nat} {ρ n W h}
    (hc : arraySlot G Γ j = true) (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h) :
    ∃ st ls, Footprints.spineOf (ρ j) = some st ∧ h[st]? = some (.arr ls) ∧ st < h.length ∧
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
  -- The spine field's location, whose contract implies the spine's type.
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
  have hlist := (represents_raw (show Represents G S (.list T []) from hT) _ _ _ hspine).1
  obtain ⟨ls, rfl, -⟩ := hlist
  refine ⟨l, ls, by simp [hobj, Footprints.spineOf, Footprints.fieldsOf, hf], hwv,
    (List.getElem?_eq_some_iff.mp hwv).1, fun l' hl' => ?_⟩
  obtain ⟨c', hc'⟩ := listT_cells ((represents_raw (show Represents G S (.list T []) from hT) _ _ _ hspine).1) l' hl'
  obtain ⟨c0, hc0, -⟩ := lookup_trunc_inv _ W l' c' hc'
  obtain ⟨u, hu, -⟩ := hh.1.2 l' c0 hc0
  exact (List.getElem?_eq_some_iff.mp hu).1

/-- Two postconditions of one term hold together: its execution is
deterministic. -/
theorem safePost_and {Ξ T : Fam} {Q R : Post} : ∀ {n W W' h t}, SafePost Ξ T Q n W h t →
    SafePost Ξ T R n W' h t → SafePost Ξ T (fun h' u => Q h' u ∧ R h' u) n W h t := by
  intro n; induction n with
  | zero => intros; assumption
  | succ n ih =>
    intro W W' h t hq hr
    obtain ⟨hrf, hq⟩ := hq
    refine ⟨hrf, ?_⟩
    rcases hq with (⟨hv, ht, hq⟩ | hth) | ⟨U, h1, t1, hx, hu, st1, hh1, hq1⟩
    · rcases hr.2 with (⟨_, _, hr⟩ | hth') | ⟨_, _, _, _, _, st2, _, _⟩
      · exact .inl (.inl ⟨hv, ht, hq, hr⟩)
      · exact absurd hth' (val_not_thrown hv)
      · exact absurd st2 (value_no_step hv)
    · exact .inl (.inr hth)
    · rcases hr.2 with (⟨hv', _, _⟩ | hth') | ⟨U2, h2, t2, _, _, st2, _, hr2⟩
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

/-- The array slots an unconditional atom keeps apart from the raw spine in slot 0. -/
def rawPartners (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : List Nat :=
  k.indices.filterMap fun a => if a.cond.isNone then match a.fact with
    | .apart x y =>
      if x == 0 && y != 0 && arraySlot G Γ y then some y
      else if y == 0 && x != 0 && arraySlot G Γ x then some x else none
    | _ => none
    else none

theorem rawPartners_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {y : Nat} {ρ h}
    (hy : y ∈ rawPartners G Γ k) (hk : Holds k ε ρ h) :
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

/-- Empty-path slots `(s, [])` named in a spine separation, including under
guards, with `s < limit`: `readPath h (ρ s) []` is always defined (`some (ρ s)`). -/
def guardedSpineSlots (limit : Nat) : IndexFact → List (Nat × List String)
  | .spineApart s p o q =>
    (if p.isEmpty && s < limit then [(s, [])] else []) ++
    (if q.isEmpty && o < limit then [(o, [])] else [])
  | .guarded _ _ _ B => guardedSpineSlots limit B
  | _ => []

theorem guardedSpineSlots_empty {limit : Nat} :
    ∀ {F : IndexFact} {s p}, (s, p) ∈ guardedSpineSlots limit F → p = []
  | .spineApart _ _ _ _, _, _, hm => by
    simp only [guardedSpineSlots] at hm
    rcases List.mem_append.mp hm with h1 | h2
    · split at h1 <;> simp_all
    · split at h2 <;> simp_all
  | .guarded _ _ _ B, _, _, hm => guardedSpineSlots_empty (F := B) hm
  | .index _, _, _, hm | .length _ _, _, _, hm | .bound _ _ _, _, _, hm
  | .int _, _, _, hm | .pastSafe _, _, _, hm | .linear _, _, _, hm
  | .either _ _, _, _, hm | .element _ _ _, _, _, hm | .every _ _ _ _, _, _, hm
  | .atIndex _ _ _ _ _, _, _, hm | .apart _ _, _, _, hm | .same _ _, _, _, hm => by
    simp [guardedSpineSlots] at hm

/-- Array-length paths `(s, p)` unconditionally defined by `k.indices` with
`s < limit`, plus empty-path slots named in guarded spine separations. -/
def indexPaths (limit : Nat) (k : Knowledge) : List (Nat × List String) :=
  (k.indices.flatMap fun a =>
    if a.cond.isSome then []
    else match a.fact with
      | .linear F => F.vars.filterMap fun t =>
          if !t.atEntry && !t.path.isEmpty && t.kind == .length && t.slot < limit then some (t.slot, t.path) else none
      | .spineApart s p o q =>
          (if !p.isEmpty && s < limit then [(s, p)] else []) ++
          (if !q.isEmpty && o < limit then [(o, q)] else [])
      | .every s p _ _ => if !p.isEmpty && s < limit then [(s, p)] else []
      | .guarded _ _ _ B => guardedSpineSlots limit B
      | _ => []).eraseDups

/-- A fresh array at slot `0` has a spine apart from every existing path in `indexPaths`. -/
def freshSpineApart (limit : Nat) (k : Knowledge) : List IndexAtom :=
  (indexPaths limit k).map fun (s, p) => { fact := .spineApart 0 [] (s + 1) p }

/-- The region facts an allocation states (`region-alloc`): a literal's
spine, of slots, apart from every array slot; its combined object allocation
likewise; and an array object holding the raw spine in slot 0, apart from
every array slot the raw spine is known apart from. Both array object
allocations also separate their fresh spine from existing field paths named in
the state's index facts. -/
def regionAtoms (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Tm → List IndexAtom
  | .arrLit es => match slotVars es with
    | some is => if is.all (· < Γ.length) && decide (is.length ≤ maxArrayLength) then freshApart G Γ else []
    | none => []
  | .makeAt .absent [s, p] [.var 0, .var proto] =>
    if s == arraySpineKey && p == CallArguments.protoField && decide (proto < Γ.length) && spineSlot G Γ 0 then
      (rawPartners G Γ k).map (fun y => { fact := .apart 0 (y + 1) }) ++ freshSpineApart Γ.length k
    else []
  | .letE (.arrLit es) (.makeAt .absent [s, p] [.var 0, .var proto]) =>
    if s == arraySpineKey && p == CallArguments.protoField && decide (proto < Γ.length + 1) &&
        appendSlots Γ.length es && decide (es.length ≤ maxArrayLength) then
      freshApart G Γ ++ freshSpineApart Γ.length k
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
    IndexHolds ε (freshApart G Γ) (push u ρ) (h ++ vs) := by
  intro a ha _
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  have hc : arraySlot G Γ j = true := (List.mem_filter.mp hj).2
  show RegionsApart (h ++ vs) u (ρ j)
  exact fresh_apart_slot hc he hh hu habove

private theorem objRefs_slot_mem {fs : List (PropKey × Nat)} {oid : Nat} {k : PropKey} {l : Nat}
    (hlk : fs.lookup k = some l) : Ref.slot k l ∈ objRefs fs oid := by
  have hm := HeapKnowledge.lookup_mem' hlk
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(k, l), hm, rfl⟩)

private theorem refs_obj_slot_mem {fs : List (PropKey × Nat)} {cd : CallCode} {oid : Nat} {k : PropKey} {l : Nat}
    (hlk : fs.lookup k = some l) : Ref.slot k l ∈ refs (.objAt fs cd oid) := by
  have hm := objRefs_slot_mem (oid := oid) hlk
  cases cd <;> simp [refs, hm]

private theorem slotRole_some {key : PropKey} {o : Option Role} (h : SlotRole key o) : ∃ r, o = some r := by
  cases o with
  | none => cases h
  | some r => exact ⟨r, rfl⟩

theorem refsOk_readPath_extend {n : Nat} {W : WorldT n} {h : Heap} (hh : HeapOk n W h)
    (vs : List Val) : ∀ {p : List String} {v w : Val}, RefsOk W v → readPath (h ++ vs) v p = some w → RefsOk W w
  | [], _, _, hv, hr => by simp only [readPath, Option.some.injEq] at hr; exact hr ▸ hv
  | f :: q, v, w, hv, hr => by
    cases v with
    | objAt fs cd oid =>
      simp only [readPath] at hr
      cases hlk : fs.lookup (.str f) with
      | none => simp [hlk] at hr
      | some l =>
        simp only [hlk] at hr
        have hsr : SlotRole (.str f) (roleAt W l) := hv _ (refs_obj_slot_mem hlk)
        obtain ⟨r, hrw⟩ := slotRole_some hsr
        have hlt : l < h.length := by
          have := roleAt_lt hrw
          have hlen : h.length = (entries W).length := by simpa using hh.1.1
          omega
        rw [List.getElem?_append_left hlt] at hr
        obtain ⟨u, hu, hsh⟩ := hh.2 l r hrw
        simp only [hu] at hr
        exact refsOk_readPath_extend hh vs hsh.2 hr
    | _ => simp [readPath] at hr

theorem refsOk_spineOf_lt {n : Nat} {W : WorldT n} {h : Heap} (hh : HeapOk n W h)
    {v : Val} {l : Nat} (hv : RefsOk W v) (hs : Footprints.spineOf v = some l) : l < h.length := by
  cases v with
  | objAt fs cd oid =>
    simp only [Footprints.spineOf, Footprints.fieldsOf] at hs
    have hsr : SlotRole arraySpineKey (roleAt W l) := hv _ (refs_obj_slot_mem hs)
    obtain ⟨r, hrw⟩ := slotRole_some hsr
    have := roleAt_lt hrw
    have hlen : h.length = (entries W).length := by simpa using hh.1.1
    omega
  | _ => simp [Footprints.spineOf, Footprints.fieldsOf] at hs

theorem indexPaths_defined {limit : Nat} {k : Knowledge} {ρ h s p}
    (hm : (s, p) ∈ indexPaths limit k) (hk : Holds k ε ρ h) :
    ∃ w, readPath h (ρ s) p = some w := by
  have hm' := List.mem_eraseDups.mp hm
  obtain ⟨a, ha, hfa⟩ := List.mem_flatMap.mp hm'
  split at hfa
  · cases hfa
  · rename_i hnone
    have hnone' : a.cond = none := by cases hc : a.cond <;> simp_all
    have hF := hk.2.2.2.2.2 a ha fun b hb => by rw [hnone'] at hb; cases hb
    cases hof : a.fact with
    | linear F =>
      rw [hof] at hfa hF
      obtain ⟨t, ht, htm⟩ := List.mem_filterMap.mp hfa
      split at htm
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at htm
        obtain ⟨rfl, rfl⟩ := htm
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hF.1 t ht)
        rw [termValue_now hc.1.1.1] at hz
        obtain ⟨w, hw, -⟩ := Option.bind_eq_some_iff.mp hz
        exact ⟨w, hw⟩
      · cases htm
    | spineApart s1 p1 s2 p2 =>
      rw [hof] at hfa hF
      obtain ⟨u, w, hu, hw, -⟩ := hF
      rcases List.mem_append.mp hfa with h1 | h2
      · split at h1
        · simp only [List.mem_singleton, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1; exact ⟨u, hu⟩
        · cases h1
      · split at h2
        · simp only [List.mem_singleton, Prod.mk.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2; exact ⟨w, hw⟩
        · cases h2
    | every s1 p1 _ _ =>
      simp only [hof] at hfa
      rw [hof] at hF
      obtain ⟨w, -, -, -, hw, -⟩ := hF
      split at hfa
      · simp only [List.mem_singleton, Prod.mk.injEq] at hfa
        obtain ⟨rfl, rfl⟩ := hfa; exact ⟨w, hw⟩
      · cases hfa
    | guarded _ _ _ B =>
      simp only [hof] at hfa
      have hp := guardedSpineSlots_empty hfa
      exact ⟨ρ s, by rw [hp]; rfl⟩
    | _ => simp only [hof] at hfa; cases hfa

theorem freshSpineApart_holds {limit : Nat} {k : Knowledge} {ρ n W h} {u : Val} {vs : List Val} {lu : Nat}
    (hk : Holds k ε ρ h) (hh : HeapOk n W h) (hρ : RootsOk W ρ)
    (hsp : Footprints.spineOf u = some lu) (hge : h.length ≤ lu) :
    IndexHolds ε (freshSpineApart limit k) (push u ρ) (h ++ vs) := by
  intro a ha _
  obtain ⟨⟨s, p⟩, hmem, rfl⟩ := List.mem_map.mp ha
  dsimp only
  obtain ⟨w, hw⟩ := indexPaths_defined hmem hk
  have hw' : readPath (h ++ vs) (ρ s) p = some w := readPath_extend vs hw
  refine ⟨u, w, rfl, hw', fun s1 s2 hs1 hs2 => ?_⟩
  rw [hsp] at hs1; cases hs1
  have hrb := refsOk_readPath_extend hh vs (hρ s) hw'
  have hlt := refsOk_spineOf_lt hh hrb hs2
  omega

theorem regionAtoms_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {Ξ T : Fam} {Q : Post}
    {ρ n W h t k}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) (hh : HeapOk n W h) (hρ : RootsOk W ρ)
    (hs : SafePost Ξ T Q n W h (instantiate 0 ρ t)) :
    SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds ε (regionAtoms G Γ k t) (push u ρ) h')
      n W h (instantiate 0 ρ t) := by
  cases n with
  | zero => assumption
  | succ n =>
  have hval : ∀ i, i < Γ.length → isVal (ρ i) = true :=
    fun i hi => (meaning_value (he.2 i _ (List.getElem?_eq_getElem hi))).1
  have none_holds : SafePost Ξ T (fun h' u => Q h' u ∧ IndexHolds ε [] (push u ρ) h') (n + 1) W h
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
      obtain ⟨⟨⟨rfl, rfl⟩, hproto⟩, hspine⟩ := hc
      obtain ⟨cells, hcells, -⟩ := spineSlot_sound hspine he
      have hinst : instantiate 0 ρ (.makeAt .absent [arraySpineKey, CallArguments.protoField] [.var 0, .var proto]) =
          .makeAt .absent [arraySpineKey, CallArguments.protoField] [ρ 0, ρ proto] := by
        simp [instantiate, instantiateArgs_eq_map]
      rw [hinst] at hs ⊢
      have run : Steps 1 h (.makeAt .absent [arraySpineKey, CallArguments.protoField] [ρ 0, ρ proto])
          (h ++ [ρ 0, ρ proto] ++ [.nul])
          (.objAt (slots h.length [arraySpineKey, CallArguments.protoField]) .absent (h.length + 2)) :=
        .next (Step.makeFields (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact hval 0 (by
              cases hΓ : Γ with
              | nil => simp [spineSlot, hΓ] at hspine
              | cons _ _ => simp)
          · exact hval proto hproto) rfl) .refl
      refine weaken (fun heap u hq => ?_) (steps_run run rfl hs)
      obtain ⟨hq, rfl, rfl⟩ := hq
      refine ⟨hq, fun a ha hcond => ?_⟩
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
        obtain ⟨hcy, hap⟩ := rawPartners_sound hy hk
        obtain ⟨st, ls, hst, hls, hlt, hbelow⟩ := arraySlot_region hcy he hh
        obtain ⟨sa, xs, sb, ys, hra, hrb, hsep⟩ := hap
        obtain ⟨e1, e2⟩ := regionOf_unique hra (.inl ⟨rfl, hcells⟩)
        obtain ⟨e3, e4⟩ := regionOf_unique hrb (.inr ⟨st, rfl, hst, hls⟩)
        rw [e1, e2, e3, e4] at hsep
        have hlen : (h ++ [ρ 0, ρ proto] ++ [Tm.nul])[h.length]? = some (.arr cells) := by
          simp [hcells]
        refine ⟨some h.length, cells, some st, ls,
          .inr ⟨h.length, rfl, by simp [push, Footprints.spineOf, Footprints.fieldsOf, slots], hlen⟩,
          .inr ⟨st, rfl, hst, by rw [List.append_assoc, List.getElem?_append_left hlt]; exact hls⟩,
          fun l hl m hm => ?_⟩
        rcases hl with hl | hl
        · cases hl
          rcases hm with hm | hm
          · cases hm; omega
          · have := hbelow m hm; omega
        · exact hsep l (.inr hl) m hm
      · rw [List.append_assoc]
        exact freshSpineApart_holds (ε := ε)
          (u := .objAt (slots h.length [arraySpineKey, CallArguments.protoField]) .absent (h.length + 2))
          (lu := h.length) hk hh hρ
          (by simp [Footprints.spineOf, Footprints.fieldsOf, slots]) (Nat.le_refl _) a ha hcond
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
      let spine := Tm.arr (elemSlots h.length vs.length)
      let heap := h ++ vs
      have hspine : isVal spine = true := rfl
      have run : Steps 3 h (instantiate 0 ρ (.letE (.arrLit es)
          (.makeAt .absent [arraySpineKey, CallArguments.protoField] [.var 0, .var proto])))
          (heap ++ [spine, (push spine ρ) proto] ++ [.nul])
          (.objAt (slots heap.length [arraySpineKey, CallArguments.protoField]) .absent (heap.length + 2)) := by
        simp only [instantiate, instantiateArgs_eq_map, List.map_cons, List.map_nil]
        apply Steps.next (Step.letC (Step.arrAlloc hvs (by omega)))
        apply Steps.next (Step.letV hspine)
        have hb := instantiate_beta ρ he.1 spine
          (.makeAt .absent [arraySpineKey, CallArguments.protoField] [.var 0, .var proto]) 0
        simp only [instantiate, instantiateArgs_eq_map, List.map_cons, List.map_nil] at hb
        rw [hb]
        simp only [Nat.not_lt_zero, ite_false, Nat.sub_zero]
        apply Steps.next (Step.makeFields ?_ rfl) Steps.refl
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hspine
        · cases proto with
          | zero => exact hspine
          | succ i => exact (meaning_value (he.2 i _ (List.getElem?_eq_getElem (by omega)))).1
      refine weaken (fun heap' u hq => ?_) (steps_run run rfl hs)
      obtain ⟨hq, rfl, rfl⟩ := hq
      refine ⟨hq, ?_⟩
      have hr : RegionOf (h ++ (vs ++ [spine, (push spine ρ) proto] ++ [.nul]))
          (.objAt (slots heap.length [arraySpineKey, CallArguments.protoField]) .absent (heap.length + 2))
          (some heap.length) (elemSlots h.length vs.length) := by
        refine .inr ⟨heap.length, rfl, ?_, ?_⟩
        · simp [Footprints.spineOf, Footprints.fieldsOf, slots]
        · rw [show h ++ (vs ++ [spine, (push spine ρ) proto] ++ [.nul]) =
              heap ++ [spine, (push spine ρ) proto] ++ [.nul] by simp [heap, List.append_assoc]]
          simp [spine]
      have hf := freshApart_holds (ε := ε) he hh hr (fun l hl => by
        rcases hl with hl | hl
        · cases hl; simp [heap]
        · exact elemSlots_above _ _ l hl)
      have hsf := freshSpineApart_holds (ε := ε) (limit := Γ.length) (k := k)
        (u := .objAt (slots heap.length [arraySpineKey, CallArguments.protoField]) .absent (heap.length + 2))
        (vs := vs ++ [spine, (push spine ρ) proto] ++ [.nul]) (lu := heap.length) hk hh hρ
        (by simp [Footprints.spineOf, Footprints.fieldsOf, slots]) (by simp [heap])
      have hcomb : IndexHolds ε (freshApart G Γ ++ freshSpineApart Γ.length k)
          (push (.objAt (slots heap.length [arraySpineKey, CallArguments.protoField]) .absent (heap.length + 2)) ρ)
          (h ++ (vs ++ [spine, (push spine ρ) proto] ++ [.nul])) := fun a ha hcond => by
        rcases List.mem_append.mp ha with ha | ha
        · exact hf a ha hcond
        · exact hsf a ha hcond
      simpa only [heap, List.append_assoc] using hcomb
    · exact none_holds
  · exact none_holds

/-- **Whether slot `e`'s array is apart from `a`'s** by the one disjointness
check of the knowledge's evidence (`Footprints.knowledgeQuery`): the spine
location and the element cells of either against the spine location and the
element cells of the other. It states the separation alone; that both slots
hold arrays is the premise of its use (`apartFrom_sound`). -/
def apartFrom (k : Knowledge) (a e : Nat) : Bool :=
  let q := (Footprints.knowledgeQuery k).disjoint
  q (.field a arraySpineKey) (.field e arraySpineKey) && q (.field a arraySpineKey) (.cells e) &&
    q (.cells a) (.field e arraySpineKey) && q (.cells a) (.cells e)

/-- A spine's location is the spine field's location of the value holding it. -/
private theorem spine_mem {ρ : Env} {h : Heap} {x st : Nat} (hs : Footprints.spineOf (ρ x) = some st) :
    (Footprints.Region.field x arraySpineKey).mem ρ h st = true := by
  simpa [Footprints.Region.mem, Footprints.spineOf] using hs

/-- A cell a value's spine lists is in its cells region. -/
private theorem cells_mem {ρ : Env} {h : Heap} {x st l : Nat} {ls : List (Option Nat)}
    (hs : Footprints.spineOf (ρ x) = some st) (hls : h[st]? = some (.arr ls)) (hl : some l ∈ ls) :
    (Footprints.Region.cells x).mem ρ h l = true := by
  simp only [Footprints.Region.mem, Footprints.spineCells, List.contains_iff_mem, List.mem_append]
  left
  simpa [Footprints.entriesAt, Footprints.spineOf_lookup hs, hls, spineEntries] using hl

/-- **Apart arrays from the evidence**: where both slots hold arrays, each
spine at a location of the heap holding a spine, the separation the
knowledge's query states of their spines and cells is `RegionsApart`. -/
theorem apartFrom_sound {k : Knowledge} {a e : Nat} {ρ h} {n : Nat} {W : WorldT n} {sa st : Nat}
    {xs ys : List (Option Nat)} (hc : apartFrom k a e = true) (hk : Holds k ε ρ h) (hok : HeapOk n W h)
    (hρ : RootsOk W ρ) (hu : RegionOf h (ρ a) (some sa) xs) (hse : Footprints.spineOf (ρ e) = some st)
    (hys : h[st]? = some (.arr ys)) :
    RegionsApart h (ρ a) (ρ e) := by
  have hq := Footprints.knowledgeQuery_sound hk hok hρ
  simp only [apartFrom, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hss, hsc⟩, hcs⟩, hcc⟩ := hc
  obtain ⟨sa', hsa, hsa', hxs⟩ : ∃ s', some sa = some s' ∧ Footprints.spineOf (ρ a) = some s' ∧
      h[s']? = some (.arr xs) := by
    rcases hu with ⟨h1, -⟩ | h2
    · cases h1
    · exact h2
  cases hsa
  have hxb : ∀ l, some l ∈ xs → l < h.length := fun _ hl => (hok.spine_cells hxs hl).2
  have hyb : ∀ l, some l ∈ ys → l < h.length := fun _ hl => (hok.spine_cells hys hl).2
  refine ⟨some sa, xs, some st, ys, hu, .inr ⟨st, rfl, hse, hys⟩, fun l hl m hm heq => ?_⟩
  subst heq
  rcases hl with hl | hl <;> rcases hm with hm | hm
  · cases hl; cases hm
    exact hq _ _ _ (List.getElem?_eq_some_iff.mp hys).1 hss (spine_mem hsa') (spine_mem hse)
  · cases hl
    exact hq _ _ _ (hyb _ hm) hsc (spine_mem hsa') (cells_mem hse hys hm)
  · cases hm
    exact hq _ _ _ (hxb _ hl) hcs (cells_mem hsa' hxs hl) (spine_mem hse)
  · exact hq _ _ _ (hxb _ hl) hcc (cells_mem hsa' hxs hl) (cells_mem hse hys hm)

/-- **No pair is lost**: an unconditional region fact between an alias of `a`
and `e` makes the query answer each pair `apartFrom` asks. -/
theorem apartFrom_of_atom {k : Knowledge} {a e : Nat} {atom : IndexAtom} (hat : atom ∈ k.indices)
    (hn : atom.cond.isNone = true)
    (hf : (∃ x, atom.fact = .apart x e ∧ x ∈ HeapLinks.aliases k.links a) ∨
      (∃ y, atom.fact = .apart e y ∧ y ∈ HeapLinks.aliases k.links a)) :
    apartFrom k a e = true := by
  have hself : ∀ z, z ∈ HeapLinks.aliases k.links z := fun z => by simp [HeapLinks.aliases]
  have hin : ∀ x y, atom.fact = .apart x y →
      Footprints.SepFact.arrays (x, []) (y, []) ∈ (Footprints.knowledgeEvidence k).facts := by
    intro x y hxy
    have hsep : Footprints.SepFact.arrays (x, []) (y, []) ∈ Footprints.knowledgeSeps k := by
      simp only [Footprints.knowledgeSeps, List.mem_flatMap]
      exact ⟨atom, hat, by simp [hn, hxy, Footprints.factSeps]⟩
    simp [Footprints.knowledgeEvidence, hsep]
  have hby : ∀ (r s : Footprints.Region) x y p q, atom.fact = .apart x y →
      Footprints.arraySite r = some (p, []) → Footprints.arraySite s = some (q, []) →
      x ∈ HeapLinks.aliases k.links p → y ∈ HeapLinks.aliases k.links q →
      (Footprints.knowledgeQuery k).disjoint r s = true := by
    intro r s x y p q hxy hr hs hx hy
    exact Footprints.SepEvidence.query_fact _ (hin x y hxy) (by
      simp [Footprints.SepEvidence.byFact, hr, hs, Footprints.sameSite, Footprints.pathViews,
        Footprints.knowledgeEvidence, hx, hy])
  have hsa : Footprints.arraySite (.field a arraySpineKey) = some (a, []) := by simp [Footprints.arraySite]
  have hse : Footprints.arraySite (.field e arraySpineKey) = some (e, []) := by simp [Footprints.arraySite]
  have hca : Footprints.arraySite (.cells a) = some (a, []) := rfl
  have hce : Footprints.arraySite (.cells e) = some (e, []) := rfl
  simp only [apartFrom, Bool.and_eq_true]
  rcases hf with ⟨x, hxy, hx⟩ | ⟨y, hxy, hy⟩
  · exact ⟨⟨⟨hby _ _ _ _ _ _ hxy hsa hse hx (hself e), hby _ _ _ _ _ _ hxy hsa hce hx (hself e)⟩,
      hby _ _ _ _ _ _ hxy hca hse hx (hself e)⟩, hby _ _ _ _ _ _ hxy hca hce hx (hself e)⟩
  · simp only [Footprints.knowledgeQuery] at hby ⊢
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> rw [Footprints.SepEvidence.query_symm] <;>
      exact hby _ _ _ _ _ _ hxy (by assumption) (by assumption) (hself e) hy

/-- Whether a term reads, through the heap, only locations apart from the
region of `a`'s class: an entry term, which reads the entry state; a slot's
value, a string's length, or the length of an array whose region the one
disjointness check keeps apart (`apartFrom`). -/
def termApart (k : Knowledge) (a : Nat) (t : Term) : Bool :=
  t.atEntry || t.path.isEmpty && match t.kind with
    | .value | .strLength => true
    | .length => apartFrom k a t.slot
    | .view => false

/-- The facts a write at the spine of `a`'s array keeps (`region-write`,
`every-apart-write`): a region fact one of whose sides is the written array and
the other an array slot apart from it, or both of whose sides are array slots
apart from it; and a quantified fact over an array slot apart from it whose
bound and free terms read nothing of its region. Each separation is the one
disjointness check's (`apartFrom`); that a side is an array is its slot's
type (`arraySlot`). -/
def writeAtoms (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (a : Nat) : List IndexAtom :=
  k.indices.filter fun atom => atom.cond.isNone && match atom.fact with
    | .apart x y =>
      ((HeapLinks.aliases k.links a).contains x && apartFrom k a y && arraySlot G Γ y) ||
      ((HeapLinks.aliases k.links a).contains y && apartFrom k a x && arraySlot G Γ x) ||
      (apartFrom k a x && apartFrom k a y && arraySlot G Γ x && arraySlot G Γ y)
    | .every s [] stop body => apartFrom k a s && arraySlot G Γ s && termApart k a stop &&
        body.all fun B => B.targets.isEmpty && B.vars.all fun b => match b with
          | .free t => termApart k a t
          | .project _ _ | .parallel _ _ _ _ => false
          | _ => true
    | _ => false

/-- What an element write at the spine cell `target`, which held `xs`,
leaves: `target` holds a spine listing old cells of `xs` and at most the one
fresh cell at the old heap's end; every other old location keeps its value,
but the written element cell, one of `xs`. -/
structure WriteHeap (h h' : Heap) (target : Nat) (xs : List (Option Nat)) (written : Option Nat) : Prop where
  spine : ∃ xs', h'[target]? = some (.arr xs') ∧ ∀ l, some l ∈ xs' → some l ∈ xs ∨ l = h.length
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
    {nw : Nat} {W : WorldT nw} (hw : WriteHeap h h' target xs written) (hk : Holds k ε ρ h)
    (hok : HeapOk nw W h) (hρ : RootsOk W ρ)
    (hu : RegionOf h (ρ a) (some target) xs) (hc : termApart k a t = true)
    (ht : termValue ε ρ h t = some z) : termValue ε ρ h' t = some z := by
  obtain ⟨kind, x, p, e⟩ := t
  cases e
  case true => exact termValue_entry_some rfl ht
  simp only [termApart, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff] at hc
  obtain ⟨rfl, hc⟩ := hc
  simp only [termValue_nil] at ht ⊢
  cases kind with
  | value => exact ht
  | strLength => exact ht
  | view => simp at hc
  | length =>
    simp only at hc
    obtain ⟨st, ls, hst, hls, rfl, hmax⟩ := lengthOf_spine ht
    obtain ⟨se, ys, hre, hre', -⟩ := untouched hw hu (apartFrom_sound hc hk hok hρ hu hst hls)
    obtain ⟨e1, e2⟩ := regionOf_unique hre (.inr ⟨st, rfl, hst, hls⟩)
    rw [e1, e2] at hre'
    rcases hre' with ⟨he, -⟩ | ⟨st', he, hst', hls'⟩
    · cases he
    · cases he
      simp only [kindValue, lengthOf, hst, hls', hmax, ite_true]

theorem writeAtoms_after [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {a : Nat}
    {ρ n W h h'} {target : Nat} {xs : List (Option Nat)} {written : Option Nat}
    (he : EnvOk G Γ ρ (n + 1) W) (hk : Holds k ε ρ h) (hh : HeapOk (n + 1) W h) (hρ : RootsOk W ρ)
    (hu : RegionOf h (ρ a) (some target) xs) (hw : WriteHeap h h' target xs written) :
    IndexHolds ε (writeAtoms G Γ k a) ρ h' := by
  intro atom hm hcond
  obtain ⟨hmem, hsel⟩ := List.mem_filter.mp hm
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hsel
  obtain ⟨hnone, hsel⟩ := hsel
  have hat := hk.2.2.2.2.2 atom hmem fun b hb => by rw [hnone] at hb; cases hb
  obtain ⟨xs', hxs', hcells⟩ := hw.spine
  have hwritten : RegionOf h' (ρ a) (some target) xs' := by
    rcases hu with ⟨he, -⟩ | ⟨st, he, hst, -⟩
    · cases he
    · cases he; exact .inr ⟨target, rfl, hst, hxs'⟩
  -- The written array beside an array slot apart from it.
  have side : ∀ x y, x ∈ HeapLinks.aliases k.links a → apartFrom k a y = true → arraySlot G Γ y = true →
      RegionsApart h' (ρ x) (ρ y) := by
    intro x y hx hy hs
    rw [HeapLinks.aliases_eq hk.2.2.1 hx]
    obtain ⟨st, ls, hst, hls, hlt, hbelow⟩ := arraySlot_region hs he hh
    obtain ⟨se, ys, hre, hre', hsep⟩ := untouched hw hu (apartFrom_sound hy hk hh hρ hu hst hls)
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
    rcases hsel with (⟨⟨hx, hy⟩, hs⟩ | ⟨⟨hy, hx⟩, hs⟩) | ⟨⟨⟨hx, hy⟩, hsx⟩, hsy⟩
    · exact side x y hx hy hs
    · exact regionsApart_symm (side y x hy hx hs)
    · obtain ⟨stx, lsx, hstx, hlsx, -, -⟩ := arraySlot_region hsx he hh
      obtain ⟨sty, lsy, hsty, hlsy, -, -⟩ := arraySlot_region hsy he hh
      obtain ⟨sx, xs1, hrx, hrx', -⟩ := untouched hw hu (apartFrom_sound hx hk hh hρ hu hstx hlsx)
      obtain ⟨sy, ys1, hry, hry', -⟩ := untouched hw hu (apartFrom_sound hy hk hh hρ hu hsty hlsy)
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
    obtain ⟨⟨⟨hs, hsa⟩, hstop⟩, hbody⟩ := hsel
    show (IndexFact.every s [] stop body).HoldsAt ε ρ h'
    obtain ⟨w, st, ls, z, hwp, hst, hls, hz, hall⟩ := hat
    simp only [readPath, Option.some.injEq] at hwp
    subst hwp
    obtain ⟨sts, lss, hsts, hlss, -, -⟩ := arraySlot_region hsa he hh
    obtain ⟨se, ys, hre, -, hsep⟩ := untouched hw hu (apartFrom_sound hs hk hh hρ hu hsts hlss)
    -- A region is an array's: its elements are its spine's.
    have hst0 : Footprints.spineOf (ρ s) = some st ∧ h[st]? = some (.arr ls) := by
      rcases hre with ⟨-, hv⟩ | ⟨st0, -, hs0, hys⟩
      · rw [hv] at hst; simp [elementsOf] at hst
      · rw [elementsOf_spine hs0] at hst; cases hst
        rw [hys] at hls
        simp only [Option.bind_some, spineEntries, Option.some.injEq] at hls
        subst hls; exact ⟨hs0, hys⟩
    obtain ⟨e1, e2⟩ := regionOf_unique hre (.inr ⟨st, rfl, hst0.1, hst0.2⟩)
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
      obtain ⟨u, hu', hue⟩ := Option.bind_eq_some_iff.mp hls'
      rw [hkeep st (.inl rfl) _ hu']; exact hue
    · intro z' hz'; exact termApart_kept hw hk hh hρ hu hstop hz'
    · intro w st' ls' hw' hst' hls' F hF i t ht v hv
      have hnt := (hbody F hF).1
      simp only [List.isEmpty_iff] at hnt
      rw [hnt] at ht; cases ht
    · intro w st' ls' hw' hst' hls' F hF i b hb z' hz'
      simp only [readPath, Option.some.injEq] at hw'
      subst hw'
      rw [hst] at hst'; cases hst'
      rw [hls] at hls'; cases hls'
      have hbv := (hbody F hF).2 b hb
      cases b with
      | index => exact hz'
      | free t => exact termApart_kept hw hk hh hρ hu hbv hz'
      | elem => exact elementInt_frame hz' fun l v hl hv => hkeep l (.inr (List.mem_of_getElem? hl)) v hv
      | offset d => exact elementInt_frame hz' fun l v hl hv => hkeep l (.inr (List.mem_of_getElem? hl)) v hv
      | project k p => simp at hbv
      | parallel s p k ep => simp at hbv
  all_goals (rw [hfact] at hsel; cases hsel)

/-- A write at the spine of `a`'s array keeps `writeAtoms` (`region-write`,
`every-apart-write`) in each heap it returns in. -/
theorem writeAtoms_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {Ξ T : Fam} {k : Knowledge}
    {a : Nat} {ρ n W h} {flds : List (PropKey × Nat)} {cd : CallCode} {oid target : Nat}
    {xs : List (Option Nat)} {b : UInt64} {value : Val}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) (hh : HeapOk n W h) (hρ : RootsOk W ρ)
    (hobj : ρ a = .objAt flds cd oid) (hfield : flds.lookup arraySpineKey = some target)
    (hxs : h[target]? = some (.arr xs)) (hv : isVal value = true)
    (hs : Safe Ξ T n W h (.writeAt arraySpineKey (.objAt flds cd oid)
      (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) (.num b) value))) :
    SafePost Ξ T (fun h' _ => IndexHolds ε (writeAtoms G Γ k a) ρ h') n W h
      (.writeAt arraySpineKey (.objAt flds cd oid)
        (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) (.num b) value)) := by
  cases n with
  | zero => assumption
  | succ n =>
  have hu : RegionOf h (ρ a) (some target) xs :=
    .inr ⟨target, rfl, by simp [hobj, Footprints.spineOf, Footprints.fieldsOf, hfield], hxs⟩
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
    refine writeAtoms_after (written := some cell) he hk hh hρ hu ⟨⟨xs, ?_, fun l hl => .inl hl⟩, fun l _ hl hc' => ?_, ?_⟩
    · rw [List.getElem?_set_self (by simpa using htl)]
    · have hne : cell ≠ l := fun he => hc' (by rw [he])
      rw [List.getElem?_set_ne (Ne.symm hl), List.getElem?_set_ne hne]
    · intro c hc'; cases hc'; exact hm
  · intro i _ _
    refine writeAtoms_after (written := none) he hk hh hρ hu
      ⟨⟨placeAt xs i h.length, ?_, fun l hl => ExpressionEffects.placeAt_mem hl⟩, fun l hlt hl _ => ?_, ?_⟩
    · rw [List.getElem?_set_self (by simp; omega)]
    · rw [List.getElem?_set_ne (Ne.symm hl), List.getElem?_append_left hlt]
    · intro c hc'; cases hc'

/-! ## The length after a write at the length (PROGRAM-TYPING.md, "Writes at a checked index")

A write `x[k] = v` at `0 ≤ k ≤ |x|` leaves `|x| = max(|x|_before, k + 1)`
with the index `k` present: a present cell keeps the spine, and a fresh
cell is placed at `k` (`placeAt`). So `k < |x|` after it (`write-bound`), and
where `k = |x|` before it, every linear fact over `|x|` and terms the write
keeps holds with `|x|` one longer (`write-append`). -/

/-! ## An index's bits denote an integer -/

/-- **A double an index reads is a safe integer**: the bits `indexOfBits`
reads as `i` are `±0` or `bitsOfNat i`. -/
theorem index_safeInt {x : UInt64} {i : Nat} (h : indexOfBits x = some i) : SafeIntegers.SafeInt x i := by
  obtain ⟨hd, hi⟩ := IndexNumbers.indexOfBits_denotes h
  have hx := x.toNat_lt
  rcases hd with ⟨hz, rfl⟩ | ⟨hs, h1, h2, hv⟩
  · have h0 : (bitsOfNat 0).toNat = 0 := SafeIntegers.bitsOfNat_zero
    refine ⟨by decide, ?_⟩
    rcases hz with hz | hz
    · exact .inl ⟨by decide, by show x.toNat = (bitsOfNat 0).toNat; rw [hz, h0]⟩
    · exact .inr ⟨by decide, by show x.toNat = (bitsOfNat 0).toNat + 2 ^ 63; rw [hz, h0]⟩
  · have hpos := IndexNumbers.denotes_pos hv
    rcases IndexNumbers.denotes_bitsOfNat (L := i) (by omega) with ⟨-, h0⟩ | ⟨hs', h1', h2', hv'⟩
    · omega
    have hc := IndexNumbers.lex_scaled (m1 := x.toNat % 2 ^ 52 + 2 ^ 52) (m2 := (bitsOfNat i).toNat % 2 ^ 52 + 2 ^ 52)
      (E1 := x.toNat / 2 ^ 52 % 2 ^ 11) (E2 := (bitsOfNat i).toNat / 2 ^ 52 % 2 ^ 11) (by omega) (by omega) h1 h1'
    have hsc : IndexNumbers.scaled x = IndexNumbers.scaled (bitsOfNat i) := by rw [hv, hv']
    unfold IndexNumbers.scaled at hsc
    rw [hsc, Nat.compare_eq_eq.mpr rfl] at hc
    have hy := (bitsOfNat i).toNat_lt
    have key : ∀ o1 o2 : Ordering, o1.then o2 = .eq → o1 = .eq ∧ o2 = .eq := by decide
    obtain ⟨he1, he2⟩ := key _ _ hc
    have hE := Int.compare_eq_eq.mp he1
    have hm := Nat.compare_eq_eq.mp he2
    have d1 := Nat.div_add_mod x.toNat (2 ^ 52)
    have d2 := Nat.div_add_mod (bitsOfNat i).toNat (2 ^ 52)
    have heq : x.toNat = (bitsOfNat i).toNat := by omega
    refine ⟨by rw [Int.natAbs_natCast]; omega, .inl ⟨Int.natCast_nonneg _, by rw [Int.natAbs_natCast]; exact heq⟩⟩

open HeapKnowledge in
/-- The change of a term: the receiver's length grows by the actual count. -/
def appendDelta (i count : Nat) (t : Term) : Int :=
  if t == Term.length i then count else 0

open HeapKnowledge in
def appendFact (i count : Nat) : Linear.Fact Term → Linear.Fact Term
  | .le F d => .le F (d + Linear.Form.eval (appendDelta i count) F)
  | .ne F d => .ne F (d + Linear.Form.eval (appendDelta i count) F)

open HeapKnowledge in
/-- A linear fact translated by the exact change of its terms. -/
theorem append_fact_holds {i count : Nat} {ρ : Env} {h h' : Heap} {F : Linear.Fact Term}
    (terms : ∀ t ∈ F.vars, ∀ n, termValue ε ρ h t = some n →
      termValue ε ρ h' t = some (n + appendDelta i count t))
    (hF : (IndexFact.linear F).HoldsAt ε ρ h) :
    (IndexFact.linear (appendFact i count F)).HoldsAt ε ρ h' := by
  obtain ⟨hd, hF⟩ := hF
  have hd' : ∀ t ∈ F.vars, (termValue ε ρ h' t).isSome := by
    intro t ht
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hd t ht)
    simp [terms t ht n hn]
  have eval : ∀ G : Linear.Form Term, (∀ t ∈ G.map (·.1), t ∈ F.vars) →
      Linear.Form.eval (termValuation ε ρ h') G =
        Linear.Form.eval (termValuation ε ρ h) G + Linear.Form.eval (appendDelta i count) G := by
    intro G
    induction G with
    | nil => intro _; simp [Linear.Form.eval]
    | cons tc G ih =>
      obtain ⟨t,c⟩ := tc
      intro hm
      have ht := hm t (by simp)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hd t ht)
      have hn' := terms t ht n hn
      have hi := ih (fun t ht => hm t (by simp [ht]))
      simp only [Linear.Form.eval, termValuation, hn, hn', Option.getD_some, Int.mul_add, hi]
      omega
  cases F with
  | le G d =>
    refine ⟨hd', ?_⟩
    have he := eval G (fun _ ht => ht)
    simp only [appendFact, Linear.Fact.Holds] at hF ⊢
    omega
  | ne G d =>
    refine ⟨hd', ?_⟩
    have he := eval G (fun _ ht => ht)
    simp only [appendFact, Linear.Fact.Holds] at hF ⊢
    omega


/-- **The spine after a write at an index at most its length**: the written
array's spine, at its location, lists a cell at the index, so the index is
below its length; where the index was at the length, the spine is one
longer. -/
theorem boundedWrite_spine [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' _ => ∃ s ls ls' b idx, Footprints.spineOf (ρ a) = some s ∧ h[s]? = some (.arr ls) ∧
        h'[s]? = some (.arr ls') ∧ ρ i = .num b ∧ indexOfBits b = some idx ∧ idx < ls'.length ∧
        ls'.length ≤ max ls.length (idx + 1) ∧ (ls.length ≤ idx → ls'.length = ls.length + 1))
      n W h (instantiate 0 ρ j.term) := by
  simp only [boundedWriteCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hslots, -⟩, htypes⟩, hbd⟩, hnul⟩ := hc
  rw [boundedSlots_eq hslots] at href ⊢
  split at htypes
  · rename_i R V hR hV
    split at htypes
    · rename_i E hE
      obtain ⟨fs, vs, os, ms, ks, st, _, S, pr, hrep, hm, hS⟩ := writableElement_sound hE
      obtain ⟨s, ls, b, idx, hs, hl, hb, hidx, hle⟩ := bounded_sound hbd hk
      have hv : meaning G E n W (ρ v) := PositiveCertificates.acceptedUsing (Bool.and_eq_true _ _ |>.mp htypes).1 n W _ (he.2 v V hV)
      have hsafe := boundedWrite_safe (Ξ := excOf G) hrep hm hS (he.2 a R hR) hs hl hidx (by simpa using hle) hv hw hh
        (tyIn_sound (G.sorted G.env) (Bool.and_eq_true _ _ |>.mp htypes).2 hv).1
        (by simpa [instantiate, hb] using href)
      have hsafe' := Safe_mono n (fun m _ X u hu => (represents_back (c := .nul) hnul m X u) hu) W h _ hsafe
      obtain ⟨flds, cd, oid, hoi⟩ : ∃ flds cd oid, ρ a = .objAt flds cd oid := by
        cases hra : ρ a
        case objAt => exact ⟨_, _, _, rfl⟩
        all_goals rw [hra] at hs; simp [Footprints.spineOf, Footprints.fieldsOf] at hs
      have hfl : flds.lookup arraySpineKey = some s := by
        simpa [Footprints.spineOf, Footprints.fieldsOf, hoi] using hs
      have hval : isVal (ρ v) = true := (meaning_value hv).1
      have hslt : s < h.length := (List.getElem?_eq_some_iff.mp hl).1
      have hle' : idx ≤ ls.length := by simpa using hle
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, hb]
      rw [hoi] at hsafe' ⊢
      refine elementWrite_post hfl hl hval (fun cell hcell => ?_) (fun i' hi' _ => ?_) hsafe'
      · have hlt : idx < ls.length := by
          simp only [elemLoc, hidx, Option.bind_some] at hcell
          cases hq : ls[idx]? with
          | none => simp [hq] at hcell
          | some o => exact (List.getElem?_eq_some_iff.mp hq).1
        refine ⟨s, ls, ls, b, idx, hoi ▸ hs, hl, ?_, rfl, hidx, hlt, by omega, fun h1 => absurd h1 (by omega)⟩
        rw [List.getElem?_set_self (by simpa using hslt)]
      · rw [hidx] at hi'; cases hi'
        refine ⟨s, ls, placeAt ls idx h.length, b, idx, hoi ▸ hs, hl, ?_, rfl, hidx, ?_, ?_, fun h1 => ?_⟩
        · rw [List.getElem?_set_self (by simp; omega)]
        · rw [placeAt_length]; omega
        · rw [placeAt_length]; omega
        · rw [placeAt_length]; omega
    · cases htypes
  · cases htypes

/-- The unconditional linear facts among atoms: the facts before a step a
composition reads (`HeapKnowledge.compose`). -/
def unconditionalLinear (as : List IndexAtom) : List (Linear.Fact Term) :=
  as.filterMap fun a => match a.cond, a.fact with
    | none, .linear F => some F
    | _, _ => none

theorem unconditionalLinear_holds {as : List IndexAtom} {ρ : Env} {h : Heap} (he : IndexHolds ε as ρ h) :
    ∀ F ∈ unconditionalLinear as, (IndexFact.linear F).HoldsAt ε ρ h := by
  intro F hF
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hF
  split at hm
  · rename_i G hc hf
    cases hm
    have := he a ha (fun b hb => by rw [hc] at hb; cases hb)
    rwa [hf] at this
  · cases hm

/-- A term a change keeps, read after it at its own slot. -/
def keptOf (c : Changes) (first : Nat → String → Bool) (t : Term) : Option Term :=
  if t.keptBy c first then some t else none

theorem keptOf_sound {c : Changes} {first : Nat → String → Bool} {ρ : Env} {h h' : Heap}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') :
    ∀ t t' n, keptOf c first t = some t' → termValue ε ρ h t = some n → termValue ε ρ h' t' = some n := by
  intro t t' n ht hn
  unfold keptOf at ht
  split at ht
  · rename_i hk; cases ht; exact termValue_kept hc hf hk hn
  · cases ht

/-- A term a change grows (`Term.grownBy`), read after it at its own slot. -/
def grownOf (c : Changes) (first : Nat → String → Bool) (t : Term) : Option Term :=
  if t.grownBy c first then some t else none

theorem grownOf_sound {c : Changes} {first : Nat → String → Bool} {ρ : Env} {h h' : Heap}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') :
    ∀ t t' n, grownOf c first t = some t' → termValue ε ρ h t = some n →
      ∃ n', termValue ε ρ h' t' = some n' ∧ n ≤ n' := by
  intro t t' n ht hn
  unfold grownOf at ht
  split at ht
  · rename_i hg; cases ht; exact termValue_grown hc hf hg hn
  · cases ht

/-- **The exact growth of a spine's length**: the length of the slot `a`'s
array after the step is its length before it plus `count`, as two facts over
the before- and after-lengths; the length after defined. -/
def lengthGrowth (a count : Nat) : StepRelation :=
  { facts := [.le [(.before (Term.length a), 1), (.after (Term.length a), -1)] (-(count : Int)),
      .le [(.before (Term.length a), -1), (.after (Term.length a), 1)] count]
    defined := [Term.length a] }

/-- The growth relation holds of a step that leaves the array's spine one
`count` longer wherever it was defined. -/
theorem lengthGrowth_holds {a count : Nat} {ρ ρ' : Env} {h h' : Heap}
    (hg : ∀ n, termValue ε ρ h (Term.length a) = some n → termValue ε ρ' h' (Term.length a) = some (n + count)) :
    (lengthGrowth a count).Holds ε ρ h ρ' h' := by
  have hd : (termValue ε ρ h (Term.length a)).isSome → ∃ n, termValue ε ρ h (Term.length a) = some n ∧
      termValue ε ρ' h' (Term.length a) = some (n + count) := by
    intro hs
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨n, hn, hg n hn⟩
  refine ⟨fun F hF hdef => ?_, fun hall t ht => ?_, fun t ht => by simp [lengthGrowth] at ht⟩
  · obtain ⟨n, hn, hn'⟩ := hd (hdef _ (by
      simp only [lengthGrowth, List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl <;> simp [Linear.Fact.vars]))
    simp only [lengthGrowth, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl <;>
      simp only [Linear.Fact.Holds, Linear.Form.eval, StepVar.value, termValuation, hn, hn', Option.getD_some] <;> omega
  · simp only [lengthGrowth, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    obtain ⟨n, -, hn'⟩ := hd (hall (.le [(.before (Term.length a), 1), (.after (Term.length a), -1)] (-(count : Int)))
      (by simp [lengthGrowth]) _ (by simp [Linear.Fact.vars]))
    simp [hn']

/-- **The facts a write at the length carries** (`write-append`, an instance
of the composition): the unconditional linear facts of the write's entry
over the written array's length, each term the write keeps read after it,
with the length one longer (`lengthGrowth a 1`) and each length it grows at
least what it was (`growth`). -/
def writeCarried (a : Nat) (first : Nat → String → Bool) (k : Knowledge) : List IndexAtom :=
  (compose (keptOf (Changes.ofClosed ⟨.any, .grow, .grow⟩) first) (unconditionalLinear k.indices)
    ((lengthGrowth a 1).join (growth (grownOf (Changes.ofClosed ⟨.any, .grow, .grow⟩) first)
      (unconditionalLinear k.indices)))).map
    fun F => { fact := .linear F }

/-- The slot guards `(s, tag)` appearing on unconditional guarded linear facts of `k`. -/
def guardedLinearGuards (k : Knowledge) : List (Nat × GuardTag) :=
  (k.indices.filterMap fun atom => match atom.cond, atom.fact with
    | none, .guarded s [] tag (.linear _) => some (s, tag)
    | _, _ => none).eraseDups

/-- The linear facts holding in `k` when slot guard `(s, tag)` does not hold:
all unconditional linear facts plus all linear facts guarded by `(s, tag)`. -/
def linearUnderGuard (s : Nat) (tag : GuardTag) (k : Knowledge) : List (Linear.Fact Term) :=
  unconditionalLinear k.indices ++ k.indices.filterMap fun atom => match atom.cond, atom.fact with
    | none, .guarded s' [] tag' (.linear F) => if s' == s && tag' == tag then some F else none
    | _, _ => none

/-- The guarded facts a write at the length carries (`write-append`, under a
slot guard `(s, tag)`): for each guard `(s, tag)` under which the entry facts
entail `a.length <= i`, compose `lengthGrowth a 1` with `linearUnderGuard s tag k`
and re-guard each resulting linear fact by `(s, tag)`. -/
def guardedWriteCarried (a i : Nat) (first : Nat → String → Bool) (k : Knowledge) : List IndexAtom :=
  (guardedLinearGuards k).flatMap fun (s, tag) =>
    let fs := linearUnderGuard s tag k
    if entailsKnown (fs.map fun F => { fact := .linear F }) (.le [(Term.length a, 1), (Term.value i, -1)] 0) then
      (compose (keptOf (Changes.ofClosed ⟨.any, .grow, .grow⟩) first) fs
        ((lengthGrowth a 1).join (growth (grownOf (Changes.ofClosed ⟨.any, .grow, .grow⟩) first) fs))).map
        fun F => { fact := .guarded s [] tag (.linear F) }
    else []

/-- The facts a write at a checked index states of its spine, at the entry's
slots (`write-bound`, `write-append`): the index below the length; and, where
the write grows the spines (`ExpressionEffects.elemWriteStep`) and the facts
(unconditional or under a slot guard) entail the index at least the length,
the facts `writeCarried` and `guardedWriteCarried` compose. -/
def atLengthAtoms [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) (k : Knowledge) (a i : Nat) :
    List IndexAtom :=
  { fact := .bound a i true } ::
    ((if termDefined k.indices (Term.length a) then
        [{ fact := .linear (.le [(Term.value i, 1), (Term.length a, -1)] (-1)) }] else []) ++
    (if (ExpressionEffects.elemWriteStep G j.context j.term).isSome then
      (let carried := writeCarried a (HeapExpressionRules.stableFirst G j.context) k
       if !carried.isEmpty && entailsKnown k.indices (.le [(Term.length a, 1), (Term.value i, -1)] 0) then
         carried else []) ++
      guardedWriteCarried a i (HeapExpressionRules.stableFirst G j.context) k
    else []))

theorem atLengthAtoms_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' _ => IndexHolds ε (atLengthAtoms G j k a i) ρ h') n W h (instantiate 0 ρ j.term) := by
  have hst := boundedWrite_spine hc he hk hw hh href
  -- `write-bound`, and its linear fact where the entry's length is defined.
  have hbound : ∀ h', (∃ s ls ls' b idx, Footprints.spineOf (ρ a) = some s ∧ h[s]? = some (.arr ls) ∧
      h'[s]? = some (.arr ls') ∧ ρ i = .num b ∧ indexOfBits b = some idx ∧ idx < ls'.length ∧
      ls'.length ≤ max ls.length (idx + 1) ∧ (ls.length ≤ idx → ls'.length = ls.length + 1)) →
      IndexHolds ε ({ fact := .bound a i true } :: if termDefined k.indices (Term.length a) then
        [{ fact := .linear (.le [(Term.value i, 1), (Term.length a, -1)] (-1)) }] else []) ρ h' := by
    intro h' ⟨s, ls, ls', b, idx, hs, hl, hl', hb, hidx, hlt, hmx, _⟩ atom hm _
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨s, ls', b, idx, hs, hl', hb, hidx, by simp; omega⟩
    · split at hm
      · rename_i hdef
        simp only [List.mem_singleton] at hm
        subst hm
        obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp (termDefined_sound hk.2.2.2.2.2 hdef)
        simp only [termValue_length] at hn0
        obtain ⟨s0, ls0, hs0, hls0, -, hmax0⟩ := lengthOf_spine hn0
        rw [hs] at hs0; cases hs0
        rw [hl] at hls0; cases hls0
        have hmax : ls'.length ≤ maxArrayLength := by
          have := indexOfBits_lt hidx; omega
        have hlv := lengthOf_of_spine hs hl' hmax
        have hiv : intValue (ρ i) = some (idx : Int) := by
          rw [hb]; exact HeapKnowledge.intValue_num (index_safeInt hidx)
        refine ⟨fun t ht => ?_, ?_⟩
        · simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
            or_false] at ht
          rcases ht with rfl | rfl
          · simp [hiv]
          · simp [hlv]
        · simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, termValue_value, termValue_length,
            hiv, hlv, Option.getD_some]
          omega
      · cases hm
  -- `write-append`: the composition with the length one longer (unconditional and guarded).
  have happ : SafePost (excOf G) (meaning G j.type)
      (fun h' _ => IndexHolds ε (if (ExpressionEffects.elemWriteStep G j.context j.term).isSome then
        (let carried := writeCarried a (HeapExpressionRules.stableFirst G j.context) k
         if !carried.isEmpty && entailsKnown k.indices (.le [(Term.length a, 1), (Term.value i, -1)] 0) then
           carried else []) ++
        guardedWriteCarried a i (HeapExpressionRules.stableFirst G j.context) k else []) ρ h')
      n W h (instantiate 0 ρ j.term) := by
    by_cases hws : (ExpressionEffects.elemWriteStep G j.context j.term).isSome = true
    · rw [ite_eq_left hws]
      obtain ⟨wi, hwi⟩ := Option.isSome_iff_exists.mp hws
      have hgrow := HeapExpressionRules.stableFirst_frame he hw hh
        (ExpressionEffects.elemWriteStep_grow hwi he hh (HeapObservations.erase hst))
      refine weaken (fun h' _ hq => ?_) (safePost_and hst hgrow)
      obtain ⟨⟨s, ls, ls', b, idx, hs, hl, hl', hb, hidx, hlt, -, hgr⟩, hch, hfirst⟩ := hq
      have hiv : termValuation ε ρ h (Term.value i) = idx := by
        simp [termValuation, hb, HeapKnowledge.intValue_num (index_safeInt hidx)]
      have hR_of : (Linear.Fact.Holds (termValuation ε ρ h) (.le [(Term.length a, 1), (Term.value i, -1)] 0)) →
          (lengthGrowth a 1).Holds ε ρ h ρ h' := fun hge => lengthGrowth_holds fun m hm' => by
        simp only [termValue_length] at hm' ⊢
        obtain ⟨s0, ls0, hs0, hls0, rfl, -⟩ := lengthOf_spine hm'
        rw [hs] at hs0; cases hs0
        rw [hl] at hls0; cases hls0
        have hlv : termValuation ε ρ h (Term.length a) = ls.length := by
          simp [termValuation, hm']
        simp only [Linear.Fact.Holds, Linear.Form.eval, hlv, hiv] at hge
        have hlen := hgr (by omega)
        have hmax : ls'.length ≤ maxArrayLength := by
          have := indexOfBits_lt hidx; omega
        rw [lengthOf_of_spine hs hl' hmax, hlen]
        simp
      intro atom hm _
      rcases List.mem_append.mp hm with hm | hm
      · dsimp only at hm
        split at hm
        · rename_i hcond
          obtain ⟨-, hent⟩ := Bool.and_eq_true_iff.mp hcond
          have hR := hR_of (entailsKnown_sound hk.2.2.2.2.2 hent)
          obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hm
          exact compose_holds (unconditionalLinear_holds hk.2.2.2.2.2) (keptOf_sound hch hfirst)
            (StepRelation.join_holds hR (growth_holds (grownOf_sound hch hfirst))) F hF
        · cases hm
      · unfold guardedWriteCarried at hm
        obtain ⟨⟨gs, tag⟩, -, hm⟩ := List.mem_flatMap.mp hm
        dsimp only at hm
        split at hm
        · rename_i hent
          obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hm
          refine ⟨ρ gs, rfl, ?_⟩
          by_cases htg : tag.holds (ρ gs)
          · exact .inl htg
          · have hfs : ∀ G' ∈ linearUnderGuard gs tag k,
                (∀ t ∈ G'.vars, (termValue ε ρ h t).isSome = true) ∧ Linear.Fact.Holds (termValuation ε ρ h) G' := by
              intro G' hG'
              rcases List.mem_append.mp hG' with hG' | hG'
              · exact unconditionalLinear_holds hk.2.2.2.2.2 G' hG'
              · obtain ⟨a', ha', hmap⟩ := List.mem_filterMap.mp hG'
                cases hcd' : a'.cond with
                | some _ => simp [hcd'] at hmap
                | none =>
                  cases hft' : a'.fact with
                  | guarded s' p' tag' B' =>
                    cases p' with
                    | cons _ _ => simp [hcd', hft'] at hmap
                    | nil =>
                      cases B' with
                      | linear F' =>
                        simp only [hcd', hft', Bool.and_eq_true, beq_iff_eq] at hmap
                        split at hmap
                        · rename_i heq
                          cases hmap
                          obtain ⟨rfl, rfl⟩ := heq
                          have haH := hk.2.2.2.2.2 a' ha' (by simp [hcd'])
                          rw [hft'] at haH
                          obtain ⟨v', hv', hor'⟩ := haH
                          simp only [readGuard, Option.some.injEq] at hv'
                          subst hv'
                          exact hor'.resolve_left htg
                        · cases hmap
                      | _ => simp [hcd', hft'] at hmap
                  | _ => simp [hcd', hft'] at hmap
            have hfsAtoms : IndexHolds ε ((linearUnderGuard gs tag k).map fun F' => { fact := .linear F' }) ρ h := by
              intro a' ha' _
              obtain ⟨G', hG', rfl⟩ := List.mem_map.mp ha'
              exact hfs G' hG'
            have hR := hR_of (entailsKnown_sound hfsAtoms hent)
            exact .inr (compose_holds hfs (keptOf_sound hch hfirst)
              (StepRelation.join_holds hR (growth_holds (grownOf_sound hch hfirst))) F hF)
        · cases hm
    · rw [ite_eq_right hws]
      exact weaken (fun _ _ _ => indexHolds_nil _ _) hst
  refine weaken (fun h' _ hq => ?_) (safePost_and hst happ)
  have hb0 := hbound h' hq.1
  intro atom hm hcd
  unfold atLengthAtoms at hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hb0 _ (List.mem_cons_self ..) hcd
  rcases List.mem_append.mp hm with hm | hm
  · exact hb0 _ (List.mem_cons_of_mem _ hm) hcd
  · exact hq.2 _ hm hcd

/-- The output of a write, with the facts it keeps one push deeper. -/
def withWritten (out : Knowledge) (kept : List IndexAtom) : Knowledge :=
  { out with indices := out.indices ++ shiftIndices kept }

theorem withWritten_sound {Ξ T : Fam} {out : Knowledge} {kept : List IndexAtom} {ρ n W h t}
    (hk : SafePost Ξ T (fun h' _ => IndexHolds ε kept ρ h') n W h t)
    (ho : SafePost Ξ T (fun h' u => Holds out ε (push u ρ) h') n W h t) :
    SafePost Ξ T (fun h' u => Holds (withWritten out kept) ε (push u ρ) h') n W h t :=
  weaken (fun _ u hq => ⟨hq.1.1, hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1, hq.1.2.2.2.2.1,
    indexHolds_cat hq.1.2.2.2.2.2 (shiftIndices_holds (v := u) hq.2)⟩) (safePost_and ho hk)

/-- **An element write's change** (`weak-update`'s effect): at any index, it
sets the spine location to an array spine and at most one element location
to the written value, and leaves every other old location as it was; a
fresh element's location is past the heap. The spine location held a spine
and holds one. -/
theorem elementWrite_into {Ξ T : Fam} {h : Heap} {flds : List (PropKey × Nat)} {cd : CallCode}
    {oid target : Nat} {iv value : Tm} {R : ValueSets.ValueSet} {n W}
    (hfield : flds.lookup arraySpineKey = some target) (hiv : isVal iv = true) (hR : R.mem value = true)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (.writeAt arraySpineKey (.objAt flds cd oid)
      (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) iv value))) :
    SafePost Ξ T (fun h' _ => HeapExpressionRules.IntoContents (fun _ => True) (some R) h h')
      n W h (.writeAt arraySpineKey (.objAt flds cd oid)
        (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) iv value)) := by
  have hv : isVal value = true := ValueSets.ValueSet.mem_isVal hR
  cases n with
  | zero => exact hs
  | succ n1 =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hbad, _⟩ | hr) | ⟨U1, h1, t1, hx1, hu1, step1, hh1, hs1⟩
    · simp [isVal] at hbad
    · exact .inl (.inr hr)
    obtain ⟨u, hu, rfl, rfl⟩ := ExpressionEffects.elem_read_inv hfield step1
    have huv : isVal u = true := HeapExpressionRules.heap_values hw hh target u hu
    have htlt : target < h.length := (List.getElem?_eq_some_iff.mp hu).1
    refine .inr ⟨U1, h, _, hx1, hu1, step1, hh1, ?_⟩
    cases n1 with
    | zero => exact hs1
    | succ n2 =>
      obtain ⟨hrf1, hs1⟩ := hs1
      refine ⟨hrf1, ?_⟩
      rcases hs1 with (⟨hbad, _⟩ | hr) | ⟨U2, h2, t2, hx2, hu2, step2, hh2, hs2⟩
      · simp [isVal] at hbad
      · exact .inl (.inr hr)
      obtain ⟨b', xs, -, rfl, hcase⟩ := ExpressionEffects.elem_set_inv rfl huv hiv hv step2
      rcases hcase with ⟨cell, -, rfl, rfl⟩ | ⟨i, -, -, rfl, rfl⟩
      · refine .inr ⟨U2, _, _, hx2, hu2, step2, hh2,
          (ExpressionEffects.write_back_post hfield ?_ hs2).post⟩
        intro l w hl
        by_cases hlt : l = target
        · subst hlt
          rw [hu] at hl; cases hl
          exact .inr (.inl ⟨xs, xs, rfl, by rw [List.getElem?_set_self (by simpa using htlt)]⟩)
        · rw [List.getElem?_set_ne (Ne.symm hlt)]
          by_cases hlc : l = cell
          · subst hlc
            have hl' : l < h.length := (List.getElem?_eq_some_iff.mp hl).1
            exact .inr (.inr ⟨trivial, value, by rw [List.getElem?_set_self hl'], fun R' hR' => by cases hR'; exact hR⟩)
          · rw [List.getElem?_set_ne (Ne.symm hlc)]; exact .inl hl
      · refine .inr ⟨U2, _, _, hx2, hu2, step2, hh2,
          (ExpressionEffects.write_back_post hfield ?_ hs2).post⟩
        intro l w hl
        have hl' : l < h.length := (List.getElem?_eq_some_iff.mp hl).1
        by_cases hlt : l = target
        · subst hlt
          rw [hu] at hl; cases hl
          exact .inr (.inl ⟨xs, _, rfl, by rw [List.getElem?_set_self (by simp; omega)]⟩)
        · rw [List.getElem?_set_ne (Ne.symm hlt), List.getElem?_append_left hl']; exact .inl hl

/-- The cell facts an element write of a value of `R` keeps
(`weak-update`): those whose contents hold every value of `R`
(`HeapExpressionRules.keptCells`, nothing known apart). -/
def writtenCells (k : Knowledge) (R : Option ValueSets.ValueSet) : HeapFacts.Facts :=
  HeapExpressionRules.keptCells (fun _ => false) R k.cells

/-- `out` with the cell facts `cs` added. -/
def withCells (out : Knowledge) (cs : HeapFacts.Facts) : Knowledge :=
  { out with cells := out.cells ++ cs }

theorem withCells_sound {Ξ T : Fam} {out : Knowledge} {cs : HeapFacts.Facts} {ρ n W h t}
    (hc : SafePost Ξ T (fun h' u => HeapFacts.Holds cs (push u ρ) h') n W h t)
    (ho : SafePost Ξ T (fun h' u => Holds out ε (push u ρ) h') n W h t) :
    SafePost Ξ T (fun h' u => Holds (withCells out cs) ε (push u ρ) h') n W h t :=
  weaken (fun _ _ hq => ⟨fun f hf => (List.mem_append.mp hf).elim (hq.1.1 f) (hq.2 f), hq.1.2⟩)
    (safePost_and ho hc)

/-- **An element write keeps `writtenCells`** at any index: of an object
holding a spine, of a value of `R`. -/
theorem writtenCells_sound {Ξ T : Fam} {k : Knowledge} {R : Option ValueSets.ValueSet} {ρ : Env}
    {h : Heap} {flds : List (PropKey × Nat)} {cd : CallCode} {oid target : Nat} {iv value : Tm} {n W}
    (hk : Holds k ε ρ h) (hfield : flds.lookup arraySpineKey = some target) (hiv : isVal iv = true)
    (hR : ∀ R', R = some R' → R'.mem value = true)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : Safe Ξ T n W h (.writeAt arraySpineKey (.objAt flds cd oid)
      (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) iv value))) :
    SafePost Ξ T (fun h' u => HeapFacts.Holds (writtenCells k R) (push u ρ) h') n W h
      (.writeAt arraySpineKey (.objAt flds cd oid)
        (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) iv value)) := by
  cases hRc : R with
  | none =>
    exact weaken (fun _ _ _ => by simp [writtenCells, HeapExpressionRules.keptCells,
      HeapExpressionRules.cellKept, HeapFacts.Holds]) (HeapObservations.of_safe hs)
  | some R' =>
    exact weaken (fun h' u hq => HeapExpressionRules.keptCells_holds hk.1 hq (fun _ _ ha => by cases ha))
      (elementWrite_into hfield hiv (hR R' hRc) hw hh hs)

/-- **A write at a checked index keeps `writtenCells`** (`weak-update`). -/
theorem boundedCells_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' u => HeapFacts.Holds (writtenCells k (HeapExpressionRules.valuesAt G j.context k v)) (push u ρ) h')
      n W h (instantiate 0 ρ j.term) := by
  have hs := boundedWrite_sound hc he hk hw hh href
  have hcheck := hc
  simp only [boundedWriteCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨hslots, -⟩, htypes⟩, hbd⟩, -⟩ := hcheck
  have hvl : v < j.context.length := by
    split at htypes
    · rename_i R' V hR' hV; exact (List.getElem?_eq_some_iff.mp hV).1
    · cases htypes
  obtain ⟨s, ls, b, idx, hst, hl, hb, -, -⟩ := bounded_sound hbd hk
  obtain ⟨flds, cd, oid, hoi⟩ : ∃ flds cd oid, ρ a = .objAt flds cd oid := by
    cases hra : ρ a
    case objAt => exact ⟨_, _, _, rfl⟩
    all_goals rw [hra] at hst; simp [Footprints.spineOf, Footprints.fieldsOf] at hst
  have hfl : flds.lookup arraySpineKey = some s := by
    simpa [Footprints.spineOf, Footprints.fieldsOf, hoi] using hst
  have hval : isVal (ρ v) = true := (meaning_value (he.2 v _ (List.getElem?_eq_getElem hvl))).1
  rw [boundedSlots_eq hslots] at hs ⊢
  simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, hb, hoi] at hs ⊢
  exact writtenCells_sound hk hfl rfl (fun R' hR' => HeapExpressionRules.valuesAt_sound hR' he hk) hw hh
    (HeapObservations.erase hs)

/-- The slot an element write's value is read from. -/
def writeValue (t : Tm) : Option Nat :=
  match ExpressionEffects.elemVarWriteSlots t with
  | some (_, _, _, k) => some k
  | none => (ExpressionEffects.elemWriteSlots t).map fun (_, _, _, k) => k

/-- **An element write whose typing gives its change writes a spine field**:
its array slot holds an object with a spine, its index is a value, and it
writes the value of `writeValue`'s slot. -/
theorem writeStep_spine [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {t : Tm}
    {w : Nat × Footprints.Change} {ρ n W}
    (hc : ExpressionEffects.elemWriteStep G Γ t = some w) (he : EnvOk G Γ ρ n W) :
    ∃ flds cd oid fl iv v, ρ w.1 = .objAt flds cd oid ∧ flds.lookup arraySpineKey = some fl ∧ isVal iv = true ∧
      writeValue t = some v ∧ v < Γ.length ∧
      instantiate 0 ρ t = .writeAt arraySpineKey (.objAt flds cd oid)
        (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) iv (ρ v)) := by
  obtain ⟨i, s⟩ := w
  rcases ExpressionEffects.elemWriteStep_cases hc with ⟨j, k, Ref, rfl, hk, hj, hi, hsel, -⟩ |
    ⟨b, k, Ref, idx, present, rfl, hk, hi, -, hst, -⟩
  · obtain ⟨B, _, L, hmem, -, hbag⟩ := ExpressionEffects.spineFieldEvery_sound hsel (he.2 _ Ref hi)
    obtain ⟨flds, code, oid, hl0, _, hrec⟩ := hbag
    obtain ⟨flds1, fl, cfl, oid', hproj, hfd, -, -⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨L, hmem, rfl⟩) hrec
    cases hproj
    refine ⟨flds, code, oid, fl, ρ j, k, hl0, hfd,
      (meaning_value (he.2 j Γ[j] (List.getElem?_eq_getElem hj))).1,
      by simp [writeValue, ExpressionEffects.elemVarWriteSlots], hk, ?_⟩
    simp [instantiate, hl0]
  · obtain ⟨B, _, L, hmem, -, hbag⟩ := ExpressionEffects.spineField_sound hst (he.2 _ Ref hi)
    obtain ⟨flds, code, oid, hl0, _, hrec⟩ := hbag
    obtain ⟨flds1, fl, cfl, oid', hproj, hfd, -, -⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨L, hmem, rfl⟩) hrec
    cases hproj
    refine ⟨flds, code, oid, fl, .num b, k, hl0, hfd, rfl,
      by simp [writeValue, ExpressionEffects.elemVarWriteSlots, ExpressionEffects.elemWriteSlots], hk, ?_⟩
    simp [instantiate, hl0]

/-- The knowledge after a step that is an element write at any index: `out`,
and every atom the change `{value: any, spine: grow}` keeps, a linear fact
whose length terms have non-positive coefficients and whose other terms read
no location holding an object or a number, or locations a stable field holds
(`ExpressionEffects.elemWriteStep_grow`, `stable-first`); and the cell facts the
write's change respects (`writtenCells`, `weak-update`). -/
def growOutput [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) (k out : Knowledge) : Knowledge :=
  if (ExpressionEffects.elemWriteStep G j.context j.term).isSome then
    withCells (withWritten out (keptIndices (Changes.ofClosed ⟨.any, .grow, .grow⟩) (HeapExpressionRules.stableFirst G j.context)
      k.indices))
      (match writeValue j.term with
        | some v => writtenCells k (HeapExpressionRules.valuesAt G j.context k v)
        | none => [])
  else out

theorem growOutput_sound [DecidableEq ι] {G : NormalGraph ι} {j : Sequent ι} {k out : Knowledge} {T : Fam}
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : SafePost (excOf G) T (fun h' u => Holds out ε (push u ρ) h') n W h (instantiate 0 ρ j.term)) :
    SafePost (excOf G) T (fun h' u => Holds (growOutput G j k out) ε (push u ρ) h') n W h
      (instantiate 0 ρ j.term) := by
  unfold growOutput
  split
  · rename_i hw'
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hw'
    refine withCells_sound ?_ (withWritten_sound ?_ hs)
    · obtain ⟨flds, cd, oid, fl, iv, v, -, hfd, hiv, hv, hvl, ht⟩ := writeStep_spine hi he
      rw [hv]
      simp only
      have hsafe := HeapObservations.erase hs
      rw [ht] at hsafe ⊢
      exact writtenCells_sound hk hfd hiv (fun R' hR' => HeapExpressionRules.valuesAt_sound hR' he hk) hw hh hsafe
    · exact weaken (fun _ _ hq => keptIndices_holds hk.2.2.2.2.2 hq.1 hq.2)
        (HeapExpressionRules.stableFirst_frame he hw hh
          (ExpressionEffects.elemWriteStep_grow hi he hh (HeapObservations.erase hs)))
  · exact hs

/-- The footprint of an element write at array slot `a`: `a`'s spine grows and
`a`'s element cells may change; every other location is untouched. -/
def writeFootprint (a : Nat) : Footprints.Footprint :=
  [(.field a arraySpineKey, .grow), (.cells a, .any)]

/-- The heap-reading index atoms of `k` kept by an element write at slot `a`
under the tolerant frame (`Footprints.IndexFact.keeps`). -/
def writeFrameAtoms (stable : Nat → String → Bool) (k : Knowledge) (a : Nat) : List IndexAtom :=
  k.indices.filter fun atom => !atom.fact.envOnly &&
    atom.fact.keepsUnder k (.ofFirst stable) (writeFootprint a) []

/-- The read links of `k` kept by an element write at slot `a` under the
tolerant frame (`Footprints.FactKind.link`), shifted past the step's result. -/
def writeFrameLinks (stable : Nat → String → Bool) (k : Knowledge) (a : Nat) : HeapLinks.Links :=
  (k.links.filter fun g => !g.alias && Footprints.respects (Footprints.knowledgeQuery k)
    ((Footprints.FactKind.link g).supportIn (.ofFirst stable)) (writeFootprint a)).map
    fun g => { g with cell := g.cell + 1, value := g.value + 1 }

/-- `out` with the read links `ls` added. -/
def withLinks (out : Knowledge) (ls : HeapLinks.Links) : Knowledge :=
  { out with links := out.links ++ ls.filter (!out.links.contains ·) }

theorem withLinks_sound {Ξ T : Fam} {out : Knowledge} {ls : HeapLinks.Links} {ρ n W h t}
    (hl : SafePost Ξ T (fun h' u => HeapLinks.Holds ls (push u ρ) h') n W h t)
    (ho : SafePost Ξ T (fun h' u => Holds out ε (push u ρ) h') n W h t) :
    SafePost Ξ T (fun h' u => Holds (withLinks out ls) ε (push u ρ) h') n W h t :=
  weaken (fun _ _ hq => ⟨hq.1.1, hq.1.2.1, fun g hg =>
    (List.mem_append.mp hg).elim (hq.1.2.2.1 g) (fun hg => hq.2 g (List.mem_filter.mp hg).1),
    hq.1.2.2.2⟩) (safePost_and ho hl)

/-- An element write on slot `a` satisfies `Footprints.Post (writeFootprint a)`. -/
theorem elementWrite_footprint_post {Ξ T : Fam} {a : Nat} {ρ : Env} {n W h}
    {flds : List (PropKey × Nat)} {cd : CallCode} {oid target : Nat}
    {xs : List (Option Nat)} {b : UInt64} {value : Val}
    (hobj : ρ a = .objAt flds cd oid) (hfield : flds.lookup arraySpineKey = some target)
    (hxs : h[target]? = some (.arr xs)) (hv : isVal value = true)
    (hs : Safe Ξ T n W h (.writeAt arraySpineKey (.objAt flds cd oid)
      (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) (.num b) value))) :
    SafePost Ξ T (fun h' _ => Footprints.Post (writeFootprint a) ρ h h') n W h
      (.writeAt arraySpineKey (.objAt flds cd oid)
        (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) (.num b) value)) := by
  have htl : target < h.length := (List.getElem?_eq_some_iff.mp hxs).1
  apply elementWrite_post hfield hxs hv _ _ hs
  · intro cell hc
    have hcm : some cell ∈ xs := by
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
    refine ⟨by simp, fun l v hv' => ?_⟩
    have hlt : l < h.length := (List.getElem?_eq_some_iff.mp hv').1
    by_cases hlt' : l = target
    · subst hlt'
      rw [hxs] at hv'; cases hv'
      exact ⟨.arr xs, by rw [List.getElem?_set_self (by simpa using htl)], .inl rfl⟩
    · by_cases hlc : l = cell
      · subst hlc
        refine ⟨value, ?_, .inr ⟨(.cells a, .any), by simp [writeFootprint], ?_, trivial⟩⟩
        · rw [List.getElem?_set_ne (Ne.symm hlt'), List.getElem?_set_self hlt]
        · simp [Footprints.Region.mem, Footprints.spineCells, Footprints.fieldsOf, Footprints.entriesAt,
            spineEntries, hobj, hfield, hxs, hcm]
      · refine ⟨v, ?_, .inl rfl⟩
        rw [List.getElem?_set_ne (Ne.symm hlt'), List.getElem?_set_ne (Ne.symm hlc)]
        exact hv'
  · intro i hi _
    have hilt := indexOfBits_lt hi
    refine ⟨by simp, fun l v hv' => ?_⟩
    have hlt : l < h.length := (List.getElem?_eq_some_iff.mp hv').1
    by_cases hlt' : l = target
    · subst hlt'
      rw [hxs] at hv'; cases hv'
      refine ⟨.arr (placeAt xs i h.length), by rw [List.getElem?_set_self (by simp; omega)],
        .inr ⟨(.field a arraySpineKey, .grow), by simp [writeFootprint], ?_, ?_⟩⟩
      · simp [Footprints.Region.mem, Footprints.fieldsOf, hobj, hfield]
      · exact .inr (.inl ⟨xs, _, rfl, rfl, fun m hd => ExpressionEffects.placeAt_dense hd,
          fun x hx => (ExpressionEffects.placeAt_mem hx).imp id (fun e => by omega),
          ⟨by rw [placeAt_length]; omega, fun hmax => by rw [placeAt_length]; omega⟩⟩)
    · refine ⟨v, ?_, .inl rfl⟩
      rw [List.getElem?_set_ne (Ne.symm hlt'), List.getElem?_append_left hlt]
      exact hv'

/-- A checked write at array slot `a` keeps both `writeFrameAtoms` and
`writeFrameLinks` via the tolerant frame (`Footprints.Post (writeFootprint a)`). -/
theorem boundedWriteFrame_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) (hρ : RootsOk W ρ) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' u => IndexHolds ε (writeFrameAtoms (HeapExpressionRules.stableFirst G j.context) k a) ρ h' ∧
        HeapLinks.Holds (writeFrameLinks (HeapExpressionRules.stableFirst G j.context) k a) (push u ρ) h')
      n W h (instantiate 0 ρ j.term) := by
  have hs := boundedWrite_sound hc he hk hw hh href
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
    all_goals rw [hra] at hs0; simp [Footprints.spineOf, Footprints.fieldsOf] at hs0
  have hfl : flds.lookup arraySpineKey = some s := by
    simpa [Footprints.spineOf, Footprints.fieldsOf, hoi] using hs0
  have hval : isVal (ρ v) = true := (meaning_value (he.2 v _ (List.getElem?_eq_getElem hvl))).1
  rw [boundedSlots_eq hslots] at hs ⊢
  have hsafe := HeapObservations.erase hs
  simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, hoi, hb] at hsafe ⊢
  have hpost := HeapExpressionRules.stableFirst_frame he hw hh
    (elementWrite_footprint_post hoi hfl hl hval hsafe)
  refine weaken (fun h' u hq => ?_) hpost
  obtain ⟨hp, hst⟩ := hq
  have hqsound := Footprints.knowledgeQuery_sound hk hh hρ
  have hctx := Footprints.ReadContext.ofFirst_holds hst
  refine ⟨fun atom hm hcd => ?_, fun g hg => ?_⟩
  · obtain ⟨ha, hkeep⟩ := List.mem_filter.mp hm
    simp only [Bool.and_eq_true] at hkeep
    exact Footprints.IndexFact.keepsUnder_sound hk hh hρ hp hctx atom.fact [] (by simp) hkeep.2 (hk.2.2.2.2.2 atom ha hcd)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hgm, hr⟩ := List.mem_filter.mp hg0
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hr
    have hF : (Footprints.FactKind.link g0).Holds ρ h := fun g' hg' => by
      rw [List.mem_singleton.mp hg']; exact hk.2.2.1 g0 hgm
    have hres := Footprints.frame_step (D := Footprints.heaps) (m := 0)
      (Footprints.FactKind.supportsIn (.ofFirst (HeapExpressionRules.stableFirst G j.context)) (.link g0))
      hr.2 hqsound hp trivial hctx hF g0 (List.mem_singleton_self _)
    simpa [push] using hres

theorem boundedRegions_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) (hρ : RootsOk W ρ) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' _ => IndexHolds ε (writeAtoms G j.context k a) ρ h') n W h (instantiate 0 ρ j.term) := by
  have hs := boundedWrite_sound hc he hk hw hh href
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
    all_goals rw [hra] at hs0; simp [Footprints.spineOf, Footprints.fieldsOf] at hs0
  have hfl : flds.lookup arraySpineKey = some s := by
    simpa [Footprints.spineOf, Footprints.fieldsOf, hoi] using hs0
  have hval : isVal (ρ v) = true := (meaning_value (he.2 v _ (List.getElem?_eq_getElem hvl))).1
  rw [boundedSlots_eq hslots] at hs ⊢
  have hsafe := HeapObservations.erase hs
  simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, hoi, hb] at hsafe ⊢
  exact writeAtoms_holds he hk hh hρ hoi hfl hl hval hsafe

/-- The effect of a call extending the array spine of its receiver, the
slot `r`: the note's Push, `{r.spine: extend}` (`CallEffects.receiverExtendFrame`
at the caller's slot). -/
def receiverExtendAt (r : Nat) : Footprints.Footprint :=
  [(.field r arraySpineKey, .extend)]

/-- The region facts a call growing its receiver's spine keeps
(`region-grow`), between two array slots: each whose support
(`apartGrowSupport`, or its mirror) the call's effect (`receiverExtendAt`)
respects under the knowledge's query, the note's Frame. -/
def grownRegions (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Tm → List IndexAtom
  | .invoke _ (.var r) args => match slotVars args with
    | some is => if is.all (· < Γ.length) then
        k.indices.filter fun a => a.cond.isNone && match a.fact with
          | .apart x y => arraySlot G Γ x && arraySlot G Γ y &&
              (Footprints.respects (Footprints.knowledgeQuery k) (apartGrowSupport x y) (receiverExtendAt r) ||
                Footprints.respects (Footprints.knowledgeQuery k) (apartGrowSupport y x) (receiverExtendAt r))
          | _ => false
      else []
    | none => []
  | _ => []

/-- A growth of the receiver's spine at the callee's positions is one at the
caller's slot holding the receiver. -/
theorem receiverExtendAt_post {env ρ : Env} {r : Nat} {h h' : Heap}
    (hp : Footprints.Post CallEffects.receiverExtendFrame env h h') (hr : env 0 = ρ r) :
    Footprints.Post (receiverExtendAt r) ρ h h' := by
  refine ⟨hp.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with h | ⟨e, he, hm, hh⟩
  · exact .inl h
  · simp only [CallEffects.receiverExtendFrame, List.mem_singleton] at he
    subst he
    exact .inr ⟨_, List.mem_singleton_self _, by simpa [Footprints.Region.mem, hr] using hm, hh⟩

/-- **The region facts a growing call keeps hold after it**: the tolerant
frame at each one's support (`apartGrow_supports` or its mirror), which the
call's effect `receiverExtendAt r` respects under the knowledge's query
(`frame_step`); the support's condition, the other array's region in the
heap, from the array slot's type (`arraySlot_region`). -/
theorem grownRegions_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {t : Tm} {ρ n W h h'}
    (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h) (hk : Holds k ε ρ h) (hρ : RootsOk W ρ)
    (hg : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (ha : CallEffects.ReceiverAppends (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h') :
    IndexHolds ε (grownRegions G Γ k t) ρ h' := by
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
  have hv : ∀ a ∈ ExpressionEffects.actualsOf (instantiate 0 ρ (.invoke f (.var r) (is.map Tm.var))),
      isVal a = true := by
    intro a hm
    simp only [ExpressionEffects.actualsOf, instantiate, instantiateArgs_eq_map, List.map_map,
      List.mem_map, Function.comp_apply] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    simp only [Nat.not_lt_zero, ite_false, Nat.sub_zero]
    exact (meaning_value (he.2 i _ (List.getElem?_eq_getElem (hlt i hi)))).1
  have hlen : h.length ≤ h'.length := by
    cases hl : h.length with
    | zero => exact Nat.zero_le _
    | succ m =>
      have hm : m < h.length := by omega
      rcases hg m h[m] (List.getElem?_eq_getElem hm) with hk' | ⟨-, -, ls', -, hk', -⟩ <;>
        exact (List.getElem?_eq_some_iff.mp hk').1
  have hp : Footprints.Post (receiverExtendAt r) ρ h h' :=
    receiverExtendAt_post (CallEffects.receiverExtendFrame_post (args := []) hlen hg hv ha)
      (by simp [CallEffects.callEnv, ExpressionEffects.receiverOf, instantiate])
  have hq := Footprints.knowledgeQuery_sound hk hh hρ
  intro a hm hcond
  obtain ⟨hmem, hsel⟩ := List.mem_filter.mp hm
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hsel
  obtain ⟨hnone, hsel⟩ := hsel
  have hat := hk.2.2.2.2.2 a hmem fun b hb => by rw [hnone] at hb; cases hb
  cases hfact : a.fact
  case apart x y =>
    rw [hfact] at hsel hat
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hsel
    obtain ⟨⟨hx, hy⟩, hr⟩ := hsel
    show RegionsApart h' (ρ x) (ρ y)
    have below : ∀ z, arraySlot G Γ z = true → RegionBelow h (ρ z) := fun z hz => arraySlot_region hz he hh
    rcases hr with hr | hr
    · exact Footprints.frame_step (D := Footprints.heaps) (m := 0) (apartGrow_supports x y) hr hq hp trivial
        (below y hy) hat
    · exact Footprints.frame_step (D := Footprints.heaps) (m := 0) (apartGrow_supports_mirror x y) hr hq hp trivial
        (below x hx) hat
  all_goals (rw [hfact] at hsel; simp at hsel)

/-! ## Quantified invariants across dense-append writes

A bounded write `a[i] = v` with `i = a.length` allocates one fresh cell at
`h.length` holding `v` and replaces only `a`'s spine cell `target` with
`placeAt xs xs.length h.length`, leaving every existing location `l ≠ target`
unchanged (`DenseAppendHeap`). Any non-array-spine location (fields, cells,
element cells, view spines) is untouched by role disjointness; any array spine
separated from `target` by `knowledgeQuery` or by contract disjointness of its
element type (`spineTypesDisjoint`) is likewise untouched. On that transition:
- `element v a i` holds;
- facts reading only locations untouched by `target` survive;
- a quantified fact `every s [] stop body` over `a` (with `i ≤ stop`) keeps its
  prefix at `.value i`, and extends to `.length s` when `body` holds of `v` at `i`;
- a quantified fact `every s [] stop body` over an array `s` apart from `a`
  referencing `a` in parallel (with `i ≤ stop` and a non-`undefined` element
  binding `element r s i`) extends to `.length a` (and `.length s` where
  `s.length ≤ i + 1`) when `body` holds of `(r, v)` at `i`. -/

/-- The complete element-write execution takes three steps before reaching a
value, so its postcondition is only evaluated when the step budget is at least
four (`n ≥ 4`). -/
theorem elementWrite_post4 {Ξ T : Fam} {P : Heap → Prop}
    {h : Heap} {flds : List (PropKey × Nat)} {cd : CallCode} {oid target : Nat}
    {xs : List (Option Nat)} {b : UInt64} {value : Val} {n W}
    (hfield : flds.lookup arraySpineKey = some target)
    (hxs : h[target]? = some (.arr xs)) (hv : isVal value = true)
    (hpresent : n ≥ 4 → ∀ cell, elemLoc xs b = some cell →
      P ((h.set cell value).set target (.arr xs)))
    (hfresh : n ≥ 4 → ∀ i, indexOfBits b = some i → elemLoc xs b = none →
      P ((h ++ [value]).set target (.arr (placeAt xs i h.length))))
    (hs : Safe Ξ T n W h (.writeAt arraySpineKey (.objAt flds cd oid)
      (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) (.num b) value))) :
    SafePost Ξ T (fun h' _ => P h') n W h
      (.writeAt arraySpineKey (.objAt flds cd oid)
        (.setElem (.readAt arraySpineKey (.objAt flds cd oid)) (.num b) value)) := by
  cases n with
  | zero => assumption
  | succ n1 =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hbad, _⟩ | hr) | ⟨U1, h1, t1, hx1, hu1, step1, hh1, hs1⟩
    · simp [isVal] at hbad
    · exact .inl (.inr hr)
    obtain ⟨u, hu, rfl, rfl⟩ := ExpressionEffects.elem_read_inv hfield step1
    rw [hxs] at hu; cases hu
    refine .inr ⟨U1, h, _, hx1, hu1, step1, hh1, ?_⟩
    cases n1 with
    | zero => assumption
    | succ n2 =>
      obtain ⟨hrf1, hs1⟩ := hs1
      refine ⟨hrf1, ?_⟩
      rcases hs1 with (⟨hbad, _⟩ | hr) | ⟨U2, h2, t2, hx2, hu2, step2, hh2, hs2⟩
      · simp [isVal] at hbad
      · exact .inl (.inr hr)
      obtain ⟨b', xs', hb, hls, hcase⟩ := ExpressionEffects.elem_set_inv rfl rfl rfl hv step2
      cases hb; cases hls
      rcases hcase with ⟨cell, hc, rfl, rfl⟩ | ⟨i, hi, hn, rfl, rfl⟩
      · refine .inr ⟨U2, _, _, hx2, hu2, step2, hh2, ?_⟩
        cases n2 with
        | zero => exact hs2
        | succ n3 =>
          obtain ⟨hrf2, hs2⟩ := hs2
          refine ⟨hrf2, ?_⟩
          rcases hs2 with (⟨hbad, _⟩ | hr) | ⟨U3, h3, t3, hx3, hu3, step3, hh3, hs3⟩
          · simp [isVal] at hbad
          · exact absurd hr (ExpressionEffects.write_values_not_thrown rfl rfl)
          obtain ⟨flds', c', oid', l3, ho, hl3, -, rfl, rfl⟩ := HeapExpressionRules.write_inv rfl rfl step3
          cases ho; rw [hfield] at hl3; cases hl3
          refine .inr ⟨U3, _, _, hx3, hu3, step3, hh3, ?_⟩
          cases n3 with
          | zero => exact hs3
          | succ n4 =>
            obtain ⟨hrf3, hs3⟩ := hs3
            refine ⟨hrf3, ?_⟩
            rcases hs3 with (⟨hv3, ht3⟩ | hr) | ⟨_, _, _, _, _, st', _, _⟩
            · exact .inl (.inl ⟨hv3, ht3, hpresent (by omega) cell hc⟩)
            · exact absurd hr (val_not_thrown rfl)
            · exact False.elim (value_no_step rfl st')
      · refine .inr ⟨U2, _, _, hx2, hu2, step2, hh2, ?_⟩
        cases n2 with
        | zero => exact hs2
        | succ n3 =>
          obtain ⟨hrf2, hs2⟩ := hs2
          refine ⟨hrf2, ?_⟩
          rcases hs2 with (⟨hbad, _⟩ | hr) | ⟨U3, h3, t3, hx3, hu3, step3, hh3, hs3⟩
          · simp [isVal] at hbad
          · exact absurd hr (ExpressionEffects.write_values_not_thrown rfl rfl)
          obtain ⟨flds', c', oid', l3, ho, hl3, -, rfl, rfl⟩ := HeapExpressionRules.write_inv rfl rfl step3
          cases ho; rw [hfield] at hl3; cases hl3
          refine .inr ⟨U3, _, _, hx3, hu3, step3, hh3, ?_⟩
          cases n3 with
          | zero => exact hs3
          | succ n4 =>
            obtain ⟨hrf3, hs3⟩ := hs3
            refine ⟨hrf3, ?_⟩
            rcases hs3 with (⟨hv3, ht3⟩ | hr) | ⟨_, _, _, _, _, st', _, _⟩
            · exact .inl (.inl ⟨hv3, ht3, hfresh (by omega) i hi hn⟩)
            · exact absurd hr (val_not_thrown rfl)
            · exact False.elim (value_no_step rfl st')

/-! ### Type-directed array-spine disjointness -/

/-- Whether a clause rejects every object value `.objAt`. -/
def clauseRejectsObj {α : Type} : Clause α → Bool
  | .nul | .undef | .bool | .boolLit _ | .num | .numLit _ | .numIn _ | .int
  | .str | .strLit _ | .strIn _ | .bigint | .bigintLit _ | .symbol | .symbolLit _
  | .list _ _ | .pack _ _ => true
  | _ => false

theorem clauseRejectsObj_sound {G : NormalGraph ι} {c : Clause (List ι)} {fs : List (PropKey × Nat)}
    {cd : CallCode} {oid k : Nat} {W : WorldT k}
    (h : clauseRejectsObj c = true) (hv : clauseSem G c k W (.objAt fs cd oid)) : False := by
  have hs := hv.1
  cases c with
  | nul | undef | bool | num | int | str | bigint | symbol =>
    simp [semWithArgs, nulT, undefT, boolT, numT, PositiveNormalization.intT, strT, bigintT, symbolT] at hs
  | boolLit b => cases b <;> simp [semWithArgs] at hs
  | numLit _ | strLit _ | bigintLit _ | symbolLit _ => simp [semWithArgs] at hs
  | numIn _ | strIn _ => simp [semWithArgs] at hs
  | list _ _ => obtain ⟨_, he, -⟩ := hs.1; cases he
  | pack _ _ => exact hs
  | refs _ _ _ _ _ _ _ | dict _ _ _ _ _ _ _ _ _ | arrs _ _ | callable _ _ _ _ _
  | ctors _ _ _ _ _ | view _ _ | top | source =>
    simp [clauseRejectsObj] at h

/-- Whether a tuple contract `tup` (from a writable or readonly array spine)
cannot share its spine contract with a homogeneous writable array of element
type `E_a`. -/
@[nospecialize] def tupleDisjointFrom (G : NormalGraph ι) (E_a : Ty ι) (writable : Bool) (tup : Tuple (Ty ι)) : Bool :=
  if tup.required.isEmpty && tup.optional.isEmpty && tup.rest.isNone then true
  else match tup.required[0]?.orElse (fun _ => tup.optional[0]?.orElse fun _ => tup.rest) with
    | some E_w =>
      HeapExpressionRules.elemWitnessExcluded G E_a E_w ||
        (writable && tup.required.isEmpty && tup.optional.isEmpty && !tup.readonly && HeapExpressionRules.elemWitnessExcluded G E_w E_a)
    | none => false

/-- Whether a single clause `c` of a value's type excludes its array spine from
aliasing the spine of a homogeneous writable array of element type `E_a`. -/
@[nospecialize] def spineClauseDisjoint (G : NormalGraph ι) (E_a : Ty ι) (c : Clause (List ι)) : Bool :=
  if clauseRejectsObj c then true
  else match c with
    | .refs fs [] vs _ _ _ _ =>
      match (Stored.views fs).lookup arraySpineKey with
      | some S => match expand G S with
        | [.list tup []] => tupleDisjointFrom G E_a true tup
        | _ => false
      | none => match vs.lookup arraySpineKey with
        | some S => match expand G S with
          | [.list tup []] => tupleDisjointFrom G E_a false tup
          | _ => false
        | none => false
    | _ => false

/-- Whether every array spine of any value of type `T_w` is contract-disjoint
from the spine of a homogeneous writable array of element type `E_a`. -/
@[nospecialize] def spineTypesDisjoint (G : NormalGraph ι) (E_a T_w : Ty ι) : Bool :=
  G.plainTy T_w && (expand G T_w).all (spineClauseDisjoint G E_a)

/-- The homogeneous element type of a writable or readonly array type. -/
@[nospecialize] def arrayElemType (G : NormalGraph ι) (R : Ty ι) : Option (Ty ι) :=
  match expand G R with
  | [.refs fs [] vs _ _ _ _] =>
    match ((Stored.views fs).lookup arraySpineKey).orElse fun _ => vs.lookup arraySpineKey with
    | some S => match expand G S with
      | [.list ⟨[], [], some E, _, _⟩ []] => some E
      | _ => none
    | none => none
  | _ => none

private theorem singleton_listT {E : Fam} {pr : ArrayPresence} :
    listT ⟨[], [], some E, false, pr⟩ 1 (ofEntries [(.elem, res E)]) (.arr [some 0]) := by
  refine ⟨[some 0], rfl, fun j _ => SpinePresence.of_dense (by simp) j, by simp, by decide, by simp,
    fun i A hA => by simp at hA, fun i A l hA => by simp at hA, fun i l _ hl => ?_⟩
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    exact ⟨E, res E, rfl, by simp [lookup, toList], fun _ _ _ _ => ⟨id, fun _ => id⟩⟩
  | succ i' => simp at hl

private theorem tupleDisjointFrom_contra {G : NormalGraph ι} {E_a : Ty ι} {pr_a : ArrayPresence}
    {writable : Bool} {tup : Tuple (Ty ι)}
    (hd : tupleDisjointFrom G E_a writable tup = true)
    (hfwd : ∀ (W1 : WorldT 1) u, listT ⟨[], [], some (meaning G E_a), false, pr_a⟩ 1 W1 u →
      listT (tupleFams (meaning G) tup) 1 W1 u)
    (hrev : writable = true → ∀ (W1 : WorldT 1) u, listT (tupleFams (meaning G) tup) 1 W1 u →
      listT ⟨[], [], some (meaning G E_a), false, pr_a⟩ 1 W1 u) : False := by
  unfold tupleDisjointFrom at hd
  split at hd
  · rename_i hemp
    simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hemp
    obtain ⟨⟨hreq, hopt⟩, hrest⟩ := hemp
    have hl := hfwd (ofEntries [(.elem, res (meaning G E_a))]) (.arr [some 0]) singleton_listT
    obtain ⟨ls, heq, -, -, -, hbound, -⟩ := hl
    cases heq
    have hb := hbound (by simp [tupleFams, hrest])
    simp [tupleFams, hreq, hopt] at hb
  · split at hd
    case h_2 => cases hd
    rename_i E_w hEw
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true'] at hd
    rcases hd with hpw | ⟨⟨⟨⟨hwr, hreq⟩, hopt⟩, hro⟩, hpw⟩
    · obtain ⟨v, hvA, hvW⟩ := HeapExpressionRules.elemWitnessExcluded_sound hpw (ofEntries [])
      have hl := hfwd (ofEntries [(.elem, res (meaning G E_a))]) (.arr [some 0]) singleton_listT
      obtain ⟨ls, heq, -, -, -, -, hreqL, hoptL, hrestL⟩ := hl
      cases heq
      have himp : meaning G E_a 0 (ofEntries []) v → meaning G E_w 0 (ofEntries []) v := by
        cases hr0 : tup.required[0]? with
        | some E0 =>
          rw [hr0] at hEw; simp only [Option.orElse_some, Option.some.injEq] at hEw; subst hEw
          obtain ⟨l, c, hls0, hlk, hag⟩ := hreqL 0 (meaning G E0) (by simp [tupleFams, hr0])
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hls0; subst hls0
          simp only [lookup, toList, entries_ofEntries, List.map_cons, List.getElem?_cons_zero,
            Option.some.injEq] at hlk
          subst hlk
          exact (hag 0 (by omega) (ofEntries []) v).1
        | none =>
          rw [hr0] at hEw; simp only [Option.orElse_none] at hEw
          have hreqNil : tup.required.length = 0 := by
            cases hr : tup.required with
            | nil => rfl
            | cons _ _ => simp [hr] at hr0
          cases ho0 : tup.optional[0]? with
          | some E0 =>
            rw [ho0] at hEw; simp only [Option.orElse_some, Option.some.injEq] at hEw; subst hEw
            obtain ⟨c, hlk, hag⟩ := hoptL 0 (meaning G E0) 0 (by simp [tupleFams, ho0])
              (by simp [tupleFams, hreqNil])
            simp only [lookup, toList, entries_ofEntries, List.map_cons, List.getElem?_cons_zero,
              Option.some.injEq] at hlk
            subst hlk
            exact (hag 0 (by omega) (ofEntries []) v).1
          | none =>
            rw [ho0] at hEw; simp only [Option.orElse_none] at hEw
            have hoptNil : tup.optional.length = 0 := by
              cases ho : tup.optional with
              | nil => rfl
              | cons _ _ => simp [ho] at ho0
            obtain ⟨E0, c, hE0, hlk, hag⟩ := hrestL 0 0 (by simp [tupleFams, hreqNil, hoptNil]) rfl
            simp only [tupleFams, hEw, Option.map_some, Option.some.injEq] at hE0; subst hE0
            simp only [lookup, toList, entries_ofEntries, List.map_cons, List.getElem?_cons_zero,
              Option.some.injEq] at hlk
            subst hlk
            exact (hag 0 (by omega) (ofEntries []) v).1
      exact hvW (himp hvA)
    · obtain ⟨v, hvW, hvA⟩ := HeapExpressionRules.elemWitnessExcluded_sound hpw (ofEntries [])
      simp only [hreq, hopt, List.getElem?_nil, Option.orElse_none] at hEw
      have htup : tupleFams (meaning G) tup = ⟨[], [], some (meaning G E_w), false, tup.presence⟩ := by
        simp [tupleFams, hreq, hopt, hEw, hro]
      have hl := hrev hwr (ofEntries [(.elem, res (meaning G E_w))]) (.arr [some 0])
        (htup ▸ singleton_listT)
      obtain ⟨ls, heq, -, -, -, -, -, -, hrestL⟩ := hl
      cases heq
      obtain ⟨E0, c, hE0, hlk, hag⟩ := hrestL 0 0 (by simp) rfl
      cases hE0
      simp only [lookup, toList, entries_ofEntries, List.map_cons, List.getElem?_cons_zero,
        Option.some.injEq] at hlk
      subst hlk
      exact hvA ((hag 0 (by omega) (ofEntries []) v).1 hvW)

/-- **Type-directed array-spine disjointness**: a value `w` whose type `T_w`
satisfies `spineTypesDisjoint G E_a T_w` cannot have its array spine at the
location `target` of a homogeneous writable array whose element type is `E_a`. -/
theorem spineTypesDisjoint_sound {G : NormalGraph ι} {E_a T_w : Ty ι} {pr_a : ArrayPresence}
    {target l_w n k : Nat} {W : WorldT n} {c_a : Ctr n} {w : Val}
    (hca : lookup W target = some c_a)
    (haga : ∀ (j : Nat) (hj : j < n) (W' : WorldT j) (u : Val),
      c_a j hj W' u ↔ listT ⟨[], [], some (meaning G E_a), false, pr_a⟩ j W' u)
    (hdisj : spineTypesDisjoint G E_a T_w = true)
    (hk2 : 2 ≤ k) (hkn : k ≤ n)
    (hw : meaning G T_w k (trunc k hkn W) w)
    (hsw : Footprints.spineOf w = some l_w) : l_w ≠ target := by
  intro heq; subst heq
  obtain ⟨flds, cd, oid, rfl⟩ : ∃ flds cd oid, w = .objAt flds cd oid := by
    cases hwv : w
    case objAt => exact ⟨_, _, _, rfl⟩
    all_goals rw [hwv] at hsw; simp [Footprints.spineOf, Footprints.fieldsOf] at hsw
  have hfl : flds.lookup arraySpineKey = some l_w := by
    simpa [Footprints.spineOf, Footprints.fieldsOf] using hsw
  simp only [spineTypesDisjoint, Bool.and_eq_true, List.all_eq_true] at hdisj
  obtain ⟨hplain, hall⟩ := hdisj
  obtain ⟨c, hcm, hsem⟩ := (expand_sem G T_w hplain k (trunc k hkn W) _).mp hw
  have hsc := hall c hcm
  unfold spineClauseDisjoint at hsc
  split at hsc
  · rename_i hrej; exact clauseRejectsObj_sound hrej hsem
  · cases c with
    | refs fs rs vs os ms ks st =>
      cases rs with
      | cons _ _ => simp at hsc
      | nil =>
        have htr := lookup_trunc hkn W l_w c_a hca
        cases hfs : (Stored.views fs).lookup arraySpineKey with
        | some S =>
          simp only [hfs] at hsc
          split at hsc
          case h_2 => cases hsc
          rename_i tup hS
          obtain ⟨sr, hm⟩ := Stored.mem_views.mp (PositiveRules.mem_of_lookup hfs)
          obtain ⟨flds', l', c', oid', he, hfl', hlk', hag'⟩ :=
            recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨S, hm, rfl⟩) hsem.1.1.1
          cases he; rw [hfl] at hfl'; cases hfl'
          rw [htr] at hlk'; cases hlk'
          have hSrep : Represents G S (.list tup []) := hS
          refine tupleDisjointFrom_contra (pr_a := pr_a) hsc (fun W1 u hu => ?_) (fun _ W1 u hu => ?_)
          · have hc1 := (haga 1 (by omega) W1 u).mpr hu
            have hm1 := (hag' 1 (by omega) W1 u).mp hc1
            exact ((represents_raw hSrep 1 W1 u) hm1).1
          · have hm1 := (represents_back hSrep 1 W1 u) ⟨hu, fun _ hm => by cases hm⟩
            have hc1 := (hag' 1 (by omega) W1 u).mpr hm1
            exact (haga 1 (by omega) W1 u).mp hc1
        | none =>
          simp only [hfs] at hsc
          cases hvs : vs.lookup arraySpineKey with
          | none => simp [hvs] at hsc
          | some S =>
            simp only [hvs] at hsc
            split at hsc
            case h_2 => cases hsc
            rename_i tup hS
            obtain ⟨flds', l', c', oid', he, hfl', hlk', hag'⟩ :=
              viewsT_at (ReferenceConjunctions.mem_viewsOf.mpr ⟨S, PositiveRules.mem_of_lookup hvs, rfl⟩)
                (by simp [arraySpineKey, lengthKey]) hsem.1.2.1
            cases he; rw [hfl] at hfl'; cases hfl'
            rw [htr] at hlk'; cases hlk'
            have hSrep : Represents G S (.list tup []) := hS
            refine tupleDisjointFrom_contra (pr_a := pr_a) hsc (fun W1 u hu => ?_) (fun h => by cases h)
            have hc1 := (haga 1 (by omega) W1 u).mpr hu
            have hm1 := hag' 1 (by omega) W1 u hc1
            exact ((represents_raw hSrep 1 W1 u) hm1).1
    | _ => simp at hsc

/-- An element stored in a homogeneous array of element type `E` satisfies
`meaning G E` two levels below the array's budget. -/
theorem arrayElemType_sound {G : NormalGraph ι} {R E : Ty ι} {m : Nat} {W : WorldT (m + 4)} {h : Heap}
    {u w : Val} {st j l : Nat} {ls : List (Option Nat)}
    (hc : arrayElemType G R = some E) (hu : meaning G R (m + 4) W u) (hh : HeapOk (m + 4) W h)
    (hst : Footprints.spineOf u = some st) (hls : h[st]? = some (.arr ls))
    (hl : ls[j]? = some (some l)) (hw : h[l]? = some w) :
    meaning G E (m + 2) (trunc (m + 2) (by omega) W) w := by
  unfold arrayElemType at hc
  split at hc
  case h_2 => cases hc
  rename_i fs vs os ms ks st_keys hexp
  split at hc
  case h_2 => cases hc
  rename_i S hS
  split at hc
  case h_2 => cases hc
  rename_i ro pr hT
  cases hc
  have hr : Represents G R (.refs fs [] vs os ms ks st_keys) := hexp
  have hsem := (represents_raw hr _ W _) hu
  obtain ⟨flds, l0, c, oid, hobj, hf, hlc, hag⟩ : ∃ (flds : List (PropKey × Nat)) (l0 : Nat) (c : Ctr (m + 4)) (oid : Nat),
      u = .objAt flds .absent oid ∧ flds.lookup arraySpineKey = some l0 ∧ lookup W l0 = some c ∧
      ∀ (i : Nat) (hi : i < m + 4) (W' : WorldT i) (v : Val), c i hi W' v → meaning G S i W' v := by
    cases hfs : (Stored.views fs).lookup arraySpineKey with
    | some S' =>
      rw [hfs] at hS; simp only [Option.orElse_some, Option.some.injEq] at hS; subst hS
      obtain ⟨_, hm⟩ := Stored.mem_views.mp (PositiveRules.mem_of_lookup hfs)
      obtain ⟨flds, l0, c, oid, hobj, hf, hlc, hag⟩ :=
        recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨S', hm, rfl⟩) hsem.1.1
      exact ⟨flds, l0, c, oid, hobj, hf, hlc, fun i hi W' v hv => (hag i hi W' v).mp hv⟩
    | none =>
      rw [hfs] at hS; simp only [Option.orElse_none] at hS
      exact viewsT_at (ReferenceConjunctions.mem_viewsOf.mpr ⟨S, PositiveRules.mem_of_lookup hS, rfl⟩)
        (by simp [arraySpineKey, lengthKey]) hsem.2.1
  have hst0 : l0 = st := by
    rw [hobj] at hst; simp only [Footprints.spineOf, Footprints.fieldsOf] at hst
    rw [hf] at hst; cases hst; rfl
  subst hst0
  obtain ⟨v0, hv0, hvc⟩ := hh.1.2 l0 c hlc
  rw [hls] at hv0; cases hv0
  have hsp : meaning G S (m + 3) (trunc (m + 3) (by omega) W) (.arr ls) :=
    hag (m + 3) (by omega) _ _ (hvc (m + 3) (by omega))
  have hlist := ((represents_raw (show Represents G S (.list ⟨[], [], some E, ro, pr⟩ []) from hT) _ _ _) hsp).1
  obtain ⟨ls', heq, -, -, -, -, -, -, hrest⟩ := hlist
  cases heq
  obtain ⟨E', c', hE', hlk', hag'⟩ := hrest j l (by simp [tupleFams]) hl
  simp only [tupleFams, Option.map_some, Option.some.injEq] at hE'; subst hE'
  obtain ⟨c0, hc0, rfl⟩ := lookup_trunc_inv (by omega) W l c' hlk'
  obtain ⟨w', hw', hwc⟩ := hh.1.2 l c0 hc0
  rw [hw] at hw'; cases hw'
  exact (hag' (m + 2) (by omega) (trunc (m + 2) (by omega) W) w).1 (hwc (m + 2) (by omega))

/-! ### Dense-append heap transition -/

/-- The heap transition of a dense append `a[a.length] = v`: only the spine
cell `target` changes (growing by one cell at `h.length` holding `value`), and
every other location below `h.length` is unchanged. -/
structure DenseAppendHeap (h h' : Heap) (target : Nat) (xs : List (Option Nat)) (value : Val) : Prop where
  target_lt : target < h.length
  old_spine : h[target]? = some (.arr xs)
  new_spine : h'[target]? = some (.arr (placeAt xs xs.length h.length))
  fresh_val : h'[h.length]? = some value
  kept : ∀ l, l < h.length → l ≠ target → h'[l]? = h[l]?

theorem readPath_denseAppend {n : Nat} {W : WorldT n} {h h' : Heap} {target : Nat}
    {xs : List (Option Nat)} {value : Val}
    (hda : DenseAppendHeap h h' target xs value) (hh : HeapOk n W h)
    (htarg : roleAt W target = some (.spine .array)) :
    ∀ {p : List String} {v w : Val}, p.all (· != "[]") = true → RefsOk W v → readPath h v p = some w → readPath h' v p = some w
  | [], _, _, _, _, hr => hr
  | f :: q, v, w, hp, hv, hr => by
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne] at hp
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
          have hsr : SlotRole (.str f) (roleAt W l) := hv _ (refs_obj_slot_mem hlk)
          have hne : l ≠ target := by
            intro heq; subst heq; rw [htarg] at hsr
            simp [SlotRole, arraySpineKey] at hsr
            exact hp.1 hsr
          have hlt : l < h.length := (List.getElem?_eq_some_iff.mp hu).1
          rw [hda.kept l hlt hne, hu]
          obtain ⟨r, hrw⟩ := slotRole_some hsr
          obtain ⟨u', hu', hsh⟩ := hh.2 l r hrw
          rw [hu] at hu'; cases hu'
          exact readPath_denseAppend hda hh htarg hp.2 hsh.2 hr
    | _ => simp [readPath] at hr

theorem readGuard_denseAppend {n : Nat} {W : WorldT n} {h h' : Heap} {target : Nat}
    {xs : List (Option Nat)} {value : Val}
    (hda : DenseAppendHeap h h' target xs value) (hh : HeapOk n W h)
    (htarg : roleAt W target = some (.spine .array)) :
    ∀ {p : List String} {v w : Val}, p.all (· != "[]") = true → RefsOk W v → readGuard h v p = some w → readGuard h' v p = some w
  | [], _, _, _, _, hr => hr
  | f :: q, v, w, hp, hv, hr => by
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne] at hp
    cases v with
    | objAt fs cd oid =>
      simp only [readGuard] at hr ⊢
      cases hlk : fs.lookup (.str f) with
      | none =>
        simp only [hlk] at hr ⊢
        split at hr
        · rename_i hpr
          simp only [hpr, ite_true]
          exact readGuard_denseAppend hda hh htarg hp.2 (fun _ h => by simp [refs] at h) hr
        · cases hr
      | some l =>
        simp only [hlk] at hr ⊢
        cases hu : h[l]? with
        | none => simp [hu] at hr
        | some u =>
          simp only [hu] at hr
          have hsr : SlotRole (.str f) (roleAt W l) := hv _ (refs_obj_slot_mem hlk)
          have hne : l ≠ target := by
            intro heq; subst heq; rw [htarg] at hsr
            simp [SlotRole, arraySpineKey] at hsr
            exact hp.1 hsr
          have hlt : l < h.length := (List.getElem?_eq_some_iff.mp hu).1
          rw [hda.kept l hlt hne, hu]
          obtain ⟨r, hrw⟩ := slotRole_some hsr
          obtain ⟨u', hu', hsh⟩ := hh.2 l r hrw
          rw [hu] at hu'; cases hu'
          exact readGuard_denseAppend hda hh htarg hp.2 hsh.2 hr
    | _ => simp [readGuard] at hr

theorem elemCell_denseAppend {n : Nat} {W : WorldT n} {h h' : Heap} {target st l : Nat}
    {xs ls : List (Option Nat)} {value : Val}
    (hda : DenseAppendHeap h h' target xs value) (hh : HeapOk n W h)
    (htarg : roleAt W target = some (.spine .array))
    (hls : h[st]?.bind spineEntries = some ls) (hl : some l ∈ ls) :
    h'[l]? = h[l]? := by
  obtain ⟨hrole, hlt⟩ := hh.entries_cells hls hl
  exact hda.kept l hlt (fun heq => by subst heq; rw [htarg] at hrole; cases hrole)

theorem viewSpine_denseAppend {n : Nat} {W : WorldT n} {h h' : Heap} {target st : Nat}
    {xs : List (Option Nat)} {value w : Val}
    (hda : DenseAppendHeap h h' target xs value) (hh : HeapOk n W h)
    (htarg : roleAt W target = some (.spine .array))
    (hw : RefsOk W w) (he : elementsOf w = some st) (hns : Footprints.spineOf w = none) :
    h'[st]? = h[st]? := by
  cases w with
  | objAt fs cd oid =>
    simp only [Footprints.spineOf, Footprints.fieldsOf] at hns
    simp only [elementsOf, hns] at he
    cases cd with
    | view s f m =>
      cases he
      have hmem : Ref.view st f m (fs.lookup arraySpineKey).isNone ∈ refs (.objAt fs (.view st f m) oid) := by
        simp [refs]
      have hvr : roleAt W st = some (.spine (.view f m)) := (hw _ hmem).2
      have hne : st ≠ target := fun heq => by subst heq; rw [htarg] at hvr; cases hvr
      have hlt : st < h.length := by
        have hstlt := roleAt_lt hvr
        have hl : h.length = (entries W).length := by simpa using hh.1.1
        omega
      exact hda.kept st hlt hne
    | _ => simp at he
  | _ => simp [elementsOf] at he

/-! ### Dense-append framing and `IndexFact.every` extension -/

/-- Whether the array spine of `(s, p)` is provably distinct from `a`'s spine
`target`, by separation evidence (`knowledgeQuery`) or contract disjointness
(`spineTypesDisjoint`). -/
@[nospecialize] def spineDisjointFromA [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι))
    (k : Knowledge) (a : Nat) (E_a : Ty ι) (s : Nat) (p : List String) : Bool :=
  (Footprints.knowledgeQuery k).disjoint (.field a arraySpineKey) (.path s p arraySpineKey) ||
    (p.isEmpty && match Γ[s]? with | some T => spineTypesDisjoint G E_a T | none => false)

/-- Whether every element of array slot `s` has an array spine contract-disjoint
from `a`'s spine `target`. -/
@[nospecialize] def elemSpinesDisjointFromA [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι))
    (E_a : Ty ι) (s : Nat) : Bool :=
  match Γ[s]? with
  | some R => match arrayElemType G R with
    | some E_s => spineTypesDisjoint G E_a E_s
    | none => false
  | none => false

/-- Whether a term's value is preserved by a dense append on `a` (which modifies
only `target`, an array spine with element type `E_a`). -/
@[nospecialize] def termKeptByDenseAppend [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι))
    (k : Knowledge) (a : Nat) (E_a : Ty ι) (t : Term) : Bool :=
  t.atEntry || (t.path.all (· != "[]") && match t.kind with
    | .value | .strLength | .view => true
    | .length => spineDisjointFromA G Γ k a E_a t.slot t.path)

/-- Whether a quantified body clause over array slot `s` is preserved at existing
indices (`j < xs.length` when `allowParallelA` holds) across a dense append on
`a`. -/
@[nospecialize] def bodyClauseKeptByDenseAppend [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι))
    (k : Knowledge) (a : Nat) (E_a : Ty ι) (s : Nat) (allowParallelA : Bool) (B : BodyClause) : Bool :=
  let aCls := HeapLinks.aliases k.links a
  B.targets.all (fun
    | .self ep => ep.all (· != "[]")
    | .parallel s' p' ep => p'.all (· != "[]") && ep.all (· != "[]") &&
        ((allowParallelA && p'.isEmpty && aCls.contains s') || spineDisjointFromA G Γ k a E_a s' p')) &&
  B.vars.all (fun
    | .index | .elem | .offset _ => true
    | .free t => termKeptByDenseAppend G Γ k a E_a t
    | .project k' ep => ep.all (· != "[]") && (k' != .length || (ep.isEmpty && elemSpinesDisjointFromA G Γ E_a s))
    | .parallel s' p' k' ep => p'.all (· != "[]") && ep.all (· != "[]") &&
        ((allowParallelA && p'.isEmpty && aCls.contains s') || spineDisjointFromA G Γ k a E_a s' p') &&
        (k' != .length || (p'.isEmpty && ep.isEmpty && elemSpinesDisjointFromA G Γ E_a s')))

/-- Whether an index fact is preserved across a dense append on `a`. -/
@[nospecialize] def factKeptByDenseAppend [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι))
    (k : Knowledge) (a : Nat) (E_a : Ty ι) : IndexFact → Bool
  | .linear F => F.vars.all (termKeptByDenseAppend G Γ k a E_a)
  | .guarded _ p _ B => p.all (· != "[]") && factKeptByDenseAppend G Γ k a E_a B
  | .either A B => factKeptByDenseAppend G Γ k a E_a A && factKeptByDenseAppend G Γ k a E_a B
  | .element _ x _ => (HeapLinks.aliases k.links a).contains x || spineDisjointFromA G Γ k a E_a x []
  | .every s [] stop body =>
    spineDisjointFromA G Γ k a E_a s [] && termKeptByDenseAppend G Γ k a E_a stop &&
      body.all (bodyClauseKeptByDenseAppend G Γ k a E_a s false)
  | _ => false

/-- Guard tags from both `guardTags k` and `valuesAt G Γ k` on bare slots. -/
@[nospecialize] def denseTags [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) :
    Nat → List String → GuardTag → Bool :=
  fun s p t => guardTags k s p t ||
    (p.isEmpty && match HeapExpressionRules.valuesAt G Γ k s with
      | some V => onlyTag V t
      | none => false)

/-- Whether slot `r` is known not to hold `undefined` (by `valuesAt`). -/
@[nospecialize] def slotNotUndef [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (r : Nat) : Bool :=
  match HeapExpressionRules.valuesAt G Γ k r with
  | some V => onlyTag V .notUndef
  | none => false

/-- Resolve a parallel array `(s', p')` at the appended index `i`: either the
newly written value `v` when `s'` aliases `a` (and `parWritten = some v`), or a
non-`undefined` element binding `element r' s' i` on an array apart from `a`. -/
@[nospecialize] def resolveParallelAppend [DecidableEq ι] (K : Linear.Known Term) (G : NormalGraph ι)
    (Γ : List (Ty ι)) (k : Knowledge) (a : Nat) (E_a : Ty ι) (aCls : List Nat) (i : Nat)
    (parWritten : Option Nat) (s' : Nat) (p' : List String) : Option Nat :=
  if p'.isEmpty then
    match parWritten with
    | some v =>
      if aCls.contains s' then some v
      else match parallelSlot K k.links k.indices s' [] i with
        | some r' => if slotNotUndef G Γ k r' && spineDisjointFromA G Γ k a E_a s' [] then some r' else none
        | none => none
    | none =>
      match parallelSlot K k.links k.indices s' [] i with
      | some r' => if slotNotUndef G Γ k r' && spineDisjointFromA G Γ k a E_a s' [] then some r' else none
      | none => none
  else none

/-- Instantiate a bound variable at the appended index `i`, using `selfSlot` for
the quantified array's element and `resolveParallelAppend` for parallel arrays. -/
@[nospecialize] def boundForAppend [DecidableEq ι] (K : Linear.Known Term) (G : NormalGraph ι)
    (Γ : List (Ty ι)) (k : Knowledge) (a : Nat) (E_a : Ty ι) (aCls : List Nat) (i selfSlot : Nat)
    (parWritten : Option Nat) : Bound → Option Term
  | .index => some (.value i)
  | .elem => some (.value selfSlot)
  | .offset _ => none
  | .project kd ep => some (.now kd selfSlot ep)
  | .parallel s' p' kd ep =>
    (resolveParallelAppend K G Γ k a E_a aCls i parWritten s' p').map fun r' => .now kd r' ep
  | .free t => some t

/-- Instantiate a `BodyClause` at the appended index `i` into an `IndexFact`. -/
@[nospecialize] def bodyClauseForAppend [DecidableEq ι] (K : Linear.Known Term) (G : NormalGraph ι)
    (Γ : List (Ty ι)) (k : Knowledge) (a : Nat) (E_a : Ty ι) (aCls : List Nat) (i selfSlot : Nat)
    (parWritten : Option Nat) : BodyClause → Option IndexFact
  | .clause c =>
    (c.mapVars (boundForAppend K G Γ k a E_a aCls i selfSlot parWritten)).map LinearClause.toIndexFact
  | .guarded (.self ep) tag b =>
    (bodyClauseForAppend K G Γ k a E_a aCls i selfSlot parWritten b).map (.guarded selfSlot ep tag)
  | .guarded (.parallel s' p' ep) tag b => do
    let r' ← resolveParallelAppend K G Γ k a E_a aCls i parWritten s' p'
    let b' ← bodyClauseForAppend K G Γ k a E_a aCls i selfSlot parWritten b
    pure (.guarded r' ep tag b')

/-- Whether every clause in `body` instantiates at the appended index `i`, is
entailed by `k` (via `indicesCheckWith`), and survives the dense append on `a`
(`factKeptByDenseAppend`). -/
@[nospecialize] def bodyHoldsAtAppend [DecidableEq ι] (K : Linear.Known Term) (G : NormalGraph ι)
    (Γ : List (Ty ι)) (k : Knowledge) (a : Nat) (E_a : Ty ι) (aCls : List Nat) (i selfSlot : Nat)
    (parWritten : Option Nat) (body : List BodyClause) : Bool :=
  let tags := denseTags G Γ k
  let M := HeapLinks.aliases k.links
  body.all fun B =>
    match bodyClauseForAppend K G Γ k a E_a aCls i selfSlot parWritten B with
    | some F =>
      indicesCheckWith tags M k.links k.indices [{ fact := F }] none &&
        factKeptByDenseAppend G Γ k a E_a F
    | none => false

/-- Whether a quantified body references any array of `aCls` in parallel. -/
def bodyMentionsParallel (aCls : List Nat) (body : List BodyClause) : Bool :=
  body.any fun B =>
    B.targets.any (fun | .parallel s' [] _ => aCls.contains s' | _ => false) ||
    B.vars.any (fun | .parallel s' [] _ _ => aCls.contains s' | _ => false)

/-- The index atoms a dense-append bounded write `a[i] = v` (with `a.length ≤ i`
entailed by `k`) produces and preserves:
1. `element v a i`;
2. facts of `k` untouched by `a`'s spine (`factKeptByDenseAppend`);
3. for each unconditional `every s [] stop body` with `i ≤ stop`:
   - when `s` aliases `a`, preserves the prefix at `.value i` and extends to
     `.length s` when `v` satisfies `body` at `i`;
   - when `s` is apart from `a` and `body` references `a` in parallel, extends
     to `.length a` (and `.length s` when `s.length ≤ i + 1`) using `element r s i`
     when `(r, v)` satisfies `body` at `i`. -/
@[nospecialize] def denseAppendAtoms [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι))
    (k : Knowledge) (a i v : Nat) : List IndexAtom :=
  match Γ[a]? with
  | none => []
  | some R =>
    match writableElement G R with
    | none => []
    | some E_a =>
      let K := knownOf k.indices
      let aCls := HeapLinks.aliases k.links a
      let iCls := HeapLinks.aliases k.links i
      if !(aCls.any fun a' => iCls.any fun i' => K.entails (.le [(.length a', 1), (.value i', -1)] 0)) then
        []
      else
        let elemAtom : IndexAtom := { fact := .element v a i }
        let keptAtoms := k.indices.filter fun atom => factKeptByDenseAppend G Γ k a E_a atom.fact
        let everyAtoms := k.indices.flatMap fun atom =>
          if atom.cond.isSome then []
          else match atom.fact with
            | .every s [] stop body =>
              if !(termDefined k.indices stop && K.entails (.le [(.value i, 1), (stop, -1)] 0)) then []
              else if aCls.contains s then
                if body.all (bodyClauseKeptByDenseAppend G Γ k a E_a s true) then
                  { fact := .every s [] (.value i) body } ::
                    (if bodyHoldsAtAppend K G Γ k a E_a aCls i v none body then
                      [{ fact := .every s [] (.length s) body }] else [])
                else []
              else if spineDisjointFromA G Γ k a E_a s [] && bodyMentionsParallel aCls body &&
                  body.all (bodyClauseKeptByDenseAppend G Γ k a E_a s true) then
                match parallelSlot K k.links k.indices s [] i with
                | some r =>
                  if slotNotUndef G Γ k r && bodyHoldsAtAppend K G Γ k a E_a aCls i r (some v) body then
                    { fact := .every s [] (.length a) body } ::
                      (if termDefined k.indices (.length s) &&
                          K.entails (.le [(.length s, 1), (.value i, -1)] 1) then
                        [{ fact := .every s [] (.length s) body }] else [])
                  else []
                | none => []
              else []
            | _ => []
        (elemAtom :: keptAtoms ++ everyAtoms).eraseDups

private theorem spineDisjointFromA_ne [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge}
    {a s target st m : Nat} {p : List String} {E_a : Ty ι} {pr_a : ArrayPresence}
    {W : WorldT (m + 4)} {c_a : Ctr (m + 4)} {ρ : Env} {h : Heap} {w : Val}
    (hca : lookup W target = some c_a)
    (haga : ∀ (j : Nat) (hj : j < m + 4) (W' : WorldT j) (u : Val),
      c_a j hj W' u ↔ listT ⟨[], [], some (meaning G E_a), false, pr_a⟩ j W' u)
    (he : EnvOk G Γ ρ (m + 4) W) (hk : Holds k ε ρ h) (hh : HeapOk (m + 4) W h) (hρ : RootsOk W ρ)
    (hsa : Footprints.spineOf (ρ a) = some target)
    (hrp : readPath h (ρ s) p = some w) (hsw : Footprints.spineOf w = some st)
    (hdisj : spineDisjointFromA G Γ k a E_a s p = true) : st ≠ target := by
  simp only [spineDisjointFromA, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at hdisj
  rcases hdisj with hq | ⟨rfl, hty⟩
  · intro heq; subst heq
    have hlt := refsOk_spineOf_lt hh (Footprints.readPath_refs hh p (hρ s) hrp) hsw
    have hma : (Footprints.Region.field a arraySpineKey).mem ρ h st = true := by
      simpa [Footprints.Region.mem, Footprints.spineOf] using hsa
    have hms : (Footprints.Region.path s p arraySpineKey).mem ρ h st = true := by
      simp [Footprints.Region.mem, hrp]; simpa [Footprints.spineOf] using hsw
    exact Footprints.knowledgeQuery_sound hk hh hρ _ _ st hlt hq hma hms
  · simp only [readPath, Option.some.injEq] at hrp; subst hrp
    cases hTs : Γ[s]? with
    | none => simp [hTs] at hty
    | some T =>
      simp only [hTs] at hty
      have hws : meaning G T (m + 4) (trunc (m + 4) (Nat.le_refl _) W) (ρ s) :=
        (meaning_adm G T).down_le (m + 4) (m + 4) (Nat.le_refl _) W _ (he.2 s T hTs)
      exact spineTypesDisjoint_sound hca haga hty (by omega) (Nat.le_refl _) hws hsw

private theorem elementsOf_denseAppend_eq [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge}
    {a s target st m : Nat} {p : List String} {E_a : Ty ι} {pr_a : ArrayPresence}
    {W : WorldT (m + 4)} {c_a : Ctr (m + 4)} {ρ : Env} {h h' : Heap} {xs : List (Option Nat)}
    {value w : Val}
    (hda : DenseAppendHeap h h' target xs value)
    (htarg : roleAt W target = some (.spine .array))
    (hca : lookup W target = some c_a)
    (haga : ∀ (j : Nat) (hj : j < m + 4) (W' : WorldT j) (u : Val),
      c_a j hj W' u ↔ listT ⟨[], [], some (meaning G E_a), false, pr_a⟩ j W' u)
    (he : EnvOk G Γ ρ (m + 4) W) (hk : Holds k ε ρ h) (hh : HeapOk (m + 4) W h) (hρ : RootsOk W ρ)
    (hsa : Footprints.spineOf (ρ a) = some target)
    (hrp : readPath h (ρ s) p = some w) (hel : elementsOf w = some st)
    (hdisj : spineDisjointFromA G Γ k a E_a s p = true) : h'[st]? = h[st]? := by
  have hrefw := Footprints.readPath_refs hh p (hρ s) hrp
  cases hsp : Footprints.spineOf w with
  | none => exact viewSpine_denseAppend hda hh htarg hrefw hel hsp
  | some st' =>
    have heq : st' = st := by rw [elementsOf_spine hsp] at hel; cases hel; rfl
    rw [← heq]
    have hne := spineDisjointFromA_ne hca haga he hk hh hρ hsa hrp hsp hdisj
    exact hda.kept st' (refsOk_spineOf_lt hh hrefw hsp) hne

private theorem elemSpinesDisjointFromA_ne [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)}
    {s target st j l lw m : Nat} {E_a : Ty ι} {pr_a : ArrayPresence}
    {W : WorldT (m + 4)} {c_a : Ctr (m + 4)} {ρ : Env} {h : Heap} {ls : List (Option Nat)} {w : Val}
    (hca : lookup W target = some c_a)
    (haga : ∀ (j : Nat) (hj : j < m + 4) (W' : WorldT j) (u : Val),
      c_a j hj W' u ↔ listT ⟨[], [], some (meaning G E_a), false, pr_a⟩ j W' u)
    (he : EnvOk G Γ ρ (m + 4) W) (hh : HeapOk (m + 4) W h)
    (hdisj : elemSpinesDisjointFromA G Γ E_a s = true)
    (hel : elementsOf (ρ s) = some st) (hls : h[st]?.bind spineEntries = some ls)
    (hl : ls[j]? = some (some l)) (hw : h[l]? = some w) (hsw : Footprints.spineOf w = some lw) :
    lw ≠ target := by
  unfold elemSpinesDisjointFromA at hdisj
  cases hRs : Γ[s]? with
  | none => simp [hRs] at hdisj
  | some R =>
    simp only [hRs] at hdisj
    cases hEs : arrayElemType G R with
    | none => simp [hEs] at hdisj
    | some E_s =>
      simp only [hEs] at hdisj
      -- Extract `Footprints.spineOf (ρ s) = some st` and `h[st]? = some (.arr ls)` from `arrayElemType`.
      have hsp_arr : Footprints.spineOf (ρ s) = some st ∧ h[st]? = some (.arr ls) := by
        have hEs0 := hEs
        unfold arrayElemType at hEs0
        split at hEs0
        case h_2 => cases hEs0
        rename_i fs vs os ms ks st_keys hexp
        split at hEs0
        case h_2 => cases hEs0
        rename_i S hS
        split at hEs0
        case h_2 => cases hEs0
        rename_i ro pr hT
        cases hEs0
        have hr : Represents G R (.refs fs [] vs os ms ks st_keys) := hexp
        have hsem := (represents_raw hr _ W _) (he.2 s R hRs)
        obtain ⟨flds, l0, c, oid, hobj, hf, hlc, hag⟩ : ∃ (flds : List (PropKey × Nat)) (l0 : Nat) (c : Ctr (m + 4)) (oid : Nat),
            ρ s = .objAt flds .absent oid ∧ flds.lookup arraySpineKey = some l0 ∧ lookup W l0 = some c ∧
            ∀ (i : Nat) (hi : i < m + 4) (W' : WorldT i) (v : Val), c i hi W' v → meaning G S i W' v := by
          cases hfs : (Stored.views fs).lookup arraySpineKey with
          | some S' =>
            rw [hfs] at hS; simp only [Option.orElse_some, Option.some.injEq] at hS; subst hS
            obtain ⟨_, hm⟩ := Stored.mem_views.mp (PositiveRules.mem_of_lookup hfs)
            obtain ⟨flds, l0, c, oid, hobj, hf, hlc, hag⟩ :=
              recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨S', hm, rfl⟩) hsem.1.1
            exact ⟨flds, l0, c, oid, hobj, hf, hlc, fun i hi W' v hv => (hag i hi W' v).mp hv⟩
          | none =>
            rw [hfs] at hS; simp only [Option.orElse_none] at hS
            exact viewsT_at (ReferenceConjunctions.mem_viewsOf.mpr ⟨S, PositiveRules.mem_of_lookup hS, rfl⟩)
              (by simp [arraySpineKey, lengthKey]) hsem.2.1
        have hsp0 : Footprints.spineOf (ρ s) = some l0 := by simp [hobj, Footprints.spineOf, Footprints.fieldsOf, hf]
        have heq : l0 = st := by rw [elementsOf_spine hsp0] at hel; cases hel; rfl
        subst heq
        obtain ⟨u, hu, huc⟩ := hh.1.2 l0 c hlc
        have hSsem := hag (m + 3) (by omega) _ _ (huc (m + 3) (by omega))
        obtain ⟨ls0, rfl, -⟩ := ((represents_raw (show Represents G S (.list ⟨[], [], some E_s, ro, pr⟩ []) from hT) _ _ _) hSsem).1
        rw [hu] at hls; simp only [Option.bind_some, spineEntries, Option.some.injEq] at hls; subst hls
        exact ⟨hsp0, hu⟩
      have hwm := arrayElemType_sound hEs (he.2 s R hRs) hh hsp_arr.1 hsp_arr.2 hl hw
      exact spineTypesDisjoint_sound hca haga hdisj (by omega) (by omega) hwm hsw

private theorem termKeptByDenseAppend_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)}
    {k : Knowledge} {a target m : Nat} {E_a : Ty ι} {pr_a : ArrayPresence}
    {W : WorldT (m + 4)} {c_a : Ctr (m + 4)} {ρ : Env} {h h' : Heap} {xs : List (Option Nat)}
    {value : Val} {t : Term} {z : Int}
    (hda : DenseAppendHeap h h' target xs value)
    (htarg : roleAt W target = some (.spine .array))
    (hca : lookup W target = some c_a)
    (haga : ∀ (j : Nat) (hj : j < m + 4) (W' : WorldT j) (u : Val),
      c_a j hj W' u ↔ listT ⟨[], [], some (meaning G E_a), false, pr_a⟩ j W' u)
    (he : EnvOk G Γ ρ (m + 4) W) (hk : Holds k ε ρ h) (hh : HeapOk (m + 4) W h) (hρ : RootsOk W ρ)
    (hsa : Footprints.spineOf (ρ a) = some target)
    (hkept : termKeptByDenseAppend G Γ k a E_a t = true)
    (ht : termValue ε ρ h t = some z) : termValue ε ρ h' t = some z := by
  obtain ⟨kd, s, p, ent⟩ := t
  cases ent with
  | true => exact termValue_entry_some rfl ht
  | false =>
    simp only [termKeptByDenseAppend, Bool.false_or, Bool.and_eq_true] at hkept
    obtain ⟨hp, hkd⟩ := hkept
    rw [termValue_now rfl] at ht ⊢
    simp only [termAt, Option.bind_eq_some_iff] at ht ⊢
    obtain ⟨w, hrp, hkv⟩ := ht
    refine ⟨w, readPath_denseAppend hda hh htarg hp (hρ s) hrp, ?_⟩
    cases kd with
    | value | strLength | view => exact hkv
    | length =>
      obtain ⟨st, ls, hsw, hls, rfl, hmax⟩ := lengthOf_spine hkv
      have hne := spineDisjointFromA_ne hca haga he hk hh hρ hsa hrp hsw hkd
      have hlt : st < h.length := (List.getElem?_eq_some_iff.mp hls).1
      exact lengthOf_of_spine hsw (by rw [hda.kept st hlt hne]; exact hls) hmax

private theorem bodyClauseKeptByDenseAppend_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)}
    {k : Knowledge} {a s st target j m : Nat} {E_a : Ty ι} {pr_a : ArrayPresence}
    {allowParallelA : Bool}
    {W : WorldT (m + 4)} {c_a : Ctr (m + 4)} {ρ : Env} {h h' : Heap} {xs ls ls' : List (Option Nat)}
    {value : Val} {B : BodyClause}
    (hda : DenseAppendHeap h h' target xs value)
    (htarg : roleAt W target = some (.spine .array))
    (hca : lookup W target = some c_a)
    (haga : ∀ (j : Nat) (hj : j < m + 4) (W' : WorldT j) (u : Val),
      c_a j hj W' u ↔ listT ⟨[], [], some (meaning G E_a), false, pr_a⟩ j W' u)
    (he : EnvOk G Γ ρ (m + 4) W) (hk : Holds k ε ρ h) (hh : HeapOk (m + 4) W h) (hρ : RootsOk W ρ)
    (hsa : Footprints.spineOf (ρ a) = some target)
    (hels : elementsOf (ρ s) = some st) (hls : h[st]?.bind spineEntries = some ls)
    (hls_sub : ∀ d l, ls[j + d]? = some (some l) → ls'[j + d]? = some (some l))
    (hpar : allowParallelA = true → j < xs.length)
    (hkept : bodyClauseKeptByDenseAppend G Γ k a E_a s allowParallelA B = true)
    (hB : B.HoldsAt ε ρ h ls j) : B.HoldsAt ε ρ h' ls' j := by
  induction B with
  | guarded tgt tag b ih =>
    simp only [bodyClauseKeptByDenseAppend, BodyClause.targets, BodyClause.vars, List.all_cons,
      Bool.and_eq_true] at hkept
    obtain ⟨⟨htgt, hrestT⟩, hvars⟩ := hkept
    obtain ⟨w, hw, hor⟩ := hB
    have hread : tgt.read ρ h' ls' j = some w := by
      cases tgt with
      | self ep =>
        simp only [ElemTarget.read] at hw ⊢
        cases hl : ls[j]? with
        | none => simp [hl] at hw
        | some o =>
          cases o with
          | none => simp [hl] at hw
          | some l =>
            rw [hl] at hw
            have hl' : ls'[j]? = some (some l) := by simpa using hls_sub 0 l (by simpa using hl)
            rw [hl']
            obtain ⟨v, hv, hrg⟩ := Option.bind_eq_some_iff.mp hw
            have hcell := elemCell_denseAppend hda hh htarg hls (List.mem_of_getElem? hl)
            exact Option.bind_eq_some_iff.mpr ⟨v, by rw [hcell]; exact hv,
              readGuard_denseAppend hda hh htarg htgt (hh.refs_at hv) hrg⟩
      | parallel s' p' ep =>
        simp only [Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff, List.contains_iff_mem] at htgt
        obtain ⟨⟨hp', hep⟩, hpar_a | hdisj⟩ := htgt
        · obtain ⟨⟨hallow, rfl⟩, hal⟩ := hpar_a
          simp only [ElemTarget.read, readPath] at hw ⊢
          have hseq : ρ s' = ρ a := HeapLinks.aliases_eq hk.2.2.1 hal
          simp only [hseq, elementsOf_spine hsa] at hw ⊢
          simp only [hda.old_spine, Option.bind_some, spineEntries] at hw
          simp only [hda.new_spine, Option.bind_some, spineEntries]
          have hjlt := hpar hallow
          cases hl : xs[j]? with
          | none => simp [hl] at hw
          | some o =>
            cases o with
            | none => simp [hl] at hw
            | some l =>
              simp only [hl] at hw
              have hl' : (placeAt xs xs.length h.length)[j]? = some (some l) := by
                rw [placeAt_getElem?]; simp only [Nat.ne_of_lt hjlt, hjlt, ite_false, ite_true, hl]
              simp only [hl']
              obtain ⟨v, hv, hrg⟩ := Option.bind_eq_some_iff.mp hw
              have hcell := elemCell_denseAppend hda hh htarg (by rw [hda.old_spine]; rfl) (List.mem_of_getElem? hl)
              exact Option.bind_eq_some_iff.mpr ⟨v, by rw [hcell]; exact hv,
                readGuard_denseAppend hda hh htarg hep (hh.refs_at hv) hrg⟩
        · simp only [ElemTarget.read] at hw ⊢
          cases hrp : readPath h (ρ s') p' with
          | none => simp [hrp] at hw
          | some a' =>
            simp only [hrp] at hw
            simp only [readPath_denseAppend hda hh htarg hp' (hρ s') hrp]
            cases hel' : elementsOf a' with
            | none => simp [hel'] at hw
            | some st' =>
              simp only [hel'] at hw ⊢
              cases hls' : h[st']?.bind spineEntries with
              | none => simp [hls'] at hw
              | some ls2 =>
                simp only [hls'] at hw
                have hst_eq := elementsOf_denseAppend_eq hda htarg hca haga he hk hh hρ hsa hrp hel' hdisj
                simp only [hst_eq, hls']
                cases hl : ls2[j]? with
                | none => simp [hl] at hw
                | some o =>
                  cases o with
                  | none => simp [hl] at hw
                  | some l =>
                    simp only [hl] at hw ⊢
                    obtain ⟨v, hv, hrg⟩ := Option.bind_eq_some_iff.mp hw
                    have hcell := elemCell_denseAppend hda hh htarg hls' (List.mem_of_getElem? hl)
                    exact Option.bind_eq_some_iff.mpr ⟨v, by rw [hcell]; exact hv,
                      readGuard_denseAppend hda hh htarg hep (hh.refs_at hv) hrg⟩
    exact ⟨w, hread, hor.imp id (ih (by simp only [bodyClauseKeptByDenseAppend, hrestT, hvars, Bool.and_self]))⟩
  | clause c =>
    simp only [bodyClauseKeptByDenseAppend, BodyClause.targets, BodyClause.vars, List.all_nil,
      Bool.true_and, List.all_eq_true] at hkept
    refine LinearClause.holdsAt_extend (fun x hx z hz => ?_) hB
    have hxk := hkept x hx
    cases x with
    | index => exact hz
    | elem =>
      simp only [boundValue, elementInt] at hz ⊢
      cases hl : ls[j]? with
      | none => simp [hl] at hz
      | some o =>
        cases o with
        | none => simp [hl] at hz
        | some l =>
          simp only [hl] at hz
          have hl' : ls'[j]? = some (some l) := by simpa using hls_sub 0 l (by simpa using hl)
          simp only [hl', elemCell_denseAppend hda hh htarg hls (List.mem_of_getElem? hl)]
          exact hz
    | offset d =>
      simp only [boundValue, elementInt] at hz ⊢
      cases hl : ls[j + d]? with
      | none => simp [hl] at hz
      | some o =>
        cases o with
        | none => simp [hl] at hz
        | some l =>
          simp only [hl] at hz
          simp only [hls_sub d l hl, elemCell_denseAppend hda hh htarg hls (List.mem_of_getElem? hl)]
          exact hz
    | free t =>
      exact termKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hsa hxk hz
    | project kd ep =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, List.isEmpty_iff] at hxk
      obtain ⟨hep, hlen⟩ := hxk
      simp only [boundValue] at hz ⊢
      cases hl : ls[j]? with
      | none => simp [hl] at hz
      | some o =>
        cases o with
        | none => simp [hl] at hz
        | some l =>
          simp only [hl] at hz
          have hl' : ls'[j]? = some (some l) := by simpa using hls_sub 0 l (by simpa using hl)
          simp only [hl']
          obtain ⟨v, hv, htv⟩ := Option.bind_eq_some_iff.mp hz
          have hcell := elemCell_denseAppend hda hh htarg hls (List.mem_of_getElem? hl)
          refine Option.bind_eq_some_iff.mpr ⟨v, by rw [hcell]; exact hv, ?_⟩
          rw [termValue_now rfl] at htv ⊢
          simp only [termAt, Option.bind_eq_some_iff] at htv ⊢
          obtain ⟨w, hrp, hkv⟩ := htv
          refine ⟨w, readPath_denseAppend hda hh htarg hep (hh.refs_at hv) hrp, ?_⟩
          cases kd with
          | value | strLength | view => exact hkv
          | length =>
            rcases hlen with hne | ⟨rfl, hed⟩
            · exact absurd rfl hne
            · simp only [readPath, Option.some.injEq] at hrp; subst hrp
              obtain ⟨st_w, ls_w, hsw, hlsw, rfl, hmax⟩ := lengthOf_spine hkv
              have hne := elemSpinesDisjointFromA_ne hca haga he hh hed hels hls hl hv hsw
              exact lengthOf_of_spine hsw (by rw [hda.kept st_w (List.getElem?_eq_some_iff.mp hlsw).1 hne]; exact hlsw) hmax
    | parallel s' p' kd ep =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, List.isEmpty_iff, List.contains_iff_mem] at hxk
      obtain ⟨⟨⟨hp', hep⟩, hpar_a | hdisj⟩, hlen⟩ := hxk
      · obtain ⟨⟨hallow, rfl⟩, hal⟩ := hpar_a
        have hjlt := hpar hallow
        have hseq : ρ s' = ρ a := HeapLinks.aliases_eq hk.2.2.1 hal
        simp only [boundValue, readPath, hseq, elementsOf_spine hsa] at hz ⊢
        simp only [hda.old_spine, Option.bind_some, spineEntries] at hz
        simp only [hda.new_spine, Option.bind_some, spineEntries]
        cases hl : xs[j]? with
        | none => simp [hl] at hz
        | some o =>
          cases o with
          | none => simp [hl] at hz
          | some l =>
            simp only [hl] at hz
            have hl' : (placeAt xs xs.length h.length)[j]? = some (some l) := by
              rw [placeAt_getElem?]; simp only [Nat.ne_of_lt hjlt, hjlt, ite_false, ite_true, hl]
            simp only [hl']
            obtain ⟨v, hv, htv⟩ := Option.bind_eq_some_iff.mp hz
            have hcell := elemCell_denseAppend hda hh htarg (by rw [hda.old_spine]; rfl) (List.mem_of_getElem? hl)
            refine Option.bind_eq_some_iff.mpr ⟨v, by rw [hcell]; exact hv, ?_⟩
            rw [termValue_now rfl] at htv ⊢
            simp only [termAt, Option.bind_eq_some_iff] at htv ⊢
            obtain ⟨w, hrp, hkv⟩ := htv
            refine ⟨w, readPath_denseAppend hda hh htarg hep (hh.refs_at hv) hrp, ?_⟩
            cases kd with
            | value | strLength | view => exact hkv
            | length =>
              rcases hlen with hne | ⟨⟨-, rfl⟩, hed⟩
              · exact absurd rfl hne
              · simp only [readPath, Option.some.injEq] at hrp; subst hrp
                obtain ⟨st_w, ls_w, hsw, hlsw, rfl, hmax⟩ := lengthOf_spine hkv
                have hels' : elementsOf (ρ s') = some target := by rw [hseq]; exact elementsOf_spine hsa
                have hne := elemSpinesDisjointFromA_ne hca haga he hh hed hels' (by rw [hda.old_spine]; rfl) hl hv hsw
                exact lengthOf_of_spine hsw (by rw [hda.kept st_w (List.getElem?_eq_some_iff.mp hlsw).1 hne]; exact hlsw) hmax
      · simp only [boundValue] at hz ⊢
        cases hrp : readPath h (ρ s') p' with
        | none => simp [hrp] at hz
        | some a' =>
          simp only [hrp] at hz
          simp only [readPath_denseAppend hda hh htarg hp' (hρ s') hrp]
          cases hel' : elementsOf a' with
          | none => simp [hel'] at hz
          | some st' =>
            simp only [hel'] at hz ⊢
            cases hls2 : h[st']?.bind spineEntries with
            | none => simp [hls2] at hz
            | some ls2 =>
              simp only [hls2] at hz
              have hst_eq := elementsOf_denseAppend_eq hda htarg hca haga he hk hh hρ hsa hrp hel' hdisj
              simp only [hst_eq, hls2]
              cases hl : ls2[j]? with
              | none => simp [hl] at hz
              | some o =>
                cases o with
                | none => simp [hl] at hz
                | some l =>
                  simp only [hl] at hz ⊢
                  obtain ⟨v, hv, htv⟩ := Option.bind_eq_some_iff.mp hz
                  have hcell := elemCell_denseAppend hda hh htarg hls2 (List.mem_of_getElem? hl)
                  refine Option.bind_eq_some_iff.mpr ⟨v, by rw [hcell]; exact hv, ?_⟩
                  rw [termValue_now rfl] at htv ⊢
                  simp only [termAt, Option.bind_eq_some_iff] at htv ⊢
                  obtain ⟨w, hrpw, hkv⟩ := htv
                  refine ⟨w, readPath_denseAppend hda hh htarg hep (hh.refs_at hv) hrpw, ?_⟩
                  cases kd with
                  | value | strLength | view => exact hkv
                  | length =>
                    rcases hlen with hne | ⟨⟨rfl, rfl⟩, hed⟩
                    · exact absurd rfl hne
                    · simp only [readPath, Option.some.injEq] at hrp hrpw; subst hrp; subst hrpw
                      obtain ⟨st_w, ls_w, hsw, hlsw, rfl, hmax⟩ := lengthOf_spine hkv
                      have hne := elemSpinesDisjointFromA_ne hca haga he hh hed hel' hls2 hl hv hsw
                      exact lengthOf_of_spine hsw (by rw [hda.kept st_w (List.getElem?_eq_some_iff.mp hlsw).1 hne]; exact hlsw) hmax

private theorem factKeptByDenseAppend_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)}
    {k : Knowledge} {a target m : Nat} {E_a : Ty ι} {pr_a : ArrayPresence}
    {W : WorldT (m + 4)} {c_a : Ctr (m + 4)} {ρ : Env} {h h' : Heap} {xs : List (Option Nat)}
    {value : Val}
    (hda : DenseAppendHeap h h' target xs value)
    (htarg : roleAt W target = some (.spine .array))
    (hca : lookup W target = some c_a)
    (haga : ∀ (j : Nat) (hj : j < m + 4) (W' : WorldT j) (u : Val),
      c_a j hj W' u ↔ listT ⟨[], [], some (meaning G E_a), false, pr_a⟩ j W' u)
    (he : EnvOk G Γ ρ (m + 4) W) (hk : Holds k ε ρ h) (hh : HeapOk (m + 4) W h) (hρ : RootsOk W ρ)
    (hsa : Footprints.spineOf (ρ a) = some target) :
    ∀ {F : IndexFact}, factKeptByDenseAppend G Γ k a E_a F = true → F.HoldsAt ε ρ h → F.HoldsAt ε ρ h'
  | .linear L, hkept, hF => by
    simp only [factKeptByDenseAppend, List.all_eq_true] at hkept
    refine LinearClause.holdsAt_extend (F := .atom L) (fun t ht z hz =>
      termKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hsa (hkept t ht) hz) hF
  | .guarded s p tag B, hkept, ⟨w, hw, hor⟩ => by
    simp only [factKeptByDenseAppend, Bool.and_eq_true] at hkept
    exact ⟨w, readGuard_denseAppend hda hh htarg hkept.1 (hρ s) hw,
      hor.imp id (factKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hsa hkept.2)⟩
  | .either A B, hkept, hor => by
    simp only [factKeptByDenseAppend, Bool.and_eq_true] at hkept
    exact hor.imp (factKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hsa hkept.1)
      (factKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hsa hkept.2)
  | .element r x idxSlot, hkept, ⟨st, ls, b, idx, hel, hls, hbi, hsi, hlt, hpres, hhole⟩ => by
    simp only [factKeptByDenseAppend, Bool.or_eq_true, List.contains_iff_mem] at hkept
    rcases hkept with hal | hdisj
    · have hxeq : ρ x = ρ a := HeapLinks.aliases_eq hk.2.2.1 hal
      rw [hxeq, elementsOf_spine hsa] at hel; cases hel
      rw [hda.old_spine] at hls; simp only [Option.bind_some, spineEntries, Option.some.injEq] at hls; subst hls
      refine ⟨target, placeAt xs xs.length h.length, b, idx, by rw [hxeq]; exact elementsOf_spine hsa,
        by rw [hda.new_spine]; rfl, hbi, hsi, by rw [placeAt_length]; omega, fun l hl => ?_, fun hho => ?_⟩
      · rw [placeAt_getElem?] at hl; simp only [Nat.ne_of_lt hlt, hlt, ite_false, ite_true] at hl
        rw [elemCell_denseAppend hda hh htarg (by rw [hda.old_spine]; rfl) (List.mem_of_getElem? hl)]
        exact hpres l hl
      · rw [placeAt_getElem?] at hho; simp only [Nat.ne_of_lt hlt, hlt, ite_false, ite_true] at hho
        exact hhole hho
    · have hst_eq := elementsOf_denseAppend_eq hda htarg hca haga he hk hh hρ hsa rfl hel hdisj
      refine ⟨st, ls, b, idx, hel, by rw [hst_eq]; exact hls, hbi, hsi, hlt, fun l hl => ?_, hhole⟩
      rw [elemCell_denseAppend hda hh htarg hls (List.mem_of_getElem? hl)]
      exact hpres l hl
  | .every s [] stop body, hkept, ⟨w, st, ls, n0, hw, hel, hls, hstop, hall⟩ => by
    simp only [factKeptByDenseAppend, Bool.and_eq_true, List.all_eq_true] at hkept
    obtain ⟨⟨hdisj, hstK⟩, hbodyK⟩ := hkept
    simp only [readPath, Option.some.injEq] at hw; subst hw
    have hst_eq := elementsOf_denseAppend_eq hda htarg hca haga he hk hh hρ hsa rfl hel hdisj
    refine ⟨ρ s, st, ls, n0, rfl, hel, by rw [hst_eq]; exact hls,
      termKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hsa hstK hstop, fun j hj B hB => ?_⟩
    exact bodyClauseKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hsa hel hls
      (fun _ _ h => h) (fun h => by cases h) (hbodyK B hB) (hall j hj B hB)
  | .every _ (_ :: _) _ _, hkept, _ => by simp [factKeptByDenseAppend] at hkept
  | .index _, hkept, _ | .length _ _, hkept, _ | .bound _ _ _, hkept, _ | .int _, hkept, _
  | .pastSafe _, hkept, _ | .fieldRead _ _ _, hkept, _ | .atIndex _ _ _ _ _, hkept, _
  | .apart _ _, hkept, _ | .spineApart _ _ _ _, hkept, _ | .same _ _, hkept, _ => by
    simp [factKeptByDenseAppend] at hkept

private theorem denseTags_sound [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge}
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) :
    ∀ s p t, denseTags G Γ k s p t = true → ∃ v, readGuard h (ρ s) p = some v ∧ t.holds v := by
  intro s p t ht
  simp only [denseTags, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at ht
  rcases ht with hgt | ⟨rfl, hval⟩
  · exact guardTags_sound hk s p t hgt
  · cases hV : HeapExpressionRules.valuesAt G Γ k s with
    | none => simp [hV] at hval
    | some V =>
      rw [hV] at hval
      exact ⟨ρ s, rfl, onlyTag_mem hval (HeapExpressionRules.valuesAt_sound hV he hk)⟩

private theorem slotNotUndef_sound [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge}
    {r : Nat} {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) (hnu : slotNotUndef G Γ k r = true) :
    ρ r ≠ .undef := by
  unfold slotNotUndef at hnu
  cases hV : HeapExpressionRules.valuesAt G Γ k r with
  | none => simp [hV] at hnu
  | some V =>
    rw [hV] at hnu
    exact onlyTag_mem hnu (HeapExpressionRules.valuesAt_sound hV he hk)

private theorem bodyClauseForAppend_sound [DecidableEq ι] {K : Linear.Known Term} {G : NormalGraph ι}
    {Γ : List (Ty ι)} {k : Knowledge} {a i selfSlot idx target m : Nat}
    {E_a : Ty ι} {pr_a : ArrayPresence} {aCls : List Nat} {parWritten : Option Nat}
    {W : WorldT (m + 4)} {c_a : Ctr (m + 4)} {ρ : Env} {h h' : Heap} {xs ls_s : List (Option Nat)}
    {value : Val} {l_self : Nat}
    (hda : DenseAppendHeap h h' target xs value)
    (htarg : roleAt W target = some (.spine .array))
    (hca : lookup W target = some c_a)
    (haga : ∀ (j : Nat) (hj : j < m + 4) (W' : WorldT j) (u : Val),
      c_a j hj W' u ↔ listT ⟨[], [], some (meaning G E_a), false, pr_a⟩ j W' u)
    (he : EnvOk G Γ ρ (m + 4) W) (hk : Holds k ε ρ h) (hh : HeapOk (m + 4) W h) (hρ : RootsOk W ρ)
    (hK : K.Holds (termValuation ε ρ h))
    (hsa : Footprints.spineOf (ρ a) = some target)
    (haCls : ∀ x ∈ aCls, ρ x = ρ a)
    (hparW : ∀ v, parWritten = some v → ρ v = value)
    (hidx : intValue (ρ i) = some (idx : Int)) (hidx_len : idx = xs.length)
    (hself_l : ls_s[idx]? = some (some l_self)) (hself_v : h'[l_self]? = some (ρ selfSlot)) :
    ∀ {B : BodyClause} {F : IndexFact},
      bodyClauseForAppend K G Γ k a E_a aCls i selfSlot parWritten B = some F →
      F.HoldsAt ε ρ h' → B.HoldsAt ε ρ h' ls_s idx := by
  have hres_par : ∀ s' p' r',
      resolveParallelAppend K G Γ k a E_a aCls i parWritten s' p' = some r' →
      ∃ a' st' ls' l', readPath h' (ρ s') p' = some a' ∧ elementsOf a' = some st' ∧
        h'[st']?.bind spineEntries = some ls' ∧ ls'[idx]? = some (some l') ∧ h'[l']? = some (ρ r') := by
    intro s' p' r' hr
    unfold resolveParallelAppend at hr
    split at hr
    case isFalse => cases hr
    rename_i hp'
    simp only [List.isEmpty_iff] at hp'; subst hp'
    have hpar_slot : ∀ (hslot : parallelSlot K k.links k.indices s' [] i = some r')
        (hnu : slotNotUndef G Γ k r' = true) (hdisj : spineDisjointFromA G Γ k a E_a s' [] = true),
        ∃ a' st' ls' l', readPath h' (ρ s') [] = some a' ∧ elementsOf a' = some st' ∧
          h'[st']?.bind spineEntries = some ls' ∧ ls'[idx]? = some (some l') ∧ h'[l']? = some (ρ r') := by
      intro hslot hnu hdisj
      -- Extract `elementsOf (ρ s') = some st'` and `h[st']?.bind spineEntries = some ls'` from `parallelSlot`.
      simp only [parallelSlot, Option.bind_eq_bind, Option.bind_eq_some_iff] at hslot
      obtain ⟨at_, hfind, hm⟩ := hslot
      have hc := List.find?_some hfind
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
      obtain ⟨hcond, hc⟩ := hc
      have hat := hk.2.2.2.2.2 at_ (List.mem_of_find?_eq_some hfind) (fun b hb => by rw [hcond] at hb; cases hb)
      cases hf : at_.fact <;> simp only [hf] at hm hc hat <;> try cases hm
      rename_i y j0
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      obtain ⟨hpath, hjk⟩ := hc
      obtain ⟨st', ls', b', j1, hst', hls', hj0, hsi, hlt, hpres, hhole⟩ := hat
      have hyeq : ρ s' = ρ y := readsPath_eq hk.2.2.1 hpath rfl
      have hj1 : intValue (ρ j0) = some (j1 : Int) := by rw [hj0]; exact intValue_num hsi
      have hj_eq : j1 = idx := by
        rcases hjk with rfl | ⟨hlo, hhi⟩
        · rw [hidx] at hj1; cases hj1; rfl
        · have lo := Linear.Known.entails_sound hK hlo
          have hi := Linear.Known.entails_sound hK hhi
          simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, termValue_value, hidx, hj1, Option.getD_some] at lo hi
          omega
      subst hj_eq
      have hst_eq := elementsOf_denseAppend_eq hda htarg hca haga he hk hh hρ hsa rfl (by rw [hyeq]; exact hst') hdisj
      cases hl : ls'[j1]? with
      | none => exact absurd (List.getElem?_eq_none_iff.mp hl) (by omega)
      | some o =>
        cases o with
        | none => exact absurd (hhole hl) (slotNotUndef_sound he hk hnu)
        | some l' =>
          have hcell := elemCell_denseAppend hda hh htarg hls' (List.mem_of_getElem? hl)
          exact ⟨ρ s', st', ls', l', rfl, by rw [hyeq]; exact hst', by rw [hst_eq]; exact hls', hl,
            by rw [hcell]; exact hpres l' hl⟩
    cases hpw : parWritten with
    | some v =>
      simp only [hpw] at hr
      split at hr
      · rename_i hmem
        simp only [Option.some.injEq] at hr; subst hr
        have hseq : ρ s' = ρ a := haCls s' (List.contains_iff_mem.mp hmem)
        refine ⟨ρ s', target, placeAt xs xs.length h.length, h.length, rfl, by rw [hseq]; exact elementsOf_spine hsa,
          by rw [hda.new_spine]; rfl, ?_, by rw [hda.fresh_val, hparW v hpw]⟩
        rw [hidx_len, placeAt_getElem?]; simp
      · cases hslot : parallelSlot K k.links k.indices s' [] i with
        | none => simp [hslot] at hr
        | some r0 =>
          simp only [hslot] at hr
          split at hr
          · rename_i hcond
            simp only [Option.some.injEq] at hr; subst hr
            obtain ⟨hnu, hdisj⟩ := Bool.and_eq_true_iff.mp hcond
            exact hpar_slot hslot hnu hdisj
          · cases hr
    | none =>
      simp only [hpw] at hr
      cases hslot : parallelSlot K k.links k.indices s' [] i with
      | none => simp [hslot] at hr
      | some r0 =>
        simp only [hslot] at hr
        split at hr
        · rename_i hcond
          simp only [Option.some.injEq] at hr; subst hr
          obtain ⟨hnu, hdisj⟩ := Bool.and_eq_true_iff.mp hcond
          exact hpar_slot hslot hnu hdisj
        · cases hr
  intro B
  induction B with
  | clause c =>
    intro F hinst hF
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hinst
    have hc'H := LinearClause.toIndexFact_holds.mp hF
    refine (LinearClause.holdsAt_mapVars hc' fun x _ t ht => ?_).mp hc'H
    cases x with
    | index =>
      simp only [boundForAppend, Option.some.injEq] at ht; subst ht
      simp only [termValue_value, hidx, boundValue]
    | elem =>
      simp only [boundForAppend, Option.some.injEq] at ht; subst ht
      simp only [termValue_value, boundValue, elementInt, hself_l, hself_v, Option.bind_some]
    | offset _ => simp [boundForAppend] at ht
    | project kd ep =>
      simp only [boundForAppend, Option.some.injEq] at ht; subst ht
      simp only [boundValue, hself_l, hself_v, Option.bind_some]
      rw [termValue_now rfl, termValue_now rfl]; rfl
    | parallel s' p' kd ep =>
      obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp ht
      obtain ⟨a', st', ls', l', hrp, hel', hls', hl', hv'⟩ := hres_par s' p' r' hr'
      simp only [boundValue, hrp, hel', hls', hl', hv', Option.bind_some]
      rw [termValue_now rfl, termValue_now rfl]; rfl
    | free t' =>
      simp only [boundForAppend, Option.some.injEq] at ht; subst ht; rfl
  | guarded tgt tag b ih =>
    intro F hinst hF
    cases tgt with
    | self ep =>
      obtain ⟨Fb, hFb, rfl⟩ := Option.map_eq_some_iff.mp hinst
      obtain ⟨w, hrg, hor⟩ := hF
      refine ⟨w, by simp only [ElemTarget.read, hself_l, hself_v, Option.bind_some]; exact hrg,
        hor.imp id (ih hFb)⟩
    | parallel s' p' ep =>
      simp only [bodyClauseForAppend, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hinst
      obtain ⟨r', hr', Fb, hFb, rfl⟩ := hinst
      obtain ⟨a', st', ls', l', hrp, hel', hls', hl', hv'⟩ := hres_par s' p' r' hr'
      obtain ⟨w, hrg, hor⟩ := hF
      refine ⟨w, by simp only [ElemTarget.read, hrp, hel', hls', hl', hv', Option.bind_some]; exact hrg,
        hor.imp id (ih hFb)⟩

theorem denseAppendAtoms_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {k : Knowledge} {a i v : Nat} {sub : PositiveCertificates.SubtypeChoices ι}
    (hc : boundedWriteCheck G images j k a i v sub = true) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) (hρ : RootsOk W ρ) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' _ => IndexHolds ε (denseAppendAtoms G j.context k a i v) ρ h') n W h (instantiate 0 ρ j.term) := by
  have hsafe0 := boundedWrite_sound hc he hk hw hh href
  have hcheck := hc
  simp only [boundedWriteCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨hslots, -⟩, htypes⟩, hbd⟩, -⟩ := hcheck
  cases hRa : j.context[a]? with
  | none =>
    exact weaken (fun _ _ _ => by simp [denseAppendAtoms, hRa, IndexHolds]) hsafe0
  | some R =>
    cases hEa : writableElement G R with
    | none =>
      exact weaken (fun _ _ _ => by simp [denseAppendAtoms, hRa, hEa, IndexHolds]) hsafe0
    | some E_a =>
      let K := knownOf k.indices
      let aCls := HeapLinks.aliases k.links a
      let iCls := HeapLinks.aliases k.links i
      by_cases hda_cond : (aCls.any fun a' => iCls.any fun i' =>
          K.entails (.le [(.length a', 1), (.value i', -1)] 0)) = true
      case neg =>
        have hnil : denseAppendAtoms G j.context k a i v = [] := by
          simp [denseAppendAtoms, hRa, hEa, K, aCls, iCls, hda_cond]
        rw [hnil]
        exact weaken (fun _ _ _ => indexHolds_nil _ _) hsafe0
      have hvl : v < j.context.length := by
        rw [hRa] at htypes
        split at htypes
        · rename_i V hV; exact (List.getElem?_eq_some_iff.mp hV).1
        · cases htypes
      obtain ⟨fs, vs, os, ms, ks, st_keys, sr, S_a, pr_a, hrep, hm_sp, hS_a⟩ := writableElement_sound hEa
      obtain ⟨s, ls, b, idx, hs0, hl, hb, hidx, hle⟩ := bounded_sound hbd hk
      have hle' : idx ≤ ls.length := by simpa using hle
      obtain ⟨flds, cd, oid, hoi⟩ : ∃ flds cd oid, ρ a = .objAt flds cd oid := by
        cases hra : ρ a
        case objAt => exact ⟨_, _, _, rfl⟩
        all_goals rw [hra] at hs0; simp [Footprints.spineOf, Footprints.fieldsOf] at hs0
      have hfl : flds.lookup arraySpineKey = some s := by
        simpa [Footprints.spineOf, Footprints.fieldsOf, hoi] using hs0
      have hval : isVal (ρ v) = true := (meaning_value (he.2 v _ (List.getElem?_eq_getElem hvl))).1
      have hK : K.Holds (termValuation ε ρ h) := knownOf_holds hk.2.2.2.2.2
      have hidx_int : intValue (ρ i) = some (idx : Int) := by
        rw [hb]; exact intValue_num (index_safeInt hidx)
      have hidx_eq_of : n ≥ 4 → idx = ls.length := fun hn4 => by
        obtain ⟨a', ha', hi'⟩ := List.any_eq_true.mp hda_cond
        obtain ⟨i', hi'm, hent⟩ := List.any_eq_true.mp hi'
        have haeq : ρ a' = ρ a := HeapLinks.aliases_eq hk.2.2.1 ha'
        have hieq : ρ i' = ρ i := HeapLinks.aliases_eq hk.2.2.1 hi'm
        have hlen_a : termValue ε ρ h (.length a') = some (ls.length : Int) := by
          simp only [termValue_length, haeq]
          refine lengthOf_of_spine hs0 hl ?_
          obtain ⟨flds1, l1, c1, oid1, h1, hf1, hlk1, hag1⟩ :=
            recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨S_a, hm_sp, rfl⟩)
              ((represents_raw hrep n W _) (he.2 a R hRa)).1.1
          rw [hoi] at h1; cases h1; rw [hfl] at hf1; cases hf1
          obtain ⟨u1, hu1, huc1⟩ := hh.1.2 s c1 hlk1
          rw [hl] at hu1; cases hu1
          have hsp1 := (hag1 (n - 1) (by omega) _ _).mp (huc1 (n - 1) (by omega))
          obtain ⟨ls1, heq1, -, -, hmax1, -⟩ := ((represents_raw hS_a (n - 1) _ _) hsp1).1
          cases heq1; exact hmax1
        have hli := Linear.Known.entails_sound hK hent
        simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hlen_a, termValue_value, hieq,
          hidx_int, Option.getD_some] at hli
        omega
      rw [boundedSlots_eq hslots] at hsafe0 ⊢
      have hsafe := HeapObservations.erase hsafe0
      simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero, hoi, hb] at hsafe ⊢
      refine elementWrite_post4 hfl hl hval (fun hn4 cell hcell => ?_) (fun hn4 i' hi' _ => ?_) hsafe
      · -- Present branch is impossible because `idx = ls.length`.
        have hidx_eq := hidx_eq_of hn4
        simp only [elemLoc, hidx, hidx_eq, Option.bind_some, List.getElem?_eq_none (Nat.le_refl _)] at hcell
        cases hcell
      · rw [hidx] at hi'; cases hi'
        have hidx_eq := hidx_eq_of hn4
        -- Obtain `m` with `n = m + 4`.
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
        have htl : s < h.length := (List.getElem?_eq_some_iff.mp hl).1
        let h' := (h ++ [ρ v]).set s (.arr (placeAt ls ls.length h.length))
        have hda : DenseAppendHeap h h' s ls (ρ v) := by
          refine ⟨htl, hl, ?_, ?_, fun l hlt hne => ?_⟩
          · rw [List.getElem?_set_self (by simp; omega)]
          · rw [List.getElem?_set_ne (by omega), List.getElem?_append_right (Nat.le_refl _)]
            simp
          · rw [List.getElem?_set_ne (Ne.symm hne), List.getElem?_append_left hlt]
        have htarg : roleAt W s = some (.spine .array) := by
          have hsr : SlotRole arraySpineKey (roleAt W s) :=
            (hρ a) (.slot arraySpineKey s) (by rw [hoi]; exact refs_obj_slot_mem hfl)
          rcases hr : roleAt W s with _ | role
          · rw [hr] at hsr; cases hsr
          · rw [hr] at hsr
            cases role with
            | spine f => cases f with | array => rfl | view => simp [SlotRole] at hsr
            | _ => simp [SlotRole] at hsr
        obtain ⟨flds1, l1, c_a, oid1, h1, hf1, hca, haga0⟩ :=
          recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨S_a, hm_sp, rfl⟩)
            ((represents_raw hrep (m + 4) W _) (he.2 a R hRa)).1.1
        rw [hoi] at h1; cases h1; rw [hfl] at hf1; cases hf1
        have haga : ∀ (j : Nat) (hj : j < m + 4) (W' : WorldT j) (u : Val),
            c_a j hj W' u ↔ listT ⟨[], [], some (meaning G E_a), false, pr_a⟩ j W' u := by
          intro j hj W' u
          rw [haga0 j hj W' u]
          exact ⟨fun h => ((represents_raw hS_a j W' u) h).1,
            fun h => (represents_back hS_a j W' u) ⟨h, fun _ hm => by cases hm⟩⟩
        have hmax' : (placeAt ls ls.length h.length).length ≤ maxArrayLength := by
          have := indexOfBits_lt hidx; rw [placeAt_length]; omega
        rw [hidx_eq]
        change IndexHolds ε (denseAppendAtoms G j.context k a i v) ρ h'
        intro atom hm hcond
        simp only [denseAppendAtoms, hRa, hEa, K, aCls, iCls, hda_cond, Bool.not_true, Bool.false_eq_true,
          ite_false] at hm
        have hm' := List.mem_eraseDups.mp hm
        rcases List.mem_cons.mp hm' with rfl | hm'
        · -- 1. `element v a i`
          refine ⟨s, placeAt ls ls.length h.length, b, ls.length, elementsOf_spine hs0,
            by rw [hda.new_spine]; rfl, hb, hidx_eq ▸ index_safeInt hidx,
            by rw [placeAt_length]; omega, fun l hl' => ?_, fun hho => ?_⟩
          · rw [placeAt_getElem?] at hl'; simp only [ite_true, Option.some.injEq] at hl'; subst hl'
            exact hda.fresh_val
          · rw [placeAt_getElem?] at hho; simp at hho
        · rcases List.mem_append.mp hm' with hm_kept | hm_ev
          · -- 2. `factKeptByDenseAppend`
            obtain ⟨ha_mem, hfk⟩ := List.mem_filter.mp hm_kept
            exact factKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hs0 hfk
              (hk.2.2.2.2.2 atom ha_mem hcond)
          · -- 3. `every` preservation and extension
            obtain ⟨src, hsrc_mem, hflat⟩ := List.mem_flatMap.mp hm_ev
            split at hflat
            · cases hflat
            rename_i hnone
            have hnone' : src.cond = none := by cases hsc : src.cond <;> simp_all
            have hsrc_H := hk.2.2.2.2.2 src hsrc_mem (fun b hb => by rw [hnone'] at hb; cases hb)
            cases hsf : src.fact <;> simp only [hsf] at hflat <;> try cases hflat
            rename_i s_ev p_ev stop body
            cases p_ev with
            | cons _ _ => simp at hflat
            | nil =>
              rw [hsf] at hsrc_H
              obtain ⟨w0, st0, ls0, n0, hw0, hel0, hls0, hstop0, hall0⟩ := hsrc_H
              simp only [readPath, Option.some.injEq] at hw0; subst hw0
              cases hstop_ok : (termDefined k.indices stop && (knownOf k.indices).entails (.le [(.value i, 1), (stop, -1)] 0)) with
              | false => simp [hstop_ok] at hflat
              | true =>
                simp only [hstop_ok, Bool.not_true, Bool.false_eq_true, ite_false] at hflat
                obtain ⟨-, hent_stop⟩ := Bool.and_eq_true_iff.mp hstop_ok
                have hi_le_n0 : (ls.length : Int) ≤ n0 := by
                  have hent := Linear.Known.entails_sound hK hent_stop
                  simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, termValue_value, hidx_int,
                    hidx_eq, hstop0, Option.getD_some] at hent
                  omega
                have hbody_at : ∀ selfSlot parWritten,
                    (∀ v0, parWritten = some v0 → ρ v0 = ρ v) →
                    ∀ ls_t l_self,
                    ls_t[ls.length]? = some (some l_self) → h'[l_self]? = some (ρ selfSlot) →
                    bodyHoldsAtAppend K G j.context k a E_a aCls i selfSlot parWritten body = true →
                    ∀ B ∈ body, B.HoldsAt ε ρ h' ls_t ls.length := by
                  intro selfSlot parWritten hpw ls_t l_self hsl hsv hba B hB
                  have hBc := List.all_eq_true.mp hba B hB
                  cases hinst : bodyClauseForAppend K G j.context k a E_a aCls i selfSlot parWritten B with
                  | none => simp [hinst] at hBc
                  | some F =>
                    simp only [hinst] at hBc
                    obtain ⟨hchk, hfk⟩ := Bool.and_eq_true_iff.mp hBc
                    have hF_h : F.HoldsAt ε ρ h := by
                      have hres := indicesCheckWith_sound (denseTags_sound he hk)
                        (fun _ _ hm => HeapLinks.aliases_eq hk.2.2.1 hm) hk.2.2.1 hchk hk.2.2.2.2.2
                        { fact := F } (List.mem_singleton_self _) (fun _ hc' => by cases hc')
                      rwa [show PointClaims.mapEnv none ρ = ρ from by funext x; rfl] at hres
                    have hF_h' := factKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hs0 hfk hF_h
                    exact hidx_eq ▸ bodyClauseForAppend_sound hda htarg hca haga he hk hh hρ hK hs0
                      (fun x hx => HeapLinks.aliases_eq hk.2.2.1 hx) hpw hidx_int hidx_eq
                      (hidx_eq ▸ hsl) hsv hinst hF_h'
                split at hflat
                · -- Case 1: `s_ev ∈ aCls` (single-array `every` on `a`)
                  rename_i hsa_ev
                  split at hflat
                  case isFalse => cases hflat
                  rename_i hbk
                  simp only [List.all_eq_true] at hbk
                  have hs_eq : ρ s_ev = ρ a := HeapLinks.aliases_eq hk.2.2.1 (List.contains_iff_mem.mp hsa_ev)
                  rw [hs_eq, elementsOf_spine hs0] at hel0; cases hel0
                  rw [hda.old_spine] at hls0
                  simp only [Option.bind_some, spineEntries, Option.some.injEq] at hls0; subst hls0
                  have hprefix : ∀ j0 : Nat, j0 < ls.length → ∀ B ∈ body,
                      B.HoldsAt ε ρ h' (placeAt ls ls.length h.length) j0 := by
                    intro j0 hj0 B hB
                    refine bodyClauseKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hs0
                      (by rw [hs_eq]; exact elementsOf_spine hs0) (by rw [hda.old_spine]; rfl)
                      (fun d l hl0 => by
                        have hlt0 : j0 + d < ls.length := (List.getElem?_eq_some_iff.mp hl0).1
                        rw [placeAt_getElem?]; simp only [Nat.ne_of_lt hlt0, hlt0, ite_false, ite_true, hl0])
                      (fun _ => hj0) (hbk B hB) (hall0 j0 (by omega) B hB)
                  rcases List.mem_cons.mp hflat with rfl | hflat
                  · -- Prefix at `.value i`
                    refine ⟨ρ s_ev, s, placeAt ls ls.length h.length, ls.length, rfl,
                      by rw [hs_eq]; exact elementsOf_spine hs0, by rw [hda.new_spine]; rfl,
                      by simp [termValue_value, hidx_int, hidx_eq], fun j0 hj0 B hB => hprefix j0 (by omega) B hB⟩
                  · -- Full extension to `.length s_ev`
                    split at hflat
                    case isFalse => cases hflat
                    rename_i hba
                    simp only [List.mem_singleton] at hflat; subst hflat
                    refine ⟨ρ s_ev, s, placeAt ls ls.length h.length, (placeAt ls ls.length h.length).length, rfl,
                      by rw [hs_eq]; exact elementsOf_spine hs0, by rw [hda.new_spine]; rfl,
                      by simp only [termValue_length, hs_eq]; exact lengthOf_of_spine hs0 hda.new_spine hmax',
                      fun j0 hj0 B hB => ?_⟩
                    rw [placeAt_length] at hj0
                    by_cases hjlt : j0 < ls.length
                    · exact hprefix j0 hjlt B hB
                    · have hjeq : j0 = ls.length := by omega
                      subst hjeq
                      exact hbody_at v none (fun _ h => by cases h) (placeAt ls ls.length h.length) h.length
                        (by rw [placeAt_getElem?]; simp) hda.fresh_val hba B hB
                · -- Case 2: `s_ev` apart from `a`, referencing `a` in parallel
                  split at hflat
                  case isFalse => cases hflat
                  rename_i hpar_cond
                  simp only [Bool.and_eq_true, List.all_eq_true] at hpar_cond
                  obtain ⟨⟨hdisj_s, -⟩, hbk⟩ := hpar_cond
                  cases hps : parallelSlot (knownOf k.indices) k.links k.indices s_ev [] i with
                  | none => simp [hps] at hflat
                  | some r =>
                    simp only [hps] at hflat
                    split at hflat
                    case isFalse => cases hflat
                    rename_i hr_cond
                    obtain ⟨hnu, hba⟩ := Bool.and_eq_true_iff.mp hr_cond
                    have hst_eq := elementsOf_denseAppend_eq hda htarg hca haga he hk hh hρ hs0 rfl hel0 hdisj_s
                    have hpr := parallelSlot_read hK hk.2.2.1 hk.2.2.2.2.2 (hidx_eq ▸ hidx_int) hps rfl hel0 hls0
                    obtain ⟨hlt_s, hpres_s, hhole_s⟩ := hpr
                    obtain ⟨l_r, hl_r, hv_r⟩ : ∃ l_r, ls0[ls.length]? = some (some l_r) ∧ h'[l_r]? = some (ρ r) := by
                      cases hl0 : ls0[ls.length]? with
                      | none => exact absurd (List.getElem?_eq_none_iff.mp hl0) (by omega)
                      | some o =>
                        cases o with
                        | none => exact absurd (hhole_s hl0) (slotNotUndef_sound he hk hnu)
                        | some l_r =>
                          exact ⟨l_r, rfl, by
                            rw [elemCell_denseAppend hda hh htarg hls0 (List.mem_of_getElem? hl0)]
                            exact hpres_s l_r hl0⟩
                    have hstep_all : ∀ j0 : Nat, j0 < ls.length + 1 → ∀ B ∈ body, B.HoldsAt ε ρ h' ls0 j0 := by
                      intro j0 hj0 B hB
                      by_cases hjlt : j0 < ls.length
                      · exact bodyClauseKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hs0 hel0 hls0
                          (fun _ _ h => h) (fun _ => hjlt) (hbk B hB) (hall0 j0 (by omega) B hB)
                      · have hjeq : j0 = ls.length := by omega
                        subst hjeq
                        exact hbody_at r (some v) (fun v0 hv0 => by cases hv0; rfl) ls0 l_r hl_r hv_r hba B hB
                    rcases List.mem_cons.mp hflat with rfl | hflat
                    · -- Extension to `.length a`
                      refine ⟨ρ s_ev, st0, ls0, (placeAt ls ls.length h.length).length, rfl, hel0,
                        by rw [hst_eq]; exact hls0,
                        by simp only [termValue_length]; exact lengthOf_of_spine hs0 hda.new_spine hmax',
                        fun j0 hj0 B hB => hstep_all j0 (by rw [placeAt_length] at hj0; omega) B hB⟩
                    · -- Extension to `.length s_ev` when `s_ev.length ≤ i + 1`
                      split at hflat
                      case isFalse => cases hflat
                      rename_i hs_len_cond
                      simp only [List.mem_singleton] at hflat; subst hflat
                      obtain ⟨hdef_s, hent_s⟩ := Bool.and_eq_true_iff.mp hs_len_cond
                      obtain ⟨ns, hns⟩ := Option.isSome_iff_exists.mp (termDefined_sound hk.2.2.2.2.2 hdef_s)
                      have hns' : termValue ε ρ h' (.length s_ev) = some ns :=
                        termKeptByDenseAppend_holds hda htarg hca haga he hk hh hρ hs0
                          (by simp [termKeptByDenseAppend, Term.length, hdisj_s]) hns
                      have hns_le : ns ≤ (ls.length : Int) + 1 := by
                        have hl_s := Linear.Known.entails_sound hK hent_s
                        simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hns, termValue_value,
                          hidx_int, hidx_eq, Option.getD_some] at hl_s
                        omega
                      refine ⟨ρ s_ev, st0, ls0, ns, rfl, hel0, by rw [hst_eq]; exact hls0, hns',
                        fun j0 hj0 B hB => hstep_all j0 (by omega) B hB⟩

end Verification.IndexWrites

namespace Verification.HeapExpressionRules
variable {ε : Verification.HeapKnowledge.EntryState}
open ProgramCertificates PositiveGraphs HeapObservations
open PositiveCertificates (InstanceImageCheck)

theorem indexHolds_append {as bs : List HeapKnowledge.IndexAtom} {ρ h}
    (ha : HeapKnowledge.IndexHolds ε as ρ h) (hb : HeapKnowledge.IndexHolds ε bs ρ h) :
    HeapKnowledge.IndexHolds ε (as ++ bs) ρ h := fun a hm hc =>
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
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hρ
    simp only [CheckResult.map, Option.map_eq_some_iff] at hc
    obtain ⟨out0, hrun, rfl⟩ := hc
    have hs := base.sound hrun hcodes hsums he hk hw hh href hρ
    refine weaken (fun _ _ hr =>
      let hq := hr.1; ⟨hq.1.1, hq.1.2.1, hq.1.2.2.1, ?_,
      hq.1.2.2.2.2.1, indexHolds_append (indexHolds_append (indexHolds_append hq.1.2.2.2.2.2 hq.2.1) ?_) hr.2⟩)
      (IndexWrites.regionAtoms_holds he hk hh hρ (IndexWrites.literalArrayAtoms_holds he hk hh hs))
    · split
      · exact hr.1.1.2.2.2.1
      · have hp := hr.1.2.2
        simp only [*, Bool.false_eq_true, ite_false] at hp
        exact hp.1
    · split
      · exact HeapKnowledge.indexHolds_nil _ _
      · have hp := hr.1.2.2
        simp only [*, Bool.false_eq_true, ite_false] at hp
        exact hp.2
  normal := base.normal
  normal_sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hn
    simp only [CheckResult.map, Option.map_eq_some_iff] at hc
    obtain ⟨out0, hrun, -⟩ := hc
    exact base.normal_sound hrun hcodes hsums he hk hw hh href hn

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
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hρ
    simp only [CheckResult.map, Option.map_eq_some_iff] at hc
    obtain ⟨out0, hrun, rfl⟩ := hc
    have hs := base.emptyArrays.sound hrun hcodes hsums he hk hw hh href hρ
    exact weaken (fun h' u hq => ⟨hq.1.1.1.1, hq.1.1.1.2.1, hq.1.1.1.2.2.1, hq.1.1.1.2.2.2.1, hq.1.1.1.2.2.2.2.1,
      indexHolds_append hq.1.1.1.2.2.2.2.2 (indexHolds_append (indexHolds_append hq.1.1.2 hq.1.2) hq.2)⟩)
      (IndexWrites.lengthAtoms_holds he hk (IndexWrites.linearAtoms_holds he hk (IndexWrites.stepAtoms_holds he hk hs)))
  normal := base.emptyArrays.normal
  normal_sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hn
    simp only [CheckResult.map, Option.map_eq_some_iff] at hc
    obtain ⟨out0, hrun, -⟩ := hc
    exact base.emptyArrays.normal_sound hrun hcodes hsums he hk hw hh href hn

/-- A checker whose `boundedWrite` steps are writes at a checked index
(`IndexWrites.boundedWriteCheck`, `setElem-bounded`), keeping the cell facts
the written value and an array spine meet (`IndexWrites.writtenCells`,
`weak-update`), and whose element writes
at any index keep the atoms a growing change keeps (`IndexWrites.growOutput`);
every other step is `base`'s. -/
@[nospecialize] def Checker.boundedWrites [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums => match e with
    | .boundedWrite a i v p =>
      if IndexWrites.boundedWriteCheck G images j k a i v p then
        pure (IndexWrites.withLinks (IndexWrites.withCells (IndexWrites.withWritten (if IndexWrites.keepsLengths G j k a i then IndexWrites.lengthOutput (stableFirst G j.context) k
          else IndexWrites.growOutput G j k (ordinaryOutput k))
          (IndexWrites.writeAtoms G j.context k a ++ IndexWrites.writeFrameAtoms (stableFirst G j.context) k a ++
            IndexWrites.atLengthAtoms G j k a i ++ IndexWrites.denseAppendAtoms G j.context k a i v))
          (IndexWrites.writtenCells k (valuesAt G j.context k v)))
          (IndexWrites.writeFrameLinks (stableFirst G j.context) k a))
      else failure
    | _ => (base.run j k e codes sums).map (IndexWrites.growOutput G j k)
  select := fun j k e codes sums => match e with
    | .boundedWrite a i v p =>
      if IndexWrites.boundedWriteCheck G images j k a i v p then
        pure (IndexWrites.withLinks (IndexWrites.withCells (IndexWrites.withWritten (if IndexWrites.keepsLengths G j k a i then IndexWrites.lengthOutput (stableFirst G j.context) k
          else IndexWrites.growOutput G j k (ordinaryOutput k))
          (IndexWrites.writeAtoms G j.context k a ++ IndexWrites.writeFrameAtoms (stableFirst G j.context) k a ++
            IndexWrites.atLengthAtoms G j k a i ++ IndexWrites.denseAppendAtoms G j.context k a i v))
          (IndexWrites.writtenCells k (valuesAt G j.context k v)))
          (IndexWrites.writeFrameLinks (stableFirst G j.context) k a))
      else failure
    | _ => (base.select j k e codes sums).map (IndexWrites.growOutput G j k)
  sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hρ
    split at hc
    · split at hc
      · rename_i hck
        cases hc
        have hfr := IndexWrites.boundedWriteFrame_sound hck he hk hw hh href hρ
        apply IndexWrites.withLinks_sound (weaken (fun _ _ hq => hq.2) hfr)
        apply IndexWrites.withCells_sound (IndexWrites.boundedCells_sound hck he hk hw hh href)
        apply IndexWrites.withWritten_sound
          (weaken (fun _ _ hq => indexHolds_append (indexHolds_append (indexHolds_append hq.1.1.1 hq.1.1.2) hq.1.2) hq.2)
            (IndexWrites.safePost_and
              (IndexWrites.safePost_and
                (IndexWrites.safePost_and (IndexWrites.boundedRegions_sound hck he hk hw hh href hρ)
                  (weaken (fun _ _ hq => hq.1) hfr))
                (IndexWrites.atLengthAtoms_sound hck he hk hw hh href))
              (IndexWrites.denseAppendAtoms_sound hck he hk hw hh href hρ)))
        split
        · rename_i hkeep
          exact IndexWrites.boundedLength_sound hck hkeep he hk hw hh href
        · exact IndexWrites.growOutput_sound he hk hw hh (IndexWrites.boundedWrite_sound hck he hk hw hh href)
      · cases hc
    · simp only [CheckResult.map, Option.map_eq_some_iff] at hc
      obtain ⟨out0, hrun, rfl⟩ := hc
      exact IndexWrites.growOutput_sound he hk hw hh (base.sound hrun hcodes hsums he hk hw hh href hρ)
  normal := fun j k e codes sums => match e with
    | .boundedWrite .. => .top
    | _ => base.normal j k e codes sums
  normal_sound := by
    intro j k e out codes sums hc hcodes hsums ε ρ n W h he hk hw hh href hn
    cases e with
    | boundedWrite => exact absurd hn Footprints.Closed.top_ne_empty
    | _ =>
      dsimp only at hc hn
      simp only [CheckResult.map, Option.map_eq_some_iff] at hc
      obtain ⟨out0, hrun, -⟩ := hc
      exact base.normal_sound hrun hcodes hsums he hk hw hh href hn

end Verification.HeapExpressionRules
