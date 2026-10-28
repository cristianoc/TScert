import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Verification.Semantics.FootprintProvenance
import Verification.Semantics.ClosedFootprints
import Verification.Semantics.FootprintNatives
import Verification.Semantics.HeapFacts
import Verification.Types.PositiveNormalization

/-! Controls for the footprint lemmas. Each counterexample a design review
found against an earlier statement is a theorem refuting that statement, so a
definition changed back to the false form fails here. The file ends with the
axiom check of every footprint theorem. The acceptance path uses the
closed-footprint theorems (their composition, `Closed.Holds.trans`, and order,
through `GraphCode.goto_bounded` and `checkJson_safe`), whose axioms
`AxiomCheck.lean` also checks. -/
namespace Verification.Footprints.Controls

/-- Slot 0 holds an array whose store is location 0. -/
private def arr0 : Env := fun i => if i = 0 then .objAt [(arrayStoreKey, 0)] .absent 9 else .undef

/-! ## Union is not composition

`Φ` changes `x`'s store and its listed elements. Location 2 is listed only
after the first step, so `Φ` read at `h₀` does not cover the second step's
write. Transporting `elems` to `class(value)` does. -/

private def Φelems : Footprint := [(.field 0 arrayStoreKey, .any), (.elems 0, .any)]
private def h₀ : Heap := [.arr [some 1], .nul, .nul]
private def h₁ : Heap := [.arr [some 2], .nul, .nul]
private def h₂ : Heap := [.arr [some 2], .nul, .tru]
private def elemsValue : TransportEvidence := ⟨fun _ => false, fun x => x == 0⟩

#guard postB (Φelems ++ transportAll elemsValue Φelems) arr0 h₀ h₂

/-- The two-step rule without transport is false. -/
theorem union_composition_false :
    ¬ ∀ (Φ : Footprint) (ρ : Env) (a b c : Heap), Post Φ ρ a b → Post Φ ρ b c → Post Φ ρ a c := by
  intro H
  have h := H Φelems arr0 h₀ h₁ h₂ (postB_iff.mp (by decide)) (postB_iff.mp (by decide))
  exact absurd (postB_iff.mpr h) (by decide)

/-! ## Inclusion needs evidence valid at the entry heap

At `g` the field holds a value, at `g₀` a store. Class evidence true at `g`
justifies the inclusion of `Φp` in `Φq`, and the composed claim fails. -/

private def fieldK : Env := fun i => if i = 0 then .objAt [("k", 0)] .absent 9 else .undef
private def g₀ : Heap := [.arr []]
private def g : Heap := [.nul]
private def Φp : Footprint := [(.field 0 "k", .any)]
private def Φq : Footprint := [(.cls .value, .any)]
private def valueK : ClassEvidence := fun x k => if x = 0 ∧ k = "k" then some .value else none

theorem valueK_ok_current : ClassOk valueK fieldK g := by
  intro x k c l hc hl _
  simp only [valueK] at hc
  split at hc
  · rename_i hxk
    obtain ⟨rfl, rfl⟩ := hxk
    cases hc
    simp [fieldK, fieldsOf] at hl
    subst hl
    decide
  · cases hc

theorem valueK_fails_entry : ¬ ClassOk valueK fieldK g₀ := by
  intro h
  have := h 0 "k" .value 0 (by simp [valueK]) (by simp [fieldK, fieldsOf]) (by decide)
  exact absurd this (by decide)

/-- Composition with class evidence valid at the current heap, instead of the
entry heap, is false. -/
theorem current_heap_compose_false :
    ¬ ∀ (Φp Φn Φq : Footprint) (cl : ClassEvidence) (ρ : Env) (a b c : Heap) (ev : TransportEvidence),
      Post Φp ρ a b → Post Φn ρ b c → FreshOk ev.fresh ρ a.length → ElemsValueOk ev.elemsValue ρ b →
      Footprint.le cl (Φp ++ transportAll ev Φn) Φq = true → ClassOk cl ρ b → Post Φq ρ a c := by
  intro H
  have h := H Φp [] Φq valueK fieldK g₀ g g ⟨fun _ => false, fun _ => false⟩
    (postB_iff.mp (by decide)) (Post.refl _ _ _) (fun _ h => by cases h)
    (fun _ h => by cases h) (by decide) valueK_ok_current
  exact absurd (postB_iff.mpr h) (by decide)

/-- `Post.compose` itself cannot be applied to the witness: applied with any
class evidence that justifies the inclusion and holds at the entry heap, it
would give the false postcondition. So no such evidence exists, while
evidence holding at the current heap does (`valueK_ok_current`). -/
theorem compose_needs_entry_evidence :
    ¬ ∃ cl, Footprint.le cl (Φp ++ transportAll ⟨fun _ => false, fun _ => false⟩ []) Φq = true ∧
      ClassOk cl fieldK g₀ := by
  rintro ⟨cl, hle, hc⟩
  have h := Post.compose (Φn := []) (h := g) (h' := g) (postB_iff.mp (by decide)) (Post.refl _ _ _)
    (fun _ h => by cases h) (fun _ h => by cases h) hle hc
  exact absurd (postB_iff.mpr h) (by decide)

/-! ## Freshness of a store says nothing of its elements

Slot 0's own location is 5, at least mark 1; slot 1's typed field `f` is
location 1, below mark 1. The store at 5 lists location 1. -/

private def apart : Env := fun i =>
  if i = 0 then .objAt [(arrayStoreKey, 5)] .absent 9
  else if i = 1 then .objAt [("f", 1)] .absent 9 else .undef
private def heap5 : Heap := [.nul, .nul, .nul, .nul, .nul, .arr [some 1]]
private def apartStamps : Stamps :=
  ⟨fun x => if x = 0 then some 1 else none, fun y => if y = 1 then some 1 else none⟩
private def typedF : Nat → List PropKey := fun y => if y = 1 then ["f"] else []
private def μ5 : Nat → Nat := fun i => if i = 0 then 0 else 5

theorem apart_stamps_hold : StampsHold apartStamps typedF μ5 apart := by
  refine ⟨fun x m ha l hl => ?_, fun y m hb k hk l hl => ?_⟩
  · simp only [apartStamps] at ha
    split at ha
    · rename_i hx; subst hx; cases ha
      simp [apart, fieldsOf] at hl; subst hl; decide
    · cases ha
  · simp only [apartStamps] at hb
    split at hb
    · rename_i hy; subst hy; cases hb
      simp [typedF] at hk; subst hk
      simp [apart, fieldsOf] at hl; subst hl; decide
    · cases hb

/-- Separation by `after` of every region rooted at a slot, its listed
elements included, is false. -/
theorem elems_separation_false :
    ¬ ∀ (st : Stamps) (typed : Nat → List PropKey) (μ : Nat → Nat) (ρ : Env) (h : Heap)
        (x y m m' l : Nat) (k : PropKey) (l' : Nat),
      StampsHold st typed μ ρ → (∀ i j, i ≤ j → μ i ≤ μ j) → st.after x = some m →
      st.before y = some m' → m' ≤ m → (Region.elems x).mem ρ h l = true → k ∈ typed y →
      (fieldsOf (ρ y)).lookup k = some l' → l ≠ l' := by
  intro H
  exact H apartStamps typedF μ5 apart heap5 0 1 1 1 1 "f" 1 apart_stamps_hold
    (fun i j hij => by simp only [μ5]; split <;> split <;> omega) rfl rfl (Nat.le_refl _)
    (by decide) (by simp [typedF]) (by simp [apart, fieldsOf]) rfl

/-- The separation checker, on these stamps: it separates slot 0's own
locations from slot 1's typed field, and refuses to separate slot 0's listed
elements from it. -/
private def apartK : SepKnowledge := ⟨fun _ _ => none, apartStamps, typedF, []⟩

#guard apartK.apart (.own 0) (.field 1 "f")
#guard apartK.apart (.field 0 arrayStoreKey) (.field 1 "f")
#guard !apartK.apart (.elems 0) (.field 1 "f")

/-- `stamps_separate`'s region premise must exclude `elems`: on the witness,
slot 0's listed element and slot 1's typed field are one location, so the
theorem's conclusion fails there; were its premise to admit `elems 0`, this
would prove `False`. -/
theorem stamps_separate_excludes_elems
    (hr : (∃ k, Region.elems 0 = Region.field 0 k) ∨ Region.elems 0 = Region.own 0) : False :=
  stamps_separate (x := 0) (y := 1) (m := 1) (m' := 1) (r := .elems 0) (h := heap5) (l := 1) (k := "f")
    (l' := 1) apart_stamps_hold
    (fun i j hij => by simp only [μ5]; split <;> split <;> omega) rfl rfl (Nat.le_refl _) hr
    (by decide) (by simp [typedF]) (by simp [apart, fieldsOf]) rfl

/-! ## Mark maps

Source stamps: `after 0 = 1`, `before 1 = 2`, with marks `0, 5, 10`, and
location 7 both an own location of slot 0 and slot 1's typed field. A target
merging marks 1 and 2 would make them apart. The check refuses every way to
state it, as it refuses a reordering and a moved mark 0, and each merge it
refuses is false. -/

private def source : Stamps := ⟨fun x => if x = 0 then some 1 else none, fun y => if y = 1 then some 2 else none⟩
private def merged : Stamps := ⟨fun x => if x = 0 then some 1 else none, fun y => if y = 1 then some 1 else none⟩

#guard stampEdgeOk ⟨[0, 1, 2], id⟩ source source typedF typedF [0, 1]
#guard !stampEdgeOk ⟨[0, 1], id⟩ source merged typedF typedF [0, 1]
#guard !stampEdgeOk ⟨[0, 2], id⟩ source merged typedF typedF [0, 1]
#guard !stampEdgeOk ⟨[0, 2, 1], id⟩ source source typedF typedF [0, 1]
#guard !stampEdgeOk ⟨[1, 1, 2], id⟩ source source typedF typedF [0, 1]
-- weakening in its own direction is admitted: `after` to an earlier mark, `before` to a later one
#guard stampEdgeOk ⟨[0, 1, 2], id⟩ source ⟨fun x => if x = 0 then some 0 else none, source.before⟩ typedF typedF [0, 1]

private def μ0510 : Nat → Nat := fun i => if i = 0 then 0 else if i = 1 then 5 else 10
private def shared7 : Env := fun i =>
  if i = 0 then .objAt [("g", 7)] .absent 9 else if i = 1 then .objAt [("f", 7)] .absent 9 else .undef

theorem merged_marks_unsound :
    StampsHold source typedF μ0510 shared7 ∧
      ¬ StampsHold merged typedF (fun i => μ0510 (markAt [0, 1] i)) shared7 ∧
      ¬ StampsHold merged typedF (fun i => μ0510 (markAt [0, 2] i)) shared7 := by
  refine ⟨⟨fun x m ha l hl => ?_, fun y m hb k hk l hl => ?_⟩, fun h => ?_, fun h => ?_⟩
  · simp only [source] at ha
    split at ha
    · rename_i hx; subst hx; cases ha
      simp [shared7, fieldsOf] at hl; subst hl; decide
    · cases ha
  · simp only [source] at hb
    split at hb
    · rename_i hy; subst hy; cases hb
      simp [typedF] at hk; subst hk
      simp [shared7, fieldsOf] at hl; subst hl; decide
    · cases hb
  · have := h.2 1 1 rfl "f" (by simp [typedF]) 7 (by simp [shared7, fieldsOf])
    exact absurd this (by decide)
  · have := h.1 0 1 rfl 7 (by simp [shared7, fieldsOf])
    exact absurd this (by decide)

/-! ## Density depends on its store alone

Every slot names store location 0. Location 1 shrinks; every region that
covers it also covers location 0, so no footprint keeping location 0 within
`grow` states the change, and density survives it. -/

private def store0 : Env := fun _ => .objAt [(arrayStoreKey, 0)] .absent 9

theorem dense_survives_outside_support :
    Dense 0 1 store0 [.arr [some 2], .arr [some 2], .nul] ∧
      Dense 0 1 store0 [.arr [some 2], .arr [], .nul] := by
  have hd : Dense 0 1 store0 [.arr [some 2], .arr [some 2], .nul] :=
    ⟨0, [some 2], by simp [store0, fieldsOf], rfl,
      ⟨by simp, fun i hi => by cases i with | zero => simp | succ i => omega⟩⟩
  refine ⟨hd, dense_support hd fun e he l v hm hv => ?_⟩
  simp only [List.mem_singleton] at he
  subst he
  simp only [Region.mem, store0, fieldsOf, List.lookup, beq_self_eq_true, beq_iff_eq,
    Option.some.injEq] at hm
  subst hm
  exact ⟨v, by simpa using hv, Change.Holds.refl _ _ _⟩

/-! ## Classes need contracts -/

/-- `nonNull` holds of a store: a `cell` fact alone gives no class. -/
theorem nonNull_admits_store : HeapFacts.Atom.holds .nonNull (.arr []) := by
  simp [HeapFacts.Atom.holds, isVal]

/-- A source value may name any location, one the heap does not have
included: `before` comes only from typed fields. -/
theorem source_names_any_location (n : Nat) (W : WorldT n) :
    PositiveNormalization.sourceT n W (.objAt [("f", 100)] .absent 0) ∧
      ¬ 100 < ([] : Heap).length := by
  refine ⟨⟨rfl, ?_⟩, by simp⟩
  simp [Scoped]

/-- The array of numbers, whose element family admits only source values. -/
private def numbers : TupleF :=
  { required := [], optional := [], rest := some (fun _ _ v => ∃ b, v = .num b), presence := .readable }

private def storeC : Ctr 1 := fun j _ U v => listT numbers j U v
private def anyC : Ctr 1 := fun _ _ _ _ => True

/-- **One level is not enough** for an element's class: at level 1 a number
array's store contract holds while its element location holds a store. -/
theorem elems_class_needs_two_levels :
    ∃ (W : WorldT 1) (h : Heap), HeapOk 1 W h ∧ lookup W 0 = some storeC ∧
      h[0]? = some (.arr [some 1]) ∧ h[1]? = some (.arr []) := by
  refine ⟨ofList [storeC, anyC], [.arr [some 1], .arr []], ⟨by simp, ?_⟩, by simp [lookup], rfl, rfl⟩
  intro l c hl
  simp only [lookup, toList_ofList] at hl
  match l, hl with
  | 0, hl =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    refine ⟨_, rfl, fun j hj => ?_⟩
    have hj0 : j = 0 := by omega
    subst hj0
    refine ⟨[some 1], rfl, fun j hj => absurd hj (Nat.not_lt_zero _), by simp [numbers],
      fun h => by simp [numbers] at h, fun i A hA => by simp [numbers] at hA,
      fun i A l hA => by simp [numbers] at hA, fun i l _ hl => ?_⟩
    have hi : i = 0 := by
      cases i with
      | zero => rfl
      | succ i => simp at hl
    subst hi
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    exact ⟨_, _, rfl, lookup_trunc (Nat.zero_le 1) _ 1 anyC (by simp [lookup]),
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | 1, hl =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    exact ⟨_, rfl, fun _ _ => trivial⟩
  | l + 2, hl => simp at hl

/-! ## The stability check

A cell fact about `x.k` survives a write to `class(value)` only where the
field's class is known to be another one, and never a write to the field
itself. -/

private def noKnowledge : SepKnowledge := ⟨fun _ _ => none, ⟨fun _ => none, fun _ => none⟩, fun _ => [], []⟩
private def storeK : SepKnowledge := { noKnowledge with cl := fun x k => if x = 0 ∧ k = "k" then some .store else none }
private def cellK : FactKind := .cell ⟨0, { nul := true }, "k"⟩

#guard !stable noKnowledge cellK.support [(.cls .value, .any)]
#guard stable storeK cellK.support [(.cls .value, .any)]
#guard !stable storeK cellK.support [(.field 0 "k", .any)]
#guard stable storeK cellK.support [(.field 0 "k", .keep)]

/-! ## Array mutators

The removing mutators break a dense prefix: `pop` and `shift` of a dense
array, `reverse` of one with a trailing hole, and a shorter length. The
growing ones keep it, `reverse` of a fully dense array too, which the
footprint of `reverse` does not claim. -/

private def grows (a : Arr) (f : Arr → Arr) : Bool := Change.grow.holdsB a.next (.arr a.ls) (.arr (f a).ls)

#guard !grows ⟨[some 0], 1⟩ Arr.pop
#guard !grows ⟨[some 0, some 1], 2⟩ Arr.shift
#guard !grows ⟨[some 0, none], 1⟩ Arr.reverse
#guard !grows ⟨[some 0], 1⟩ (·.setLength 0)
#guard grows ⟨[some 0, some 1], 2⟩ Arr.reverse
#guard grows ⟨[some 0, none, some 2], 3⟩ Arr.push
#guard grows ⟨[some 0, none, some 2], 3⟩ Arr.unshift
#guard grows ⟨[some 0, none], 2⟩ (·.setLength 4)
-- `unshift` ends by setting the length: [1, hole] becomes [9, 1, hole]
#guard (Arr.unshift ⟨[some 0, none], 2⟩).ls.length == 3
#guard present (Arr.unshift ⟨[some 0, none], 2⟩).ls 0 && present (Arr.unshift ⟨[some 0, none], 2⟩).ls 1
#guard !present (Arr.unshift ⟨[some 0, none], 2⟩).ls 2
#guard grows ⟨[some 0, none], 2⟩ Arr.unshift
-- sort's writeback, judged from the entry store, after a comparator that removed both indices
#guard Change.grow.holdsB 2 (.arr [some 0, some 1])
  (.arr ((Arr.mk [] 2).writeback (itemCount [some 0, some 1] 2) 2).ls)
-- and the step from the comparator's store is no `grow` of the entry store's prefix after a
-- comparator that filled a hole the writeback deletes: [3, 1, hole, 2] sorted keeps 3 values
#guard !present ((Arr.mk [some 0, some 1, some 5, some 3] 6).writeback
  (itemCount [some 0, some 1, none, some 3] 4) 4).ls 3

/-! ## The lemmas rest on the standard axioms

Every theorem of the `Footprints` namespace, these controls included. -/

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .thmInfo _ => if (`Verification.Footprints).isPrefixOf n then acc.push n else acc
    | _ => acc
  if names.size < 50 then
    throwError "the footprint axiom check found only {names.size} theorems"
  for name in names do
    let used ← liftCoreM <| collectAxioms name
    for axiom_ in used do
      unless standard.contains axiom_ do
        throwError "{name} depends on the axiom {axiom_}"

end Verification.Footprints.Controls
