import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Verification.Semantics.FootprintProvenance
import Verification.Semantics.HeapFacts
import Verification.Types.PositiveNormalization

/-! Controls for the footprint lemmas: each counterexample a design review
found against an earlier statement, run against the decision procedures or
stated as a theorem, and the axiom check of the lemmas themselves, which
nothing in the acceptance path uses yet. -/
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

#guard postB Φelems arr0 h₀ h₁
#guard postB Φelems arr0 h₁ h₂
#guard !postB Φelems arr0 h₀ h₂
#guard postB (Φelems ++ transportAll elemsValue Φelems) arr0 h₀ h₂

/-! ## Inclusion needs evidence valid at the entry heap

At `h` the field holds a value, at `h₀` a store. Class evidence that holds
at `h` justifies the inclusion of `Φp` in `Φq`, and the composed claim
fails; the same evidence fails at `h₀`, where `Post.compose` requires it. -/

private def fieldK : Env := fun i => if i = 0 then .objAt [("k", 0)] .absent 9 else .undef
private def g₀ : Heap := [.arr []]
private def g : Heap := [.nul]
private def Φp : Footprint := [(.field 0 "k", .any)]
private def Φq : Footprint := [(.cls .value, .any)]
private def valueK : ClassEvidence := fun x k => if x = 0 ∧ k = "k" then some .value else none

#guard postB Φp fieldK g₀ g
#guard postB [] fieldK g g
#guard !postB Φq fieldK g₀ g
#guard Footprint.le valueK (Φp ++ transportAll ⟨fun _ => false, fun _ => false⟩ []) Φq
#guard classOkB valueK fieldK g [0] ["k"]
#guard !classOkB valueK fieldK g₀ [0] ["k"]

/-! ## Freshness of a store says nothing of its elements

Slot 0's own location is 5, at least mark 1; slot 1's typed field `f` is
location 1, below mark 1. The store at 5 lists location 1. So slot 0's own
locations are apart from slot 1's typed field, and its listed elements are
not. -/

private def apart : Env := fun i =>
  if i = 0 then .objAt [(arrayStoreKey, 5)] .absent 9
  else if i = 1 then .objAt [("f", 1)] .absent 9 else .undef
private def heap5 : Heap := [.nul, .nul, .nul, .nul, .nul, .arr [some 1]]

#guard (Region.own 0).mem apart heap5 5 && !(Region.own 0).mem apart heap5 1
#guard (Region.field 1 "f").mem apart heap5 1
#guard (Region.elems 0).mem apart heap5 1

/-! ## Mark maps

Source stamps: `after 0 = 1`, `before 1 = 2`, with marks `0, 5, 10`; one
location may be in both regions (7). A target that merges marks 1 and 2
would make the regions apart; every way to state it is refused, as are a
reordering and a moved mark 0. -/

private def source : Stamps := ⟨fun x => if x = 0 then some 1 else none, fun y => if y = 1 then some 2 else none⟩
private def merged : Stamps := ⟨fun x => if x = 0 then some 1 else none, fun y => if y = 1 then some 1 else none⟩
private def typedF : Nat → List PropKey := fun y => if y = 1 then ["f"] else []

#guard stampEdgeOk ⟨[0, 1, 2], id⟩ source source typedF typedF [0, 1]
#guard !stampEdgeOk ⟨[0, 1], id⟩ source merged typedF typedF [0, 1]
#guard !stampEdgeOk ⟨[0, 2], id⟩ source merged typedF typedF [0, 1]
#guard !stampEdgeOk ⟨[0, 2, 1], id⟩ source source typedF typedF [0, 1]
#guard !stampEdgeOk ⟨[1, 1, 2], id⟩ source source typedF typedF [0, 1]
-- weakening in the right direction is admitted: `after` to an earlier mark, `before` to a later one
#guard stampEdgeOk ⟨[0, 1, 2], id⟩ source ⟨fun x => if x = 0 then some 0 else none, source.before⟩ typedF typedF [0, 1]

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

/-! ## The lemmas rest on the standard axioms -/

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``Post.compose, ``transport_sound, ``Post.mono, ``Post.empty_iff, ``Post.all_iff,
      ``postB_iff, ``stamps_transport, ``stamps_separate, ``MarksOk.rename, ``MarksOk.push,
      ``alloc_after, ``typed_below, ``before_of_typed, ``contract_class, ``contract_store,
      ``contract_class_entry, ``dense_class, ``dense_stable, ``stableDenseClosed_sound,
      ``elems_class, ``elems_class_needs_two_levels] do
    let used ← liftCoreM <| collectAxioms name
    for axiom_ in used do
      unless standard.contains axiom_ do
        throwError "{name} depends on the axiom {axiom_}"

end Verification.Footprints.Controls
