import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Verification.Semantics.FootprintProvenance
import Verification.Semantics.ClosedFootprints
import Verification.Semantics.FootprintRebase
import Verification.Semantics.FootprintNatives
import Verification.Semantics.HeapFacts
import Verification.Types.PositiveNormalization

/-! Controls for the footprint lemmas. Each counterexample a design review
found against an earlier statement is a theorem refuting that statement, so a
definition changed back to the false form fails here. The file ends with the
axiom check of every footprint theorem. The acceptance path uses the
closed-footprint theorems (their composition below a cutoff,
`Closed.Holds.trans_on`, and their order, `Closed.Holds.mono`, through
`GraphCode.goto_bounded`), whose axioms
`AxiomCheck.lean` also checks. -/
namespace Verification.Footprints.Controls

/-- Slot 0 holds an array whose spine is location 0. -/
private def arr0 : Env := fun i => if i = 0 then .objAt [(arraySpineKey, 0)] .absent 9 else .undef

/-! ## Union is not composition

`Φ` changes `x`'s spine and its listed elements. Location 2 is listed only
after the first step, so `Φ` read at `h₀` does not cover the second step's
write. Rebasing the second step's `cells` to the entry (`all`) does. -/

private def Φcells : Footprint := [(.field 0 arraySpineKey, .any), (.cells 0, .any)]
private def h₀ : Heap := [.arr [some 1], .nul, .nul]
private def h₁ : Heap := [.arr [some 2], .nul, .nul]
private def h₂ : Heap := [.arr [some 2], .nul, .tru]
/-- The step's slot 0 is the entry's slot 0. -/
private def sameSlots : RebaseEvidence := { link := fun s => some (s, []), agree := fun _ _ => false }

#guard postB (Φcells ++ rebaseAll sameSlots Φcells) arr0 h₀ h₂

/-- The two-step rule without rebasing is false. -/
theorem union_composition_false :
    ¬ ∀ (Φ : Footprint) (ρ : Env) (a b c : Heap), Post Φ ρ a b → Post Φ ρ b c → Post Φ ρ a c := by
  intro H
  have h := H Φcells arr0 h₀ h₁ h₂ (postB_iff.mp (by decide)) (postB_iff.mp (by decide))
  exact absurd (postB_iff.mpr h) (by decide)

/-! ## Inclusion needs evidence valid at the entry heap

At `g` the field holds a value, at `g₀` a spine. Class evidence true at `g`
justifies the inclusion of `Φp` in `Φq`, and the composed claim fails. -/

private def fieldK : Env := fun i => if i = 0 then .objAt [("k", 0)] .absent 9 else .undef
private def g₀ : Heap := [.arr []]
private def g : Heap := [.nul]
private def Φp : Footprint := [(.field 0 "k", .any)]
private def Φq : Footprint := [(.cls .values, .any)]
private def valueK : ClassEvidence := fieldClass 0 "k" .values
/-- Rebasing evidence stating nothing. -/
private def noLinks : RebaseEvidence := { link := fun _ => none, agree := fun _ _ => false }

/-- `g = [.nul]` satisfies the intrinsic categories at `fieldK`: location 0
holds `null` (a value), and `"k"` is a non-spine field. -/
private theorem g_categories : ClassOk intrinsicClasses fieldK g := by
  intro r c l hc hm hl
  cases hc
  have hl0 : l = 0 := by simp [g] at hl; omega
  subst hl0
  cases r with
  | field x k =>
    by_cases hx : x = 0
    · subst hx
      by_cases hk : k = "k"
      · subst hk; decide
      · have hne : (k == "k") = false := beq_eq_false_iff_ne.mpr hk
        simp [Region.mem, fieldK, fieldsOf, List.lookup, hne] at hm
    · simp [Region.mem, fieldK, hx, fieldsOf] at hm
  | fields x =>
    simp [Region.mem, Region.cats, g, Selector.selects, contentsCategory, Selector.has]
  | cells x =>
    simp [Region.mem, Region.cats, g, Selector.selects, contentsCategory, Selector.has]
  | cls s => exact hm
  | all => simp [Region.mem, Region.cats, g, Selector.selects, contentsCategory, Selector.has]
  | path x p k =>
    cases p with
    | nil =>
      by_cases hx : x = 0
      · subst hx
        by_cases hk : k = "k"
        · subst hk; decide
        · have hne : (k == "k") = false := beq_eq_false_iff_ne.mpr hk
          simp [Region.mem, HeapKnowledge.readPath, fieldK, fieldsOf, List.lookup, hne] at hm
      · simp [Region.mem, HeapKnowledge.readPath, fieldK, hx, fieldsOf] at hm
    | cons f p =>
      by_cases hx : x = 0
      · subst hx
        simp only [Region.mem, HeapKnowledge.readPath, fieldK, ite_true] at hm
        cases hfk : ([("k", 0)] : List (PropKey × Nat)).lookup (.str f) with
        | none => simp [hfk] at hm
        | some l' =>
          have hl' : l' = 0 := by
            simp only [List.lookup] at hfk
            split at hfk <;> simp_all
          subst hl'
          cases p with
          | nil => simp [hfk, g, HeapKnowledge.readPath, fieldsOf] at hm
          | cons _ _ => simp [hfk, g, HeapKnowledge.readPath] at hm
      · simp [Region.mem, HeapKnowledge.readPath, fieldK, hx] at hm
  | pathFields x p =>
    simp [Region.mem, Region.cats, g, Selector.selects, contentsCategory, Selector.has]
  | pathCells x p =>
    simp [Region.mem, Region.cats, g, Selector.selects, contentsCategory, Selector.has]
  | spine x p =>
    cases p with
    | nil =>
      by_cases hx : x = 0
      · subst hx; exact absurd hm (by decide)
      · simp [Region.mem, HeapKnowledge.readPath, fieldK, hx, HeapKnowledge.elementsOf] at hm
    | cons f p =>
      by_cases hx : x = 0
      · subst hx
        simp only [Region.mem, HeapKnowledge.readPath, fieldK, ite_true] at hm
        cases hfk : ([("k", 0)] : List (PropKey × Nat)).lookup (.str f) with
        | none => simp [hfk] at hm
        | some l' =>
          have hl' : l' = 0 := by
            simp only [List.lookup] at hfk
            split at hfk <;> simp_all
          subst hl'
          cases p <;> simp [hfk, g, HeapKnowledge.readPath, HeapKnowledge.elementsOf] at hm
      · simp [Region.mem, HeapKnowledge.readPath, fieldK, hx] at hm
  | elemSpines x p =>
    cases p with
    | nil =>
      by_cases hx : x = 0
      · subst hx; exact absurd hm (by decide)
      · simp [Region.mem, HeapKnowledge.readPath, fieldK, hx, spineCells, fieldsOf, entriesAt, HeapKnowledge.descriptorSpine] at hm
    | cons f p =>
      by_cases hx : x = 0
      · subst hx
        simp only [Region.mem, HeapKnowledge.readPath, fieldK, ite_true] at hm
        cases hfk : ([("k", 0)] : List (PropKey × Nat)).lookup (.str f) with
        | none => simp [hfk] at hm
        | some l' =>
          have hl' : l' = 0 := by
            simp only [List.lookup] at hfk
            split at hfk <;> simp_all
          subst hl'
          cases p <;> simp [hfk, g, HeapKnowledge.readPath, spineCells, fieldsOf, entriesAt, HeapKnowledge.descriptorSpine] at hm
      · simp [Region.mem, HeapKnowledge.readPath, fieldK, hx] at hm

private theorem noLinks_ok (ρ₀ : Env) (a : Heap) : RebaseOk noLinks fieldK ρ₀ a g where
  link := by intro _ _ _ h; simp [noLinks] at h
  agree := by intro _ _ h; simp [noLinks] at h
  fresh := by intro _ _ h; exact absurd h (by simp [noLinks])
  categories := g_categories

theorem valueK_ok_current : ClassOk valueK fieldK g := by
  intro r c l hc hm _
  cases r <;> simp only [valueK, fieldClass] at hc
  case field x k =>
    split at hc
    · rename_i hxk
      obtain ⟨rfl, rfl⟩ := hxk
      cases hc
      simp [Region.mem, fieldK, fieldsOf] at hm
      subst hm
      decide
    · cases hc
  all_goals cases hc

theorem valueK_fails_entry : ¬ ClassOk valueK fieldK g₀ := by
  intro h
  have := h (.field 0 "k") .values 0 (by simp [valueK, fieldClass]) (by simp [Region.mem, fieldK, fieldsOf]) (by decide)
  exact absurd this (by decide)

/-- Composition with class evidence valid at the current heap, instead of the
entry heap, is false. -/
theorem current_heap_compose_false :
    ¬ ∀ (Φp Ψ Φq : Footprint) (cl : ClassEvidence) (ρ₀ σ : Env) (a b c : Heap) (ev : RebaseEvidence),
      Post Φp ρ₀ a b → Post Ψ σ b c → RebaseOk ev σ ρ₀ a b →
      Footprint.le cl (Φp ++ rebaseAll ev Ψ) Φq = true → ClassOk cl ρ₀ b → Post Φq ρ₀ a c := by
  intro H
  have h := H Φp [] Φq valueK fieldK fieldK g₀ g g noLinks
    (postB_iff.mp (by decide)) (Post.refl _ _ _)
    (noLinks_ok _ _) (by decide) valueK_ok_current
  exact absurd (postB_iff.mpr h) (by decide)

/-- `Post.compose_at` itself cannot be applied to the witness: applied with
any class evidence that justifies the inclusion and holds at the entry heap,
it would give the false postcondition. So no such evidence exists, while
evidence holding at the current heap does (`valueK_ok_current`). -/
theorem compose_needs_entry_evidence :
    ¬ ∃ cl, Footprint.le cl (Φp ++ rebaseAll noLinks []) Φq = true ∧ ClassOk cl fieldK g₀ := by
  rintro ⟨cl, hle, hc⟩
  have h := Post.compose_at (Ψ := []) (σ := fieldK) (h := g) (h' := g) (postB_iff.mp (by decide))
    (Post.refl _ _ _)
    (noLinks_ok _ _) hle hc
  exact absurd (postB_iff.mpr h) (by decide)

/-! ## Freshness of a spine says nothing of its elements

Slot 0's own location is 5, at least mark 1; slot 1's typed field `f` is
location 1, below mark 1. The spine at 5 lists location 1. -/

private def apart : Env := fun i =>
  if i = 0 then .objAt [(arraySpineKey, 5)] .absent 9
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
theorem cells_separation_false :
    ¬ ∀ (st : Stamps) (typed : Nat → List PropKey) (μ : Nat → Nat) (ρ : Env) (h : Heap)
        (x y m m' l : Nat) (k : PropKey) (l' : Nat),
      StampsHold st typed μ ρ → (∀ i j, i ≤ j → μ i ≤ μ j) → st.after x = some m →
      st.before y = some m' → m' ≤ m → (Region.cells x).mem ρ h l = true → k ∈ typed y →
      (fieldsOf (ρ y)).lookup k = some l' → l ≠ l' := by
  intro H
  exact H apartStamps typedF μ5 apart heap5 0 1 1 1 1 "f" 1 apart_stamps_hold
    (fun i j hij => by simp only [μ5]; split <;> split <;> omega) rfl rfl (Nat.le_refl _)
    (by decide) (by simp [typedF]) (by simp [apart, fieldsOf]) rfl

/-- `stamps_separate`'s region premise must exclude `cells`: on the witness,
slot 0's listed element and slot 1's typed field are one location, so the
theorem's conclusion fails there; were its premise to admit `elems 0`, this
would prove `False`. -/
theorem stamps_separate_excludes_cells
    (hr : (∃ k, Region.cells 0 = Region.field 0 k) ∨ Region.cells 0 = Region.fields 0) : False :=
  stamps_separate (x := 0) (y := 1) (m := 1) (m' := 1) (r := .cells 0) (h := heap5) (l := 1) (k := "f")
    (l' := 1) apart_stamps_hold
    (fun i j hij => by simp only [μ5]; split <;> split <;> omega) rfl rfl (Nat.le_refl _) hr
    (by decide) (by simp [typedF]) (by simp [apart, fieldsOf]) rfl

/-! ## Mark maps

Source stamps: `after 0 = 1`, `before 1 = 2`, with marks `0, 5, 10`, and
location 7 both an own location of slot 0 and slot 1's typed field. A target
merging marks 1 and 2 would make them apart, and each such merge is false.
The mark-map check (`stampEdgeOk`) belongs to the deferred provenance stamps
([FOOTPRINTS](../../../docs/FOOTPRINTS.md#deferred-extra-precision)), which no
checker uses; its soundness theorem with this counterexample shows it refuses
both merges. -/

private def source : Stamps := ⟨fun x => if x = 0 then some 1 else none, fun y => if y = 1 then some 2 else none⟩
private def merged : Stamps := ⟨fun x => if x = 0 then some 1 else none, fun y => if y = 1 then some 1 else none⟩

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

/-! ## Density depends on its spine alone

Every slot names spine location 0. Location 1 shrinks; every region that
covers it also covers location 0, so no footprint keeping location 0 within
`grow` states the change, and density survives it. -/

private def spine0 : Env := fun _ => .objAt [(arraySpineKey, 0)] .absent 9

theorem dense_survives_outside_support :
    Dense 0 1 spine0 [.arr [some 2], .arr [some 2], .nul] ∧
      Dense 0 1 spine0 [.arr [some 2], .arr [], .nul] := by
  have hd : Dense 0 1 spine0 [.arr [some 2], .arr [some 2], .nul] :=
    ⟨0, [some 2], by simp [spine0, fieldsOf], rfl,
      ⟨by simp, fun i hi => by cases i with | zero => simp | succ i => omega⟩⟩
  refine ⟨hd, dense_support hd fun e he l v hm hv => ?_⟩
  simp only [List.mem_singleton] at he
  subst he
  simp only [Region.mem, spine0, fieldsOf, List.lookup, beq_self_eq_true, beq_iff_eq,
    Option.some.injEq] at hm
  subst hm
  exact ⟨v, by simpa using hv, Change.Holds.refl _ _ _⟩

/-! ## Classes need contracts -/

/-- `nonNull` holds of a spine: a `cell` fact alone gives no class. -/
theorem nonNull_admits_spine : HeapFacts.Atom.holds .nonNull (.arr []) := by
  simp [HeapFacts.Atom.holds, isVal]

/-- A source value may name any location, one the heap does not have
included: `before` comes only from typed fields. -/
theorem source_names_any_location (n : Nat) (W : WorldT n) :
    PositiveNormalization.sourceT n W (.objAt [("f", 100)] .absent 0) ∧
      ¬ 100 < ([] : Heap).length := by
  refine ⟨⟨rfl, ?_⟩, by simp⟩
  simp [Scoped]

/-- **An element location holds no spine**, at any level: a spine's
references give its element locations the element role, whose contents are
source values. -/
theorem element_holds_no_spine :
    ¬ ∃ (n : Nat) (W : WorldT n) (h : Heap), HeapOk n W h ∧
      h[0]? = some (.arr [some 1]) ∧ h[1]? = some (.arr []) := by
  rintro ⟨n, W, h, hok, h0, h1⟩
  have hrole : roleAt W 1 = some .elem := RefsOk_arr_iff.mp (hok.refs_at h0) 1 (by simp)
  obtain ⟨u, hu, hcat, -⟩ := hok.2 1 .elem hrole
  rw [h1] at hu
  cases hu
  simp [Cat, isSourceVal] at hcat

/-! ## The stability check

A cell fact about `x.k` survives a write to `class(value)` only where the
field's class is known to be another one, a write to the spines (no field
is a spine, by the bounds), and never a write to the field itself. A field
under a key other than the spine key whose class evidence is the spines
selects no location of a well-formed state: its bound under the evidence
is empty. -/

private def noKnowledge : SepEvidence := {}
private def spineK : SepEvidence := { cl := fieldClass 0 "k" .spines }
private def cellK : FactKind := .cell ⟨0, { nul := true }, "k"⟩

#guard !stable noKnowledge cellK.support [(.cls .values, .any)]
#guard stable noKnowledge cellK.support [(.cls .spines, .any)]
#guard !stable noKnowledge cellK.support [(.field 0 "k", .any)]
#guard stable noKnowledge cellK.support [(.field 0 "k", .keep)]
#guard stable spineK cellK.support [(.cls .values, .any)]
#guard stable spineK cellK.support [(.field 0 "k", .any)]

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
-- sort's writeback, judged from the entry spine, after a comparator that removed both indices
#guard Change.grow.holdsB 2 (.arr [some 0, some 1])
  (.arr ((Arr.mk [] 2).writeback (itemCount [some 0, some 1] 2) 2).ls)
-- and the step from the comparator's spine is no `grow` of the entry spine's prefix after a
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

/-! ## Keeping a length across an argument-path frame

The central example: `readRuns(runs)` states `value: any, spine: keep` and
`runs.openBrackets[*]: any`; the caller keeps a density fact of `flags`
(slot 0) where `runs` (slot 1) reaches its array apart from `flags`'s spine
and that array's cells are element cells. -/

private def runsFrame : Footprint :=
  [(.cls .values, .any), (.cls .spines, .keep),
   (.path 1 ["openBrackets"] arraySpineKey, .any), (.pathCells 1 ["openBrackets"], .any)]
private def flagsSpine : ClassEvidence := fieldClass 0 arraySpineKey .spines
private def runsK : SepEvidence :=
  { cl := flagsSpine
    facts := [.spines (1, ["openBrackets"]) (0, [])] }

#guard stable runsK (FactKind.dense 0 1).support runsFrame
-- Without spine separation the path's spine may be `flags`'s.
#guard !stable { runsK with facts := [] } (FactKind.dense 0 1).support runsFrame
-- The cells are element cells and `flags`'s spine an array spine: their
-- bounds are apart, and the class evidence adds nothing.
#guard stable { runsK with cl := noClassEvidence } (FactKind.dense 0 1).support runsFrame

end Verification.Footprints.Controls
