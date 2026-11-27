import Verification.Paper.EffectLanguage.Rules
import Verification.Semantics.ClosedFootprints
import Verification.Semantics.Confinement
import Verification.Semantics.SurvivalSeparation

/-! # An idealised model of the paper's effects

The effects of "An effect language for TScert" over the heaps, regions and
changes of `Verification.Semantics.Footprints`, extended with confined module
state regions `M.@state` (`ModuleRegion`) grounded in `Confinement.ClosedOut`,
and the proof that the model meets all five rules of `Rules.lean`
(`model_rules`).

- A state is a heap. An effect of the paper with its `else` is an `Atom.eff`:
  concrete `Footprints.Region` entries, confined module-state entries
  `ModuleRegion × Change`, the change `dflt` of locations no entry covers, and
  the environment its concrete regions are read in. `Atom.old n C` keeps every
  external location allocated since a heap of length `n` (i.e., `l ≥ n` with
  `C.mem h l = false`).
- A confined module region `ModuleRegion` models a module's private state
  `M.@state`: allocated locations satisfying boundary closure
  (`Confinement.ClosedOut`) at every heap and fresh-only growth
  (`R_M(h') ⊆ R_M(h) ∪ [|h|, |h'|)`). By `Confinement.ClosedOut.not_reaches`,
  every concrete region or declared-reach path rooted at an external value
  (`NoPriv`) is disjoint from `M.@state` (`closedOut_region_disjoint`,
  `closedOut_reach_disjoint`).
- An effect is a list of atoms, their meet: each location's bound is the
  weakest of the atoms' bounds (`bnd`), and a transition is bounded when the
  heap only grows and every old location changes within its bound (`Act`).
- A run is a heap extension (`Reaches`). The model reads no admissibility:
  its transitions are every pair of heaps with the first a length-prefix of
  the second's locations.
-/

namespace Verification.Paper.EffectLanguage.Model

open Verification Footprints Confinement
open Verification.TolerantFrames.Reach

/-! ## Confined module regions -/

/-- A confined module region `M.@state`: a heap-indexed set of allocated
locations that is boundary-closed (`Confinement.ClosedOut`) at every heap
and satisfies fresh-only growth (`R_M(h') ⊆ R_M(h) ∪ [|h|, |h'|)`). -/
structure ModuleRegion where
  mem : Heap → Nat → Bool
  bounded : ∀ h l, mem h l = true → l < h.length
  closedOut : ∀ h, ClosedOut h (fun l => mem h l = true)
  freshGrowth : ∀ h h', h.length ≤ h'.length → ∀ l < h.length, mem h' l = true → mem h l = true

namespace ModuleRegion

/-- Containment of confined module regions. -/
def Sub (M C : ModuleRegion) : Prop :=
  ∀ h l, M.mem h l = true → C.mem h l = true

theorem Sub.refl (M : ModuleRegion) : M.Sub M := fun _ _ h => h

/-- The empty confined module region. -/
def empty : ModuleRegion where
  mem _ _ := false
  bounded _ _ h := by cases h
  closedOut _ _ _ _ _ _ _ _ hf := by cases hf
  freshGrowth _ _ _ _ _ h := by cases h

/-- The union of two confined module regions is itself boundary-closed and
satisfies fresh-only growth. -/
def union (M₁ M₂ : ModuleRegion) : ModuleRegion where
  mem h l := M₁.mem h l || M₂.mem h l
  bounded h l hm := by
    rcases Bool.or_eq_true_iff.mp hm with h₁ | h₂
    · exact M₁.bounded h l h₁
    · exact M₂.bounded h l h₂
  closedOut h m hlt hnot v hv l hleaf hmem := by
    have hnot₁ : ¬ (M₁.mem h m = true) := fun h₁ => hnot (by simp [h₁])
    have hnot₂ : ¬ (M₂.mem h m = true) := fun h₂ => hnot (by simp [h₂])
    rcases Bool.or_eq_true_iff.mp hmem with h₁ | h₂
    · exact M₁.closedOut h m hlt hnot₁ v hv l hleaf h₁
    · exact M₂.closedOut h m hlt hnot₂ v hv l hleaf h₂
  freshGrowth h h' hle l hlt hm := by
    rcases Bool.or_eq_true_iff.mp hm with h₁ | h₂
    · exact Bool.or_eq_true_iff.mpr (.inl (M₁.freshGrowth h h' hle l hlt h₁))
    · exact Bool.or_eq_true_iff.mpr (.inr (M₂.freshGrowth h h' hle l hlt h₂))

theorem sub_union_left (M₁ M₂ : ModuleRegion) : M₁.Sub (M₁.union M₂) :=
  fun _ _ h => Bool.or_eq_true_iff.mpr (.inl h)

theorem sub_union_right (M₁ M₂ : ModuleRegion) : M₂.Sub (M₁.union M₂) :=
  fun _ _ h => Bool.or_eq_true_iff.mpr (.inr h)

end ModuleRegion

/-! ## Disjointness of confined module regions from external roots -/

/-- Every key in an object's property list maps uniquely under `List.lookup`. -/
def ObjNoDup (v : Val) : Prop :=
  ∀ k l, (k, l) ∈ fieldsOf v → (fieldsOf v).lookup k = some l

/-- A heap whose allocated objects all have unique property keys. -/
def HeapNoDup (h : Heap) : Prop :=
  ∀ (l : Nat) (v : Val), h[l]? = some v → ObjNoDup v

/-- Following a field path (`HeapKnowledge.readPath`) from a value satisfying
`NoPriv priv` in a `ClosedOut` heap yields a value satisfying `NoPriv priv`. -/
theorem closedOut_readPath_noPriv {h : Heap} {priv : Nat → Prop} (hc : ClosedOut h priv) :
    ∀ {p : List String} {v v' : Val}, NoPriv priv v → HeapKnowledge.readPath h v p = some v' →
      NoPriv priv v'
  | [], _, _, hnp, hr => by
    simp [HeapKnowledge.readPath] at hr; subst hr; exact hnp
  | f :: p, v, v', hnp, hr => by
    cases v with
    | objAt fs c i =>
      simp only [HeapKnowledge.readPath] at hr
      cases hlk : fs.lookup (.str f) with
      | none => simp [hlk] at hr
      | some l =>
        simp only [hlk] at hr
        cases hu : h[l]? with
        | none => simp [hu] at hr
        | some u =>
          simp only [hu] at hr
          have hnext : next (.objAt fs c i) (.key (.str f)) = some l := by
            simpa [next, fieldsOf] using hlk
          have hnot : ¬ priv l := hnp.of_next hnext
          have hlt : l < h.length := (List.getElem?_eq_some_iff.mp hu).1
          exact closedOut_readPath_noPriv hc (hc l hlt hnot u hu) hr
    | _ => simp [HeapKnowledge.readPath] at hr

/-- `readPath` from an `ObjNoDup` value in a `HeapNoDup` heap yields an `ObjNoDup` value. -/
theorem readPath_objNoDup {h : Heap} (hnd : HeapNoDup h) :
    ∀ {p : List String} {v v' : Val}, ObjNoDup v → HeapKnowledge.readPath h v p = some v' →
      ObjNoDup v'
  | [], _, _, hv, hr => by simp [HeapKnowledge.readPath] at hr; subst hr; exact hv
  | f :: p, v, v', _, hr => by
    cases v with
    | objAt fs c i =>
      simp only [HeapKnowledge.readPath] at hr
      cases hlk : fs.lookup (.str f) with
      | none => simp [hlk] at hr
      | some l =>
        simp only [hlk] at hr
        cases hu : h[l]? with
        | none => simp [hu] at hr
        | some u =>
          simp only [hu] at hr
          exact readPath_objNoDup hnd (hnd l u hu) hr
    | _ => simp [HeapKnowledge.readPath] at hr

/-- Every element cell listed by a spine of a `NoPriv` value lies outside `priv`
in a `ClosedOut` heap. -/
theorem closedOut_spineCells_not_priv {h : Heap} {priv : Nat → Prop} (hc : ClosedOut h priv)
    {v : Val} (hnp : NoPriv priv v) {l : Nat} (hm : some l ∈ spineCells h v) : ¬ priv l := by
  have entries_not_priv : ∀ {s : Nat}, ¬ priv s → some l ∈ entriesAt h (some s) → ¬ priv l := by
    intro s hns he
    simp only [entriesAt] at he
    cases hs : h[s]? with
    | none => rw [hs] at he; simp at he
    | some sv =>
      rw [hs] at he
      cases hse : spineEntries sv with
      | none => simp [hse] at he
      | some ls =>
        simp only [hse, Option.bind_some, Option.getD_some] at he
        obtain ⟨i, hi⟩ := List.getElem?_of_mem he
        have hnext : next sv (.cell i) = some l := by
          simp [next, hse, hi]
        have hlt : s < h.length := (List.getElem?_eq_some_iff.mp hs).1
        exact (hc s hlt hns sv hs).of_next hnext
  simp only [spineCells, List.mem_append] at hm
  rcases hm with hm | hm
  · cases hlk : (fieldsOf v).lookup arraySpineKey with
    | none => rw [hlk] at hm; simp [entriesAt] at hm
    | some s =>
      rw [hlk] at hm
      exact entries_not_priv (hnp.of_next (a := .key arraySpineKey) (by simpa [next] using hlk)) hm
  · cases hd : HeapKnowledge.descriptorSpine v with
    | none => rw [hd] at hm; simp [entriesAt] at hm
    | some s =>
      rw [hd] at hm
      exact entries_not_priv (hnp.of_next (a := .view) (by simpa [next] using hd)) hm

/-- The spine selected by `HeapKnowledge.elementsOf` of a `NoPriv` value lies
outside `priv`. -/
theorem closedOut_elementsOf_not_priv {priv : Nat → Prop} {v : Val} (hnp : NoPriv priv v)
    {l : Nat} (hm : HeapKnowledge.elementsOf v = some l) : ¬ priv l := by
  cases v with
  | objAt fs c i =>
    simp only [HeapKnowledge.elementsOf] at hm
    cases hlk : fs.lookup arraySpineKey with
    | some s =>
      rw [hlk] at hm; cases hm
      exact hnp.of_next (a := .key arraySpineKey) (by simpa [next, fieldsOf] using hlk)
    | none =>
      rw [hlk] at hm
      cases c with
      | view s f n =>
        cases hm
        exact hnp.of_next (a := .view) (by simp [next, HeapKnowledge.descriptorSpine])
      | _ => simp at hm
  | _ => simp [HeapKnowledge.elementsOf] at hm

/-- The slot a concrete `Footprints.Region` is rooted at, where it is rooted
at one (every region except `cls` and `all`). -/
def rootOf : Region → Option Nat
  | .field x _ | .fields x | .cells x | .path x _ _ | .pathFields x _ | .pathCells x _
  | .spine x _ | .elemSpines x _ => some x
  | .cls _ | .all => none

/-- **Module disjointness for concrete regions**: in a `ClosedOut` heap,
every location of any concrete region rooted at an external value `ρ x`
(`NoPriv priv (ρ x)`) lies outside `priv`. -/
theorem closedOut_region_disjoint {h : Heap} {priv : Nat → Prop} {ρ : Env} {x l : Nat}
    (hc : ClosedOut h priv) (hnd : HeapNoDup h) (hnp : NoPriv priv (ρ x)) (hxd : ObjNoDup (ρ x))
    (r : Region) (hr : rootOf r = some x) (hmem : r.mem ρ h l = true) : ¬ priv l := by
  cases r with
  | cls _ | all => simp [rootOf] at hr
  | field y k =>
    simp [rootOf] at hr; subst hr
    simp only [Region.mem, beq_iff_eq] at hmem
    exact hnp.of_next (a := .key k) (by simpa [next] using hmem)
  | fields y =>
    simp [rootOf] at hr; subst hr
    simp only [Region.mem, List.contains_iff_mem, fieldLocs, List.mem_map, List.mem_filter] at hmem
    obtain ⟨⟨k, l'⟩, ⟨hkl, _⟩, rfl⟩ := hmem
    exact hnp.of_next (a := .key k) (by simpa [next] using hxd k l' hkl)
  | cells y =>
    simp [rootOf] at hr; subst hr
    simp only [Region.mem, List.contains_iff_mem] at hmem
    exact closedOut_spineCells_not_priv hc hnp hmem
  | path y p k =>
    simp [rootOf] at hr; subst hr
    simp only [Region.mem] at hmem
    cases hrp : HeapKnowledge.readPath h (ρ y) p with
    | none => rw [hrp] at hmem; cases hmem
    | some v =>
      rw [hrp] at hmem; simp only [beq_iff_eq] at hmem
      exact (closedOut_readPath_noPriv hc hnp hrp).of_next (a := .key k) (by simpa [next] using hmem)
  | pathFields y p =>
    simp [rootOf] at hr; subst hr
    simp only [Region.mem] at hmem
    cases hrp : HeapKnowledge.readPath h (ρ y) p with
    | none => rw [hrp] at hmem; cases hmem
    | some v =>
      rw [hrp] at hmem
      simp only [List.contains_iff_mem, fieldLocs, List.mem_map, List.mem_filter] at hmem
      obtain ⟨⟨k, l'⟩, ⟨hkl, _⟩, rfl⟩ := hmem
      have hvn := closedOut_readPath_noPriv hc hnp hrp
      have hvd := readPath_objNoDup hnd hxd hrp
      exact hvn.of_next (a := .key k) (by simpa [next] using hvd k l' hkl)
  | pathCells y p =>
    simp [rootOf] at hr; subst hr
    simp only [Region.mem] at hmem
    cases hrp : HeapKnowledge.readPath h (ρ y) p with
    | none => rw [hrp] at hmem; cases hmem
    | some v =>
      rw [hrp] at hmem; simp only [List.contains_iff_mem] at hmem
      exact closedOut_spineCells_not_priv hc (closedOut_readPath_noPriv hc hnp hrp) hmem
  | spine y p =>
    simp [rootOf] at hr; subst hr
    simp only [Region.mem] at hmem
    cases hrp : HeapKnowledge.readPath h (ρ y) p with
    | none => rw [hrp] at hmem; cases hmem
    | some v =>
      rw [hrp] at hmem; simp only [beq_iff_eq] at hmem
      exact closedOut_elementsOf_not_priv (closedOut_readPath_noPriv hc hnp hrp) hmem
  | elemSpines y p =>
    simp [rootOf] at hr; subst hr
    simp only [Region.mem] at hmem
    cases hrp : HeapKnowledge.readPath h (ρ y) p with
    | none => rw [hrp] at hmem; cases hmem
    | some v =>
      rw [hrp] at hmem; simp only [List.any_eq_true] at hmem
      obtain ⟨o, ho, hm⟩ := hmem
      cases o with
      | none => cases hm
      | some c =>
        simp only at hm
        cases hcu : h[c]? with
        | none => rw [hcu] at hm; cases hm
        | some u =>
          rw [hcu] at hm; simp only [beq_iff_eq] at hm
          have hcn := closedOut_spineCells_not_priv hc (closedOut_readPath_noPriv hc hnp hrp) ho
          exact closedOut_elementsOf_not_priv (hc c (List.getElem?_eq_some_iff.mp hcu).1 hcn u hcu) (elementsOf_of_lookup_spine hm)

/-- **Module disjointness for declared reach (`x.**_T`)**: any location
reachable along arbitrary public field, spine, and element paths from an
external root `v` (`NoPriv`) lies outside every confined module region `M`. -/
theorem closedOut_reach_disjoint (M : ModuleRegion) {h : Heap} {v : Val} {l : Nat}
    (hnp : NoPriv (fun loc => M.mem h loc = true) v) (hr : Reaches allC h v l) :
    M.mem h l = false := by
  cases hm : M.mem h l with
  | false => rfl
  | true => exact False.elim ((M.closedOut h).not_reaches hnp hr hm)

/-! ## Non-spine object fields class (`"fields"`, `Role.field`) -/

/-- A role-typed set of non-spine object field locations (`"fields"`,
`Role.field`): allocated locations disjoint from every array spine, element
cell, and element spine (which carry `Role.spine` or `Role.elem`). -/
structure FieldClass where
  mem : Heap → Nat → Bool
  bounded : ∀ h l, mem h l = true → l < h.length
  noSpine : ∀ h v s, HeapKnowledge.elementsOf v = some s → mem h s = false
  noElemCell : ∀ h v l, some l ∈ spineCells h v → mem h l = false
  noSpineKey : ∀ h v l, (fieldsOf v).lookup arraySpineKey = some l → mem h l = false

/-- Regions whose locations are never non-spine object fields (`Role.field`):
array/view spines, array element cells, element spines, and spine-key lookups. -/
def nonFieldRegion : Region → Bool
  | .spine _ _ | .cells _ | .pathCells _ _ | .elemSpines _ _ => true
  | .field _ k | .path _ _ k => k == arraySpineKey
  | _ => false

/-- **Role disjointness for `"fields"`**: every location of a `nonFieldRegion`
lies outside `FieldClass`. -/
theorem fieldClass_region_disjoint (F : FieldClass) {ρ : Env} {h : Heap} {r : Region} {l : Nat}
    (hnf : nonFieldRegion r = true) (hm : r.mem ρ h l = true) : F.mem h l = false := by
  cases r with
  | spine x p =>
    simp only [Region.mem] at hm
    cases hrp : HeapKnowledge.readPath h (ρ x) p with
    | none => rw [hrp] at hm; cases hm
    | some v =>
      rw [hrp] at hm; simp only [beq_iff_eq] at hm
      exact F.noSpine h v l hm
  | cells x =>
    simp only [Region.mem, List.contains_iff_mem] at hm
    exact F.noElemCell h (ρ x) l hm
  | pathCells x p =>
    simp only [Region.mem] at hm
    cases hrp : HeapKnowledge.readPath h (ρ x) p with
    | none => rw [hrp] at hm; cases hm
    | some v =>
      rw [hrp] at hm; simp only [List.contains_iff_mem] at hm
      exact F.noElemCell h v l hm
  | elemSpines x p =>
    simp only [Region.mem] at hm
    cases hrp : HeapKnowledge.readPath h (ρ x) p with
    | none => rw [hrp] at hm; cases hm
    | some v =>
      rw [hrp] at hm; simp only [List.any_eq_true] at hm
      obtain ⟨o, _, ho⟩ := hm
      cases o with
      | none => cases ho
      | some c =>
        simp only at ho
        cases hcu : h[c]? with
        | none => rw [hcu] at ho; cases ho
        | some u =>
          rw [hcu] at ho; simp only [beq_iff_eq] at ho
          exact F.noSpineKey h u l ho
  | field x k =>
    simp only [nonFieldRegion, beq_iff_eq] at hnf; subst hnf
    simp only [Region.mem, beq_iff_eq] at hm
    exact F.noSpineKey h (ρ x) l hm
  | path x p k =>
    simp only [nonFieldRegion, beq_iff_eq] at hnf; subst hnf
    simp only [Region.mem] at hm
    cases hrp : HeapKnowledge.readPath h (ρ x) p with
    | none => rw [hrp] at hm; cases hm
    | some v =>
      rw [hrp] at hm; simp only [beq_iff_eq] at hm
      exact F.noSpineKey h v l hm
  | fields _ | pathFields _ _ | cls _ | all => cases hnf

/-! ## Plain-array element-cell disjointness (`Plain-Cells-Disj`) -/

/-- Distinct plain array spines in `h` own disjoint element cells (plain array
creation and extension allocate fresh element cells per spine; typed-array
`.viewSpine` views are excluded because `.subarray()` may share cells). -/
def PlainElemCellsDisjoint (h : Heap) : Prop :=
  ∀ (s t : Nat) (ls₁ ls₂ : List (Option Nat)) (l : Nat), s ≠ t →
    h[s]? = some (Tm.arr ls₁) → h[t]? = some (Tm.arr ls₂) →
    some l ∈ ls₁ → some l ∉ ls₂

/-- **Plain-array element-cell disjointness**: in a `PlainElemCellsDisjoint`
heap, any two plain-array paths `(x, p)` and `(y, q)` (no view descriptor
spine) whose array spines are distinct have disjoint `pathCells` regions. -/
theorem plainArray_cells_disjoint {ρ : Env} {h : Heap}
    (hdisj : PlainElemCellsDisjoint h)
    {x y : Nat} {p q : List String} {u w : Val} {s t : Nat} {ls₁ ls₂ : List (Option Nat)}
    (hu : HeapKnowledge.readPath h (ρ x) p = some u)
    (hw : HeapKnowledge.readPath h (ρ y) q = some w)
    (hdu : HeapKnowledge.descriptorSpine u = none)
    (hdw : HeapKnowledge.descriptorSpine w = none)
    (hsu : spineOf u = some s) (hsw : spineOf w = some t)
    (hs₁ : h[s]? = some (.arr ls₁)) (hs₂ : h[t]? = some (.arr ls₂))
    (hne : s ≠ t) {l : Nat}
    (hm₁ : (Region.pathCells x p).mem ρ h l = true) :
    (Region.pathCells y q).mem ρ h l = false := by
  have hlu : (fieldsOf u).lookup arraySpineKey = some s := by simpa [spineOf] using hsu
  have hlw : (fieldsOf w).lookup arraySpineKey = some t := by simpa [spineOf] using hsw
  have hsc₁ : spineCells h u = ls₁ := by
    simp [spineCells, entriesAt, hlu, hdu, hs₁, spineEntries]
  have hsc₂ : spineCells h w = ls₂ := by
    simp [spineCells, entriesAt, hlw, hdw, hs₂, spineEntries]
  simp only [Region.mem, hu, hsc₁, List.contains_iff_mem] at hm₁
  simp only [Region.mem, hw, hsc₂]
  cases hc : ls₂.contains (some l) with
  | false => rfl
  | true => exact False.elim (hdisj s t ls₁ ls₂ l hne hs₁ hs₂ hm₁ (List.contains_iff_mem.mp hc))

/-! ## Effects and bounds -/

/-- The largest of a list of changes, `keep` for none. -/
def maxOf (cs : List Change) : Change := cs.foldr Change.max .keep

/-- An effect of the paper without variables: concrete regions, confined
module-state regions `M.@state`, an optional `"fields"` class entry, a default
`else` change, and the environment its concrete regions read. -/
structure Eff1 where
  entries : Footprint
  modules : List (ModuleRegion × Change) := []
  fields : Option (FieldClass × Change) := none
  dflt : Change
  env : Env

/-- An atom of an effect: an effect of the paper, or the anchor effect keeping
every external post-entry location (outside `[0, n)` and outside confined
module state `C`). -/
inductive Atom where
  | eff (Φ : Eff1)
  | old (n : Nat) (C : ModuleRegion := ModuleRegion.empty)

/-- An effect: the meet of its atoms. -/
abbrev Eff := List Atom

/-- The changes of the concrete, `"fields"`, and module entries whose regions cover `l`. -/
def Eff1.cov (Φ : Eff1) (h : Heap) (l : Nat) : List Change :=
  (Φ.entries.filter fun e => e.1.mem Φ.env h l).map Prod.snd ++
  (match Φ.fields with | some (F, c) => if F.mem h l then [c] else [] | none => []) ++
  (Φ.modules.filter fun e => e.1.mem h l).map Prod.snd

/-- The change an effect allows at `l`: the largest covering entry's, or
`dflt` where no entry covers `l`. -/
def Eff1.bnd (Φ : Eff1) (h : Heap) (l : Nat) : Change :=
  match Φ.cov h l with
  | [] => Φ.dflt
  | cs => maxOf cs

def Atom.bnd : Atom → Heap → Nat → Change
  | .eff Φ, h, l => Φ.bnd h l
  | .old n C, h, l => if l < n || C.mem h l then .any else .keep

/-- The change an effect allows at `l`: the weakest of its atoms'. -/
def bnd (E : Eff) (h : Heap) (l : Nat) : Change :=
  E.foldr (fun a c => (a.bnd h l).min c) .any

/-- The transitions an effect bounds. -/
def Act (E : Eff) (h h' : Heap) : Prop :=
  h.length ≤ h'.length ∧
    ∀ l v, h[l]? = some v → ∃ v', h'[l]? = some v' ∧ (bnd E h l).Holds h.length v v'

def Reaches (h₀ h : Heap) : Prop := h₀.length ≤ h.length

/-- `E` is within `F` at `h₀` (relative to the confined module universe `C`):
at every location of `h₀`, and at every future location allocated inside `C`,
`E`'s bound is within `F`'s. -/
def Within (C : ModuleRegion) (E F : Eff) (h₀ : Heap) : Prop :=
  (∀ l < h₀.length, (bnd E h₀ l).le (bnd F h₀ l) = true) ∧
  (∀ h, Reaches h₀ h → ∀ l, h₀.length ≤ l → C.mem h l = true → (bnd E h l).le (bnd F h l) = true)

def Same (E : Eff) (h₀ h : Heap) : Prop :=
  ∀ l < h₀.length, bnd E h l = bnd E h₀ l

/-- An instance anchored at a call at `h₀` (generalized for confined module
regions in `C`): on old locations `l < |h₀|`, its bound at any later heap `h`
never widens beyond its bound at `h₀` (admitting fresh-only growth and
dropping old interior storage), and on every external post-entry location
(`l ≥ |h₀|` with `C.mem h l = false`), its bound is `keep`. -/
def Anchored (C : ModuleRegion) (E : Eff) (h₀ : Heap) : Prop :=
  ∀ h, Reaches h₀ h →
    (∀ l < h₀.length, (bnd E h l).le (bnd E h₀ l) = true) ∧
    (∀ l, h₀.length ≤ l → C.mem h l = false → bnd E h l = .keep)

/-- A renaming to the caller: the caller's slot of each callee position,
and the caller's environment. -/
abbrev Ren := (Nat → Option Nat) × Env

def renAtom (σ : Ren) : Atom → Atom
  | .eff Φ => .eff ⟨Φ.entries.renameM σ.1, Φ.modules, Φ.fields, Φ.dflt, σ.2⟩
  | .old n C => .old n C

def rename (σ : Ren) (E : Eff) : Eff := E.map (renAtom σ)

/-- Every position of each effect atom is an argument's slot holding that
position's value. -/
def RenOk (σ : Ren) (E : Eff) : Prop :=
  ∀ Φ, Atom.eff Φ ∈ E → ∀ i, ∃ j, σ.1 i = some j ∧ σ.2 j = Φ.env i

/-- A confined module region within the universe `C`. -/
abbrev Mod (C : ModuleRegion) := { M : ModuleRegion // M.Sub C }

/-- The effect `{ M.@state : any; else : keep }` of mutating confined module
state `M`. -/
def modEff {C : ModuleRegion} (M : Mod C) : Eff :=
  [.eff ⟨[], [(M.1, .any)], none, .keep, fun _ => .undef⟩]

/-- `M.@state` is disjoint from `Φ` from `h₀` onward when every atom of `Φ` is
an effect with `else : any` whose entries never cover `M.@state` at any
reachable heap. -/
def ModDisjoint {C : ModuleRegion} (M : Mod C) (Φ : Eff) (h₀ : Heap) : Prop :=
  ∀ a ∈ Φ, match a with
    | .eff Ψ =>
      Ψ.dflt = .any ∧
      Ψ.fields = none ∧
      ∀ h, Reaches h₀ h → ∀ l, M.1.mem h l = true →
        (∀ e ∈ Ψ.entries, e.1.mem Ψ.env h l = false) ∧
        (∀ e ∈ Ψ.modules, e.1.mem h l = false)
    | .old _ _ => False

/-- The class effect `{ fields : any; else : keep }` of mutating non-spine
object fields (`Role.field`). -/
def fieldsEff (F : FieldClass) : Eff :=
  [.eff ⟨[], [], some (F, .any), .keep, fun _ => .undef⟩]

/-- `"fields"` is disjoint from `Φ` from `h₀` onward when every atom of `Φ` is
an effect with `else : any` and no `"fields"` entry whose concrete and module
entries never cover `F` at any reachable heap. -/
def FieldsDisjoint (F : FieldClass) (Φ : Eff) (h₀ : Heap) : Prop :=
  ∀ a ∈ Φ, match a with
    | .eff Ψ =>
      Ψ.dflt = .any ∧
      Ψ.fields = none ∧
      ∀ h, Reaches h₀ h → ∀ l, F.mem h l = true →
        (∀ e ∈ Ψ.entries, e.1.mem Ψ.env h l = false) ∧
        (∀ e ∈ Ψ.modules, e.1.mem h l = false)
    | .old _ _ => False

/-- Two effects `E` and `Φ` are plain-array element-cell disjoint at `h₀`
(within module universe `C`) when every location `E` may mutate at `h₀` (and at
post-entry locations in `C`) is allowed `.any` by `Φ`. -/
def PlainCellsDisj (C : ModuleRegion) (E Φ : Eff) (h₀ : Heap) : Prop :=
  (∀ l < h₀.length, bnd E h₀ l ≠ .keep → bnd Φ h₀ l = .any) ∧
  (∀ h, Reaches h₀ h → ∀ l, h₀.length ≤ l → C.mem h l = true → bnd E h l ≠ .keep → bnd Φ h l = .any)

/-- Every present element of the array at path `(x, p)` whose array spine
holds `.arr ls` satisfies `P ls.length`. -/
def AllElemLen (P : Nat → Prop) (ρ : Env) (x : Nat) (p : List String) (h : Heap) : Prop :=
  ∀ v c u s ls,
    HeapKnowledge.readPath h (ρ x) p = some v →
    some c ∈ spineCells h v →
    h[c]? = some u →
    (fieldsOf u).lookup arraySpineKey = some s →
    h[s]? = some (.arr ls) →
    P ls.length

/-- An effect `Φ` preserves an outer array's path, spine, and element cells
while bounding every element spine by at most `.extend`, paired with a monotone
lower-bound predicate `P` on each element's spine length. -/
def ElemLenExtend (Φ : Eff) (Q : Heap → Prop) : Prop :=
  ∃ (P : Nat → Prop) (ρ : Env) (x : Nat) (p : List String),
    (∀ a b, a ≤ b → P a → P b) ∧
    Q = AllElemLen P ρ x p ∧
    ∀ h h' v c u s,
      Act Φ h h' →
      HeapKnowledge.readPath h' (ρ x) p = some v →
      some c ∈ spineCells h' v →
      h'[c]? = some u →
      (fieldsOf u).lookup arraySpineKey = some s →
      HeapKnowledge.readPath h (ρ x) p = some v ∧
      some c ∈ spineCells h v ∧
      h[c]? = some u ∧
      s < h.length ∧
      (bnd Φ h s).le .extend = true

/-! ## Lemmas -/

theorem keep_le (c : Change) : Change.keep.le c = true := by
  cases c <;> rfl

theorem le_any (c : Change) : c.le .any = true := by
  cases c <;> rfl

theorem le_refl (c : Change) : c.le c = true := by
  cases c <;> rfl

theorem le_trans {a b c : Change} (h₁ : a.le b = true) (h₂ : b.le c = true) : a.le c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [Change.le, Change.rank]

theorem min_any_right (c : Change) : c.min .any = c := by
  cases c <;> rfl

theorem le_min_iff {a b c : Change} : a.le (b.min c) = true ↔ a.le b = true ∧ a.le c = true := by
  cases a <;> cases b <;> cases c <;> decide

theorem max_le_iff {a b c : Change} : (a.max b).le c = true ↔ a.le c = true ∧ b.le c = true := by
  cases a <;> cases b <;> cases c <;> decide

theorem max_assoc (a b c : Change) : a.max (b.max c) = (a.max b).max c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem mem_le_maxOf {c : Change} {cs : List Change} (hc : c ∈ cs) : c.le (maxOf cs) = true := by
  induction cs with
  | nil => cases hc
  | cons y ys ih =>
    simp only [maxOf, List.foldr_cons]
    rcases List.mem_cons.mp hc with rfl | hm
    · exact Change.le_max_left c _
    · exact le_trans (ih hm) (Change.le_max_right y _)

theorem maxOf_le_iff {cs : List Change} {b : Change} :
    (maxOf cs).le b = true ↔ ∀ c ∈ cs, c.le b = true := by
  induction cs with
  | nil => simp [maxOf, keep_le]
  | cons x xs ih =>
    simp only [maxOf] at ih ⊢
    simp only [List.foldr_cons, max_le_iff, ih, List.mem_cons, forall_eq_or_imp]

theorem maxOf_le_of_sub_all {cs₁ cs₂ : List Change} (hsub : ∀ c ∈ cs₁, c ∈ cs₂) :
    (maxOf cs₁).le (maxOf cs₂) = true :=
  maxOf_le_iff.mpr fun c hc => mem_le_maxOf (hsub c hc)

/-- A transition bounded by an effect is bounded by one that allows at
least as much at every old location. -/
theorem act_mono {E F : Eff} {h h' : Heap}
    (hle : ∀ l < h.length, (bnd E h l).le (bnd F h l) = true) (ha : Act E h h') : Act F h h' := by
  refine ⟨ha.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', hh⟩ := ha.2 l v hv
  exact ⟨v', hv', hh.mono (hle l (List.getElem?_eq_some_iff.mp hv).1)⟩

theorem bnd_append (E F : Eff) (h : Heap) (l : Nat) :
    (bnd (E ++ F) h l).Holds = fun b v v' => (bnd E h l).Holds b v v' ∧ (bnd F h l).Holds b v v' := by
  funext b v v'
  induction E with
  | nil =>
    simp only [List.nil_append, bnd, List.foldr_nil]
    exact propext ⟨fun h => ⟨trivial, h⟩, And.right⟩
  | cons a E ih =>
    simp only [List.cons_append, bnd, List.foldr_cons] at ih ⊢
    rw [propext Change.min_holds, propext Change.min_holds, ih]
    exact propext ⟨fun ⟨x, y, z⟩ => ⟨⟨x, y⟩, z⟩, fun ⟨⟨x, y⟩, z⟩ => ⟨x, y, z⟩⟩

/-- A region read at the caller's slots by a renaming defined at every
position covers what it covered at the callee's positions. -/
theorem mem_renameM_total {σ : Nat → Option Nat} {ρ env : Env} {h : Heap} {l : Nat}
    (hσ : ∀ i, ∃ j, σ i = some j ∧ ρ j = env i) :
    ∀ r : Region, (r.renameM σ).mem ρ h l = r.mem env h l := by
  intro r
  cases r with
  | cls | all => rfl
  | field x | fields x | cells x | path x | pathFields x | pathCells x | spine x | elemSpines x =>
    obtain ⟨j, hj, hρ⟩ := hσ x
    simp only [Region.renameM, hj, Region.mem, hρ]

theorem renAtom_bnd {σ : Ren} {Φ : Eff1} {h : Heap} {l : Nat}
    (hσ : ∀ i, ∃ j, σ.1 i = some j ∧ σ.2 j = Φ.env i) :
    (renAtom σ (.eff Φ)).bnd h l = (Atom.eff Φ).bnd h l := by
  simp only [renAtom, Atom.bnd, Eff1.bnd, Eff1.cov, Footprint.renameM, List.filter_map,
    Function.comp_def, mem_renameM_total hσ, List.map_map]

theorem rename_bnd {σ : Ren} {E : Eff} {h : Heap} {l : Nat} (hσ : RenOk σ E) :
    bnd (rename σ E) h l = bnd E h l := by
  induction E with
  | nil => rfl
  | cons a E ih =>
    simp only [rename, List.map_cons, bnd, List.foldr_cons] at ih ⊢
    have hrest : RenOk σ E := fun Φ hm => hσ Φ (List.mem_cons_of_mem _ hm)
    rw [ih hrest]
    cases a with
    | eff Φ => rw [renAtom_bnd (hσ Φ List.mem_cons_self)]
    | old n C => rfl

/-- The pointwise bound of `modEff M` at `(h, l)`: `any` inside `M.@state`,
`keep` outside. -/
theorem modEff_bnd {C : ModuleRegion} (M : Mod C) (h : Heap) (l : Nat) :
    bnd (modEff M) h l = if M.1.mem h l then .any else .keep := by
  simp only [modEff, bnd, List.foldr_cons, List.foldr_nil, min_any_right, Atom.bnd, Eff1.bnd,
    Eff1.cov, List.filter_nil, List.map_nil, List.nil_append, List.filter_cons]
  cases hm : M.1.mem h l <;> rfl

/-- The pointwise bound of `fieldsEff F` at `(h, l)`: `any` inside `"fields"`,
`keep` outside. -/
theorem fieldsEff_bnd (F : FieldClass) (h : Heap) (l : Nat) :
    bnd (fieldsEff F) h l = if F.mem h l then .any else .keep := by
  simp only [fieldsEff, bnd, List.foldr_cons, List.foldr_nil, min_any_right, Atom.bnd, Eff1.bnd,
    Eff1.cov, List.filter_nil, List.map_nil, List.nil_append, List.append_nil]
  cases hf : F.mem h l <;> rfl

/-- **Disjointness of `"fields"` from non-field regions**: if `Ψ` has
`else : any`, no module or `"fields"` entries, and every concrete entry of `Ψ`
is a `nonFieldRegion` (array/view spines, element cells, element spines), then
`FieldsDisjoint F [.eff Ψ] h₀` holds. -/
theorem fieldsDisj_of_nonField (F : FieldClass) (Ψ : Eff1) (h₀ : Heap)
    (hdflt : Ψ.dflt = .any) (hmods : Ψ.modules = []) (hflds : Ψ.fields = none)
    (hnf : ∀ e ∈ Ψ.entries, nonFieldRegion e.1 = true) :
    FieldsDisjoint F [.eff Ψ] h₀ := by
  intro a ha
  simp only [List.mem_singleton] at ha
  subst ha
  refine ⟨hdflt, hflds, fun h _ l hfl => ⟨fun e he => ?_, fun e he => by rw [hmods] at he; cases he⟩⟩
  cases hm : e.1.mem Ψ.env h l with
  | false => rfl
  | true =>
    have := fieldClass_region_disjoint F (hnf e he) hm
    rw [hfl] at this; cases this

/-- **Plain-array cell disjointness lifted to `PlainCellsDisj`**: if `E` only
mutates `Region.pathCells x p` of a plain array and every entry of `Φ` (with
`else : any`, no module or `"fields"` entries) is a `Region.pathCells y q` of a
plain array whose spine is distinct from `(x, p)` in `PlainElemCellsDisjoint`
heaps, then `PlainCellsDisj C E [.eff Φ] h₀` holds. -/
theorem plainCellsDisj_of_apart {C : ModuleRegion} {ρ : Env} {x : Nat} {p : List String}
    {c : Change} {Φ : Eff1} {h₀ : Heap}
    (hdflt : Φ.dflt = .any) (hmods : Φ.modules = []) (hflds : Φ.fields = none)
    (hapart : ∀ h, Reaches h₀ h →
      PlainElemCellsDisjoint h ∧
      (∀ e ∈ Φ.entries, ∃ y q u w s t ls₁ ls₂,
        e.1 = .pathCells y q ∧
        HeapKnowledge.readPath h (ρ x) p = some u ∧
        HeapKnowledge.readPath h (Φ.env y) q = some w ∧
        HeapKnowledge.descriptorSpine u = none ∧
        HeapKnowledge.descriptorSpine w = none ∧
        spineOf u = some s ∧ spineOf w = some t ∧
        h[s]? = some (.arr ls₁) ∧ h[t]? = some (.arr ls₂) ∧
        s ≠ t)) :
    PlainCellsDisj C [.eff ⟨[(Region.pathCells x p, c)], [], none, .keep, ρ⟩] [.eff Φ] h₀ := by
  have step : ∀ h, Reaches h₀ h → ∀ l,
      bnd [.eff ⟨[(Region.pathCells x p, c)], [], none, .keep, ρ⟩] h l ≠ .keep →
      bnd [.eff Φ] h l = .any := by
    intro h hr l hne
    have hm₁ : (Region.pathCells x p).mem ρ h l = true := by
      cases hm : (Region.pathCells x p).mem ρ h l with
      | true => rfl
      | false =>
        exfalso; apply hne
        simp [bnd, min_any_right, Atom.bnd, Eff1.bnd, Eff1.cov, hm]
    obtain ⟨hdisj, hent⟩ := hapart h hr
    have hfilt : (Φ.entries.filter fun e => e.1.mem Φ.env h l) = [] := by
      refine List.filter_eq_nil_iff.mpr fun e he => ?_
      obtain ⟨y, q, u, w, s, t, ls₁, ls₂, heq, hu, hw, hdu, hdw, hsu, hsw, hs₁, hs₂, hst⟩ := hent e he
      rw [heq]
      have hlu : (fieldsOf u).lookup arraySpineKey = some s := by simpa [spineOf] using hsu
      have hlw : (fieldsOf w).lookup arraySpineKey = some t := by simpa [spineOf] using hsw
      have hsc₁ : spineCells h u = ls₁ := by
        simp [spineCells, entriesAt, hlu, hdu, hs₁, spineEntries]
      have hsc₂ : spineCells h w = ls₂ := by
        simp [spineCells, entriesAt, hlw, hdw, hs₂, spineEntries]
      simp only [Region.mem, hu, hsc₁, List.contains_iff_mem] at hm₁
      simp only [Region.mem, hw, hsc₂]
      cases hc : ls₂.contains (some l) with
      | false => simp
      | true => exact False.elim (hdisj s t ls₁ ls₂ l hst hs₁ hs₂ hm₁ (List.contains_iff_mem.mp hc))
    simp [bnd, min_any_right, Atom.bnd, Eff1.bnd, Eff1.cov, hfilt, hmods, hflds, hdflt]
  exact ⟨fun l _ hne => step h₀ (Nat.le_refl _) l hne, fun h hr l _ _ hne => step h hr l hne⟩

/-- An `.extend` step producing an array spine `.arr ls'` comes from an array
spine `.arr ls` of length at most `ls'.length`. -/
theorem extend_arr_back {b : Nat} {v : Val} {ls' : List (Option Nat)}
    (h : Change.extend.Holds b v (.arr ls')) :
    ∃ ls, v = .arr ls ∧ ls.length ≤ ls'.length := by
  rcases h with hEq | hsc | hext
  · exact ⟨ls', hEq.symm, Nat.le_refl _⟩
  · simp [ScalarStep, isArr] at hsc
  · obtain ⟨ls, more, rfl, h2, _, hlen⟩ := hext
    cases h2
    exact ⟨ls, rfl, hlen.1⟩

/-- **Disjointness of `M.@state` from an external bound**: if `Ψ` has
`else : any`, no module or `"fields"` entries, and every concrete entry of `Ψ`
is rooted at an external slot satisfying `NoPriv` (on `HeapNoDup` heaps), then
`ModDisjoint M [.eff Ψ] h₀` holds. -/
theorem modDisjoint_of_external {C : ModuleRegion} (M : Mod C) (Ψ : Eff1) (h₀ : Heap)
    (hdflt : Ψ.dflt = .any) (hmods : Ψ.modules = []) (hflds : Ψ.fields = none)
    (hext : ∀ h, Reaches h₀ h →
      HeapNoDup h ∧
      ∀ e ∈ Ψ.entries, ∃ x, rootOf e.1 = some x ∧
        NoPriv (fun l => M.1.mem h l = true) (Ψ.env x) ∧ ObjNoDup (Ψ.env x)) :
    ModDisjoint M [.eff Ψ] h₀ := by
  intro a ha
  simp only [List.mem_singleton] at ha
  subst ha
  refine ⟨hdflt, hflds, fun h hr l hml => ⟨fun e he => ?_, fun e he => by rw [hmods] at he; cases he⟩⟩
  obtain ⟨hnd, hent⟩ := hext h hr
  obtain ⟨x, hrx, hnp, hxd⟩ := hent e he
  cases hmem : e.1.mem Ψ.env h l with
  | false => rfl
  | true => exact False.elim (closedOut_region_disjoint (M.1.closedOut h) hnd hnp hxd e.1 hrx hmem hml)

theorem maxOf_append (xs ys : List Change) : maxOf (xs ++ ys) = (maxOf xs).max (maxOf ys) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, maxOf, List.foldr_nil, Change.max, keep_le, ↓reduceIte]
  | cons x xs ih =>
    simp only [List.cons_append, maxOf, List.foldr_cons] at ih ⊢
    rw [ih, max_assoc]

theorem max_le_max {a b c d : Change} (h₁ : a.le c = true) (h₂ : b.le d = true) :
    (a.max b).le (c.max d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [Change.le, Change.rank, Change.max]

theorem eff1_bnd_of_keep {Φ : Eff1} (hdflt : Φ.dflt = .keep) (h : Heap) (l : Nat) :
    Φ.bnd h l = maxOf (Φ.cov h l) := by
  unfold Eff1.bnd
  cases Φ.cov h l with
  | nil => exact hdflt
  | cons _ _ => rfl

/-- Joining confined module regions into an anchored single-atom effect
(with `else : keep`) preserves `Anchored`. -/
theorem eff1_add_modules_anchored {C : ModuleRegion} {Φ : Eff1} {ms : List (ModuleRegion × Change)}
    {h₀ : Heap} (hdflt : Φ.dflt = .keep)
    (hsub : ∀ e ∈ ms, e.1.Sub C)
    (hanch : Anchored C [.eff Φ] h₀) :
    Anchored C [.eff { Φ with modules := Φ.modules ++ ms }] h₀ := by
  have hdflt' : ({ Φ with modules := Φ.modules ++ ms } : Eff1).dflt = .keep := hdflt
  have hΦ_cov : ∀ h l, ({ Φ with modules := Φ.modules ++ ms } : Eff1).cov h l =
      Φ.cov h l ++ (ms.filter fun e => e.1.mem h l).map Prod.snd := by
    intro h l
    simp only [Eff1.cov, List.filter_append, List.map_append, List.append_assoc]
  intro h hr
  obtain ⟨hold, hnew⟩ := hanch h hr
  constructor
  · intro l hlt
    have holdl := hold l hlt
    simp only [bnd, List.foldr_cons, List.foldr_nil, min_any_right, Atom.bnd] at holdl ⊢
    rw [eff1_bnd_of_keep hdflt, eff1_bnd_of_keep hdflt] at holdl
    rw [eff1_bnd_of_keep hdflt', eff1_bnd_of_keep hdflt', hΦ_cov, hΦ_cov, maxOf_append, maxOf_append]
    refine max_le_max holdl (maxOf_le_of_sub_all fun c hc => ?_)
    simp only [List.mem_map, List.mem_filter] at hc ⊢
    obtain ⟨e, ⟨he, hml⟩, rfl⟩ := hc
    exact ⟨e, ⟨he, e.1.freshGrowth h₀ h hr l hlt hml⟩, rfl⟩
  · intro l hle hnotC
    have hnewl := hnew l hle hnotC
    simp only [bnd, List.foldr_cons, List.foldr_nil, min_any_right, Atom.bnd] at hnewl ⊢
    have hms_empty : (ms.filter fun e => e.1.mem h l) = [] := by
      refine List.filter_eq_nil_iff.mpr fun e he => ?_
      cases hm : e.1.mem h l with
      | false => simp
      | true =>
        have := hsub e he h l hm
        rw [hnotC] at this; cases this
    simp only [Eff1.bnd, hΦ_cov, hms_empty, List.map_nil, List.append_nil]
    exact hnewl

/-- Joining confined module regions disjoint from `Ψ` into a single-atom
effect within `Ψ` preserves `Within`. -/
theorem eff1_add_modules_within {C : ModuleRegion} {Φ : Eff1} {ms : List (ModuleRegion × Change)}
    {Ψ : Eff} {h₀ : Heap} (hdflt : Φ.dflt = .keep)
    (hsub : ∀ e ∈ ms, e.1.Sub C)
    (hw : Within C [.eff Φ] Ψ h₀)
    (hdisj : ∀ e (he : e ∈ ms), ModDisjoint ⟨e.1, hsub e he⟩ Ψ h₀) :
    Within C [.eff { Φ with modules := Φ.modules ++ ms }] Ψ h₀ := by
  have hdflt' : ({ Φ with modules := Φ.modules ++ ms } : Eff1).dflt = .keep := hdflt
  have hΦ_cov : ∀ h l, ({ Φ with modules := Φ.modules ++ ms } : Eff1).cov h l =
      Φ.cov h l ++ (ms.filter fun e => e.1.mem h l).map Prod.snd := by
    intro h l
    simp only [Eff1.cov, List.filter_append, List.map_append, List.append_assoc]
  have mod_le : ∀ h, Reaches h₀ h → ∀ l,
      (maxOf ((ms.filter fun e => e.1.mem h l).map Prod.snd)).le (bnd Ψ h l) = true := by
    intro h hr l
    cases hfilt : ms.filter fun e => e.1.mem h l with
    | nil => exact keep_le _
    | cons e es =>
      have hmem : e ∈ ms ∧ e.1.mem h l = true := List.mem_filter.mp (hfilt ▸ List.mem_cons_self)
      have hd := hdisj e hmem.1
      have hΨ : ∀ (E : Eff), ModDisjoint ⟨e.1, hsub e hmem.1⟩ E h₀ → bnd E h l = .any := by
        intro E
        induction E with
        | nil => intro _; rfl
        | cons a rest ih =>
          intro hE
          have ha := hE a List.mem_cons_self
          have hrest := ih (fun a' ha' => hE a' (List.mem_cons_of_mem _ ha'))
          change (a.bnd h l).min (bnd rest h l) = .any
          rw [hrest, min_any_right]
          cases a with
          | old _ _ => exact False.elim ha
          | eff P =>
            obtain ⟨hdP, hfP, hno⟩ := ha
            obtain ⟨he', hm'⟩ := hno h hr l hmem.2
            have hf₁ : (P.entries.filter fun x => x.1.mem P.env h l) = [] :=
              List.filter_eq_nil_iff.mpr fun x hx => by simp [he' x hx]
            have hf₂ : (P.modules.filter fun x => x.1.mem h l) = [] :=
              List.filter_eq_nil_iff.mpr fun x hx => by simp [hm' x hx]
            simp [Atom.bnd, Eff1.bnd, Eff1.cov, hf₁, hf₂, hfP, hdP]
      rw [hΨ Ψ hd]
      exact le_any _
  have bnd_one : ∀ (P : Eff1) (h : Heap) (l : Nat), bnd [.eff P] h l = P.bnd h l := fun P h l => by
    simp [bnd, min_any_right, Atom.bnd]
  constructor
  · intro l hlt
    have hwl := hw.1 l hlt
    rw [bnd_one, eff1_bnd_of_keep hdflt] at hwl
    rw [bnd_one, eff1_bnd_of_keep hdflt', hΦ_cov, maxOf_append]
    exact max_le_iff.mpr ⟨hwl, mod_le h₀ (Nat.le_refl _) l⟩
  · intro h hr l hle hC
    have hwl := hw.2 h hr l hle hC
    rw [bnd_one, eff1_bnd_of_keep hdflt] at hwl
    rw [bnd_one, eff1_bnd_of_keep hdflt', hΦ_cov, maxOf_append]
    exact max_le_iff.mpr ⟨hwl, mod_le h hr l⟩

/-! ## The model and its rules -/

def semantics (C : ModuleRegion) (F : FieldClass) : Semantics where
  St := Heap
  Eff := Eff
  Ren := Ren
  Mod := Mod C
  Act := Act
  Reaches := Reaches
  Within := Within C
  Same := Same
  Anchored := Anchored C
  old h₀ := [.old h₀.length C]
  meet := fun (E F : Eff) => E ++ F
  rename := rename
  RenOk := RenOk
  modEff := modEff
  ModDisjoint := ModDisjoint
  fieldsEff := fieldsEff F
  FieldsDisjoint := FieldsDisjoint F
  PlainCellsDisj := PlainCellsDisj C
  ElemLenExtend := ElemLenExtend

theorem bound_rule (C : ModuleRegion) (F : FieldClass) : BoundRule (semantics C F) := by
  intro (θ : Eff) (Φ : Eff) (h₀ : Heap) (h : Heap) hw hr ha hs (h' : Heap) hact
  obtain ⟨hold, hnew⟩ := ha h hr
  refine act_mono (fun l _ => ?_) hact
  by_cases hl₀ : l < h₀.length
  · show (bnd θ h l).le (bnd Φ h l) = true
    rw [hs l hl₀]
    exact le_trans (hold l hl₀) (hw.1 l hl₀)
  · have hge : h₀.length ≤ l := Nat.le_of_not_lt hl₀
    cases hC : C.mem h l with
    | true => exact hw.2 h hr l hge hC
    | false =>
      show (bnd θ h l).le (bnd Φ h l) = true
      rw [hnew l hge hC]
      exact keep_le _

theorem anch_rule (C : ModuleRegion) (F : FieldClass) : AnchRule (semantics C F) := by
  intro (θ : Eff) (h₀ : Heap) (h : Heap) ha hr (h' : Heap) hact
  obtain ⟨-, hnew⟩ := ha h hr
  refine act_mono (fun l _ => ?_) hact
  show (bnd θ h l).le (bnd [.old h₀.length C] h l) = true
  by_cases hl₀ : l < h₀.length
  · simp only [bnd, List.foldr_cons, List.foldr_nil, min_any_right, Atom.bnd]
    simp [hl₀, le_any]
  · have hge : h₀.length ≤ l := Nat.le_of_not_lt hl₀
    cases hC : C.mem h l with
    | true =>
      simp only [bnd, List.foldr_cons, List.foldr_nil, min_any_right, Atom.bnd]
      simp [hC, le_any]
    | false =>
      rw [hnew l hge hC]
      exact keep_le _

theorem meet_rule (C : ModuleRegion) (F : FieldClass) : MeetRule (semantics C F) := by
  intro (E : Eff) (Φ₁ : Eff) (Φ₂ : Eff) (h : Heap) h₁ h₂ (h' : Heap) hact
  obtain ⟨hlen, a₁⟩ := h₁ h' hact
  obtain ⟨-, a₂⟩ := h₂ h' hact
  refine ⟨hlen, fun l v hv => ?_⟩
  obtain ⟨v', hv', hh₁⟩ := a₁ l v hv
  obtain ⟨v'', hv'', hh₂⟩ := a₂ l v hv
  have : v'' = v' := Option.some.inj (hv''.symm.trans hv')
  subst this
  refine ⟨v'', hv', ?_⟩
  show (bnd (Φ₁ ++ Φ₂) h l).Holds h.length v v''
  rw [bnd_append]
  exact ⟨hh₁, hh₂⟩

theorem inst_rule (C : ModuleRegion) (F : FieldClass) : InstRule (semantics C F) := by
  intro (σ : Ren) (E : Eff) (h : Heap) (h' : Heap) hσ hact
  refine ⟨hact.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', hh⟩ := hact.2 l v hv
  refine ⟨v', hv', ?_⟩
  show (bnd (rename σ E) h l).Holds h.length v v'
  rw [rename_bnd hσ]
  exact hh

theorem confined_rule (C : ModuleRegion) (F : FieldClass) : ConfinedRule (semantics C F) := by
  intro (M : Mod C) (h₀ : Heap)
  constructor
  · intro (h : Heap) hr
    constructor
    · intro l hlt
      show (bnd (modEff M) h l).le (bnd (modEff M) h₀ l) = true
      rw [modEff_bnd, modEff_bnd]
      cases hm : M.1.mem h l with
      | false => exact keep_le _
      | true =>
        rw [M.1.freshGrowth h₀ h hr l hlt hm]
        exact le_refl _
    · intro l _ hnotC
      show bnd (modEff M) h l = .keep
      rw [modEff_bnd]
      cases hm : M.1.mem h l with
      | false => rfl
      | true =>
        have hC := M.2 h l hm
        rw [hnotC] at hC; cases hC
  · intro (Φ : Eff) hdisj
    have bnd_any : ∀ h, Reaches h₀ h → ∀ l, M.1.mem h l = true → bnd Φ h l = .any := by
      intro h hr l hml
      induction Φ with
      | nil => rfl
      | cons a rest ih =>
        have ha := hdisj a List.mem_cons_self
        have hrest := ih (fun x hx => hdisj x (List.mem_cons_of_mem _ hx))
        change (a.bnd h l).min (bnd rest h l) = .any
        rw [hrest, min_any_right]
        cases a with
        | old _ _ => exact False.elim ha
        | eff Ψ =>
          obtain ⟨hdflt, hflds, hno⟩ := ha
          obtain ⟨he, hm⟩ := hno h hr l hml
          have hf₁ : (Ψ.entries.filter fun e => e.1.mem Ψ.env h l) = [] :=
            List.filter_eq_nil_iff.mpr fun e hmem => by simp [he e hmem]
          have hf₂ : (Ψ.modules.filter fun e => e.1.mem h l) = [] :=
            List.filter_eq_nil_iff.mpr fun e hmem => by simp [hm e hmem]
          simp [Atom.bnd, Eff1.bnd, Eff1.cov, hf₁, hf₂, hflds, hdflt]
    constructor
    · intro l _
      show (bnd (modEff M) h₀ l).le (bnd Φ h₀ l) = true
      rw [modEff_bnd]
      cases hm : M.1.mem h₀ l with
      | false => exact keep_le _
      | true =>
        rw [bnd_any h₀ (Nat.le_refl _) l hm]
        exact le_any _
    · intro h hr l _ _
      show (bnd (modEff M) h l).le (bnd Φ h l) = true
      rw [modEff_bnd]
      cases hm : M.1.mem h l with
      | false => exact keep_le _
      | true =>
        rw [bnd_any h hr l hm]
        exact le_any _

theorem callbackInv_rule (C : ModuleRegion) (F : FieldClass) : CallbackInvRule (semantics C F) := by
  intro Φ_own Φ_cb Ψ P h₀ h hp₀ hpres hstab hwOwn haOwn hwCb haCb hsteps
  suffices ∀ h₁ h₂, Semantics.Steps (semantics C F) Φ_own Φ_cb h₁ h₂ →
      Reaches h₀ h₁ → Same Ψ h₀ h₁ → P h₁ → P h₂ from
    this h₀ h hsteps (Nat.le_refl _) (fun _ _ => rfl) hp₀
  intro h₁ h₂ hst
  induction hst with
  | refl => intro _ _ hp; exact hp
  | @step a b _ hab _ ih =>
    intro hr hs hp
    have hactΨ : Act Ψ a b := by
      rcases hab with hown | hcb
      · exact bound_rule C F Φ_own Ψ h₀ a hwOwn hr haOwn hs b hown
      · exact bound_rule C F Φ_cb Ψ h₀ a hwCb hr haCb hs b hcb
    have hr' : Reaches h₀ b := Nat.le_trans hr hactΨ.1
    have hstab' : Same Ψ a b := hstab a b hactΨ
    have hs' : Same Ψ h₀ b := fun l hlt => (hstab' l (Nat.lt_of_lt_of_le hlt hr)).trans (hs l hlt)
    exact ih hr' hs' (hpres a b hp hactΨ)

theorem fieldsDisj_rule (C : ModuleRegion) (F : FieldClass) : FieldsDisjRule (semantics C F) := by
  intro (Φ : Eff) (h₀ : Heap) hdisj
  have bnd_any : ∀ h, Reaches h₀ h → ∀ l, F.mem h l = true → bnd Φ h l = .any := by
    intro h hr l hfl
    induction Φ with
    | nil => rfl
    | cons a rest ih =>
      have ha := hdisj a List.mem_cons_self
      have hrest := ih (fun x hx => hdisj x (List.mem_cons_of_mem _ hx))
      change (a.bnd h l).min (bnd rest h l) = .any
      rw [hrest, min_any_right]
      cases a with
      | old _ _ => exact False.elim ha
      | eff Ψ =>
        obtain ⟨hdflt, hflds, hno⟩ := ha
        obtain ⟨he, hm⟩ := hno h hr l hfl
        have hf₁ : (Ψ.entries.filter fun e => e.1.mem Ψ.env h l) = [] :=
          List.filter_eq_nil_iff.mpr fun e hmem => by simp [he e hmem]
        have hf₂ : (Ψ.modules.filter fun e => e.1.mem h l) = [] :=
          List.filter_eq_nil_iff.mpr fun e hmem => by simp [hm e hmem]
        simp [Atom.bnd, Eff1.bnd, Eff1.cov, hf₁, hf₂, hflds, hdflt]
  constructor
  · intro l _
    show (bnd (fieldsEff F) h₀ l).le (bnd Φ h₀ l) = true
    rw [fieldsEff_bnd]
    cases hf : F.mem h₀ l with
    | false => exact keep_le _
    | true =>
      rw [bnd_any h₀ (Nat.le_refl _) l hf]
      exact le_any _
  · intro h hr l _ _
    show (bnd (fieldsEff F) h l).le (bnd Φ h l) = true
    rw [fieldsEff_bnd]
    cases hf : F.mem h l with
    | false => exact keep_le _
    | true =>
      rw [bnd_any h hr l hf]
      exact le_any _

theorem plainCellsDisj_rule (C : ModuleRegion) (F : FieldClass) : PlainCellsDisjRule (semantics C F) := by
  intro (E : Eff) (Φ : Eff) (h₀ : Heap) hdisj
  constructor
  · intro l hlt
    show (bnd E h₀ l).le (bnd Φ h₀ l) = true
    by_cases hk : bnd E h₀ l = .keep
    · rw [hk]; exact keep_le _
    · rw [hdisj.1 l hlt hk]; exact le_any _
  · intro h hr l hge hC
    show (bnd E h l).le (bnd Φ h l) = true
    by_cases hk : bnd E h l = .keep
    · rw [hk]; exact keep_le _
    · rw [hdisj.2 h hr l hge hC hk]; exact le_any _

theorem elemLenExtend_rule (C : ModuleRegion) (F : FieldClass) : ElemLenExtendRule (semantics C F) := by
  intro (Φ : Eff) Q hex (h : Heap) (h' : Heap) hQ hact
  obtain ⟨P, ρ, x, p, hmono, rfl, hkeep⟩ := hex
  intro v c u s ls' hrp' hc' hu' hsu hs'
  obtain ⟨hrp, hc, hu, hslt, hle⟩ := hkeep h h' v c u s hact hrp' hc' hu' hsu
  have hvs : h[s]? = some h[s] := List.getElem?_eq_some_iff.mpr ⟨hslt, rfl⟩
  obtain ⟨vs', hvs', hholds⟩ := hact.2 s h[s] hvs
  rw [hs'] at hvs'; cases hvs'
  obtain ⟨ls, hls, hlen⟩ := extend_arr_back (hholds.mono hle)
  rw [hls] at hvs
  exact hmono ls.length ls'.length hlen (hQ v c u s ls hrp hc hu hsu hvs)

/-- **The idealised model meets all nine paper rules**, for any universe `C` of
confined module regions and role-typed field class `F`. -/
theorem model_rules (C : ModuleRegion) (F : FieldClass) : PaperRules (semantics C F) :=
  ⟨bound_rule C F, anch_rule C F, meet_rule C F, inst_rule C F, confined_rule C F,
   callbackInv_rule C F, fieldsDisj_rule C F, plainCellsDisj_rule C F, elemLenExtend_rule C F⟩

end Verification.Paper.EffectLanguage.Model
