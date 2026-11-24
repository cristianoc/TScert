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
  | .field x _ | .fields x | .cells x | .path x _ _ | .pathFields x _ | .pathCells x _ | .spine x _ => some x
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

/-- **Module disjointness for declared reach (`x.**_T`)**: any location
reachable along arbitrary public field, spine, and element paths from an
external root `v` (`NoPriv`) lies outside every confined module region `M`. -/
theorem closedOut_reach_disjoint (M : ModuleRegion) {h : Heap} {v : Val} {l : Nat}
    (hnp : NoPriv (fun loc => M.mem h loc = true) v) (hr : Reaches allC h v l) :
    M.mem h l = false := by
  cases hm : M.mem h l with
  | false => rfl
  | true => exact False.elim ((M.closedOut h).not_reaches hnp hr hm)

/-! ## Effects and bounds -/

/-- The largest of a list of changes, `keep` for none. -/
def maxOf (cs : List Change) : Change := cs.foldr Change.max .keep

/-- An effect of the paper without variables: concrete regions, confined
module-state regions `M.@state`, a default `else` change, and the environment
its concrete regions read. -/
structure Eff1 where
  entries : Footprint
  modules : List (ModuleRegion × Change) := []
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

/-- The changes of the concrete and module entries whose regions cover `l`. -/
def Eff1.cov (Φ : Eff1) (h : Heap) (l : Nat) : List Change :=
  (Φ.entries.filter fun e => e.1.mem Φ.env h l).map Prod.snd ++
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
  | .eff Φ => .eff ⟨Φ.entries.renameM σ.1, Φ.modules, Φ.dflt, σ.2⟩
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
  [.eff ⟨[], [(M.1, .any)], .keep, fun _ => .undef⟩]

/-- `M.@state` is disjoint from `Φ` from `h₀` onward when every atom of `Φ` is
an effect with `else : any` whose entries never cover `M.@state` at any
reachable heap. -/
def ModDisjoint {C : ModuleRegion} (M : Mod C) (Φ : Eff) (h₀ : Heap) : Prop :=
  ∀ a ∈ Φ, match a with
    | .eff Ψ =>
      Ψ.dflt = .any ∧
      ∀ h, Reaches h₀ h → ∀ l, M.1.mem h l = true →
        (∀ e ∈ Ψ.entries, e.1.mem Ψ.env h l = false) ∧
        (∀ e ∈ Ψ.modules, e.1.mem h l = false)
    | .old _ _ => False

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
  | field x | fields x | cells x | path x | pathFields x | pathCells x | spine x =>
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

/-- **Disjointness of `M.@state` from an external bound**: if `Ψ` has
`else : any`, no module entries, and every concrete entry of `Ψ` is rooted at
an external slot satisfying `NoPriv` (on `HeapNoDup` heaps), then
`ModDisjoint M [.eff Ψ] h₀` holds. -/
theorem modDisjoint_of_external {C : ModuleRegion} (M : Mod C) (Ψ : Eff1) (h₀ : Heap)
    (hdflt : Ψ.dflt = .any) (hmods : Ψ.modules = [])
    (hext : ∀ h, Reaches h₀ h →
      HeapNoDup h ∧
      ∀ e ∈ Ψ.entries, ∃ x, rootOf e.1 = some x ∧
        NoPriv (fun l => M.1.mem h l = true) (Ψ.env x) ∧ ObjNoDup (Ψ.env x)) :
    ModDisjoint M [.eff Ψ] h₀ := by
  intro a ha
  simp only [List.mem_singleton] at ha
  subst ha
  refine ⟨hdflt, fun h hr l hml => ⟨fun e he => ?_, fun e he => by rw [hmods] at he; cases he⟩⟩
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
            obtain ⟨hdP, hno⟩ := ha
            obtain ⟨he', hm'⟩ := hno h hr l hmem.2
            have hf₁ : (P.entries.filter fun x => x.1.mem P.env h l) = [] :=
              List.filter_eq_nil_iff.mpr fun x hx => by simp [he' x hx]
            have hf₂ : (P.modules.filter fun x => x.1.mem h l) = [] :=
              List.filter_eq_nil_iff.mpr fun x hx => by simp [hm' x hx]
            simp [Atom.bnd, Eff1.bnd, Eff1.cov, hf₁, hf₂, hdP]
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

def semantics (C : ModuleRegion) : Semantics where
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

theorem bound_rule (C : ModuleRegion) : BoundRule (semantics C) := by
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

theorem anch_rule (C : ModuleRegion) : AnchRule (semantics C) := by
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

theorem meet_rule (C : ModuleRegion) : MeetRule (semantics C) := by
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

theorem inst_rule (C : ModuleRegion) : InstRule (semantics C) := by
  intro (σ : Ren) (E : Eff) (h : Heap) (h' : Heap) hσ hact
  refine ⟨hact.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', hh⟩ := hact.2 l v hv
  refine ⟨v', hv', ?_⟩
  show (bnd (rename σ E) h l).Holds h.length v v'
  rw [rename_bnd hσ]
  exact hh

theorem confined_rule (C : ModuleRegion) : ConfinedRule (semantics C) := by
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
          obtain ⟨hdflt, hno⟩ := ha
          obtain ⟨he, hm⟩ := hno h hr l hml
          have hf₁ : (Ψ.entries.filter fun e => e.1.mem Ψ.env h l) = [] :=
            List.filter_eq_nil_iff.mpr fun e hmem => by simp [he e hmem]
          have hf₂ : (Ψ.modules.filter fun e => e.1.mem h l) = [] :=
            List.filter_eq_nil_iff.mpr fun e hmem => by simp [hm e hmem]
          simp [Atom.bnd, Eff1.bnd, Eff1.cov, hf₁, hf₂, hdflt]
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

/-- **The idealised model meets all five paper rules**, for any universe `C` of
confined module regions. -/
theorem model_rules (C : ModuleRegion) : PaperRules (semantics C) :=
  ⟨bound_rule C, anch_rule C, meet_rule C, inst_rule C, confined_rule C⟩

end Verification.Paper.EffectLanguage.Model
