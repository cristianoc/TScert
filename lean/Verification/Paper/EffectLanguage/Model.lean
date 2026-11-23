import Verification.Paper.EffectLanguage.Rules
import Verification.Semantics.ClosedFootprints
import Verification.Semantics.SurvivalSeparation

/-! # An idealised model of the paper's effects

The effects of "An effect language for TScert" over the heaps, regions and
changes of `Verification.Semantics.Footprints`, and the proof that the model
meets the rules of `Rules.lean` (`model_rules`).

- A state is a heap. An effect of the paper with its `else` is an `Atom.eff`:
  entries, the change `dflt` of the locations no entry covers, and the
  environment its regions are read in, so that an instance is read in its
  caller's environment wherever it is used. `Atom.old n` is `{old: any}` for
  a call at a heap of length `n`.
- An effect is a list of atoms, their meet: each location's bound is the
  weakest of the atoms' bounds (`bnd`), and a transition is bounded when the
  heap only grows and every old location changes within its bound (`Act`).
- A run is a heap extension (`Reaches`). The model reads no admissibility:
  its transitions are every pair of heaps with the first a length-prefix of
  the second's locations.
-/

namespace Verification.Paper.EffectLanguage.Model

open Verification Footprints

/-- The largest of a list of changes, `keep` for none. -/
def maxOf (cs : List Change) : Change := cs.foldr Change.max .keep

/-- An effect of the paper without variables. -/
structure Eff1 where
  entries : Footprint
  dflt : Change
  env : Env

/-- An atom of an effect: an effect of the paper, or `{old: any}` at a call
whose heap has length `n`. -/
inductive Atom where
  | eff (Φ : Eff1)
  | old (n : Nat)

/-- An effect: the meet of its atoms. -/
abbrev Eff := List Atom

/-- The changes of the entries whose regions cover `l`. -/
def Eff1.cov (Φ : Eff1) (h : Heap) (l : Nat) : List Change :=
  (Φ.entries.filter fun e => e.1.mem Φ.env h l).map Prod.snd

/-- The change an effect allows at `l`: the largest covering entry's, or
`dflt` where no entry covers `l`. -/
def Eff1.bnd (Φ : Eff1) (h : Heap) (l : Nat) : Change :=
  match Φ.cov h l with
  | [] => Φ.dflt
  | cs => maxOf cs

def Atom.bnd : Atom → Heap → Nat → Change
  | .eff Φ, h, l => Φ.bnd h l
  | .old n, _, l => if l < n then .any else .keep

/-- The change an effect allows at `l`: the weakest of its atoms'. -/
def bnd (E : Eff) (h : Heap) (l : Nat) : Change :=
  E.foldr (fun a c => (a.bnd h l).min c) .any

/-- The transitions an effect bounds. -/
def Act (E : Eff) (h h' : Heap) : Prop :=
  h.length ≤ h'.length ∧
    ∀ l v, h[l]? = some v → ∃ v', h'[l]? = some v' ∧ (bnd E h l).Holds h.length v v'

def Reaches (h₀ h : Heap) : Prop := h₀.length ≤ h.length

def Within (E F : Eff) (h : Heap) : Prop :=
  ∀ l < h.length, (bnd E h l).le (bnd F h l) = true

def Same (E : Eff) (h₀ h : Heap) : Prop :=
  ∀ l < h₀.length, bnd E h l = bnd E h₀ l

/-- An instance anchored at a call at `h₀`: at every heap a run reaches, it
allows on the old locations what it allowed at the call, and keeps every
location allocated since. -/
def Anchored (E : Eff) (h₀ : Heap) : Prop :=
  ∀ h, Reaches h₀ h →
    (∀ l < h₀.length, bnd E h l = bnd E h₀ l) ∧ ∀ l, h₀.length ≤ l → bnd E h l = .keep

/-- A renaming to the caller: the caller's slot of each callee position,
and the caller's environment. -/
abbrev Ren := (Nat → Option Nat) × Env

def renAtom (σ : Ren) : Atom → Atom
  | .eff Φ => .eff ⟨Φ.entries.renameM σ.1, Φ.dflt, σ.2⟩
  | .old n => .old n

def rename (σ : Ren) (E : Eff) : Eff := E.map (renAtom σ)

/-- Every position of each effect atom is an argument's slot holding that
position's value. -/
def RenOk (σ : Ren) (E : Eff) : Prop :=
  ∀ Φ, Atom.eff Φ ∈ E → ∀ i, ∃ j, σ.1 i = some j ∧ σ.2 j = Φ.env i

/-! ## Lemmas -/

theorem keep_le (c : Change) : Change.keep.le c = true := by
  cases c <;> rfl

theorem le_any (c : Change) : c.le .any = true := by
  cases c <;> rfl

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
  induction r with
  | inCls r c ih => simp only [Region.renameM, Region.mem, ih]
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
    | old n => rfl

/-! ## The model and its rules -/

def semantics : Semantics where
  St := Heap
  Eff := Eff
  Ren := Ren
  Act := Act
  Reaches := Reaches
  Within := Within
  Same := Same
  Anchored := Anchored
  old h₀ := [.old h₀.length]
  meet := fun (E F : Eff) => E ++ F
  rename := rename
  RenOk := RenOk

theorem bound_rule : BoundRule semantics := by
  intro (θ : Eff) (Φ : Eff) (h₀ : Heap) (h : Heap) hw hr ha hs (h' : Heap) hact
  obtain ⟨hold, hnew⟩ := ha h hr
  refine act_mono (fun l hl => ?_) hact
  by_cases hl₀ : l < h₀.length
  · show (bnd θ h l).le (bnd Φ h l) = true
    rw [hold l hl₀, hs l hl₀]
    exact hw l hl₀
  · show (bnd θ h l).le (bnd Φ h l) = true
    rw [hnew l (Nat.le_of_not_lt hl₀)]
    exact keep_le _

theorem anch_rule : AnchRule semantics := by
  intro (θ : Eff) (h₀ : Heap) (h : Heap) ha hr (h' : Heap) hact
  obtain ⟨-, hnew⟩ := ha h hr
  refine act_mono (fun l _ => ?_) hact
  show (bnd θ h l).le (bnd [.old h₀.length] h l) = true
  by_cases hl₀ : l < h₀.length
  · simp only [bnd, List.foldr_cons, List.foldr_nil, Atom.bnd, hl₀, ↓reduceIte]
    exact le_any _
  · rw [hnew l (Nat.le_of_not_lt hl₀)]
    exact keep_le _

theorem meet_rule : MeetRule semantics := by
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

theorem inst_rule : InstRule semantics := by
  intro (σ : Ren) (E : Eff) (h : Heap) (h' : Heap) hσ hact
  refine ⟨hact.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', hh⟩ := hact.2 l v hv
  refine ⟨v', hv', ?_⟩
  show (bnd (rename σ E) h l).Holds h.length v v'
  rw [rename_bnd hσ]
  exact hh

/-- **The idealised model meets the paper's rules.** -/
theorem model_rules : PaperRules semantics :=
  ⟨bound_rule, anch_rule, meet_rule, inst_rule⟩

end Verification.Paper.EffectLanguage.Model
