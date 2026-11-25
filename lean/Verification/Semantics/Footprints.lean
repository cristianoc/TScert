import Verification.Semantics.Heaps

/-! # Footprints

A footprint says which old locations an action may change, and how. It is a
list of entries, each a region and a change; a location no entry covers keeps
its contents. Its meaning, `Post`, relates the heap its regions are read at to
a later heap, and constrains only the locations the first heap already had.
Fresh locations are unconstrained.

Composition across a sequence of actions rebases each action's regions to
the invocation's entry (`FootprintRebase`, `Post.compose_at`). Region containments that depend on the class of
a location's contents are justified by evidence valid at the heap the
including footprint is read at (`ClassOk`). -/
namespace Verification.HeapKnowledge

/-- The value a path of named data fields reads from a value: each step an
object owning the field as a string key, whose location the heap
allocates. -/
def readPath (h : Heap) : Val → List String → Option Val
  | v, [] => some v
  | .objAt fs _ _, f :: p => match fs.lookup (.str f) with
    | some l => match h[l]? with
      | some v => readPath h v p
      | none => none
    | none => none
  | _, _ :: _ => none

/-- The location of the spine of elements a value holds (the note *Tolerant
frames*, the spine a typed array's or an array's element facts read): an
array's spine, which its `[]` slot names and the calculus's array steps
read, or else a typed array's view spine, which its descriptor names. The
one spine selection of both forms. -/
def elementsOf : Val → Option Nat
  | .objAt fs c _ => match fs.lookup arraySpineKey, c with
    | some s, _ => some s
    | none, .view s _ _ => some s
    | none, _ => none
  | _ => none

/-- **The descriptor selects the spine of a typed array owning no `[]` slot.** -/
theorem elementsOf_view {fs : List (PropKey × Nat)} (hfs : fs.lookup arraySpineKey = none) (i s : Nat)
    (f : ViewFormat) (n : Nat) : elementsOf (.viewAt fs i s f n) = some s := by
  simp [elementsOf, hfs]

/-- The view spine a typed array's descriptor names. -/
def descriptorSpine : Val → Option Nat
  | .objAt _ (.view s _ _) _ => some s
  | _ => none

end Verification.HeapKnowledge

namespace Verification.Footprints

/-! ## Changes -/

/-- Whether a location's contents are `null` or `undefined`: what a lazy
initialization (`x ??= e`) replaces. -/
def nullish : Val → Bool
  | .nul | .undef => true
  | _ => false

/-- Whether contents are a spine: an array's, or a typed array's view spine
(the note *Tolerant frames*, §3, class `spine`). -/
def isArr : Val → Bool
  | .arr _ | .viewSpine .. => true
  | _ => false

def isObj : Val → Bool
  | .objAt .. => true
  | _ => false

/-- An initialization's step: a location holding `null` or `undefined` takes
a value that is no spine. -/
def InitStep (v v' : Val) : Prop := nullish v = true ∧ isArr v' = false

/-- A scalar's step: a location holding neither an object nor a spine takes a
value that is no spine. -/
def ScalarStep (v v' : Val) : Prop := isObj v = false ∧ isArr v = false ∧ isArr v' = false

theorem InitStep.scalar {v v' : Val} (h : InitStep v v') : ScalarStep v v' := by
  obtain ⟨hn, ha⟩ := h
  refine ⟨?_, ?_, ha⟩ <;> cases v <;> simp_all [nullish, isObj, isArr]

/-- How an entry may change a location's contents: not at all, by an
initialization of `null` or `undefined`, by a scalar's step (contents
neither an object nor a spine replaced by contents that are no spine), as an
array spine extended at its end (or by a scalar's step), as a spine that
keeps every dense prefix (or by a scalar's step), or arbitrarily. They form
the chain `keep ⊑ init ⊑ scalar ⊑ extend ⊑ grow ⊑ any`. -/
inductive Change where
  | keep
  | init
  | scalar
  | extend
  | grow
  | any
  deriving DecidableEq, Repr

/-- A change's rank in the chain. -/
def Change.rank : Change → Nat
  | .keep => 0
  | .init => 1
  | .scalar => 2
  | .extend => 3
  | .grow => 4
  | .any => 5

def Change.le (a b : Change) : Bool := a.rank ≤ b.rank

def Change.max (a b : Change) : Change := if a.le b then b else a

/-- The first `n` indices of a spine are present. -/
def DensePrefix (n : Nat) (ls : List (Option Nat)) : Prop :=
  n ≤ ls.length ∧ ∀ i, i < n → ls[i]? ≠ some none

/-- A spine at least as long, at most `maxArrayLength` long where it was. -/
def LengthGrows (ls ls' : List (Option Nat)) : Prop :=
  ls.length ≤ ls'.length ∧ (ls.length ≤ maxArrayLength → ls'.length ≤ maxArrayLength)

theorem LengthGrows.refl (ls : List (Option Nat)) : LengthGrows ls ls := ⟨Nat.le_refl _, id⟩

theorem LengthGrows.trans {ls ls' ls'' : List (Option Nat)} (h₁ : LengthGrows ls ls')
    (h₂ : LengthGrows ls' ls'') : LengthGrows ls ls'' :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun h => h₂.2 (h₁.2 h)⟩

/-- A view spine's step (the note *Tolerant frames*, §2, a write through a
typed array): a view spine replaced by a view spine of the same format and
length, every cell it newly lists fresh against the starting heap's length
`b`. It has no hole before or after, so it keeps every dense prefix. -/
def ViewStep (b : Nat) (v v' : Val) : Prop :=
  ∃ f cs cs', v = .viewSpine f cs ∧ v' = .viewSpine f cs' ∧ cs'.length = cs.length ∧
    ∀ c ∈ cs', c ∈ cs ∨ b ≤ c

/-- An array spine's extension at its end (what `push` does): the old spine
is a prefix of the new, every cell the extension lists fresh against the
starting heap's length `b`, the length within `maxArrayLength` where it
was. Every cell the old spine lists stays at its index. -/
def ExtendStep (b : Nat) (v v' : Val) : Prop :=
  ∃ ls more, v = .arr ls ∧ v' = .arr (ls ++ more) ∧ (∀ l, some l ∈ more → b ≤ l) ∧
    LengthGrows ls (ls ++ more)

/-- A change's relation on contents. `b` is the length of the heap the change
starts from: an extended spine keeps every entry it listed and lists only
fresh cells after them (`ExtendStep`); a growing spine gains no element location below it that it did
not already list, and gets no shorter; a growing view spine keeps its format
and length (`ViewStep`). -/
def Change.Holds : Change → Nat → Val → Val → Prop
  | .keep, _, v, v' => v' = v
  | .init, _, v, v' => v' = v ∨ InitStep v v'
  | .scalar, _, v, v' => v' = v ∨ ScalarStep v v'
  | .extend, b, v, v' => v' = v ∨ ScalarStep v v' ∨ ExtendStep b v v'
  | .grow, b, v, v' => v' = v ∨ (∃ ls ls', v = .arr ls ∧ v' = .arr ls' ∧
      (∀ n, DensePrefix n ls → DensePrefix n ls') ∧ (∀ l, some l ∈ ls' → some l ∈ ls ∨ b ≤ l) ∧
      LengthGrows ls ls') ∨ ScalarStep v v' ∨ ViewStep b v v'
  | .any, _, _, _ => True

theorem Change.Holds.refl (δ : Change) (b : Nat) (v : Val) : δ.Holds b v v := by
  cases δ <;> simp [Change.Holds]

/-- An extension is a grow step: it keeps every dense prefix, lists only
fresh cells beyond the old ones, and gets no shorter. -/
theorem ExtendStep.grow {b v v'} (h : ExtendStep b v v') : ∃ ls ls', v = .arr ls ∧ v' = .arr ls' ∧
    (∀ n, DensePrefix n ls → DensePrefix n ls') ∧ (∀ l, some l ∈ ls' → some l ∈ ls ∨ b ≤ l) ∧
    LengthGrows ls ls' := by
  obtain ⟨ls, more, rfl, rfl, hm, hg⟩ := h
  refine ⟨ls, ls ++ more, rfl, rfl, fun n hn => ⟨Nat.le_trans hn.1 hg.1, fun i hi => ?_⟩,
    fun l hl => (List.mem_append.mp hl).imp id (hm l), hg⟩
  rw [List.getElem?_append_left (Nat.lt_of_lt_of_le hi hn.1)]
  exact hn.2 i hi

theorem ExtendStep.lower {b b' v v'} (hb : b ≤ b') (h : ExtendStep b' v v') : ExtendStep b v v' := by
  obtain ⟨ls, more, rfl, rfl, hm, hg⟩ := h
  exact ⟨ls, more, rfl, rfl, fun l hl => Nat.le_trans hb (hm l hl), hg⟩

/-- A scalar's step is within `scalar`, so within `extend`. -/
theorem Change.scalar_le_extend {b v v'} (h : Change.scalar.Holds b v v') : Change.extend.Holds b v v' :=
  h.imp id .inl

/-- An extension is within `grow`. -/
theorem Change.extend_le_grow {b v v'} (h : Change.extend.Holds b v v') : Change.grow.Holds b v v' := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inl h.grow)

theorem Change.init_le_extend {b v v'} (h : Change.init.Holds b v v') : Change.extend.Holds b v v' :=
  Change.scalar_le_extend (h.imp id InitStep.scalar)

/-- A scalar's step is within `scalar`, so within `grow`. -/
theorem Change.scalar_le_grow {b v v'} (h : Change.scalar.Holds b v v') : Change.grow.Holds b v v' := by
  rcases h with h | h
  · exact .inl h
  · exact .inr (.inr (.inl h))

theorem Change.init_le_scalar {b v v'} (h : Change.init.Holds b v v') : Change.scalar.Holds b v v' :=
  h.imp id InitStep.scalar

theorem Change.init_le_grow {b v v'} (h : Change.init.Holds b v v') : Change.grow.Holds b v v' :=
  Change.scalar_le_grow (Change.init_le_scalar h)

theorem Change.Holds.mono {δ δ' : Change} {b v v'} (hle : δ.le δ' = true)
    (h : δ.Holds b v v') : δ'.Holds b v v' := by
  cases δ <;> cases δ' <;> simp only [Change.le, Change.rank] at hle <;> try omega
  all_goals first
    | exact h
    | trivial
    | exact Change.init_le_grow h
    | exact Change.init_le_scalar h
    | exact Change.init_le_extend h
    | exact Change.scalar_le_grow h
    | exact Change.scalar_le_extend h
    | exact Change.extend_le_grow h
    | exact .inl h

/-- A larger starting heap only strengthens what `grow` requires of new
element locations. -/
theorem Change.Holds.lower {δ : Change} {b b' v v'} (hb : b ≤ b')
    (h : δ.Holds b' v v') : δ.Holds b v v' := by
  cases δ with
  | keep | init | scalar | any => exact h
  | extend => exact h.imp id (Or.imp id (ExtendStep.lower hb))
  | grow =>
    rcases h with h | ⟨ls, ls', rfl, rfl, hd, hl, hg⟩ | h | ⟨f, cs, cs', rfl, rfl, hn, hc⟩
    · exact .inl h
    · exact .inr (.inl ⟨ls, ls', rfl, rfl, hd, fun l hm => (hl l hm).imp id (Nat.le_trans hb), hg⟩)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨f, cs, cs', rfl, rfl, hn, fun c hm => (hc c hm).imp id (Nat.le_trans hb)⟩))

private theorem InitStep.trans {v v' v'' : Val} (h₁ : InitStep v v') (h₂ : v'' = v' ∨ InitStep v' v'') :
    InitStep v v'' := by
  rcases h₂ with rfl | h₂
  · exact h₁
  · exact ⟨h₁.1, h₂.2⟩

private theorem ScalarStep.trans {v v' v'' : Val} (h₁ : ScalarStep v v') (h₂ : v'' = v' ∨ ScalarStep v' v'') :
    ScalarStep v v'' := by
  rcases h₂ with rfl | h₂
  · exact h₁
  · exact ⟨h₁.1, h₁.2.1, h₂.2.2⟩

theorem Change.Holds.trans {δ : Change} {b b' v v' v''} (hb : b ≤ b')
    (h₁ : δ.Holds b v v') (h₂ : δ.Holds b' v' v'') : δ.Holds b v v'' := by
  cases δ with
  | any => trivial
  | keep => simp only [Change.Holds] at h₁ h₂ ⊢; rw [h₂, h₁]
  | init =>
    rcases h₁ with rfl | h₁
    · exact h₂
    · exact .inr (h₁.trans h₂)
  | scalar =>
    rcases h₁ with rfl | h₁
    · exact h₂
    · exact .inr (h₁.trans h₂)
  | extend =>
    rcases h₁ with rfl | h₁ | ⟨ls, more, rfl, rfl, hm₁, hg₁⟩
    · exact h₂.lower hb
    · rcases h₂ with rfl | h₂ | ⟨_, _, he, -⟩
      · exact .inr (.inl h₁)
      · exact .inr (.inl (h₁.trans (.inr h₂)))
      · subst he; exact absurd h₁.2.2 (by simp [isArr])
    · rcases h₂ with rfl | h₂ | ⟨ms, more', hms, rfl, hm₂, hg₂⟩
      · exact .inr (.inr ⟨ls, more, rfl, rfl, hm₁, hg₁⟩)
      · exact absurd h₂.2.1 (by simp [isArr])
      · cases hms
        refine .inr (.inr ⟨ls, more ++ more', rfl, by rw [List.append_assoc], fun l hl => ?_,
          by rw [← List.append_assoc]; exact hg₁.trans hg₂⟩)
        rcases List.mem_append.mp hl with hl | hl
        · exact hm₁ l hl
        · exact Nat.le_trans hb (hm₂ l hl)
  | grow =>
    rcases h₁ with rfl | ⟨ls, ls', rfl, rfl, hd₁, hl₁, hg₁⟩ | h₁ | ⟨f, cs, cs', rfl, rfl, hn₁, hc₁⟩
    · exact h₂.lower hb
    · rcases h₂ with rfl | ⟨ms, ls'', hms, rfl, hd₂, hl₂, hg₂⟩ | h₂ | ⟨_, _, _, he, -⟩
      · exact .inr (.inl ⟨ls, ls', rfl, rfl, hd₁, hl₁, hg₁⟩)
      · cases hms
        refine .inr (.inl ⟨ls, ls'', rfl, rfl, fun n h => hd₂ n (hd₁ n h), fun l hm => ?_, hg₁.trans hg₂⟩)
        rcases hl₂ l hm with hm' | hle
        · exact hl₁ l hm'
        · exact .inr (Nat.le_trans hb hle)
      · exact absurd h₂.2.1 (by simp [isArr])
      · cases he
    · rcases h₂ with rfl | ⟨ms, ls'', hms, rfl, -, -, -⟩ | h₂ | ⟨_, _, _, he, -⟩
      · exact .inr (.inr (.inl h₁))
      · subst hms; exact absurd h₁.2.2 (by simp [isArr])
      · exact .inr (.inr (.inl (h₁.trans (.inr h₂))))
      · subst he; exact absurd h₁.2.2 (by simp [isArr])
    · rcases h₂ with rfl | ⟨_, _, he, -⟩ | h₂ | ⟨g, ds, cs'', he, rfl, hn₂, hc₂⟩
      · exact .inr (.inr (.inr ⟨f, cs, cs', rfl, rfl, hn₁, hc₁⟩))
      · cases he
      · exact absurd h₂.2.1 (by simp [isArr])
      · cases he
        refine .inr (.inr (.inr ⟨f, cs, cs'', rfl, rfl, hn₂.trans hn₁, fun c hm => ?_⟩))
        rcases hc₂ c hm with hm' | hle
        · exact hc₁ c hm'
        · exact .inr (Nat.le_trans hb hle)

theorem Change.le_max_left (a b : Change) : a.le (a.max b) = true := by
  cases a <;> cases b <;> rfl

theorem Change.le_max_right (a b : Change) : b.le (a.max b) = true := by
  cases a <;> cases b <;> rfl

theorem Change.max_cases (a b : Change) : a.max b = a ∨ a.max b = b := by
  unfold Change.max; split <;> simp

/-- Two changes in sequence are within their join. -/
theorem Change.Holds.seq {δ₁ δ₂ : Change} {b b' v v' v''} (hb : b ≤ b')
    (h₁ : δ₁.Holds b v v') (h₂ : δ₂.Holds b' v' v'') : (δ₁.max δ₂).Holds b v v'' :=
  (h₁.mono (Change.le_max_left δ₁ δ₂)).trans hb (h₂.mono (Change.le_max_right δ₁ δ₂))

/-! ## Selectors of categories

A class region (the note *Tolerant frames*, §3: $\mathsf{spines}$,
$\mathsf{views}$, $\mathsf{values}$) is named by a selector, a finite set of
the three categories (`Category`, which partition the roles); the named
ones are `values`, `arrays`, `views`, `spines` (arrays and views) and `all`.
Inclusion and disjointness are the set operations on the three categories,
so two selectors are disjoint exactly when no category is in both: `spines`
and `views` overlap. -/

/-- A finite set of categories (the note, §3: a class region names one). -/
structure Selector where
  value : Bool
  array : Bool
  view : Bool
  deriving DecidableEq, Repr

/-- Whether a selector names a category. -/
def Selector.has (s : Selector) : Category → Bool
  | .value => s.value
  | .array => s.array
  | .view => s.view

/-- Inclusion of selectors: every category of the first is in the second. -/
def Selector.sub (a b : Selector) : Bool :=
  (!a.value || b.value) && (!a.array || b.array) && (!a.view || b.view)

/-- Disjointness of selectors: no category is in both. -/
def Selector.disjoint (a b : Selector) : Bool :=
  !(a.value && b.value) && !(a.array && b.array) && !(a.view && b.view)

def Selector.union (a b : Selector) : Selector := ⟨a.value || b.value, a.array || b.array, a.view || b.view⟩

def Selector.inter (a b : Selector) : Selector := ⟨a.value && b.value, a.array && b.array, a.view && b.view⟩

/-- The note's $\mathsf{values}$: field, cell, element and identity locations. -/
@[simp] def Selector.values : Selector := ⟨true, false, false⟩

/-- The spines of arrays. -/
@[simp] def Selector.arrays : Selector := ⟨false, true, false⟩

/-- The note's $\mathsf{views}$: the view spines of typed arrays. -/
@[simp] def Selector.views : Selector := ⟨false, false, true⟩

/-- The note's $\mathsf{spines}$: array spines and view spines. -/
@[simp] def Selector.spines : Selector := ⟨false, true, true⟩

/-- Every location. -/
@[simp] def Selector.all : Selector := ⟨true, true, true⟩

/-- The selector of one category. -/
def Selector.of : Category → Selector
  | .value => .values
  | .array => .arrays
  | .view => .views

theorem Selector.ext_has {a b : Selector} (h : ∀ c, a.has c = b.has c) : a = b := by
  rcases a with ⟨av, aa, aw⟩
  rcases b with ⟨bv, ba, bw⟩
  have h1 := h .value; have h2 := h .array; have h3 := h .view
  simp only [Selector.has] at h1 h2 h3
  subst h1 h2 h3; rfl

theorem Selector.sub_iff {a b : Selector} : a.sub b = true ↔ ∀ c, a.has c = true → b.has c = true := by
  rcases a with ⟨av, aa, aw⟩
  rcases b with ⟨bv, ba, bw⟩
  constructor
  · intro h c; cases c <;> cases av <;> cases aa <;> cases aw <;> cases bv <;> cases ba <;> cases bw <;>
      simp_all [Selector.sub, Selector.has]
  · intro h
    have h1 := h .value; have h2 := h .array; have h3 := h .view
    cases av <;> cases aa <;> cases aw <;> cases bv <;> cases ba <;> cases bw <;>
      simp_all [Selector.sub, Selector.has]

theorem Selector.disjoint_iff {a b : Selector} :
    a.disjoint b = true ↔ ∀ c, a.has c = true → b.has c = false := by
  rcases a with ⟨av, aa, aw⟩
  rcases b with ⟨bv, ba, bw⟩
  constructor
  · intro h c; cases c <;> cases av <;> cases aa <;> cases aw <;> cases bv <;> cases ba <;> cases bw <;>
      simp_all [Selector.disjoint, Selector.has]
  · intro h
    have h1 := h .value; have h2 := h .array; have h3 := h .view
    cases av <;> cases aa <;> cases aw <;> cases bv <;> cases ba <;> cases bw <;>
      simp_all [Selector.disjoint, Selector.has]

/-- **Inclusion is sound**: a category of the first is one of the second. -/
theorem Selector.sub_sound {a b : Selector} (h : a.sub b = true) {c : Category} (hc : a.has c = true) :
    b.has c = true :=
  Selector.sub_iff.mp h c hc

/-- **Disjointness is sound**: no category is in both. -/
theorem Selector.disjoint_sound {a b : Selector} (h : a.disjoint b = true) {c : Category}
    (hc : a.has c = true) : b.has c = false :=
  Selector.disjoint_iff.mp h c hc

@[simp] theorem Selector.has_union (a b : Selector) (c : Category) :
    (a.union b).has c = (a.has c || b.has c) := by
  cases c <;> rfl

@[simp] theorem Selector.has_inter (a b : Selector) (c : Category) :
    (a.inter b).has c = (a.has c && b.has c) := by
  cases c <;> rfl

@[simp] theorem Selector.has_of (c e : Category) : (Selector.of c).has e = decide (c = e) := by
  cases c <;> cases e <;> rfl

@[simp] theorem Selector.has_all (c : Category) : Selector.all.has c = true := by
  cases c <;> rfl

/-- **The three categories partition**: each category is in exactly one of
`values`, `arrays` and `views`. -/
theorem Selector.partition (c : Category) :
    (Selector.values.has c && !Selector.arrays.has c && !Selector.views.has c) ||
    (!Selector.values.has c && Selector.arrays.has c && !Selector.views.has c) ||
    (!Selector.values.has c && !Selector.arrays.has c && Selector.views.has c) = true := by
  cases c <;> rfl

theorem Selector.values_disjoint_arrays : Selector.values.disjoint Selector.arrays = true := rfl
theorem Selector.values_disjoint_views : Selector.values.disjoint Selector.views = true := rfl
theorem Selector.arrays_disjoint_views : Selector.arrays.disjoint Selector.views = true := rfl
theorem Selector.values_disjoint_spines : Selector.values.disjoint Selector.spines = true := rfl

/-- `spines` is the union of `arrays` and `views`. -/
theorem Selector.spines_eq : Selector.spines = Selector.arrays.union Selector.views := rfl

theorem Selector.arrays_sub_spines : Selector.arrays.sub Selector.spines = true := rfl
theorem Selector.views_sub_spines : Selector.views.sub Selector.spines = true := rfl

/-- **`spines` and `views` overlap**: different selectors need not be
disjoint. -/
theorem Selector.spines_views_overlap : Selector.spines.disjoint Selector.views = false := rfl

/-- `all` is the union of the three categories. -/
theorem Selector.all_eq : Selector.all = (Selector.values.union Selector.arrays).union Selector.views := rfl

theorem Selector.sub_all (a : Selector) : a.sub Selector.all = true :=
  Selector.sub_iff.mpr fun c _ => Selector.has_all c

theorem Selector.sub_refl (a : Selector) : a.sub a = true := Selector.sub_iff.mpr fun _ h => h

theorem Selector.sub_trans {a b c : Selector} (h₁ : a.sub b = true) (h₂ : b.sub c = true) : a.sub c = true :=
  Selector.sub_iff.mpr fun _ hd => Selector.sub_sound h₂ (Selector.sub_sound h₁ hd)

/-- A selector disjoint from another is disjoint from every part of it. -/
theorem Selector.disjoint_of_sub {a b b' : Selector} (hd : a.disjoint b = true) (hs : b'.sub b = true) :
    a.disjoint b' = true :=
  Selector.disjoint_iff.mpr fun c hc => by
    cases hb' : b'.has c
    · rfl
    · have := Selector.sub_sound hs hb'
      rw [Selector.disjoint_sound hd hc] at this
      cases this

theorem Selector.disjoint_comm {a b : Selector} (h : a.disjoint b = true) : b.disjoint a = true :=
  Selector.disjoint_iff.mpr fun c hc => by
    cases ha : a.has c
    · rfl
    · rw [Selector.disjoint_sound h ha] at hc; cases hc

/-- The category a role has is in its category's selector and in no
selector disjoint from it. -/
theorem Selector.has_category (r : Role) : (Selector.of r.category).has r.category = true := by
  simp

/-! ## Class regions read the contents

A class region selects locations by their contents in the entry heap: a
selector selects a location whose contents' category (`contentsCategory`:
an array spine, a view spine, or a value) it names. The selector algebra is
sound for this selection (`Selector.selects_sub`,
`Selector.selects_disjoint`), and on a well-formed heap a location's
contents category is its role's (`Shaped.category`). -/

/-- Whether the class region of `S` selects a location holding `v`: whether
`S` names the category of `v` (`contentsCategory`). -/
def Selector.selects (S : Selector) (v : Val) : Bool :=
  S.has (contentsCategory v)

/-- **Selector inclusion is inclusion of the locations selected.** -/
theorem Selector.selects_sub {a b : Selector} (hab : a.sub b = true) {v : Val}
    (ha : a.selects v = true) : b.selects v = true :=
  Selector.sub_sound hab ha

/-- **Disjoint selectors select disjoint locations.** -/
theorem Selector.selects_disjoint {a b : Selector} (hab : a.disjoint b = true) {v : Val}
    (ha : a.selects v = true) : b.selects v = false :=
  Selector.disjoint_sound hab ha

/-- Contents are of the value category exactly when they are no spine. -/
theorem contentsCategory_value (v : Val) : (contentsCategory v = .value) ↔ isArr v = false := by
  cases v <;> simp [contentsCategory, isArr]

theorem Selector.selects_values (v : Val) : Selector.values.selects v = !isArr v := by
  cases v <;> rfl

theorem Selector.selects_spines (v : Val) : Selector.spines.selects v = isArr v := by
  cases v <;> rfl

/-- A selector naming no value category selects spines only. -/
theorem Selector.selects_noValue {c : Selector} {v : Val} (hc : c.value = false) (h : c.selects v = true) :
    isArr v = true := by
  unfold Selector.selects at h
  cases v <;> simp_all [contentsCategory, Selector.has, isArr]

/-- A selector naming neither spine category selects values only. -/
theorem Selector.selects_valueOnly {c : Selector} {v : Val} (ha : c.array = false) (hw : c.view = false)
    (h : c.selects v = true) : isArr v = false := by
  unfold Selector.selects at h
  cases v <;> simp_all [contentsCategory, Selector.has, isArr]

@[simp] theorem Selector.selects_values' (v : Val) :
    ({ value := true, array := false, view := false } : Selector).selects v = !isArr v := by
  cases v <;> rfl

@[simp] theorem Selector.selects_spines' (v : Val) :
    ({ value := false, array := true, view := true } : Selector).selects v = isArr v := by
  cases v <;> rfl

/-- Only `any` changes the category of a location's contents. -/
theorem Change.Holds.same_category {δ : Change} {b v v'} (hδ : δ ≠ .any)
    (h : δ.Holds b v v') : contentsCategory v' = contentsCategory v := by
  have scalar_class : ScalarStep v v' → contentsCategory v' = contentsCategory v := fun ⟨_, hv, hv'⟩ => by
    rw [(contentsCategory_value v').mpr hv', (contentsCategory_value v).mpr hv]
  cases δ with
  | any => exact absurd rfl hδ
  | keep => simp only [Change.Holds] at h; rw [h]
  | init =>
    rcases h with rfl | h
    · rfl
    · exact scalar_class h.scalar
  | scalar =>
    rcases h with rfl | h
    · rfl
    · exact scalar_class h
  | extend =>
    rcases h with rfl | h | ⟨_, _, rfl, rfl, _⟩
    · rfl
    · exact scalar_class h
    · rfl
  | grow =>
    rcases h with rfl | ⟨_, _, rfl, rfl, _, _⟩ | h | ⟨_, _, _, rfl, rfl, _⟩
    · rfl
    · rfl
    · exact scalar_class h
    · rfl

/-- Only `any` changes the class of a location's contents. -/
theorem Change.Holds.same_class {δ : Change} {b v v'} (hδ : δ ≠ .any)
    (h : δ.Holds b v v') (c : Selector) : c.selects v' = c.selects v := by
  simp only [Selector.selects, h.same_category hδ]

/-- On contents that are no spine, `grow` is `scalar`. -/
theorem Change.Holds.grow_value {b v v'} (h : Change.grow.Holds b v v') (hv : isArr v = false) :
    Change.scalar.Holds b v v' := by
  rcases h with h | ⟨_, _, rfl, _, _, _⟩ | h | ⟨_, _, _, rfl, _⟩
  · exact .inl h
  · simp [isArr] at hv
  · exact .inr h
  · simp [isArr] at hv

/-- On contents that are no spine, `extend` is `scalar`. -/
theorem Change.Holds.extend_value {b v v'} (h : Change.extend.Holds b v v') (hv : isArr v = false) :
    Change.scalar.Holds b v v' := by
  rcases h with h | h | ⟨_, _, rfl, _⟩
  · exact .inl h
  · exact .inr h
  · simp [isArr] at hv

/-- On contents that are no spine and neither `null` nor `undefined`,
`init` is `keep`. -/
theorem Change.Holds.init_defined {b v v'} (h : Change.init.Holds b v v') (hv : nullish v = false) :
    v' = v := by
  rcases h with h | h
  · exact h
  · rw [h.1] at hv; cases hv

/-- `keep` and `init` keep contents neither `null` nor `undefined`. -/
theorem Change.Holds.defined_kept {δ : Change} {b v v'} (hδ : δ.le .init = true) (h : δ.Holds b v v')
    (hn : nullish v = false) : v' = v := by
  cases δ with
  | keep => exact h
  | init => exact h.init_defined hn
  | _ => simp [Change.le, Change.rank] at hδ

/-- A change other than `any` keeps an object. -/
theorem Change.Holds.object_kept {δ : Change} {b v v'} (hδ : δ ≠ .any) (h : δ.Holds b v v')
    (ho : isObj v = true) : v' = v := by
  have hn : nullish v = false := by cases v <;> simp_all [isObj, nullish]
  have ha : isArr v = false := by cases v <;> simp_all [isObj, isArr]
  have hs : Change.scalar.Holds b v v' → v' = v := fun h => h.resolve_right fun hs => by
    rw [hs.1] at ho; cases ho
  cases δ with
  | keep => exact h
  | init => exact h.init_defined hn
  | scalar => exact hs h
  | extend => exact hs (h.extend_value ha)
  | grow => exact hs (h.grow_value ha)
  | any => exact absurd rfl hδ

/-- A change within `extend` on an array spine extends it at its end: every
entry it lists stays at its index, every cell after them is fresh, and its
length grows. -/
theorem Change.Holds.spine_extended {δ : Change} {b ls v'} (hδ : δ.le .extend = true)
    (h : δ.Holds b (.arr ls) v') :
    ∃ more, v' = .arr (ls ++ more) ∧ (∀ l, some l ∈ more → b ≤ l) ∧ LengthGrows ls (ls ++ more) := by
  rcases h.mono hδ with rfl | hs | ⟨ms, more, he, rfl, hm, hg⟩
  · exact ⟨[], by simp, by simp, by simpa using LengthGrows.refl ls⟩
  · exact absurd hs.2.1 (by simp [isArr])
  · cases he; exact ⟨more, rfl, hm, hg⟩

/-- A change within `extend` keeps every entry an array spine lists, at its
index. -/
theorem Change.Holds.extend_entry {δ : Change} {b ls v'} (hδ : δ.le .extend = true)
    (h : δ.Holds b (.arr ls) v') {i : Nat} (hi : i < ls.length) :
    ∃ ls', v' = .arr ls' ∧ ls'[i]? = ls[i]? := by
  obtain ⟨more, rfl, -, -⟩ := h.spine_extended hδ
  exact ⟨ls ++ more, rfl, List.getElem?_append_left hi⟩

/-- A change within `extend` keeps a view spine. -/
theorem Change.Holds.extend_view {δ : Change} {b f cs v'} (hδ : δ.le .extend = true)
    (h : δ.Holds b (.viewSpine f cs) v') : v' = .viewSpine f cs := by
  rcases h.mono hδ with h | hs | ⟨_, _, he, -⟩
  · exact h
  · exact absurd hs.2.1 (by simp [isArr])
  · cases he

/-- On a spine, `scalar` is `keep`. -/
theorem Change.Holds.scalar_spine {b ls v'} (h : Change.scalar.Holds b (.arr ls) v') : v' = .arr ls :=
  h.resolve_right fun hs => absurd hs.2.1 (by simp [isArr])

/-- On a spine, `init` is `keep`. -/
theorem Change.Holds.init_spine {b ls v'} (h : Change.init.Holds b (.arr ls) v') : v' = .arr ls :=
  h.init_defined rfl

/-- On any spine, an array's or a view spine, `scalar` is `keep`. -/
theorem Change.Holds.scalar_isArr {b v v'} (hv : isArr v = true) (h : Change.scalar.Holds b v v') : v' = v :=
  h.resolve_right fun hs => absurd hs.2.1 (by simp [hv])

/-- On any spine, `init` is `keep`. -/
theorem Change.Holds.init_isArr {b v v'} (hv : isArr v = true) (h : Change.init.Holds b v v') : v' = v :=
  h.init_defined (by cases v <;> simp_all [isArr, nullish])

def fieldsOf : Tm → List (PropKey × Nat)
  | .objAt fs _ _ => fs
  | _ => []

/-- The entries the spine at a location lists, at a heap (`spineEntries`). -/
def entriesAt (h : Heap) : Option Nat → List (Option Nat)
  | some s => (h[s]?.bind spineEntries).getD []
  | none => []

/-- The element locations a value's spines list, at a heap: those of the
spine its `[]` slot names, which the calculus's array steps read and write,
and those of the view spine its descriptor names, which a typed array's
element facts read (`HeapKnowledge.elementsOf`). A value is an array or a
typed array, so on a well-formed heap one of the two lists nothing. -/
def spineCells (h : Heap) (v : Tm) : List (Option Nat) :=
  entriesAt h ((fieldsOf v).lookup arraySpineKey) ++ entriesAt h (HeapKnowledge.descriptorSpine v)

/-- The cells of the spine a value selects are among its spine cells. -/
theorem elementsOf_entries_sub {h : Heap} {v : Tm} {s : Nat} (hs : HeapKnowledge.elementsOf v = some s)
    {o : Option Nat} (ho : o ∈ entriesAt h (some s)) : o ∈ spineCells h v := by
  cases v with
  | objAt fs c i =>
    simp only [HeapKnowledge.elementsOf] at hs
    cases hl : fs.lookup arraySpineKey with
    | some s' =>
      rw [hl] at hs; cases hs
      exact List.mem_append_left _ (by simpa [fieldsOf, hl] using ho)
    | none =>
      rw [hl] at hs
      cases c <;> simp at hs
      cases hs
      exact List.mem_append_right _ (by simpa [HeapKnowledge.descriptorSpine] using ho)
  | _ => simp [HeapKnowledge.elementsOf] at hs

/-- The field locations of a value: an object's own locations under every
key but the spine key `[]` (the note's $`\pi.\mathsf{fields}`$). -/
def fieldLocs (v : Tm) : List Nat :=
  ((fieldsOf v).filter fun kl => kl.1 != arraySpineKey).map Prod.snd

/-- A region names locations relative to the values of slots and to a heap.
`fields x` is the field locations of the object `x` holds (`fieldLocs`), its
spine slot excluded.
`field`, `fields` are timeless; `cells` and `cls` are read at a heap: `cls S`
is the class region of the selector `S`, read from the contents. A path
`p` reads own data fields from a slot's value (`HeapKnowledge.readPath`):
`path x p k` is the own field `k` of the object it reads, `pathFields x p` that
object's field locations and `pathCells x p` the element cells its spine
lists; a read that fails denotes no location, and at the empty path they are
`field`, `fields` and `cells`. `spine x p` selects the spine location of the
value the path reads (`HeapKnowledge.elementsOf`). `all` is every allocated
location. -/
inductive Region where
  | field (x : Nat) (k : PropKey)
  | fields (x : Nat)
  | cells (x : Nat)
  | cls (c : Selector)
  | all
  | path (x : Nat) (p : List String) (k : PropKey)
  | pathFields (x : Nat) (p : List String)
  | pathCells (x : Nat) (p : List String)
  /-- The spine location of the value the path reads (parity-interfaces I1,
  the selected spine): an array's or a typed array's
  (`HeapKnowledge.elementsOf`); a failed read or a value with no spine
  selects nothing. -/
  | spine (x : Nat) (p : List String)
  /-- The spine locations of the elements listed by the array or typed array
  the path reads from `x`: for every present element cell listed by `x.p`'s
  spine, the spine location (`HeapKnowledge.elementsOf`) of the value it holds. -/
  | elemSpines (x : Nat) (p : List String)
  deriving DecidableEq, Repr

def Region.mem (ρ : Env) (h : Heap) : Region → Nat → Bool
  | .field x k, l => (fieldsOf (ρ x)).lookup k == some l
  | .fields x, l => (fieldLocs (ρ x)).contains l
  | .cells x, l => (spineCells h (ρ x)).contains (some l)
  | .cls c, l => match h[l]? with
    | some v => c.selects v
    | none => false
  | .all, l => decide (l < h.length)
  | .path x p k, l => match HeapKnowledge.readPath h (ρ x) p with
    | some v => (fieldsOf v).lookup k == some l
    | none => false
  | .pathFields x p, l => match HeapKnowledge.readPath h (ρ x) p with
    | some v => (fieldLocs v).contains l
    | none => false
  | .pathCells x p, l => match HeapKnowledge.readPath h (ρ x) p with
    | some v => (spineCells h v).contains (some l)
    | none => false
  | .spine x p, l => match HeapKnowledge.readPath h (ρ x) p with
    | some v => HeapKnowledge.elementsOf v == some l
    | none => false
  | .elemSpines x p, l => match HeapKnowledge.readPath h (ρ x) p with
    | some v => (spineCells h v).any fun o => match o with
      | some c => match h[c]? with
        | some u => (fieldsOf u).lookup arraySpineKey == some l
        | none => false
      | none => false
    | none => false

@[simp] theorem Region.mem_path_nil (ρ : Env) (h : Heap) (x : Nat) (k : PropKey) (l : Nat) :
    (Region.path x [] k).mem ρ h l = (Region.field x k).mem ρ h l := by
  simp [Region.mem, HeapKnowledge.readPath]

@[simp] theorem Region.mem_pathFields_nil (ρ : Env) (h : Heap) (x : Nat) (l : Nat) :
    (Region.pathFields x []).mem ρ h l = (Region.fields x).mem ρ h l := by
  simp [Region.mem, HeapKnowledge.readPath]

@[simp] theorem Region.mem_pathCells_nil (ρ : Env) (h : Heap) (x : Nat) (l : Nat) :
    (Region.pathCells x []).mem ρ h l = (Region.cells x).mem ρ h l := by
  simp [Region.mem, HeapKnowledge.readPath]

theorem lookup_mem_snd {fs : List (PropKey × Nat)} {k : PropKey} {l : Nat}
    (h : fs.lookup k = some l) : l ∈ fs.map Prod.snd := by
  induction fs with
  | nil => simp at h
  | cons p fs ih =>
    rcases p with ⟨k', l'⟩
    by_cases hk : k = k'
    · subst hk; simp [List.lookup] at h; simp [h]
    · have : fs.lookup k = some l := by
        simpa [List.lookup, show (k == k') = false from by simpa using hk] using h
      simp [ih this]

theorem lookup_mem_pair {fs : List (PropKey × Nat)} {k : PropKey} {l : Nat}
    (h : fs.lookup k = some l) : (k, l) ∈ fs := by
  induction fs with
  | nil => simp at h
  | cons p fs ih =>
    rcases p with ⟨k', l'⟩
    by_cases hk : k = k'
    · subst hk; simp [List.lookup] at h; simp [h]
    · have : fs.lookup k = some l := by
        simpa [List.lookup, show (k == k') = false from by simpa using hk] using h
      simp [ih this]

/-- A field location is an own location. -/
theorem fieldLocs_own {v : Tm} {l : Nat} (h : l ∈ fieldLocs v) : l ∈ (fieldsOf v).map Prod.snd := by
  simp only [fieldLocs, List.mem_map, List.mem_filter] at h ⊢
  obtain ⟨kl, ⟨hm, -⟩, rfl⟩ := h
  exact ⟨kl, hm, rfl⟩

/-- An own location under a key other than the spine key is a field
location. -/
theorem lookup_mem_fieldLocs {v : Tm} {k : PropKey} {l : Nat} (h : (fieldsOf v).lookup k = some l)
    (hk : k ≠ arraySpineKey) : l ∈ fieldLocs v := by
  simp only [fieldLocs, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq]
  exact ⟨(k, l), ⟨lookup_mem_pair h, hk⟩, rfl⟩

/-- A field under a key other than the spine key is among the field
locations of its object. -/
theorem field_mem_fields {ρ h x k l} (hk : k ≠ arraySpineKey) (hm : (Region.field x k).mem ρ h l = true) :
    (Region.fields x).mem ρ h l = true := by
  simp only [Region.mem, beq_iff_eq] at hm
  simpa [Region.mem] using lookup_mem_fieldLocs hm hk

/-- A region every location of which holds a spine where it is read: a class
region of a selector naming no value category. -/
def spineOnly : Region → Bool
  | .cls c => !c.value
  | _ => false

theorem spineOnly_mem {r : Region} {σ : Env} {h : Heap} {l : Nat} {v : Val} (hs : spineOnly r = true)
    (hm : r.mem σ h l = true) (hv : h[l]? = some v) : isArr v = true := by
  cases r <;> simp only [spineOnly, Bool.false_eq_true] at hs
  case cls c =>
    simp only [Bool.not_eq_true'] at hs
    exact Selector.selects_noValue hs (by simpa [Region.mem, hv] using hm)

/-- The class a field key demands of its location's contents: an array
spine for the array spine key, a value otherwise (`SlotRole`). -/
def keyClass (k : PropKey) : Selector :=
  if k = arraySpineKey then .arrays else .values

/-- **The categories a region's locations may hold** at a well-formed state
(`Region.bound_sound`, `intrinsicClasses_ok`): a field or path field its key's
class, field locations and element cells values, a selected spine spines, a
class region its selector, and `all` every category. -/
def Region.cats : Region → Selector
  | .field _ k | .path _ _ k => keyClass k
  | .fields _ | .pathFields _ _ | .cells _ | .pathCells _ _ => .values
  | .spine _ _ => .spines
  | .elemSpines _ _ => .arrays
  | .cls S => S
  | .all => .all

/-- The `[]` slot of a value is the spine it selects. -/
theorem elementsOf_of_lookup_spine {v : Val} {l : Nat}
    (hs : (fieldsOf v).lookup arraySpineKey = some l) : HeapKnowledge.elementsOf v = some l := by
  cases v with
  | objAt fs c i => simp only [fieldsOf] at hs; simp [HeapKnowledge.elementsOf, hs]
  | _ => simp [fieldsOf] at hs

/-! ## Footprints and their meaning -/

abbrev Footprint := List (Region × Change)

/-- The change from `v` to `v'` at `l` is within one entry covering `l`, or
there is none. Equivalent to being within the join of the covering entries,
since changes form a chain and each is monotone. -/
def Allowed (Φ : Footprint) (ρ : Env) (h : Heap) (l : Nat) (v v' : Val) : Prop :=
  v' = v ∨ ∃ e ∈ Φ, e.1.mem ρ h l = true ∧ e.2.Holds h.length v v'

/-- The footprint's postcondition from the heap its regions are read at. -/
def Post (Φ : Footprint) (ρ : Env) (h h' : Heap) : Prop :=
  h.length ≤ h'.length ∧ ∀ l v, h[l]? = some v → ∃ v', h'[l]? = some v' ∧ Allowed Φ ρ h l v v'

/-- Every location of every region of `S`, read at `h`, changes from `h` to
`h'` at most by its entry's change: what a fact's support tolerates. Locations
outside `S` may change arbitrarily. -/
def Supported (S : Footprint) (ρ : Env) (h h' : Heap) : Prop :=
  ∀ e ∈ S, ∀ l v, e.1.mem ρ h l = true → h[l]? = some v →
    ∃ v', h'[l]? = some v' ∧ e.2.Holds h.length v v'

theorem Post.refl (Φ : Footprint) (ρ : Env) (h : Heap) : Post Φ ρ h h :=
  ⟨Nat.le_refl _, fun _ v hv => ⟨v, hv, .inl rfl⟩⟩

theorem Post.empty_iff {ρ : Env} {h h' : Heap} : Post [] ρ h h' ↔ h.IsPrefix h' := by
  constructor
  · rintro ⟨hlen, hall⟩
    refine List.prefix_iff_eq_take.mpr (List.ext_getElem? fun l => ?_)
    rw [List.getElem?_take]
    by_cases hl : l < h.length
    · obtain ⟨v, hv⟩ : ∃ v, h[l]? = some v := ⟨h[l], List.getElem?_eq_getElem hl⟩
      obtain ⟨v', hv', hal⟩ := hall l v hv
      rcases hal with rfl | ⟨e, he, -⟩
      · rw [hv, ite_eq_left hl, hv']
      · simp at he
    · rw [ite_eq_right hl, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
  · rintro ⟨t, rfl⟩
    refine ⟨by simp, fun l v hv => ⟨v, ?_, .inl rfl⟩⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1, hv]

/-- Class evidence: for any region, an optional selector that every allocated
location of the region holds contents of (`ClassOk`). -/
abbrev ClassEvidence := Region → Option Selector

/-- The class evidence stating no class. -/
def noClassEvidence : ClassEvidence := fun _ => none

/-- The class evidence stating a single field's class. -/
def fieldClass (x : Nat) (k : PropKey) (c : Selector) : ClassEvidence
  | .field y k' => if y = x ∧ k' = k then some c else none
  | _ => none

/-- **The intrinsic class evidence**: every region's locations lie in its
own categories (`Region.cats`). Holds at every well-formed state
(`intrinsicClasses_ok`, `Semantics/RegionBounds.lean`). -/
def intrinsicClasses : ClassEvidence := fun r => some r.cats

/-- The class evidence holds at `h` for every location `h` has. -/
def ClassOk (cl : ClassEvidence) (ρ : Env) (h : Heap) : Prop :=
  ∀ r c l, cl r = some c → r.mem ρ h l = true → l < h.length →
    (Region.cls c).mem ρ h l = true

theorem noClassEvidence_ok (ρ : Env) (h : Heap) : ClassOk noClassEvidence ρ h :=
  fun _ _ _ hc => nomatch hc

/-- **Region inclusion**: equal regions, every region in `all`, a field under a
key other than the spine key among its object's field locations (at slot or
path), a spine field in the selected spine, a class region in a larger one, and
any region in a class region its class evidence justifies. -/
def Region.sub (cl : ClassEvidence) (r s : Region) : Bool :=
  r == s || s == .all || match r, s with
    | .field x k, .fields y => x == y && k != arraySpineKey
    | .path x [] k, .fields y => x == y && k != arraySpineKey
    | .field x k, .pathFields y [] => x == y && k != arraySpineKey
    | .path x p k, .pathFields y q => x == y && p == q && k != arraySpineKey
    | .field x k, .spine y [] => x == y && k == arraySpineKey
    | .path x p k, .spine y q => x == y && p == q && k == arraySpineKey
    | .cls a, .cls b => a.sub b
    | r, .cls c => match cl r with
      | some c' => c'.sub c
      | none => false
    | _, _ => false

/-- **Selector inclusion is class-region inclusion.** -/
theorem class_subset_sound {a b : Selector} (hab : a.sub b = true) {ρ h l}
    (ha : (Region.cls a).mem ρ h l = true) : (Region.cls b).mem ρ h l = true := by
  simp only [Region.mem] at ha ⊢
  split at ha
  · exact Selector.selects_sub hab ha
  · cases ha

/-- **Selector disjointness excludes common membership.** Unequal selectors
need not be disjoint: `spines` and `views` overlap. -/
theorem class_disjoint_sound {a b : Selector} (hab : a.disjoint b = true) {ρ h l}
    (ha : (Region.cls a).mem ρ h l = true) : (Region.cls b).mem ρ h l = false := by
  simp only [Region.mem] at ha ⊢
  split at ha
  · exact Selector.selects_disjoint hab ha
  · rfl

theorem Region.sub_mem {cl : ClassEvidence} {r s : Region} {ρ h l}
    (hs : Region.sub cl r s = true) (hc : ClassOk cl ρ h) (hl : l < h.length)
    (hm : r.mem ρ h l = true) : s.mem ρ h l = true := by
  unfold Region.sub at hs
  simp only [Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with (rfl | rfl) | hs
  · exact hm
  · simpa [Region.mem] using hl
  · have byCl : ∀ c, (match cl r with | some c' => c'.sub c | none => false) = true →
        (Region.cls c).mem ρ h l = true := by
      intro c hcl
      cases hcr : cl r with
      | none => rw [hcr] at hcl; cases hcl
      | some c' => rw [hcr] at hcl; exact class_subset_sound hcl (hc r c' l hcr hm hl)
    cases r <;> cases s <;> (try simp only [Bool.false_eq_true] at hs)
    case field.fields x k y =>
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hs; obtain ⟨rfl, hk⟩ := hs
      exact field_mem_fields hk hm
    case path.fields x p k y =>
      cases p with
      | nil =>
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hs; obtain ⟨rfl, hk⟩ := hs
        exact field_mem_fields hk (by simpa using hm)
      | cons _ _ => simp only [Bool.false_eq_true] at hs
    case field.pathFields x k y q =>
      cases q with
      | nil =>
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hs; obtain ⟨rfl, hk⟩ := hs
        simpa using field_mem_fields hk hm
      | cons _ _ => simp only [Bool.false_eq_true] at hs
    case path.pathFields x p k y q =>
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hs
      obtain ⟨⟨rfl, rfl⟩, hk⟩ := hs
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv
        simp only [beq_iff_eq] at hm
        simpa using lookup_mem_fieldLocs hm hk
      · cases hm
    case field.spine x k y q =>
      cases q with
      | nil =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hs; obtain ⟨rfl, rfl⟩ := hs
        simp only [Region.mem, HeapKnowledge.readPath, beq_iff_eq] at hm ⊢
        exact elementsOf_of_lookup_spine hm
      | cons _ _ => simp only [Bool.false_eq_true] at hs
    case path.spine x p k y q =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv
        simp only [beq_iff_eq] at hm ⊢
        exact elementsOf_of_lookup_spine hm
      · cases hm
    case cls.cls a b => exact class_subset_sound hs hm
    case field.cls c => exact byCl c hs
    case fields.cls c => exact byCl c hs
    case cells.cls c => exact byCl c hs
    case all.cls c => exact byCl c hs
    case path.cls c => exact byCl c hs
    case pathFields.cls c => exact byCl c hs
    case pathCells.cls c => exact byCl c hs
    case spine.cls c => exact byCl c hs
    case elemSpines.cls c => exact byCl c hs

/-- Every entry of `Φ` lies in an entry of `Ψ` with at least its change. -/
def Footprint.le (cl : ClassEvidence) (Φ Ψ : Footprint) : Bool :=
  Φ.all fun e => Ψ.any fun f => e.2.le f.2 && Region.sub cl e.1 f.1

theorem Allowed.mono {cl Φ Ψ ρ h l v v'} (hle : Footprint.le cl Φ Ψ = true)
    (hc : ClassOk cl ρ h) (hl : l < h.length) (ha : Allowed Φ ρ h l v v') :
    Allowed Ψ ρ h l v v' := by
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact .inl rfl
  · obtain ⟨f, hf, hfe⟩ := List.any_eq_true.mp (List.all_eq_true.mp hle e he)
    simp only [Bool.and_eq_true] at hfe
    exact .inr ⟨f, hf, Region.sub_mem hfe.2 hc hl hm, hh.mono hfe.1⟩

/-- **Coverage.** A footprint within another, by inclusions justified by
class evidence valid at the heap they are read at, bounds less. -/
theorem Post.mono {cl : ClassEvidence} {Φ Ψ : Footprint} {ρ : Env} {h h' : Heap}
    (hle : Footprint.le cl Φ Ψ = true) (hc : ClassOk cl ρ h) (hp : Post Φ ρ h h') : Post Ψ ρ h h' :=
  ⟨hp.1, fun l v hv => by
    obtain ⟨v', hv', ha⟩ := hp.2 l v hv
    exact ⟨v', hv', Allowed.mono hle hc (List.getElem?_eq_some_iff.mp hv).1 ha⟩⟩

/-- Every element location the spine of `v` lists at `h`, below the entry
heap `h₀`'s length, the spine of `v` listed at `h₀`: **cell provenance**. -/
def CellsFrom (h₀ h : Heap) (v : Val) : Prop :=
  ∀ l, some l ∈ spineCells h v → l < h₀.length → some l ∈ spineCells h₀ v

/-- A spine location whose list at `h` keeps only cells of its list at `h₀`
and cells at or above `h₀`'s length gives cell provenance. -/
theorem CellsFrom.of_lists {h₀ h : Heap} {v : Val} {s : Nat}
    (hs : (fieldsOf v).lookup arraySpineKey = some s) (hd : HeapKnowledge.descriptorSpine v = none)
    (hl : ∀ ls', h[s]?.bind spineEntries = some ls' → ∀ m, some m ∈ ls' → m < h₀.length →
      ∃ ls, h₀[s]?.bind spineEntries = some ls ∧ some m ∈ ls) : CellsFrom h₀ h v := by
  intro m hm hm₀
  simp only [spineCells, hs, hd, entriesAt, List.append_nil] at hm ⊢
  cases hls' : h[s]?.bind spineEntries with
  | none => rw [hls'] at hm; simp at hm
  | some ls' =>
    rw [hls'] at hm
    obtain ⟨ls, hls, hm'⟩ := hl ls' hls' m hm hm₀
    simpa [hls] using hm'

/-- A change of the spine location within `grow` gives cell provenance. -/
theorem CellsFrom.of_change {δ : Change} {h₀ h : Heap} {v : Val} {s : Nat} {w w' : Val}
    (hδ : δ.le .grow = true) (hs : (fieldsOf v).lookup arraySpineKey = some s)
    (hd : HeapKnowledge.descriptorSpine v = none)
    (hw : h₀[s]? = some w) (hw' : h[s]? = some w') (hc : δ.Holds h₀.length w w') :
    CellsFrom h₀ h v := by
  have hg : Change.grow.Holds h₀.length w w' := hc.mono hδ
  refine CellsFrom.of_lists hs hd fun ls' hls' m hm hm₀ => ?_
  rw [hw'] at hls'
  simp only [Option.bind_some] at hls'
  rcases hg with rfl | ⟨ls, ls'', rfl, rfl, -, hl, -⟩ | hsc | ⟨f, cs, cs', rfl, rfl, -, hl⟩
  · exact ⟨ls', by rw [hw]; exact hls', hm⟩
  · cases hls'
    rcases hl m hm with hm' | hle
    · exact ⟨ls, by rw [hw]; rfl, hm'⟩
    · omega
  · cases w' <;> simp_all [isArr, spineEntries, ScalarStep]
  · cases hls'
    rcases hl m (by simpa using hm) with hm' | hle
    · exact ⟨cs.map some, by rw [hw]; rfl, by simpa using hm'⟩
    · omega

/-- A footprint letting the spine location of `v`, read at `h₀`, change at
most within `grow` gives cell provenance. -/
theorem CellsFrom.of_post {Φ : Footprint} {ρ : Env} {h₀ h : Heap} {v : Val} {s : Nat}
    (hp : Post Φ ρ h₀ h) (hs : (fieldsOf v).lookup arraySpineKey = some s)
    (hd : HeapKnowledge.descriptorSpine v = none) (hs₀ : s < h₀.length)
    (hΦ : ∀ e ∈ Φ, e.1.mem ρ h₀ s = true → e.2.le .grow = true) : CellsFrom h₀ h v := by
  obtain ⟨w, hw⟩ : ∃ w, h₀[s]? = some w := ⟨h₀[s], List.getElem?_eq_getElem hs₀⟩
  obtain ⟨w', hw', ha⟩ := hp.2 s w hw
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact CellsFrom.of_change (δ := .keep) rfl hs hd hw hw' rfl
  · exact CellsFrom.of_change (hΦ e he hm) hs hd hw hw' hh

def FreshOk (fresh : Nat → Bool) (ρ : Env) (b : Nat) : Prop :=
  ∀ x, fresh x = true → ∀ l, l ∈ (fieldsOf (ρ x)).map Prod.snd → b ≤ l

/-- **Class regions across an action**: a location of a class region after
an action of `Φp` was in it before, unless an entry of `Φp` at `any` covers it. -/
theorem cls_back {Φp ρ h₀ h l c} (hp : Post Φp ρ h₀ h) (hl : l < h₀.length)
    (hm : (Region.cls c).mem ρ h l = true) :
    (Region.cls c).mem ρ h₀ l = true ∨ ∃ e ∈ Φp, e.1.mem ρ h₀ l = true ∧ e.2 = .any := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, h₀[l]? = some v := ⟨h₀[l], List.getElem?_eq_getElem hl⟩
  obtain ⟨v, hv, ha⟩ := hp.2 l v₀ hv₀
  have hcv : c.selects v = true := by simpa [Region.mem, hv] using hm
  by_cases hc₀ : c.selects v₀ = true
  · exact .inl (by simp [Region.mem, hv₀, hc₀])
  · rcases ha with rfl | ⟨e, he, hem, hh⟩
    · exact absurd hcv hc₀
    · exact .inr ⟨e, he, hem, Classical.byContradiction fun hne =>
        hc₀ (by rw [← hh.same_class hne c]; exact hcv)⟩

/-! ## Decision procedures for controls

`postB` decides `Post` on concrete heaps; the controls in
`Tests/FootprintControls.lean` run it on the counterexamples. -/

/-- The length of the longest dense prefix. -/
def denseLen : List (Option Nat) → Nat
  | some _ :: ls => denseLen ls + 1
  | _ => 0

theorem densePrefix_iff : ∀ (ls : List (Option Nat)) (n : Nat), DensePrefix n ls ↔ n ≤ denseLen ls
  | [], n => by simp [DensePrefix, denseLen]
  | none :: ls, n => by
    simp only [DensePrefix, denseLen, List.length_cons]
    constructor
    · rintro ⟨-, hall⟩
      exact Classical.byContradiction fun hn => hall 0 (by omega) rfl
    · intro hn; refine ⟨by omega, fun i hi => by omega⟩
  | some l :: ls, n => by
    cases n with
    | zero => simp [DensePrefix]
    | succ n =>
      have ih := densePrefix_iff ls n
      simp only [DensePrefix, denseLen, List.length_cons] at ih ⊢
      constructor
      · rintro ⟨hlen, hall⟩
        exact Nat.succ_le_succ (ih.mp ⟨by omega, fun i hi => hall (i+1) (by omega)⟩)
      · intro hn
        obtain ⟨hlen, hall⟩ := ih.mpr (by omega)
        refine ⟨by omega, fun i hi => ?_⟩
        cases i with
        | zero => simp
        | succ i => simpa using hall i (by omega)

theorem preserves_dense_iff (ls ls' : List (Option Nat)) :
    (∀ n, DensePrefix n ls → DensePrefix n ls') ↔ denseLen ls ≤ denseLen ls' := by
  simp only [densePrefix_iff]
  exact ⟨fun h => h _ (Nat.le_refl _), fun h n hn => Nat.le_trans hn h⟩

/-- `grow` on an array's spine, decided. -/
def arrayGrowB (b : Nat) : Val → Val → Bool
  | .arr ls, .arr ls' => decide (denseLen ls ≤ denseLen ls') &&
      ((ls'.all fun o => match o with
        | some l => ls.contains (some l) || decide (b ≤ l)
        | none => true) &&
      (decide (ls.length ≤ ls'.length) && (!decide (ls.length ≤ maxArrayLength) || decide (ls'.length ≤ maxArrayLength))))
  | _, _ => false

/-- An array spine's extension at its end, decided (`ExtendStep`). -/
def extendStepB (b : Nat) : Val → Val → Bool
  | .arr ls, .arr ls' => ls'.take ls.length == ls && decide (ls.length ≤ ls'.length) &&
      ((ls'.drop ls.length).all fun o => match o with
        | some l => decide (b ≤ l)
        | none => true) &&
      (!decide (ls.length ≤ maxArrayLength) || decide (ls'.length ≤ maxArrayLength))
  | _, _ => false

/-- A view spine's step, decided (`ViewStep`). -/
def viewStepB (b : Nat) : Val → Val → Bool
  | .viewSpine f cs, .viewSpine f' cs' => f' == f && cs'.length == cs.length &&
      cs'.all fun c => cs.contains c || decide (b ≤ c)
  | _, _ => false

theorem arrayGrowB_iff (b : Nat) (v v' : Val) : arrayGrowB b v v' = true ↔
    ∃ ls ls', v = .arr ls ∧ v' = .arr ls' ∧
      (∀ n, DensePrefix n ls → DensePrefix n ls') ∧ (∀ l, some l ∈ ls' → some l ∈ ls ∨ b ≤ l) ∧
      LengthGrows ls ls' := by
  cases v <;> cases v' <;> simp [arrayGrowB]
  rename_i ls ls'
  rw [preserves_dense_iff]
  apply and_congr Iff.rfl
  unfold LengthGrows
  apply and_congr _ (by constructor <;> intro h <;> (try intro h') <;> omega)
  constructor
  · intro h l hl
    have := h (some l) hl
    simpa using this
  · intro h o ho
    cases o with
    | none => rfl
    | some l => simpa using h l ho

theorem extendStepB_iff (b : Nat) (v v' : Val) : extendStepB b v v' = true ↔ ExtendStep b v v' := by
  unfold ExtendStep
  cases v <;> cases v' <;> simp [extendStepB]
  rename_i ls ls'
  constructor
  · rintro ⟨⟨⟨ht, hlen⟩, hall⟩, hmax⟩
    have he : ls' = ls ++ ls'.drop ls.length := by
      conv => lhs; rw [← List.take_append_drop ls.length ls']
      rw [ht]
    refine ⟨ls'.drop ls.length, he, fun l hl => by simpa using hall (some l) hl, ?_⟩
    rw [← he]
    exact ⟨hlen, fun h => hmax.resolve_left (by omega)⟩
  · rintro ⟨more, rfl, hm, hg⟩
    refine ⟨⟨⟨by simp, by simp⟩, fun o ho => ?_⟩, ?_⟩
    · cases o with
      | none => rfl
      | some l => simpa using hm l (by simpa using ho)
    · by_cases h : ls.length ≤ maxArrayLength
      · exact .inr (hg.2 h)
      · exact .inl (by omega)

theorem viewStepB_iff (b : Nat) (v v' : Val) : viewStepB b v v' = true ↔ ViewStep b v v' := by
  unfold viewStepB ViewStep
  cases v <;> cases v' <;> simp
  rename_i f cs f' cs'
  constructor
  · rintro ⟨⟨rfl, hn⟩, hall⟩
    exact ⟨f', cs, ⟨rfl, rfl⟩, cs', ⟨rfl, rfl⟩, hn, fun c hc => by simpa using hall c hc⟩
  · rintro ⟨g, ds, ⟨rfl, rfl⟩, ds', ⟨rfl, rfl⟩, hn, hall⟩
    exact ⟨⟨rfl, hn⟩, fun c hc => by simpa using hall c hc⟩

def Change.holdsB : Change → Nat → Val → Val → Bool
  | .keep, _, v, v' => v' == v
  | .init, _, v, v' => v' == v || (nullish v && !isArr v')
  | .scalar, _, v, v' => v' == v || (!isObj v && (!isArr v && !isArr v'))
  | .extend, b, v, v' => v' == v || ((!isObj v && (!isArr v && !isArr v')) || extendStepB b v v')
  | .grow, b, v, v' => v' == v || (arrayGrowB b v v' ||
      ((!isObj v && (!isArr v && !isArr v')) || viewStepB b v v'))
  | .any, _, _, _ => true

theorem Change.holdsB_iff (δ : Change) (b : Nat) (v v' : Val) : δ.holdsB b v v' = true ↔ δ.Holds b v v' := by
  cases δ with
  | keep => simp [Change.holdsB, Change.Holds]
  | any => simp [Change.holdsB, Change.Holds]
  | init => simp [Change.holdsB, Change.Holds, InitStep]
  | scalar => simp [Change.holdsB, Change.Holds, ScalarStep]
  | extend =>
    simp only [Change.holdsB, Change.Holds, Bool.or_eq_true, beq_iff_eq]
    refine or_congr Iff.rfl (or_congr ?_ (extendStepB_iff b v v'))
    simp [ScalarStep]
  | grow =>
    simp only [Change.holdsB, Change.Holds, Bool.or_eq_true, beq_iff_eq]
    refine or_congr Iff.rfl (or_congr (arrayGrowB_iff b v v') (or_congr ?_ (viewStepB_iff b v v')))
    simp [ScalarStep]

def allowedB (Φ : Footprint) (ρ : Env) (h : Heap) (l : Nat) (v v' : Val) : Bool :=
  v' == v || Φ.any fun e => e.1.mem ρ h l && e.2.holdsB h.length v v'

def postB (Φ : Footprint) (ρ : Env) (h h' : Heap) : Bool :=
  decide (h.length ≤ h'.length) && (List.range h.length).all fun l =>
    match h[l]?, h'[l]? with
    | some v, some v' => allowedB Φ ρ h l v v'
    | _, _ => false

theorem allowedB_iff {Φ ρ h l v v'} : allowedB Φ ρ h l v v' = true ↔ Allowed Φ ρ h l v v' := by
  simp only [allowedB, Allowed, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
    Change.holdsB_iff]

theorem postB_iff {Φ ρ h h'} : postB Φ ρ h h' = true ↔ Post Φ ρ h h' := by
  simp only [postB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hlen, hall⟩
    refine ⟨hlen, fun l v hv => ?_⟩
    have hl := (List.getElem?_eq_some_iff.mp hv).1
    have := hall l hl
    rw [hv] at this
    rcases h'' : h'[l]? with _ | v'
    · rw [h''] at this; simp at this
    · rw [h''] at this; exact ⟨v', rfl, allowedB_iff.mp this⟩
  · rintro ⟨hlen, hall⟩
    refine ⟨hlen, fun l hl => ?_⟩
    have hv : h[l]? = some h[l] := List.getElem?_eq_getElem hl
    obtain ⟨v', hv', ha⟩ := hall l _ hv
    rw [hv, hv']
    exact allowedB_iff.mpr ha

end Verification.Footprints
