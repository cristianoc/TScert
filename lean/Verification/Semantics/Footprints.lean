import Verification.Semantics.Heaps

/-! # Footprints

A footprint says which old locations an action may change, and how. It is a
list of entries, each a region and a change; a location no entry covers keeps
its contents. Its meaning, `Post`, relates the heap its regions are read at to
a later heap, and constrains only the locations the first heap already had.
Fresh locations are unconstrained.

Composition across a sequence of actions reads each action's regions at the
heap it starts in, and transports them to the invocation's entry heap
(`transport`, `Post.compose`). Region containments that depend on the class of
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

end Verification.HeapKnowledge

namespace Verification.Footprints

/-! ## Changes -/

/-- Whether a location's contents are `null` or `undefined`: what a lazy
initialization (`x ??= e`) replaces. -/
def nullish : Val → Bool
  | .nul | .undef => true
  | _ => false

def isArr : Val → Bool
  | .arr _ => true
  | _ => false

def isObj : Val → Bool
  | .objAt .. => true
  | _ => false

/-- An initialization's step: a location holding `null` or `undefined` takes
a value that is no store. -/
def InitStep (v v' : Val) : Prop := nullish v = true ∧ isArr v' = false

/-- A scalar's step: a location holding neither an object nor a store takes a
value that is no store. -/
def ScalarStep (v v' : Val) : Prop := isObj v = false ∧ isArr v = false ∧ isArr v' = false

theorem InitStep.scalar {v v' : Val} (h : InitStep v v') : ScalarStep v v' := by
  obtain ⟨hn, ha⟩ := h
  refine ⟨?_, ?_, ha⟩ <;> cases v <;> simp_all [nullish, isObj, isArr]

/-- How an entry may change a location's contents: not at all, by an
initialization of `null` or `undefined`, by a scalar's step (contents
neither an object nor a store replaced by contents that are no store), as a
store that keeps every dense prefix (or by a scalar's step), or arbitrarily.
They form the chain `keep ⊑ init ⊑ scalar ⊑ grow ⊑ any`. -/
inductive Change where
  | keep
  | init
  | scalar
  | grow
  | any
  deriving DecidableEq, Repr

/-- A change's rank in the chain. -/
def Change.rank : Change → Nat
  | .keep => 0
  | .init => 1
  | .scalar => 2
  | .grow => 3
  | .any => 4

def Change.le (a b : Change) : Bool := a.rank ≤ b.rank

def Change.max (a b : Change) : Change := if a.le b then b else a

/-- The first `n` indices of a store are present. -/
def DensePrefix (n : Nat) (ls : List (Option Nat)) : Prop :=
  n ≤ ls.length ∧ ∀ i, i < n → ls[i]? ≠ some none

/-- A store at least as long, at most `maxArrayLength` long where it was. -/
def LengthGrows (ls ls' : List (Option Nat)) : Prop :=
  ls.length ≤ ls'.length ∧ (ls.length ≤ maxArrayLength → ls'.length ≤ maxArrayLength)

theorem LengthGrows.refl (ls : List (Option Nat)) : LengthGrows ls ls := ⟨Nat.le_refl _, id⟩

theorem LengthGrows.trans {ls ls' ls'' : List (Option Nat)} (h₁ : LengthGrows ls ls')
    (h₂ : LengthGrows ls' ls'') : LengthGrows ls ls'' :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun h => h₂.2 (h₁.2 h)⟩

/-- A change's relation on contents. `b` is the length of the heap the change
starts from: a growing store gains no element location below it that it did
not already list, and gets no shorter. -/
def Change.Holds : Change → Nat → Val → Val → Prop
  | .keep, _, v, v' => v' = v
  | .init, _, v, v' => v' = v ∨ InitStep v v'
  | .scalar, _, v, v' => v' = v ∨ ScalarStep v v'
  | .grow, b, v, v' => v' = v ∨ (∃ ls ls', v = .arr ls ∧ v' = .arr ls' ∧
      (∀ n, DensePrefix n ls → DensePrefix n ls') ∧ (∀ l, some l ∈ ls' → some l ∈ ls ∨ b ≤ l) ∧
      LengthGrows ls ls') ∨ ScalarStep v v'
  | .any, _, _, _ => True

theorem Change.Holds.refl (δ : Change) (b : Nat) (v : Val) : δ.Holds b v v := by
  cases δ <;> simp [Change.Holds]

/-- A scalar's step is within `scalar`, so within `grow`. -/
theorem Change.scalar_le_grow {b v v'} (h : Change.scalar.Holds b v v') : Change.grow.Holds b v v' := by
  rcases h with h | h
  · exact .inl h
  · exact .inr (.inr h)

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
    | exact Change.scalar_le_grow h
    | exact .inl h

/-- A larger starting heap only strengthens what `grow` requires of new
element locations. -/
theorem Change.Holds.lower {δ : Change} {b b' v v'} (hb : b ≤ b')
    (h : δ.Holds b' v v') : δ.Holds b v v' := by
  cases δ with
  | keep | init | scalar | any => exact h
  | grow =>
    rcases h with h | ⟨ls, ls', rfl, rfl, hd, hl, hg⟩ | h
    · exact .inl h
    · exact .inr (.inl ⟨ls, ls', rfl, rfl, hd, fun l hm => (hl l hm).imp id (Nat.le_trans hb), hg⟩)
    · exact .inr (.inr h)

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
  | grow =>
    rcases h₁ with rfl | ⟨ls, ls', rfl, rfl, hd₁, hl₁, hg₁⟩ | h₁
    · exact h₂.lower hb
    · rcases h₂ with rfl | ⟨ms, ls'', hms, rfl, hd₂, hl₂, hg₂⟩ | h₂
      · exact .inr (.inl ⟨ls, ls', rfl, rfl, hd₁, hl₁, hg₁⟩)
      · cases hms
        refine .inr (.inl ⟨ls, ls'', rfl, rfl, fun n h => hd₂ n (hd₁ n h), fun l hm => ?_, hg₁.trans hg₂⟩)
        rcases hl₂ l hm with hm' | hle
        · exact hl₁ l hm'
        · exact .inr (Nat.le_trans hb hle)
      · exact absurd h₂.2.1 (by simp [isArr])
    · rcases h₂ with rfl | ⟨ms, ls'', hms, rfl, -, -, -⟩ | h₂
      · exact .inr (.inr h₁)
      · subst hms; exact absurd h₁.2.2 (by simp [isArr])
      · exact .inr (.inr (h₁.trans (.inr h₂)))

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

/-! ## Classes of contents and regions -/

/-- The two classes of a location's contents: an array store, or anything
else. -/
inductive Cls where
  | store
  | value
  deriving DecidableEq, Repr

def Cls.has : Cls → Val → Bool
  | .store, v => isArr v
  | .value, v => !isArr v

/-- Only `any` changes the class of a location's contents. -/
theorem Change.Holds.same_class {δ : Change} {b v v'} (hδ : δ ≠ .any)
    (h : δ.Holds b v v') (c : Cls) : c.has v' = c.has v := by
  have scalar_class : ScalarStep v v' → c.has v' = c.has v := fun ⟨_, hv, ha⟩ => by
    cases c <;> simp only [Cls.has, ha, hv]
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
  | grow =>
    rcases h with rfl | ⟨_, _, rfl, rfl, _, _⟩ | h
    · rfl
    · cases c <;> rfl
    · exact scalar_class h

/-- On contents that are no store, `grow` is `scalar`. -/
theorem Change.Holds.grow_value {b v v'} (h : Change.grow.Holds b v v') (hv : isArr v = false) :
    Change.scalar.Holds b v v' := by
  rcases h with h | ⟨_, _, rfl, _, _, _⟩ | h
  · exact .inl h
  · simp [isArr] at hv
  · exact .inr h

/-- On contents that are no store and neither `null` nor `undefined`,
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
  | grow => exact hs (h.grow_value ha)
  | any => exact absurd rfl hδ

/-- On a store, `scalar` is `keep`. -/
theorem Change.Holds.scalar_store {b ls v'} (h : Change.scalar.Holds b (.arr ls) v') : v' = .arr ls :=
  h.resolve_right fun hs => absurd hs.2.1 (by simp [isArr])

/-- On a store, `init` is `keep`. -/
theorem Change.Holds.init_store {b ls v'} (h : Change.init.Holds b (.arr ls) v') : v' = .arr ls :=
  h.init_defined rfl

def fieldsOf : Tm → List (PropKey × Nat)
  | .objAt fs _ _ => fs
  | _ => []

/-- The element locations a value's store lists, at a heap. -/
def storeElems (h : Heap) (v : Tm) : List (Option Nat) :=
  match (fieldsOf v).lookup arrayStoreKey with
  | some s => match h[s]? with
    | some (.arr ls) => ls
    | _ => []
  | none => []

/-- A region names locations relative to the values of slots and to a heap.
`field`, `own` are timeless; `elems` and `cls` are read at a heap. A path
`p` reads own data fields from a slot's value (`HeapKnowledge.readPath`):
`path x p k` is the own field `k` of the object it reads, `pathOwn x p` that
object's own locations and `pathElems x p` the element cells its store
lists; a read that fails denotes no location, and at the empty path they are
`field`, `own` and `elems`. `cell b` is a module cell's location, read at the
class its contents have: a cell holds a source value, never a store, so it
denotes the locations of class `value` (the exact cell needs module-cell
agreement, a step of the stated-effects design). `inCls r c` is the locations
of `r` whose contents are of class `c`. -/
inductive Region where
  | field (x : Nat) (k : PropKey)
  | own (x : Nat)
  | elems (x : Nat)
  | cls (c : Cls)
  | all
  | path (x : Nat) (p : List String) (k : PropKey)
  | pathOwn (x : Nat) (p : List String)
  | pathElems (x : Nat) (p : List String)
  | cell (b : String)
  | inCls (r : Region) (c : Cls)
  deriving DecidableEq, Repr

def Region.mem (ρ : Env) (h : Heap) : Region → Nat → Bool
  | .field x k, l => (fieldsOf (ρ x)).lookup k == some l
  | .own x, l => ((fieldsOf (ρ x)).map Prod.snd).contains l
  | .elems x, l => (storeElems h (ρ x)).contains (some l)
  | .cls c, l => match h[l]? with
    | some v => c.has v
    | none => false
  | .all, _ => true
  | .path x p k, l => match HeapKnowledge.readPath h (ρ x) p with
    | some v => (fieldsOf v).lookup k == some l
    | none => false
  | .pathOwn x p, l => match HeapKnowledge.readPath h (ρ x) p with
    | some v => ((fieldsOf v).map Prod.snd).contains l
    | none => false
  | .pathElems x p, l => match HeapKnowledge.readPath h (ρ x) p with
    | some v => (storeElems h v).contains (some l)
    | none => false
  | .cell _, l => match h[l]? with
    | some v => Cls.value.has v
    | none => false
  | .inCls r c, l => r.mem ρ h l && match h[l]? with
    | some v => c.has v
    | none => false

@[simp] theorem Region.mem_path_nil (ρ : Env) (h : Heap) (x : Nat) (k : PropKey) (l : Nat) :
    (Region.path x [] k).mem ρ h l = (Region.field x k).mem ρ h l := by
  simp [Region.mem, HeapKnowledge.readPath]

@[simp] theorem Region.mem_pathOwn_nil (ρ : Env) (h : Heap) (x : Nat) (l : Nat) :
    (Region.pathOwn x []).mem ρ h l = (Region.own x).mem ρ h l := by
  simp [Region.mem, HeapKnowledge.readPath]

@[simp] theorem Region.mem_pathElems_nil (ρ : Env) (h : Heap) (x : Nat) (l : Nat) :
    (Region.pathElems x []).mem ρ h l = (Region.elems x).mem ρ h l := by
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

theorem field_mem_own {ρ h x k l} (hm : (Region.field x k).mem ρ h l = true) :
    (Region.own x).mem ρ h l = true := by
  simp only [Region.mem, beq_iff_eq] at hm
  simpa [Region.mem] using lookup_mem_snd hm

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
      · rw [hv, if_pos hl, hv']
      · simp at he
    · rw [if_neg hl, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
  · rintro ⟨t, rfl⟩
    refine ⟨by simp, fun l v hv => ⟨v, ?_, .inl rfl⟩⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1, hv]

abbrev ClassEvidence := Nat → PropKey → Option Cls

/-- The class evidence holds at `h` for every location `h` has. -/
def ClassOk (cl : ClassEvidence) (ρ : Env) (h : Heap) : Prop :=
  ∀ x k c l, cl x k = some c → (fieldsOf (ρ x)).lookup k = some l → l < h.length →
    (Region.cls c).mem ρ h l = true

/-- The inclusions read without recursion: equal regions, every region in
`all`, a field among its object's own locations and in the class its
contents have by class evidence, a path's field among the path object's own
locations, and a cell among the locations of class `value`. -/
def Region.subBase (cl : ClassEvidence) (r s : Region) : Bool :=
  r == s || s == .all || match r, s with
    | .field x _, .own y => x == y
    | .field x k, .cls c => cl x k == some c
    | .path x p _, .pathOwn y q => x == y && p == q
    | .cell _, .cls .value => true
    | _, _ => false

/-- Region inclusion: `subBase`, and the part of `r` of class `c` in `s`
where `r` is, in `cls c`, and in `s`'s part of class `c` where `r` is in
`s`. -/
def Region.sub (cl : ClassEvidence) : Region → Region → Bool
  | .inCls r c, s => Region.sub cl r s || (match s with
      | .cls c' => c == c'
      | .inCls s' c' => c == c' && Region.sub cl r s'
      | _ => false) || Region.subBase cl (.inCls r c) s
  | r, s => Region.subBase cl r s

theorem Region.subBase_mem {cl : ClassEvidence} {r s : Region} {ρ h l}
    (hs : Region.subBase cl r s = true) (hc : ClassOk cl ρ h) (hl : l < h.length)
    (hm : r.mem ρ h l = true) : s.mem ρ h l = true := by
  unfold Region.subBase at hs
  simp only [Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with (rfl | rfl) | hs
  · exact hm
  · rfl
  · cases r <;> cases s <;> (try simp only [Bool.false_eq_true] at hs)
    case field.own x k y =>
      simp only [beq_iff_eq] at hs; subst hs; exact field_mem_own hm
    case field.cls x k c =>
      simp only [beq_iff_eq] at hs
      simp only [Region.mem, beq_iff_eq] at hm
      exact hc x k c l hs hm hl
    case path.pathOwn x p k y q =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv
        simp only [beq_iff_eq] at hm
        simpa using lookup_mem_snd hm
      · cases hm
    case cell.cls b c =>
      cases c
      · simp at hs
      · simpa [Region.mem] using hm

theorem Region.sub_mem {cl : ClassEvidence} {r s : Region} {ρ h l}
    (hs : Region.sub cl r s = true) (hc : ClassOk cl ρ h) (hl : l < h.length)
    (hm : r.mem ρ h l = true) : s.mem ρ h l = true := by
  induction r generalizing s with
  | inCls r c ih =>
    simp only [Region.sub, Bool.or_eq_true] at hs
    have hm' := hm
    simp only [Region.mem, Bool.and_eq_true] at hm'
    rcases hs with (hs | hs) | hs
    · exact ih hs hm'.1
    · cases s <;> (try simp only [Bool.false_eq_true] at hs)
      case cls c' =>
        simp only [beq_iff_eq] at hs; subst hs
        simpa [Region.mem] using hm'.2
      case inCls s' c' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨rfl, hs⟩ := hs
        simp only [Region.mem, Bool.and_eq_true]
        exact ⟨ih hs hm'.1, hm'.2⟩
    · exact Region.subBase_mem hs hc hl hm
  | field | own | elems | cls | all | path | pathOwn | pathElems | cell =>
    exact Region.subBase_mem (by simpa [Region.sub] using hs) hc hl hm

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

/-- Every element location the store of `v` lists at `h`, below the entry
heap `h₀`'s length, the store of `v` listed at `h₀`: **cell provenance**. -/
def CellsFrom (h₀ h : Heap) (v : Val) : Prop :=
  ∀ l, some l ∈ storeElems h v → l < h₀.length → some l ∈ storeElems h₀ v

theorem CellsFrom.refl (h : Heap) (v : Val) : CellsFrom h h v := fun _ hm _ => hm

/-- Cell provenance composes along a growing heap. -/
theorem CellsFrom.trans {h₀ h₁ h₂ : Heap} {v : Val} (hb : h₀.length ≤ h₁.length)
    (h₁₀ : CellsFrom h₀ h₁ v) (h₂₁ : CellsFrom h₁ h₂ v) : CellsFrom h₀ h₂ v :=
  fun l hm hl => h₁₀ l (h₂₁ l hm (Nat.lt_of_lt_of_le hl hb)) hl

/-- A store location whose list at `h` keeps only cells of its list at `h₀`
and cells at or above `h₀`'s length gives cell provenance. -/
theorem CellsFrom.of_lists {h₀ h : Heap} {v : Val} {s : Nat}
    (hs : (fieldsOf v).lookup arrayStoreKey = some s)
    (hl : ∀ ls', h[s]? = some (.arr ls') → ∀ m, some m ∈ ls' → m < h₀.length →
      ∃ ls, h₀[s]? = some (.arr ls) ∧ some m ∈ ls) : CellsFrom h₀ h v := by
  intro m hm hm₀
  simp only [storeElems, hs] at hm ⊢
  split at hm
  · rename_i ls' hls'
    obtain ⟨ls, hls, hm'⟩ := hl ls' hls' m hm hm₀
    simpa [hls] using hm'
  · simp at hm

/-- A change of the store location within `grow` gives cell provenance. -/
theorem CellsFrom.of_change {δ : Change} {h₀ h : Heap} {v : Val} {s : Nat} {w w' : Val}
    (hδ : δ.le .grow = true) (hs : (fieldsOf v).lookup arrayStoreKey = some s)
    (hw : h₀[s]? = some w) (hw' : h[s]? = some w') (hc : δ.Holds h₀.length w w') :
    CellsFrom h₀ h v := by
  have hg : Change.grow.Holds h₀.length w w' := hc.mono hδ
  refine CellsFrom.of_lists hs fun ls' hls' m hm hm₀ => ?_
  rw [hw'] at hls'
  cases hls'
  rcases hg with rfl | ⟨ls, ls'', rfl, hls'', -, hl, -⟩ | hsc
  · exact ⟨ls', hw, hm⟩
  · cases hls''
    rcases hl m hm with hm' | hle
    · exact ⟨ls, hw, hm'⟩
    · omega
  · exact absurd hsc.2.2 (by simp [isArr])

/-- A footprint letting the store location of `v`, read at `h₀`, change at
most within `grow` gives cell provenance. -/
theorem CellsFrom.of_post {Φ : Footprint} {ρ : Env} {h₀ h : Heap} {v : Val} {s : Nat}
    (hp : Post Φ ρ h₀ h) (hs : (fieldsOf v).lookup arrayStoreKey = some s) (hs₀ : s < h₀.length)
    (hΦ : ∀ e ∈ Φ, e.1.mem ρ h₀ s = true → e.2.le .grow = true) : CellsFrom h₀ h v := by
  obtain ⟨w, hw⟩ : ∃ w, h₀[s]? = some w := ⟨h₀[s], List.getElem?_eq_getElem hs₀⟩
  obtain ⟨w', hw', ha⟩ := hp.2 s w hw
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact CellsFrom.of_change (δ := .keep) rfl hs hw hw' rfl
  · exact CellsFrom.of_change (hΦ e he hm) hs hw hw' hh

/-- Placing a location in a store lists only that location beyond the
store's own. -/
theorem mem_placeAt {ls : List (Option Nat)} {k l m : Nat} (h : some m ∈ placeAt ls k l) :
    some m ∈ ls ∨ m = l := by
  unfold placeAt at h
  rcases List.mem_or_eq_of_mem_set h with h | h
  · rcases List.mem_append.mp h with h | h
    · exact .inl h
    · simp [List.mem_replicate] at h
  · cases h; exact .inr rfl

/-- An element write, which places a location allocated at or above `b`,
lists below `b` only cells its store listed: the step's cell provenance. -/
theorem placeAt_cells {ls : List (Option Nat)} {k l b : Nat} (hb : b ≤ l) :
    ∀ m, some m ∈ placeAt ls k l → m < b → some m ∈ ls := fun m hm hmb =>
  (mem_placeAt hm).resolve_right fun h => by omega

/-- What transport may use, at the heap the step starts in: the slots whose
own locations are at least the entry heap's length, and the slots whose
listed element locations hold no store; the paths that read the value they
read at the entry heap, those whose store meets cell provenance, and those
whose listed element locations hold no store. -/
structure TransportEvidence where
  fresh : Nat → Bool
  elemsValue : Nat → Bool
  kept : Nat → List String → Bool := fun _ _ => false
  cellsFrom : Nat → List String → Bool := fun _ _ => false
  pathElemsValue : Nat → List String → Bool := fun _ _ => false

def FreshOk (fresh : Nat → Bool) (ρ : Env) (b : Nat) : Prop :=
  ∀ x, fresh x = true → ∀ l, l ∈ (fieldsOf (ρ x)).map Prod.snd → b ≤ l

def ElemsValueOk (ev : Nat → Bool) (ρ : Env) (h : Heap) : Prop :=
  ∀ x, ev x = true → ∀ l, (Region.elems x).mem ρ h l = true → (Region.cls .value).mem ρ h l = true

/-- The path evidence of a step from `h`, against the entry heap `h₀`. -/
structure PathEvidenceOk (ev : TransportEvidence) (ρ : Env) (h₀ h : Heap) : Prop where
  kept : ∀ x p, ev.kept x p = true → ∀ v, HeapKnowledge.readPath h (ρ x) p = some v →
    HeapKnowledge.readPath h₀ (ρ x) p = some v
  cellsFrom : ∀ x p, ev.cellsFrom x p = true → ∀ v, HeapKnowledge.readPath h (ρ x) p = some v →
    CellsFrom h₀ h v
  pathElemsValue : ∀ x p, ev.pathElemsValue x p = true → ∀ l,
    (Region.pathElems x p).mem ρ h l = true → (Region.cls .value).mem ρ h l = true

/-- The evidence of no path, valid of every step. -/
theorem PathEvidenceOk.none {fresh elemsValue : Nat → Bool} {ρ : Env} {h₀ h : Heap} :
    PathEvidenceOk ⟨fresh, elemsValue, fun _ _ => false, fun _ _ => false, fun _ _ => false⟩ ρ h₀ h :=
  ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩

/-- Whether a path is read at the entry heap where it is read at the step's:
the empty path always, any other where the evidence says so. -/
def TransportEvidence.reads (ev : TransportEvidence) (x : Nat) (p : List String) : Bool :=
  p.isEmpty || ev.kept x p

/-- A region read at the step's heap, in regions read at the entry heap: a
fresh slot's fields and own locations in none, a path's where the path
reads its entry value, else in `all`; a store's cells, where they meet cell
provenance, in themselves, else in `cls value` where they hold no store,
else in `all`; a class and a cell in themselves (`cls_back`); the part of a
region of class `c`, in its transport's parts of class `c`. -/
def transport (ev : TransportEvidence) : Region → List Region
  | .field x k => if ev.fresh x then [] else [.field x k]
  | .own x => if ev.fresh x then [] else [.own x]
  | .elems x => if ev.cellsFrom x [] then [.elems x]
      else if ev.elemsValue x then [.cls .value] else [.all]
  | .cls c => [.cls c]
  | .all => [.all]
  | .path x p k => if p.isEmpty && ev.fresh x then []
      else if ev.reads x p then [.path x p k] else [.all]
  | .pathOwn x p => if p.isEmpty && ev.fresh x then []
      else if ev.reads x p then [.pathOwn x p] else [.all]
  | .pathElems x p => if ev.reads x p && ev.cellsFrom x p then [.pathElems x p]
      else if ev.pathElemsValue x p then [.cls .value] else [.all]
  | .cell b => [.cell b]
  | .inCls r c => (transport ev r).map (·.inCls c)

def transportAll (ev : TransportEvidence) (Φ : Footprint) : Footprint :=
  Φ.flatMap fun e => (transport ev e.1).map (·, e.2)

theorem cls_back {Φp ρ h₀ h l c} (hp : Post Φp ρ h₀ h) (hl : l < h₀.length)
    (hm : (Region.cls c).mem ρ h l = true) :
    (Region.cls c).mem ρ h₀ l = true ∨ ∃ e ∈ Φp, e.1.mem ρ h₀ l = true ∧ e.2 = .any := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, h₀[l]? = some v := ⟨h₀[l], List.getElem?_eq_getElem hl⟩
  obtain ⟨v, hv, ha⟩ := hp.2 l v₀ hv₀
  have hcv : c.has v = true := by simpa [Region.mem, hv] using hm
  by_cases hc₀ : c.has v₀ = true
  · exact .inl (by simp [Region.mem, hv₀, hc₀])
  · rcases ha with rfl | ⟨e, he, hem, hh⟩
    · exact absurd hcv hc₀
    · exact .inr ⟨e, he, hem, Classical.byContradiction fun hne =>
        hc₀ (by rw [← hh.same_class hne c]; exact hcv)⟩

/-- A path read at the step's heap that the evidence keeps reads the same
value at the entry heap. -/
private theorem reads_back {ev ρ h₀ h x p v} (hk : PathEvidenceOk ev ρ h₀ h)
    (hr : ev.reads x p = true) (hv : HeapKnowledge.readPath h (ρ x) p = some v) :
    HeapKnowledge.readPath h₀ (ρ x) p = some v := by
  simp only [TransportEvidence.reads, Bool.or_eq_true, List.isEmpty_iff] at hr
  rcases hr with rfl | hr
  · simpa [HeapKnowledge.readPath] using hv
  · exact hk.kept x p hr v hv

theorem transport_sound {Φp ρ h₀ h ev l} (hp : Post Φp ρ h₀ h) (hf : FreshOk ev.fresh ρ h₀.length)
    (he : ElemsValueOk ev.elemsValue ρ h) (hk : PathEvidenceOk ev ρ h₀ h) (hl : l < h₀.length) :
    ∀ {r : Region}, r.mem ρ h l = true →
    (∃ s ∈ transport ev r, s.mem ρ h₀ l = true) ∨ ∃ e ∈ Φp, e.1.mem ρ h₀ l = true ∧ e.2 = .any := by
  intro r
  induction r with
  | field x k =>
    intro hm
    by_cases hx : ev.fresh x = true
    · exact absurd (hf x hx l (lookup_mem_snd (by simpa [Region.mem] using hm))) (by omega)
    · exact .inl ⟨.field x k, by simp [transport, hx], by simpa [Region.mem] using hm⟩
  | own x =>
    intro hm
    by_cases hx : ev.fresh x = true
    · exact absurd (hf x hx l (by simpa [Region.mem] using hm)) (by omega)
    · exact .inl ⟨.own x, by simp [transport, hx], by simpa [Region.mem] using hm⟩
  | elems x =>
    intro hm
    by_cases hc : ev.cellsFrom x [] = true
    · have hcf := hk.cellsFrom x [] hc (ρ x) rfl l (by simpa [Region.mem] using hm) hl
      exact .inl ⟨.elems x, by simp [transport, hc], by simpa [Region.mem] using hcf⟩
    · by_cases hx : ev.elemsValue x = true
      · rcases cls_back hp hl (he x hx l hm) with h | h
        · exact .inl ⟨.cls .value, by simp [transport, hc, hx], h⟩
        · exact .inr h
      · exact .inl ⟨.all, by simp [transport, hc, hx], rfl⟩
  | cls c =>
    intro hm
    rcases cls_back hp hl hm with h | h
    · exact .inl ⟨.cls c, by simp [transport], h⟩
    · exact .inr h
  | all => intro _; exact .inl ⟨.all, by simp [transport], rfl⟩
  | path x p k =>
    intro hm
    by_cases hx : (p.isEmpty && ev.fresh x) = true
    · simp only [Bool.and_eq_true, List.isEmpty_iff] at hx
      obtain ⟨rfl, hx⟩ := hx
      exact absurd (hf x hx l (lookup_mem_snd (by simpa [Region.mem, HeapKnowledge.readPath] using hm)))
        (by omega)
    · by_cases hr : ev.reads x p = true
      · refine .inl ⟨.path x p k, by simp [transport, hx, hr], ?_⟩
        simp only [Region.mem] at hm ⊢
        split at hm
        · rename_i v hv; rw [reads_back hk hr hv]; exact hm
        · cases hm
      · exact .inl ⟨.all, by simp [transport, hx, hr], rfl⟩
  | pathOwn x p =>
    intro hm
    by_cases hx : (p.isEmpty && ev.fresh x) = true
    · simp only [Bool.and_eq_true, List.isEmpty_iff] at hx
      obtain ⟨rfl, hx⟩ := hx
      exact absurd (hf x hx l (by simpa [Region.mem, HeapKnowledge.readPath] using hm)) (by omega)
    · by_cases hr : ev.reads x p = true
      · refine .inl ⟨.pathOwn x p, by simp [transport, hx, hr], ?_⟩
        simp only [Region.mem] at hm ⊢
        split at hm
        · rename_i v hv; rw [reads_back hk hr hv]; exact hm
        · cases hm
      · exact .inl ⟨.all, by simp [transport, hx, hr], rfl⟩
  | pathElems x p =>
    intro hm
    by_cases hrc : (ev.reads x p && ev.cellsFrom x p) = true
    · simp only [Bool.and_eq_true] at hrc
      refine .inl ⟨.pathElems x p, by simp [transport, hrc.1, hrc.2], ?_⟩
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv
        rw [reads_back hk hrc.1 hv]
        simpa using hk.cellsFrom x p hrc.2 v hv l (by simpa using hm) hl
      · cases hm
    · by_cases hx : ev.pathElemsValue x p = true
      · rcases cls_back hp hl (hk.pathElemsValue x p hx l hm) with h | h
        · exact .inl ⟨.cls .value, by simp [transport, hrc, hx], h⟩
        · exact .inr h
      · exact .inl ⟨.all, by simp [transport, hrc, hx], rfl⟩
  | cell b =>
    intro hm
    have hv : (Region.cls .value).mem ρ h l = true := by simpa [Region.mem] using hm
    rcases cls_back hp hl hv with h | h
    · exact .inl ⟨.cell b, by simp [transport], by simpa [Region.mem] using h⟩
    · exact .inr h
  | inCls r c ih =>
    intro hm
    simp only [Region.mem, Bool.and_eq_true] at hm
    have hc : (Region.cls c).mem ρ h l = true := by simpa [Region.mem] using hm.2
    rcases ih hm.1 with ⟨s, hs, hsm⟩ | h
    · rcases cls_back hp hl hc with hc₀ | h
      · refine .inl ⟨s.inCls c, by simp only [transport]; exact List.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
        simp only [Region.mem, Bool.and_eq_true]
        exact ⟨hsm, by simpa [Region.mem] using hc₀⟩
      · exact .inr h
    · exact .inr h

/-- **Composition.** An entry footprint so far, a step from the current heap,
and an inclusion justified by class evidence valid at the entry heap give the
next entry footprint. -/
theorem Post.compose {Φp Φn Φq : Footprint} {cl ρ h₀ h h' ev}
    (hp : Post Φp ρ h₀ h) (hn : Post Φn ρ h h')
    (hf : FreshOk ev.fresh ρ h₀.length) (he : ElemsValueOk ev.elemsValue ρ h)
    (hk : PathEvidenceOk ev ρ h₀ h)
    (hle : Footprint.le cl (Φp ++ transportAll ev Φn) Φq = true) (hc : ClassOk cl ρ h₀) :
    Post Φq ρ h₀ h' := by
  refine ⟨Nat.le_trans hp.1 hn.1, fun l v₀ hv₀ => ?_⟩
  have hl := (List.getElem?_eq_some_iff.mp hv₀).1
  have hb : h₀.length ≤ h.length := hp.1
  obtain ⟨v₁, hv₁, ha₁⟩ := hp.2 l v₀ hv₀
  obtain ⟨v₂, hv₂, ha₂⟩ := hn.2 l v₁ hv₁
  refine ⟨v₂, hv₂, Allowed.mono hle hc hl ?_⟩
  -- an entry of `Φp` that changes arbitrarily covers every sequence
  have viaAny : ∀ e ∈ Φp, e.1.mem ρ h₀ l = true → e.2 = .any →
      Allowed (Φp ++ transportAll ev Φn) ρ h₀ l v₀ v₂ := fun e hm hem hany =>
    .inr ⟨e, List.mem_append_left _ hm, hem, by rw [hany]; trivial⟩
  -- the step's entry, transported
  have stepEntry : ∀ e ∈ Φn, e.1.mem ρ h l = true →
      (∃ s, (s, e.2) ∈ transportAll ev Φn ∧ s.mem ρ h₀ l = true) ∨
        ∃ e' ∈ Φp, e'.1.mem ρ h₀ l = true ∧ e'.2 = .any := by
    intro e hem hm
    rcases transport_sound hp hf he hk hl hm with ⟨s, hs, hsm⟩ | h
    · exact .inl ⟨s, List.mem_flatMap.mpr ⟨e, hem, List.mem_map.mpr ⟨s, hs, rfl⟩⟩, hsm⟩
    · exact .inr h
  rcases ha₁ with rfl | ⟨e₁, he₁, hm₁, hh₁⟩
  · rcases ha₂ with rfl | ⟨e₂, he₂, hm₂, hh₂⟩
    · exact .inl rfl
    · rcases stepEntry e₂ he₂ hm₂ with ⟨s, hs, hsm⟩ | ⟨e', he', hm', hany⟩
      · exact .inr ⟨(s, e₂.2), List.mem_append_right _ hs, hsm, hh₂.lower hb⟩
      · exact viaAny e' he' hm' hany
  · rcases ha₂ with rfl | ⟨e₂, he₂, hm₂, hh₂⟩
    · exact .inr ⟨e₁, List.mem_append_left _ he₁, hm₁, hh₁⟩
    · rcases stepEntry e₂ he₂ hm₂ with ⟨s, hs, hsm⟩ | ⟨e', he', hm', hany⟩
      · have hseq := hh₁.seq hb hh₂
        rcases Change.max_cases e₁.2 e₂.2 with hmax | hmax
        · exact .inr ⟨e₁, List.mem_append_left _ he₁, hm₁, by rw [← hmax]; exact hseq⟩
        · exact .inr ⟨(s, e₂.2), List.mem_append_right _ hs, hsm, by rw [← hmax]; exact hseq⟩
      · exact viaAny e' he' hm' hany

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

def Change.holdsB : Change → Nat → Val → Val → Bool
  | .keep, _, v, v' => v' == v
  | .init, _, v, v' => v' == v || (nullish v && !isArr v')
  | .scalar, _, v, v' => v' == v || (!isObj v && (!isArr v && !isArr v'))
  | .grow, b, v, v' => v' == v || ((match v, v' with
    | .arr ls, .arr ls' => decide (denseLen ls ≤ denseLen ls') &&
        ((ls'.all fun o => match o with
          | some l => ls.contains (some l) || decide (b ≤ l)
          | none => true) &&
        (decide (ls.length ≤ ls'.length) && (!decide (ls.length ≤ maxArrayLength) || decide (ls'.length ≤ maxArrayLength))))
    | _, _ => false) || (!isObj v && (!isArr v && !isArr v')))
  | .any, _, _, _ => true

theorem Change.holdsB_iff (δ : Change) (b : Nat) (v v' : Val) : δ.holdsB b v v' = true ↔ δ.Holds b v v' := by
  cases δ with
  | keep => simp [Change.holdsB, Change.Holds]
  | any => simp [Change.holdsB, Change.Holds]
  | init => simp [Change.holdsB, Change.Holds, InitStep]
  | scalar => simp [Change.holdsB, Change.Holds, ScalarStep]
  | grow =>
    simp only [Change.holdsB, Change.Holds, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true',
      ScalarStep]
    apply or_congr Iff.rfl
    apply or_congr _ Iff.rfl
    cases v <;> cases v' <;> simp
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
