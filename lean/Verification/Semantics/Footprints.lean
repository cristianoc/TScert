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
including footprint is read at (`ClassOk`). Nothing uses this module yet. -/
namespace Verification.Footprints

/-! ## Changes -/

/-- How an entry may change a location's contents: not at all, as a store that
keeps every dense prefix, or arbitrarily. -/
inductive Change where
  | keep
  | grow
  | any
  deriving DecidableEq, Repr

def Change.le : Change → Change → Bool
  | .keep, _ => true
  | .grow, .grow | .grow, .any => true
  | .any, .any => true
  | _, _ => false

def Change.max : Change → Change → Change
  | .any, _ | _, .any => .any
  | .grow, _ | _, .grow => .grow
  | .keep, .keep => .keep

/-- The first `n` indices of a store are present. -/
def DensePrefix (n : Nat) (ls : List (Option Nat)) : Prop :=
  n ≤ ls.length ∧ ∀ i, i < n → ls[i]? ≠ some none

/-- A change's relation on contents. `b` is the length of the heap the change
starts from: a growing store gains no element location below it that it did
not already list. -/
def Change.Holds : Change → Nat → Val → Val → Prop
  | .keep, _, v, v' => v' = v
  | .grow, b, v, v' => v' = v ∨ ∃ ls ls', v = .arr ls ∧ v' = .arr ls' ∧
      (∀ n, DensePrefix n ls → DensePrefix n ls') ∧ ∀ l, some l ∈ ls' → some l ∈ ls ∨ b ≤ l
  | .any, _, _, _ => True

theorem Change.Holds.refl (δ : Change) (b : Nat) (v : Val) : δ.Holds b v v := by
  cases δ <;> simp [Change.Holds]

theorem Change.Holds.mono {δ δ' : Change} {b v v'} (hle : δ.le δ' = true)
    (h : δ.Holds b v v') : δ'.Holds b v v' := by
  cases δ <;> cases δ' <;> simp_all [Change.le, Change.Holds]

/-- A larger starting heap only strengthens what `grow` requires of new
element locations. -/
theorem Change.Holds.lower {δ : Change} {b b' v v'} (hb : b ≤ b')
    (h : δ.Holds b' v v') : δ.Holds b v v' := by
  cases δ with
  | keep | any => exact h
  | grow =>
    rcases h with h | ⟨ls, ls', rfl, rfl, hd, hl⟩
    · exact .inl h
    · exact .inr ⟨ls, ls', rfl, rfl, hd, fun l hm => (hl l hm).imp id (Nat.le_trans hb)⟩

theorem Change.Holds.trans {δ : Change} {b b' v v' v''} (hb : b ≤ b')
    (h₁ : δ.Holds b v v') (h₂ : δ.Holds b' v' v'') : δ.Holds b v v'' := by
  cases δ with
  | any => trivial
  | keep => simp only [Change.Holds] at h₁ h₂ ⊢; rw [h₂, h₁]
  | grow =>
    rcases h₁ with rfl | ⟨ls, ls', rfl, rfl, hd₁, hl₁⟩
    · exact h₂.lower hb
    · rcases h₂ with rfl | ⟨ms, ls'', hms, rfl, hd₂, hl₂⟩
      · exact .inr ⟨ls, ls', rfl, rfl, hd₁, hl₁⟩
      · cases hms
        refine .inr ⟨ls, ls'', rfl, rfl, fun n h => hd₂ n (hd₁ n h), fun l hm => ?_⟩
        rcases hl₂ l hm with hm' | hle
        · exact hl₁ l hm'
        · exact .inr (Nat.le_trans hb hle)

theorem Change.le_max_left (a b : Change) : a.le (a.max b) = true := by
  cases a <;> cases b <;> rfl

theorem Change.le_max_right (a b : Change) : b.le (a.max b) = true := by
  cases a <;> cases b <;> rfl

theorem Change.max_cases (a b : Change) : a.max b = a ∨ a.max b = b := by
  cases a <;> cases b <;> simp [Change.max]

theorem Change.le_trans {a b c : Change} (h₁ : a.le b = true) (h₂ : b.le c = true) : a.le c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [Change.le]

/-- Two changes in sequence are within their join. -/
theorem Change.Holds.seq {δ₁ δ₂ : Change} {b b' v v' v''} (hb : b ≤ b')
    (h₁ : δ₁.Holds b v v') (h₂ : δ₂.Holds b' v' v'') : (δ₁.max δ₂).Holds b v v'' :=
  (h₁.mono (Change.le_max_left δ₁ δ₂)).trans hb (h₂.mono (Change.le_max_right δ₁ δ₂))

/-! ## Classes of contents and regions -/

def isArr : Val → Bool
  | .arr _ => true
  | _ => false

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
  cases δ with
  | any => exact absurd rfl hδ
  | keep => simp only [Change.Holds] at h; rw [h]
  | grow =>
    rcases h with rfl | ⟨_, _, rfl, rfl, _, _⟩
    · rfl
    · cases c <;> rfl

/-- On contents that are no store, `grow` is `keep`. -/
theorem Change.Holds.grow_value {b v v'} (h : Change.grow.Holds b v v') (hv : isArr v = false) :
    v' = v := by
  rcases h with h | ⟨_, _, rfl, _, _, _⟩
  · exact h
  · simp [isArr] at hv

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
`field`, `own` are timeless; `elems` and `cls` are read at a heap. -/
inductive Region where
  | field (x : Nat) (k : PropKey)
  | own (x : Nat)
  | elems (x : Nat)
  | cls (c : Cls)
  | all
  deriving DecidableEq, Repr

def Region.mem (ρ : Env) (h : Heap) : Region → Nat → Bool
  | .field x k, l => (fieldsOf (ρ x)).lookup k == some l
  | .own x, l => ((fieldsOf (ρ x)).map Prod.snd).contains l
  | .elems x, l => (storeElems h (ρ x)).contains (some l)
  | .cls c, l => match h[l]? with
    | some v => c.has v
    | none => false
  | .all, _ => true

/-- `field` and `own` do not depend on the heap. -/
def Region.timeless : Region → Bool
  | .field .. | .own _ | .all => true
  | .elems _ | .cls _ => false

theorem Region.mem_timeless {r : Region} (ht : r.timeless = true) (ρ : Env) (h h' : Heap) (l : Nat) :
    r.mem ρ h l = r.mem ρ h' l := by
  cases r <;> simp_all [Region.timeless, Region.mem]

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

theorem Post.all_iff {ρ : Env} {h h' : Heap} : Post [(.all, .any)] ρ h h' ↔ h.length ≤ h'.length := by
  refine ⟨fun hp => hp.1, fun hlen => ⟨hlen, fun l v hv => ?_⟩⟩
  have hl := (List.getElem?_eq_some_iff.mp hv).1
  exact ⟨h'[l], List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hl hlen),
    .inr ⟨(.all, .any), by simp, rfl, trivial⟩⟩

/-! ## Containment and order

A region containment that depends on contents is justified by class
evidence: for a slot and a key, the class of the contents at that field's
location, at the heap the footprint is read at. -/

abbrev ClassEvidence := Nat → PropKey → Option Cls

/-- The class evidence holds at `h` for every location `h` has. -/
def ClassOk (cl : ClassEvidence) (ρ : Env) (h : Heap) : Prop :=
  ∀ x k c l, cl x k = some c → (fieldsOf (ρ x)).lookup k = some l → l < h.length →
    (Region.cls c).mem ρ h l = true

def Region.sub (cl : ClassEvidence) : Region → Region → Bool
  | _, .all => true
  | .field x _, .own y => x == y
  | .field x k, .cls c => cl x k == some c
  | r, s => r == s

theorem Region.sub_mem {cl : ClassEvidence} {r s : Region} {ρ h l}
    (hs : Region.sub cl r s = true) (hc : ClassOk cl ρ h) (hl : l < h.length)
    (hm : r.mem ρ h l = true) : s.mem ρ h l = true := by
  cases s with
  | all => rfl
  | own y =>
    cases r with
    | field x k =>
      simp only [Region.sub, beq_iff_eq] at hs; subst hs; exact field_mem_own hm
    | _ => simp_all [Region.sub]
  | cls c =>
    cases r with
    | field x k =>
      simp only [Region.sub, beq_iff_eq] at hs
      simp only [Region.mem, beq_iff_eq] at hm
      exact hc x k c l hs hm hl
    | _ => simp_all [Region.sub]
  | _ => cases r <;> simp_all [Region.sub]

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

theorem Post.mono {cl Φ Ψ ρ h h'} (hle : Footprint.le cl Φ Ψ = true) (hc : ClassOk cl ρ h)
    (hp : Post Φ ρ h h') : Post Ψ ρ h h' := by
  refine ⟨hp.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  exact ⟨v', hv', ha.mono hle hc (List.getElem?_eq_some_iff.mp hv).1⟩

/-! ## Transport to the entry heap

An entry footprint is read at the invocation's entry heap `h₀`. A step
footprint is read at the heap its action starts in. `transport` maps a step
region to entry regions; `transport_sound` says that every location of `h₀`
in the step region is in the transported one at `h₀`, unless the entry
footprint already lets that location change arbitrarily. -/

/-- What transport may use, at the heap the step starts in: the slots whose
own locations are at least the entry heap's length, and the slots whose
listed element locations hold no store. -/
structure TransportEvidence where
  fresh : Nat → Bool
  elemsValue : Nat → Bool

def FreshOk (fresh : Nat → Bool) (ρ : Env) (b : Nat) : Prop :=
  ∀ x, fresh x = true → ∀ l, l ∈ (fieldsOf (ρ x)).map Prod.snd → b ≤ l

def ElemsValueOk (ev : Nat → Bool) (ρ : Env) (h : Heap) : Prop :=
  ∀ x, ev x = true → ∀ l, (Region.elems x).mem ρ h l = true → (Region.cls .value).mem ρ h l = true

def transport (ev : TransportEvidence) : Region → List Region
  | .field x k => if ev.fresh x then [] else [.field x k]
  | .own x => if ev.fresh x then [] else [.own x]
  | .elems x => if ev.elemsValue x then [.cls .value] else [.all]
  | .cls c => [.cls c]
  | .all => [.all]

def transportAll (ev : TransportEvidence) (Φ : Footprint) : Footprint :=
  Φ.flatMap fun e => (transport ev e.1).map (·, e.2)

private theorem cls_back {Φp ρ h₀ h l c} (hp : Post Φp ρ h₀ h) (hl : l < h₀.length)
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

theorem transport_sound {Φp ρ h₀ h ev r l} (hp : Post Φp ρ h₀ h) (hf : FreshOk ev.fresh ρ h₀.length)
    (he : ElemsValueOk ev.elemsValue ρ h) (hl : l < h₀.length) (hm : r.mem ρ h l = true) :
    (∃ s ∈ transport ev r, s.mem ρ h₀ l = true) ∨ ∃ e ∈ Φp, e.1.mem ρ h₀ l = true ∧ e.2 = .any := by
  cases r with
  | field x k =>
    by_cases hx : ev.fresh x = true
    · exact absurd (hf x hx l (lookup_mem_snd (by simpa [Region.mem] using hm))) (by omega)
    · exact .inl ⟨.field x k, by simp [transport, hx], by simpa [Region.mem] using hm⟩
  | own x =>
    by_cases hx : ev.fresh x = true
    · exact absurd (hf x hx l (by simpa [Region.mem] using hm)) (by omega)
    · exact .inl ⟨.own x, by simp [transport, hx], by simpa [Region.mem] using hm⟩
  | elems x =>
    by_cases hx : ev.elemsValue x = true
    · rcases cls_back hp hl (he x hx l hm) with h | h
      · exact .inl ⟨.cls .value, by simp [transport, hx], h⟩
      · exact .inr h
    · exact .inl ⟨.all, by simp [transport, hx], rfl⟩
  | cls c =>
    rcases cls_back hp hl hm with h | h
    · exact .inl ⟨.cls c, by simp [transport], h⟩
    · exact .inr h
  | all => exact .inl ⟨.all, by simp [transport], rfl⟩

/-- **Composition.** An entry footprint so far, a step from the current heap,
and an inclusion justified by class evidence valid at the entry heap give the
next entry footprint. -/
theorem Post.compose {Φp Φn Φq : Footprint} {cl ρ h₀ h h' ev}
    (hp : Post Φp ρ h₀ h) (hn : Post Φn ρ h h')
    (hf : FreshOk ev.fresh ρ h₀.length) (he : ElemsValueOk ev.elemsValue ρ h)
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
    rcases transport_sound hp hf he hl hm with ⟨s, hs, hsm⟩ | h
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
  | .grow, b, v, v' => v' == v || match v, v' with
    | .arr ls, .arr ls' => decide (denseLen ls ≤ denseLen ls') &&
        ls'.all fun o => match o with
          | some l => ls.contains (some l) || decide (b ≤ l)
          | none => true
    | _, _ => false
  | .any, _, _, _ => true

theorem Change.holdsB_iff (δ : Change) (b : Nat) (v v' : Val) : δ.holdsB b v v' = true ↔ δ.Holds b v v' := by
  cases δ with
  | keep => simp [Change.holdsB, Change.Holds]
  | any => simp [Change.holdsB, Change.Holds]
  | grow =>
    simp only [Change.holdsB, Change.Holds, Bool.or_eq_true, beq_iff_eq]
    apply or_congr Iff.rfl
    cases v <;> cases v' <;> simp
    rename_i ls ls'
    rw [preserves_dense_iff]
    apply and_congr Iff.rfl
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

/-- `ClassOk` on a finite set of slots and keys, decided at a heap. -/
def classOkB (cl : ClassEvidence) (ρ : Env) (h : Heap) (slots : List Nat) (keys : List PropKey) : Bool :=
  slots.all fun x => keys.all fun k => match cl x k, (fieldsOf (ρ x)).lookup k with
    | some c, some l => !decide (l < h.length) || (Region.cls c).mem ρ h l
    | _, _ => true

end Verification.Footprints
