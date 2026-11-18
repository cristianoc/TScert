import Verification.Semantics.Support
import Verification.Semantics.IndexedStates

/-! # Read-only handles: the protected region

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, section
"What the Lean states"), its region and history, over the paper's heap: a
package's sites and their marks, paths and read-only reach, crossings, the
history of the active calls `A` with the between-calls record `B`, the
exposed locations `E`, and the one membership test of the protected region
`R_P`.

- The history's transitions keep every set of `A` equal to the protected
  set `⋃A ∪ B` (`HStep.uniform`): the sets of overlapping calls grow
  together, so the stack carries one set and its depth.
- Inside a call at depth `d`, a sequence of transitions that never pops
  below `d` only grows the protected set and keeps `B` (`HSteps.grows`,
  the draft's (L3) on histories); with the marks fixed at allocation the
  region only grows (`InR.mono`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

/-! ## Paths and read-only reach -/

/-- **A step of a path** (the draft, "What the Lean states", Paths): a
field key, the spine key `[]` among them, which reaches an array's spine;
a typed array's view spine; or the element cell a spine lists at an index.
A collection's entries are held in no location, so no step reaches them. -/
inductive Label where
  | key (k : PropKey)
  | view
  | cell (i : Nat)

/-- The location one step reaches from the contents `v`. -/
def next (v : Val) : Label → Option Nat
  | .key k => (fieldsOf v).lookup k
  | .view => HeapKnowledge.descriptorSpine v
  | .cell i => match spineEntries v with
    | some ls => ls[i]?.join
    | none => none

/-- **Following a path** `h ⊢ v →π l`: from the value `v`, each step reads
the next location, and each location before the last is read for the next
step's contents. -/
def Follows (h : Heap) : Val → List Label → Nat → Prop
  | _, [], _ => False
  | v, [a], l => next v a = some l
  | v, a :: b :: π, l => ∃ l₀ v₀, next v a = some l₀ ∧ h[l₀]? = some v₀ ∧ Follows h v₀ (b :: π) l

/-- A location is reachable from a value through some path. -/
def Reaches (h : Heap) (v : Val) (l : Nat) : Prop := ∃ π, Follows h v π l

/-- A location is reachable from one of the values `roots`. -/
def ReachesFrom (h : Heap) (roots : List Val) (l : Nat) : Prop := ∃ v ∈ roots, Reaches h v l

/-- **The types of a crossing's positions** (the draft, Definitions,
"Read-only types and crossings"): each position below the root has the type
its parent's type gives it at the step, an own field the type does not
mention having `unknown`; `RO` is the draft's read-only types, closed under
the types of children ("from that position on, every position is
read-only"). -/
structure TypeView where
  Ty : Type
  child : Ty → Label → Ty
  RO : Ty → Prop
  ro_child : ∀ t a, RO t → RO (child t a)

namespace TypeView
variable (tv : TypeView)

/-- The type of the position a path ends at, from the root's type. -/
def typeAt (T : tv.Ty) (π : List Label) : tv.Ty := π.foldl tv.child T

/-- **A read-only path** `ro_T(π)`: some prefix of the path ends at a
position whose type is read-only throughout. -/
def roPath (T : tv.Ty) (π : List Label) : Prop := ∃ π₁ π₂, π = π₁ ++ π₂ ∧ tv.RO (tv.typeAt T π₁)

theorem ro_at {T : tv.Ty} {π : List Label} (h : tv.RO T) : tv.RO (tv.typeAt T π) := by
  induction π generalizing T with
  | nil => exact h
  | cons a π ih => exact ih (tv.ro_child T a h)

/-- **A path is read-only exactly when its last position's type is**: the
read-only types are closed under children. -/
theorem roPath_iff {T : tv.Ty} {π : List Label} : tv.roPath T π ↔ tv.RO (tv.typeAt T π) := by
  constructor
  · rintro ⟨π₁, π₂, rfl, h⟩
    simp only [TypeView.typeAt, List.foldl_append]
    exact tv.ro_at h
  · intro h; exact ⟨π, [], by simp, h⟩

end TypeView

/-- **Read-only reach** `Reach^ro_T(v, h)`: the locations a path from `v`
reaches that is read-only for the crossing type `T`. -/
def ReachRO (tv : TypeView) (T : tv.Ty) (h : Heap) (v : Val) (l : Nat) : Prop :=
  ∃ π, Follows h v π l ∧ tv.roPath T π

/-! ## Paths of a well-formed heap -/

theorem slot_mem_refs {fs : List (PropKey × Nat)} {c : CallCode} {i : Nat} {k : PropKey} {l : Nat}
    (h : (k, l) ∈ fs) : Ref.slot k l ∈ refs (.objAt fs c i) := by
  have : Ref.slot k l ∈ objRefs fs i := List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(k, l), h, rfl⟩)
  cases c <;> simp only [refs] <;> first | exact this | exact List.mem_append_left _ this

theorem lt_of_role {s : IndexedHeap} {l : Nat} {r : Role} (h : roleAt s.W l = some r) : l < s.h.length := by
  have hl := roleAt_lt h
  have := s.ok.1.1
  simp only [toList, List.length_map] at this
  omega

theorem lt_of_slotRole {s : IndexedHeap} {k : PropKey} {l : Nat} (h : SlotRole k (roleAt s.W l)) :
    l < s.h.length := by
  cases hr : roleAt s.W l with
  | none => rw [hr] at h; exact h.elim
  | some r => exact lt_of_role hr

/-- **One step of a path from a valid value reaches an allocated
location.** -/
theorem next_lt {s : IndexedHeap} {v : Val} {a : Label} {l : Nat} (hv : RefsOk s.W v)
    (hn : next v a = some l) : l < s.h.length := by
  cases a with
  | key k =>
    simp only [next] at hn
    cases v
    case objAt fs c i =>
      simp only [fieldsOf] at hn
      exact lt_of_slotRole (hv _ (slot_mem_refs (c := c) (i := i) (lookup_mem_pair hn)))
    all_goals simp [fieldsOf] at hn
  | view =>
    simp only [next] at hn
    cases v
    case objAt fs c i =>
      cases c
      case view s' f n =>
        simp only [HeapKnowledge.descriptorSpine, Option.some.injEq] at hn
        rw [← hn]
        have := hv _ (by simp [refs] : Ref.view s' f n (fs.lookup arraySpineKey).isNone ∈ refs (.objAt fs (.view s' f n) i))
        exact lt_of_role this.2
      all_goals simp [HeapKnowledge.descriptorSpine] at hn
    all_goals simp [HeapKnowledge.descriptorSpine] at hn
  | cell i =>
    simp only [next] at hn
    cases v
    case arr ls =>
      simp only [spineEntries] at hn
      have hm : some l ∈ ls := by
        cases hi : ls[i]? with
        | none => rw [hi] at hn; cases hn
        | some o =>
          rw [hi] at hn
          simp only [Option.join_some] at hn
          subst hn
          exact List.mem_of_getElem? hi
      have : Ref.elem l ∈ refs (.arr ls) := by
        simp only [refs, spineRefs, List.mem_filterMap]
        exact ⟨some l, hm, rfl⟩
      exact lt_of_role (hv _ this)
    case viewSpine f cs =>
      simp only [spineEntries] at hn
      have hm : l ∈ cs := by
        cases hi : (cs.map some)[i]? with
        | none => rw [hi] at hn; cases hn
        | some o =>
          rw [hi] at hn
          simp only [Option.join_some] at hn
          subst hn
          simpa using List.mem_of_getElem? hi
      have : Ref.elem l ∈ refs (.viewSpine f cs) := by
        simp only [refs, List.mem_map]
        exact ⟨l, hm, rfl⟩
      exact lt_of_role (hv _ this)
    all_goals simp [spineEntries] at hn

/-- The contents of an allocated location of a well-formed heap are valid. -/
theorem contents_valid {s : IndexedHeap} {l : Nat} {v : Val} (hl : l < s.h.length) (hv : s.h[l]? = some v) :
    RefsOk s.W v := by
  have hlen : l < (entries s.W).length := by
    have := s.ok.1.1
    simp only [toList, List.length_map] at this
    omega
  obtain ⟨r, hr⟩ := roleAt_some hlen
  obtain ⟨u, hu, -, hok⟩ := s.ok.2 l r hr
  rw [hv] at hu
  cases hu
  exact hok

/-- **A path of a well-formed heap from a valid value ends at an allocated
location.** -/
theorem follows_lt {s : IndexedHeap} :
    ∀ {v : Val} {π : List Label} {l : Nat}, RefsOk s.W v → Follows s.h v π l → l < s.h.length
  | _, [], _, _, h => h.elim
  | _, [_], _, hv, h => next_lt hv h
  | _, _ :: _ :: _, _, hv, ⟨_, _, hn, hl₀, hf⟩ =>
    follows_lt (contents_valid (next_lt hv hn) hl₀) hf

/-! ## Marks and the ghost state -/

/-- **The marks** (the draft, Definitions, "Marks, one per allocation
site"). -/
inductive Mark where
  | «local»
  | internal
  | exposed
  | released
  deriving DecidableEq

/-- **A package**: its allocation sites, each with its mark. -/
structure Package where
  Site : Type
  mark : Site → Mark

/-- **The ghost state** (the draft, "What the Lean states"): the site that
allocated each location, `none` for storage outside code allocated; each
field location's key, both fixed at allocation; the exposed locations `E`;
the history `A`, one set per active call of the package, bottom first; and
the between-calls record `B`. -/
structure Ghost (P : Package) where
  site : Nat → Option P.Site
  key : Nat → Option PropKey
  E : Nat → Prop
  A : List (Nat → Prop)
  B : Nat → Prop

namespace Ghost
variable {P : Package} (g : Ghost P)

/-- A location's mark `μ(l)`, `none` for `out`. -/
def origin (l : Nat) : Option Mark := (g.site l).map P.mark

/-- A released location or one outside code allocated: the origins whose
protection is decided by the history. -/
def Lent (l : Nat) : Prop := g.origin l = some .released ∨ g.origin l = none

/-- **The protected set**: a location recorded in a set of `A` or in `B`. -/
def Prot (l : Nat) : Prop := (∃ X ∈ g.A, X l) ∨ g.B l

/-- **The membership test** (the draft, "What the Lean states", the
membership test): `l ∈ R_P` when `l` is of a local or an exposed site, or
is released or outside storage recorded in `A` or `B`. -/
def InR (l : Nat) : Prop :=
  g.origin l = some .local ∨ g.origin l = some .exposed ∨ (g.Lent l ∧ g.Prot l)

/-- Adding the locations `N` to every set of `A`. -/
def add (N : Nat → Prop) : Ghost P := { g with A := g.A.map fun X l => X l ∨ N l }

end Ghost

/-! ## Crossings -/

/-- The direction of a crossing. -/
inductive Dir where
  | into
  | outOf

/-- **The locations an incoming crossing protects** (the draft, Crossings,
`N`): the released and outside locations a crossing into the package
reaches read-only; a crossing out of it protects none. -/
def Ghost.incoming {P : Package} (g : Ghost P) (tv : TypeView) (d : Dir) (T : tv.Ty) (h : Heap) (v : Val)
    (l : Nat) : Prop :=
  d = .into ∧ ReachRO tv T h v l ∧ g.Lent l

/-- **The crossing update** (the draft, Crossings): the exposed locations
the crossing reaches read-only join `E`, in either direction, and those of
`N` join every set of `A`. -/
def Ghost.cross {P : Package} (g : Ghost P) (tv : TypeView) (d : Dir) (T : tv.Ty) (h : Heap) (v : Val) :
    Ghost P :=
  { g.add (g.incoming tv d T h v) with
    E := fun l => g.E l ∨ (ReachRO tv T h v l ∧ g.origin l = some .exposed) }

/-! ## The history -/

/-- The record `B` after an exit that leaves the calls `A₀` active: when
none is, the popped set's locations the package still holds. -/
def exitRecord {P : Package} (g : Ghost P) (A₀ : List (Nat → Prop)) (X held : Nat → Prop) : Nat → Prop :=
  match A₀ with
  | [] => fun l => X l ∧ held l
  | _ :: _ => g.B

/-- A call's exit, normal or exceptional: both pop its own set. -/
inductive Exit where
  | normal
  | exceptional

/-- **The history's transitions** (the draft, "What the Lean states", the
history): a call's entry pushes the protected set, `B` among it; a crossing
updates `E` and `A`; a hold that makes locations `N` protected adds them to
every set; each exit, normal or exceptional, pops the top set, and when it
leaves no call active `B` becomes the popped set's locations the package
still holds (`held`); a step outside every call removes from `B` each
location no longer held. The marks and keys are untouched. -/
inductive HStep {P : Package} (tv : TypeView) (h : Heap) : Ghost P → Ghost P → Prop
  | enter (g : Ghost P) : HStep tv h g { g with A := g.A ++ [g.Prot] }
  | cross (g : Ghost P) (d : Dir) (T : tv.Ty) (v : Val) : HStep tv h g (g.cross tv d T h v)
  | hold (g : Ghost P) (N : Nat → Prop) : HStep tv h g (g.add N)
  | exit (g : Ghost P) (x : Exit) (held : Nat → Prop) (A₀ : List (Nat → Prop)) (X : Nat → Prop)
      (hA : g.A = A₀ ++ [X]) : HStep tv h g { g with A := A₀, B := exitRecord g A₀ X held }
  | drop (g : Ghost P) (held : Nat → Prop) (hA : g.A = []) :
      HStep tv h g { g with B := fun l => g.B l ∧ held l }

/-- **Every set of the history is the protected set.** -/
def Ghost.Uniform {P : Package} (g : Ghost P) : Prop := ∀ X ∈ g.A, ∀ l, X l ↔ g.Prot l

theorem Ghost.uniform_empty {P : Package} {g : Ghost P} (hA : g.A = []) : g.Uniform := by
  intro X hX; rw [hA] at hX; cases hX

theorem Ghost.prot_add {P : Package} {g : Ghost P} {N : Nat → Prop} {l : Nat} (hp : g.Prot l) :
    (g.add N).Prot l := by
  rcases hp with ⟨X, hX, hx⟩ | hb
  · exact .inl ⟨_, List.mem_map.mpr ⟨X, hX, rfl⟩, .inl hx⟩
  · exact .inr hb

theorem Ghost.uniform_add {P : Package} {g : Ghost P} (N : Nat → Prop) (hu : g.Uniform) :
    (g.add N).Uniform := by
  intro X' hX' l
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hX'
  constructor
  · intro hl; exact .inl ⟨_, hX', hl⟩
  · rintro (⟨Y', hY', hy⟩ | hb)
    · obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hY'
      rcases hy with hy | hn
      · exact .inl ((hu X hX l).mpr ((hu Y hY l).mp hy))
      · exact .inr hn
    · exact .inl ((hu X hX l).mpr (.inr hb))

/-- **The sets of overlapping calls grow together**: every transition keeps
each set of `A` equal to the protected set. -/
theorem HStep.uniform {P : Package} {tv : TypeView} {h : Heap} {g g' : Ghost P} (hs : HStep tv h g g')
    (hu : g.Uniform) : g'.Uniform := by
  cases hs with
  | enter =>
    intro X hX l
    simp only [List.mem_append, List.mem_singleton] at hX
    have hp : (g.Prot l) ↔ ({ g with A := g.A ++ [g.Prot] } : Ghost P).Prot l := by
      constructor
      · rintro (⟨Y, hY, hy⟩ | hb)
        · exact .inl ⟨Y, List.mem_append_left _ hY, hy⟩
        · exact .inr hb
      · rintro (⟨Y, hY, hy⟩ | hb)
        · simp only [List.mem_append, List.mem_singleton] at hY
          rcases hY with hY | rfl
          · exact (hu Y hY l).mp hy
          · exact hy
        · exact .inr hb
    rcases hX with hX | rfl
    · exact (hu X hX l).trans hp
    · exact hp
  | cross d T v => exact Ghost.uniform_add _ hu
  | hold N => exact Ghost.uniform_add _ hu
  | exit x held A₀ X hA =>
    intro Y hY l
    cases A₀ with
    | nil => cases hY
    | cons Z A₁ =>
      have hY₀ : Y ∈ g.A := by rw [hA]; exact List.mem_append_left _ hY
      refine (hu Y hY₀ l).trans ⟨fun hp => ?_, fun hp => ?_⟩
      · exact .inl ⟨Y, hY, (hu Y hY₀ l).mpr hp⟩
      · rcases hp with ⟨W, hW, hw⟩ | hb
        · have hW₀ : W ∈ g.A := by rw [hA]; exact List.mem_append_left _ hW
          exact (hu W hW₀ l).mp hw
        · exact .inr hb
  | drop held hA => exact Ghost.uniform_empty hA

/-! ## The history inside a call -/

/-- **The history grows inside a call at depth `d`** (the draft, (L3), the
relation on histories): at least `d` calls are active at both ends, `B` is
kept, every protected location stays protected and `E` only grows. -/
structure Grows {P : Package} (d : Nat) (g g' : Ghost P) : Prop where
  pos : 0 < d
  len : d ≤ g.A.length
  len' : d ≤ g'.A.length
  record : g'.B = g.B
  prot : ∀ l, g.Prot l → g'.Prot l
  exposed : ∀ l, g.E l → g'.E l

theorem Grows.refl {P : Package} {d : Nat} {g : Ghost P} (hd : 0 < d) (hl : d ≤ g.A.length) : Grows d g g :=
  ⟨hd, hl, hl, rfl, fun _ h => h, fun _ h => h⟩

theorem Grows.trans {P : Package} {d : Nat} {g g' g'' : Ghost P} (h₁ : Grows d g g') (h₂ : Grows d g' g'') :
    Grows d g g'' :=
  ⟨h₁.pos, h₁.len, h₂.len', h₂.record.trans h₁.record, fun l h => h₂.prot l (h₁.prot l h),
    fun l h => h₂.exposed l (h₁.exposed l h)⟩

/-- **A transition inside a call grows the history**: from a uniform history
with at least `d ≥ 1` calls active, a transition that leaves at least `d`
active keeps `B` and every protected location. -/
theorem HStep.grows {P : Package} {tv : TypeView} {h : Heap} {d : Nat} {g g' : Ghost P}
    (hs : HStep tv h g g') (hu : g.Uniform) (hd : 0 < d) (hl : d ≤ g.A.length) (hl' : d ≤ g'.A.length) :
    Grows d g g' := by
  cases hs with
  | enter =>
    exact ⟨hd, hl, hl', rfl, fun l hp => hp.elim (fun ⟨Y, hY, hy⟩ => .inl ⟨Y, List.mem_append_left _ hY, hy⟩) .inr,
      fun _ h => h⟩
  | cross d' T v => exact ⟨hd, hl, hl', rfl, fun _ hp => Ghost.prot_add hp, fun _ h => .inl h⟩
  | hold N => exact ⟨hd, hl, hl', rfl, fun _ hp => Ghost.prot_add hp, fun _ h => h⟩
  | exit x held A₀ X hA =>
    cases A₀ with
    | nil => simp at hl'; omega
    | cons Z A₁ =>
      refine ⟨hd, hl, hl', rfl, fun l hp => ?_, fun _ h => h⟩
      have hZ : Z ∈ g.A := by rw [hA]; exact List.mem_append_left _ (List.mem_cons_self ..)
      exact .inl ⟨Z, List.mem_cons_self .., (hu Z hZ l).mpr hp⟩
  | drop held hA => rw [hA] at hl; simp at hl; omega

/-- **A sequence of history transitions**, each at the heap of its step. -/
inductive HSteps {P : Package} (tv : TypeView) (d : Nat) : Ghost P → Ghost P → Prop
  | refl (g : Ghost P) : HSteps tv d g g
  | step {g g' g'' : Ghost P} (h : Heap) : HStep tv h g g' → d ≤ g'.A.length → HSteps tv d g' g'' →
      HSteps tv d g g''

/-- **The history across a nested call** (the draft, (L3), composition over
the history): from a uniform history inside a call at depth `d ≥ 1`, a
sequence of transitions none of which pops below depth `d` (a nested
call's entry, its steps and its normal or exceptional exit among them)
grows the history and leaves it uniform. -/
theorem HSteps.grows {P : Package} {tv : TypeView} {d : Nat} {g g' : Ghost P} (hs : HSteps tv d g g')
    (hu : g.Uniform) (hd : 0 < d) (hl : d ≤ g.A.length) : Grows d g g' ∧ g'.Uniform := by
  induction hs with
  | refl g => exact ⟨Grows.refl hd hl, hu⟩
  | step h hst hl' _ ih =>
    obtain ⟨hg, hu'⟩ := ih (hst.uniform hu) hl'
    exact ⟨(hst.grows hu hd hl hl').trans hg, hu'⟩

/-! ## The region inside a call -/

/-- **The region only grows inside a call**: with the location's site kept,
a location of `R_P` stays in it as the history grows. -/
theorem InR.mono {P : Package} {d : Nat} {g g' : Ghost P} {l : Nat} (hg : Grows d g g')
    (hs : g'.site l = g.site l) (hr : g.InR l) : g'.InR l := by
  have ho : g'.origin l = g.origin l := by simp only [Ghost.origin, hs]
  rcases hr with h | h | ⟨hL, hp⟩
  · exact .inl (ho.trans h)
  · exact .inr (.inl (ho.trans h))
  · exact .inr (.inr ⟨by unfold Ghost.Lent; rw [ho]; exact hL, hg.prot l hp⟩)

/-- **Protection ends at the outermost exit**: a location recorded only in
the outermost call's set, which the package no longer holds, is not
protected once that call exits, normally or exceptionally. The region grows
only inside a call (`InR.mono`); across the outermost exit it may shrink. -/
theorem exit_unprotects {P : Package} {tv : TypeView} {h : Heap} {g : Ghost P} {X held : Nat → Prop}
    {l : Nat} (x : Exit) (hA : g.A = [X]) (hn : ¬ held l) :
    HStep tv h g { g with A := [], B := exitRecord g [] X held } ∧
      ¬ ({ g with A := [], B := exitRecord g [] X held } : Ghost P).Prot l := by
  refine ⟨.exit g x held [] X (by simpa using hA), ?_⟩
  rintro (⟨Y, hY, -⟩ | ⟨-, hl⟩)
  · cases hY
  · exact hn hl

end Verification.TolerantFrames.ReadOnly
