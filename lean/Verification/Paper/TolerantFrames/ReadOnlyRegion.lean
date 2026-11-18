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

/-! ## The values outside code holds -/

section Roots
variable (ofC : ComponentTag → Bool)

mutual
/-- **The values held at the positions of outside code** (the draft,
"Frames and whose code runs"; `ofC` tells the tags whose code is the
package's, `o` whether the position runs outside code): objects, spines and
view spines, a frame's or a `goto`'s positions run by its own tag. A bound
function holds the values it saved and a closure of outside code those of
its code (node expressions and captures, `codeVals`); a closure whose code
is the package's holds none outside code reaches without calling it. An
allocation of a typed array holds its view spine, as the object it
allocates names it. -/
def vals (o : Bool) : Tm → List Val
  | .var _ => []
  | .invoke f r args => vals o f ++ vals o r ++ valsArgs o args
  | .construct f args => vals o f ++ valsArgs o args
  | .letE a b => vals o a ++ vals o b
  | .objAt fs .absent i => if o then [.objAt fs .absent i] else []
  | .objAt fs (.view s f n) i => if o then [.objAt fs (.view s f n) i] else []
  | .objAt fs (.bound t r pre) i =>
    if o then .objAt fs (.bound t r pre) i :: (vals true t ++ vals true r ++ valsArgs true pre) else []
  | .objAt fs (.graph n E K s caps k r comp) i =>
    if o then .objAt fs (.graph n E K s caps k r comp) i ::
      (if ofC comp then [] else valsArgs true E ++ valsArgs true caps) else []
  | .makeAt .absent _ xs => valsArgs o xs
  | .makeAt (.view s f n) _ xs => (if o then [.objAt [] (.view s f n) 0] else []) ++ valsArgs o xs
  | .makeAt (.bound t r pre) _ xs => (vals o t ++ vals o r ++ valsArgs o pre) ++ valsArgs o xs
  | .makeAt (.graph _ E _ _ caps _ _ comp) _ xs =>
    (if o && !ofC comp then valsArgs true E ++ valsArgs true caps else []) ++ valsArgs o xs
  | .readAt _ a => vals o a
  | .indexAt a key => vals o a ++ vals o key
  | .writeAt _ a b => vals o a ++ vals o b
  | .test _ a => vals o a
  | .ite x a b => vals o x ++ vals o a ++ vals o b
  | .arith _ a b => vals o a ++ vals o b
  | .arr ls => if o then [.arr ls] else []
  | .viewSpine f cs => if o then [.viewSpine f cs] else []
  | .arrLit xs => valsArgs o xs
  | .elemAt a i => vals o a ++ vals o i
  | .setElem a i v => vals o a ++ vals o i ++ vals o v
  | .lenOf a => vals o a
  | .spread a => vals o a
  | .throw a => vals o a
  | .merge _ a b => vals o a ++ vals o b
  | .makeKey k a => vals o k ++ vals o a
  | .goto E _ _ L d comp => if ofC comp then [] else valsArgs true E ++ valsArgs true L ++ vals true d
  | .frame E _ t L d _ _ comp =>
    (if ofC comp then [] else valsArgs true E ++ valsArgs true L ++ vals true d) ++ vals (!ofC comp) t
  | _ => []
termination_by structural t => t

def valsArgs (o : Bool) : List Tm → List Val
  | [] => []
  | x :: xs => vals o x ++ valsArgs o xs
termination_by structural xs => xs
end

@[simp] theorem valsArgs_eq (o : Bool) (xs : List Tm) : valsArgs ofC o xs = xs.flatMap (vals ofC o) := by
  induction xs <;> simp_all [valsArgs]

/-- **The values a value's code holds**: a bound function's saved target,
receiver and arguments; a closure of outside code's node expressions and
captures. A closure whose code is the package's has none. -/
def codeVals : Val → List Val
  | .objAt _ (.bound t r pre) _ => vals ofC true t ++ vals ofC true r ++ valsArgs ofC true pre
  | .objAt _ (.graph _ E _ _ caps _ _ comp) _ =>
    if ofC comp then [] else valsArgs ofC true E ++ valsArgs ofC true caps
  | _ => []

/-- An object at a position of outside code holds itself and its code's
values. -/
theorem vals_objAt (fs : List (PropKey × Nat)) (cc : CallCode) (i : Nat) :
    vals ofC true (.objAt fs cc i) = .objAt fs cc i :: codeVals ofC (.objAt fs cc i) := by
  cases cc <;> simp [vals, codeVals]

end Roots

/-! ## Paths and read-only reach -/

/-- **A step of a path** (the draft, "What the Lean states", Paths): a
field key, the spine key `[]` among them, which reaches an array's spine;
a typed array's view spine; the element cell a spine lists at an index; or
the `i`-th value a value's code holds (`codeVals`). A collection's entries
are held in no location, so no step reaches them. -/
inductive Label where
  | key (k : PropKey)
  | view
  | cell (i : Nat)
  | code (i : Nat)

/-- The location one step reaches from the contents `v`; a step into code
reaches a value, no location. -/
def next (v : Val) : Label → Option Nat
  | .key k => (fieldsOf v).lookup k
  | .view => HeapKnowledge.descriptorSpine v
  | .cell i => match spineEntries v with
    | some ls => ls[i]?.join
    | none => none
  | .code _ => none

/-- **One step of a path between values**: through a location, its
contents in the heap; or into the code, a value the code holds. -/
def Succ (ofC : ComponentTag → Bool) (h : Heap) (v : Val) (a : Label) (v₀ : Val) : Prop :=
  (∃ l₀, next v a = some l₀ ∧ h[l₀]? = some v₀) ∨ ∃ i, a = .code i ∧ (codeVals ofC v)[i]? = some v₀

/-- **Following a path** `h ⊢ v →π l`: from the value `v`, each step
before the last goes through a location to its contents, or into the
code of a closure of outside code or of a bound function to a value it
holds; the last step reaches the location `l`. -/
def Follows (ofC : ComponentTag → Bool) (h : Heap) : Val → List Label → Nat → Prop
  | _, [], _ => False
  | v, [a], l => next v a = some l
  | v, a :: b :: π, l => ∃ v₀, Succ ofC h v a v₀ ∧ Follows ofC h v₀ (b :: π) l

/-- A location is reachable from a value through some path. -/
def Reaches (ofC : ComponentTag → Bool) (h : Heap) (v : Val) (l : Nat) : Prop := ∃ π, Follows ofC h v π l

/-- A location is reachable from one of the values `roots`. -/
def ReachesFrom (ofC : ComponentTag → Bool) (h : Heap) (roots : List Val) (l : Nat) : Prop :=
  ∃ v ∈ roots, Reaches ofC h v l

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
def ReachRO (tv : TypeView) (ofC : ComponentTag → Bool) (T : tv.Ty) (h : Heap) (v : Val) (l : Nat) : Prop :=
  ∃ π, Follows ofC h v π l ∧ tv.roPath T π

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

/-- **A value's references other than identities are valid**: no path
follows an identity. -/
def RefsOkN {k : Nat} (W : WorldT k) (v : Val) : Prop := ∀ r ∈ refs v, (∀ l, r ≠ .ident l) → RefOk W r

theorem RefsOk.refsOkN {k : Nat} {W : WorldT k} {v : Val} (h : RefsOk W v) : RefsOkN W v :=
  fun r hr _ => h r hr

/-- **The references of a value outside code holds**: the term's, but an
identity, or the view spine of a typed array's allocation, which the term
names in its descriptor. -/
theorem vals_refs {ofC : ComponentTag → Bool} (t : Tm) : ∀ o, ∀ u ∈ vals ofC o t, ∀ r ∈ refs u,
    r ∈ refs t ∨ (∃ l, r = .ident l) ∨ ∃ s f n p, r = .view s f n true ∧ Ref.view s f n p ∈ refs t := by
  induction t using Tm.induct
  case makeView s f n ns args ih =>
    intro o u hu r hr
    simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap] at hu
    rcases hu with hu | ⟨a, ha, hu⟩
    · split at hu
      · simp only [List.mem_singleton] at hu
        subst hu
        simp only [refs, objRefs, List.map_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, List.lookup_nil, Option.isNone_none] at hr
        rcases hr with rfl | rfl
        · exact .inr (.inl ⟨0, rfl⟩)
        · exact .inr (.inr ⟨s, f, n, !ns.contains arraySpineKey, rfl, by simp [refs]⟩)
      · simp at hu
    · rcases ih a ha o u hu r hr with h | h | ⟨s', f', n', p, h₁, h₂⟩
      · exact .inl (by simp only [refs, refsArgs_eq, List.mem_cons, List.mem_flatMap]; exact .inr ⟨a, ha, h⟩)
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨s', f', n', p, h₁, by
          simp only [refs, refsArgs_eq, List.mem_cons, List.mem_flatMap]; exact .inr ⟨a, ha, h₂⟩⟩)
  all_goals intro o u hu r hr
  all_goals simp only [vals, valsArgs_eq] at hu
  all_goals (repeat' split at hu)
  all_goals (try simp only [List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil,
    false_or, or_false] at hu)
  all_goals (try (subst hu; exact .inl hr))
  all_goals (try (rcases hu with rfl | hu; exact .inl hr))
  all_goals (simp only [refs, refsArgs_eq, objRefs, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.mem_map] at hr ⊢; grind)

/-- **The values outside code holds have valid references** where the term
does, identities aside. -/
theorem vals_refsOkN {k : Nat} {W : WorldT k} {ofC : ComponentTag → Bool} {t : Tm} {o : Bool} {u : Val}
    (ht : RefsOkN W t) (hu : u ∈ vals ofC o t) : RefsOkN W u := by
  intro r hr hn
  rcases vals_refs t o u hu r hr with h | ⟨l, rfl⟩ | ⟨s, f, n, p, rfl, hp⟩
  · exact ht r h hn
  · exact (hn l rfl).elim
  · have := ht _ hp (by simp)
    obtain ⟨rfl, hrole⟩ := this
    exact ⟨rfl, hrole⟩

/-- A value of a valid value's code has valid references, identities
aside. -/
theorem codeVals_refsOkN {k : Nat} {W : WorldT k} {ofC : ComponentTag → Bool} {v w : Val}
    (hv : RefsOkN W v) (hw : w ∈ codeVals ofC v) : RefsOkN W w := by
  cases v
  case objAt fs cc i =>
    have hm : w ∈ vals ofC true (.objAt fs cc i) := by rw [vals_objAt]; exact List.mem_cons_of_mem _ hw
    exact vals_refsOkN hv hm
  all_goals simp [codeVals] at hw

/-- **One step of a path from a valid value reaches an allocated
location.** -/
theorem next_lt {s : IndexedHeap} {v : Val} {a : Label} {l : Nat} (hv : RefsOkN s.W v)
    (hn : next v a = some l) : l < s.h.length := by
  cases a with
  | code => cases hn
  | key k =>
    simp only [next] at hn
    cases v
    case objAt fs c i =>
      simp only [fieldsOf] at hn
      exact lt_of_slotRole (hv _ (slot_mem_refs (c := c) (i := i) (lookup_mem_pair hn)) (by simp))
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
          (by simp)
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
      exact lt_of_role (hv _ this (by simp))
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
      exact lt_of_role (hv _ this (by simp))
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
theorem follows_lt {s : IndexedHeap} {ofC : ComponentTag → Bool} :
    ∀ {v : Val} {π : List Label} {l : Nat}, RefsOkN s.W v → Follows ofC s.h v π l → l < s.h.length
  | _, [], _, _, h => h.elim
  | _, [_], _, hv, h => next_lt hv h
  | _, _ :: _ :: _, _, hv, ⟨_, .inl ⟨_, hn, hl₀⟩, hf⟩ =>
    follows_lt (RefsOk.refsOkN (contents_valid (next_lt hv hn) hl₀)) hf
  | _, _ :: _ :: _, _, hv, ⟨_, .inr ⟨_, _, hc⟩, hf⟩ =>
    follows_lt (codeVals_refsOkN hv (List.mem_of_getElem? hc)) hf

/-! ## Code steps and the first locations of paths -/

/-- **Code steps**: the values a value's code holds, and theirs. -/
inductive CodeReach (ofC : ComponentTag → Bool) : Val → Val → Prop
  | refl (v : Val) : CodeReach ofC v v
  | step {v x w : Val} : x ∈ codeVals ofC v → CodeReach ofC x w → CodeReach ofC v w

/-- **The locations a path's first location step reaches from `u`**: one
location step from `u`, or from a value code steps reach from `u`. -/
def Leaves (ofC : ComponentTag → Bool) (u : Val) (l : Nat) : Prop :=
  ∃ x, CodeReach ofC u x ∧ ∃ a, next x a = some l

theorem Leaves.of_next {ofC : ComponentTag → Bool} {u : Val} {a : Label} {l : Nat} (hn : next u a = some l) :
    Leaves ofC u l :=
  ⟨u, .refl u, a, hn⟩

theorem Leaves.code {ofC : ComponentTag → Bool} {u x : Val} {l : Nat} (hx : x ∈ codeVals ofC u)
    (hl : Leaves ofC x l) : Leaves ofC u l :=
  let ⟨y, hy, a, hn⟩ := hl
  ⟨y, .step hx hy, a, hn⟩

/-- A first location of a path is either a location step of the value
itself or a first location of a value its code holds. -/
theorem Leaves.cases {ofC : ComponentTag → Bool} {u : Val} {l : Nat} (hl : Leaves ofC u l) :
    (∃ a, next u a = some l) ∨ ∃ x ∈ codeVals ofC u, Leaves ofC x l := by
  obtain ⟨y, hy, a, hn⟩ := hl
  cases hy with
  | refl => exact .inl ⟨a, hn⟩
  | step hx hxy => exact .inr ⟨_, hx, _, hxy, a, hn⟩

theorem codeReach_reaches {ofC : ComponentTag → Bool} {h : Heap} {v w : Val} (hw : CodeReach ofC v w) :
    ∀ {a : Label} {l : Nat}, next w a = some l → Reaches ofC h v l := by
  induction hw with
  | refl => intro a l hn; exact ⟨[a], hn⟩
  | step hx _ ih =>
    intro a l hn
    obtain ⟨π, hf⟩ := ih hn
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    match π, hf with
    | b :: π', hf => exact ⟨.code i :: b :: π', ⟨_, .inr ⟨i, rfl, hi⟩, hf⟩⟩

theorem Leaves.reaches {ofC : ComponentTag → Bool} {h : Heap} {u : Val} {l : Nat} (hl : Leaves ofC u l) :
    Reaches ofC h u l :=
  let ⟨_, hy, _, hn⟩ := hl
  codeReach_reaches hy hn

theorem CodeReach.refsOkN {k : Nat} {W : WorldT k} {ofC : ComponentTag → Bool} {v w : Val}
    (hw : CodeReach ofC v w) (hv : RefsOkN W v) : RefsOkN W w := by
  induction hw with
  | refl => exact hv
  | step hx _ ih => exact ih (codeVals_refsOkN hv hx)

/-- **A first location of a path from a valid value is allocated.** -/
theorem Leaves.lt {s : IndexedHeap} {ofC : ComponentTag → Bool} {u : Val} {l : Nat} (hu : RefsOkN s.W u)
    (hl : Leaves ofC u l) : l < s.h.length :=
  let ⟨_, hy, _, hn⟩ := hl
  next_lt (hy.refsOkN hu) hn

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
  /-- The tags whose code is the package's. -/
  ofC : ComponentTag → Bool

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
  d = .into ∧ ReachRO tv P.ofC T h v l ∧ g.Lent l

/-- **The crossing update** (the draft, Crossings): the exposed locations
the crossing reaches read-only join `E`, in either direction, and those of
`N` join every set of `A`. -/
def Ghost.cross {P : Package} (g : Ghost P) (tv : TypeView) (d : Dir) (T : tv.Ty) (h : Heap) (v : Val) :
    Ghost P :=
  { g.add (g.incoming tv d T h v) with
    E := fun l => g.E l ∨ (ReachRO tv P.ofC T h v l ∧ g.origin l = some .exposed) }

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
