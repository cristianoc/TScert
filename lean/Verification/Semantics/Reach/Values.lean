import Verification.Semantics.IndexedStates

/-! # The values a term holds and the locations they reach

`vals` collects the values a term holds; `Reaches` and `ReachesFrom` are
the locations those values reach through the heap, field by field, cell by
cell and through the captures of closures (`CodeReach`). -/

namespace Verification.TolerantFrames.Reach

open Verification Footprints

/-- A code: the expressions of its nodes, and their continuations and handlers. -/
abbrev Code := List Tm × List (ControlFlow.Continuation × Option ControlFlow.Target)

/-- **The realm's code and the calls of a native** (Read-only frames, its
natives item; the draft "Framed acceptance", Natives): the tags of the
realm's code, the code of the standard natives, and the node keys at which
a frame calls a native, each read with the frame's code and tag. A frame
of the realm's code is owned by the frame that called it where that frame
is suspended at a native-call key, and by the client otherwise. Every call
node of the realm's own code is a native-call key (`native_realm`): a
native's run, the realm's calls of its own code included, is one run of
the frame that called it (Read-only frames, the natives item: "A standard
native's steps are the component's when the component's code calls it at a
call of a native"). -/
structure Realm where
  tags : ComponentTag → Bool
  native : (List Tm × List (ControlFlow.Continuation × Option ControlFlow.Target)) × ComponentTag →
    ControlFlow.Continuation × Option ControlFlow.Target → Bool
  native_realm : ∀ m kx, tags m.2 = true → native m kx = true

/-- The realm of a program with no realm code. -/
def Realm.empty : Realm := ⟨fun _ => false, fun _ _ => false, fun _ _ h => h⟩

/-- The realm at which every frame is the realm's, called at a native-call
key: every frame takes its caller's owner, so a reading at it is the
widest (`vals_all`). The values of code are read at it. -/
def Realm.all : Realm := ⟨fun _ => true, fun _ _ => true, fun _ _ _ => rfl⟩

/-- **The owner of a frame** tagged `comp` whose caller is owned by `c`, `nk`
telling whether the caller is suspended at a native-call key: the caller's
owner for a frame of the realm's code called at a native-call key, the
client `none` for one called elsewhere, its own tag for any other frame. -/
def Realm.own (rl : Realm) (c : ComponentTag) (nk : Bool) (comp : ComponentTag) : ComponentTag :=
  if rl.tags comp then (if nk then c else none) else comp

/-- **Whether a frame's positions run outside code**, the frame tagged
`comp` and its caller's positions' flag `o`: the flag of its owner
(`Realm.flag_own`). -/
def Realm.flag (rl : Realm) (ofC : ComponentTag → Bool) (o nk : Bool) (comp : ComponentTag) : Bool :=
  if rl.tags comp then (if nk then o else !ofC none) else !ofC comp

theorem Realm.flag_own (rl : Realm) (ofC : ComponentTag → Bool) {c : ComponentTag} {o : Bool} (ho : (!ofC c) = o)
    (nk : Bool) (comp : ComponentTag) : rl.flag ofC o nk comp = !ofC (rl.own c nk comp) := by
  unfold Realm.flag Realm.own
  by_cases h : rl.tags comp = true
  · cases nk <;> simp [h, ho]
  · simp [h]

@[simp] theorem Realm.flag_empty (ofC : ComponentTag → Bool) (o nk : Bool) (comp : ComponentTag) :
    Realm.empty.flag ofC o nk comp = !ofC comp := rfl

/-- A frame whose positions are outside code's runs no code `ofC` names,
where no realm tag is one `ofC` names. -/
theorem Realm.ofC_of_flag {rl : Realm} {ofC : ComponentTag → Bool} (hrl : ∀ t, rl.tags t = true → ofC t = false)
    {o nk : Bool} {comp : ComponentTag} (h : rl.flag ofC o nk comp = true) : ofC comp = false := by
  unfold Realm.flag at h
  by_cases ht : rl.tags comp = true
  · exact hrl _ ht
  · simpa [ht] using h

@[simp] theorem Realm.flag_all (ofC : ComponentTag → Bool) (o : Bool) (comp : ComponentTag) :
    Realm.all.flag ofC o true comp = o := rfl

@[simp] theorem Realm.native_all (m : (List Tm × List (ControlFlow.Continuation × Option ControlFlow.Target)) × ComponentTag)
    (kx : ControlFlow.Continuation × Option ControlFlow.Target) : Realm.all.native m kx = true := rfl

@[simp] theorem Realm.native_empty
    (m : (List Tm × List (ControlFlow.Continuation × Option ControlFlow.Target)) × ComponentTag)
    (kx : ControlFlow.Continuation × Option ControlFlow.Target) : Realm.empty.native m kx = false := rfl

@[simp] theorem Realm.tags_empty (t : ComponentTag) : Realm.empty.tags t = false := rfl

@[simp] theorem Realm.own_empty (c : ComponentTag) (nk : Bool) (comp : ComponentTag) :
    Realm.empty.own c nk comp = comp := rfl

section Roots

variable (ofC : ComponentTag → Bool)

mutual
/-- **The values held at the positions of outside code** (the draft,
"Frames and whose code runs"; `ofC` tells the tags whose code is the
package's, `o` whether the position runs outside code, `nk` whether the
frame around it is suspended at a native-call key): objects, spines and
view spines, a frame's or a `goto`'s positions run by its owner
(`Realm.flag`, the flag of `Realm.own`). A value's code, and a frame's
code, environment and default, are read at `Realm.all`, the widest
reading (`vals_all`). A bound
function holds the values it saved and a closure of outside code those of
its code (node expressions and captures, `codeVals`); a closure whose code
is the package's holds none outside code reaches without calling it. An
allocation of a typed array holds its view spine, as the object it
allocates names it. -/
def vals (rl : Realm) (o nk : Bool) : Tm → List Val
  | .var _ => []
  | .invoke f r args => vals rl o nk f ++ vals rl o nk r ++ valsArgs rl o nk args
  | .construct f args => vals rl o nk f ++ valsArgs rl o nk args
  | .letE a b => vals rl o nk a ++ vals rl o nk b
  | .objAt fs .absent i => if o then [.objAt fs .absent i] else []
  | .objAt fs (.view s f n) i => if o then [.objAt fs (.view s f n) i] else []
  | .objAt fs (.bound t r pre) i =>
    if o then .objAt fs (.bound t r pre) i :: (vals Realm.all true true t ++ vals Realm.all true true r ++ valsArgs Realm.all true true pre) else []
  | .objAt fs (.graph n E K s caps k r comp) i =>
    if o then .objAt fs (.graph n E K s caps k r comp) i ::
      (if ofC comp then [] else valsArgs Realm.all true true E ++ valsArgs Realm.all true true caps) else []
  | .makeAt .absent _ xs => valsArgs rl o nk xs
  | .makeAt (.view s f n) _ xs => (if o then [.objAt [] (.view s f n) 0] else []) ++ valsArgs rl o nk xs
  | .makeAt (.bound t r pre) _ xs => (vals Realm.all o true t ++ vals Realm.all o true r ++ valsArgs Realm.all o true pre) ++ valsArgs rl o nk xs
  | .makeAt (.graph _ E _ _ caps _ _ comp) _ xs =>
    (if o && !ofC comp then valsArgs Realm.all true true E ++ valsArgs Realm.all true true caps else []) ++ valsArgs rl o nk xs
  | .readAt _ a => vals rl o nk a
  | .indexAt a key => vals rl o nk a ++ vals rl o nk key
  | .writeAt _ a b => vals rl o nk a ++ vals rl o nk b
  | .test _ a => vals rl o nk a
  | .ite x a b => vals rl o nk x ++ vals rl o nk a ++ vals rl o nk b
  | .arith _ a b => vals rl o nk a ++ vals rl o nk b
  | .arr ls => if o then [.arr ls] else []
  | .viewSpine f cs => if o then [.viewSpine f cs] else []
  | .arrLit xs => valsArgs rl o nk xs
  | .elemAt a i => vals rl o nk a ++ vals rl o nk i
  | .setElem a i v => vals rl o nk a ++ vals rl o nk i ++ vals rl o nk v
  | .lenOf a => vals rl o nk a
  | .spread a => vals rl o nk a
  | .throw a => vals rl o nk a
  | .merge _ a b => vals rl o nk a ++ vals rl o nk b
  | .makeKey k a => vals rl o nk k ++ vals rl o nk a
  | .goto E _ _ L d comp =>
    if rl.flag ofC o nk comp then valsArgs Realm.all true true E ++ valsArgs Realm.all true true L ++
      vals Realm.all true true d else []
  | .frame E K t L d k x comp =>
    (if rl.flag ofC o nk comp then valsArgs Realm.all true true E ++ valsArgs Realm.all true true L ++
      vals Realm.all true true d else []) ++ vals rl (rl.flag ofC o nk comp) (rl.native ((E, K), comp) (k, x)) t
  | _ => []
termination_by structural t => t

def valsArgs (rl : Realm) (o nk : Bool) : List Tm → List Val
  | [] => []
  | x :: xs => vals rl o nk x ++ valsArgs rl o nk xs
termination_by structural xs => xs
end

@[simp] theorem valsArgs_eq (rl : Realm) (o nk : Bool) (xs : List Tm) :
    valsArgs ofC rl o nk xs = xs.flatMap (vals ofC rl o nk) := by
  induction xs <;> simp_all [valsArgs]

/-- **The values a value's code holds**: a bound function's saved target,
receiver and arguments; a closure of outside code's node expressions and
captures. A closure whose code is the package's has none. -/
def codeVals : Val → List Val
  | .objAt _ (.bound t r pre) _ =>
    vals ofC Realm.all true true t ++ vals ofC Realm.all true true r ++ valsArgs ofC Realm.all true true pre
  | .objAt _ (.graph _ E _ _ caps _ _ comp) _ =>
    if ofC comp then [] else valsArgs ofC Realm.all true true E ++ valsArgs ofC Realm.all true true caps
  | _ => []

/-- An object at a position of outside code holds itself and its code's
values. -/
theorem vals_objAt (rl : Realm) (nk : Bool) (fs : List (PropKey × Nat)) (cc : CallCode) (i : Nat) :
    vals ofC rl true nk (.objAt fs cc i) = .objAt fs cc i :: codeVals ofC (.objAt fs cc i) := by
  cases cc <;> simp [vals, codeVals]

/-- A value holds no frame: its values are the same at every realm. -/
theorem vals_val (rl rl' : Realm) (o nk nk' : Bool) {v : Tm} (hv : isVal v = true) :
    vals ofC rl o nk v = vals ofC rl' o nk' v := by
  cases v with
  | objAt fs cc i => cases cc <;> simp [vals]
  | _ => simp_all [isVal, vals]

/-- **The widest reading**: the values held at the positions of outside
code at any realm, flag and key are among those at `Realm.all`, every
position outside code's. -/
theorem vals_all : ∀ (t : Tm) (rl : Realm) (o nk : Bool) {x : Val}, x ∈ vals ofC rl o nk t →
    x ∈ vals ofC Realm.all true true t := by
  intro t
  induction t using Tm.induct
  all_goals intro rl o nk x hx
  all_goals simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap, Realm.flag_all, Realm.native_all] at hx ⊢
  all_goals (repeat' split at hx) <;> (try split) <;> grind

end Roots

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
theorem vals_refs {ofC : ComponentTag → Bool} (t : Tm) : ∀ rl o nk, ∀ u ∈ vals ofC rl o nk t, ∀ r ∈ refs u,
    r ∈ refs t ∨ (∃ l, r = .ident l) ∨ ∃ s f n p, r = .view s f n true ∧ Ref.view s f n p ∈ refs t := by
  induction t using Tm.induct
  case makeView s f n ns args ih =>
    intro rl o nk u hu r hr
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
    · rcases ih a ha rl o nk u hu r hr with h | h | ⟨s', f', n', p, h₁, h₂⟩
      · exact .inl (by simp only [refs, refsArgs_eq, List.mem_cons, List.mem_flatMap]; exact .inr ⟨a, ha, h⟩)
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨s', f', n', p, h₁, by
          simp only [refs, refsArgs_eq, List.mem_cons, List.mem_flatMap]; exact .inr ⟨a, ha, h₂⟩⟩)
  all_goals intro rl o nk u hu r hr
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
theorem vals_refsOkN {k : Nat} {W : WorldT k} {ofC : ComponentTag → Bool} {t : Tm} {rl : Realm} {o nk : Bool}
    {u : Val} (ht : RefsOkN W t) (hu : u ∈ vals ofC rl o nk t) : RefsOkN W u := by
  intro r hr hn
  rcases vals_refs t rl o nk u hu r hr with h | ⟨l, rfl⟩ | ⟨s, f, n, p, rfl, hp⟩
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
    have hm : w ∈ vals ofC Realm.all true true (.objAt fs cc i) := by
      rw [vals_objAt]; exact List.mem_cons_of_mem _ hw
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

/-- **Code steps**: the values a value's code holds, and theirs. -/
inductive CodeReach (ofC : ComponentTag → Bool) : Val → Val → Prop
  | refl (v : Val) : CodeReach ofC v v
  | step {v x w : Val} : x ∈ codeVals ofC v → CodeReach ofC x w → CodeReach ofC v w

/-- **The locations a path's first location step reaches from `u`**: one
location step from `u`, or from a value code steps reach from `u`. -/
def Leaves (ofC : ComponentTag → Bool) (u : Val) (l : Nat) : Prop :=
  ∃ x, CodeReach ofC u x ∧ ∃ a, next x a = some l

theorem Leaves.code {ofC : ComponentTag → Bool} {u x : Val} {l : Nat} (hx : x ∈ codeVals ofC u)
    (hl : Leaves ofC x l) : Leaves ofC u l :=
  let ⟨y, hy, a, hn⟩ := hl
  ⟨y, .step hx hy, a, hn⟩

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
allocated each location, `none` for storage outside code allocated, fixed
at allocation; the exposed locations `E`;
the history `A`, one set per active call of the package, bottom first; and
the between-calls record `B`. -/
structure Ghost (P : Package) where
  site : Nat → Option P.Site
  E : Nat → Prop
  A : List (Nat → Prop)
  B : Nat → Prop

end Verification.TolerantFrames.Reach
