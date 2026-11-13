import Verification.Semantics.ExceptionalPosts
import Verification.Semantics.Purity
import Verification.Semantics.ClosedFootprints
import Verification.Semantics.IndexFacts
import Verification.Semantics.StoreRegions

/-! Call postconditions qualify the same receiver/arguments/result contract
as ordinary arrows. They concern calls admitted by that contract, not every
untyped invocation of a function. A call's footprint states which old
locations a normal return may have changed, and how; fresh allocation is
always permitted. Throws carry no return postcondition, just as in
`SafePost`. -/
namespace Verification.CallEffects
open HeapObservations

/-- A promise about the actual at `param`, whose type is then the signature's
result operand. `guards p` is a type guard's, `(x: A) => x is T`: the result
is `true` or `false`, and a `true` result leaves the actual at `p` in the
result operand. `asserts p` is an assertion function's,
`(x: A) => asserts x is T`: a normal return is `undefined`, and leaves the
actual at `p` in the result operand. -/
inductive TypePromise where
  | guards (param : Nat)
  | asserts (param : Nat)
  deriving Repr, DecidableEq

def TypePromise.param : TypePromise → Nat
  | .guards p | .asserts p => p

/-- A predicate of values by their kind: what an element fact states of
every present element of an array (`ElemsAt`). It reads no heap and no
world: `string`, `number`, `boolean`, `null`, `undefined`, and their unions,
the nullish exclusions among them. -/
structure ElemPred where
  nul : Bool := false
  undef : Bool := false
  bool : Bool := false
  num : Bool := false
  str : Bool := false
  big : Bool := false
  sym : Bool := false
  obj : Bool := false
  deriving Repr, DecidableEq, Hashable

def ElemPred.mem (R : ElemPred) : Tm → Bool
  | .nul => R.nul
  | .undef => R.undef
  | .tru | .fls => R.bool
  | .num _ => R.num
  | .str _ => R.str
  | .bigint _ => R.big
  | .sym _ => R.sym
  | .objAt .. => R.obj
  | _ => false

/-- Inclusion of predicates. -/
def ElemPred.le (a b : ElemPred) : Bool :=
  (!a.nul || b.nul) && (!a.undef || b.undef) && (!a.bool || b.bool) && (!a.num || b.num) &&
    (!a.str || b.str) && (!a.big || b.big) && (!a.sym || b.sym) && (!a.obj || b.obj)

theorem ElemPred.le_sound {a b : ElemPred} (h : a.le b = true) {v : Tm} (hv : a.mem v = true) :
    b.mem v = true := by
  simp only [ElemPred.le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  cases v <;> simp_all [ElemPred.mem] <;> omega

/-- **The elements fact** of a value `r` at a heap: `r`'s array store exists
and every element location it lists holds a value meeting `R`. A hole lists
no location, so the fact is about present elements. -/
def ElemsAt (R : ElemPred) (r : Tm) (h : Heap) : Prop :=
  ∃ s ls, Footprints.storeOf r = some s ∧ h[s]? = some (.arr ls) ∧
    ∀ l, some l ∈ ls → ∃ v, h[l]? = some v ∧ R.mem v = true

theorem ElemsAt.mono {R R' : ElemPred} {r : Tm} {h : Heap} (hle : R.le R' = true) (he : ElemsAt R r h) :
    ElemsAt R' r h := by
  obtain ⟨s, ls, hs, hl, hall⟩ := he
  exact ⟨s, ls, hs, hl, fun l hm => let ⟨v, hv, hr⟩ := hall l hm; ⟨v, hv, ElemPred.le_sound hle hr⟩⟩

/-- What a typed array's element write keeps (`%ByteSet%`, a view's `fill`,
`copyWithin` and `set`; SOURCE-CONTRACTS.md, "Stated library types"). The
model holds a view's elements as a store (`viewElementsKey`), and a write
replaces entries of the stores of the views over the written bytes: every
old location holding no store keeps its value, and every store keeps its
length (`HeapKnowledge.Changes` with no object or number altered and every
store's length kept). -/
inductive ElementWrite where
  | stores
  /-- Besides, the element store of the view (the first actual) changed
  only at the index (the second actual, a safe integer below its length),
  whose entry is a location holding the value (the third actual): each
  element of a view is its own bytes of the buffer, and the value is one the
  view's element type holds unchanged (`%ByteSet%`'s exact signatures). -/
  | exact
  deriving Repr, DecidableEq

/-- The change an element write allows. -/
def ElementWrite.changes : ElementWrite → HeapKnowledge.Changes
  | _ => ⟨false, false, .length⟩

/-- An exact element write of the actuals `args`: where the store of
elements of `args[0]` held entries `ls`, it lists after the call the same
entries but at the safe integer `args[1]`, below their number, where it lists
a location holding `args[2]`. -/
def ExactWrite (args : List Tm) (before after : Heap) : Prop :=
  ∀ s ls, HeapKnowledge.elementsOf (args.getD 0 .undef) = some s → before[s]? = some (.arr ls) →
    ∃ ls' b, ∃ i : Nat, after[s]? = some (.arr ls') ∧ args.getD 1 .undef = .num b ∧
      SafeIntegers.SafeInt b (i : Int) ∧ i < ls.length ∧ (∀ j, j ≠ i → ls'[j]? = ls[j]?) ∧
      ∃ l, ls'[i]? = some (some l) ∧ after[l]? = some (args.getD 2 .undef)

/-- What an element write states of a call with actuals `args`: its change,
and, where exact, `ExactWrite`. -/
def ElementWrite.Holds (w : ElementWrite) (args : List Tm) (before after : Heap) : Prop :=
  w.changes.Holds before after ∧ (w = .exact → ExactWrite args before after)

theorem ExactWrite.prefix_left {args : List Tm} {before middle after : Heap} (hx : ExactWrite args middle after)
    (hprefix : before.IsPrefix middle) : ExactWrite args before after := by
  intro s ls hs hls
  apply hx s ls hs
  obtain ⟨t, rfl⟩ := hprefix
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hls).1, hls]

theorem ElementWrite.Holds.prefix_left {w : ElementWrite} {args : List Tm} {before middle after : Heap}
    (hx : w.Holds args middle after) (hprefix : before.IsPrefix middle) : w.Holds args before after :=
  ⟨hx.1.prefix_left hprefix, fun he => (hx.2 he).prefix_left hprefix⟩

/-- An element write of any actuals keeps what a write of stores does. -/
theorem ElementWrite.Holds.stores {w : ElementWrite} {args args' : List Tm} {before after : Heap}
    (h : w.Holds args before after) : ElementWrite.stores.Holds args' before after :=
  ⟨by cases w <;> exact h.1, fun he => by cases he⟩

/-- What a call signature guarantees beyond its contract: a closed footprint
(`Footprints.Closed`) bounding the change from its entry heap to the heap a
normal return leaves, and an optional promise. Without a promise the
signature's result operand is the result's type. `fresh` states that a normal
return's value has an array store allocated by the call; `receiverStore` that
the footprint bounds every old location but the receiver's array store, which
the call may change arbitrarily. `onThrow` states that the footprint also
bounds the change to the heap a throw leaves; a promise and `fresh` concern a
normal return alone. `receiverOwn` states that the footprint bounds every old
location but the receiver's own ones, its store's among them, which the call
may change arbitrarily; `freshObject` that a normal return's value is an
object every own location of which the call allocated. `requires` states a
precondition: the receiver's elements meet the predicate in the heap the call
starts in (`ElemsAt`); `pre` a precondition on the call's values: each index
fact holds of them in the heap the call starts in, read at the call's
positions (`callEnv`: 0 the receiver, `i + 1` the `i`-th actual), such as
`bound(1, 2, true)`, the second actual an index below the length of the first
actual's store; `elements` a promise: a normal return of `true` leaves the
receiver's elements meeting it; `receiverGrows` that a normal return changed
no old location but the receiver's store, which it extended
(`ReceiverGrows`), the actuals, where each is a value, appended in order
(`ReceiverAppends`); `elementWrite` that a normal return changed the heap as
a typed array's element write may (`ElementWrite.changes`). -/
structure Effect where
  /-- The closed bound of the frame (`Effect.frame`). -/
  closed : Footprints.Closed
  promise : Option TypePromise
  fresh : Bool
  receiverStore : Bool
  onThrow : Bool
  receiverOwn : Bool
  freshObject : Bool
  requires : Option ElemPred := none
  elements : Option ElemPred := none
  pre : List HeapKnowledge.IndexFact := []
  /-- Facts a normal return states, at the result (position `0`) and the
  call's positions one higher (`ensuresEnv`), in the heap it leaves. -/
  ensures : List HeapKnowledge.IndexFact := []
  /-- A normal return changed no old location but the receiver's store, which
  it extended (`ReceiverGrows`) by the actuals (`ReceiverAppends`). -/
  receiverGrows : Bool := false
  /-- A normal return changed the heap as a typed array's element write may
  (`ElementWrite.changes`). -/
  elementWrite : Option ElementWrite := none
  /-- The argument store regions of the frame (`Effect.frame`): the store
  each selects at the call's entry, read from a call position through a
  path of own data fields, may change arbitrarily (`"x.f[*]": "any"`). -/
  regions : List Footprints.ArgumentStoreRegion := []
  deriving Repr, DecidableEq

/-- The closed bound the frame implies, for conservative checks
(`Effect.within_closed`): the closed bound, or `top` where the frame states
store regions, whose selected locations may change whatever they hold. -/
def Effect.footprint (e : Effect) : Footprints.Closed :=
  if e.regions.isEmpty then e.closed else .top

theorem Effect.footprint_of_regions {e : Effect} (h : e.regions = []) : e.footprint = e.closed := by
  simp [Effect.footprint, h]

/-- A signature with a footprint and no promise. -/
def Effect.ofFootprint (c : Footprints.Closed) : Effect := ⟨c, none, false, false, false, false, false, none, none, [], [], false, none, []⟩

/-- A call's values by position: `0` the receiver, `i + 1` the `i`-th actual,
`undefined` past the last. -/
def callEnv (r : Tm) (args : List Tm) : Env := fun i => if i = 0 then r else args.getD (i - 1) .undef

/-- A return's values by position: `0` the result, `i + 1` the call's
position `i` (`callEnv`). -/
def ensuresEnv (v : Tm) (r : Tm) (args : List Tm) : Env := fun i => if i = 0 then v else callEnv r args (i - 1)

/-- Trailing `undefined` actuals are the positions a call passes none at. -/
theorem callEnv_pad (r : Tm) (args : List Tm) {pad : List Tm} (hpad : ∀ a ∈ pad, a = .undef) :
    callEnv r (args ++ pad) = callEnv r args := by
  funext i
  unfold callEnv
  split
  · rfl
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    by_cases hi : i - 1 < args.length
    · rw [List.getElem?_append_left hi]
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := args) (by omega)]
      cases hq : pad[i - 1 - args.length]? with
      | none => rfl
      | some a => simp only [Option.getD_some, Option.getD_none]; exact hpad a (List.mem_of_getElem? hq)

/-- A signature's precondition on a call with receiver `r` and actuals `args`
and the heap it starts in. -/
def Effect.Requires (e : Effect) (r : Tm) (args : List Tm) (h : Heap) : Prop :=
  (∀ R, e.requires = some R → ElemsAt R r h) ∧ ∀ F ∈ e.pre, F.HoldsAt (callEnv r args) h

theorem Effect.requires_none {e : Effect} (h : e.requires = none) (hp : e.pre = []) (r : Tm) (args : List Tm)
    (heap : Heap) : e.Requires r args heap :=
  ⟨fun R hR => (by rw [h] at hR; cases hR), fun F hF => (by rw [hp] at hF; cases hF)⟩

/-- An ordinary arrow's guarantee: none beyond its contract. -/
def Effect.ordinary : Effect := .ofFootprint .top

/-- One qualified call contract. `Args` distinguishes fixed argument lists
from a fixed prefix followed by an argument-pack contract. Mapping the type
operands preserves the effect by construction. -/
structure Contract (Receiver Args Result : Type) where
  receiver : Receiver
  arguments : Args
  result : Result
  effect : Effect
  deriving Repr, DecidableEq

def Contract.map (f : Receiver → Receiver') (g : Args → Args') (h : Result → Result')
    (s : Contract Receiver Args Result) : Contract Receiver' Args' Result' :=
  ⟨f s.receiver, g s.arguments, h s.result, s.effect⟩

/-- A host-relative method supplies its receiver when read. All other parts
of its signature, including its effect, are retained unchanged. -/
def Contract.withReceiver (receiver : Receiver') (s : Contract Receiver Args Result) :
    Contract Receiver' Args Result :=
  ⟨receiver, s.arguments, s.result, s.effect⟩

abbrev Arrow (α : Type) := Contract α (List α) α
abbrev RestArrow (α : Type) := Contract α (List α × α) α
abbrev MethodArrow (α : Type) := Contract Unit (List α) α
abbrev MethodRestArrow (α : Type) := Contract Unit (List α × α) α

def Arrow.map (f : α → β) (s : Arrow α) : Arrow β := Contract.map f (List.map f) f s
/-- Interpret fixed positions as value families and the rest as an argument
family, preserving the same effect. Ordinary renaming uses the same map for
both kinds of operand. -/
def RestArrow.mapWith (f : α → β) (g : α → γ) (s : RestArrow α) : Contract β (List β × γ) β :=
  Contract.map f (fun p => (p.1.map f, g p.2)) f s

def RestArrow.map (f : α → β) (s : RestArrow α) : RestArrow β := RestArrow.mapWith f f s

def MethodArrow.map (f : α → β) (s : MethodArrow α) : MethodArrow β :=
  Contract.map id (List.map f) f s

def MethodRestArrow.mapWith (f : α → β) (g : α → γ) (s : MethodRestArrow α) :
    Contract Unit (List β × γ) β :=
  Contract.map id (fun p => (p.1.map f, g p.2)) f s

def MethodRestArrow.map (f : α → β) (s : MethodRestArrow α) : MethodRestArrow β :=
  MethodRestArrow.mapWith f f s

/-- The body row of a rest signature keeps its effect and fixed parameters. -/
def RestArrow.fixed (s : RestArrow α) : Arrow α :=
  ⟨s.receiver, s.arguments.1, s.result, s.effect⟩

def Arrow.operands (s : Arrow α) : List α := s.receiver :: s.arguments ++ [s.result]
def RestArrow.operands (s : RestArrow α) : List α :=
  s.receiver :: s.arguments.1 ++ [s.arguments.2, s.result]
def MethodArrow.operands (s : MethodArrow α) : List α := s.arguments ++ [s.result]
def MethodRestArrow.operands (s : MethodRestArrow α) : List α :=
  s.arguments.1 ++ [s.arguments.2, s.result]

private theorem map_fixed {f : α → α} {xs : List α} (h : ∀ x ∈ xs, f x = x) :
    xs.map f = xs := by
  rw [List.map_congr_left (g := id) h, List.map_id]

theorem Arrow.map_of_operands {f : α → α} {s : Arrow α}
    (h : ∀ a ∈ s.operands, f a = a) : s.map f = s := by
  rcases s with ⟨r, args, result, effect⟩
  have hr := h r (by simp [operands])
  have hd := h result (by simp [operands])
  have ha := map_fixed (xs := args) (fun x hx => h x (by simp [operands, hx]))
  simp [map, Contract.map, hr, hd, ha]

theorem RestArrow.map_of_operands {f : α → α} {s : RestArrow α}
    (h : ∀ a ∈ s.operands, f a = a) : s.map f = s := by
  rcases s with ⟨r, ⟨args, rest⟩, result, effect⟩
  have hr := h r (by simp [operands])
  have hd := h result (by simp [operands])
  have he := h rest (by simp [operands])
  have ha := map_fixed (xs := args) (fun x hx => h x (by simp [operands, hx]))
  simp [map, mapWith, Contract.map, hr, hd, he, ha]

theorem MethodArrow.map_of_operands {f : α → α} {s : MethodArrow α}
    (h : ∀ a ∈ s.operands, f a = a) : s.map f = s := by
  rcases s with ⟨r, args, result, effect⟩
  have hd := h result (by simp [operands])
  have ha := map_fixed (xs := args) (fun x hx => h x (by simp [operands, hx]))
  simp [map, Contract.map, hd, ha]

theorem MethodRestArrow.map_of_operands {f : α → α} {s : MethodRestArrow α}
    (h : ∀ a ∈ s.operands, f a = a) : s.map f = s := by
  rcases s with ⟨r, ⟨args, rest⟩, result, effect⟩
  have hd := h result (by simp [operands])
  have he := h rest (by simp [operands])
  have ha := map_fixed (xs := args) (fun x hx => h x (by simp [operands, hx]))
  simp [map, mapWith, Contract.map, hd, he, ha]

/-- Deliberate forgetting, for ordinary call elimination. -/
def Arrow.plain (s : Arrow α) : α × List α × α := (s.receiver, s.arguments, s.result)

/-- How a signature stating `receiverOwn` may change its receiver's own
locations: a value arbitrarily, a store as its footprint's stores. -/
def Effect.ownChange (e : Effect) : Footprints.Closed := ⟨.any, e.footprint.store⟩

theorem Effect.le_ownChange (e : Effect) : e.footprint.le e.ownChange = true := by
  unfold Effect.ownChange
  generalize e.footprint = c
  rcases c with ⟨v, s⟩
  cases v <;> cases s <;> rfl

/-- The closed reading of a signature's frame with receiver `r`, its coarse
bound `footprint`: on every old location; or, with `receiverOwn`, on every
one but `r`'s own, which may change as `ownChange` allows; or, with
`receiverStore`, on every one but `r`'s store. The frame implies it
(`Effect.within_closed`), and it is the frame where the frame states no
store regions (`Effect.within_iff_closed`). -/
def Effect.withinClosed (e : Effect) (r : Tm) (before after : Heap) : Prop :=
  if e.receiverOwn then e.footprint.HoldsOn (fun l => l ∉ Footprints.ownOf r) before after ∧
    e.ownChange.HoldsOn (fun l => l ∈ Footprints.ownOf r) before after
  else if e.receiverStore then e.footprint.HoldsOn (fun l => Footprints.storeOf r ≠ some l) before after
  else e.footprint.Holds before after

/-- A change from `before` to `after` that alters no old location but the
receiver `r`'s store, which, where it changes, held a store and holds one
extending it, its old elements at their indices, at most `2^32 - 1` long:
`Array.prototype.push` on an ordinary array (SOURCE-CONTRACTS.md, "Native
footprints"). -/
def ReceiverGrows (r : Tm) (before after : Heap) : Prop :=
  ∀ l v, before[l]? = some v → after[l]? = some v ∨
    (Footprints.storeOf r = some l ∧ ∃ ls ls', v = .arr ls ∧ after[l]? = some (.arr ls') ∧
      ls <+: ls' ∧ ls'.length ≤ maxArrayLength)

/-- A change from `before` to `after` appending the actuals `args`, where each
is a value, to the receiver `r`'s store: the store it held holds one longer
by the actuals' number, whose element at the old length plus `j` is present
and holds the `j`-th actual at a location beyond the input heap: `Array.prototype.push` on an ordinary array
(SOURCE-CONTRACTS.md, "Native footprints"). -/
def ReceiverAppends (r : Tm) (args : List Tm) (before after : Heap) : Prop :=
  (∀ a ∈ args, isVal a = true) → ∀ s ls, Footprints.storeOf r = some s → before[s]? = some (.arr ls) →
    ∃ ls', after[s]? = some (.arr ls') ∧ ls'.length = ls.length + args.length ∧
      ∀ j a, args[j]? = some a → ∃ l, ls'[ls.length + j]? = some (some l) ∧ after[l]? = some a ∧ before.length ≤ l

/-- An append to a heap extending `before` is one to `before`. -/
theorem ReceiverAppends.prefix_left {r : Tm} {args : List Tm} {before middle after : Heap}
    (ha : ReceiverAppends r args middle after) (hprefix : before.IsPrefix middle) :
    ReceiverAppends r args before after := by
  intro hv s ls hs hls
  obtain ⟨t, rfl⟩ := hprefix
  have hmid : (before ++ t)[s]? = some (.arr ls) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hls).1, hls]
  obtain ⟨ls', hout, hlen, hel⟩ := ha hv s ls hs hmid
  refine ⟨ls', hout, hlen, fun j a hj => ?_⟩
  obtain ⟨l, hl, hv, hfresh⟩ := hel j a hj
  exact ⟨l, hl, hv, by simp only [List.length_append] at hfresh; omega⟩

/-- Actuals one of which is no value append nothing a call states. -/
theorem ReceiverAppends.of_not_values {r : Tm} {args : List Tm} {before after : Heap}
    (h : ∃ a ∈ args, isVal a = false) : ReceiverAppends r args before after := by
  intro hv
  obtain ⟨a, ha, hf⟩ := h
  rw [hv a ha] at hf
  cases hf

/-- A receiver holding no store has nothing appended. -/
theorem ReceiverAppends.of_no_store {r : Tm} {args : List Tm} {before after : Heap}
    (h : Footprints.storeOf r = none) : ReceiverAppends r args before after := by
  intro _ s ls hs
  rw [h] at hs
  cases hs

/-- A growth from a heap extending `before` is one from `before`. -/
theorem ReceiverGrows.prefix_left {r : Tm} {before middle after : Heap} (hg : ReceiverGrows r middle after)
    (hprefix : before.IsPrefix middle) : ReceiverGrows r before after := by
  intro l v hv
  apply hg l v
  obtain ⟨t, rfl⟩ := hprefix
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1, hv]

/-- The receiver's entries of a signature's frame: with `receiverOwn`, its
own locations holding a value at `any` (one holding a store stays at the
closed bound's stores, which `ownChange` gives it); else, with
`receiverStore`, its store's location at `any`. -/
def Effect.receiverEntries (e : Effect) : Footprints.Footprint :=
  if e.receiverOwn then [(.inCls (.own 0) .value, .any)]
  else if e.receiverStore then [(.field 0 arrayStoreKey, .any)] else []

/-- An argument store region's entry of a frame: the store location the
region selects at the call's entry, at `any`. -/
def regionEntry (r : Footprints.ArgumentStoreRegion) : Footprints.Region × Footprints.Change := r.entry

/-- **The frame** of a signature: its closed bound's two classes, its
receiver's entries and its argument store regions, read at the call's
positions (`callEnv`). It is the one statement of what a call may change. -/
def Effect.frame (e : Effect) : Footprints.Footprint :=
  e.closed.fp ++ e.receiverEntries ++ e.regions.map regionEntry

/-- What a signature's frame states of a call with receiver `r` and actuals
`args`: `Post` of the frame at the call's positions. -/
def Effect.within (e : Effect) (r : Tm) (args : List Tm) (before after : Heap) : Prop :=
  Footprints.Post e.frame (callEnv r args) before after

/-- A signature's normal-return postcondition for a call with receiver `r`,
from the heap the call starts in: its frame, and, where it states one, a
fresh store for the result; with `receiverGrows`, `ReceiverGrows` and
`ReceiverAppends` at the actuals; with `elementWrite`, its change. -/
def Effect.post (e : Effect) (r : Tm) (args : List Tm) : Heap → Post := fun before after v =>
  e.within r args before after ∧ (e.fresh = true → Footprints.FreshAt before.length v) ∧
    (e.freshObject = true → Footprints.FreshObjectAt before.length v) ∧
    (∀ R, e.elements = some R → v = .tru → ElemsAt R r after) ∧
    (∀ F ∈ e.ensures, F.HoldsAt (ensuresEnv v r args) after) ∧
    (e.receiverGrows = true → ReceiverGrows r before after ∧ ReceiverAppends r args before after) ∧
    (∀ w, e.elementWrite = some w → w.Holds args before after)

/-- A signature's postcondition on a throw, from the heap the call starts in:
its frame at the call's actuals where it states `onThrow`, and nothing
otherwise. -/
def Effect.excPost (e : Effect) (r : Tm) (args : List Tm) (before : Heap) : Heap → Prop := fun after =>
  e.onThrow = true → e.within r args before after

theorem Effect.withinClosed_of_holds {e : Effect} {r : Tm} {before after : Heap}
    (h : e.footprint.Holds before after) : e.withinClosed r before after := by
  unfold Effect.withinClosed
  split
  · exact ⟨h.on _, (h.on _).mono e.le_ownChange⟩
  · split
    · exact h.on _
    · exact h

/-- A signature stating `receiverOwn` changes every old location as its
`ownChange` allows. -/
theorem Effect.withinClosed_own {e : Effect} {r : Tm} {before after : Heap}
    (h : e.withinClosed r before after) (ho : e.receiverOwn = true) : e.ownChange.Holds before after := by
  simp only [Effect.withinClosed, ho, if_true] at h
  obtain ⟨hout, hin⟩ := h
  have hout := hout.mono e.le_ownChange
  refine Footprints.Closed.holds_of_on ⟨hout.1, fun l v _ hv => ?_⟩
  by_cases hm : l ∈ Footprints.ownOf r
  · exact hin.2 l v hm hv
  · exact hout.2 l v hm hv

/-- What a footprint on the locations below `b` follows from: the footprint
anywhere, or on every location but a store, or every own location of an
object, allocated after `b`. -/
theorem Effect.withinClosed_below {e : Effect} {r : Tm} {b : Nat} {before after : Heap}
    (h : e.withinClosed r before after) (hr : e.receiverStore = true → Footprints.FreshAt b r)
    (ho : e.receiverOwn = true → Footprints.FreshObjectAt b r) :
    e.footprint.HoldsOn (· < b) before after := by
  unfold Effect.withinClosed at h
  split at h
  · rename_i hs
    exact h.1.below_fresh_object (ho hs)
  · split at h
    · rename_i hs
      exact h.below_fresh (hr hs)
    · exact h.on _

theorem Effect.withinClosed_holds {e : Effect} {r : Tm} {before after : Heap}
    (h : e.withinClosed r before after) (hr : e.receiverStore = false) (ho : e.receiverOwn = false) :
    e.footprint.Holds before after := by
  simpa [Effect.withinClosed, hr, ho] using h

theorem Effect.withinClosed_top {e : Effect} {r : Tm} {before after : Heap}
    (h : e.withinClosed r before after) : Footprints.Closed.top.Holds before after := by
  unfold Effect.withinClosed at h
  split at h
  · exact h.1.top
  · split at h
    · exact h.top
    · exact Footprints.Closed.holds_top.mpr (Footprints.Closed.holds_iff.mp h).1

/-- A footprint's postcondition bounds the locations `P` admits by a closed
bound at least each covering entry's change. -/
theorem post_closedOn {Φ : Footprints.Footprint} {ρ : Env} {h h' : Heap} {c : Footprints.Closed}
    {P : Nat → Prop} (hp : Footprints.Post Φ ρ h h')
    (hΦ : ∀ e ∈ Φ, ∀ l v, P l → e.1.mem ρ h l = true → h[l]? = some v → e.2.le (c.at v) = true) :
    c.HoldsOn P h h' :=
  ⟨hp.1, fun l v hP hv => by
    obtain ⟨v', hv', ha⟩ := hp.2 l v hv
    refine ⟨v', hv', ?_⟩
    rcases ha with rfl | ⟨e, he, hm, hh⟩
    · exact Footprints.Change.Holds.refl _ _ _
    · exact hh.mono (hΦ e he l v hP hm hv)⟩

private theorem change_le_any (c : Footprints.Change) : c.le .any = true := by
  cases c <;> rfl

private theorem change_le_refl (c : Footprints.Change) : c.le c = true := by
  cases c <;> rfl

/-- An entry of the closed bound covers a location at most as its class's
change of the coarse bound allows. -/
private theorem closed_entry_le {e : Effect} {x : Footprints.Region × Footprints.Change}
    (hx : x ∈ e.closed.fp) {ρ : Env} {h : Heap} {l : Nat} {v : Val}
    (hm : x.1.mem ρ h l = true) (hv : h[l]? = some v) : x.2.le (e.footprint.at v) = true := by
  simp only [Footprints.Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at hx
  unfold Effect.footprint
  rcases hx with rfl | rfl <;>
    simp only [Footprints.Region.mem, hv, Footprints.Cls.has] at hm <;>
    split <;> simp_all [Footprints.Closed.at, Footprints.Closed.top, change_le_refl, change_le_any]

/-- A region entry covers its location at `any`, which the coarse bound
allows. -/
private theorem region_entry_le {e : Effect} {r : Footprints.ArgumentStoreRegion}
    (hr : r ∈ e.regions) {v : Val} : (regionEntry r).2.le (e.footprint.at v) = true := by
  have hne : e.regions.isEmpty = false := by
    cases hq : e.regions with
    | nil => rw [hq] at hr; cases hr
    | cons _ _ => rfl
  simp only [Effect.footprint, hne, Bool.false_eq_true, if_false, Footprints.Closed.at, Footprints.Closed.top]
  split <;> rfl

theorem Effect.mem_frame {e : Effect} {x : Footprints.Region × Footprints.Change} (hx : x ∈ e.frame) :
    x ∈ e.closed.fp ∨ x ∈ e.receiverEntries ∨ ∃ r ∈ e.regions, x = regionEntry r := by
  simp only [Effect.frame, List.mem_append, List.mem_map] at hx
  rcases hx with (hx | hx) | ⟨r, hr, rfl⟩
  · exact .inl hx
  · exact .inr (.inl hx)
  · exact .inr (.inr ⟨r, hr, rfl⟩)

/-- **The closed reading.** A signature's frame implies its closed reading
at the coarse bound `footprint`. -/
theorem Effect.within_closed {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) : e.withinClosed r before after := by
  have h0 : callEnv r args 0 = r := rfl
  have base : ∀ (P : Nat → Prop), (∀ x ∈ e.receiverEntries, ∀ l, P l → x.1.mem (callEnv r args) before l = false) →
      e.footprint.HoldsOn P before after := by
    intro P hrecv
    refine post_closedOn h fun x hx l v hP hm hv => ?_
    rcases Effect.mem_frame hx with hx | hx | ⟨q, hq, rfl⟩
    · exact closed_entry_le hx hm hv
    · rw [hrecv x hx l hP] at hm; cases hm
    · exact region_entry_le hq
  unfold Effect.withinClosed
  split
  · rename_i ho
    refine ⟨base _ fun x hx l hl => ?_, post_closedOn h fun x hx l v hP hm hv => ?_⟩
    · simp only [Effect.receiverEntries, ho, if_true, List.mem_singleton] at hx
      subst hx
      simp only [Footprints.Region.mem, h0, Bool.and_eq_false_iff]
      left
      simpa [List.contains_iff_mem, Footprints.ownOf] using hl
    · have hst : e.ownChange.at v = (if Footprints.isArr v then e.footprint.store else .any) := by
        simp [Effect.ownChange, Footprints.Closed.at]
      rcases Effect.mem_frame hx with hx | hx | ⟨q, hq, rfl⟩
      · have := closed_entry_le hx hm hv
        rw [hst]
        revert this
        simp only [Footprints.Closed.at]
        split <;> simp [change_le_any]
      · rw [hst]; split <;> simp only [Effect.receiverEntries, ho, if_true, List.mem_singleton] at hx <;>
          subst hx <;> simp_all [Footprints.Region.mem, Footprints.Cls.has, change_le_any]
      · have := region_entry_le (v := v) hq
        rw [hst]
        revert this
        simp only [Footprints.Closed.at]
        split <;> simp [change_le_any]
  · rename_i ho
    split
    · rename_i hs
      refine base _ fun x hx l hl => ?_
      simp only [Effect.receiverEntries, ho, hs, if_true, Bool.false_eq_true, if_false, List.mem_singleton] at hx
      subst hx
      simp only [Footprints.Region.mem, h0]
      simpa [Footprints.storeOf] using hl
    · rename_i hs
      apply Footprints.Closed.holds_of_on
      refine base _ fun x hx l _ => ?_
      simp [Effect.receiverEntries, ho, hs] at hx

/-- **The translation.** Without store regions, a signature's frame is its
closed reading: the closed bound, the receiver's own locations at
`ownChange` where it states `receiverOwn`, else its store excepted where it
states `receiverStore`. -/
theorem Effect.within_iff_closed {e : Effect} (hreg : e.regions = []) (r : Tm) (args : List Tm) (before after : Heap) :
    e.within r args before after ↔ e.withinClosed r before after := by
  have hfp : e.footprint = e.closed := Effect.footprint_of_regions hreg
  have h0 : callEnv r args 0 = r := rfl
  unfold Effect.within Effect.withinClosed Effect.frame Effect.receiverEntries
  simp only [hreg, List.map_nil, List.append_nil]
  rw [show e.closed = e.footprint from hfp.symm]
  by_cases ho : e.receiverOwn = true
  · simp only [ho, if_true]
    rw [Footprints.Closed.post_extra_any]
    have hmem : ∀ l, (Footprints.Region.inCls (.own 0) .value).mem (callEnv r args) before l =
        (((Footprints.ownOf r).contains l) && match before[l]? with
          | some v => Footprints.Cls.value.has v
          | none => false) := fun l => rfl
    constructor
    · intro hw
      refine ⟨hw.weaken fun l hl => ?_, hw.1, fun l v hown hv => ?_⟩
      · show (Footprints.Region.inCls (.own 0) .value).mem (callEnv r args) before l = false
        rw [hmem l]
        simp [hl]
      by_cases ha : Footprints.isArr v = true
      · have hl : (Footprints.Region.inCls (.own 0) .value).mem (callEnv r args) before l = false := by
          rw [hmem l, hv]; simp [Footprints.Cls.has, ha]
        obtain ⟨v', hv', hc⟩ := hw.2 l v hl hv
        refine ⟨v', hv', ?_⟩
        simpa [Footprints.Closed.at, ha, Effect.ownChange] using hc
      · have hl := (List.getElem?_eq_some_iff.mp hv).1
        have hla : l < after.length := Nat.lt_of_lt_of_le hl hw.1
        refine ⟨after[l], List.getElem?_eq_getElem hla, ?_⟩
        simp [Footprints.Closed.at, ha, Effect.ownChange, Footprints.Change.Holds]
    · rintro ⟨hout, hin⟩
      refine ⟨hout.1, fun l v hl hv => ?_⟩
      replace hl : (Footprints.Region.inCls (.own 0) .value).mem (callEnv r args) before l = false := hl
      rw [hmem l, hv] at hl
      by_cases hown : l ∈ Footprints.ownOf r
      · obtain ⟨v', hv', hc⟩ := hin.2 l v hown hv
        have ha : Footprints.isArr v = true := by
          simpa [List.contains_iff_mem, hown, Footprints.Cls.has] using hl
        refine ⟨v', hv', ?_⟩
        simpa [Footprints.Closed.at, ha, Effect.ownChange] using hc
      · exact hout.2 l v hown hv
  · simp only [ho, Bool.false_eq_true, if_false]
    by_cases hs : e.receiverStore = true
    · simp only [hs, if_true]
      rw [Footprints.Closed.post_extra_any]
      apply Footprints.Closed.HoldsOn.congr
      intro l
      simp [Footprints.Region.mem, h0, Footprints.storeOf]
    · simp only [hs, Bool.false_eq_true, if_false, List.append_nil]
      exact Footprints.Closed.post_iff.trans Footprints.Closed.holds_iff.symm

/-- A closed reading of a signature stating no store regions is its frame. -/
theorem Effect.within_of_closed {e : Effect} (hreg : e.regions = []) {r : Tm} {args : List Tm}
    {before after : Heap} (h : e.withinClosed r before after) : e.within r args before after :=
  (Effect.within_iff_closed hreg r args before after).mpr h

/-- A signature's frame holds where its closed bound holds everywhere. -/
theorem Effect.within_of_holds {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.closed.Holds before after) : e.within r args before after := by
  have hp : Footprints.Post e.closed.fp (callEnv r args) before after :=
    Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp h)
  exact ⟨hp.1, fun l v hv => by
    obtain ⟨v', hv', ha⟩ := hp.2 l v hv
    refine ⟨v', hv', ?_⟩
    rcases ha with h | ⟨x, hx, hm, hh⟩
    · exact .inl h
    · exact .inr ⟨x, List.mem_append_left _ (List.mem_append_left _ hx), hm, hh⟩⟩

/-- Without store regions the coarse bound is the closed bound. -/
theorem Effect.within_of_footprint {e : Effect} (hreg : e.regions = []) {r : Tm} {args : List Tm}
    {before after : Heap} (h : e.footprint.Holds before after) : e.within r args before after :=
  Effect.within_of_holds (by rw [← Effect.footprint_of_regions hreg]; exact h)

theorem Effect.within_own {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) (ho : e.receiverOwn = true) : e.ownChange.Holds before after :=
  Effect.withinClosed_own (Effect.within_closed h) ho

theorem Effect.within_below {e : Effect} {r : Tm} {args : List Tm} {b : Nat} {before after : Heap}
    (h : e.within r args before after) (hr : e.receiverStore = true → Footprints.FreshAt b r)
    (ho : e.receiverOwn = true → Footprints.FreshObjectAt b r) :
    e.footprint.HoldsOn (· < b) before after :=
  Effect.withinClosed_below (Effect.within_closed h) hr ho

theorem Effect.within_holds {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) (hr : e.receiverStore = false) (ho : e.receiverOwn = false) :
    e.footprint.Holds before after :=
  Effect.withinClosed_holds (Effect.within_closed h) hr ho

theorem Effect.within_top {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) : Footprints.Closed.top.Holds before after :=
  Effect.withinClosed_top (Effect.within_closed h)

/-- **Store regions.** A signature stating no receiver mode: its frame is
the closed bound on every location but the stores the regions select at the
call's entry (`ArgumentStoreRegionsWithin`), the store-exception predicate of
a statement's store regions. -/
theorem Effect.within_iff_regions {e : Effect} (hs : e.receiverStore = false) (ho : e.receiverOwn = false)
    (r : Tm) (args : List Tm) (before after : Heap) :
    e.within r args before after ↔
      Footprints.ArgumentStoreRegionsWithin e.closed e.regions (callEnv r args) before after := by
  have hrecv : e.receiverEntries = [] := by simp [Effect.receiverEntries, hs, ho]
  rw [Footprints.ArgumentStoreRegionsWithin.iff_post]
  unfold Effect.within Effect.frame
  rw [hrecv, List.append_nil]
  rfl

@[simp] theorem Effect.post_ofFootprint (c : Footprints.Closed) (r : Tm) (args : List Tm) (before after : Heap) (v : Val) :
    (Effect.ofFootprint c).post r args before after v ↔ c.Holds before after := by
  have hw : (Effect.ofFootprint c).within r args before after ↔ c.Holds before after := by
    unfold Effect.within Effect.frame Effect.receiverEntries
    simp only [Effect.ofFootprint, Bool.false_eq_true, if_false, List.map_nil, List.append_nil]
    exact Footprints.Closed.post_iff.trans Footprints.Closed.holds_iff.symm
  unfold Effect.post
  rw [hw]
  simp [Effect.ofFootprint]

/-- Whether the signature's result operand is the result's type and it
states no precondition: a signature an ordinary arrow can stand for once its
postcondition, an elements promise included, is forgotten. -/
def Effect.plain (e : Effect) : Bool := e.promise.isNone && e.requires.isNone && e.pre.isEmpty

/-- Whether a signature states no precondition and no elements promise, the
two parts of a guarantee about its receiver's elements. -/
def Effect.elementFree (e : Effect) : Bool :=
  e.requires.isNone && e.elements.isNone && e.pre.isEmpty && e.ensures.isEmpty

/-- The actual a promise is about: the one at its parameter, `undefined` where
the call passes none. A signature without a promise is about none. -/
def Effect.promised (e : Effect) (args : List Tm) : Tm :=
  match e.promise with
  | some p => args.getD p.param .undef
  | none => .undef

/-- What a promised result meets, given the result operand `T` and the
promised actual `a`. -/
def TypePromise.result : TypePromise → Fam → Tm → Fam
  | .guards _, T, a => fun k W u => (u = .tru ∧ T k W a) ∨ u = .fls
  | .asserts _, T, a => fun k W u => u = .undef ∧ T k W a

/-- What a call's result meets, given the signature's result operand `R` and
the promised actual `a`. -/
def Effect.result (e : Effect) (R : Fam) (a : Tm) : Fam :=
  match e.promise with
  | some p => p.result R a
  | none => R

theorem Effect.result_none {e : Effect} (h : e.promise = none) (R : Fam) (a : Tm) : e.result R a = R := by
  simp [Effect.result, h]

theorem Effect.result_plain {e : Effect} (h : e.plain = true) (R : Fam) (a : Tm) : e.result R a = R :=
  Effect.result_none (by simp only [Effect.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at h; exact h.1.1) R a

theorem Effect.plain_of {e : Effect} (hp : e.promise = none) (hr : e.requires = none) (hpre : e.pre = []) :
    e.plain = true := by
  simp [Effect.plain, hp, hr, hpre]

theorem Effect.plain_requires {e : Effect} (h : e.plain = true) : e.requires = none := by
  simp only [Effect.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at h; exact h.1.2

theorem Effect.plain_pre {e : Effect} (h : e.plain = true) : e.pre = [] := by
  simp only [Effect.plain, Bool.and_eq_true, List.isEmpty_iff] at h; exact h.2

theorem Effect.result_mono (e : Effect) {R T : Fam} {a : Tm} {k W u}
    (h : ∀ u, R k W u → T k W u) (hr : ∀ a', R k W a' → T k W a') :
    e.result R a k W u → e.result T a k W u := by
  unfold Effect.result
  match e.promise with
  | none => exact h u
  | some (.guards _) => exact fun hu => hu.imp (fun ⟨hu, ha⟩ => ⟨hu, hr a ha⟩) id
  | some (.asserts _) => exact fun ⟨hu, ha⟩ => ⟨hu, hr a ha⟩

/-- A promise's parameter, counted after `n` saved actuals: what a bound
signature promises of its own actuals. Defined where the promise is about one
of them. -/
def TypePromise.drop (n : Nat) : TypePromise → TypePromise
  | .guards p => .guards (p - n)
  | .asserts p => .asserts (p - n)

def Effect.drop (n : Nat) (e : Effect) : Effect :=
  ⟨if e.receiverStore || e.receiverOwn then .top else e.footprint, e.promise.map (TypePromise.drop n), e.fresh, false,
    e.onThrow, false, e.freshObject, e.requires, none, e.pre, [], false, e.elementWrite.map fun _ => .stores, []⟩

/-- Whether binding `n` actuals keeps the promise about an actual of the
bound call. A precondition or an elements promise is about the receiver the
binding saves, which the bound call does not pass: binding keeps neither. -/
def Effect.keeps (n : Nat) (e : Effect) : Bool :=
  e.elementFree && match e.promise with
  | some p => n ≤ p.param
  | none => true

theorem Effect.keeps_elementFree {e : Effect} {n : Nat} (h : e.keeps n = true) : e.elementFree = true := by
  simp only [Effect.keeps, Bool.and_eq_true] at h; exact h.1

theorem Effect.keeps_requires {e : Effect} {n : Nat} (h : e.keeps n = true) : e.requires = none := by
  have := Effect.keeps_elementFree h
  simp only [Effect.elementFree, Bool.and_eq_true, Option.isNone_iff_eq_none] at this; exact this.1.1.1

theorem Effect.keeps_pre {e : Effect} {n : Nat} (h : e.keeps n = true) : e.pre = [] := by
  have := Effect.keeps_elementFree h
  simp only [Effect.elementFree, Bool.and_eq_true, List.isEmpty_iff] at this; exact this.1.2

theorem Effect.promised_drop {e : Effect} {pre args : List Tm} (h : e.keeps pre.length = true) :
    (e.drop pre.length).promised args = e.promised (pre ++ args) := by
  rcases e with ⟨c, _ | (p | p), f, s, o, w, fo, rq, el⟩ <;>
    simp only [Effect.keeps, Effect.drop, Effect.promised, TypePromise.drop, TypePromise.param,
      Option.map, Bool.and_eq_true] at h ⊢
  all_goals
    have h' : pre.length ≤ p := of_decide_eq_true h.2
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h']

/-- Whether a promise is about one of the first `n` parameters, the ones code
of arity `n` binds. -/
def Effect.promiseBelow (n : Nat) (e : Effect) : Bool :=
  match e.promise with
  | some p => p.param < n
  | none => true

/-- Whether what a signature states of the call's values is about the
receiver and the first `n` parameters, the ones code of arity `n` binds: its
promise, and each position its precondition `pre` names. Code states no
postcondition: a fact over a parameter needs its entry value, which a
reassigned parameter no longer holds; and no append, which a native's
audited signature alone states. -/
def Effect.below (n : Nat) (e : Effect) : Bool :=
  e.promiseBelow n && e.pre.all (fun F => F.slots.all (· ≤ n)) && e.ensures.isEmpty && !e.receiverGrows &&
    e.elementWrite.isNone && e.regions.isEmpty

theorem Effect.below_promise {e : Effect} {n : Nat} (h : e.below n = true) : e.promiseBelow n = true := by
  simp only [Effect.below, Bool.and_eq_true] at h; exact h.1.1.1.1.1

theorem Effect.below_pre {e : Effect} {n : Nat} (h : e.below n = true) :
    ∀ F ∈ e.pre, ∀ s ∈ F.slots, s ≤ n := by
  simp only [Effect.below, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h; exact h.1.1.1.1.2

theorem Effect.below_ensures {e : Effect} {n : Nat} (h : e.below n = true) : e.ensures = [] := by
  simp only [Effect.below, Bool.and_eq_true, List.isEmpty_iff] at h; exact h.1.1.1.2

theorem Effect.below_grows {e : Effect} {n : Nat} (h : e.below n = true) : e.receiverGrows = false := by
  simp only [Effect.below, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.1.1.2

theorem Effect.below_write {e : Effect} {n : Nat} (h : e.below n = true) : e.elementWrite = none := by
  simp only [Effect.below, Bool.and_eq_true, Option.isNone_iff_eq_none] at h; exact h.1.2

theorem Effect.below_regions {e : Effect} {n : Nat} (h : e.below n = true) : e.regions = [] := by
  simp only [Effect.below, Bool.and_eq_true, List.isEmpty_iff] at h; exact h.2

/-- A frame stating no store regions reads the receiver alone. -/
theorem Effect.within_args {e : Effect} (hreg : e.regions = []) {r : Tm} {args args' : List Tm}
    {before after : Heap} (h : e.within r args before after) : e.within r args' before after :=
  Effect.within_of_closed hreg (Effect.within_closed h)

theorem Effect.excPost_args {e : Effect} (hreg : e.regions = []) {r : Tm} {args args' : List Tm}
    {before after : Heap} (h : e.excPost r args before after) : e.excPost r args' before after :=
  fun ho => Effect.within_args hreg (h ho)

/-- A signature stating no postcondition (`ensures`), no append and no store
regions has a `post` independent of the actuals. -/
theorem Effect.post_args {e : Effect} (he : e.ensures = []) (hg : e.receiverGrows = false)
    (hx : e.elementWrite = none) (hreg : e.regions = []) {r : Tm}
    {args args' : List Tm} {before after : Heap}
    {v : Val} (h : e.post r args before after v) : e.post r args' before after v :=
  ⟨Effect.within_args hreg h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun F hF => (by rw [he] at hF; cases hF),
    (fun h' => by rw [hg] at h'; cases h'), fun w hw => (by rw [hx] at hw; cases hw)⟩

private theorem parameters_getD : ∀ (n : Nat) (args : List Tm) (p : Nat), p < n →
    (CallArguments.parameters n args).getD p .undef = args.getD p .undef
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], 0, _ => rfl
  | n + 1, [], p + 1, h => by
    simpa [CallArguments.parameters] using parameters_getD n [] p (by omega)
  | n + 1, _ :: _, 0, _ => rfl
  | n + 1, _ :: args, p + 1, h => by
    simpa [CallArguments.parameters] using parameters_getD n args p (by omega)

theorem Effect.parameters_length : ∀ (n : Nat) (args : List Tm), (CallArguments.parameters n args).length = n
  | 0, _ => rfl
  | n + 1, [] => by simp [CallArguments.parameters, parameters_length n []]
  | n + 1, _ :: args => by simp [CallArguments.parameters, parameters_length n args]

/-- Code binding `n` parameters holds a promised actual among them. -/
theorem Effect.promised_frame {e : Effect} {n : Nat} (h : e.below n = true) (args vs : List Tm) :
    e.promised (CallArguments.parameters n args ++ vs) = e.promised args := by
  unfold Effect.promised
  have h := Effect.below_promise h
  unfold Effect.promiseBelow at h
  split
  · rename_i p hp
    rw [hp] at h
    simp only [decide_eq_true_eq] at h
    rw [← parameters_getD n args p.param h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [Effect.parameters_length]; exact h)]
  · rfl

/-- Actuals past those code binds do not change what it promises about. -/
theorem Effect.promised_take {e : Effect} {n m : Nat} (h : e.below n = true) (hm : n ≤ m) (args : List Tm) :
    e.promised (args.take m) = e.promised args := by
  unfold Effect.promised
  have h := Effect.below_promise h
  unfold Effect.promiseBelow at h
  split
  · rename_i p hp
    rw [hp] at h
    simp only [decide_eq_true_eq] at h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [if_pos (by omega)]
  · rfl

/-- Code binding `n` parameters reads the precondition's positions in its
frame as the call passed them: the receiver, then each actual it binds. -/
theorem Effect.pre_frame {e : Effect} {n : Nat} (h : e.below n = true) {F : HeapKnowledge.IndexFact}
    (hF : F ∈ e.pre) (r : Tm) (args vs : List Tm) (d : Tm) (heap : Heap) :
    F.HoldsAt (callEnv r args) heap ↔ F.HoldsAt (envOf (r :: CallArguments.parameters n args ++ vs) d) heap := by
  refine HeapKnowledge.IndexFact.holdsAt_congr fun s hs => ?_
  have hle := Effect.below_pre h F hF s hs
  simp only [callEnv, envOf]
  cases s with
  | zero => simp
  | succ i =>
    have hp : (CallArguments.parameters n args).getD i .undef = args.getD i .undef :=
      parameters_getD n args i (by omega)
    have hlen : i < (CallArguments.parameters n args).length := by rw [Effect.parameters_length]; omega
    obtain ⟨x, hx⟩ : ∃ x, (CallArguments.parameters n args)[i]? = some x :=
      ⟨_, List.getElem?_eq_getElem hlen⟩
    simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some] at hp
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
      List.cons_append, List.getElem?_cons_succ, List.getElem?_append_left hlen, hx, Option.getD_some, hp]

/-- Actuals past those code binds do not change what its precondition reads. -/
theorem Effect.pre_take {e : Effect} {n m : Nat} (h : e.below n = true) (hm : n ≤ m) {F : HeapKnowledge.IndexFact}
    (hF : F ∈ e.pre) (r : Tm) (args : List Tm) (heap : Heap) :
    F.HoldsAt (callEnv r (args.take m)) heap ↔ F.HoldsAt (callEnv r args) heap := by
  refine HeapKnowledge.IndexFact.holdsAt_congr fun s hs => ?_
  have hle := Effect.below_pre h F hF s hs
  simp only [callEnv]
  cases s with
  | zero => simp
  | succ i =>
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [if_pos (by omega)]

/-- **What a module function's code realizes at arity `n`**: its effect
below `n` (`below`) but for its postcondition, each fact of which names the
result (position `0`), the receiver (`1`) and the first `n` parameters only.
A unit request states its postcondition at its entry frame
(`PassUnit.EnsuresClause`), so a reassigned parameter does not change what
it reads. -/
def Effect.belowRow (n : Nat) (e : Effect) : Bool :=
  ({ e with ensures := [] } : Effect).below n && e.ensures.all (fun F => F.slots.all (· ≤ n + 1))

theorem Effect.belowRow_below {e : Effect} {n : Nat} (h : e.belowRow n = true) :
    ({ e with ensures := [] } : Effect).below n = true := by
  simp only [Effect.belowRow, Bool.and_eq_true] at h; exact h.1

theorem Effect.belowRow_ensures {e : Effect} {n : Nat} (h : e.belowRow n = true) :
    ∀ F ∈ e.ensures, ∀ s ∈ F.slots, s ≤ n + 1 := by
  simp only [Effect.belowRow, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h; exact h.2

/-- An effect below `n` is one a module function's code realizes. -/
theorem Effect.belowRow_of_below {e : Effect} {n : Nat} (h : e.below n = true) : e.belowRow n = true := by
  have he := Effect.below_ensures h
  have h' : ({ e with ensures := [] } : Effect) = e := by cases e; simp_all
  simp [Effect.belowRow, h', h, he]

/-- Actuals past those code binds do not change what its postcondition
reads. -/
theorem Effect.ensures_take {e : Effect} {n m : Nat} (h : e.belowRow n = true) (hm : n ≤ m)
    {F : HeapKnowledge.IndexFact} (hF : F ∈ e.ensures) (v r : Tm) (args : List Tm) (heap : Heap) :
    F.HoldsAt (ensuresEnv v r (args.take m)) heap ↔ F.HoldsAt (ensuresEnv v r args) heap := by
  refine HeapKnowledge.IndexFact.holdsAt_congr fun s hs => ?_
  have hle := Effect.belowRow_ensures h F hF s hs
  simp only [ensuresEnv, callEnv]
  rcases s with _ | _ | i
  · simp
  · simp
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [if_pos (by omega)]

/-- Code binding `n` parameters reads its postcondition's positions in its
entry frame, the result pushed, as the call passed them. -/
theorem Effect.ensures_frame {e : Effect} {n : Nat} (h : e.belowRow n = true) {F : HeapKnowledge.IndexFact}
    (hF : F ∈ e.ensures) (v r : Tm) (args vs : List Tm) (d : Tm) (heap : Heap) :
    F.HoldsAt (ensuresEnv v r args) heap ↔
      F.HoldsAt (push v (envOf (r :: CallArguments.parameters n args ++ vs) d)) heap := by
  refine HeapKnowledge.IndexFact.holdsAt_congr fun s hs => ?_
  have hle := Effect.belowRow_ensures h F hF s hs
  rcases s with _ | _ | i
  · rfl
  · simp [ensuresEnv, callEnv, push, envOf]
  · have hp : (CallArguments.parameters n args).getD i .undef = args.getD i .undef :=
      parameters_getD n args i (by omega)
    have hlen : i < (CallArguments.parameters n args).length := by rw [Effect.parameters_length]; omega
    obtain ⟨x, hx⟩ : ∃ x, (CallArguments.parameters n args)[i]? = some x :=
      ⟨_, List.getElem?_eq_getElem hlen⟩
    simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some] at hp
    simp only [ensuresEnv, callEnv, push, envOf, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
      List.getD_eq_getElem?_getD, List.cons_append, List.getElem?_cons_succ, List.getElem?_append_left hlen, hx,
      Option.getD_some, hp]

/-- **A module row's post at a prefix of the actuals is its post at all of
them** (proved), the prefix at least `n` long. -/
theorem Effect.post_take_row {e : Effect} {n m : Nat} (h : e.belowRow n = true) (hm : n ≤ m) {r : Tm}
    {args : List Tm} {before after : Heap} {v : Tm}
    (hp : e.post r (args.take m) before after v) : e.post r args before after v := by
  have hb := Effect.belowRow_below h
  have hreg : e.regions = [] := Effect.below_regions (e := { e with ensures := [] }) hb
  have hg : e.receiverGrows = false := Effect.below_grows (e := { e with ensures := [] }) hb
  have hx : e.elementWrite = none := Effect.below_write (e := { e with ensures := [] }) hb
  exact ⟨Effect.within_args hreg hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
    fun F hF => (Effect.ensures_take h hm hF v r args after).mp (hp.2.2.2.2.1 F hF),
    (fun h' => by rw [hg] at h'; cases h'), fun w hw => (by rw [hx] at hw; cases hw)⟩

theorem Effect.result_drop (e : Effect) (n : Nat) (R : Fam) (a : Tm) :
    (e.drop n).result R a = e.result R a := by
  rcases e with ⟨c, _ | (_ | _), f, s, o, w, fo, rq, el⟩ <;> rfl

/-- A bound call forwards to its target with the receiver it saved: the
target's postcondition at that receiver is the bound signature's at any. -/
theorem Effect.within_drop {e : Effect} (n : Nat) {rv r : Tm} {argsv args : List Tm} {before after : Heap}
    (h : e.within rv argsv before after) : (e.drop n).within r args before after := by
  apply Effect.within_of_holds
  unfold Effect.drop
  by_cases hs : (e.receiverStore || e.receiverOwn) = true
  · simp only [hs, if_true]
    exact Effect.within_top h
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hs
    simp only [hs.1, hs.2, Bool.or_self, Bool.false_eq_true, if_false]
    exact Effect.within_holds h hs.1 hs.2

theorem Effect.post_drop {e : Effect} (n : Nat) {rv r : Tm} {argsv args : List Tm} {before after : Heap} {v : Val}
    (h : e.post rv argsv before after v) : (e.drop n).post r args before after v :=
  ⟨Effect.within_drop n h.1, h.2.1, h.2.2.1, fun _ hR => by simp [Effect.drop] at hR,
    fun _ hF => (by simp [Effect.drop] at hF), fun hg => (by simp [Effect.drop] at hg), fun w hw => (by
      simp only [Effect.drop, Option.map_eq_some_iff] at hw
      obtain ⟨w0, h0, rfl⟩ := hw
      exact ElementWrite.Holds.stores (h.2.2.2.2.2.2 w0 h0))⟩

theorem Effect.excPost_drop {e : Effect} (n : Nat) {rv r : Tm} {argsv args : List Tm} {before after : Heap}
    (h : e.excPost rv argsv before after) : (e.drop n).excPost r args before after :=
  fun ho => Effect.within_drop n (h ho)

/-- A signature without its postcondition: what a call whose actuals are not
its positions' values (a variadic call) concludes. -/
def Effect.forgetEnsures (e : Effect) : Effect :=
  { e with ensures := [], elementWrite := (e.elementWrite.map fun _ => .stores), closed := e.footprint, regions := [] }


theorem Effect.forgetEnsures_write {e : Effect} {args args' : List Tm} {before after : Heap}
    (h : ∀ w, e.elementWrite = some w → w.Holds args before after) :
    ∀ w, e.forgetEnsures.elementWrite = some w → w.Holds args' before after := by
  intro w hw
  simp only [Effect.forgetEnsures, Option.map_eq_some_iff] at hw
  obtain ⟨w0, h0, rfl⟩ := hw
  exact ElementWrite.Holds.stores (h w0 h0)

/-- Forgetting a signature's store regions keeps its coarse bound, at any
actuals. -/
theorem Effect.within_forgetEnsures {e : Effect} {r : Tm} {args args' : List Tm} {before after : Heap}
    (h : e.within r args before after) : e.forgetEnsures.within r args' before after :=
  Effect.within_of_closed (e := e.forgetEnsures) rfl (by have hc := Effect.within_closed h; exact hc)

theorem Effect.post_forgetEnsures {e : Effect} {r : Tm} {args : List Tm} {before after : Heap} {v : Val}
    (h : e.post r args before after v) : e.forgetEnsures.post r args before after v :=
  ⟨Effect.within_forgetEnsures h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun F hF => (by simp [Effect.forgetEnsures] at hF),
    h.2.2.2.2.2.1, Effect.forgetEnsures_write h.2.2.2.2.2.2⟩

/-- A variadic call with a spread among its actuals concludes the signature's
postcondition without its postcondition facts at those actuals: an append
states nothing of actuals one of which is no value. -/
theorem Effect.post_forgetEnsures_spread {e : Effect} {r : Tm} {args args' : List Tm} {before after : Heap}
    {v : Val} (hs : ∃ a ∈ args', isVal a = false)
    (h : e.post r args before after v) : e.forgetEnsures.post r args' before after v :=
  ⟨Effect.within_forgetEnsures h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun F hF => (by simp [Effect.forgetEnsures] at hF),
    fun hg => ⟨(h.2.2.2.2.2.1 hg).1, ReceiverAppends.of_not_values hs⟩, Effect.forgetEnsures_write h.2.2.2.2.2.2⟩

/-- A postcondition at actuals padded with `undefined` is the one at the
actuals, of a receiver holding no store. -/
theorem Effect.post_pad {e : Effect} {r : Tm} (hr : Footprints.storeOf r = none) {args pad : List Tm}
    (hpad : ∀ a ∈ pad, a = .undef)
    {before after : Heap} {v : Val} (h : e.post r (args ++ pad) before after v) : e.post r args before after v := by
  have hwr : ∀ w, e.elementWrite = some w → w.Holds args before after := by
    intro w hw
    obtain ⟨hc, hx⟩ := h.2.2.2.2.2.2 w hw
    refine ⟨hc, fun he => ?_⟩
    have hg : ∀ i, (args ++ pad).getD i .undef = args.getD i .undef := fun i => by
      simpa [callEnv] using congrFun (callEnv_pad r args hpad) (i + 1)
    have := hx he
    simp only [ExactWrite, hg] at this ⊢
    exact this
  have hw := h.1
  unfold Effect.within at hw
  rw [callEnv_pad r args hpad] at hw
  refine ⟨hw, h.2.1, h.2.2.1, h.2.2.2.1, fun F hF => ?_,
    fun hg => ⟨(h.2.2.2.2.2.1 hg).1, ReceiverAppends.of_no_store hr⟩, hwr⟩
  have := h.2.2.2.2.1 F hF
  have he : ensuresEnv v r (args ++ pad) = ensuresEnv v r args := by
    funext i; simp only [ensuresEnv, callEnv_pad r args hpad]
  rwa [he] at this

/-- A throw's postcondition at actuals padded with `undefined` is the one at
the actuals. -/
theorem Effect.excPost_pad {e : Effect} {r : Tm} {args pad : List Tm} (hpad : ∀ a ∈ pad, a = .undef)
    {before after : Heap} (h : e.excPost r (args ++ pad) before after) : e.excPost r args before after := by
  intro ho
  have hw := h ho
  unfold Effect.within at hw ⊢
  rwa [callEnv_pad r args hpad] at hw

/-- A footprint's postcondition from a heap extending `before` by
allocation is one from `before` where each entry covers, read at `before`,
every old location it covers read at the later heap. -/
theorem post_prefix_of_mem {Φ : Footprints.Footprint} {ρ : Env} {before middle after : Heap}
    (hprefix : before.IsPrefix middle) (hp : Footprints.Post Φ ρ middle after)
    (hm : ∀ x ∈ Φ, ∀ l, l < before.length → x.1.mem ρ middle l = true → x.1.mem ρ before l = true) :
    Footprints.Post Φ ρ before after := by
  refine ⟨Nat.le_trans hprefix.length_le hp.1, fun l v hv => ?_⟩
  have hl := (List.getElem?_eq_some_iff.mp hv).1
  have hv' : middle[l]? = some v := by
    obtain ⟨t, rfl⟩ := hprefix
    rw [List.getElem?_append_left hl, hv]
  obtain ⟨v', hv'', ha⟩ := hp.2 l v hv'
  refine ⟨v', hv'', ?_⟩
  rcases ha with h | ⟨x, hx, hxm, hh⟩
  · exact .inl h
  · exact .inr ⟨x, hx, hm x hx l hl hxm, hh.lower hprefix.length_le⟩

/-- **Agreement across allocation.** Each store region's path reads, at the
heap before an allocation, what it reads after it: the checked transport a
frame reading nonempty paths needs to lift across allocation (an actual may
be a fresh object holding an old array). Empty paths agree always. -/
def Effect.PrefixAgrees (e : Effect) (ρ : Env) (before middle : Heap) : Prop :=
  ∀ q ∈ e.regions, ∀ v, HeapKnowledge.readPath middle (ρ q.position) q.path = some v →
    HeapKnowledge.readPath before (ρ q.position) q.path = some v

theorem Effect.prefixAgrees_of_nil {e : Effect} (h : e.regions.all (·.path.isEmpty) = true) (ρ : Env)
    (before middle : Heap) : e.PrefixAgrees ρ before middle := by
  intro q hq v hv
  have hp := List.isEmpty_iff.mp (List.all_eq_true.mp h q hq)
  rw [hp] at hv ⊢
  exact hv

theorem Effect.prefixAgrees_of_regions {e : Effect} (h : e.regions = []) (ρ : Env)
    (before middle : Heap) : e.PrefixAgrees ρ before middle :=
  Effect.prefixAgrees_of_nil (by simp [h]) ρ before middle

/-- Allocation before a call composes with its frame where the frame's paths
agree across it (`PrefixAgrees`). -/
theorem Effect.within_prefix {e : Effect} {r : Tm} {args : List Tm} {before middle after : Heap}
    (hprefix : before.IsPrefix middle) (hagree : e.PrefixAgrees (callEnv r args) before middle)
    (hw : e.within r args middle after) : e.within r args before after := by
  apply post_prefix_of_mem hprefix hw
  intro x hx l hl hm
  have hgl : middle[l]? = before[l]? := by
    obtain ⟨t, rfl⟩ := hprefix
    exact List.getElem?_append_left hl
  rcases Effect.mem_frame hx with hx | hx | ⟨q, hq, rfl⟩
  · simp only [Footprints.Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simpa only [Footprints.Region.mem, hgl] using hm
  · unfold Effect.receiverEntries at hx
    split at hx
    · simp only [List.mem_singleton] at hx
      subst hx
      simpa only [Footprints.Region.mem, hgl] using hm
    · split at hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact hm
      · cases hx
  · simp only [regionEntry, Footprints.ArgumentStoreRegion.entry, Footprints.Region.mem] at hm ⊢
    split at hm
    · rename_i w hw'
      rw [hagree q hq w hw']
      exact hm
    · cases hm

/-- Fresh entry allocation composes with the body's frame, where the frame's
paths agree across it. -/
theorem Effect.post_prefix (effect : Effect) {r : Tm} {args : List Tm} {before middle after : Heap} {v : Val}
    (hprefix : before.IsPrefix middle) (hagree : effect.PrefixAgrees (callEnv r args) before middle) :
    effect.post r args middle after v → effect.post r args before after v := by
  rintro ⟨hw, hf, ho, hel, hen, hg, hew⟩
  exact ⟨Effect.within_prefix hprefix hagree hw, fun h => (hf h).lower hprefix.length_le,
    fun h => (ho h).lower hprefix.length_le, hel, hen,
    fun h => ⟨(hg h).1.prefix_left hprefix, (hg h).2.prefix_left hprefix⟩, fun w h => (hew w h).prefix_left hprefix⟩

/-- Fresh entry allocation composes with the frame on a throw too, where the
frame's paths agree across it. -/
theorem Effect.excPost_prefix (effect : Effect) {r : Tm} {args : List Tm} {before middle after : Heap}
    (hprefix : before.IsPrefix middle) (hagree : effect.PrefixAgrees (callEnv r args) before middle) :
    effect.excPost r args middle after → effect.excPost r args before after :=
  fun hw ho => Effect.within_prefix hprefix hagree (hw ho)

/-- Conjoining two guarantees for the same call retains both: the meet of
their closed bounds, with the promise, receiver mode and store regions they
share, a fresh result where either states one. -/
def Effect.meet (a b : Effect) : Effect :=
  ⟨a.closed.meet b.closed, a.promise, a.fresh || b.fresh, a.receiverStore, a.onThrow && b.onThrow,
    a.receiverOwn, a.freshObject || b.freshObject, a.requires, a.elements, a.pre, a.ensures ++ b.ensures,
    a.receiverGrows || b.receiverGrows, a.elementWrite, a.regions⟩

/-- Two guarantees whose results mean the same: the same promise, or none,
the same precondition and elements promise, frames over the same locations
(the same receiver mode and store regions, and no receiver mode beside
store regions), and the same element write. Only these combine. -/
def Effect.sameResult (a b : Effect) : Bool :=
  (a.promise == b.promise && a.receiverStore == b.receiverStore && a.receiverOwn == b.receiverOwn &&
    a.requires == b.requires && a.elements == b.elements && a.pre == b.pre) && a.elementWrite == b.elementWrite &&
    (a.regions == b.regions && (a.regions.isEmpty || (!a.receiverStore && !a.receiverOwn)))

private theorem change_min_any : Footprints.Change.min .any .any = .any := rfl

theorem Effect.footprint_meet {a b : Effect} (hr : b.regions = a.regions) :
    (a.meet b).footprint = a.footprint.meet b.footprint := by
  unfold Effect.footprint Effect.meet
  simp only [hr]
  split <;> simp [Footprints.Closed.meet, Footprints.Closed.top, change_min_any]

private theorem Effect.withinClosed_meet {a b : Effect} (hfp : (a.meet b).footprint = a.footprint.meet b.footprint)
    (hs : b.receiverStore = a.receiverStore) (ho : b.receiverOwn = a.receiverOwn) {r : Tm} {before after : Heap} :
    (a.meet b).withinClosed r before after ↔ a.withinClosed r before after ∧ b.withinClosed r before after := by
  have hown : (a.meet b).ownChange = a.ownChange.meet b.ownChange := by
    simp only [Effect.ownChange, hfp, Footprints.Closed.meet, change_min_any]
  unfold Effect.withinClosed
  rw [hfp, hown, hs, ho]
  show (if a.receiverOwn = true then _ else _) ↔ _
  split
  · rw [Footprints.Closed.holdsOn_meet, Footprints.Closed.holdsOn_meet]
    exact ⟨fun ⟨⟨a1, b1⟩, a2, b2⟩ => ⟨⟨a1, a2⟩, b1, b2⟩, fun ⟨⟨a1, a2⟩, b1, b2⟩ => ⟨⟨a1, b1⟩, a2, b2⟩⟩
  · show (if a.receiverStore = true then _ else _) ↔ _
    split
    · exact Footprints.Closed.holdsOn_meet
    · exact Footprints.Closed.holds_meet

theorem Effect.within_meet {a b : Effect} (hs : a.sameResult b = true) {r : Tm} {args : List Tm} {before after : Heap} :
    (a.meet b).within r args before after ↔ a.within r args before after ∧ b.within r args before after := by
  simp only [Effect.sameResult, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.isEmpty_iff,
    Bool.not_eq_true'] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hst⟩, how⟩, _⟩, _⟩, _⟩, _⟩, hreg, hmode⟩ := hs
  have hfp := Effect.footprint_meet (a := a) (b := b) hreg.symm
  have hmr : (a.meet b).regions = a.regions := rfl
  rcases hmode with hnil | ⟨hs0, ho0⟩
  · rw [Effect.within_iff_closed (by rw [hmr, hnil]), Effect.within_iff_closed hnil,
      Effect.within_iff_closed (by rw [← hreg, hnil])]
    exact Effect.withinClosed_meet hfp hst.symm how.symm
  · have hbs : b.receiverStore = false := by rw [← hst]; exact hs0
    have hbo : b.receiverOwn = false := by rw [← how]; exact ho0
    rw [Effect.within_iff_regions (e := a.meet b) hs0 ho0, Effect.within_iff_regions hs0 ho0,
      Effect.within_iff_regions hbs hbo, hmr]
    unfold Footprints.ArgumentStoreRegionsWithin
    rw [show (a.meet b).closed = a.closed.meet b.closed from rfl, Footprints.Closed.holdsOn_meet, hreg]

theorem Effect.post_meet {a b : Effect} (hs : a.sameResult b = true) (r : Tm) (args : List Tm) (before after : Heap)
    (value : Val) :
    (a.meet b).post r args before after value ↔ a.post r args before after value ∧ b.post r args before after value := by
  have hw := Effect.within_meet hs (r := r) (args := args) (before := before) (after := after)
  have hf : (a.meet b).fresh = (a.fresh || b.fresh) := rfl
  have ho : (a.meet b).freshObject = (a.freshObject || b.freshObject) := rfl
  have he : (a.meet b).elements = a.elements := rfl
  have hen : (a.meet b).ensures = a.ensures ++ b.ensures := rfl
  have hg : (a.meet b).receiverGrows = (a.receiverGrows || b.receiverGrows) := rfl
  have hbe : b.elements = a.elements := by
    simp only [Effect.sameResult, Bool.and_eq_true, beq_iff_eq] at hs; exact hs.1.1.1.2.symm
  have hew : (a.meet b).elementWrite = a.elementWrite := rfl
  have hbw : b.elementWrite = a.elementWrite := by
    simp only [Effect.sameResult, Bool.and_eq_true, beq_iff_eq] at hs; exact hs.1.2.symm
  unfold Effect.post
  rw [hw, hf, ho, he, hen, hbe, hg, hew, hbw, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨⟨ha, hb⟩, hf, ho, hel, hens, hgr, hwr⟩
    exact ⟨⟨ha, fun h => hf (.inl h), fun h => ho (.inl h), hel, fun F hF => hens F (List.mem_append_left _ hF),
        fun h => hgr (.inl h), hwr⟩,
      ⟨hb, fun h => hf (.inr h), fun h => ho (.inr h), hel, fun F hF => hens F (List.mem_append_right _ hF),
        fun h => hgr (.inr h), hwr⟩⟩
  · rintro ⟨⟨ha, hfa, hoa, hel, hena, hga, hwa⟩, ⟨hb, hfb, hob, -, henb, hgb, -⟩⟩
    exact ⟨⟨ha, hb⟩, fun h => h.elim hfa hfb, fun h => h.elim hoa hob, hel,
      fun F hF => (List.mem_append.mp hF).elim (hena F) (henb F), fun h => h.elim hga hgb, hwa⟩

/-- Both guarantees' throw postconditions give the meet's: it states
`onThrow` only where both do. -/
theorem Effect.excPost_meet {a b : Effect} (hs : a.sameResult b = true) (r : Tm) (args : List Tm) (before after : Heap)
    (ha : a.excPost r args before after) (hb : b.excPost r args before after) : (a.meet b).excPost r args before after := by
  intro ho
  have ho' : a.onThrow = true ∧ b.onThrow = true := by simpa [Effect.meet] using ho
  exact (Effect.within_meet hs).mpr ⟨ha ho'.1, hb ho'.2⟩

theorem Effect.meet_same {a b : Effect} (hs : a.sameResult b = true) :
    (a.meet b).result = a.result ∧ (a.meet b).promised = a.promised ∧
      b.result = a.result ∧ b.promised = a.promised := by
  simp only [Effect.sameResult, Bool.and_eq_true, beq_iff_eq] at hs
  replace hs := hs.1.1.1.1.1
  refine ⟨rfl, rfl, ?_, ?_⟩
  · funext R x; simp [Effect.result, hs]
  · funext args; simp [Effect.promised, hs]

/-- The arrow equation, with a heap postcondition relative to this call's
entry heap. The input and result contracts are exactly those of `Promise`.
The effect is per signature: one overload may preserve its input heap while
another overload of the same value does not. -/
def PromiseWith (Ξ : Fam) (effect : Effect)
    (Acc : (j : Nat) → WorldT j → List Tm → Prop) (Rc R : Fam)
    (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
    WorldAdm U → ∀ (heap : Heap), HeapOk j U heap → ∀ r, isVal r = true → Rc j U r →
      ∀ args, CallArguments.Values args → Acc j U args → effect.Requires r args heap →
        ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧
          SafePostExc Ξ (effect.result R (effect.promised args)) (effect.post r args heap)
            (effect.excPost r args heap) j U heap result

/-- A heap effect's signature is an ordinary arrow once its postcondition is
forgotten. A promise's is not: its result operand is not the result's type;
nor is a precondition's, which an ordinary call does not establish. -/
theorem PromiseWith.erase {effect Acc Rc R k W v} (hp : effect.plain = true)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : Promise Ξ Acc Rc R k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  obtain ⟨result, hi, hs⟩ := h j hj U hx hu heap hh r hrv hr args hv ha
    (Effect.requires_none (Effect.plain_requires hp) (Effect.plain_pre hp) r args heap)
  rw [Effect.result_plain hp] at hs
  exact ⟨result, hi, HeapObservations.erase hs.post⟩

theorem PromiseWith.down {effect Acc Rc R n W v}
    (h : PromiseWith Ξ effect Acc Rc R (n + 1) W v) :
    PromiseWith Ξ effect Acc Rc R n (trunc n (Nat.le_succ n) W) v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha hq
  exact h j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh r hrv hr args hv ha hq

theorem PromiseWith.mono {effect Acc Rc R n W W' v} (hx : WExt W W')
    (h : PromiseWith Ξ effect Acc Rc R n W v) : PromiseWith Ξ effect Acc Rc R n W' v := by
  intro j hj U hy hu heap hh r hrv hr args hv ha hq
  exact h j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh r hrv hr args hv ha hq

/-- Effect coverage is implication of the normal-return postcondition and of
what the result meets, at every result operand. There is deliberately no rule
relating a promise to a signature without one, whose result operands mean
different things. -/
def Effect.Covers (source target : Effect) : Prop :=
  (∀ r args before after value, source.post r args before after value → target.post r args before after value) ∧
  (∀ R args k W u, source.result R (source.promised args) k W u → target.result R (target.promised args) k W u) ∧
  (∀ r args before after, source.excPost r args before after → target.excPost r args before after) ∧
  ∀ r args heap, target.Requires r args heap → source.Requires r args heap

/-- A precondition implying another's: none, or a predicate at most the
other's. -/
def requiresCovers : Option ElemPred → Option ElemPred → Bool
  | none, _ => true
  | some a, some b => b.le a
  | some _, none => false

/-- An elements promise implying another's: the other states none, or a
predicate at least this one's. -/
def elementsCovers : Option ElemPred → Option ElemPred → Bool
  | _, none => true
  | some a, some b => a.le b
  | none, some _ => false

/-- A precondition on the call's values implying another's: each fact of the
other's is one of this one's. -/
def preCovers (a b : List HeapKnowledge.IndexFact) : Bool := a.all b.contains

/-- A postcondition implying another: each of the other's facts is one of its facts. -/
def ensuresCovers (a b : List HeapKnowledge.IndexFact) : Bool := b.all a.contains

theorem requiresCovers_sound {a b : Effect} (h : requiresCovers a.requires b.requires = true)
    (hp : preCovers a.pre b.pre = true) {r args heap}
    (hb : b.Requires r args heap) : a.Requires r args heap := by
  refine ⟨fun R hR => ?_, fun F hF => hb.2 F (List.contains_iff_mem.mp (List.all_eq_true.mp hp F hF))⟩
  rw [hR] at h
  cases hq : b.requires with
  | none => rw [hq] at h; cases h
  | some R' => rw [hq] at h; exact (hb.1 R' hq).mono h

theorem elementsCovers_sound {a b : Effect} (h : elementsCovers a.elements b.elements = true) {r after} {v : Tm}
    (ha : ∀ R, a.elements = some R → v = .tru → ElemsAt R r after) :
    ∀ R, b.elements = some R → v = .tru → ElemsAt R r after := by
  intro R hR hv
  rw [hR] at h
  cases hq : a.elements with
  | none => rw [hq] at h; cases h
  | some R' => rw [hq] at h; exact (ha R' hq hv).mono h

/-- A frame within another's. Where the other states no store regions:
a smaller coarse bound; the receiver's store excepted only where the other
excepts it and not the receiver's own locations, or lets everything change;
and the receiver's own locations excepted only where the other excepts them
or lets everything change. Where it states store regions, which add the
locations they select, each entry of the frame lies in one of the other's
(`Footprint.le`), or the other's closed bound lets everything change. -/
def Effect.frameCovers (a b : Effect) : Bool :=
  if b.regions.isEmpty then
    a.footprint.le b.footprint &&
      (!a.receiverStore || (b.receiverStore && !b.receiverOwn) || b.footprint == .top) &&
      (!a.receiverOwn || b.receiverOwn || b.footprint == .top)
  else Footprints.Footprint.le (fun _ _ => none) a.frame b.frame || b.closed == .top

private theorem Effect.withinClosed_top_of {e : Effect} {r : Tm} {before after : Heap}
    (ht : e.footprint = .top) (h : Footprints.Closed.top.Holds before after) : e.withinClosed r before after := by
  apply Effect.withinClosed_of_holds
  rw [ht]; exact h

theorem Effect.frameCovers_sound {a b : Effect} (h : a.frameCovers b = true) {r : Tm} {args : List Tm}
    {before after : Heap} (hwa : a.within r args before after) : b.within r args before after := by
  unfold Effect.frameCovers at h
  split at h
  · rename_i hb
    have hbr : b.regions = [] := List.isEmpty_iff.mp hb
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hle, hs⟩, hw⟩ := h
    have hown : a.ownChange.le b.ownChange = true := by
      simp only [Footprints.Closed.le, Bool.and_eq_true] at hle
      simp only [Effect.ownChange, Footprints.Closed.le, Bool.and_eq_true]
      exact ⟨rfl, hle.2⟩
    apply Effect.within_of_closed hbr
    have hwc := Effect.within_closed hwa
    by_cases hao : a.receiverOwn = true
    · simp only [hao, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hw
      rcases hw with hbo | htop
      · simp only [Effect.withinClosed, hao, if_true] at hwc
        simp only [Effect.withinClosed, hbo, if_true]
        exact ⟨hwc.1.mono hle, hwc.2.mono hown⟩
      · exact Effect.withinClosed_top_of htop (Effect.within_top hwa)
    · simp only [Bool.not_eq_true] at hao
      by_cases has : a.receiverStore = true
      · simp only [has, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
          Bool.not_eq_true'] at hs
        rcases hs with ⟨hbs, hbo⟩ | htop
        · simp only [Effect.withinClosed, hao, has, Bool.false_eq_true, if_false, if_true] at hwc
          simp only [Effect.withinClosed, hbo, hbs, Bool.false_eq_true, if_false, if_true]
          exact hwc.mono hle
        · exact Effect.withinClosed_top_of htop (Effect.within_top hwa)
      · simp only [Bool.not_eq_true] at has
        exact Effect.withinClosed_of_holds ((Effect.within_holds hwa has hao).mono hle)
  · simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with hle | htop
    · exact Footprints.Post.mono hle (fun _ _ _ _ hc => by cases hc) hwa
    · apply Effect.within_of_holds
      rw [htop]
      exact Effect.within_top hwa

/-- A frame within the other's and the same promise; a fresh result, or a
fresh object, where the other states one; `onThrow` where the other states
it; a weaker precondition and stronger promises. -/
def Effect.covers (a b : Effect) : Bool :=
  a.frameCovers b && a.promise == b.promise && (!b.fresh || a.fresh) && (!b.onThrow || a.onThrow) &&
    (!b.freshObject || a.freshObject) &&
    requiresCovers a.requires b.requires && elementsCovers a.elements b.elements && preCovers a.pre b.pre &&
    ensuresCovers a.ensures b.ensures && (!b.receiverGrows || a.receiverGrows) &&
    (b.elementWrite.isNone || a.elementWrite == b.elementWrite)

theorem Effect.covers_sound {a b : Effect} (h : a.covers b = true) : a.Covers b := by
  simp only [Effect.covers, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfc, hp⟩, hf⟩, ho⟩, hfo⟩, hrq⟩, hel⟩, hpre⟩, hens⟩, hgr⟩, hwr⟩ := h
  simp only [beq_iff_eq] at hp
  refine ⟨fun r args before after v ⟨hw, hfr, hfro, hels, hen, hga, hwa⟩ =>
      ⟨Effect.frameCovers_sound hfc hw, fun hb => hfr ?_,
      fun hb => hfro ?_, elementsCovers_sound hel hels,
      fun F hF => hen F (List.contains_iff_mem.mp (List.all_eq_true.mp hens F hF)),
      fun hb => hga (by simp only [hb, Bool.not_true, Bool.false_or] at hgr; exact hgr),
      fun w hb => hwa w (by
        simp only [hb, Option.isNone_some, Bool.false_or, beq_iff_eq] at hwr; exact hwr)⟩,
    fun R args k W u hu => ?_, fun r args before after he hb => Effect.frameCovers_sound hfc (he ?_),
    fun r args heap hq => requiresCovers_sound hrq hpre hq⟩
  · rw [hb] at hf; simpa using hf
  · rw [hb] at hfo; simpa using hfo
  · simpa [Effect.result, Effect.promised, hp] using hu
  · rw [hb] at ho; simpa using ho

/-- Whether binding `n` actuals of a signature keeps what it guarantees and
the bound signature covers `b`. -/
def Effect.bindCovers (n : Nat) (a b : Effect) : Bool := a.keeps n && (a.drop n).covers b

theorem Effect.bindCovers_keeps {n : Nat} {a b : Effect} (h : a.bindCovers n b = true) : a.keeps n = true := by
  simp only [Effect.bindCovers, Bool.and_eq_true] at h; exact h.1

theorem Effect.bindCovers_covers {n : Nat} {a b : Effect} (h : a.bindCovers n b = true) :
    (a.drop n).covers b = true := by
  simp only [Effect.bindCovers, Bool.and_eq_true] at h; exact h.2

theorem Effect.Covers.refl (e : Effect) : e.Covers e :=
  ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ h => h⟩

/-- Two executions' results combine as the results of their operands do. -/
theorem Effect.cross_result (e : Effect) {B C D : Fam} {a : Tm} {n}
    (h : CrossCompatUpTo n B C D) : CrossCompatUpTo n (e.result B a) (e.result C a) (e.result D a) := by
  intro j hj W W' heap hok hok' u hb hc
  unfold Effect.result at hb hc ⊢
  match hp : e.promise with
  | none => rw [hp] at hb hc; exact h j hj W W' heap hok hok' u hb hc
  | some (.guards _) =>
    rw [hp] at hb hc
    rcases hb with ⟨rfl, hb⟩ | rfl
    · rcases hc with ⟨-, hc⟩ | hc
      · exact .inl ⟨rfl, h j hj W W' heap hok hok' a hb hc⟩
      · cases hc
    · exact .inr rfl
  | some (.asserts _) =>
    rw [hp] at hb hc
    exact ⟨hb.1, h j hj W W' heap hok hok' a hb.2 hc.2⟩

theorem PromiseWith.weaken' {Ξ Ξ' : Fam} {effect effect' Acc Acc' Rc Rc' R T k W v}
    (he : effect.Covers effect')
    (hexc : ∀ j, j < k → ∀ U u, Ξ j U u → Ξ' j U u)
    (hrecv : ∀ j, j < k → ∀ U r, Rc' j U r → Rc j U r)
    (hacc : ∀ j, j < k → ∀ U args, Acc' j U args → Acc j U args)
    (hres : ∀ j, j < k → ∀ U u, R j U u → T j U u)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : PromiseWith Ξ' effect' Acc' Rc' T k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha hq
  obtain ⟨result, hi, hs⟩ :=
    h j hj U hx hu heap hh r hrv (hrecv j hj U r hr) args hv (hacc j hj U args ha) (he.2.2.2 r args heap hq)
  exact ⟨result, hi, SafePostExc.consequence_below' (fun m hm => hexc m (by omega))
    (fun m hm U' u hu => he.2.1 T args m U' u
      (Effect.result_mono effect (hres m (by omega) U') (hres m (by omega) U') hu)) (he.1 r args heap)
    (he.2.2.1 r args heap) hs⟩

theorem PromiseWith.weaken {Ξ : Fam} {effect effect' Acc Acc' Rc Rc' R T k W v}
    (he : effect.Covers effect')
    (hrecv : ∀ j, j < k → ∀ U r, Rc' j U r → Rc j U r)
    (hacc : ∀ j, j < k → ∀ U args, Acc' j U args → Acc j U args)
    (hres : ∀ j, j < k → ∀ U u, R j U u → T j U u)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : PromiseWith Ξ effect' Acc' Rc' T k W v :=
  h.weaken' he (fun _ _ _ _ h => h) hrecv hacc hres

/-- Receiver restriction may depend on the calling world, without changing effects. -/
theorem PromiseWith.weaken_recv {effect : Effect} {Acc : ArgFam} {Rc Rc' R : Fam}
    {k W v}
    (hrecv : ∀ j (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      ∀ r, Rc' j U r → Rc j U r)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : PromiseWith Ξ effect Acc Rc' R k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha hq
  exact h j hj U hx hu heap hh r hrv (hrecv j hj U hx r hr) args hv ha hq

theorem PromiseWith.congr {Ξ Ξ' : Fam} {effect Acc Acc' Rc Rc' R T n W v}
    (hexc : Agree Ξ Ξ' n)
    (hrecv : Agree Rc Rc' n)
    (hacc : ∀ j, j < n → ∀ U args, Acc j U args ↔ Acc' j U args)
    (hres : Agree R T n) :
    PromiseWith Ξ effect Acc Rc R n W v ↔ PromiseWith Ξ' effect Acc' Rc' T n W v := by
  constructor <;> intro h
  · exact h.weaken' (Effect.Covers.refl _)
      (fun j hj U u => (hexc j hj U u).mp)
      (fun j hj U r => (hrecv j hj U r).mpr)
      (fun j hj U args => (hacc j hj U args).mpr)
      (fun j hj U u => (hres j hj U u).mp)
  · exact h.weaken' (Effect.Covers.refl _)
      (fun j hj U u => (hexc j hj U u).mpr)
      (fun j hj U r => (hrecv j hj U r).mp)
      (fun j hj U args => (hacc j hj U args).mp)
      (fun j hj U u => (hres j hj U u).mpr)

/-! ### Construct signatures -/

/-- The promise of one construct signature, independent of argument-list
syntax: constructing the value, in any strictly future world, with actuals
`P` admits, runs a body safe at the result whose normal return meets the
signature's effect, from the heap the construction starts in. -/
def ConstructPromise (Ξ : Fam) (effect : Effect) (P : ArgFam) (R : Fam) (k : Nat) (W : WorldT k)
    (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j),
    WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U → ∀ (heap : Heap), HeapOk j U heap →
      ∀ args, CallArguments.Values args → P j U args → effect.Requires .undef args heap →
        ∃ result, ConstructsTo v args result ∧
          SafePostExc Ξ (effect.result R (effect.promised args)) (effect.post .undef args heap)
            (effect.excPost .undef args heap) j U heap result

theorem ConstructPromise.down {effect P R n W v}
    (h : ConstructPromise Ξ effect P R (n + 1) W v) :
    ConstructPromise Ξ effect P R n (trunc n (Nat.le_succ n) W) v := by
  intro j hj U hx hu heap hh args hv ha hq
  exact h j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh args hv ha hq

theorem ConstructPromise.mono {effect P R n W W' v} (hx : WExt W W')
    (h : ConstructPromise Ξ effect P R n W v) : ConstructPromise Ξ effect P R n W' v := by
  intro j hj U hy hu heap hh args hv ha hq
  exact h j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh args hv ha hq

theorem ConstructPromise.weaken' {Ξ Ξ' : Fam} {effect effect' P P' R T k W v}
    (he : effect.Covers effect')
    (hexc : ∀ j, j < k → ∀ U u, Ξ j U u → Ξ' j U u)
    (hacc : ∀ j, j < k → ∀ U args, P' j U args → P j U args)
    (hres : ∀ j, j < k → ∀ U u, R j U u → T j U u)
    (h : ConstructPromise Ξ effect P R k W v) : ConstructPromise Ξ' effect' P' T k W v := by
  intro j hj U hx hu heap hh args hv ha hq
  obtain ⟨result, hc, hs⟩ := h j hj U hx hu heap hh args hv (hacc j hj U args ha) (he.2.2.2 .undef args heap hq)
  exact ⟨result, hc, SafePostExc.consequence_below' (fun m hm => hexc m (by omega))
    (fun m hm U' u hu => he.2.1 T args m U' u
      (Effect.result_mono effect (hres m (by omega) U') (hres m (by omega) U') hu)) (he.1 .undef args heap)
    (he.2.2.1 .undef args heap) hs⟩

theorem ConstructPromise.congr {Ξ Ξ' : Fam} {effect P P' R T n W v}
    (hexc : Agree Ξ Ξ' n)
    (hacc : ∀ j, j < n → ∀ U args, P j U args ↔ P' j U args)
    (hres : Agree R T n) :
    ConstructPromise Ξ effect P R n W v ↔ ConstructPromise Ξ' effect P' T n W v := by
  constructor <;> intro h
  · exact h.weaken' (Effect.Covers.refl _)
      (fun j hj U u => (hexc j hj U u).mp)
      (fun j hj U args => (hacc j hj U args).mpr)
      (fun j hj U u => (hres j hj U u).mp)
  · exact h.weaken' (Effect.Covers.refl _)
      (fun j hj U u => (hexc j hj U u).mpr)
      (fun j hj U args => (hacc j hj U args).mp)
      (fun j hj U u => (hres j hj U u).mpr)

/-- A plain signature's promise gives a safe construction once its
postcondition is forgotten. -/
theorem ConstructPromise.erase {effect P R k W v} (hp : effect.plain = true)
    (h : ConstructPromise Ξ effect P R k W v) :
    ∀ (j : Nat) (hj : j < k) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U → ∀ (heap : Heap), HeapOk j U heap →
        ∀ args, CallArguments.Values args → P j U args →
          ∃ result, ConstructsTo v args result ∧ Safe Ξ R j U heap result := by
  intro j hj U hx hu heap hh args hv ha
  obtain ⟨result, hc, hs⟩ := h j hj U hx hu heap hh args hv ha
    (Effect.requires_none (Effect.plain_requires hp) (Effect.plain_pre hp) .undef args heap)
  rw [Effect.result_plain hp] at hs
  exact ⟨result, hc, HeapObservations.erase hs.post⟩

/-- **Construct signatures.** Values meeting every signature `(parameters,
result)` under `new`, each with its effect (`ConstructPromise`). The code is
construct-only, so a plain call cannot run it, and no code without
`[[Construct]]` is one. As for call signatures, the promise is about the term
after the step, which is what lets the signature's variance be used only
below the current level. -/
def ctorsT (Ξ : Fam) (L : List (MethodArrow Fam)) : Fam := fun k W v =>
  Constructible v ∧ ∀ p ∈ L, ConstructPromise Ξ p.effect (ArgsT p.arguments) p.result k W v

theorem ctorsT_adm (L : List (MethodArrow Fam)) : Adm (ctorsT Ξ L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun p hp => (h.2 p hp).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun p hp => (h.2 p hp).mono hx⟩⟩

/-- A variadic construct signature: its fixed parameters, then, as one
argument pack, the rest. -/
abbrev CtorRestSignature := Contract Unit (List Fam × ArgFam) Fam

/-- **Variadic construct signatures** `(parameters, rest, result)`: as
`ctorsT`, for the lists `CtorRest` admits. -/
def ctorRestsT (Ξ : Fam) (S : List CtorRestSignature) : Fam := fun k W v =>
  Constructible v ∧ ∀ s ∈ S,
    ConstructPromise Ξ s.effect (CtorRest s.arguments.1 s.arguments.2) s.result k W v

theorem ctorRestsT_adm (S : List CtorRestSignature) : Adm (ctorRestsT Ξ S) :=
  ⟨fun _ _ _ h => ⟨h.1, fun p hp => (h.2 p hp).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun p hp => (h.2 p hp).mono hx⟩⟩

theorem ctorRestsT_append (S T : List CtorRestSignature) (k : Nat) (W : WorldT k) (v : Val) :
    ctorRestsT Ξ (S ++ T) k W v ↔ ctorRestsT Ξ S k W v ∧ ctorRestsT Ξ T k W v := by
  simp only [ctorRestsT, List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨hc, hl, hm⟩; exact ⟨⟨hc, hl⟩, hc, hm⟩
  · rintro ⟨⟨hc, hl⟩, -, hm⟩; exact ⟨hc, hl, hm⟩

theorem ctorsT_select {L n W v p} (hf : ctorsT Ξ L n W v) (hp : p ∈ L) : ctorsT Ξ [p] n W v :=
  ⟨hf.1, fun q hq => by cases List.mem_singleton.mp hq; exact hf.2 p hp⟩

theorem ctorsT_append (L M : List (MethodArrow Fam)) (k : Nat) (W : WorldT k) (v : Val) :
    ctorsT Ξ (L ++ M) k W v ↔ ctorsT Ξ L k W v ∧ ctorsT Ξ M k W v := by
  simp only [ctorsT, List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨hc, hl, hm⟩; exact ⟨⟨hc, hl⟩, hc, hm⟩
  · rintro ⟨⟨hc, hl⟩, -, hm⟩; exact ⟨hc, hl, hm⟩

theorem ctorsT_congr {Ξ Ξ' : Fam} {α : Type} (l : List α) (f g : α → MethodArrow Fam) {n : Nat}
    (hΞ : Agree Ξ Ξ' n)
    (h : ∀ x ∈ l, (f x).effect = (g x).effect ∧ ArgsAgree n (f x).arguments (g x).arguments ∧
      Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : ctorsT Ξ (l.map f) n W v ↔ ctorsT Ξ' (l.map g) n W v := by
  unfold ctorsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩ <;>
    obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
  · have hp := hs (f x) (List.mem_map_of_mem hm)
    rw [(h x hm).1] at hp
    exact (ConstructPromise.congr hΞ (fun j hj U args => ArgsT_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mp hp
  · have hp := hs (g x) (List.mem_map_of_mem hm)
    rw [← (h x hm).1] at hp
    exact (ConstructPromise.congr hΞ (fun j hj U args => ArgsT_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mpr hp

theorem ctorRestsT_congr {Ξ Ξ' : Fam} {α : Type} (l : List α) (f g : α → CtorRestSignature) {n : Nat}
    (hΞ : Agree Ξ Ξ' n)
    (h : ∀ x ∈ l, (f x).effect = (g x).effect ∧ ArgsAgree n (f x).arguments.1 (g x).arguments.1 ∧
      Agree (f x).arguments.2 (g x).arguments.2 n ∧ Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : ctorRestsT Ξ (l.map f) n W v ↔ ctorRestsT Ξ' (l.map g) n W v := by
  unfold ctorRestsT
  have hacc : ∀ x ∈ l, ∀ j, j < n → ∀ U args,
      CtorRest (f x).arguments.1 (f x).arguments.2 j U args ↔
        CtorRest (g x).arguments.1 (g x).arguments.2 j U args := by
    intro x hm j hj U args
    have hl := ArgsAgree_length (h x hm).2.1
    unfold CtorRest
    rw [hl]
    exact and_congr Iff.rfl (and_congr (ArgsT_congr (h x hm).2.1 hj U _) ((h x hm).2.2.1 j hj U _))
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩ <;>
    obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
  · have hp := hs (f x) (List.mem_map_of_mem hm)
    rw [(h x hm).1] at hp
    exact (ConstructPromise.congr hΞ (hacc x hm) (h x hm).2.2.2).mp hp
  · have hp := hs (g x) (List.mem_map_of_mem hm)
    rw [← (h x hm).1] at hp
    exact (ConstructPromise.congr hΞ (hacc x hm) (h x hm).2.2.2).mpr hp

/-- Combining result guarantees retains the effects established for this call
domain by either premise. World-sensitive results still require the same
cross-world compatibility as ordinary arrows. Effects concern the shared final
heap, so they do not depend on which result world supplies the conclusion. -/
theorem PromiseWith.combine {effect other Acc Rc B C D k W v}
    (hs : effect.sameResult other = true)
    (hb : PromiseWith Ξ effect Acc Rc B k W v)
    (hc : PromiseWith Ξ other Acc Rc C k W v)
    (hcross : ∀ n, n < k → CrossCompatUpTo n B C D) :
    PromiseWith Ξ (effect.meet other) Acc Rc D k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha hq
  have hq' : other.Requires r args heap := by
    simp only [Effect.sameResult, Bool.and_eq_true, beq_iff_eq] at hs
    exact ⟨fun R hR => hq.1 R (by simp only [Effect.meet]; rw [hs.1.1.1.1.2]; exact hR),
      fun F hF => hq.2 F (by simp only [Effect.meet]; rw [hs.1.1.2]; exact hF)⟩
  obtain ⟨b, hib, hsb⟩ := hb j hj U hx hu heap hh r hrv hr args hv ha ⟨hq.1, hq.2⟩
  obtain ⟨c, hic, hsc⟩ := hc j hj U hx hu heap hh r hrv hr args hv ha hq'
  cases CallArguments.invoke_deterministic hib hic
  obtain ⟨hr1, hp1, hr2, hp2⟩ := Effect.meet_same hs
  rw [hr2, hp2] at hsc
  rw [hr1, hp1]
  exact ⟨b, hib, SafePostExc.weaken
    (fun heap' value hpost => (Effect.post_meet hs r args heap heap' value).mpr hpost)
    (fun heap' hexc => Effect.excPost_meet hs r args heap heap' hexc.1 hexc.2)
    (SafePostExc.cross_upto j (Effect.cross_result effect (hcross j hj)) U U heap b hh hh hsb hsc)⟩

/-- Binding saves a receiver and argument prefix, then forwards without
changing the heap. This generic rule covers fixed and variadic signatures;
only the argument-admission premise differs. The callee's effect is retained
at the heap where the forwarded call actually starts; a promise, about an
actual past the saved prefix, is about the same actual of the bound call. -/
theorem PromiseWith.bound {effect : Effect} {Acc Rest : ArgFam} {Rt R Rc : Fam}
    {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {tv rv : Val} {pre : List Tm}
    (hkeeps : effect.keeps pre.length = true)
    (ht : PromiseWith Ξ effect Acc Rt R k W tv)
    (hRt : Adm Rt) (hRest : Adm Rest)
    (hrv : isVal rv = true) (hr : Rt k W rv) (hp : CallArguments.Values pre)
    (hprefix : ∀ j (hj : j < k) U, WExt (trunc j (Nat.le_of_lt hj) W) U →
      ∀ args, Rest j U args → Acc j U (pre ++ args)) :
    PromiseWith Ξ (effect.drop pre.length) Rest Rc R k W (.objAt fs (.bound tv rv pre) oid) := by
  intro j hj U hx hu heap hh r hv _ args hargs ha _
  refine ⟨_, .bound hv hargs, ?_⟩
  cases j with
  | zero => trivial
  | succ i =>
    have hi : i < k := by omega
    have hxU : WExt (trunc i (Nat.le_of_lt hi) W) (trunc i (Nat.le_succ i) U) := by
      have hx' := WExt_trunc (Nat.le_succ i) hx
      rwa [trunc_trunc] at hx'
    have hu' := WorldAdm_trunc (Nat.le_succ i) hu
    have hh' := HeapOk_trunc i U heap hh
    have hr' := hRt.mono i _ _ hxU rv (hRt.down_le k i (Nat.le_of_lt hi) W rv hr)
    have ha' := hRest.down i U args ha
    have hall : CallArguments.Values (pre ++ args) := by
      intro a hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hp a hm
      · exact hargs a hm
    obtain ⟨res, hinv, hsafe⟩ := ht i hi _ hxU hu' heap hh' rv hrv hr'
      (pre ++ args) hall (hprefix i hi _ hxU args ha')
      (Effect.requires_none (Effect.keeps_requires hkeeps) (Effect.keeps_pre hkeeps) rv (pre ++ args) heap)
    rw [Effect.result_drop, Effect.promised_drop hkeeps]
    exact .inr ⟨_, heap, res, WExt_refl _, hu', hinv.step heap, hh',
      SafePostExc.weaken (fun _ _ h => Effect.post_drop pre.length h)
        (fun _ h => Effect.excPost_drop pre.length h) hsafe⟩

/-- Application consumes a qualified signature, without inspecting the
callee's implementation. Its entry heap is after actual evaluation. -/
theorem call_safe_exc {effect : Effect} {P : ArgFam} {Rc R : Fam}
    (hP : Adm P) (hRc : Adm Rc) {n W heap f r vs}
    (hf : PromiseWith Ξ effect P Rc R n W f) (hr : Rc n W r)
    (hrv : isVal r = true) (hv : CallArguments.Values vs) (ha : P n W vs)
    (hw : WorldAdm W) (hh : HeapOk n W heap) (hq : effect.Requires r vs heap) :
    SafePostExc Ξ (effect.result R (effect.promised vs)) (effect.post r vs heap) (effect.excPost r vs heap)
      n W heap (.invoke f r vs) := by
  cases n with
  | zero => trivial
  | succ n =>
    let U := trunc n (Nat.le_succ n) W
    obtain ⟨body, hi, hs⟩ := hf n (Nat.lt_succ_self n) U (WExt_refl _)
      (WorldAdm_trunc _ hw) heap (HeapOk_trunc n W heap hh) r hrv (hRc.down n W r hr)
      vs hv (hP.transfer ha n (Nat.le_succ n) U (WExt_refl _)) hq
    exact .inr ⟨U, heap, body, WExt_refl _, WorldAdm_trunc _ hw, hi.step heap,
      HeapOk_trunc n W heap hh, hs⟩

theorem call_safe {effect : Effect} {P : ArgFam} {Rc R : Fam}
    (hP : Adm P) (hRc : Adm Rc) {n W heap f r vs}
    (hf : PromiseWith Ξ effect P Rc R n W f) (hr : Rc n W r)
    (hrv : isVal r = true) (hv : CallArguments.Values vs) (ha : P n W vs)
    (hw : WorldAdm W) (hh : HeapOk n W heap) (hq : effect.Requires r vs heap) :
    SafePost Ξ (effect.result R (effect.promised vs)) (effect.post r vs heap) n W heap (.invoke f r vs) :=
  (call_safe_exc hP hRc hf hr hrv hv ha hw hh hq).post

/-- Trailing `undefined` actuals change no precondition: a construction's
positions past its actuals hold `undefined` either way (`callEnv_pad`). -/
theorem Effect.requires_pad {e : Effect} {r : Tm} {args pad : List Tm} {h : Heap}
    (hpad : ∀ a ∈ pad, a = .undef) (hq : e.Requires r args h) : e.Requires r (args ++ pad) h := by
  refine ⟨hq.1, fun F hF => ?_⟩
  rw [callEnv_pad r args hpad]
  exact hq.2 F hF

/-- A construction of a class value with value actuals takes one step to the
body its signature makes safe, meeting the signature's effect from the heap
it starts in, where the signature's precondition holds of the construction's
actuals (`call-requires`) and it states no promise, so its result operand is
the result's type. The signature may declare trailing positions the
construction omits: each admits `undefined`, which the step binds there. -/
theorem construct_safe_exc_requires {effect : Effect} (hpr : effect.promise = none) {P : ArgFam} {R : Fam}
    (hP : Adm P) {n W heap v vs pad}
    (hf : ConstructPromise Ξ effect P R n W v) (hv : CallArguments.Values vs)
    (hpad : ∀ a ∈ pad, a = .undef) (ha : P n W (vs ++ pad))
    (hw : WorldAdm W) (hh : HeapOk n W heap) (hq : effect.Requires .undef vs heap) :
    SafePostExc Ξ R (effect.post .undef vs heap) (effect.excPost .undef vs heap) n W heap (.construct v vs) := by
  cases n with
  | zero => trivial
  | succ n =>
    let U := trunc n (Nat.le_succ n) W
    have hvp : CallArguments.Values (vs ++ pad) := by
      intro a h
      rcases List.mem_append.mp h with h | h
      · exact hv a h
      · rw [hpad a h]; rfl
    obtain ⟨result, ⟨fs, c, enter, oid, rfl, hc, rfl⟩, hs⟩ := hf n (Nat.lt_succ_self n) U (WExt_refl _)
      (WorldAdm_trunc _ hw) heap (HeapOk_trunc n W heap hh) _ hvp
      (hP.transfer ha n (Nat.le_succ n) U (WExt_refl _))
      (Effect.requires_pad hpad hq)
    rw [CallArguments.construction_pad hc _ _ hpad, Effect.result_none hpr] at hs
    exact .inr ⟨U, heap, _, WExt_refl _, WorldAdm_trunc _ hw,
      CallArguments.construction_step hc hv heap, HeapOk_trunc n W heap hh,
      SafePostExc.weaken (fun _ _ h => Effect.post_pad rfl hpad h) (fun _ h => Effect.excPost_pad hpad h) hs⟩

/-- A construction at a plain signature, whose precondition is empty. -/
theorem construct_safe_exc {effect : Effect} (hpl : effect.plain = true) {P : ArgFam} {R : Fam}
    (hP : Adm P) {n W heap v vs pad}
    (hf : ConstructPromise Ξ effect P R n W v) (hv : CallArguments.Values vs)
    (hpad : ∀ a ∈ pad, a = .undef) (ha : P n W (vs ++ pad))
    (hw : WorldAdm W) (hh : HeapOk n W heap) :
    SafePostExc Ξ R (effect.post .undef vs heap) (effect.excPost .undef vs heap) n W heap (.construct v vs) :=
  construct_safe_exc_requires
    (by simp only [Effect.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at hpl; exact hpl.1.1)
    hP hf hv hpad ha hw hh (Effect.requires_none (Effect.plain_requires hpl) (Effect.plain_pre hpl) .undef vs heap)

/-- An operational invariant that only appends fresh locations supplies
the normal-return preservation postcondition, supplementing ordinary safety.
The safety proof supplies the same worlds and result contract at every step. -/
theorem prefix_safe {P : Tm → Prop} {R : Fam} {r : Tm} {args : List Tm}
    (hstep : ∀ {h t h' t'}, P t → Step h t h' t' → h.IsPrefix h' ∧ P t') :
    ∀ {n W heap t}, P t → Safe Ξ R n W heap t →
      SafePost Ξ R ((Effect.ofFootprint .empty).post r args heap) n W heap t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W heap t hp hs
    rcases hs with (⟨hv, ht⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, ht, (Effect.post_ofFootprint _ _ _ _ _ _).mpr
        (Footprints.Closed.holds_empty.mpr ⟨[], by simp⟩)⟩)
    · exact .inl (.inr hth)
    · obtain ⟨hprefix, hp'⟩ := hstep hp step
      exact .inr ⟨U, h', t', hx, hu, step, hh,
        HeapObservations.weaken (fun _ _ hpost => (Effect.post_ofFootprint _ _ _ _ _ _).mpr
          (Footprints.Closed.holds_empty.mpr
          (hprefix.trans (Footprints.Closed.holds_empty.mp ((Effect.post_ofFootprint _ _ _ _ _ _).mp hpost)))))
          (ih hp' hs)⟩

/-- The same invariant bounds the heap a throw leaves: every step keeps the
heap a prefix, so a raise does too. -/
theorem prefix_safe_exc {P : Tm → Prop} {R : Fam} {r : Tm} {args : List Tm}
    (hstep : ∀ {h t h' t'}, P t → Step h t h' t' → h.IsPrefix h' ∧ P t') :
    ∀ {n W heap t}, P t → Safe Ξ R n W heap t →
      SafePostExc Ξ R ((Effect.ofFootprint .empty).post r args heap)
        (fun h' => Footprints.Closed.empty.Holds heap h') n W heap t := by
  intro n W heap t hp hs
  have hpost := prefix_safe (r := r) (args := args) hstep hp hs
  suffices ∀ {n W h t}, P t → heap.IsPrefix h → SafePost Ξ R ((Effect.ofFootprint .empty).post r args heap) n W h t →
      SafePostExc Ξ R ((Effect.ofFootprint .empty).post r args heap)
        (fun h' => Footprints.Closed.empty.Holds heap h') n W h t from this hp (List.prefix_refl _) hpost
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hp hpre hs
    rcases hs with (hv | hr) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl hv)
    · exact .inl (.inr ⟨hr, Footprints.Closed.holds_empty.mpr hpre⟩)
    · obtain ⟨hprefix, hp'⟩ := hstep hp step
      exact .inr ⟨U, h', t', hx, hu, step, hh, ih hp' (hpre.trans hprefix) hs⟩

theorem pure_safe_exc {R : Fam} {r : Tm} {args : List Tm} {n W heap t}
    (hp : Purity.PureRun t) (hs : Safe Ξ R n W heap t) :
    SafePostExc Ξ R ((Effect.ofFootprint .empty).post r args heap)
      (fun h' => Footprints.Closed.empty.Holds heap h') n W heap t :=
  prefix_safe_exc Purity.CollectingRun.step (.pure hp) hs

def callsT (Ξ : Fam) (L : List (Arrow Fam)) : Fam := fun k W v =>
  Invocable v ∧ ∀ s ∈ L, PromiseWith Ξ s.effect (ArgsShort s.arguments) s.receiver s.result k W v

/-- Assemble an intersection from its individual qualified signatures. -/
theorem callsT_of_signatures {L : List (Arrow Fam)} {n W v}
    (hi : Invocable v) (hs : ∀ p ∈ L, callsT Ξ [p] n W v) : callsT Ξ L n W v :=
  ⟨hi, fun p hp => (hs p hp).2 p (List.mem_singleton_self _)⟩

theorem callsT_adm (L : List (Arrow Fam)) : Adm (callsT Ξ L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun s hs => (h.2 s hs).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun s hs => (h.2 s hs).mono hx⟩⟩

theorem callsT_erase {L : List (Arrow Fam)} {n W v} (hp : ∀ s ∈ L, s.effect.plain = true)
    (h : callsT Ξ L n W v) : Verification.callsT Ξ (L.map Arrow.plain) n W v := by
  refine ⟨h.1, ?_⟩
  intro p hm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
  exact (h.2 s hs).erase (hp s hs)

theorem callsT_select {L n W v p} (hf : callsT Ξ L n W v) (hp : p ∈ L) :
    callsT Ξ [p] n W v := by
  refine ⟨hf.1, ?_⟩
  intro q hq
  cases List.mem_singleton.mp hq
  exact hf.2 p hp

/-- A bound fixed signature keeps its effect, with the saved prefix removed
from its domain. -/
theorem callsT_bound {effect : Effect} {Rt R Rc : Fam} {Ps Ds : List Fam}
    {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {tv rv : Val} {pre : List Tm}
    (hRt : Adm Rt) (hPs : ∀ A ∈ Ps, Adm A) (hDs : ∀ A ∈ Ds, Adm A)
    (hkeeps : effect.keeps pre.length = true)
    (ht : callsT Ξ [⟨Rt, Ps ++ Ds, R, effect⟩] k W tv)
    (hrv : isVal rv = true) (hsr : Scoped 0 rv) (hr : Rt k W rv)
    (hp : ArgsT Ps k W pre) (hv : CallArguments.Values pre) (hsp : ∀ a ∈ pre, Scoped 0 a) :
    callsT Ξ [⟨Rc, Ds, R, effect.drop pre.length⟩] k W (.objAt fs (.bound tv rv pre) oid) := by
  refine ⟨⟨fs, _, _, rfl, rfl, ?_⟩, ?_⟩
  · simp only [Scoped, scopedArgs_iff]
    exact ⟨ht.1.scoped, hsr, hsp⟩
  · intro p hm
    cases List.mem_singleton.mp hm
    exact (ht.2 _ (List.mem_singleton_self _)).bound hkeeps hRt
      (Adm.of_transfer (fun ha j hj U hx => ArgsShort_transfer hDs ha j hj U hx)) hrv hr hv
      (fun j hj U hx args ha => ArgsShort_prefix (ArgsT_transfer hPs hp j (Nat.le_of_lt hj) U hx) ha)

theorem callsT_congr {Ξ Ξ' : Fam} {α : Type} (l : List α) (f g : α → Arrow Fam) {n : Nat}
    (hexc : Agree Ξ Ξ' n)
    (he : ∀ x ∈ l, (f x).effect = (g x).effect)
    (h : ∀ x ∈ l, Agree (f x).receiver (g x).receiver n ∧
      ArgsAgree n (f x).arguments (g x).arguments ∧ Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : callsT Ξ (l.map f) n W v ↔ callsT Ξ' (l.map g) n W v := by
  unfold callsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [← he x hm]
    exact (PromiseWith.congr hexc (h x hm).1
      (fun j hj U args => ArgsShort_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mp (hs (f x) (List.mem_map_of_mem hm))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [he x hm]
    exact (PromiseWith.congr hexc (h x hm).1
      (fun j hj U args => ArgsShort_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mpr (hs (g x) (List.mem_map_of_mem hm))

/-- Fixed arguments are value families, whereas the rest is an argument-list
family. Both are operands of the same effect-qualified contract. -/
abbrev RestSignature := Contract Fam (List Fam × ArgFam) Fam

def restsT (Ξ : Fam) (L : List RestSignature) : Fam := fun k W v =>
  Invocable v ∧ ∀ s ∈ L,
    PromiseWith Ξ s.effect (ArgsRest s.arguments.1 s.arguments.2) s.receiver s.result k W v

/-- Assemble an intersection from its individual qualified signatures. -/
theorem restsT_of_signatures {L : List (RestSignature)} {n W v}
    (hi : Invocable v) (hs : ∀ p ∈ L, restsT Ξ [p] n W v) : restsT Ξ L n W v :=
  ⟨hi, fun p hp => (hs p hp).2 p (List.mem_singleton_self _)⟩

theorem restsT_select {L n W v p} (hf : restsT Ξ L n W v) (hp : p ∈ L) :
    restsT Ξ [p] n W v := by
  refine ⟨hf.1, ?_⟩
  intro q hq
  cases List.mem_singleton.mp hq
  exact hf.2 p hp

theorem restsT_adm (L : List RestSignature) : Adm (restsT Ξ L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun s hs => (h.2 s hs).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun s hs => (h.2 s hs).mono hx⟩⟩

theorem restsT_erase {L : List RestSignature} {n W v} (hp : ∀ s ∈ L, s.effect.plain = true)
    (h : restsT Ξ L n W v) :
    Verification.restsT Ξ (L.map fun s => (s.receiver, s.arguments.1, s.arguments.2, s.result)) n W v := by
  refine ⟨h.1, ?_⟩
  intro p hm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
  exact (h.2 s hs).erase (hp s hs)

/-- Binding a variadic signature retains the same effect. A saved prefix
extending into the rest requires a contract closed under prepending those
saved values, exactly as for ordinary variadic binding. -/
theorem restsT_bound {effect : Effect} {Rt R Rc : Fam} {E : ArgFam} {Ps : List Fam}
    {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {tv rv : Val} {pre : List Tm}
    (hRt : Adm Rt) (hPs : ∀ A ∈ Ps, Adm A) (hE : Adm E)
    (hkeeps : effect.keeps pre.length = true)
    (ht : restsT Ξ [⟨Rt, (Ps, E), R, effect⟩] k W tv)
    (hrv : isVal rv = true) (hsr : Scoped 0 rv) (hr : Rt k W rv)
    (hp : ArgsT (Ps.take pre.length) k W (pre.take Ps.length))
    (hext : ∀ j (hj : j ≤ k) U, WExt (trunc j hj W) U →
      ∀ ys, E j U ys → E j U (pre.drop Ps.length ++ ys))
    (hv : CallArguments.Values pre) (hsp : ∀ a ∈ pre, Scoped 0 a) :
    restsT Ξ [⟨Rc, (Ps.drop pre.length, E), R, effect.drop pre.length⟩] k W (.objAt fs (.bound tv rv pre) oid) := by
  refine ⟨⟨fs, _, _, rfl, rfl, ?_⟩, ?_⟩
  · simp only [Scoped, scopedArgs_iff]
    exact ⟨ht.1.scoped, hsr, hsp⟩
  · intro p hm
    cases List.mem_singleton.mp hm
    exact (ht.2 _ (List.mem_singleton_self _)).bound hkeeps hRt
      (Adm.of_transfer (fun ha j hj U hx =>
        ArgsRest_transfer (fun A hm => hPs A (List.mem_of_mem_drop hm)) hE ha j hj U hx))
      hrv hr hv (fun j hj U hx args ha => ArgsRest_prefix
        (ArgsT_transfer (fun A hm => hPs A (List.mem_of_mem_take hm)) hp j (Nat.le_of_lt hj) U hx)
        (hext j (Nat.le_of_lt hj) U hx) ha)

/-- Conjunction and overload normalization preserve every signature's effect. -/
theorem callsT_append (L M : List (Arrow Fam)) (n W v) :
    callsT Ξ (L ++ M) n W v ↔ callsT Ξ L n W v ∧ callsT Ξ M n W v := by
  simp only [callsT, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨hc, hl, hm⟩ => ⟨⟨hc, hl⟩, hc, hm⟩, fun ⟨⟨hc, hl⟩, _, hm⟩ => ⟨hc, hl, hm⟩⟩

theorem restsT_append (L M : List RestSignature) (n W v) :
    restsT Ξ (L ++ M) n W v ↔ restsT Ξ L n W v ∧ restsT Ξ M n W v := by
  simp only [restsT, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨hc, hl, hm⟩ => ⟨⟨hc, hl⟩, hc, hm⟩, fun ⟨⟨hc, hl⟩, _, hm⟩ => ⟨hc, hl, hm⟩⟩

theorem restsT_congr {Ξ Ξ' : Fam} {α : Type} (l : List α) (f g : α → RestSignature) {n : Nat}
    (hexc : Agree Ξ Ξ' n)
    (he : ∀ x ∈ l, (f x).effect = (g x).effect)
    (h : ∀ x ∈ l, Agree (f x).receiver (g x).receiver n ∧
      ArgsAgree n (f x).arguments.1 (g x).arguments.1 ∧
      Agree (f x).arguments.2 (g x).arguments.2 n ∧ Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : restsT Ξ (l.map f) n W v ↔ restsT Ξ' (l.map g) n W v := by
  have args : ∀ x ∈ l, ∀ j, j < n → ∀ U vs,
      ArgsRest (f x).arguments.1 (f x).arguments.2 j U vs ↔
      ArgsRest (g x).arguments.1 (g x).arguments.2 j U vs := by
    intro x hx j hj U vs
    have hl := ArgsAgree_length (h x hx).2.1
    unfold ArgsRest
    rw [hl]
    exact and_congr (ArgsShort_congr (h x hx).2.1 hj U _) ((h x hx).2.2.1 j hj U _)
  unfold restsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [← he x hm]
    exact (PromiseWith.congr hexc (h x hm).1 (args x hm) (h x hm).2.2.2).mp
      (hs (f x) (List.mem_map_of_mem hm))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [he x hm]
    exact (PromiseWith.congr hexc (h x hm).1 (args x hm) (h x hm).2.2.2).mpr
      (hs (g x) (List.mem_map_of_mem hm))

end Verification.CallEffects
