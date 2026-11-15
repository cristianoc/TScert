import Verification.Semantics.ExitPosts
import Verification.Semantics.ExceptionalPosts
import Verification.Semantics.Purity
import Verification.Semantics.ClosedFootprints
import Verification.Semantics.IndexFacts
import Verification.Semantics.StoreRegions
import Verification.Semantics.ElementWrites

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

theorem ElemPred.le_sound {a b : ElemPred} (h : a.le b = true) {v : Tm} (hv : a.mem v = true) :
    b.mem v = true := by
  simp only [ElemPred.le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  cases v <;> simp_all [ElemPred.mem] <;> omega

theorem ElemsAt.mono {R R' : ElemPred} {r : Tm} {h : Heap} (hle : R.le R' = true) (he : ElemsAt R r h) :
    ElemsAt R' r h := by
  obtain ⟨s, ls, hs, hl, hall⟩ := he
  exact ⟨s, ls, hs, hl, fun l hm => let ⟨v, hv, hr⟩ := hall l hm; ⟨v, hv, ElemPred.le_sound hle hr⟩⟩

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
a typed array's element write may (`ElementWrite.Holds`). -/
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
  (`ElementWrite.Holds`). -/
  elementWrite : Option ElementWrite := none
  /-- The argument store regions of the frame (`Effect.frame`): the store
  each selects at the call's entry, read from a call position through a
  path of own data fields, may change arbitrarily (`"x.f[*]": "any"`). -/
  regions : List Footprints.ArgumentStoreRegion := []
  deriving Repr, DecidableEq

/-- The closed bound the frame implies, for conservative checks
(`Effect.within_holds`): the closed bound, or `top` where the frame states
store regions, whose selected locations may change whatever they hold. -/
def Effect.footprint (e : Effect) : Footprints.Closed :=
  if e.regions.isEmpty then e.closed else .top

theorem Effect.footprint_of_regions {e : Effect} (h : e.regions = []) : e.footprint = e.closed := by
  simp [Effect.footprint, h]

/-- A signature with a footprint and no promise. -/
def Effect.ofFootprint (c : Footprints.Closed) : Effect := ⟨c, none, false, false, false, false, false, none, none, [], [], false, none, []⟩

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
  (∀ R, e.requires = some R → ElemsAt R r h) ∧ ∀ F ∈ e.pre, F.HoldsAt ⟨callEnv r args, h⟩ (callEnv r args) h

theorem Effect.requires_none {e : Effect} (h : e.requires = none) (hp : e.pre = []) (r : Tm) (args : List Tm)
    (heap : Heap) : e.Requires r args heap :=
  ⟨fun R hR => (by rw [h] at hR; cases hR), fun F hF => (by rw [hp] at hF; cases hF)⟩

/-- **An exact write's precondition gives the range of its value**: where an
effect's precondition states each fact of `ElementKind.preFacts` (as the
effect decoder requires of an exact element write), a call meeting it has a
value (the third actual) its element type takes, so the exact write's
statement (`ExactWrite`) is the host's conversion of that value. -/
theorem ElementKind.takes_of_requires {e : Effect} {k : ElementKind}
    (hpre : ∀ F ∈ k.preFacts, F ∈ e.pre) {r : Tm} {args : List Tm} {heap : Heap}
    (hq : e.Requires r args heap) : k.Takes (args.getD 2 .undef) := by
  have hf : ∀ F ∈ k.preFacts, F.HoldsAt ⟨callEnv r args, heap⟩ (callEnv r args) heap :=
    fun F hF => hq.2 F (hpre F hF)
  have h3 : callEnv r args 3 = args.getD 2 .undef := rfl
  have hint := hf (.int 3) (by simp [ElementKind.preFacts])
  simp only [HeapKnowledge.IndexFact.HoldsAt, h3] at hint
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hint
  obtain ⟨b, hb, hs⟩ := HeapKnowledge.intValue_safe hi
  refine ⟨b, i, hb, hs, fun lo hi' hr => ?_⟩
  have hlo := hf (.linear (.le [(.value 3, -1)] (-lo))) (by simp [ElementKind.preFacts, hr])
  have hhi := hf (.linear (.le [(.value 3, 1)] hi')) (by simp [ElementKind.preFacts, hr])
  simp only [HeapKnowledge.IndexFact.HoldsAt, Linear.Fact.Holds, Linear.Form.eval,
    HeapKnowledge.termValuation, HeapKnowledge.termValue_value, h3, hi, Option.getD_some] at hlo hhi
  omega

/-- **An exact write's precondition gives the facts `ExactPre` states**:
the value is one its element type takes (`ElementKind.takes_of_requires`),
and the index a safe integer at least `0` and below the typed array's
length. -/
theorem ElementKind.exactPre_of_requires {e : Effect} {k : ElementKind}
    (hpre : ∀ F ∈ k.preFacts, F ∈ e.pre) {r : Tm} {args : List Tm} {heap : Heap}
    (hq : e.Requires r args heap) : ExactPre k args := by
  have hf : ∀ F ∈ k.preFacts, F.HoldsAt ⟨callEnv r args, heap⟩ (callEnv r args) heap :=
    fun F hF => hq.2 F (hpre F hF)
  have h1 : callEnv r args 1 = args.getD 0 .undef := rfl
  have h2 : callEnv r args 2 = args.getD 1 .undef := rfl
  have hint := hf (.int 2) (by simp [ElementKind.preFacts])
  simp only [HeapKnowledge.IndexFact.HoldsAt, h2] at hint
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hint
  obtain ⟨b, hb, hs⟩ := HeapKnowledge.intValue_safe hi
  have hlo := hf (.linear (.le [(.value 2, -1)] 0)) (by simp [ElementKind.preFacts])
  have hhi := hf (.linear (.le [(.value 2, 1), (.now .view 1 [], -1)] (-1))) (by simp [ElementKind.preFacts])
  obtain ⟨hdef, hhi⟩ := hhi
  obtain ⟨N, hN⟩ := Option.isSome_iff_exists.mp (hdef (.now .view 1 []) (by simp [Linear.Fact.vars]))
  simp only [HeapKnowledge.IndexFact.HoldsAt, Linear.Fact.Holds, Linear.Form.eval,
    HeapKnowledge.termValuation, HeapKnowledge.termValue_value, h2, hi, Option.getD_some] at hlo hhi
  rw [hN] at hhi
  simp only [Option.getD_some] at hhi
  have hN' : HeapKnowledge.viewLengthOf (args.getD 0 .undef) = some N := by
    simpa [HeapKnowledge.termValue_nil, HeapKnowledge.kindValue, h1] using hN
  have hk : k.Takes (args.getD 2 .undef) := ElementKind.takes_of_requires hpre hq
  refine ⟨hk, b, i.toNat, N, hb, ?_, hN', by omega⟩
  rw [show ((i.toNat : Nat) : Int) = i by omega]; exact hs

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
def Effect.ownChange (e : Effect) : Footprints.Closed := ⟨.any, e.footprint.array, e.footprint.view⟩

theorem Effect.le_ownChange (e : Effect) : e.footprint.le e.ownChange = true := by
  unfold Effect.ownChange
  generalize e.footprint = c
  rcases c with ⟨v, s, w⟩
  cases v <;> cases s <;> cases w <;> rfl

/-- The receiver's own change on contents: a store's as the coarse bound's, a
value's arbitrary. -/
theorem Effect.ownChange_at (e : Effect) (v : Val) :
    e.ownChange.at v = if Footprints.isArr v then e.footprint.at v else .any := by
  cases v <;> rfl

/-- A change from `before` to `after` that alters no old location but the
receiver `r`'s store, which, where it changes, held a store and holds one
extending it, its old elements at their indices, at most `2^32 - 1` long:
`Array.prototype.push` on an ordinary array (SOURCE-CONTRACTS.md, "Native
footprints"). -/
def ReceiverGrows (r : Tm) (before after : Heap) : Prop :=
  ∀ l v, before[l]? = some v → after[l]? = some v ∨
    (Footprints.storeOf r = some l ∧ ∃ ls ls', v = .arr ls ∧ after[l]? = some (.arr ls') ∧
      ls <+: ls' ∧ ls'.length ≤ maxArrayLength)

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
  if e.receiverOwn then [(.inCls ((.own 0)) .values, .any)]
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
    (∀ F ∈ e.ensures, F.HoldsAt ⟨callEnv r args, before⟩ (ensuresEnv v r args) after) ∧
    (e.receiverGrows = true → ReceiverGrows r before after ∧ ReceiverAppends r args before after) ∧
    (∀ w, e.elementWrite = some w → w.Holds args before after)

/-- A signature's postcondition on a throw, from the heap the call starts in:
its frame at the call's actuals where it states `onThrow`, and nothing
otherwise. -/
def Effect.excPost (e : Effect) (r : Tm) (args : List Tm) (before : Heap) : Heap → Prop := fun after =>
  e.onThrow = true → e.within r args before after

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
  rw [Footprints.Closed.fp_entry_at hx hm hv]
  unfold Effect.footprint
  split
  · exact change_le_refl _
  · rw [Footprints.Closed.at_top]; exact change_le_any _

/-- A region entry covers its location at `any`, which the coarse bound
allows. -/
private theorem region_entry_le {e : Effect} {r : Footprints.ArgumentStoreRegion}
    (hr : r ∈ e.regions) {v : Val} : (regionEntry r).2.le (e.footprint.at v) = true := by
  have hne : e.regions.isEmpty = false := by
    cases hq : e.regions with
    | nil => rw [hq] at hr; cases hr
    | cons _ _ => rfl
  simp only [Effect.footprint, hne, Bool.false_eq_true, if_false, Footprints.Closed.at_top]
  rfl

theorem Effect.mem_frame {e : Effect} {x : Footprints.Region × Footprints.Change} (hx : x ∈ e.frame) :
    x ∈ e.closed.fp ∨ x ∈ e.receiverEntries ∨ ∃ r ∈ e.regions, x = regionEntry r := by
  simp only [Effect.frame, List.mem_append, List.mem_map] at hx
  rcases hx with (hx | hx) | ⟨r, hr, rfl⟩
  · exact .inl hx
  · exact .inr (.inl hx)
  · exact .inr (.inr ⟨r, hr, rfl⟩)

/-- **The frame outside the receiver's entries**: every old location no
receiver entry covers changes within the coarse bound `footprint`. -/
theorem Effect.within_outside {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) {P : Nat → Prop}
    (hrecv : ∀ x ∈ e.receiverEntries, ∀ l, P l → x.1.mem (callEnv r args) before l = false) :
    e.footprint.HoldsOn P before after :=
  post_closedOn h fun x hx l v hP hm hv => by
    rcases Effect.mem_frame hx with hx | hx | ⟨q, hq, rfl⟩
    · exact closed_entry_le hx hm hv
    · rw [hrecv x hx l hP] at hm; cases hm
    · exact region_entry_le hq

/-- With `receiverOwn`, the frame bounds every old location but the
receiver's own by the coarse bound. -/
theorem Effect.within_outside_own {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) (ho : e.receiverOwn = true) :
    e.footprint.HoldsOn (fun l => l ∉ Footprints.ownOf r) before after := by
  have h0 : callEnv r args 0 = r := rfl
  refine Effect.within_outside h fun x hx l hl => ?_
  simp only [Effect.receiverEntries, ho, if_true, List.mem_singleton] at hx
  subst hx
  simp only [Footprints.Region.mem, h0, Bool.and_eq_false_iff]
  left
  simpa [List.contains_iff_mem, Footprints.ownOf] using hl

/-- With `receiverOwn`, the frame bounds the receiver's own locations by
`ownChange`. -/
theorem Effect.within_inside_own {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) (ho : e.receiverOwn = true) :
    e.ownChange.HoldsOn (fun l => l ∈ Footprints.ownOf r) before after := by
  refine post_closedOn h fun x hx l v hP hm hv => ?_
  rw [Effect.ownChange_at]
  rcases Effect.mem_frame hx with hx | hx | ⟨q, hq, rfl⟩
  · split
    · exact closed_entry_le hx hm hv
    · exact change_le_any _
  · split <;> simp only [Effect.receiverEntries, ho, if_true, List.mem_singleton] at hx <;>
      subst hx <;> simp_all [Footprints.Region.mem, change_le_any]
  · split
    · exact region_entry_le hq
    · exact change_le_any _

/-- With `receiverStore` and no `receiverOwn`, the frame bounds every old
location but the receiver's store by the coarse bound. -/
theorem Effect.within_outside_store {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) (ho : e.receiverOwn = false) :
    e.footprint.HoldsOn (fun l => (Footprints.fieldsOf r).lookup arrayStoreKey ≠ some l) before after := by
  have h0 : callEnv r args 0 = r := rfl
  refine Effect.within_outside h fun x hx l hl => ?_
  cases hs : e.receiverStore
  · simp [Effect.receiverEntries, ho, hs] at hx
  · simp only [Effect.receiverEntries, ho, hs, if_true, Bool.false_eq_true, if_false, List.mem_singleton] at hx
    subst hx
    simp only [Footprints.Region.mem, h0]
    simpa using hl

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

/-- **The frame of a signature stating `receiverOwn` and no store regions**,
from its coarse bound outside the receiver's own locations and `ownChange`
on them. -/
theorem Effect.within_of_own {e : Effect} (hreg : e.regions = []) (ho : e.receiverOwn = true)
    {r : Tm} {args : List Tm} {before after : Heap}
    (hout : e.footprint.HoldsOn (fun l => l ∉ Footprints.ownOf r) before after)
    (hin : e.ownChange.HoldsOn (fun l => l ∈ Footprints.ownOf r) before after) :
    e.within r args before after := by
  have hfp : e.footprint = e.closed := Effect.footprint_of_regions hreg
  have h0 : callEnv r args 0 = r := rfl
  unfold Effect.within Effect.frame Effect.receiverEntries
  simp only [hreg, List.map_nil, List.append_nil, ho, if_true]
  rw [← hfp, Footprints.Closed.post_extra_any]
  refine ⟨hout.1, fun l v hl hv => ?_⟩
  by_cases hown : l ∈ Footprints.ownOf r
  · obtain ⟨v', hv', hc⟩ := hin.2 l v hown hv
    have hmem : (Footprints.Region.inCls (.own 0) .values).mem (callEnv r args) before l =
        (((Footprints.ownOf r).contains l) && match before[l]? with
          | some v => Footprints.Selector.values.selects v
          | none => false) := rfl
    have ha : Footprints.isArr v = true := by
      replace hl : (Footprints.Region.inCls (.own 0) .values).mem (callEnv r args) before l = false := hl
      rw [hmem, hv] at hl
      simpa [List.contains_iff_mem, hown] using hl
    refine ⟨v', hv', ?_⟩
    rwa [Effect.ownChange_at, ha, if_pos rfl] at hc
  · exact hout.2 l v hown hv

/-- **The frame of a signature stating `receiverStore`, no `receiverOwn` and
no store regions**, from its coarse bound outside the receiver's store. -/
theorem Effect.within_of_store {e : Effect} (hreg : e.regions = []) (ho : e.receiverOwn = false)
    (hs : e.receiverStore = true) {r : Tm} {args : List Tm} {before after : Heap}
    (hout : e.footprint.HoldsOn (fun l => (Footprints.fieldsOf r).lookup arrayStoreKey ≠ some l) before after) :
    e.within r args before after := by
  have hfp : e.footprint = e.closed := Effect.footprint_of_regions hreg
  have h0 : callEnv r args 0 = r := rfl
  unfold Effect.within Effect.frame Effect.receiverEntries
  simp only [hreg, List.map_nil, List.append_nil, ho, hs, Bool.false_eq_true, if_false, if_true]
  rw [← hfp, Footprints.Closed.post_extra_any]
  refine (Footprints.Closed.HoldsOn.congr ?_).mp hout
  intro l
  simp [Footprints.Region.mem, h0]

theorem Effect.within_own {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) (ho : e.receiverOwn = true) : e.ownChange.Holds before after := by
  have hout := (Effect.within_outside_own h ho).mono e.le_ownChange
  have hin := Effect.within_inside_own h ho
  refine Footprints.Closed.holds_of_on ⟨hout.1, fun l v _ hv => ?_⟩
  by_cases hm : l ∈ Footprints.ownOf r
  · exact hin.2 l v hm hv
  · exact hout.2 l v hm hv

/-- What a footprint on the locations below `b` follows from: the footprint
anywhere, or on every location but a store, or every own location of an
object, allocated after `b`. -/
theorem Effect.within_below {e : Effect} {r : Tm} {args : List Tm} {b : Nat} {before after : Heap}
    (h : e.within r args before after) (hr : e.receiverStore = true → Footprints.FreshAt b r)
    (ho : e.receiverOwn = true → Footprints.FreshObjectAt b r) :
    e.footprint.HoldsOn (· < b) before after := by
  cases hown : e.receiverOwn
  · cases hs : e.receiverStore
    · exact Effect.within_outside h (P := (· < b)) fun x hx => by simp [Effect.receiverEntries, hown, hs] at hx
    · exact (Effect.within_outside_store h hown).below_fresh (hr hs)
  · exact (Effect.within_outside_own h hown).below_fresh_object (ho hown)

theorem Effect.within_holds {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) (hr : e.receiverStore = false) (ho : e.receiverOwn = false) :
    e.footprint.Holds before after :=
  Footprints.Closed.holds_of_on (Effect.within_outside h fun x hx => by
    simp [Effect.receiverEntries, hr, ho] at hx)

theorem Effect.within_top {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) : Footprints.Closed.top.Holds before after :=
  Footprints.Closed.holds_top.mpr h.1

/-- A coarse bound below another's gives the receiver's own change below. -/
theorem Effect.ownChange_le {a b : Effect} (hle : a.footprint.le b.footprint = true) :
    a.ownChange.le b.ownChange = true := by
  simp only [Footprints.Closed.le, Bool.and_eq_true] at hle
  simp only [Effect.ownChange, Footprints.Closed.le, Bool.and_eq_true]
  exact ⟨⟨rfl, hle.1.2⟩, hle.2⟩

/-- **A frame read through its coarse bound**: a signature with no store
regions, the same receiver modes and a coarse bound at least as large
bounds the same transition, at any actuals. -/
theorem Effect.within_coarse {e e' : Effect} (hreg : e'.regions = [])
    (hle : e.footprint.le e'.footprint = true) (hs : e'.receiverStore = e.receiverStore)
    (ho : e'.receiverOwn = e.receiverOwn) {r : Tm} {args args' : List Tm} {before after : Heap}
    (h : e.within r args before after) : e'.within r args' before after := by
  cases hown : e.receiverOwn
  · cases hst : e.receiverStore
    · exact Effect.within_of_footprint hreg ((Effect.within_holds h hst hown).mono hle)
    · exact Effect.within_of_store hreg (ho.trans hown) (hs.trans hst)
        ((Effect.within_outside_store h hown).mono hle)
  · exact Effect.within_of_own hreg (ho.trans hown) ((Effect.within_outside_own h hown).mono hle)
      ((Effect.within_inside_own h hown).mono (Effect.ownChange_le hle))

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
promise, and each position its precondition `pre` names, read at the
callee's entry, where `old(t)` is `t` (`IndexFact.toNow`). Code states no
postcondition: a fact over a parameter needs its entry value, which a
reassigned parameter no longer holds; and no append, which a native's
audited signature alone states. -/
def Effect.below (n : Nat) (e : Effect) : Bool :=
  e.promiseBelow n && e.pre.all (fun F => F.toNow.slots.all (· ≤ n)) && e.ensures.isEmpty &&
    !e.receiverGrows && e.elementWrite.isNone && e.regions.isEmpty

theorem Effect.below_promise {e : Effect} {n : Nat} (h : e.below n = true) : e.promiseBelow n = true := by
  simp only [Effect.below, Bool.and_eq_true] at h; exact h.1.1.1.1.1

theorem Effect.below_pre {e : Effect} {n : Nat} (h : e.below n = true) :
    ∀ F ∈ e.pre, ∀ s ∈ F.toNow.slots, s ≤ n := by
  simp only [Effect.below, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun F hF => h.1.1.1.1.2 F hF

/-- **A precondition is one-state**: read at the callee's entry, where the
current state is the entry state, a fact holds exactly where its
restatement with each `old(t)` as `t` does (`IndexFact.holdsAt_toNow`), at
any entry state (`IndexFact.entrySlots_toNow`). -/
theorem Effect.pre_toNow {F : HeapKnowledge.IndexFact} (ε : HeapKnowledge.EntryState) (ρ : Env) (heap : Heap) :
    F.HoldsAt ⟨ρ, heap⟩ ρ heap ↔ F.toNow.HoldsAt ε ρ heap :=
  (HeapKnowledge.IndexFact.holdsAt_toNow rfl rfl).symm.trans
    (HeapKnowledge.IndexFact.holdsAt_entry (HeapKnowledge.IndexFact.entrySlots_toNow F) _)

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
  Effect.within_coarse hreg (Footprints.Closed.le_refl _) rfl rfl h

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

/-- Code binding `n` parameters holds the call's position `s ≤ n` at its
frame's slot `s`: the receiver, then each actual it binds. -/
theorem callEnv_frame {n s : Nat} (hle : s ≤ n) (r : Tm) (args vs : List Tm) (d : Tm) :
    callEnv r args s = envOf (r :: CallArguments.parameters n args ++ vs) d s := by
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

/-- Actuals past position `m` do not change the call's positions up to `m`. -/
theorem callEnv_take {m s : Nat} (hle : s ≤ m) (r : Tm) (args : List Tm) :
    callEnv r (args.take m) s = callEnv r args s := by
  simp only [callEnv]
  cases s with
  | zero => simp
  | succ i =>
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [if_pos (by omega)]

/-- Code binding `n` parameters reads the precondition's positions in its
frame as the call passed them: the receiver, then each actual it binds. -/
theorem Effect.pre_frame {e : Effect} {n : Nat} (h : e.below n = true) {F : HeapKnowledge.IndexFact}
    (hF : F ∈ e.pre) (r : Tm) (args vs : List Tm) (d : Tm) (heap : Heap) :
    F.HoldsAt ⟨callEnv r args, heap⟩ (callEnv r args) heap ↔
      F.HoldsAt ⟨envOf (r :: CallArguments.parameters n args ++ vs) d, heap⟩
        (envOf (r :: CallArguments.parameters n args ++ vs) d) heap := by
  refine (Effect.pre_toNow ⟨callEnv r args, heap⟩ _ heap).trans (Iff.trans ?_ (Effect.pre_toNow ⟨callEnv r args, heap⟩ _ heap).symm)
  exact HeapKnowledge.IndexFact.holdsAt_congr fun s hs => callEnv_frame (Effect.below_pre h F hF s hs) r args vs d

/-- Actuals past those code binds do not change what its precondition reads. -/
theorem Effect.pre_take {e : Effect} {n m : Nat} (h : e.below n = true) (hm : n ≤ m) {F : HeapKnowledge.IndexFact}
    (hF : F ∈ e.pre) (r : Tm) (args : List Tm) (heap : Heap) :
    F.HoldsAt ⟨callEnv r (args.take m), heap⟩ (callEnv r (args.take m)) heap ↔
      F.HoldsAt ⟨callEnv r args, heap⟩ (callEnv r args) heap := by
  refine (Effect.pre_toNow ⟨callEnv r args, heap⟩ _ heap).trans (Iff.trans ?_ (Effect.pre_toNow ⟨callEnv r args, heap⟩ _ heap).symm)
  exact HeapKnowledge.IndexFact.holdsAt_congr fun s hs => callEnv_take (by have := Effect.below_pre h F hF s hs; omega) r args

/-- **What a module function's code realizes at arity `n`**: its effect
below `n` (`below`) but for its postcondition, each fact of which names the
result (position `0`), the receiver (`1`) and the first `n` parameters only.
A unit request states its postcondition at its entry frame
(`PassUnit.EnsuresClause`), so a reassigned parameter does not change what
it reads. -/
def Effect.belowRow (n : Nat) (e : Effect) : Bool :=
  ({ e with ensures := [] } : Effect).below n &&
    e.ensures.all (fun F => F.slots.all (· ≤ n + 1) && F.entrySlots.all (· ≤ n))

theorem Effect.belowRow_below {e : Effect} {n : Nat} (h : e.belowRow n = true) :
    ({ e with ensures := [] } : Effect).below n = true := by
  simp only [Effect.belowRow, Bool.and_eq_true] at h; exact h.1

theorem Effect.belowRow_ensures {e : Effect} {n : Nat} (h : e.belowRow n = true) :
    ∀ F ∈ e.ensures, ∀ s ∈ F.slots, s ≤ n + 1 := by
  simp only [Effect.belowRow, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun F hF => (h.2 F hF).1

/-- A module function's postcondition reads the entry at the receiver and
the first `n` parameters only. -/
theorem Effect.belowRow_ensures_entry {e : Effect} {n : Nat} (h : e.belowRow n = true) :
    ∀ F ∈ e.ensures, ∀ s ∈ F.entrySlots, s ≤ n := by
  simp only [Effect.belowRow, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun F hF => (h.2 F hF).2

/-- An effect below `n` is one a module function's code realizes. -/
theorem Effect.belowRow_of_below {e : Effect} {n : Nat} (h : e.below n = true) : e.belowRow n = true := by
  have he := Effect.below_ensures h
  have h' : ({ e with ensures := [] } : Effect) = e := by cases e; simp_all
  simp [Effect.belowRow, h', h, he]

/-- Actuals past those code binds do not change what its postcondition
reads. -/
theorem Effect.ensures_take {e : Effect} {n m : Nat} (h : e.belowRow n = true) (hm : n ≤ m)
    {F : HeapKnowledge.IndexFact} (hF : F ∈ e.ensures) (v r : Tm) (args : List Tm) (before heap : Heap) :
    F.HoldsAt ⟨callEnv r (args.take m), before⟩ (ensuresEnv v r (args.take m)) heap ↔
      F.HoldsAt ⟨callEnv r args, before⟩ (ensuresEnv v r args) heap := by
  refine (HeapKnowledge.IndexFact.holdsAt_congr_entry (ε := ⟨callEnv r (args.take m), before⟩) (ε' := ⟨callEnv r args, before⟩) rfl fun s hs =>
    callEnv_take (by have := Effect.belowRow_ensures_entry h F hF s hs; omega) r args).trans
    (HeapKnowledge.IndexFact.holdsAt_congr fun s hs => ?_)
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
    (hF : F ∈ e.ensures) (v r : Tm) (args vs : List Tm) (d : Tm) (before heap : Heap) :
    F.HoldsAt ⟨callEnv r args, before⟩ (ensuresEnv v r args) heap ↔
      F.HoldsAt ⟨envOf (r :: CallArguments.parameters n args ++ vs) d, before⟩
        (push v (envOf (r :: CallArguments.parameters n args ++ vs) d)) heap := by
  refine (HeapKnowledge.IndexFact.holdsAt_congr_entry (ε := ⟨callEnv r args, before⟩)
    (ε' := ⟨envOf (r :: CallArguments.parameters n args ++ vs) d, before⟩) rfl fun s hs =>
    callEnv_frame (Effect.belowRow_ensures_entry h F hF s hs) r args vs d).trans
    (HeapKnowledge.IndexFact.holdsAt_congr fun s hs => ?_)
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
    fun F hF => (Effect.ensures_take h hm hF v r args before after).mp (hp.2.2.2.2.1 F hF),
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
  Effect.within_coarse (e := e) (e' := e.forgetEnsures) rfl (by simp [Effect.forgetEnsures, Effect.footprint]; exact Footprints.Closed.le_refl _) rfl rfl h

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
    obtain ⟨hc, hx, ha⟩ := h.2.2.2.2.2.2 w hw
    have hg : ∀ i, (args ++ pad).getD i .undef = args.getD i .undef := fun i => by
      simpa [callEnv] using congrFun (callEnv_pad r args hpad) (i + 1)
    refine ⟨hc, fun k he => ?_, fun he => ?_⟩
    · have := hx k he
      simp only [ExactWrite, WriteAt, ExactPre, hg] at this ⊢
      exact this
    · have := ha he
      simp only [ViewAssign, WriteAt, hg] at this ⊢
      exact this
  have hw := h.1
  unfold Effect.within at hw
  rw [callEnv_pad r args hpad] at hw
  refine ⟨hw, h.2.1, h.2.2.1, h.2.2.2.1, fun F hF => ?_,
    fun hg => ⟨(h.2.2.2.2.2.1 hg).1, ReceiverAppends.of_no_store hr⟩, hwr⟩
  have := h.2.2.2.2.1 F hF
  have he : ensuresEnv v r (args ++ pad) = ensuresEnv v r args := by
    funext i; simp only [ensuresEnv, callEnv_pad r args hpad]
  rwa [he, callEnv_pad r args hpad] at this

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
  · obtain ⟨S, hS⟩ := Footprints.Closed.fp_entry_cls hx
    rw [hS] at hm ⊢
    simpa only [Footprints.Region.mem, hgl] using hm
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

/-- **Agreement of the entry across allocation**: each entry term of a
signature's postcondition denotes, at the call's positions, at the heap
before an allocation what it denotes after it. The call's entry state is
the heap before the allocation; this is what reading the post at the later
heap needs to state it there. -/
def Effect.EntryAgrees (e : Effect) (ρ : Env) (before middle : Heap) : Prop :=
  ∀ F ∈ e.ensures, ∀ t ∈ F.entryTerms, HeapKnowledge.termAt ρ middle t = HeapKnowledge.termAt ρ before t

/-- A signature stating no postcondition agrees across any allocation. -/
theorem Effect.entryAgrees_of_nil {e : Effect} (h : e.ensures = []) (ρ : Env) (before middle : Heap) :
    e.EntryAgrees ρ before middle := by
  intro F hF; rw [h] at hF; cases hF

/-- Fresh entry allocation composes with the body's frame, where the frame's
paths and the postcondition's entry terms agree across it: the post read at
the call's entry, the heap before the allocation. -/
theorem Effect.post_prefix (effect : Effect) {r : Tm} {args : List Tm} {before middle after : Heap} {v : Val}
    (hprefix : before.IsPrefix middle) (hagree : effect.PrefixAgrees (callEnv r args) before middle)
    (hens : effect.EntryAgrees (callEnv r args) before middle) :
    effect.post r args middle after v → effect.post r args before after v := by
  rintro ⟨hw, hf, ho, hel, hen, hg, hew⟩
  exact ⟨Effect.within_prefix hprefix hagree hw, fun h => (hf h).lower hprefix.length_le,
    fun h => (ho h).lower hprefix.length_le, hel,
    fun F hF => (HeapKnowledge.IndexFact.holdsAt_congr_entryTerms (hens F hF)).mp (hen F hF),
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

theorem Effect.within_meet {a b : Effect} (hs : a.sameResult b = true) {r : Tm} {args : List Tm} {before after : Heap} :
    (a.meet b).within r args before after ↔ a.within r args before after ∧ b.within r args before after := by
  simp only [Effect.sameResult, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.isEmpty_iff,
    Bool.not_eq_true'] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hst⟩, how⟩, _⟩, _⟩, _⟩, _⟩, hreg, hmode⟩ := hs
  have hfp := Effect.footprint_meet (a := a) (b := b) hreg.symm
  have hmr : (a.meet b).regions = a.regions := rfl
  rcases hmode with hnil | ⟨hs0, ho0⟩
  · have hmreg : (a.meet b).regions = [] := by rw [hmr, hnil]
    have hbreg : b.regions = [] := by rw [← hreg, hnil]
    have hms : (a.meet b).receiverStore = a.receiverStore := rfl
    have hmo : (a.meet b).receiverOwn = a.receiverOwn := rfl
    have hown : (a.meet b).ownChange = a.ownChange.meet b.ownChange := by
      simp only [Effect.ownChange, hfp, Footprints.Closed.meet, change_min_any]
    constructor
    · intro hm
      refine ⟨Effect.within_coarse hnil (by rw [hfp]; exact Footprints.Closed.meet_le_left _ _) hms.symm hmo.symm hm,
        Effect.within_coarse hbreg (by rw [hfp]; exact Footprints.Closed.meet_le_right _ _)
          (hst.symm.trans hms.symm) (how.symm.trans hmo.symm) hm⟩
    · rintro ⟨ha, hb⟩
      cases hao : a.receiverOwn
      · have hbo : b.receiverOwn = false := how.symm.trans hao
        cases has : a.receiverStore
        · have hbs : b.receiverStore = false := hst.symm.trans has
          refine Effect.within_of_footprint hmreg ?_
          rw [hfp]
          exact Footprints.Closed.holds_meet.mpr ⟨Effect.within_holds ha has hao, Effect.within_holds hb hbs hbo⟩
        · refine Effect.within_of_store hmreg (hmo.trans hao) (hms.trans has) ?_
          rw [hfp]
          exact Footprints.Closed.holdsOn_meet.mpr ⟨Effect.within_outside_store ha hao,
            Effect.within_outside_store hb hbo⟩
      · have hbo : b.receiverOwn = true := how.symm.trans hao
        refine Effect.within_of_own hmreg (hmo.trans hao) ?_ ?_
        · rw [hfp]
          exact Footprints.Closed.holdsOn_meet.mpr ⟨Effect.within_outside_own ha hao,
            Effect.within_outside_own hb hbo⟩
        · rw [hown]
          exact Footprints.Closed.holdsOn_meet.mpr ⟨Effect.within_inside_own ha hao,
            Effect.within_inside_own hb hbo⟩
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

/-- **The view write a signature states**, from the call's entry world `U`
and heap `before` to its exit world and heap: where it states an element
write, the kinded view-element write of it at the actuals
(`Kinds.ViewWriteOf`), read at the entry world's roles; where exact, the
result of an element assignment, exact or not, is the value written, the
value an assignment `b[i] = v` is. -/
def Effect.viewPost (e : Effect) (args : List Tm) {j : Nat} (U : WorldT j) (before : Heap) : WPost :=
  fun _ W' after r => ∀ w, e.elementWrite = some w → Kinds.ViewWriteOf w args U before W' after ∧
    (w ≠ .stores → r = args.getD 2 .undef)

/-- **A signature's normal-return postcondition**, given the call's entry
world `U` and heap `before`: at the exit world and heap, its heap
postcondition (`Effect.post`) and its view write (`Effect.viewPost`). -/
def Effect.postW (e : Effect) (r : Tm) (args : List Tm) {j : Nat} (U : WorldT j) (before : Heap) : WPost :=
  fun k W' after v => e.post r args before after v ∧ e.viewPost args U before k W' after v

/-- A signature's throw postcondition as a world-indexed one: its heap
postcondition (`Effect.excPost`) lifted. -/
abbrev Effect.excPostW (e : Effect) (r : Tm) (args : List Tm) (before : Heap) : HeapObservations.WExc :=
  HeapObservations.WExc.lift (e.excPost r args before)

/-- **A signature stating no element write**: its postcondition is its heap
postcondition, at every entry and exit world. -/
theorem Effect.postW_of_post {e : Effect} (hx : e.elementWrite = none) {r : Tm} {args : List Tm} {j : Nat}
    {U : WorldT j} {before : Heap} {k : Nat} {W' : WorldT k} {after : Heap} {v : Val}
    (h : e.post r args before after v) : e.postW r args U before k W' after v :=
  ⟨h, fun w hw => by rw [hx] at hw; cases hw⟩

/-- **The meet's postcondition** is the first signature's, view write
included, and the second's heap postcondition: the two state the same
element write (`Effect.sameResult`). -/
theorem Effect.postW_meet {a b : Effect} (hs : a.sameResult b = true) (r : Tm) (args : List Tm) {j : Nat}
    (U : WorldT j) (before : Heap) (k : Nat) (W' : WorldT k) (after : Heap) (v : Val) :
    (a.meet b).postW r args U before k W' after v ↔ a.postW r args U before k W' after v ∧ b.post r args before after v := by
  simp only [Effect.postW, Effect.viewPost]
  rw [Effect.post_meet hs]
  exact ⟨fun ⟨⟨ha, hb⟩, hw⟩ => ⟨⟨ha, hw⟩, hb⟩, fun ⟨⟨ha, hw⟩, hb⟩ => ⟨⟨ha, hb⟩, hw⟩⟩

/-- **Prefix transport of a signature's postcondition**: allocation between
the call's entry and the start of its body composes with the postcondition,
where the frame's paths and the entry terms agree across it
(`Effect.post_prefix`), and the view write holds from the entry
(`Kinds.ViewWrite.prefix_left`). -/
theorem Effect.postW_prefix (e : Effect) {r : Tm} {args : List Tm} {n m : Nat} {W : WorldT n} {M : WorldT m}
    {h hm : Heap} (hle : m ≤ n) (hx : WExt (trunc m hle W) M) (hok : HeapOk n W h) (hp : h.IsPrefix hm)
    (hagree : e.PrefixAgrees (callEnv r args) h hm) (hens : e.EntryAgrees (callEnv r args) h hm)
    {k : Nat} {W' : WorldT k} {h' : Heap} {v : Val} (hpost : e.postW r args M hm k W' h' v) :
    e.postW r args W h k W' h' v :=
  ⟨e.post_prefix hp hagree hens hpost.1, fun w hw =>
    ⟨⟨(hpost.2 w hw).1.1.prefix_left hle hx hok hp, fun k hk =>
      ⟨((hpost.2 w hw).1.2.1 k hk).1.prefix_left hp, ((hpost.2 w hw).1.2.1 k hk).2⟩,
      fun ha => ((hpost.2 w hw).1.2.2 ha).prefix_left hp⟩, (hpost.2 w hw).2⟩⟩

/-- **Safety at a signature stating no element write** is safety at its
postcondition over kinded worlds, from every entry world. -/
theorem Effect.safe_postW {e : Effect} (hx : e.elementWrite = none) {Ξ T : Fam} {r : Tm} {args : List Tm}
    {j : Nat} {U : WorldT j} {heap : Heap} {n : Nat} {W : WorldT n} {h : Heap} {t : Tm}
    (hs : SafePostExc Ξ T (e.post r args heap) (e.excPost r args heap) n W h t) :
    SafePostExcV Ξ T (e.postW r args U heap) (e.excPostW r args heap).liftV n W h t :=
  SafePostExcV.iff_lift.mpr (SafePostExcW.weaken (fun _ _ _ _ hp => Effect.postW_of_post hx hp) (fun _ _ _ hp => hp) hs)

/-- A call's normal postcondition: given the receiver, the actuals, and the
entry budget, world and heap, a world-indexed postcondition of the exit. -/
abbrev CPost := Tm → List Tm → (j : Nat) → WorldT j → Heap → WPost

/-- A call's exceptional postcondition: given the receiver, the actuals, and
the entry budget, world and heap, a world-indexed postcondition of the
throwing configuration and the value it raises. -/
abbrev CExc := Tm → List Tm → (j : Nat) → WorldT j → Heap → HeapObservations.WExcV

/-- **The native-contract condition** of a callable value `v`, at budget `k`
and world `W`. From every well-formed entry configuration below `k` (a heap
meeting an admissible extension `U` of the truncated world, with the
references of the callee, the receiver and the actuals valid in `U`) that
meets the input contract (the receiver's type `Rc`, the actuals' `Acc`, the
precondition `requires`), the invocation is safe with world-indexed
postconditions: a normal result has the result type `R` and meets `post` at
its exit world, a throw raises a value of the exception family `Ξ` meeting
`excPost` with its exit world and heap, each given the entry world and heap, and every
configuration on the way is well-formed under one extension of `U`
(`NativeContract.run`). -/
def NativeContract (Ξ : Fam) (Acc : ArgFam) (Rc : Fam) (requires : Tm → List Tm → Heap → Prop)
    (R : Tm → List Tm → Fam) (post : CPost) (excPost : CExc) (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
    WorldAdm U → ∀ (heap : Heap), HeapOk j U heap → RefsOk U v →
      ∀ r, isVal r = true → Rc j U r → RefsOk U r →
      ∀ args, CallArguments.Values args → (∀ a ∈ args, RefsOk U a) → Acc j U args →
        requires r args heap →
        ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧
          SafePostExcV Ξ (R r args) (post r args j U heap) (excPost r args j U heap) j U heap result

/-- **A contract's every execution prefix is well-formed**: the configuration
`i` steps into the call meets one extension of the entry world truncated to
the budget left, in both parts of heap satisfaction and with valid
references. -/
theorem NativeContract.run {Ξ : Fam} {Acc : ArgFam} {Rc : Fam}
    {requires : Tm → List Tm → Heap → Prop} {R : Tm → List Tm → Fam} {post : CPost} {excPost : CExc}
    {k : Nat} {W : WorldT k} {v : Val} (hc : NativeContract Ξ Acc Rc requires R post excPost k W v)
    {j : Nat} (hj : j < k) {U : WorldT j} (hx : WExt (trunc j (Nat.le_of_lt hj) W) U) (hu : WorldAdm U)
    {heap : Heap} (hh : HeapOk j U heap) (hv : RefsOk U v) {r : Tm} (hr : isVal r = true)
    (hrc : Rc j U r) (hrr : RefsOk U r) {args : List Tm} (ha : CallArguments.Values args)
    (har : ∀ a ∈ args, RefsOk U a) (hacc : Acc j U args) (hreq : requires r args heap) :
    ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧
      ∀ {i : Nat} {h' : Heap} {t' : Tm}, Steps i heap result h' t' → i ≤ j →
        ∃ (m : Nat) (hm : m ≤ j) (U' : WorldT m), m + i = j ∧ WExt (trunc m hm U) U' ∧
          HeapOk m U' h' ∧ RefsOk U' t' := by
  obtain ⟨result, hi, hs⟩ := hc j hj U hx hu heap hh hv r hr hrc hrr args ha har hacc hreq
  refine ⟨result, hi, fun hst hle => ?_⟩
  have hs' := (SafePostExcV.iff_lift (R := fun _ _ _ => True)).mp
    (SafePostExcV.weaken (fun _ _ _ _ h => h) (fun _ _ _ _ _ => trivial) hs)
  obtain ⟨m, hm, U', hmi, hx', -, hh', hr', -⟩ := hs'.run hst hle hu hh
  exact ⟨m, hm, U', hmi, hx', hh', hr'⟩

/-- **The native-contract condition is closed downward**: at a lower budget
and an extension of the world truncated there. -/
theorem NativeContract.down {Ξ : Fam} {Acc : ArgFam} {Rc : Fam}
    {requires : Tm → List Tm → Heap → Prop} {R : Tm → List Tm → Fam} {post : CPost} {excPost : CExc}
    {k : Nat} {W : WorldT k} {v : Val} (hc : NativeContract Ξ Acc Rc requires R post excPost k W v)
    {j : Nat} (hj : j ≤ k) {U : WorldT j} (hx : WExt (trunc j hj W) U) :
    NativeContract Ξ Acc Rc requires R post excPost j U v := by
  intro i hi V hy hu heap hh hv r hrv hrc hrr args ha har hacc hreq
  refine hc i (by omega) V ?_ hu heap hh hv r hrv hrc hrr args ha har hacc hreq
  simpa only [trunc_trunc] using WExt_trans (WExt_trunc (Nat.le_of_lt hi) hx) hy

/-- **Invocation of a callee meeting the native-contract condition.** From a
well-formed configuration whose callee, receiver and actuals are valid and
meet the input contract at the world one step below, the invocation is safe
at the contract's result type and both its postconditions, read from the
entry world truncated by the invocation's step. -/
theorem NativeContract.safe {Ξ : Fam} {Acc : ArgFam} {Rc : Fam}
    {requires : Tm → List Tm → Heap → Prop} {R : Tm → List Tm → Fam} {post : CPost} {excPost : CExc}
    {n : Nat} {W : WorldT (n + 1)} {v : Val}
    (hc : NativeContract Ξ Acc Rc requires R post excPost (n + 1) W v) (hadm : WorldAdm W)
    {heap : Heap} (hh : HeapOk (n + 1) W heap) {r : Tm} (hrv : isVal r = true)
    (hrc : Rc n (trunc n (Nat.le_succ n) W) r) {args : List Tm}
    (ha : CallArguments.Values args) (hacc : Acc n (trunc n (Nat.le_succ n) W) args)
    (hreq : requires r args heap) (href : RefsOk W (.invoke v r args)) :
    SafePostExcV Ξ (R r args) (post r args n (trunc n (Nat.le_succ n) W) heap)
      (excPost r args n (trunc n (Nat.le_succ n) W) heap) (n + 1) W heap (.invoke v r args) := by
  obtain ⟨hv, hrr, har⟩ := RefsOk_invoke.mp href
  obtain ⟨result, hi, hs⟩ := hc n (Nat.lt_succ_self n) _ (WExt_refl _) (WorldAdm_trunc _ hadm) heap
    (HeapOk_trunc n W heap hh) (RefsOk_trunc _ hv) r hrv hrc (RefsOk_trunc _ hrr) args ha
    (fun a h => RefsOk_trunc _ (har a h)) hacc hreq
  exact ⟨href, .inr ⟨_, heap, result, WExt_refl _, WorldAdm_trunc _ hadm,
    hi.step heap, HeapOk_trunc n W heap hh, hs⟩⟩

/-- **The native-contract condition of construction**: from every
well-formed entry configuration meeting the input contract, `new` runs a
construction safe at the result type and both postconditions, the receiver
`undefined`. -/
def NativeConstruct (Ξ : Fam) (Acc : ArgFam) (requires : List Tm → Heap → Prop) (R : List Tm → Fam)
    (post : CPost) (excPost : CExc) (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U →
    ∀ (heap : Heap), HeapOk j U heap → RefsOk U v →
      ∀ args, CallArguments.Values args → (∀ a ∈ args, RefsOk U a) → Acc j U args → requires args heap →
        ∃ result, ConstructsTo v args result ∧
          SafePostExcV Ξ (R args) (post .undef args j U heap) (excPost .undef args j U heap) j U heap result

end Verification.CallEffects
