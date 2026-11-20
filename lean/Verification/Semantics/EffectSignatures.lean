import Verification.Semantics.ExitPosts
import Verification.Semantics.ExceptionalPosts
import Verification.Semantics.Purity
import Verification.Semantics.ClosedFootprints
import Verification.Semantics.IndexFacts
import Verification.Semantics.SpineRegions
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

/-- **A call signature's guarantee beyond its contract** (the note
*Tolerant frames*, §6, the specification of a callable, $c:\Phi\mid\Phi^{e}$):
its specification per completion (`exits`, an `ExitSchema` for the normal
and one for the exceptional exit: a frame bounding the change from the
call's entry heap to the heap the exit leaves, and two-state postconditions,
read at the call's positions, `callEnv`, and the exit's, `ensuresEnv`), and
an optional promise and two preconditions, which are no part of an exit.
Without a promise the signature's result operand is the result's type.
`requires` states a precondition on the receiver's elements: they meet the
predicate in the heap the call starts in (`ElemsAt`); `pre` one on the
call's values: each index fact holds of them in the heap the call starts
in, read at the call's positions (`callEnv`: 0 the receiver, `i + 1` the
`i`-th actual), such as `bound(1, 2, true)`, the second actual an index
below the length of the first actual's spine. -/
structure Effect where
  exits : Exits ExitSchema
  promise : Option TypePromise
  «requires» : Option ElemPred := none
  pre : List HeapKnowledge.IndexFact := []
  deriving Repr, DecidableEq

/-- **A signature's specification schema**: its exits. -/
abbrev Effect.schema (e : Effect) : Exits ExitSchema := e.exits

/-- A signature with a closed frame on a normal return, `⊤` on a throw, and
no promise. -/
def Effect.ofFootprint (c : Footprints.Closed) : Effect :=
  ⟨⟨⟨c.fp, []⟩, ⟨Parity.topEffect, []⟩⟩, none, none, []⟩

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


/-- A change from `before` to `after` that alters no old location but the
receiver `r`'s spine, which, where it changes, held a spine and holds one
extending it, its old elements at their indices, at most `2^32 - 1` long:
`Array.prototype.push` on an array (SOURCE-CONTRACTS.md, "Native
footprints"). -/
def ReceiverGrows (r : Tm) (before after : Heap) : Prop :=
  ∀ l v, before[l]? = some v → after[l]? = some v ∨
    (Footprints.spineOf r = some l ∧ ∃ ls ls', v = .arr ls ∧ after[l]? = some (.arr ls') ∧
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

/-- A receiver holding no spine has nothing appended. -/
theorem ReceiverAppends.of_no_spine {r : Tm} {args : List Tm} {before after : Heap}
    (h : Footprints.spineOf r = none) : ReceiverAppends r args before after := by
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


/-- An argument spine region's entry of a frame: the spine location the
region selects at the call's entry, at `any`. -/
def regionEntry (r : Footprints.ArgumentSpineRegion) : Footprints.Region × Footprints.Change := r.entry

/-- **The frame** of a signature: its normal exit's, read at the call's
positions (`callEnv`). It is the one statement of what a normal return may
change. -/
def Effect.frame (e : Effect) : Footprints.Footprint := e.exits.normal.frame

/-- What a signature's frame states of a call with receiver `r` and actuals
`args`: `Post` of the frame at the call's positions. -/
def Effect.within (e : Effect) (r : Tm) (args : List Tm) (before after : Heap) : Prop :=
  Footprints.Post e.frame (callEnv r args) before after

/-- **The closed bound above a signature's frame** (`Footprint.close`): each
category's largest change any entry of the frame admits. Every change the
frame admits is within it (`Effect.within_changeBound`): the bound a
conservative reader of a call's change uses. -/
def Effect.changeBound (e : Effect) : Footprints.Closed := e.frame.close

theorem Effect.within_changeBound {e : Effect} {r : Tm} {args : List Tm} {before after : Heap}
    (h : e.within r args before after) : e.changeBound.Holds before after :=
  Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp (Footprints.Footprint.close_sound h))

/-- **Whether a signature's frame admits every change** (sufficient): its
class bound (`Footprint.classBound`) is `⊤`, so every change keeping the
heap's prefix meets the frame (`Effect.within_of_admitsAll`). -/
def Effect.admitsAll (e : Effect) : Bool := e.frame.classBound == .top

theorem Effect.within_of_admitsAll {e : Effect} (h : e.admitsAll = true) {r : Tm} {args : List Tm}
    {before after : Heap} (hl : before.length ≤ after.length) : e.within r args before after := by
  simp only [Effect.admitsAll, beq_iff_eq] at h
  exact Footprints.Footprint.classBound_sound (by rw [h]; exact Footprints.Closed.holds_top.mpr hl)


/-- Whether the signature's result operand is the result's type and it
states no precondition: a signature an ordinary arrow can stand for once its
postcondition, an elements promise included, is forgotten. -/
def Effect.plain (e : Effect) : Bool := e.promise.isNone && e.requires.isNone && e.pre.isEmpty


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

/-- Whether binding `n` actuals keeps the promise about an actual of the
bound call, and the signature states no precondition. A precondition is
about the receiver or the actuals the binding saves, which the bound call
does not pass: binding keeps none. What binding keeps of the exits is their
weakening at the bound call (`Effect.drop`). -/
def Effect.keeps (n : Nat) (e : Effect) : Bool :=
  e.requires.isNone && e.pre.isEmpty && match e.promise with
  | some p => n ≤ p.param
  | none => true

theorem Effect.keeps_requires {e : Effect} {n : Nat} (h : e.keeps n = true) : e.requires = none := by
  simp only [Effect.keeps, Bool.and_eq_true, Option.isNone_iff_eq_none] at h; exact h.1.1

theorem Effect.keeps_pre {e : Effect} {n : Nat} (h : e.keeps n = true) : e.pre = [] := by
  simp only [Effect.keeps, Bool.and_eq_true, List.isEmpty_iff] at h; exact h.1.2

/-- Whether a promise is about one of the first `n` parameters, the ones code
of arity `n` binds. -/
def Effect.promiseBelow (n : Nat) (e : Effect) : Bool :=
  match e.promise with
  | some p => p.param < n
  | none => true

/-- **Whether what a signature states of the call's values at entry is
about the receiver and the first `n` parameters**, the ones code of arity
`n` binds: its promise, and each position its precondition `pre` names, read
at the callee's entry, where `old(t)` is `t` (`IndexFact.toNow`). The scope
of its exits is `Exits.belowRow` (`Effect.belowRow`). -/
def Effect.entryBelow (n : Nat) (e : Effect) : Bool :=
  e.promiseBelow n && e.pre.all (fun F => F.toNow.slots.all (· ≤ n))

theorem Effect.entryBelow_promise {e : Effect} {n : Nat} (h : e.entryBelow n = true) : e.promiseBelow n = true := by
  simp only [Effect.entryBelow, Bool.and_eq_true] at h; exact h.1

theorem Effect.entryBelow_pre {e : Effect} {n : Nat} (h : e.entryBelow n = true) :
    ∀ F ∈ e.pre, ∀ s ∈ F.toNow.slots, s ≤ n := by
  simp only [Effect.entryBelow, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun F hF => h.2 F hF

/-- **A precondition is one-state**: read at the callee's entry, where the
current state is the entry state, a fact holds exactly where its
restatement with each `old(t)` as `t` does (`IndexFact.holdsAt_toNow`), at
any entry state (`IndexFact.entrySlots_toNow`). -/
theorem Effect.pre_toNow {F : HeapKnowledge.IndexFact} (ε : HeapKnowledge.EntryState) (ρ : Env) (heap : Heap) :
    F.HoldsAt ⟨ρ, heap⟩ ρ heap ↔ F.toNow.HoldsAt ε ρ heap :=
  (HeapKnowledge.IndexFact.holdsAt_toNow rfl rfl).symm.trans
    (HeapKnowledge.IndexFact.holdsAt_entry (HeapKnowledge.IndexFact.entrySlots_toNow F) _)


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
theorem Effect.promised_frame {e : Effect} {n : Nat} (h : e.entryBelow n = true) (args vs : List Tm) :
    e.promised (CallArguments.parameters n args ++ vs) = e.promised args := by
  unfold Effect.promised
  have h := Effect.entryBelow_promise h
  unfold Effect.promiseBelow at h
  split
  · rename_i p hp
    rw [hp] at h
    simp only [decide_eq_true_eq] at h
    rw [← parameters_getD n args p.param h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [Effect.parameters_length]; exact h)]
  · rfl

/-- Actuals past those code binds do not change what it promises about. -/
theorem Effect.promised_take {e : Effect} {n m : Nat} (h : e.entryBelow n = true) (hm : n ≤ m) (args : List Tm) :
    e.promised (args.take m) = e.promised args := by
  unfold Effect.promised
  have h := Effect.entryBelow_promise h
  unfold Effect.promiseBelow at h
  split
  · rename_i p hp
    rw [hp] at h
    simp only [decide_eq_true_eq] at h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [ite_eq_left (by omega)]
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
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
      List.cons_append, List.getElem?_cons_succ, List.getElem?_append_left hlen, hx, Option.getD_some, hp]

/-- Actuals past position `m` do not change the call's positions up to `m`. -/
theorem callEnv_take {m s : Nat} (hle : s ≤ m) (r : Tm) (args : List Tm) :
    callEnv r (args.take m) s = callEnv r args s := by
  simp only [callEnv]
  cases s with
  | zero => simp
  | succ i =>
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [ite_eq_left (by omega)]

/-- Code binding `n` parameters reads the precondition's positions in its
frame as the call passed them: the receiver, then each actual it binds. -/
theorem Effect.pre_frame {e : Effect} {n : Nat} (h : e.entryBelow n = true) {F : HeapKnowledge.IndexFact}
    (hF : F ∈ e.pre) (r : Tm) (args vs : List Tm) (d : Tm) (heap : Heap) :
    F.HoldsAt ⟨callEnv r args, heap⟩ (callEnv r args) heap ↔
      F.HoldsAt ⟨envOf (r :: CallArguments.parameters n args ++ vs) d, heap⟩
        (envOf (r :: CallArguments.parameters n args ++ vs) d) heap := by
  refine (Effect.pre_toNow ⟨callEnv r args, heap⟩ _ heap).trans (Iff.trans ?_ (Effect.pre_toNow ⟨callEnv r args, heap⟩ _ heap).symm)
  exact HeapKnowledge.IndexFact.holdsAt_congr fun s hs => callEnv_frame (Effect.entryBelow_pre h F hF s hs) r args vs d

/-- Actuals past those code binds do not change what its precondition reads. -/
theorem Effect.pre_take {e : Effect} {n m : Nat} (h : e.entryBelow n = true) (hm : n ≤ m) {F : HeapKnowledge.IndexFact}
    (hF : F ∈ e.pre) (r : Tm) (args : List Tm) (heap : Heap) :
    F.HoldsAt ⟨callEnv r (args.take m), heap⟩ (callEnv r (args.take m)) heap ↔
      F.HoldsAt ⟨callEnv r args, heap⟩ (callEnv r args) heap := by
  refine (Effect.pre_toNow ⟨callEnv r args, heap⟩ _ heap).trans (Iff.trans ?_ (Effect.pre_toNow ⟨callEnv r args, heap⟩ _ heap).symm)
  exact HeapKnowledge.IndexFact.holdsAt_congr fun s hs => callEnv_take (by have := Effect.entryBelow_pre h F hF s hs; omega) r args

/-- Code binding `n` parameters reads a postcondition fact's positions in
its entry frame, the result pushed, as the call passed them, where the fact
reads the result, the receiver and the first `n` parameters at exit and the
receiver and the first `n` parameters at entry. -/
theorem Effect.ensures_frame {n : Nat} {F : HeapKnowledge.IndexFact} (hsl : ∀ s ∈ F.slots, s ≤ n + 1)
    (hen : ∀ s ∈ F.entrySlots, s ≤ n) (v r : Tm) (args vs : List Tm) (d : Tm) (before heap : Heap) :
    F.HoldsAt ⟨callEnv r args, before⟩ (ensuresEnv v r args) heap ↔
      F.HoldsAt ⟨envOf (r :: CallArguments.parameters n args ++ vs) d, before⟩
        (push v (envOf (r :: CallArguments.parameters n args ++ vs) d)) heap := by
  refine (HeapKnowledge.IndexFact.holdsAt_congr_entry (ε := ⟨callEnv r args, before⟩)
    (ε' := ⟨envOf (r :: CallArguments.parameters n args ++ vs) d, before⟩) rfl fun s hs =>
    callEnv_frame (hen s hs) r args vs d).trans
    (HeapKnowledge.IndexFact.holdsAt_congr fun s hs => ?_)
  have hle := hsl s hs
  rcases s with _ | _ | i
  · rfl
  · simp [ensuresEnv, callEnv, push, envOf]
  · have hp : (CallArguments.parameters n args).getD i .undef = args.getD i .undef :=
      parameters_getD n args i (by omega)
    have hlen : i < (CallArguments.parameters n args).length := by rw [Effect.parameters_length]; omega
    obtain ⟨x, hx⟩ : ∃ x, (CallArguments.parameters n args)[i]? = some x :=
      ⟨_, List.getElem?_eq_getElem hlen⟩
    simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some] at hp
    simp only [ensuresEnv, callEnv, push, envOf, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
      List.getD_eq_getElem?_getD, List.cons_append, List.getElem?_cons_succ, List.getElem?_append_left hlen, hx,
      Option.getD_some, hp]


/-- A postcondition at actuals padded with `undefined` is the one at the
actuals, of a receiver holding no spine. -/
theorem ElementWrite.holds_pad {w : ElementWrite} {args pad : List Tm} (hpad : ∀ a ∈ pad, a = .undef)
    {before after : Heap} (h : w.Holds (args ++ pad) before after) : w.Holds args before after := by
  obtain ⟨hc, hx, ha⟩ := h
  have hg : ∀ i, (args ++ pad).getD i .undef = args.getD i .undef := fun i => by
    simpa [callEnv] using congrFun (callEnv_pad .undef args hpad) (i + 1)
  refine ⟨hc, fun k he => ?_, fun he => ?_⟩
  · have := hx k he
    simp only [ExactWrite, WriteAt, ExactPre, hg] at this ⊢
    exact this
  · have := ha he
    simp only [ViewAssign, WriteAt, hg] at this ⊢
    exact this

/-- **Two signatures whose results and preconditions mean the same**: the
same promise, precondition on the receiver's elements and precondition on
the call's values. Their exits conjoin as schemas (`Exits.meet`). -/
def Effect.sameResult (a b : Effect) : Bool :=
  a.promise == b.promise && a.requires == b.requires && a.pre == b.pre

theorem Effect.sameResult_same {a b : Effect} (hs : a.sameResult b = true) :
    b.result = a.result ∧ b.promised = a.promised ∧ b.requires = a.requires ∧ b.pre = a.pre := by
  simp only [Effect.sameResult, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨hp, hr⟩, hpre⟩ := hs
  refine ⟨?_, ?_, hr.symm, hpre.symm⟩
  · funext R x; simp [Effect.result, hp]
  · funext args; simp [Effect.promised, hp]


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
def NativeContract (Ξ : Fam) (Acc : ArgFam) (Rc : Fam) («requires» : Tm → List Tm → Heap → Prop)
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
def NativeConstruct (Ξ : Fam) (Acc : ArgFam) («requires» : List Tm → Heap → Prop) (R : List Tm → Fam)
    (post : CPost) (excPost : CExc) (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U →
    ∀ (heap : Heap), HeapOk j U heap → RefsOk U v →
      ∀ args, CallArguments.Values args → (∀ a ∈ args, RefsOk U a) → Acc j U args → requires args heap →
        ∃ result, ConstructsTo v args result ∧
          SafePostExcV Ξ (R args) (post .undef args j U heap) (excPost .undef args j U heap) j U heap result

end Verification.CallEffects
