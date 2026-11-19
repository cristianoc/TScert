import Verification.Paper.TolerantFrames.ReadOnlyFitsDecide
import Verification.Paper.TolerantFrames.ReadOnlyOutside
import Verification.Paper.TolerantFrames.ReadOnlyExec
import Verification.Semantics.HeapObservations

/-! # A linked call of P22's walker, from an initial configuration

The first check of milestone 1 of the framed acceptance draft
(`docs/drafts/framed-acceptance.md`, "Milestones"): one actual execution of
the calculus, from an initial configuration running the initialization
`initC` (`walk`'s closure, its outside captures the realm's
`Array.prototype` and the native `%ElementAt%`'s step model) and a client
that calls the exported closure, through the entering step and its
incoming crossing, the prologue of the realized code, to the request's
entry, and past the body's allocation `const c = { i: 0 }`; and that
allocation's site the same in the realized code and in the request's
under the canonical numbering keyed by the body (`bodyOf`).

- **The steps are the calculus's** (`step?_sound`, `runTo_sound`, proved):
  a computed step of the fragment a linked call takes is a `Step`, and
  `linked` is the execution of its first 26 steps (`HeapObservations.Steps`).
- **The checks** (`#guard`): the entering step, outside code invoking the
  closure with one more call of `C` active (`depthC`'s blocks at `C`'s
  tag); its incoming crossing, the receiver and the two parameters; the
  request's entry after the prologue, the realized tables the request's
  then the prologue; from there, each state of the realized run the
  request's run's on the realized tables at the same heap
  (`prologue_sim`'s relation), 26 steps, the allocation among them; the
  allocation's site equal in both codes at the canonical numbering, and
  different at a numbering per code.

`walkCode` is the verifier's lowering of
`pipeline/examples/bounds-pattern-unreachable-field-refused.ts` (P22),
behind the prologue `PassUnit.dropReceiver` appends, read from the flow
probe's module code (`SourceClaimJson.ProbeModule.ofRequest`). -/
namespace Verification.Tests.FramedLinkedCall
open Verification ControlFlow TolerantFrames.ReadOnly

/-! ## One step of the calculus, computed, for the steps a linked call takes -/

/-- The call step of a graph closure. -/
def callStep (h : Heap) (f r : Tm) (args : List Tm) : Option (Heap × Tm) :=
  match f with
  | .objAt fs (.graph n E K s caps k rest comp) oid =>
    if k.binds r then some (h, CallArguments.graphEntry n E K s caps (.objAt fs (.graph n E K s caps k rest comp) oid) rest comp r args)
    else none
  | _ => none

mutual
/-- **One step**, computed, of the evaluation steps a linked call of a
module function takes: a binding, a call and its congruences, an
allocation, a read, an element read, a length, a run's node and its
continuations. Any other term: none. -/
def step? (h : Heap) : Tm → Option (Heap × Tm)
  | .letE a b => if isVal a then some (h, subst 0 a b) else (step? h a).map fun p => (p.1, .letE p.2 b)
  | .invoke f r args =>
    if isVal f = false then (step? h f).map fun p => (p.1, .invoke p.2 r args)
    else if isVal r = false then (step? h r).map fun p => (p.1, .invoke f p.2 args)
    else match stepList h args with
      | some p => some (p.1, .invoke f r p.2)
      | none => if args.all isVal then callStep h f r args else none
  | .makeAt c ns inits => match stepList h inits with
    | some p => some (p.1, .makeAt c ns p.2)
    | none => if inits.all isVal && ns.length == inits.length then
        some (h ++ inits ++ [.nul], .objAt (slots h.length ns) c (h.length + inits.length)) else none
  | .arrLit inits => match stepList h inits with
    | some p => some (p.1, .arrLit p.2)
    | none => if inits.all isVal && decide (inits.length ≤ maxArrayLength) then
        some (h ++ inits, .arr (elemSlots h.length inits.length)) else none
  | .elemAt a i =>
    if isVal a = false then (step? h a).map fun p => (p.1, .elemAt p.2 i)
    else if isVal i = false then (step? h i).map fun p => (p.1, .elemAt a p.2)
    else match a, i with
      | .arr ls, .num b => match elemLoc ls b with
        | some l => h[l]?.map fun v => (h, v)
        | none => some (h, .undef)
      | _, _ => none
  | .readAt f a =>
    if isVal a = false then (step? h a).map fun p => (p.1, .readAt f p.2)
    else match a with
      | .objAt fs _ _ => match fs.lookup f with
        | some l => h[l]?.map fun v => (h, v)
        | none => none
      | _ => none
  | .lenOf a =>
    if isVal a = false then (step? h a).map fun p => (p.1, .lenOf p.2)
    else match a with
      | .arr ls => some (h, .num (bitsOfNat ls.length))
      | _ => none
  | .goto E K l L d comp => match E[l]?, K[l]? with
    | some e, some (k, x) => some (h, .frame E K (instantiate 0 (envOf L d) e) L d k x comp)
    | _, _ => none
  | .frame E K t L d k x comp =>
    if isVal t then match k with
      | .ret => some (h, t)
      | .bind y => some (h, .goto E K y.label (envMap y.mapping (t :: L) d).1 (envMap y.mapping (t :: L) d).2 comp)
      | .effect y => some (h, .goto E K y.label (envMap y.mapping L d).1 (envMap y.mapping L d).2 comp)
      | _ => none
    else (step? h t).map fun p => (p.1, .frame E K p.2 L d k x comp)
  | _ => none
termination_by structural t => t

/-- One step of the first element of a list that is no value. -/
def stepList (h : Heap) : List Tm → Option (Heap × List Tm)
  | [] => none
  | a :: as => if isVal a then (stepList h as).map fun p => (p.1, a :: p.2)
    else (step? h a).map fun p => (p.1, p.2 :: as)
termination_by structural xs => xs
end

/-- What `stepList` steps: the first element that is no value. -/
def ListStep (h : Heap) (xs : List Tm) (h' : Heap) (xs' : List Tm) : Prop :=
  ∃ i a a', xs[i]? = some a ∧ (∀ j, j < i → ∀ v, xs[j]? = some v → isVal v = true) ∧ Step h a h' a' ∧
    xs' = xs.set i a'

theorem ListStep.cons_val {h h' : Heap} {a : Tm} {xs xs' : List Tm} (ha : isVal a = true)
    (hs : ListStep h xs h' xs') : ListStep h (a :: xs) h' (a :: xs') := by
  obtain ⟨i, b, b', hb, hpre, hst, rfl⟩ := hs
  refine ⟨i + 1, b, b', by simpa using hb, ?_, hst, by simp⟩
  intro j hj v hv
  cases j with
  | zero => simp at hv; subst hv; exact ha
  | succ j => exact hpre j (by omega) v (by simpa using hv)

theorem ListStep.head {h h' : Heap} {a a' : Tm} {xs : List Tm} (hs : Step h a h' a') :
    ListStep h (a :: xs) h' (a' :: xs) :=
  ⟨0, a, a', rfl, fun j hj => absurd hj (Nat.not_lt_zero j), hs, rfl⟩

theorem callStep_sound {h h' : Heap} {f r t' : Tm} {args : List Tm} (hr : isVal r = true)
    (ha : ∀ a ∈ args, isVal a = true) (e : callStep h f r args = some (h', t')) : Step h (.invoke f r args) h' t' := by
  unfold callStep at e
  split at e
  · split at e
    · cases e; exact Step.callGraph hr ha (by assumption)
    · cases e
  · cases e

theorem all_isVal {xs : List Tm} (h : xs.all isVal = true) : ∀ a ∈ xs, isVal a = true := by
  simpa using h

mutual
/-- **The computed step is a step** (proved). -/
theorem step?_sound : (t : Tm) → ∀ {h h' t'}, step? h t = some (h', t') → Step h t h' t'
  | .letE a b, h, h', t', e => by
    unfold step? at e
    split at e
    · cases e; exact Step.letV (by assumption)
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp e
      cases he; exact Step.letC (step?_sound a hp)
  | .invoke f r args, h, h', t', e => by
    unfold step? at e
    split at e
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp e
      cases he; exact Step.callL (step?_sound f hp)
    · rename_i hf
      split at e
      · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp e
        cases he; exact Step.callRecv (by simpa using hf) (step?_sound r hp)
      · rename_i hr
        split at e
        · rename_i p hp
          cases e
          obtain ⟨i, a, a', hi, hpre, hst, heq⟩ := stepList_sound args hp
          rw [heq]; exact Step.callArg (by simpa using hf) (by simpa using hr) hi hpre hst
        · split at e
          · exact callStep_sound (by simpa using hr) (all_isVal (by assumption)) e
          · cases e
  | .makeAt c ns inits, h, h', t', e => by
    unfold step? at e
    split at e
    · rename_i p hp
      cases e
      obtain ⟨i, a, a', hi, hpre, hst, heq⟩ := stepList_sound inits hp
      rw [heq]; exact Step.makeArg hi hpre hst
    · split at e
      · rename_i hc
        cases e
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact Step.makeFields (all_isVal hc.1) hc.2
      · cases e
  | .arrLit inits, h, h', t', e => by
    unfold step? at e
    split at e
    · rename_i p hp
      cases e
      obtain ⟨i, a, a', hi, hpre, hst, heq⟩ := stepList_sound inits hp
      rw [heq]; exact Step.arrArg hi hpre hst
    · split at e
      · rename_i hc
        cases e
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact Step.arrAlloc (all_isVal hc.1) hc.2
      · cases e
  | .elemAt a i, h, h', t', e => by
    unfold step? at e
    split at e
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp e
      cases he; exact Step.elemC1 (step?_sound a hp)
    · rename_i ha
      split at e
      · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp e
        cases he; exact Step.elemC2 (by simpa using ha) (step?_sound i hp)
      · split at e
        · split at e
          · obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp e
            cases he; exact Step.elemRead (by assumption) hv
          · cases e; exact Step.elemAbsent (by assumption)
        · cases e
  | .readAt f a, h, h', t', e => by
    unfold step? at e
    split at e
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp e
      cases he; exact Step.readC (step?_sound a hp)
    · split at e
      · split at e
        · obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp e
          cases he; exact Step.readField (by assumption) hv
        · cases e
      · cases e
  | .lenOf a, h, h', t', e => by
    unfold step? at e
    split at e
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp e
      cases he; exact Step.lenC (step?_sound a hp)
    · split at e
      · cases e; exact Step.lenV
      · cases e
  | .goto E K l L d comp, h, h', t', e => by
    unfold step? at e
    split at e
    · cases e; exact Step.gotoEnter (by assumption) (by assumption)
    · cases e
  | .frame E K t L d k x comp, h, h', t', e => by
    unfold step? at e
    split at e
    · rename_i hv
      split at e
      · cases e; exact Step.frameRet hv
      · cases e; exact Step.frameBind hv
      · cases e; exact Step.frameEffect hv
      · cases e
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp e
      cases he; exact Step.frameC (step?_sound t hp)
  | .var _, _, _, _, e | .construct _ _, _, _, _, e | .nul, _, _, _, e | .undef, _, _, _, e
  | .tru, _, _, _, e | .fls, _, _, _, e | .num _, _, _, _, e | .str _, _, _, _, e | .bigint _, _, _, _, e
  | .sym _, _, _, _, e | .objAt .., _, _, _, e | .indexAt .., _, _, _, e | .writeAt .., _, _, _, e
  | .test .., _, _, _, e | .ite .., _, _, _, e | .arith .., _, _, _, e | .arr _, _, _, _, e
  | .viewSpine .., _, _, _, e | .setElem .., _, _, _, e | .spread _, _, _, _, e | .throw _, _, _, _, e
  | .merge .., _, _, _, e | .makeKey .., _, _, _, e => by simp [step?] at e

theorem stepList_sound : (xs : List Tm) → ∀ {h h' xs'}, stepList h xs = some (h', xs') → ListStep h xs h' xs'
  | [], _, _, _, e => by simp [stepList] at e
  | a :: as, h, h', xs', e => by
    unfold stepList at e
    split at e
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp e
      cases he; exact (stepList_sound as hp).cons_val (by assumption)
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp e
      cases he; exact ListStep.head (step?_sound a hp)
end


/-- `n` computed steps. -/
def runTo : Nat → Heap → Tm → Option (Heap × Tm)
  | 0, h, t => some (h, t)
  | n + 1, h, t => match step? h t with
    | some (h', t') => runTo n h' t'
    | none => none

/-- **Computed steps are an execution** (proved). -/
theorem runTo_sound : ∀ n {h t h' t'}, runTo n h t = some (h', t') → HeapObservations.Steps n h t h' t'
  | 0, h, t, h', t', e => by simp [runTo] at e; obtain ⟨rfl, rfl⟩ := e; exact .refl
  | n + 1, h, t, h', t', e => by
    simp only [runTo] at e
    split at e
    · rename_i h₁ t₁ hs
      exact .next (step?_sound t hs) (runTo_sound n e)
    · cases e

theorem runTo_steps (n : Nat) {h t} (hs : (runTo n h t).isSome = true) :
    HeapObservations.Steps n h t ((runTo n h t).get hs).1 ((runTo n h t).get hs).2 :=
  runTo_sound n (Option.some_get hs).symm

/-! ## P22's walk, linked -/

/-- The component's tag. -/
def cC : ComponentTag := some 0

/-- P22's `walk`, realized (`PassUnit.dropReceiver`): the request's 33
nodes, then the prologue node, continuing at the request's start `32` with
the slots past the receiver. -/
def walkCode : Code :=
([Tm.nul,
  Tm.nul,
  Tm.nul,
  Tm.nul,
  Tm.nul,
  Tm.nul,
  Tm.writeAt (PropKey.str "i") (Tm.var 2) (Tm.var 0),
  Tm.arith (Arith.add) (Tm.var 0) (Tm.num 4607182418800017408),
  Tm.readAt (PropKey.str "i") (Tm.var 0),
  Tm.arith (Arith.add) (Tm.var 6) (Tm.var 0),
  Tm.invoke (Tm.var 2) (Tm.undef) [Tm.var 1, Tm.var 0],
  Tm.readAt (PropKey.str "i") (Tm.var 0),
  Tm.var 8,
  Tm.invoke (Tm.var 1) (Tm.undef) [Tm.var 0],
  Tm.readAt (PropKey.str "i") (Tm.var 0),
  Tm.nul,
  Tm.var 0,
  Tm.var 0,
  Tm.arith (Arith.lt) (Tm.var 1) (Tm.var 0),
  Tm.lenOf (Tm.var 0),
  Tm.readAt (PropKey.str "[]") (Tm.var 0),
  Tm.readAt (PropKey.str "i") (Tm.var 0),
  Tm.arith (Arith.lt) (Tm.var 1) (Tm.var 0),
  Tm.lenOf (Tm.var 0),
  Tm.readAt (PropKey.str "[]") (Tm.var 0),
  Tm.readAt (PropKey.str "i") (Tm.var 0),
  Tm.var 0,
  Tm.num 0,
  Tm.makeAt (CallCode.absent) [PropKey.str "i"] [Tm.var 0],
  Tm.num 0,
  Tm.undef,
  Tm.undef,
  Tm.nul,
  Tm.undef],
 [(Continuation.effect { label := 29, mapping := none }, none),
  (Continuation.effect { label := 27, mapping := none }, none),
  (Continuation.effect { label := 25, mapping := some [1, 1, 0, 1, 2, 3, 4, 5, 6, 7] }, none),
  (Continuation.effect { label := 14, mapping := some [1, 1, 5, 0, 1, 2, 3, 4, 5, 6, 7] },
   none),
  (Continuation.effect { label := 12, mapping := some [0, 0, 1, 2, 3, 4, 5, 6, 7] }, none),
  (Continuation.effect { label := 8, mapping := some [1, 0, 1, 2, 3, 4, 5, 6, 7] }, none),
  (Continuation.effect { label := 2, mapping := some [3, 4, 5, 6, 7, 8, 9, 10] }, none),
  (Continuation.bind { label := 6, mapping := none }, none),
  (Continuation.bind { label := 7, mapping := none }, none),
  (Continuation.bind { label := 5, mapping := some [0, 9, 10, 11, 12, 13, 14, 15] }, none),
  (Continuation.bind
     { label := 9, mapping := some [0, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] },
   none),
  (Continuation.bind
     { label := 10, mapping := some [0, 3, 4, 0, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13] },
   none),
  (Continuation.bind { label := 11, mapping := some [3, 3, 6, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] },
   none),
  (Continuation.bind { label := 4, mapping := some [6, 7, 8, 9, 10, 11, 12, 13] }, none),
  (Continuation.bind
     { label := 13, mapping := some [0, 3, 0, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11] },
   none),
  (Continuation.effect { label := 16, mapping := some [0, 0, 1, 2, 3, 4, 5, 6, 7] }, none),
  (Continuation.ret, none),
  (Continuation.branchBind
     { label := 3, mapping := some [7, 8, 9, 10, 11, 12, 13, 14] }
     { label := 15, mapping := some [7, 8, 9, 10, 11, 12, 13, 14] },
   none),
  (Continuation.bind
     { label := 17, mapping := some [0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] },
   none),
  (Continuation.bind
     { label := 18, mapping := some [0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] },
   none),
  (Continuation.bind { label := 19, mapping := none }, none),
  (Continuation.bind
     { label := 20, mapping := some [11, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] },
   none),
  (Continuation.bind
     { label := 21, mapping := some [8, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] },
   none),
  (Continuation.bind
     { label := 22, mapping := some [0, 4, 0, 3, 4, 5, 6, 7, 8, 0, 10, 11, 12, 13] },
   none),
  (Continuation.bind { label := 23, mapping := none }, none),
  (Continuation.bind { label := 24, mapping := some [7, 7, 0, 2, 3, 4, 0, 6, 7, 8, 9, 10] },
   none),
  (Continuation.effect { label := 2, mapping := some [0, 1, 2, 3, 4, 5, 6, 7] }, none),
  (Continuation.bind { label := 26, mapping := some [0, 1, 2, 3, 4, 5, 6, 7] }, none),
  (Continuation.bind { label := 1, mapping := some [0, 3, 4, 5, 6, 7, 8] }, none),
  (Continuation.bind { label := 28, mapping := some [0, 0, 1, 2, 3, 4, 5, 6] }, none),
  (Continuation.bind { label := 0, mapping := some [0, 1, 2, 3, 4, 5] }, none),
  (Continuation.bind { label := 30, mapping := none }, none),
  (Continuation.effect { label := 31, mapping := none }, none),
  (Continuation.effect { label := 32, mapping := some [1, 2, 3, 4, 5] }, none)])

def walkE : List Tm := walkCode.1
def walkK : List (Continuation × Option Target) := walkCode.2
/-- The request's tables. -/
def reqE : List Tm := walkE.take 33
def reqK : List (Continuation × Option Target) := walkK.take 33

/-- The realm's `Array.prototype`, its identity at location `0`. -/
def AP : Tm := .objAt [] .absent 0
/-- `%ElementAt%`'s step model (`SourceClaimJson.hostModel?`). -/
def eaCode : Code := ([.elemAt (.readAt arraySpineKey (.var 1)) (.var 2)], [(.ret, none)])
/-- The native's closure, its identity at location `1`. -/
def EA : Tm := .objAt [] (.graph 2 eaCode.1 eaCode.2 0 [] .call false cC) 1
/-- The realm's heap: the identities of its two intrinsics. -/
def hR : Heap := [.nul, .nul]

/-- `walk`'s closure code, its captures the two outside slots. -/
def walkCall : CallCode := .graph 2 walkE walkK 33 [AP, EA] .call false cC
/-- The initialization `initC`: `walk`'s closure, then the array of exports. -/
def initE : List Tm := [.makeAt walkCall [] [], .arrLit [.var 0]]
def initK : List (Continuation × Option Target) := [(.bind ⟨1, none⟩, none), (.ret, none)]

/-- A client, lowered source of outside code scoped at one binder (the
exports): `exports[0]({ "[]": [0] }, () => undefined)`. -/
def client : Tm := .invoke (.elemAt (.var 0) (.num 0)) .undef
  [.makeAt .absent [arraySpineKey] [.arrLit [.num 0]], .makeAt (.graph 1 [.undef] [(.ret, none)] 0 [] .call false none) [] []]

/-- The initial configuration's term: `letE (gotoOf initC 0 [] undefined c_C) client`. -/
def x0 : Tm := .letE (.goto initE initK 0 [] .undef cC) client

/-- The state after `n` steps. -/
def at? (n : Nat) : Option (Heap × Tm) := runTo n hR x0

set_option maxRecDepth 100000 in
/-- **The linked call is an execution** (proved): 26 steps from the initial
configuration, through the entering step (step 12), the prologue (steps
13–14) and the allocation of the cursor (step 26). -/
theorem linked : HeapObservations.Steps 26 hR x0 ((at? 26).get (by decide)).1 ((at? 26).get (by decide)).2 :=
  runTo_steps 26 _

/-- **The calls of `C` active** (`depthC` at the tag `cC`, computed). -/
def depth (t : Tm) : Nat := blocks ((path none t).map fun p => p.1 == cC)

-- the entering step: outside code invokes `walk`'s closure, then one more call
-- of `C` is active
#guard (at? 11).any fun (_, t) => depth t == 0 && match t with
  | .invoke (.objAt fs c o) .undef _ => Tm.objAt fs c o == Tm.objAt fs walkCall o
  | _ => false
#guard (at? 12).any fun (_, t) => depth t == 1 && match t with
  | .goto E K 33 L .nul c => E == walkE && K == walkK && c == cC && L.length == 6
  | _ => false
-- the entering step's incoming crossing: the receiver and the two parameters,
-- read from the entered run's slots
#guard (at? 12).any fun (_, t) => match t with
  | .goto _ _ _ L _ _ => match L with
    | [.undef, .objAt [(k, _)] .absent _, .objAt [] (.graph 1 _ _ _ _ _ _ none) _, _, _, _] => k == arraySpineKey
    | _ => false
  | _ => false

/-- The request's entry: after the prologue, the realized code at the
request's start `32`, its slots past the receiver, its default the
receiver. -/
def entry : Option (Heap × Tm) := at? 14

-- `RealizedAt`: the realized tables are the request's, then the prologue
#guard entry.any fun (_, t) => match t with
  | .goto E K 32 L d c => E == walkE && K == walkK && c == cC && L.length == 5 && d == .undef &&
      E.take 33 == reqE && K.take 33 == reqK && E.length == 34 && depth t == 1
  | _ => false

/-- The term of the request's run for a realized one: the same run on the
request's tables. -/
def retable : Tm → Tm
  | .goto E K l L d c => if E = walkE ∧ K = walkK then .goto reqE reqK l L d c else .goto E K l L d c
  | .frame E K t L d k x c =>
    if E = walkE ∧ K = walkK then .frame reqE reqK (retable t) L d k x c else .frame E K (retable t) L d k x c
  | t => t

/-- The request's run `gotoOf r.program r.start L d r.comp` from the same
entry. -/
def reqAt (i : Nat) : Option (Heap × Tm) := entry.bind fun (h, t) => runTo i h (retable t)

-- `prologue_sim` past the allocation: from the entry, each state of the
-- realized run is the request's run's on the realized tables, at the same heap
#guard (List.range 27).all fun i => match at? (14 + i), reqAt i with
  | some (h, t), some (h', t') => h == h' && retable t == t'
  | _, _ => false

/-! ## One site per body allocation -/

/-- The package of the check: the code tagged `cC` is `C`'s. -/
abbrev Pk : Package := ⟨Nat, fun _ => .local, fun c => c == cC⟩

/-- The bodies of `C`'s codes: the request's, the initialization's, the
native's model. -/
def bodies : List Code := [(reqE, reqK), (initE, initK), eaCode]

/-- **The body of a code** (`bodyOf`): the request's tables for the
realized code, the code itself for any other. -/
def bodyOf (m : Code) : Code := if m = (walkE, walkK) then (reqE, reqK) else m

/-- **The canonical allocation sites of a code**, its body read by `body`:
per continuation and handler of the body, an object site and an array
site, numbered by the body's place among `bodies` and the first node of
that continuation and handler. -/
def canonAllocs (body : Code → Code) (m : Code) : List (NodeKey × Option Nat × Option Nat) :=
  let b := body m
  let offs := (bodies.map (·.2.length)).foldl (fun (acc : List Nat) n => acc ++ [acc.getLast?.getD 0 + n]) [0]
  match (bodies ++ [m]).idxOf? b with
  | some bi => m.2.filterMap fun kx => (b.2.idxOf? kx).map fun l =>
      let k := 3 * (bodies.length + 1) + 2 * (offs.getD bi bodies.length + l)
      (kx, some k, some (k + 1))
  | none => []

/-- A code's proposal at the canonical sites its body gives. -/
def fcOf (body : Code → Code) (m : Code) : FCode Pk :=
  ⟨#[], ⟨#[], [], [], #[], none, entryCx, true⟩, ⟨none, none⟩, #[], [], none, canonAllocs body m⟩

/-- A flow holding both codes, the realized one and the request's, at the
sites `body` numbers. -/
def flowAt (body : Code → Code) : FFlow Pk := ⟨[none], [], [((walkE, walkK), [(entryCx, fcOf body (walkE, walkK))]),
  ((reqE, reqK), [(entryCx, fcOf body (reqE, reqK))])], fun _ => false⟩

-- the cursor `const c = { i: 0 }`, allocated by step 26 in the realized code,
-- and by the request's step at the same site, keyed by the body
#guard (at? 25).any fun (h, t) => match t with
  | .frame _ _ (.makeAt .absent [k] [.num 0]) _ _ _ _ _ =>
    k == .str "i" && (at? 26).any (fun (h', _) => h'.length == h.length + 2) &&
    stepSite (flowAt bodyOf).flow none t == stepSite (flowAt bodyOf).flow none (retable t) &&
    (stepSite (flowAt bodyOf).flow none t).isSome
  | _ => false
-- numbered per code, the two allocations get two sites
#guard (at? 25).any fun (_, t) =>
  stepSite (flowAt id).flow none t != stepSite (flowAt id).flow none (retable t)

end Verification.Tests.FramedLinkedCall
