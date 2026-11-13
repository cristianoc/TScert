import Verification.Programs.ProgramTyping
-- ../Types/QualifiedGraphs.lean checks lexical instances of schemes whose binders carry resolution descriptors; without it lexical body checking has no instance comparison.
import Verification.Types.QualifiedGraphs

/-! Finite program evidence checked against the declarative rules. Each node
states its sequent explicitly. The external entry point also checks that the
root is the requested closed program and type; evidence cannot change the task.
The evidence fixes its rule and premise tree. Coercion choices are validated
through the common engine, whose execution outcome is retained by `CheckResult`. -/
namespace Verification.ProgramCertificates
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules
open CallEffects (Arrow RestArrow MethodArrow Contract Effect)

structure Sequent (ι : Type) where
  context : List (Ty ι)
  term : Tm
  type : Ty ι
  deriving DecidableEq

/-- `a = b` decided at once where `a` and `b` are one object (`withPtrEq`,
justified by the equality's reflexivity), else by `decide`. -/
@[inline] def decideSame {α : Type} [DecidableEq α] (a b : α) : Bool :=
  withPtrEq a b (fun _ => decide (a = b)) (fun h => by subst h; simp)

theorem decideSame_iff {α : Type} [DecidableEq α] (a b : α) : decideSame a b = true ↔ a = b := by
  simp [decideSame, withPtrEq]

/-- Sequent equality as the compiled verifier decides it
(`instDecidableEqSequent_eq_fast`): field by field, each answered at once
where the two fields are one object. -/
def Sequent.decEqFast {ι : Type} [DecidableEq ι] : DecidableEq (Sequent ι) := fun a b =>
  decidable_of_iff (decideSame a.context b.context && decideSame a.term b.term && decideSame a.type b.type) (by
    obtain ⟨c, t, T⟩ := a
    obtain ⟨c', t', T'⟩ := b
    simp [decideSame_iff, and_assoc])

@[csimp] theorem instDecidableEqSequent_eq_fast : @instDecidableEqSequent = @Sequent.decEqFast := by
  funext ι _ a b
  exact Subsingleton.elim _ _

/-- Validation scopes enclosing an unfinished comparison, outermost first. -/
inductive CheckFrame where
  | node (label : Nat)
  | code (index : Nat)
  | obligation (index : Nat)
  | request (index : Nat)
  deriving Repr, DecidableEq

/-- An incomplete subtype comparison, including its requested judgment. -/
structure Exhaustion (ι : Type) where
  source : Ty ι
  target : Ty ι
  limit : Nat
  rounds : Nat
  visited : Nat
  frames : List CheckFrame := []
  deriving Repr, DecidableEq

/-- The first graph node named by an unfinished comparison's validation scopes. -/
@[nospecialize] def Exhaustion.nodeLabel (stop : Exhaustion ι) : Option Nat :=
  (stop.frames.filterMap fun frame => match frame with
    | .node label => some label
    | .code _ | .obligation _ | .request _ => none).head?

/-- Compositional search and validation retain unfinished subtype work.
Successful proposal values require independent certificate validation. -/
structure CheckResult (ι α : Type) where
  value : Option α
  exhaustion : Option (Exhaustion ι) := none

/-- Attach diagnostic provenance without changing a validation value. -/
@[nospecialize] def CheckResult.at (s : CheckResult ι α) (frame : CheckFrame) : CheckResult ι α :=
  { s with exhaustion := s.exhaustion.map fun stop => { stop with frames := frame :: stop.frames } }

@[nospecialize] def CheckResult.fromOption (o : Option α) : CheckResult ι α := ⟨o, none⟩

instance : Coe (Option α) (CheckResult ι α) := ⟨CheckResult.fromOption⟩

@[nospecialize] def CheckResult.bind (s : CheckResult ι α) (f : α → CheckResult ι β) : CheckResult ι β :=
  match s.value with
  | none => ⟨none, s.exhaustion⟩
  | some a =>
    let t := f a
    if t.value.isSome then t else { t with exhaustion := s.exhaustion <|> t.exhaustion }

instance : Monad (CheckResult ι) where
  pure a := ⟨some a, none⟩
  bind := CheckResult.bind

instance : MonadLift Option (CheckResult ι) where
  monadLift := CheckResult.fromOption

@[nospecialize] def CheckResult.orElse (s : CheckResult ι α) (next : Unit → CheckResult ι α) : CheckResult ι α :=
  match s.value with
  | some a => ⟨some a, none⟩
  | none =>
    let t := next ()
    if t.value.isSome then { t with exhaustion := none }
    else { t with exhaustion := s.exhaustion <|> t.exhaustion }

instance : Alternative (CheckResult ι) where
  failure := ⟨none, none⟩
  orElse := CheckResult.orElse

@[nospecialize] def CheckResult.map (f : α → β) (s : CheckResult ι α) : CheckResult ι β :=
  ⟨s.value.map f, if s.value.isSome then none else s.exhaustion⟩

/-- Try candidates in order, retaining exhaustion only when every candidate fails. -/
@[nospecialize] def _root_.List.findCheck? (xs : List β) (f : β → CheckResult ι α) : CheckResult ι α :=
  match xs with
  | [] => failure
  | x :: xs => (f x).orElse fun _ => xs.findCheck? f

@[nospecialize] def CheckResult.accepted (s : CheckResult ι α) : Bool := s.value.isSome

theorem CheckResult.accepted_at (s : CheckResult ι α) (frame : CheckFrame) :
    (s.at frame).accepted = s.accepted := rfl

@[nospecialize] def CheckResult.ofBool (b : Bool) : CheckResult ι Unit :=
  ⟨if b then some () else none, none⟩

theorem CheckResult.accepted_ofBool (b : Bool) : (CheckResult.ofBool (ι := ι) b).accepted = b := by
  cases b <;> rfl

theorem CheckResult.value_bind (s : CheckResult ι α) (f : α → CheckResult ι β) :
    (s.bind f).value = s.value.bind (fun a => (f a).value) := by
  cases s with
  | mk v e =>
    cases v with
    | none => rfl
    | some a =>
      simp only [CheckResult.bind, Option.bind_some]
      split <;> rfl

theorem CheckResult.accepted_bind_value (s : CheckResult ι α) (f : α → CheckResult ι β) :
    (s.bind f).accepted = s.value.any (fun a => (f a).accepted) := by
  rw [CheckResult.accepted, CheckResult.value_bind]
  cases s.value <;> rfl

theorem CheckResult.accepted_bind_ofBool (s : CheckResult ι α) (p : α → Bool) :
    (s.bind fun a => CheckResult.ofBool (p a)).accepted = s.value.any p := by
  rw [CheckResult.accepted_bind_value]
  cases s.value <;> simp [CheckResult.accepted_ofBool]

theorem CheckResult.accepted_bind (s : CheckResult ι α) (t : CheckResult ι β) :
    (s.bind fun _ => t).accepted = (s.accepted && t.accepted) := by
  cases s with
  | mk v e =>
    cases v with
    | none => rfl
    | some a =>
      simp only [CheckResult.bind, CheckResult.accepted, Option.isSome_some, Bool.true_and]
      split <;> rfl

@[nospecialize] def CheckResult.all (xs : List β) (f : β → CheckResult ι Unit) : CheckResult ι Unit :=
  match xs with
  | [] => pure ()
  | x :: xs => (f x).bind fun _ => CheckResult.all xs f

theorem CheckResult.accepted_all (xs : List β) (f : β → CheckResult ι Unit) :
    (CheckResult.all xs f).accepted = xs.all (fun x => (f x).accepted) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [CheckResult.all, CheckResult.accepted_bind, ih, List.all_cons]

/-- Enumerate checks with their enclosing diagnostic scopes. -/
@[nospecialize] def CheckResult.allLocated (xs : List β) (frame : Nat → CheckFrame)
    (f : β → CheckResult ι Unit) : CheckResult ι Unit :=
  CheckResult.all xs.zipIdx fun (x, i) => (f x).at (frame i)

theorem CheckResult.accepted_allLocated (xs : List β) (frame : Nat → CheckFrame)
    (f : β → CheckResult ι Unit) :
    (CheckResult.allLocated xs frame f).accepted = xs.all (fun x => (f x).accepted) := by
  simp only [CheckResult.allLocated, CheckResult.accepted_all, CheckResult.accepted_at]
  have h := congrArg (fun ys => ys.all (fun x => (f x).accepted)) (List.zipIdx_map_fst 0 xs)
  simpa only [List.all_map, Function.comp_def] using h

/-- Disjunctive validation retains unfinished work if no alternative succeeds. -/
@[nospecialize] def CheckResult.any (xs : List β) (f : β → CheckResult ι Unit) : CheckResult ι Unit :=
  xs.findCheck? f

theorem CheckResult.accepted_orElse (s : CheckResult ι α) (t : Unit → CheckResult ι α) :
    (s.orElse t).accepted = (s.accepted || (t ()).accepted) := by
  cases s with
  | mk v e =>
    cases v with
    | none =>
      simp only [CheckResult.orElse, CheckResult.accepted, Option.isSome_none, Bool.false_or]
      split <;> rfl
    | some a => rfl

theorem CheckResult.accepted_any (xs : List β) (f : β → CheckResult ι Unit) :
    (CheckResult.any xs f).accepted = xs.any (fun x => (f x).accepted) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [CheckResult.any, List.findCheck?, CheckResult.accepted_orElse, List.any_cons]
    exact congrArg ((f x).accepted || ·) ih

theorem CheckResult.value_failure : (failure : CheckResult ι α).value = none := rfl

theorem CheckResult.value_map_const (s : CheckResult ι α) (b : β) :
    (s.map fun _ => b).value = if s.accepted then some b else none := by
  cases s with
  | mk v e => cases v <;> rfl

theorem CheckResult.value_bind_const (s : CheckResult ι α) (t : CheckResult ι β) :
    (s.bind fun _ => t).value = if s.accepted then t.value else none := by
  cases s with
  | mk v e =>
    cases v with
    | none => rfl
    | some a =>
      simp only [CheckResult.bind, CheckResult.accepted, Option.isSome_some, ite_true]
      split <;> rfl

theorem CheckResult.value_orElse (s : CheckResult ι α) (t : Unit → CheckResult ι α) :
    (s.orElse t).value = s.value.orElse fun _ => (t ()).value := by
  cases s with
  | mk v e =>
    cases v with
    | none =>
      simp only [CheckResult.orElse, Option.orElse]
      split <;> rfl
    | some a => rfl

/-- Convert the common subtype outcome while retaining the requested pair. -/
@[nospecialize] def CheckResult.fromComparison (limit : Nat) (A B : Ty ι)
    (r : PositiveCertificates.ComparisonResult α) : CheckResult ι α :=
  match r with
  | .established x => ⟨some x, none⟩
  | .notEstablished => ⟨none, none⟩
  | .exhausted rounds visited => ⟨none, some ⟨A, B, limit, rounds, visited, []⟩⟩

theorem CheckResult.accepted_fromComparison (limit : Nat) (A B : Ty ι)
    (r : PositiveCertificates.ComparisonResult α) :
    (CheckResult.fromComparison limit A B r).accepted = r.accepted := by
  cases r <;> rfl

/-- Validate supplied subtype choices through the common operation. -/
@[nospecialize] def checkSubtypeUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (A B : Ty ι)
    (choices : PositiveCertificates.SubtypeChoices ι) : CheckResult ι Unit :=
  CheckResult.fromComparison images.budget.rounds A B
    ((PositiveCertificates.compareUsing G images A B (choices.proposal G A B)
      (fun _ => choices.members)).map fun _ => ())

theorem checkSubtypeUsing_accepted [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (A B : Ty ι)
    (choices : PositiveCertificates.SubtypeChoices ι) :
    (checkSubtypeUsing G images A B choices).accepted = PositiveCertificates.checkUsing G images A B choices := by
  unfold checkSubtypeUsing PositiveCertificates.checkUsing
  rw [CheckResult.accepted_fromComparison, PositiveCertificates.ComparisonResult.accepted_map]

/-- What a literal index names in a tuple contract, as the checker reads it: a
required position's type; an optional or rest position's type with `undefined`;
any named position's type. -/
@[nospecialize] def requiredAt (T : Tuple (Ty ι)) (b : UInt64) : Option (Ty ι) :=
  (indexOfBits b).bind fun k => T.required[k]?

@[nospecialize] def optionalAt (T : Tuple (Ty ι)) (b : UInt64) (U : Ty ι) : Option (Ty ι) :=
  (indexOfBits b).bind fun k => match T.required[k]? with
    | some _ => none
    | none => (positionTy T k).map (· ++ U)

@[nospecialize] def namedAt (T : Tuple (Ty ι)) (b : UInt64) : Option (Ty ι) :=
  (indexOfBits b).bind fun k => positionTy T k

/-! ### Read summaries

A read summary states, for a receiver type `C`, a key `f` and a result `B`,
that every member of `C` (`members`, enumerated by the checker) states `f`
as a readonly view whose type is within `B`. It is a judgment about types
alone: in any context whose slot `i` holds `C`, `readAt f (var i)` has type
`B` by `unionVar`, then per member `var`, `readView` and `sub`
(`readSummary_sound`). It names no context, no heap and no code entry. -/

/-- One member's arm of a read summary: the view the member states for the
key, and the choices comparing it to the summary's result, none where the
view's type is the result itself. -/
structure SummaryArm (ι : Type) where
  view : Ty ι
  proof : Option (PositiveCertificates.SubtypeChoices ι) := none

/-- A read summary: one arm per member of `receiver`, in `members` order. -/
structure ReadSummary (ι : Type) where
  receiver : Ty ι
  field : PropKey
  result : Ty ι
  arms : List (SummaryArm ι)

/-- The member `a` states `f` as a readonly view at `A`, as `readView` reads
it at a receiver of type `[a]`: a view of `length` only at a type excluding
a number. -/
@[nospecialize] def summaryView [DecidableEq ι] (G : NormalGraph ι) (f : PropKey) (a : ι) (A : Ty ι) : Bool :=
  match expand G [a] with
  | [c] => match namedMembers c with
    | some (_, vs) => decide ((f, A) ∈ vs) && (decide (f ≠ lengthKey) || lengthExcluded G A)
    | none => false
  | _ => false

/-- One arm checked: its view, then its comparison to the result. -/
@[nospecialize] def summaryArmResult [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (f : PropKey) (B : Ty ι) (a : ι)
    (arm : SummaryArm ι) : CheckResult ι Unit :=
  (CheckResult.ofBool (summaryView G f a arm.view)).bind fun _ =>
    match arm.proof with
    | none => CheckResult.ofBool (decide (arm.view = B))
    | some p => checkSubtypeUsing G images arm.view B p

/-- A summary checked: exactly one arm per member of the receiver, each
member's arm checked. Unfinished subtype work is retained. -/
@[nospecialize] def checkReadSummaryResult [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (s : ReadSummary ι) : CheckResult ι Unit :=
  let ms := members G s.receiver
  (CheckResult.ofBool (ms.length == s.arms.length)).bind fun _ =>
    CheckResult.all (ms.zip s.arms) fun x => summaryArmResult G images s.field s.result x.1 x.2

@[nospecialize] def checkReadSummary [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (s : ReadSummary ι) : Bool :=
  (checkReadSummaryResult G images s).accepted

theorem summaryArmResult_accepted [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (f : PropKey) (B : Ty ι) (a : ι)
    (arm : SummaryArm ι) :
    (summaryArmResult G images f B a arm).accepted =
      (summaryView G f a arm.view && match arm.proof with
        | none => decide (arm.view = B)
        | some p => PositiveCertificates.checkUsing G images arm.view B p) := by
  unfold summaryArmResult
  rw [CheckResult.accepted_bind, CheckResult.accepted_ofBool]
  cases arm.proof with
  | none => rw [CheckResult.accepted_ofBool]
  | some p => rw [checkSubtypeUsing_accepted]

/-- The acceptance of a summary, as Booleans. -/
theorem checkReadSummary_eq [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (s : ReadSummary ι) :
    checkReadSummary G images s =
      ((members G s.receiver).length == s.arms.length &&
        ((members G s.receiver).zip s.arms).all fun x =>
          summaryView G s.field x.1 x.2.view && match x.2.proof with
            | none => decide (x.2.view = s.result)
            | some p => PositiveCertificates.checkUsing G images x.2.view s.result p) := by
  unfold checkReadSummary checkReadSummaryResult
  simp only [CheckResult.accepted_bind, CheckResult.accepted_ofBool, CheckResult.accepted_all,
    summaryArmResult_accepted]

/-- A table of read summaries is sound where each entry checks. The table
of a request is checked once (`checkReadSummaries`); a use looks an entry
up by index and checks only its own judgment. -/
def SummariesSound [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (sums : List (ReadSummary ι)) : Prop :=
  ∀ s ∈ sums, checkReadSummary G images s = true

theorem summariesSound_none [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) : SummariesSound G images [] := by
  intro s hs; cases hs

/-- Every entry of a table checked, unfinished subtype work retained. -/
@[nospecialize] def checkReadSummariesResult [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (sums : List (ReadSummary ι)) : CheckResult ι Unit :=
  CheckResult.all sums (checkReadSummaryResult G images)

theorem checkReadSummaries_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {sums : List (ReadSummary ι)}
    (h : (checkReadSummariesResult G images sums).accepted = true) : SummariesSound G images sums := by
  intro s hs
  rw [checkReadSummariesResult, CheckResult.accepted_all, List.all_eq_true] at h
  exact h s hs

inductive Rule (ι : Type) where
  | var | nul | undef | tru | fls | truLit | flsLit | numLit | num | strLit | str
  | bigintLit | bigint
  /-- Graph code: its captures, each a slot of the context at the type the
  code was checked with, are the premises; the code itself is an entry of the
  unit's checked code table. With a rest, `arrays` are the rest-store types of
  the variadic signatures, in their order. -/
  | funGraph (arrays : List (Ty ι))
  /-- A recursive closure: graph code of fixed arity whose table entries are
  checked with its self entry, at the closure's own type, after its
  captures; the captures are the premises. -/
  | funGraphSelf
  /-- A class value: construct-only graph code, checked at each construct
  signature with `undef`, the `undefined` type, for its receiver. -/
  | ctorGraph (undef : Ty ι)
  /-- A callable object: the bag's fields, then the captures of its graph
  code; `arrays` as for `funGraph`. -/
  | callableGraph (arrays : List (Ty ι))
  | app (effect : Effect)
  | letE | alloc | read | readView | write | arith | test
  /-- A read through an index over `keys`. -/
  | readDict (keys : IndexKeys) (element undef : Ty ι)
  /-- A computed read through an index over `keys`, of a key of `keyKeys`'s
  key clause. -/
  | indexDict (keys keyKeys : IndexKeys) (element undef : Ty ι)
  | readOptional (element undef : Ty ι)
  /-- A read through the prototype: the prototype's type. -/
  | readProto (proto : Ty ι)
  | arrLit | elem | setElem | len
  /-- A string's `length`. -/
  | lenStr
  /-- A string's code unit at a numeric index: the string and `undefined`
  types of the result. -/
  | elemStr (str undef : Ty ι)
  | elemOpt (undef : Ty ι)
  | elemAny (undef : Ty ι)
  | ifBool | ifTrue | ifFalse
  | ifKnown (answer : Bool)
  | ifBoolVar (trueType falseType : Ty ι)
  | unionVar (slot : Nat)
  | callCallable (effect : Effect)
  | readCallable | readBagView | writeCallable
  /-- A literal with spreads, at its element type: which parts are spreads. -/
  | arrParts (elem : Ty ι) (spreads : List Bool)
  /-- How many actuals are fixed, which later ones are spreads, and the rest
  type the further ones fit. -/
  | callRest (effect : Effect) (fixed omitted : Nat) (spreads : List Bool) (rest : Ty ι)
  /-- How many actuals are fixed before a spread of a value of the packed
  binder the rest is. -/
  | callPacked (effect : Effect) (fixed : Nat) (packed : ι) (rest : Ty ι)
  /-- A bound function: its saved slots are read from the context. -/
  | bindE
  /-- A bound variadic function, likewise. -/
  | bindRestE
  /-- A member read from a slot's object and bound to that same object: for
  each fixed signature of the result, proofs that a member signature covers it,
  one per parameter, then the result; for each variadic signature, likewise,
  one per fixed parameter, then the rest, then the result; and one proof per
  type the member's host must meet, that the object's type is within it; or,
  with no proofs, the result one of the member's quantified signatures, a
  scheme. -/
  | bindMember (proofs : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι))
      (rests : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι × PositiveCertificates.SubtypeChoices ι))
      (receivers : List (PositiveCertificates.SubtypeChoices ι))
  /-- `new`: the constructor, then the actuals in order, at the selected
  construct signature, whose effect is `effect`. -/
  | construct (effect : Effect)
  /-- `new` at a variadic construct signature: how many actuals are fixed,
  which later ones are spreads, and the rest type the further ones fit. -/
  | constructRest (fixed : Nat) (spreads : List Bool) (rest : Ty ι)
  | sub (proof : PositiveCertificates.SubtypeChoices ι)
  /-- `throw`: its operand at a type of its own. -/
  | throw
  /-- An allocation from parts: the accumulator, then the source. -/
  | merge
  /-- An allocation at a computed key: the key, then the initializer. -/
  | makeKey
  /-- `length` through a view of the object in a slot (`lengthRead`). -/
  | lenView (slot : Nat)
  /-- A read of a slot's object at the entry `index` of the request's read
  summaries, whose receiver is the slot's type (`readSummary_sound`). -/
  | readSummary (index : Nat)

inductive Evidence (ι : Type) where
  | node (claim : Sequent ι) (rule : Rule ι) (premises : List (Evidence ι))

@[nospecialize] def claim : Evidence ι → Sequent ι
  | .node j _ _ => j

/-- The slots a prefix of saved variables names, when every entry is one. -/
def varSlots : List Tm → Option (List Nat)
  | [] => some []
  | .var i :: ts => (varSlots ts).map (i :: ·)
  | _ :: _ => none

theorem varSlots_eq : ∀ {ts : List Tm} {saved : List Nat}, varSlots ts = some saved →
    ts = saved.map .var
  | [], _, h => by simp [varSlots] at h; subst h; rfl
  | .var i :: ts, saved, h => by
    simp only [varSlots, Option.map_eq_some_iff] at h
    obtain ⟨rest, hr, rfl⟩ := h
    simp [varSlots_eq hr]
  | .invoke .. :: _, _, h | .letE .. :: _, _, h | .nul :: _, _, h | .undef :: _, _, h
  | .tru :: _, _, h | .fls :: _, _, h | .num _ :: _, _, h | .str _ :: _, _, h
  | .objAt .. :: _, _, h | .makeAt .. :: _, _, h | .readAt .. :: _, _, h
  | .writeAt .. :: _, _, h | .test .. :: _, _, h | .ite .. :: _, _, h | .arith .. :: _, _, h
  | .arr _ :: _, _, h | .arrLit _ :: _, _, h | .elemAt .. :: _, _, h | .setElem .. :: _, _, h
  | .lenOf _ :: _, _, h | .spread _ :: _, _, h => by simp [varSlots] at h

/-- The captures of graph code are slots below `n`. -/
def capSlotsBelow (caps : List Tm) (n : Nat) : Bool :=
  match varSlots caps with
  | some slots => slots.all (· < n)
  | none => false

/-- The scheme row a type is, if it is one. -/
@[nospecialize] def schemeOf (G : NormalGraph ι) : Ty ι → Option (ι × SchemeRow ι)
  | [i] => if G.params i then none else (G.schemes i).map (i, ·)
  | _ => none

/-- Every signature `(L, S)` offers is a checked entry of graph code with
captures at `Cs` (`CodeOffers`): without a rest, each offered row; with one,
no fixed signature and each variadic signature with its store type from `As`. -/
@[nospecialize] def offersChecked [DecidableEq ι] (G : NormalGraph ι) (codes : CodeEntry ι → Bool) (arity : Nat)
    (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (rest : Bool) (L : List (Arrow (Ty ι)))
    (S : List (RestArrow (Ty ι))) (As : List (Ty ι)) : Bool :=
  match rest with
  | false => (offerRows L S).all fun p => codes ⟨arity, E, K, start, Cs, p, none⟩
  | true => L.isEmpty && S.length == As.length && (S.zip As).all fun q =>
      q.1.arguments.1.length == arity && decide (RestStore G q.2 q.1.arguments.2) &&
        codes ⟨arity, E, K, start, Cs, q.1.fixed, some q.2⟩

/-- Every signature the type `A` offers is a checked entry of graph code of
kind `kind` with captures at `Cs`, and one the kind offers (`KindOffers`): an
arrow type's signatures, or, for a generic closure, a scheme row's, whose
captures' types then read none of its binders. A table entry is checked at
every assignment of the parameter rows (`CodesSound`), so at every
instantiation of the scheme's binders. -/
@[nospecialize] def graphCodesChecked [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) (codes : CodeEntry ι → Bool)
    (kind : Invoke) (arity : Nat) (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target))
    (start : Nat) (Cs : List (Ty ι)) (rest : Bool) (As : List (Ty ι)) : Bool :=
  match schemeOf G A with
  | some (_, s) => !s.construct && capturesFree G s Cs && decide (KindOffers G kind s.signatures s.variadic) &&
      offersChecked G codes arity E K start Cs rest s.signatures s.variadic As
  | none =>
    match expand G A with
    | [.arrs L S] => decide (KindOffers G kind L S) && offersChecked G codes arity E K start Cs rest L S As
    | _ => false

/-- A recursive closure's signatures, each a checked entry of its graph code
of fixed arity with captures at `Cs` and the self entry at the closure's own
type `A` after them. -/
@[nospecialize] def graphCodesCheckedSelf [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) (codes : CodeEntry ι → Bool)
    (kind : Invoke) (arity : Nat) (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target))
    (start : Nat) (Cs : List (Ty ι)) : Bool :=
  match expand G A with
  | [.arrs L S] => decide (KindOffers G kind L S) && offersChecked G codes arity E K start (Cs ++ [A]) false L S []
  | _ => false

/-- A class value's construct signatures, each a checked entry of its graph
code at the row whose receiver is `U`, the `undefined` type `new` passes; a
variadic one with an element rest at the row `ctorRestParams` gives; and its
static fields, exactly `P`, each of the role `field` the class value's
allocation gives it. -/
@[nospecialize] def ctorCodesChecked [DecidableEq ι] (G : NormalGraph ι) (A U : Ty ι) (codes : CodeEntry ι → Bool)
    (arity : Nat) (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target))
    (start : Nat) (Cs : List (Ty ι)) (P : List (PropKey × Ty ι)) : Bool :=
  match expand G A with
  | [.ctors L S P' []] =>
      (P' == withRole .field P && L.all fun p => codes ⟨arity, E, K, start, Cs, ⟨U, p.arguments, p.result, p.effect⟩, none⟩) &&
      S.all fun s => s.effect.plain && match restElem G s.arguments.2 with
        | some El => codes ⟨arity, E, K, start, Cs,
            ⟨U, ctorRestParams arity s.arguments.1 El U, s.result, s.effect⟩, none⟩
        | none => false
  | _ => false

/-- The prototype type `P` has a field or view `f` at `A`. -/
@[nospecialize] def ProtoMember (G : NormalGraph ι) (P : Ty ι) (f : PropKey) (A : Ty ι) : Prop :=
  match expand G P with
  | [.refs gs [] ws _ _ _ _] => (f, A) ∈ Stored.views gs ++ ws.filter (·.1 != lengthKey)
  | _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (P : Ty ι) (f : PropKey) (A : Ty ι) :
    Decidable (ProtoMember G P f A) := by
  unfold ProtoMember; split <;> infer_instance

/-- Proofs that the member signature `c` covers the claimed `q`: each claimed
parameter within the member's, then the member's result within the claimed. -/
@[nospecialize] def CallProofsUsing [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G) (q : Arrow (Ty ι))
    (c : MethodArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι) : Prop :=
  q.arguments.length = c.arguments.length ∧ ps.1.length = c.arguments.length ∧
    (∀ x ∈ (q.arguments.zip c.arguments).zip ps.1, PositiveCertificates.checkUsing G images x.1.1 x.1.2 x.2 = true) ∧
    PositiveCertificates.checkUsing G images c.result q.result ps.2 = true ∧ c.effect.bindCovers 0 q.effect = true

instance [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (q c ps) : Decidable (CallProofsUsing G images q c ps) := by
  unfold CallProofsUsing; infer_instance

theorem CallProofsUsing.covered [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {q c ps}
    (h : CallProofsUsing G images q c ps) : CoveredCallUsing G images q c := by
  obtain ⟨hl, hp, hall, hr, he⟩ := h
  refine ⟨hl, fun x hx => ?_, ⟨_, hr⟩, he⟩
  obtain ⟨p, hxp⟩ := PositiveCertificates.exists_mem_zip (xs := q.arguments.zip c.arguments) (ys := ps.1)
    (by rw [List.length_zip, hl, Nat.min_self, hp]) x hx
  exact ⟨p, hall _ hxp⟩

/-- Proofs that the member's variadic signature `c` covers the claimed `q`:
each claimed fixed parameter within the member's, the claimed rest within the
member's, then the member's result within the claimed. -/
@[nospecialize] def RestProofsUsing [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (q : RestArrow (Ty ι)) (c : CallEffects.MethodRestArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι × PositiveCertificates.SubtypeChoices ι) : Prop :=
  q.arguments.1.length = c.arguments.1.length ∧ ps.1.length = c.arguments.1.length ∧
    (∀ x ∈ (q.arguments.1.zip c.arguments.1).zip ps.1, PositiveCertificates.checkUsing G images x.1.1 x.1.2 x.2 = true) ∧
    PositiveCertificates.checkUsing G images q.arguments.2 c.arguments.2 ps.2.1 = true ∧
    PositiveCertificates.checkUsing G images c.result q.result ps.2.2 = true ∧ c.effect.bindCovers 0 q.effect = true

instance [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (q c ps) : Decidable (RestProofsUsing G images q c ps) := by
  unfold RestProofsUsing; infer_instance

theorem RestProofsUsing.covered [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {q c ps}
    (h : RestProofsUsing G images q c ps) : CoveredRestUsing G images q c := by
  obtain ⟨hl, hp, hall, he, hr, heff⟩ := h
  refine ⟨hl, fun x hx => ?_, ⟨_, he⟩, ⟨_, hr⟩, heff⟩
  obtain ⟨p, hxp⟩ := PositiveCertificates.exists_mem_zip (xs := q.arguments.1.zip c.arguments.1) (ys := ps.1)
    (by rw [List.length_zip, hl, Nat.min_self, hp]) x hx
  exact ⟨p, hall _ hxp⟩

/-- Validate a fixed member signature, preserving each parameter/result comparison. -/
@[nospecialize] def checkCallProofs [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : Arrow (Ty ι)) (c : MethodArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι) : CheckResult ι Unit :=
  (CheckResult.ofBool (decide (q.arguments.length = c.arguments.length ∧
    ps.1.length = c.arguments.length) && c.effect.bindCovers 0 q.effect)).bind fun _ =>
    (CheckResult.all ((q.arguments.zip c.arguments).zip ps.1) fun x =>
      checkSubtypeUsing G images x.1.1 x.1.2 x.2).bind fun _ =>
      checkSubtypeUsing G images c.result q.result ps.2

theorem checkCallProofs_accepted [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : Arrow (Ty ι)) (c : MethodArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι) :
    (checkCallProofs G images q c ps).accepted = decide (CallProofsUsing G images q c ps) := by
  simp only [checkCallProofs, CheckResult.accepted_bind, CheckResult.accepted_ofBool,
    CheckResult.accepted_all, checkSubtypeUsing_accepted]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  unfold CallProofsUsing
  simp only [and_assoc, and_left_comm, and_comm]

/-- Validate a variadic member signature, including its rest and result. -/
@[nospecialize] def checkRestProofs [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : RestArrow (Ty ι))
    (c : CallEffects.MethodRestArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
      PositiveCertificates.SubtypeChoices ι) : CheckResult ι Unit :=
  (CheckResult.ofBool (decide (q.arguments.1.length = c.arguments.1.length ∧
    ps.1.length = c.arguments.1.length) && c.effect.bindCovers 0 q.effect)).bind fun _ =>
    (CheckResult.all ((q.arguments.1.zip c.arguments.1).zip ps.1) fun x =>
      checkSubtypeUsing G images x.1.1 x.1.2 x.2).bind fun _ =>
    (checkSubtypeUsing G images q.arguments.2 c.arguments.2 ps.2.1).bind fun _ =>
      checkSubtypeUsing G images c.result q.result ps.2.2

theorem checkRestProofs_accepted [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : RestArrow (Ty ι))
    (c : CallEffects.MethodRestArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
      PositiveCertificates.SubtypeChoices ι) :
    (checkRestProofs G images q c ps).accepted = decide (RestProofsUsing G images q c ps) := by
  simp only [checkRestProofs, CheckResult.accepted_bind, CheckResult.accepted_ofBool,
    CheckResult.accepted_all, checkSubtypeUsing_accepted]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  unfold RestProofsUsing
  simp only [and_assoc, and_left_comm, and_comm]

/-- The bound member covers each claimed signature and accepts the host receiver. -/
@[nospecialize] def MemberProofsUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (host : Option (Ty ι)) (F : Ty ι) (k : PropKey)
    (proofs : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι))
    (rests : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
      PositiveCertificates.SubtypeChoices ι)) (receivers : List (PositiveCertificates.SubtypeChoices ι)) : Prop :=
  match host, expand G F with
  | some O, [.arrs L S] => ∃ m ∈ (memberOf G O k).toList,
      proofs.length = L.length ∧ (∀ qp ∈ L.zip proofs, ∃ c ∈ m.calls, CallProofsUsing G images qp.1 c qp.2) ∧
      rests.length = S.length ∧ (∀ sp ∈ S.zip rests, ∃ c ∈ m.rests, RestProofsUsing G images sp.1 c sp.2) ∧
      receivers.length = m.receivers.length ∧
      (∀ tp ∈ m.receivers.zip receivers, PositiveCertificates.checkUsing G images O tp.1 tp.2 = true)
  | some O, _ => proofs = [] ∧ rests = [] ∧ receivers = [] ∧ expand G F = [] ∧
      ∃ m ∈ (memberOf G O k).toList, F ∈ m.schemes
  | none, _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (host F k proofs rests receivers) : Decidable (MemberProofsUsing G images host F k proofs rests receivers) := by
  unfold MemberProofsUsing
  split <;> infer_instance

/-- Check every signature using alternatives only among actual member signatures. -/
@[nospecialize] def checkMemberProofs [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (host : Option (Ty ι)) (F : Ty ι) (k : PropKey)
    (proofs : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι))
    (rests : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
      PositiveCertificates.SubtypeChoices ι)) (receivers : List (PositiveCertificates.SubtypeChoices ι)) : CheckResult ι Unit :=
  match host, expand G F with
  | some O, [.arrs L S] => CheckResult.any (memberOf G O k).toList fun m =>
      (CheckResult.ofBool (decide (proofs.length = L.length ∧ rests.length = S.length ∧
        receivers.length = m.receivers.length))).bind fun _ =>
      (CheckResult.all (L.zip proofs) fun qp =>
        CheckResult.any m.calls fun c => checkCallProofs G images qp.1 c qp.2).bind fun _ =>
      (CheckResult.all (S.zip rests) fun sp =>
        CheckResult.any m.rests fun c => checkRestProofs G images sp.1 c sp.2).bind fun _ =>
      CheckResult.all (m.receivers.zip receivers) fun tp => checkSubtypeUsing G images O tp.1 tp.2
  | some O, _ => CheckResult.ofBool (decide (proofs = [] ∧ rests = [] ∧ receivers = [] ∧ expand G F = [] ∧
      ∃ m ∈ (memberOf G O k).toList, F ∈ m.schemes))
  | none, _ => failure

theorem checkMemberProofs_accepted [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (host : Option (Ty ι)) (F : Ty ι) (k : PropKey)
    (proofs : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι))
    (rests : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
      PositiveCertificates.SubtypeChoices ι)) (receivers : List (PositiveCertificates.SubtypeChoices ι)) :
    (checkMemberProofs G images host F k proofs rests receivers).accepted =
      decide (MemberProofsUsing G images host F k proofs rests receivers) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  unfold checkMemberProofs MemberProofsUsing
  unfold CheckResult.accepted
  split
  · change (CheckResult.any _ _).accepted = true ↔ _
    simp only [CheckResult.accepted_any, CheckResult.accepted_bind, CheckResult.accepted_ofBool,
      CheckResult.accepted_all, checkSubtypeUsing_accepted, checkCallProofs_accepted, checkRestProofs_accepted]
    simp only [List.any_eq_true, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨m, hm, ⟨hp, hs, hr⟩, hcalls, hrests, hreceivers⟩
      exact ⟨m, hm, hp, hcalls, hs, hrests, hr, hreceivers⟩
    · rintro ⟨m, hm, hp, hcalls, hs, hrests, hr, hreceivers⟩
      exact ⟨m, hm, ⟨hp, hs, hr⟩, hcalls, hrests, hreceivers⟩
  · rw [← CheckResult.accepted, CheckResult.accepted_ofBool, decide_eq_true_eq]
  · change (false = true) ↔ False
    simp

/-- Each top-level label of a type replaced by the label it is aliased to. -/
@[nospecialize] def renameTy [DecidableEq ι] (aliases : List (ι × ι)) (A : Ty ι) : Ty ι :=
  A.map fun l => match aliases.find? (·.1 == l) with
    | some p => p.2
    | none => l

/-- Aliased labels denote the same values at every assignment the enclosing
scheme admits within its declared bounds. -/
def AliasesSound (G : NormalGraph ι) (source : SchemeRow ι) (aliases : List (ι × ι)) : Prop :=
  ∀ η As, As.length = source.binders.length → G.domain.allowed source As →
    (∀ m, Bounded (mixedMeaning G) η source As m) →
    ∀ p ∈ aliases, ∀ n W v,
      mixedMeaning G (assign η source.binders As) [p.1] n W (.inl v) ↔
        mixedMeaning G (assign η source.binders As) [p.2] n W (.inl v)

theorem renameTy_meaning [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {aliases : List (ι × ι)}
    (same : ∀ p ∈ aliases, ∀ n W v,
      mixedMeaning G η [p.1] n W (.inl v) ↔ mixedMeaning G η [p.2] n W (.inl v))
    (A : Ty ι) (n W v) :
    mixedMeaning G η (renameTy aliases A) n W (.inl v) ↔ mixedMeaning G η A n W (.inl v) := by
  let X := fun i => qDenoteWithArgs G (mixedParameters G) (η, i)
  have single : ∀ l, mixedMeaning G η [l] n W (.inl v) ↔ X l n W v := by
    intro l
    change (∃ i ∈ [l], X i n W v) ↔ _
    simp
  have label : ∀ l, X (match aliases.find? (·.1 == l) with
      | some p => p.2
      | none => l) n W v ↔ X l n W v := by
    intro l
    split
    · rename_i p hp
      have hm := List.mem_of_find?_eq_some hp
      have he : p.1 = l := by simpa using List.find?_some hp
      rw [← single, ← single, ← (same p hm n W v), he]
    · exact Iff.rfl
  change (∃ i ∈ renameTy aliases A, X i n W v) ↔ (∃ i ∈ A, X i n W v)
  simp only [renameTy, List.mem_map]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, hv⟩
    exact ⟨l, hl, (label l).mp hv⟩
  · rintro ⟨l, hl, hv⟩
    exact ⟨_, ⟨l, hl, rfl⟩, (label l).mpr hv⟩

/-- Body subsumption without aliases: an ordinary comparison, or a qualified
callable instantiated with the complete resolution group from its enclosing
scheme. Ordinary comparisons and all instance-image, kind, signature and bound
checks use the shared checker. -/
@[nospecialize] def lexicalComparison [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (source : SchemeRow ι)
    (A B : Ty ι) (proof : PositiveCertificates.SubtypeChoices ι) : Bool :=
  PositiveCertificates.checkUsing G images A B proof ||
    match expand G B, proof.instantiation with
    | [.arrs L M], some inst =>
      (QualifiedGraphs.compareLexicalInstance G images source
        (fun U V state => (PositiveCertificates.ComparisonResult.fromBool
          (PositiveCertificates.checkUsing G images U V proof), state))
        () A L M inst ()).1.accepted
    | _, _ => false

/-- Body subsumption compares the two types as they are or, failing that,
with each aliased label read as its alias. -/
@[nospecialize] def lexicalBodyCheck [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (source : SchemeRow ι)
    (aliases : List (ι × ι)) (A B : Ty ι) (proof : PositiveCertificates.SubtypeChoices ι) : Bool :=
  lexicalComparison G images source A B proof ||
    (!aliases.isEmpty &&
      lexicalComparison G images source (renameTy aliases A) (renameTy aliases B) proof)

/-- Body subsumption admits every ordinary comparison: a read summary's
comparisons, made by the ordinary checker, hold in a qualified body. -/
theorem lexicalBodyCheck_ordinary [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {source : SchemeRow ι}
    {aliases : List (ι × ι)} {A B : Ty ι} {proof : PositiveCertificates.SubtypeChoices ι}
    (h : PositiveCertificates.checkUsing G images A B proof = true) :
    lexicalBodyCheck G images source aliases A B proof = true := by
  simp [lexicalBodyCheck, lexicalComparison, h]

theorem lexicalComparison_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {source : SchemeRow ι}
    {N : Fam} {C : ResolutionDescriptors.Capabilities (excOf G) N}
    (domain : G.domain = ResolutionDescriptors.descriptorDomain C)
    (η : MixedAssignment ι) (As : List MixedFamily)
    (length : As.length = source.binders.length) (allowed : G.domain.allowed source As)
    {A B : Ty ι} {proof : PositiveCertificates.SubtypeChoices ι}
    (checked : lexicalComparison G images source A B proof = true) (n W v)
    (hv : mixedMeaning G (assign η source.binders As) A n W (.inl v)) :
    mixedMeaning G (assign η source.binders As) B n W (.inl v) := by
  simp only [lexicalComparison, Bool.or_eq_true] at checked
  rcases checked with ordinary | lexical
  · exact PositiveCertificates.checkUsing_sound ordinary
      (assign η source.binders As) n W (.inl v) hv
  · split at lexical
    · rename_i L M inst target instanced
      have bounds : ∀ U V (prior : Unit),
          (PositiveCertificates.ComparisonResult.fromBool
            (PositiveCertificates.checkUsing G images U V proof)).accepted = true →
          FamLe (mixedMeaning G (assign η source.binders As) U)
            (mixedMeaning G (assign η source.binders As) V) := by
        intro U V _ h
        exact PositiveCertificates.checkUsing_sound
          (by simpa only [PositiveCertificates.ComparisonResult.accepted_fromBool] using h) _
      have step := QualifiedGraphs.compareLexicalInstance_sound G images source domain
        η As length allowed (fun _ _ _ h => h) bounds lexical
      exact mixed_of_expand target (step n W v hv)
    · cases lexical

/-- The lexical check supplies precisely the subsumption premise consumed by
program typing, at an assignment permitted by the enclosing scheme within its
declared bounds. -/
@[nospecialize] def lexicalBodySubtyping [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (source : SchemeRow ι)
    {N : Fam} {C : ResolutionDescriptors.Capabilities (excOf G) N}
    (domain : G.domain = ResolutionDescriptors.descriptorDomain C)
    (aliases : List (ι × ι)) (aliasesSound : AliasesSound G source aliases)
    (η : MixedAssignment ι) (As : List MixedFamily)
    (length : As.length = source.binders.length) (allowed : G.domain.allowed source As)
    (bounded : ∀ m, Bounded (mixedMeaning G) η source As m) :
    BodySubtyping (reassign G (assign η source.binders As)) where
  check := lexicalBodyCheck G images source aliases
  sound := by
    intro A B proof checked
    simp only [lexicalBodyCheck, Bool.or_eq_true, Bool.and_eq_true] at checked
    rcases checked with direct | ⟨_, renamed⟩
    · exact fun n W v hv => lexicalComparison_sound domain η As length allowed direct n W v hv
    · have same := aliasesSound η As length allowed bounded
      intro n W v hv
      exact (renameTy_meaning same B n W v).mp
        (lexicalComparison_sound domain η As length allowed renamed n W v
          ((renameTy_meaning same A n W v).mpr hv))

/-- Only finite, syntactic premises of one rule. -/
@[nospecialize] def LocalUsing [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G) (j : Sequent ι) (r : Rule ι) (ps : List (Sequent ι))
    (codes : CodeEntry ι → Bool := fun _ => false)
    (subtype : Ty ι → Ty ι → PositiveCertificates.SubtypeChoices ι → Bool :=
      PositiveCertificates.checkUsing G images)
    (sums : List (ReadSummary ι) := []) (allowRequires : Bool := false) : Prop :=
  match r with
  | .var =>
    match j.term, ps with
    | .var i, [] => j.context[i]? = some j.type
    | _, _ => False
  | .nul =>
    match j.term, ps with
    | .nul, [] => Represents G j.type .nul
    | _, _ => False
  | .undef =>
    match j.term, ps with
    | .undef, [] => Represents G j.type .undef
    | _, _ => False
  | .tru =>
    match j.term, ps with
    | .tru, [] => Represents G j.type .bool
    | _, _ => False
  | .fls =>
    match j.term, ps with
    | .fls, [] => Represents G j.type .bool
    | _, _ => False
  | .truLit =>
    match j.term, ps with
    | .tru, [] => Represents G j.type (.boolLit true)
    | _, _ => False
  | .flsLit =>
    match j.term, ps with
    | .fls, [] => Represents G j.type (.boolLit false)
    | _, _ => False
  | .numLit =>
    match j.term, ps with
    | .num b, [] => Represents G j.type (.numLit b)
    | _, _ => False
  | .num =>
    match j.term, ps with
    | .num _, [] => Represents G j.type .num
    | _, _ => False
  | .strLit =>
    match j.term, ps with
    | .str s, [] => Represents G j.type (.strLit s)
    | _, _ => False
  | .str =>
    match j.term, ps with
    | .str _, [] => Represents G j.type .str
    | _, _ => False
  | .bigintLit =>
    match j.term, ps with
    | .bigint i, [] => Represents G j.type (.bigintLit i)
    | _, _ => False
  | .bigint =>
    match j.term, ps with
    | .bigint _, [] => Represents G j.type .bigint
    | _, _ => False
  -- Graph code: one premise per capture, a slot of this context, at the type
  -- the code's table entry states; every signature the type offers is an
  -- entry of the unit's checked table.
  | .funGraph As =>
    match j.term, ps with
    | .makeAt (.graph arity E K start caps kind rest) ns inits, ps =>
      ns = [codeField] ∧ inits = [Tm.nul] ∧ ps.map Sequent.term = caps ∧
      (∀ q ∈ ps, q.context = j.context) ∧ capSlotsBelow caps j.context.length = true ∧
      graphCodesChecked G j.type codes kind arity E K start (ps.map Sequent.type) rest As = true
    | _, _ => False
  -- A recursive closure: as graph code, of fixed arity, its entries checked
  -- with the self entry after the captures.
  | .funGraphSelf =>
    match j.term, ps with
    | .makeAt (.graph arity E K start caps kind false) ns inits, ps =>
      ns = [codeField] ∧ inits = [Tm.nul] ∧ ps.map Sequent.term = caps ∧
      (∀ q ∈ ps, q.context = j.context) ∧ capSlotsBelow caps j.context.length = true ∧
      graphCodesCheckedSelf G j.type codes kind arity E K start (ps.map Sequent.type) = true
    | _, _ => False
  -- A class value: as a function's code, construct-only, at its construct
  -- signatures with `undefined` for the receiver; its code field, then one
  -- premise per static field, then one per capture.
  | .ctorGraph U =>
    match j.term, ps with
    | .makeAt (.graph arity E K start caps kind rest) (f :: ns) (.nul :: inits), ps =>
      kind = .construct ∧ rest = false ∧ f = codeField ∧ (f :: ns).Nodup ∧ ns.length = inits.length ∧
      (ps.take ns.length).map Sequent.term = inits ∧
      (∀ q ∈ ps, q.context = j.context) ∧
      (ps.drop ns.length).map Sequent.term = caps ∧ capSlotsBelow caps j.context.length = true ∧
      Represents G U .undef ∧
      ctorCodesChecked G j.type U codes arity E K start ((ps.drop ns.length).map Sequent.type)
        (ns.zip ((ps.take ns.length).map Sequent.type)) = true
    | _, _ => False
  -- A callable object: one premise per named field, then one per capture.
  | .callableGraph As =>
    match j.term, ps with
    | .makeAt (.graph arity E K start caps kind rest) ns inits, ps =>
      match expand G j.type with
      | [.callable P [] L S] =>
        KindOffers G kind L S ∧ ns.Nodup ∧ ns.length = inits.length ∧
        (ps.take ns.length).map Sequent.term = inits ∧
        (∀ p ∈ ps, p.context = j.context) ∧
        P = withRole .field (ns.zip ((ps.take ns.length).map Sequent.type)) ∧
        (ps.drop ns.length).map Sequent.term = caps ∧ capSlotsBelow caps j.context.length = true ∧
        offersChecked G codes arity E K start ((ps.drop ns.length).map Sequent.type) rest L S As = true
      | _ => False
    | _, _ => False
  -- The callee, then the receiver at the selected signature's receiver, then
  -- the actual premises in order, then one premise per position the signature
  -- declares and this call omits. Each of those proves `undefined` at its
  -- declared type: the value the machine binds there.
  | .app effect =>
    match j.term, ps with
    | .invoke f r args, jf :: jr :: jas =>
      jf.context = j.context ∧ jf.term = f ∧ jr.context = j.context ∧ jr.term = r ∧
      (jas.take args.length).map Sequent.term = args ∧
      (∀ ja ∈ jas.drop args.length, ja.term = .undef) ∧
      (∀ ja ∈ jas, ja.context = j.context) ∧
      match expand G jf.type with
      | [.arrs L _] => ⟨jr.type, jas.map Sequent.type, j.type, effect⟩ ∈ L ∧
          effect.promise = none ∧ (allowRequires = true ∨ (effect.requires = none ∧ effect.pre = []))
      | _ => False
    | _, _ => False
  | .letE =>
    match j.term, ps with
    | .letE a b, [ja, jb] =>
      ja.context = j.context ∧ ja.term = a ∧ jb = ⟨ja.type :: j.context, b, j.type⟩
    | _, _ => False
  | .alloc =>
    match j.term, ps with
    | .makeAt .absent ns inits, ps =>
      match expand G j.type with
      -- A field among the stable keys is a view, allocated at its initial
      -- value alone (`HasTyUsing.alloc`).
      | [.refs fs [] vs [] [] ks st] =>
        ns.Nodup ∧ hostKey ∉ ns ∧ ns.length = ps.length ∧ ps.map Sequent.term = inits ∧
        (∀ p ∈ ps, p.context = j.context) ∧
        Stored.views fs = stablePart st false (ns.zip (ps.map Sequent.type)) ∧
        vs = stablePart st true (ns.zip (ps.map Sequent.type)) ∧
        (∀ K ∈ ks, ∀ n ∈ ns, K.admits n = true) ∧ allocBuiltinsUsing images (ns.zip (ps.map Sequent.type)) = true ∧
        (st = [] ∨ CallArguments.arrayStoreField ∉ ns) ∧ (∀ k ∈ st, k ∈ ns)
      -- A literal allocated directly at a dictionary: each field an index's
      -- class may admit at exactly that index's type, each optional field
      -- absent (`HasTyUsing.allocDict`).
      | [.dict fs [] [] ix os [] [] cs] =>
        ns.Nodup ∧ CallArguments.protoField ∉ ns ∧ CallArguments.arrayStoreField ∉ ns ∧ hostKey ∉ ns ∧
        ns.length = ps.length ∧ ps.map Sequent.term = inits ∧
        (∀ p ∈ ps, p.context = j.context) ∧ Stored.views fs = ns.zip (ps.map Sequent.type) ∧
        (∀ f ∈ fs, ∀ y ∈ ix ++ cellViews cs, y.1.may f.1 = true → f.2.2 = y.2) ∧
        (∀ o ∈ os, o.key ∉ ns) ∧
        (∀ o ∈ os, ∀ y ∈ cs, y.1.may o.key = true → o.type = y.2.2 ∨ PositiveRules.Uninhabited G y.2.2)
      | _ => False
    | _, _ => False
  | .read =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧
      (match expand G ja.type with
       | [c] => (f, j.type) ∈ ((namedMembers c).map fun m => Stored.views m.1).getD []
       | _ => False)
    | _, _ => False
  | .readView =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧ (f ≠ lengthKey ∨ lengthExcluded G j.type = true) ∧
      (match expand G ja.type with
       | [c] => (f, j.type) ∈ ((namedMembers c).map Prod.snd).getD []
       | _ => False)
    | _, _ => False
  -- A key a bound of the object does not admit is read from its prototype `P`, which
  -- the object holds under the reserved key; `P`'s field or view gives the type.
  | .readProto P =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧
      (match expand G ja.type with
       | [.refs fs [] vs _ _ ks _] =>
         (∃ K ∈ ks, K.admits f = false) ∧ (CallArguments.protoField, P) ∈ Stored.views fs ++ vs ∧
         ProtoMember G P f j.type
       | _ => False)
    | _, _ => False
  | .readOptional A U =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧ Represents G U .undef ∧ j.type = A ++ U ∧
      inheritedKey f = false ∧
      (match expand G ja.type with
       | [.refs _ [] _ os _ _ _] => ∃ o ∈ os, o.key = f ∧ o.type = A
       | _ => False)
    | _, _ => False
  | .readDict K A U =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧ Represents G U .undef ∧ j.type = A ++ U ∧
      K.surely f = true ∧ inheritedKey f = false ∧
      (match expand G ja.type with
       | [.dict _ [] _ ix _ _ _ _ _] => (K, A) ∈ ix
       | _ => False)
    | _, _ => False
  | .indexDict K KK A U =>
    match j.term, ps with
    | .indexAt a key, [ja, jk] =>
      ja.context = j.context ∧ ja.term = a ∧
      jk.context = j.context ∧ jk.term = key ∧
      Represents G jk.type (keyClause KK) ∧ KK.within K = true ∧
      Represents G U .undef ∧ j.type = A ++ U ∧ KK ≠ .strings ∧
      (match expand G ja.type with
       | [.dict _ [] _ ix _ _ _ _ _] => (K, A) ∈ ix
       | _ => False)
    | _, _ => False
  | .write =>
    match j.term, ps with
    | .writeAt f a b, [ja, jb] =>
      ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
      Represents G j.type .nul ∧
      (match expand G ja.type with
       | [.refs fs [] _ _ _ _ _] => (f, jb.type) ∈ Stored.views fs
       | _ => False)
    | _, _ => False
  | .arith =>
    match j.term, ps with
    | .arith op a b, [ja, jb] =>
      ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
      OperatorTypes G op ja.type jb.type j.type
    | _, _ => False
  | .test =>
    match j.term, ps with
    | .test _ a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧
      (.boolLit true) ∈ expand G j.type ∧ (.boolLit false) ∈ expand G j.type
    | _, _ => False
  | .arrLit =>
    match j.term, ps with
    | .arrLit inits, ps =>
      match expand G j.type with
      | [.list T []] =>
        ps.map Sequent.term = inits ∧ (∀ p ∈ ps, p.context = j.context) ∧
        T.required.length ≤ ps.length ∧
        (T.rest = none → ps.length ≤ T.required.length + T.optional.length) ∧
        ∀ q ∈ ps.zipIdx, positionTy T q.2 = some q.1.type
      | _ => False
    | _, _ => False
  | .elem =>
    match j.term, ps with
    | .elemAt a i, [ja, ji] =>
      ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
      (match expand G ja.type, expand G ji.type with
       | [.list T []], [.numLit b] => requiredAt T b = some j.type
       | _, _ => False)
    | _, _ => False
  | .elemOpt U =>
    match j.term, ps with
    | .elemAt a i, [ja, ji] =>
      ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
      Represents G U .undef ∧
      (match expand G ja.type, expand G ji.type with
       | [.list T []], [.numLit b] => optionalAt T b U = some j.type
       | _, _ => False)
    | _, _ => False
  | .elemAny U =>
    match j.term, ps with
    | .elemAt a i, [ja, ji] =>
      ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
      Represents G U .undef ∧ Answers G ji.type .isNum true ∧
      (match expand G ja.type with
       | [.list ⟨[], [], some E, _, _⟩ []] => j.type = E ++ U
       | _ => False)
    | _, _ => False
  | .setElem =>
    match j.term, ps with
    | .setElem a i v, [ja, ji, jv] =>
      ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
      jv.context = j.context ∧ jv.term = v ∧ j.type = ja.type ∧
      (match expand G ja.type, expand G ji.type with
       | [.list T []], [.numLit b] =>
         -- At most the required length: in bounds or appending, never a hole.
         namedAt T b = some jv.type ∧ (indexOfBits b).getD 0 ≤ T.required.length ∧
           T.readonly = false
       | _, _ => False)
    | _, _ => False
  | .len =>
    match j.term, ps with
    | .lenOf a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧ Represents G j.type .num ∧
      (match expand G ja.type with
       | [.list _ []] => True
       | _ => False)
    | _, _ => False
  | .lenStr =>
    match j.term, ps with
    | .lenOf a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧ Represents G j.type .num ∧
      Answers G ja.type .isStr true
    | _, _ => False
  | .elemStr T U =>
    match j.term, ps with
    | .elemAt a i, [ja, ji] =>
      ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
      Answers G ja.type .isStr true ∧ Answers G ji.type .isNum true ∧
      Represents G T .str ∧ Represents G U .undef ∧ j.type = T ++ U
    | _, _ => False
  | .ifBool =>
    match j.term, ps with
    | .ite c t e, [jc,jt,je] =>
      jc.context = j.context ∧ jc.term = c ∧ Answers G jc.type .isBool true ∧
      jt = ⟨j.context,t,j.type⟩ ∧ je = ⟨j.context,e,j.type⟩
    | _, _ => False
  | .ifKnown q =>
    match j.term, ps with
    | .ite c t e, [jc,jb] =>
      jc.context = j.context ∧ jc.term = c ∧ Represents G jc.type (.boolLit q) ∧
      jb = ⟨j.context, (if q then t else e), j.type⟩
    | _, _ => False
  | .ifBoolVar T F =>
    match j.term, ps with
    | .ite (.var i) t e, [jt,je] =>
      (match j.context[i]? with | some C => Answers G C .isBool true | none => False) ∧
      Represents G T (.boolLit true) ∧ Represents G F (.boolLit false) ∧
      jt = ⟨j.context.set i T,t,j.type⟩ ∧ je = ⟨j.context.set i F,e,j.type⟩
    | _, _ => False
  | .ifTrue =>
    match j.term, ps with
    | .ite (.test tag (.var i)) u _, [ju] =>
      ju = ⟨j.context, u, j.type⟩ ∧
      match j.context[i]? with
      | some A => Answers G A tag true
      | none => False
    | _, _ => False
  | .ifFalse =>
    match j.term, ps with
    | .ite (.test tag (.var i)) _ e, [je] =>
      je = ⟨j.context, e, j.type⟩ ∧
      match j.context[i]? with
      | some A => Answers G A tag false
      | none => False
    | _, _ => False
  | .unionVar i =>
    match j.term, ps with
    | _, ps =>
      match j.context[i]? with
      | some C => ps = (members G C).map (fun a => ⟨j.context.set i [a], j.term, j.type⟩)
      | none => False
  | .callCallable effect =>
    match j.term, ps with
    | .invoke f r args, jf :: jr :: jas =>
      jf.context = j.context ∧ jf.term = f ∧ jr.context = j.context ∧ jr.term = r ∧
      (jas.take args.length).map Sequent.term = args ∧
      (∀ ja ∈ jas.drop args.length, ja.term = .undef) ∧
      (∀ ja ∈ jas, ja.context = j.context) ∧
      match expand G jf.type with
      | [.callable _ _ L _ _] => ⟨jr.type, jas.map Sequent.type,j.type, effect⟩ ∈ L ∧ effect.plain = true
      | _ => False
    | _, _ => False
  -- A field of a callable object's bag or of a class value's statics.
  | .readCallable =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧
      match expand G ja.type with
      | [c] => (f, j.type) ∈ Stored.views c.bagFields
      | _ => False
    | _, _ => False
  -- A readonly static field of a class value.
  | .readBagView =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧
      match expand G ja.type with
      | [c] => (f, j.type) ∈ c.bagViews
      | _ => False
    | _, _ => False
  | .writeCallable =>
    match j.term, ps with
    | .writeAt f a b, [ja,jb] =>
      ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
      Represents G j.type .nul ∧
      match expand G ja.type with
      | [c] => (f, jb.type) ∈ Stored.views c.bagFields
      | _ => False
    | _, _ => False
  -- One premise per part: the entry itself, at the element type, or, for a
  -- part flagged as a spread, the store it reads, whose elements that type
  -- admits.
  | .arrParts E flags =>
    match j.term with
    | .arrLit args =>
      (∀ jp ∈ ps, jp.context = j.context) ∧ ps.length = flags.length ∧
      args = (flags.zip ps).map (fun q => spreadTerm (q.1, q.2.term)) ∧
      (∀ q ∈ flags.zip ps, if q.1 then SpreadsInto G q.2.type E else q.2.type = E) ∧
      match expand G j.type with
      | [.list ⟨[], [], some E', _, _⟩ []] => E = E'
      | _ => False
    | _ => False
  -- The callee, the receiver, the fixed actuals, one `undefined` premise per
  -- fixed position the call omits, then one premise per further part: the
  -- actual itself, or the store a spread reads. A call that omits a position
  -- writes no part.
  | .callRest effect k u flags P =>
    match j.term, ps with
    | .invoke f r args, jf :: jr :: jas =>
      jf.context = j.context ∧ jf.term = f ∧ jr.context = j.context ∧ jr.term = r ∧
      (∀ ja ∈ jas, ja.context = j.context) ∧
      jas.length = k + u + flags.length ∧ (u = 0 ∨ flags = []) ∧
      args = (jas.take k).map Sequent.term ++
        (flags.zip (jas.drop (k + u))).map (fun q => spreadTerm (q.1, q.2.term)) ∧
      (∀ ja ∈ (jas.drop k).take u, ja.term = .undef) ∧
      RestParts G P ((flags.zip (jas.drop (k + u))).map fun q => (q.1, q.2.type)) ∧
      ⟨jr.type, ((jas.take (k + u)).map Sequent.type, P), j.type, effect⟩ ∈ restSigs G jf.type ∧
      effect.plain = true
    | _, _ => False
  -- The callee, the receiver, the fixed actuals, then the value whose store
  -- the last actual spreads, of the packed binder the rest is.
  | .callPacked effect k t P =>
    match j.term, ps with
    | .invoke f r args, jf :: jr :: jas =>
      jf.context = j.context ∧ jf.term = f ∧ jr.context = j.context ∧ jr.term = r ∧
      (∀ ja ∈ jas, ja.context = j.context) ∧ jas.length = k + 1 ∧
      args = (jas.take k).map Sequent.term ++
        (jas.drop k).map (fun ja => .spread (.readAt CallArguments.arrayStoreField ja.term)) ∧
      (∀ ja ∈ jas.drop k, PackedBy G ja.type t) ∧ t ∈ P ∧
      ⟨jr.type, ((jas.take k).map Sequent.type, P), j.type, effect⟩ ∈ restSigs G jf.type ∧
      effect.plain = true
    | _, _ => False
  -- `.bind`'s saved slots, with no premises: each of the target's selected
  -- signatures starts with the prefix slots' contracts, and the result takes
  -- the rest of each at the receiver it states, whatever that is.
  | .bindE =>
    match j.term, ps with
    | .makeAt (.bound (.var t) (.var r) pre) ns inits, [] =>
      ns = [] ∧ inits = [] ∧
      match varSlots pre, j.context[t]?, j.context[r]?, expand G j.type with
      | some saved, some T, some Rt, [.arrs L []] =>
        saved.map (j.context[·]?) = (saved.filterMap (j.context[·]?)).map some ∧ L ≠ [] ∧
        ∀ a ∈ L, ∃ s ∈ callSigs G T, s.receiver = Rt ∧
          s.arguments = saved.filterMap (j.context[·]?) ++ a.arguments ∧
          s.result = a.result ∧ s.effect.keeps saved.length = true ∧ s.effect.drop saved.length = a.effect
      | _, _, _, _ => False
    | _, _ => False
  -- As `bindE`, for a variadic signature of the target with an element rest:
  -- the prefix takes its first fixed positions, and past them the element.
  | .bindRestE =>
    match j.term, ps with
    | .makeAt (.bound (.var t) (.var r) pre) ns inits, [] =>
      ns = [] ∧ inits = [] ∧
      match varSlots pre, j.context[t]?, j.context[r]?, expand G j.type with
      | some saved, some T, some Rt, [.arrs [] [⟨_, (Ds, E'), R, effect⟩]] =>
        saved.map (j.context[·]?) = (saved.filterMap (j.context[·]?)).map some ∧
        ∃ s ∈ restSigs G T, s.receiver = Rt ∧ s.arguments.2 = E' ∧ s.result = R ∧
          s.effect.keeps saved.length = true ∧ s.effect.drop saved.length = effect ∧
          Ds = s.arguments.1.drop saved.length ∧ ∃ El ∈ (restElem G E').toList,
          saved.filterMap (j.context[·]?) =
            s.arguments.1.take saved.length ++ List.replicate (saved.length - s.arguments.1.length) El
      | _, _, _, _ => False
    | _, _ => False
  -- A member read from a slot's object and bound to that same object, with no
  -- premises: the result's signatures are the member's, at any receiver.
  | .bindMember proofs rests receivers =>
    match j.term, ps with
    | .letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var r) pre) ns inits),
      [] =>
      r = i + 1 ∧ pre = [] ∧ ns = [] ∧ inits = [] ∧
      MemberProofsUsing G images j.context[i]? j.type k proofs rests receivers
    | _, _ => False
  -- The constructor, the actual premises in order, then one premise per
  -- position the signature declares and `new` omits, proving `undefined`
  -- there, as for `.app`.
  | .construct e =>
    match j.term, ps with
    | .construct f args, jf :: jas =>
      jf.context = j.context ∧ jf.term = f ∧ (jas.take args.length).map Sequent.term = args ∧
      (∀ ja ∈ jas.drop args.length, ja.term = .undef) ∧
      (∀ ja ∈ jas, ja.context = j.context) ∧
      match expand G jf.type with
      | [.ctors L _ _ _ _] => ⟨(), jas.map Sequent.type, j.type, e⟩ ∈ L ∧
          (e.plain = true ∨ (allowRequires = true ∧ e.promise = none))
      | _ => False
    | _, _ => False
  -- The constructor, the fixed actuals, then one premise per further part:
  -- the actual itself, or the store a spread reads.
  | .constructRest k flags P =>
    match j.term, ps with
    | .construct f args, jf :: jas =>
      jf.context = j.context ∧ jf.term = f ∧ (∀ ja ∈ jas, ja.context = j.context) ∧
      jas.length = k + flags.length ∧
      args = (jas.take k).map Sequent.term ++
        (flags.zip (jas.drop k)).map (fun q => spreadTerm (q.1, q.2.term)) ∧
      RestParts G P ((flags.zip (jas.drop k)).map fun q => (q.1, q.2.type)) ∧
      match expand G jf.type with
      | [.ctors _ S _ _ _] => ∃ s ∈ S, s.arguments = ((jas.take k).map Sequent.type, P) ∧
          s.result = j.type ∧ s.effect.plain = true
      | _ => False
    | _, _ => False
  | .sub proof =>
    match j.term, ps with
    | _, [jt] =>
      jt.context = j.context ∧ jt.term = j.term ∧
      subtype jt.type j.type proof = true
    | _, _ => False
  | .throw =>
    match j.term, ps with
    | .throw a, [ja] => ja.context = j.context ∧ ja.term = a ∧ SourceValues G ja.type
    | _, _ => False
  | .merge =>
    match j.term, ps with
    | .merge d a b, [ja, jb] =>
      ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
      ObjectMerge.MergeOk G d ja.type jb.type j.type = true
    | _, _ => False
  | .makeKey =>
    match j.term, ps with
    | .makeKey k a, [jk, ja] =>
      jk.context = j.context ∧ jk.term = k ∧ ja.context = j.context ∧ ja.term = a ∧
      ComputedKey.KeyedOk G jk.type ja.type j.type = true
    | _, _ => False
  | .lenView i =>
    match ps, j.context[i]? with
    | [], some R =>
      j.term = lengthRead i ∧ PositiveRules.numIn G j.type = true ∧
      (match expand G R with
       | [c] => (lengthKey, j.type) ∈ ((namedMembers c).map Prod.snd).getD []
       | _ => False)
    | _, _ => False
  -- A use of a checked summary: its key, its result, and the slot's type its
  -- receiver; the summary's arms are checked once, in its table.
  | .readSummary k =>
    match j.term, ps, sums[k]? with
    | .readAt f (.var i), [], some s => s.field = f ∧ s.result = j.type ∧ j.context[i]? = some s.receiver
    | _, _, _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (j : Sequent ι) (r : Rule ι) (ps)
    (codes : CodeEntry ι → Bool)
    (subtype : Ty ι → Ty ι → PositiveCertificates.SubtypeChoices ι → Bool)
    (sums : List (ReadSummary ι)) (allowRequires : Bool) :
    Decidable (LocalUsing G images j r ps codes subtype sums allowRequires) := by
  unfold LocalUsing
  split <;> (try split) <;> try infer_instance
  all_goals try dsimp [Represents, Answers]
  all_goals first | infer_instance | (split <;> infer_instance)

/-- Each evidence rule chooses its validator explicitly. Coercion checks
retain the subtype outcome; other rule predicates are their declarative checks. -/
@[nospecialize] def localCheckUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (j : Sequent ι) (r : Rule ι)
    (ps : List (Sequent ι)) (codes : CodeEntry ι → Bool := fun _ => false)
    (sums : List (ReadSummary ι) := []) : CheckResult ι Unit :=
  match r with
  | .sub choices => match ps with
    | [jt] => if jt.context = j.context ∧ jt.term = j.term then
        checkSubtypeUsing G images jt.type j.type choices else failure
    | _ => failure
  | .bindMember proofs rests receivers => match j.term, ps with
    | .letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var r) pre) ns inits), [] =>
        (CheckResult.ofBool (decide (r = i + 1 ∧ pre = [] ∧ ns = [] ∧ inits = []))).bind fun _ =>
          checkMemberProofs G images j.context[i]? j.type k proofs rests receivers
    | _, _ => failure
  | .var | .nul | .undef | .tru | .fls | .truLit | .flsLit | .numLit | .num | .strLit | .str
    | .bigintLit | .bigint | .funGraph .. | .funGraphSelf | .ctorGraph .. | .callableGraph .. | .app ..
    | .letE | .alloc | .read | .readView | .write | .arith | .test | .readDict .. | .indexDict ..
    | .readOptional .. | .readProto .. | .arrLit | .elem | .setElem | .len | .lenStr | .elemStr ..
    | .elemOpt .. | .elemAny .. | .ifBool | .ifTrue | .ifFalse | .ifKnown .. | .ifBoolVar ..
    | .unionVar .. | .callCallable .. | .readCallable | .readBagView | .writeCallable | .arrParts ..
    | .callRest .. | .callPacked .. | .bindE | .bindRestE | .construct .. | .constructRest .. | .throw | .merge
    | .makeKey
    | .lenView .. | .readSummary .. =>
      CheckResult.ofBool (decide (LocalUsing G images j r ps codes (sums := sums)))

theorem localCheckUsing_accepted [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (j : Sequent ι) (r : Rule ι)
    (ps : List (Sequent ι)) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (localCheckUsing G images j r ps codes sums).accepted =
      decide (LocalUsing G images j r ps codes (sums := sums)) := by
  cases r <;> try exact CheckResult.accepted_ofBool _
  case bindMember proofs rests receivers =>
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    simp only [localCheckUsing, CheckResult.accepted]
    split
    · change ((CheckResult.ofBool _).bind _).accepted = true ↔ _
      simp only [CheckResult.accepted_bind, CheckResult.accepted_ofBool,
        checkMemberProofs_accepted, Bool.and_eq_true, decide_eq_true_eq]
      rename_i heq
      unfold LocalUsing
      simp only [heq, and_assoc]
    · change (false = true) ↔ LocalUsing G images j (.bindMember proofs rests receivers) _ codes (sums := sums)
      simp only [Bool.false_eq_true, false_iff]
      intro h
      unfold LocalUsing at h
      split at h <;> simp_all
  case sub choices =>
    cases ps with
    | nil => rfl
    | cons jt ps =>
      cases ps with
      | cons x xs => rfl
      | nil =>
        by_cases h : jt.context = j.context ∧ jt.term = j.term
        · have hL : LocalUsing G images j (.sub choices) [jt] codes (sums := sums) ↔
              jt.context = j.context ∧ jt.term = j.term ∧
                PositiveCertificates.checkUsing G images jt.type j.type choices = true := Iff.rfl
          simp [localCheckUsing, h, checkSubtypeUsing_accepted, hL]
        · have hf : ¬ LocalUsing G images j (.sub choices) [jt] codes (sums := sums) := by
            intro hp
            exact h ⟨hp.1, hp.2.1⟩
          simp only [localCheckUsing, if_neg h, decide_eq_false hf]
          rfl

/-- Check the evidence tree once, retaining unfinished subtype work. -/
@[nospecialize] def checkTreeResult [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (e : Evidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) : CheckResult ι Unit :=
  match e with
  | .node j r ps => (localCheckUsing G images j r (ps.map claim) codes sums).bind fun _ =>
      CheckResult.all ps.attach (fun e => checkTreeResult G images e.val codes sums)
termination_by sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem e.property
  simp only [Evidence.node.sizeOf_spec]
  omega

@[nospecialize] def checkTreeUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (e : Evidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) : Bool :=
  (checkTreeResult G images e codes sums).accepted

/-- The acceptance projection has exactly the declarative rule premises. -/
theorem checkTreeUsing_eq [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (j : Sequent ι) (r : Rule ι)
    (ps : List (Evidence ι)) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    checkTreeUsing G images (.node j r ps) codes sums =
      (decide (LocalUsing G images j r (ps.map claim) codes (sums := sums)) &&
        ps.attach.all (fun e => checkTreeUsing G images e.val codes sums)) := by
  rw [checkTreeUsing, checkTreeResult, CheckResult.accepted_bind, CheckResult.accepted_all,
    localCheckUsing_accepted]
  rfl

mutual
def checkScope (d : Nat) : Tm → Bool
  | .var i => decide (i < d)
  | .objAt _ .absent _ => true
  | .objAt _ (.bound t r pre) _ => checkScope d t && checkScope d r && checkScopes d pre
  | .makeAt (.bound t r pre) _ args =>
      checkScope d t && checkScope d r && checkScopes d pre && checkScopes d args
  | .makeAt .absent _ args => checkScopes d args
  | .letE a b => checkScope d a && checkScope (d+1) b
  | .invoke f r args => checkScope d f && checkScope d r && checkScopes d args
  | .construct f args => checkScope d f && checkScopes d args
  | .writeAt _ a b | .arith _ a b | .elemAt a b | .indexAt a b | .merge _ a b | .makeKey a b =>
      checkScope d a && checkScope d b
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => checkScope d a
  | .setElem a b c => checkScope d a && checkScope d b && checkScope d c
  | .arrLit args => checkScopes d args
  | .ite c a b => checkScope d c && checkScope d a && checkScope d b
  | .objAt _ (.graph _ _ _ _ caps _ _) _ => checkScopes d caps
  | .makeAt (.graph _ _ _ _ caps _ _) _ args => checkScopes d caps && checkScopes d args
  | .goto _ _ _ L x => checkScopes d L && checkScope d x
  | .frame _ _ t L x _ _ => checkScope d t && checkScopes d L && checkScope d x
  | _ => true

def checkScopes (d : Nat) : List Tm → Bool
  | [] => true
  | a :: args => checkScope d a && checkScopes d args
end

@[simp] theorem checkScopes_iff (d : Nat) (args : List Tm) :
    checkScopes d args = true ↔ ∀ a ∈ args, checkScope d a = true := by
  induction args <;> simp_all [checkScopes]

/-- A code table is sound when each entry's code meets its signature in the
graph reassigned at every assignment of its parameter rows: a code check reads
no assignment (`Parametricity`), so a checked table is sound at all of them,
which is what a generic closure's creation needs (`HasTyUsing.funScheme`). -/
@[nospecialize] def CodesSound (G : NormalGraph ι) (codes : CodeEntry ι → Bool) : Prop :=
  ∀ c, codes c = true → ∀ η, c.Spec (reassign G η)

theorem codesSound_none (G : NormalGraph ι) : CodesSound G (fun _ => false) := by
  intro c h; cases h

/-- A generic body's code entries hold at the assignments admitted by its
own scheme. All three resolution projections are retained by that assignment. -/
@[nospecialize] def SchemeCodesSound (G : NormalGraph ι) (s : SchemeRow ι)
    (codes : CodeEntry ι → Bool) : Prop :=
  ∀ c, codes c = true → ∀ η As, As.length = s.binders.length →
    G.domain.allowed s As → c.Spec (reassign G (assign η s.binders As))

/-- Unconditionally checked code also meets a scheme's permitted assignments. -/
theorem CodesSound.scheme {G : NormalGraph ι} {codes : CodeEntry ι → Bool}
    (h : CodesSound G codes) (s : SchemeRow ι) : SchemeCodesSound G s codes :=
  fun c hc η As _ _ => h c hc (assign η s.binders As)

/-- Checked signatures use the body's actual permitted binder assignment. -/
theorem schemeOffersChecked_sound [DecidableEq ι] {G : NormalGraph ι}
    {s : SchemeRow ι} {codes : CodeEntry ι → Bool}
    (hcodes : SchemeCodesSound G s codes) {arity : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {start : Nat}
    {Cs : List (Ty ι)} {rest : Bool} {stores : List (Ty ι)}
    (h : offersChecked G codes arity E K start Cs rest s.signatures s.variadic stores = true)
    (η : MixedAssignment ι) (As : List MixedFamily)
    (hlen : As.length = s.binders.length) (ha : G.domain.allowed s As) :
    CodeOffers (reassign G (assign η s.binders As)) arity E K start Cs rest
      s.signatures s.variadic stores := by
  cases rest with
  | false =>
    simp only [offersChecked, List.all_eq_true] at h
    exact fun p hp => hcodes _ (h p hp) η As hlen ha
  | true =>
    simp only [offersChecked, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      decide_eq_true_eq, List.isEmpty_iff] at h
    obtain ⟨⟨hL, hslen⟩, hall⟩ := h
    exact ⟨hL, hslen, fun q hq => ⟨(hall q hq).1.1, (hall q hq).1.2,
      hcodes _ (hall q hq).2 η As hlen ha⟩⟩

/-- The checker establishes code formation independently of whether a scheme
has an admitted instance. -/
theorem offersChecked_shape [DecidableEq ι] {G : NormalGraph ι}
    {codes : CodeEntry ι → Bool} {arity E K start Cs rest L S stores}
    (h : offersChecked G codes arity E K start Cs rest L S stores = true) :
    CodeOffersShape G arity rest L S stores := by
  cases rest with
  | false => trivial
  | true =>
    simp only [offersChecked, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      decide_eq_true_eq, List.isEmpty_iff] at h
    exact ⟨h.1.1, h.1.2, fun q hq => (h.2 q hq).1⟩

/-- A generic closure is certified by its code table at the scheme's permitted
assignments and by the ordinary capture and code-formation checks. -/
theorem funScheme_of_checked [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {subtyping : BodySubtyping G}
    {Γ : List (Ty ι)} {j : ι} {s : SchemeRow ι}
    {codes : CodeEntry ι → Bool} (hcodes : SchemeCodesSound G s codes)
    {arity start : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {caps : List (Ty ι × Nat)} {kind : Invoke} {rest : Bool} {stores : List (Ty ι)}
    (hp : G.params j = false) (hs : G.schemes j = some s) (hcon : s.construct = false)
    (hkind : KindOffers G kind s.signatures s.variadic)
    (hc : offersChecked G codes arity E K start (caps.map Prod.fst) rest
      s.signatures s.variadic stores = true)
    (hfree : capturesFree G s (caps.map Prod.fst) = true)
    (hlt : ∀ c ∈ caps, c.2 < Γ.length)
    (hcap : ∀ c ∈ caps, HasTyUsing G images (subtyping := subtyping) Γ (.var c.2) c.1) :
    HasTyUsing G images (subtyping := subtyping) Γ
      (.makeFn (.graph arity E K start (caps.map fun c => .var c.2) kind rest) .nul) [j] :=
  .funScheme hp hs hcon hkind (schemeOffersChecked_sound hcodes hc) (offersChecked_shape hc) hfree hlt hcap

/-- A checked offer holds at every assignment: each entry does (`CodesSound`),
and a store type is read through the graph's rows only. -/
theorem offersChecked_sound [DecidableEq ι] {G : NormalGraph ι} {codes : CodeEntry ι → Bool}
    (hcodes : CodesSound G codes) {arity : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {start : Nat}
    {Cs : List (Ty ι)} {rest : Bool} {L : List (Arrow (Ty ι))}
    {S : List (RestArrow (Ty ι))} {As : List (Ty ι)}
    (h : offersChecked G codes arity E K start Cs rest L S As = true) :
    ∀ η, CodeOffers (reassign G η) arity E K start Cs rest L S As := by
  intro η
  cases rest with
  | false =>
    simp only [offersChecked, List.all_eq_true] at h
    exact fun p hp => hcodes _ (h p hp) η
  | true =>
    simp only [offersChecked, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      decide_eq_true_eq, List.isEmpty_iff] at h
    obtain ⟨⟨hL, hlen⟩, hall⟩ := h
    exact ⟨hL, hlen, fun q hq => ⟨(hall q hq).1.1, (hall q hq).1.2, hcodes _ (hall q hq).2 η⟩⟩

/-- Premises naming slots of the context are the captures of graph code: each
a slot below the context's length, typed there. -/
theorem caps_of_local [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {subtyping : BodySubtyping G} {Γ : List (Ty ι)}
    {ps : List (Sequent ι)} (hctx : ∀ q ∈ ps, q.context = Γ)
    (hslots : capSlotsBelow (ps.map Sequent.term) Γ.length = true)
    (hp : ∀ p ∈ ps, HasTyUsing G images (subtyping := subtyping) p.context p.term p.type) :
    ∃ caps : List (Ty ι × Nat), caps.map (fun c => Tm.var c.2) = ps.map Sequent.term ∧
      caps.map Prod.fst = ps.map Sequent.type ∧ (∀ c ∈ caps, c.2 < Γ.length) ∧
      ∀ c ∈ caps, HasTyUsing G images (subtyping := subtyping) Γ (.var c.2) c.1 := by
  unfold capSlotsBelow at hslots
  split at hslots
  · rename_i slots hvs
    have hterms := varSlots_eq hvs
    have hlen : (ps.map Sequent.type).length = slots.length := by
      have := congrArg List.length hterms
      simpa using this
    let caps := (ps.map Sequent.type).zip slots
    have hvar : caps.map (fun c => Tm.var c.2) = ps.map Sequent.term := by
      rw [hterms]
      have : caps.map Prod.snd = slots := List.map_snd_zip (by omega)
      rw [← this, List.map_map]; rfl
    have hfst : caps.map Prod.fst = ps.map Sequent.type := List.map_fst_zip (by omega)
    have hlt : ∀ c ∈ caps, c.2 < Γ.length := fun c hc => by
      have := List.of_mem_zip hc
      exact of_decide_eq_true (List.all_eq_true.mp hslots c.2 this.2)
    have hcap : ∀ c ∈ caps, HasTyUsing G images (subtyping := subtyping) Γ (.var c.2) c.1 := fun c hc => by
      obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hc
      have hi' : i < ps.length := by simp [caps] at hi; omega
      have hsl : i < slots.length := by simp [caps] at hi; omega
      rw [List.getElem_zip] at hci
      subst hci
      have hq := hp ps[i] (List.getElem_mem hi')
      have ht : ps[i].term = .var slots[i] := by
        have := congrArg (·[i]?) hterms
        simp [List.getElem?_map, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hsl] at this
        exact this
      rw [hctx _ (List.getElem_mem hi'), ht] at hq
      simpa using hq
    exact ⟨caps, hvar, hfst, hlt, hcap⟩
  · contradiction

/-- A graph code creation whose captures are slots and whose signatures the
table has checked is derivable. -/
theorem funGraph_of_local [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {subtyping : BodySubtyping G} {Γ : List (Ty ι)} {A : Ty ι}
    {codes : CodeEntry ι → Bool} (hcodes : CodesSound G codes) {arity start : Nat}
    {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {kind : Invoke} {rest : Bool} {As : List (Ty ι)}
    {ps : List (Sequent ι)} (hctx : ∀ q ∈ ps, q.context = Γ)
    (hslots : capSlotsBelow (ps.map Sequent.term) Γ.length = true)
    (hok : graphCodesChecked G A codes kind arity E K start (ps.map Sequent.type) rest As = true)
    (hp : ∀ p ∈ ps, HasTyUsing G images (subtyping := subtyping) p.context p.term p.type) :
    HasTyUsing G images (subtyping := subtyping) Γ (.makeFn (.graph arity E K start (ps.map Sequent.term) kind rest) .nul) A := by
  obtain ⟨caps, hvar, hfst, hlt, hcap⟩ := caps_of_local hctx hslots hp
  rw [← hvar]
  unfold graphCodesChecked at hok
  split at hok
  · -- A generic closure: its type is a scheme row.
    rename_i i s hs
    simp only [Bool.and_eq_true] at hok
    unfold schemeOf at hs
    split at hs
    · rename_i i'
      split at hs
      · cases hs
      · rename_i hpar
        obtain ⟨s', hq, he⟩ := Option.map_eq_some_iff.mp hs
        cases he
        exact funScheme_of_checked (caps := caps) (E := E) (K := K) (start := start) (arity := arity)
          (hcodes.scheme s) (by simpa using hpar) hq (by simpa using hok.1.1.1) (of_decide_eq_true hok.1.2)
          (by rw [hfst]; exact hok.2) (by rw [hfst]; exact hok.1.1.2) hlt hcap
    · cases hs
  · split at hok
    · rename_i L S hL
      simp only [Bool.and_eq_true] at hok
      exact HasTyUsing.funGraph (caps := caps) (E := E) (K := K) (start := start) (arity := arity) hL
        (of_decide_eq_true hok.1) (by rw [hfst]; exact offersChecked_sound hcodes hok.2 G.env) hlt hcap
    · contradiction

/-- A recursive closure creation whose captures are slots and whose
signatures the table has checked with the self entry is derivable. -/
theorem funGraphSelf_of_local [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {subtyping : BodySubtyping G} {Γ : List (Ty ι)} {A : Ty ι}
    {codes : CodeEntry ι → Bool} (hcodes : CodesSound G codes) {arity start : Nat}
    {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {kind : Invoke}
    {ps : List (Sequent ι)} (hctx : ∀ q ∈ ps, q.context = Γ)
    (hslots : capSlotsBelow (ps.map Sequent.term) Γ.length = true)
    (hok : graphCodesCheckedSelf G A codes kind arity E K start (ps.map Sequent.type) = true)
    (hp : ∀ p ∈ ps, HasTyUsing G images (subtyping := subtyping) p.context p.term p.type) :
    HasTyUsing G images (subtyping := subtyping) Γ (.makeFn (.graph arity E K start (ps.map Sequent.term) kind false) .nul) A := by
  obtain ⟨caps, hvar, hfst, hlt, hcap⟩ := caps_of_local hctx hslots hp
  rw [← hvar]
  unfold graphCodesCheckedSelf at hok
  split at hok
  · rename_i L S hL
    simp only [Bool.and_eq_true] at hok
    exact HasTyUsing.funGraphSelf (caps := caps) (E := E) (K := K) (start := start) (arity := arity) hL
      (of_decide_eq_true hok.1) (by rw [hfst]; exact offersChecked_sound hcodes hok.2 G.env) hlt hcap
  · contradiction

/-- **A checked read summary types the read.** In any context whose slot `i`
holds the summary's receiver, `readAt f (var i)` has the summary's result:
`unionVar` on the slot, then per member its view (`var`, `readView`) and
the arm's comparison (`sub`), each comparison accepted by the ordinary
checker and so by any body rule that admits the ordinary one (`hord`). -/
theorem readSummary_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {subtyping : BodySubtyping G}
    {s : ReadSummary ι} {Γ : List (Ty ι)} {i : Nat}
    (hs : checkReadSummary G images s = true) (hi : Γ[i]? = some s.receiver)
    (hord : ∀ {A B p}, PositiveCertificates.checkUsing G images A B p = true → subtyping.check A B p = true) :
    HasTyUsing G images (subtyping := subtyping) Γ (.readAt s.field (.var i)) s.result := by
  rw [checkReadSummary_eq] at hs
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
  obtain ⟨hlen, hall⟩ := hs
  have hlt : i < Γ.length := (List.getElem?_eq_some_iff.mp hi).1
  apply HasTyWith.unionVar hi
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have hk' : k < s.arms.length := hlen ▸ hk
  have hmem : ((members G s.receiver)[k], s.arms[k]) ∈ (members G s.receiver).zip s.arms := by
    have := List.getElem_mem (l := (members G s.receiver).zip s.arms) (n := k) (by simp only [List.length_zip]; omega)
    simpa [List.getElem_zip] using this
  have harm := hall _ hmem
  obtain ⟨hview, hproof⟩ := harm
  have hset : (Γ.set i [(members G s.receiver)[k]])[i]? = some [(members G s.receiver)[k]] := by
    simp [hlt]
  have hvar : HasTyUsing G images (subtyping := subtyping) (Γ.set i [(members G s.receiver)[k]]) (.var i)
      [(members G s.receiver)[k]] := HasTyWith.var hset
  unfold summaryView at hview
  split at hview
  · rename_i c hc
    split at hview
    · rename_i fs vs hn
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hview
      obtain ⟨hin, hlength⟩ := hview
      have hread := HasTyWith.readView (subtyping := subtyping) hvar hc hn hin hlength
      cases hp : s.arms[k].proof with
      | none =>
        rw [hp] at hproof
        simp only [decide_eq_true_eq] at hproof
        rw [← hproof]
        exact hread
      | some p =>
        rw [hp] at hproof
        exact HasTyWith.sub hread (hord hproof)
    · contradiction
  · contradiction

theorem local_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {subtyping : BodySubtyping G} {j r ps} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hl : LocalUsing G images j r ps codes subtyping.check sums) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums)
    (hord : ∀ {A B p}, PositiveCertificates.checkUsing G images A B p = true → subtyping.check A B p = true)
    (hp : ∀ p ∈ ps, HasTyUsing G images (subtyping := subtyping) p.context p.term p.type) : HasTyUsing G images (subtyping := subtyping) j.context j.term j.type := by
  rcases j with ⟨Γ, t, A⟩
  unfold LocalUsing at hl
  split at hl <;> (try split at hl) <;> (try contradiction) <;> (try dsimp only at *) <;> (try subst t)
  · exact .var hl
  · exact .nul hl
  · exact .undef hl
  · exact .tru hl
  · exact .fls hl
  · exact .truLit hl
  · exact .flsLit hl
  · exact .numLit hl
  · exact .num hl
  · exact .strLit hl
  · exact .str hl
  · exact .bigintLit hl
  · exact .bigint hl
  · rename_i As ps _ _ arity E K start caps kind rest ns inits
    obtain ⟨rfl, rfl, hterms, hctx, hslots, hok⟩ := hl
    subst caps
    exact funGraph_of_local hcodes hctx hslots hok hp
  · rename_i ps _ _ arity E K start caps kind ns inits
    obtain ⟨rfl, rfl, hterms, hctx, hslots, hok⟩ := hl
    subst caps
    exact funGraphSelf_of_local hcodes hctx hslots hok hp
  · rename_i U ps _ _ arity E K start caps kind rest f ns inits
    obtain ⟨rfl, rfl, rfl, hnd, hlen, hterms, hctx, hcaps, hslots, hu, hok⟩ := hl
    have hctxd : ∀ q ∈ ps.drop ns.length, q.context = Γ :=
      fun q hq => hctx q (List.mem_of_mem_drop hq)
    have hpd : ∀ q ∈ ps.drop ns.length, HasTyUsing G images (subtyping := subtyping) q.context q.term q.type :=
      fun q hq => hp q (List.mem_of_mem_drop hq)
    obtain ⟨caps', hvar, hfst, hlt, hcap⟩ :=
      caps_of_local hctxd (by rw [hcaps]; exact hslots) hpd
    subst caps
    rw [← hvar]
    have htl : (ps.take ns.length).length = ns.length := by
      have := congrArg List.length hterms
      simp only [List.length_map] at this
      omega
    let parts := (ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)
    have hfst' : parts.map Prod.fst = ns := by
      simp only [parts, List.map_map, Function.comp_def]
      exact List.map_fst_zip (by omega)
    have hsnd : parts.map (fun p => p.2.2) = inits := by
      rw [← hterms]
      simp only [parts, List.map_map, Function.comp_def]
      calc (ns.zip (ps.take ns.length)).map (fun r => r.2.term)
          = ((ns.zip (ps.take ns.length)).map Prod.snd).map Sequent.term := by
            simp [List.map_map, Function.comp_def]
        _ = (ps.take ns.length).map Sequent.term := by
            rw [List.map_snd_zip (by omega)]
    have hP : parts.map (fun p => (p.1, p.2.1)) =
        ns.zip ((ps.take ns.length).map Sequent.type) := by
      simp only [parts, List.map_map, Function.comp_def]
      rw [List.zip_map_right]
      simp []
    have hpart : ∀ p ∈ parts, HasTyUsing G images (subtyping := subtyping) Γ p.2.2 p.2.1 := by
      intro p hm
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
      have hmem := List.of_mem_zip hr
      have h := hp r.2 (List.mem_of_mem_take hmem.2)
      rw [hctx r.2 (List.mem_of_mem_take hmem.2)] at h
      exact h
    unfold ctorCodesChecked at hok
    split at hok
    · rename_i L S P' hL
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
      obtain ⟨⟨rfl, hok⟩, hokS⟩ := hok
      have := HasTyUsing.ctorGraph (G := G) (images := images) (Γ := Γ) (F := A) (parts := parts)
        (caps := caps') (E := E) (K := K) (start := start) (arity := arity)
        (by rw [hP]; exact hL) hu (by rw [hfst']; exact hnd) hpart
        (fun p hp' => by rw [hfst]; exact hcodes _ (hok p hp') G.env)
        (fun s hs => by
          have h := hokS s hs
          obtain ⟨hpl, h⟩ := h
          split at h
          · rename_i El hel
            exact ⟨hpl, El, hel, by rw [hfst]; exact hcodes _ h G.env⟩
          · contradiction)
        hlt hcap
      rw [hfst', hsnd] at this
      exact this
    · contradiction
  · split at hl
    · rename_i _ As ps _ _ arity E K start caps kind rest ns inits _ P L S hF
      obtain ⟨hkind, hnd, hlen, hterms, hctx, rfl, hcaps, hslots, hok⟩ := hl
      have hctxd : ∀ q ∈ ps.drop ns.length, q.context = Γ :=
        fun q hq => hctx q (List.mem_of_mem_drop hq)
      have hpd : ∀ q ∈ ps.drop ns.length, HasTyUsing G images (subtyping := subtyping) q.context q.term q.type :=
        fun q hq => hp q (List.mem_of_mem_drop hq)
      obtain ⟨caps', hvar, hfst, hlt, hcap⟩ :=
        caps_of_local hctxd (by rw [hcaps]; exact hslots) hpd
      subst caps
      rw [← hvar]
      have htl : (ps.take ns.length).length = ns.length := by
        have := congrArg List.length hterms
        simp only [List.length_map] at this
        omega
      let parts := (ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)
      have hfst' : parts.map Prod.fst = ns := by
        simp only [parts, List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : parts.map (fun p => p.2.2) = inits := by
        rw [← hterms]
        simp only [parts, List.map_map, Function.comp_def]
        calc (ns.zip (ps.take ns.length)).map (fun r => r.2.term)
            = ((ns.zip (ps.take ns.length)).map Prod.snd).map Sequent.term := by
              simp [List.map_map, Function.comp_def]
          _ = (ps.take ns.length).map Sequent.term := by
              rw [List.map_snd_zip (by omega)]
      have hP : parts.map (fun p => (p.1, p.2.1)) =
          ns.zip ((ps.take ns.length).map Sequent.type) := by
        simp only [parts, List.map_map, Function.comp_def]
        rw [List.zip_map_right]
        simp []
      have hpart : ∀ p ∈ parts, HasTyUsing G images (subtyping := subtyping) Γ p.2.2 p.2.1 := by
        intro p hm
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
        have hmem := List.of_mem_zip hr
        have h := hp r.2 (List.mem_of_mem_take hmem.2)
        rw [hctx r.2 (List.mem_of_mem_take hmem.2)] at h
        exact h
      have := HasTyUsing.callableGraph (G := G) (images := images) (Γ := Γ) (F := A) (parts := parts) (caps := caps')
        (E := E) (K := K) (start := start) (arity := arity) (rest := rest) (As := As)
        (by rw [hP]; exact hF) (by rw [hfst']; exact hnd) hpart hkind
        (by rw [hfst]; exact offersChecked_sound hcodes hok G.env) hlt hcap
      rw [hfst', hsnd] at this
      exact this
    · contradiction
  · rename_i f r args jf jr jas
    rcases hl with ⟨hΓf, htf, hΓr, htr, hargs, hundef, hcontexts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    have hrt := hp jr (by simp)
    rw [hΓr, htr] at hrt
    split at hL
    · rename_i L he
      -- The actual premises and the omitted-position premises are the same list,
      -- split at the number of actuals the call writes.
      have ha : ∀ p ∈ (jas.take args.length).map (fun ja => (ja.type,ja.term)),
          HasTyUsing G images (subtyping := subtyping) Γ p.2 p.1 := by
        intro p hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hja)))
        rw [hcontexts ja (List.mem_of_mem_take hja)] at h
        exact h
      have hu : ∀ A ∈ (jas.drop args.length).map Sequent.type, HasTyUsing G images (subtyping := subtyping) Γ .undef A := by
        intro A hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop hja)))
        rw [hcontexts ja (List.mem_of_mem_drop hja), hundef ja hja] at h
        exact h
      have hsplit : ((jas.take args.length).map (fun ja => (ja.type,ja.term))).map Prod.fst
          ++ (jas.drop args.length).map Sequent.type = jas.map Sequent.type := by
        simp only [List.map_map, Function.comp_def]
        rw [← List.map_append, List.take_append_drop]
      have h := HasTyUsing.app hf he (xs := (jas.take args.length).map (fun ja => (ja.type,ja.term)))
        (Us := (jas.drop args.length).map Sequent.type)
        (by rw [hsplit]; exact hL.1) hrt ha hu (CallEffects.Effect.plain_of hL.2.1 (hL.2.2.resolve_left (by simp)).1 (hL.2.2.resolve_left (by simp)).2)
      simpa only [List.map_map,Function.comp_def,hargs] using h
    · contradiction
  · rename_i a b ja jb
    rcases hl with ⟨hΓ, ht, rfl⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    exact .letE ha (hp ⟨ja.type :: Γ, b, A⟩ (by simp))
  · rename_i _ ps _ _ ns inits
    split at hl
    · rename_i fs vs ks st he
      obtain ⟨hnd, hnh, hlen, hterms, hctx, hfsv, rfl, hk, hreal, hstore, hst⟩ := hl
      have hzl : (ns.zip ps).length = ns.length := by simp [hlen]
      have hfst : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map Prod.fst = ns := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map (fun p => p.2.2)
          = inits := by
        rw [← hterms]
        simp only [List.map_map, Function.comp_def]
        calc (ns.zip ps).map (fun r => r.2.term)
            = ((ns.zip ps).map Prod.snd).map Sequent.term := by
              simp [List.map_map, Function.comp_def]
          _ = ps.map Sequent.term := by rw [List.map_snd_zip (by omega)]
      have htyp : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => (p.1, p.2.1)) = ns.zip (ps.map Sequent.type) := by
        rw [List.zip_map_right]
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro r _
        rfl
      have := HasTyUsing.alloc (G := G) (images := images) (Γ := Γ) (Ref := A)
        (parts := (ns.zip ps).map fun r => (r.1, r.2.type, r.2.term))
        (by rw [hfst]; exact hnd) (by rw [hfst]; exact hnh)
        (by
          intro q hq
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
          have hmem : r.2 ∈ ps := (List.of_mem_zip (by simpa using hr)).2
          have h := hp r.2 hmem
          rw [hctx r.2 hmem] at h
          exact h)
        (by rw [htyp]; exact hfsv)
        (by rw [htyp]; exact he)
        (by
          intro K hK q hq
          have : q.1 ∈ ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map Prod.fst :=
            List.mem_map_of_mem hq
          rw [hfst] at this
          exact hk K hK q.1 this)
        (by rw [htyp]; exact allocBuiltins_of_using hreal)
        (by rw [hfst]; exact hstore) (by rw [hfst]; exact hst)
      rw [hfst, hsnd] at this
      exact this
    · rename_i fs ix os cs he
      obtain ⟨hnd, hnp, hns, hnh, hlen, hterms, hctx, hfsv, hix, habs, hos⟩ := hl
      have hfst : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map Prod.fst = ns := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map (fun p => p.2.2)
          = inits := by
        rw [← hterms]
        simp only [List.map_map, Function.comp_def]
        calc (ns.zip ps).map (fun r => r.2.term)
            = ((ns.zip ps).map Prod.snd).map Sequent.term := by
              simp [List.map_map, Function.comp_def]
          _ = ps.map Sequent.term := by rw [List.map_snd_zip (by omega)]
      have htyp : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => (p.1, p.2.1)) = ns.zip (ps.map Sequent.type) := by
        rw [List.zip_map_right]
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro r _
        rfl
      have := HasTyUsing.allocDict (G := G) (images := images) (Γ := Γ) (Ref := A)
        (parts := (ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)) (fs := fs) (ix := ix) (cs := cs) (os := os)
        (by rw [hfst]; exact hnd) (by rw [hfst]; exact hnp) (by rw [hfst]; exact hns) (by rw [hfst]; exact hnh)
        (by
          intro q hq
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
          have hmem : r.2 ∈ ps := (List.of_mem_zip (by simpa using hr)).2
          have h := hp r.2 hmem
          rw [hctx r.2 hmem] at h
          exact h)
        (by rw [htyp]; exact hfsv)
        he
        (by
          intro q hq y hy hm
          have : (q.1, q.2.1) ∈ Stored.views fs := by
            rw [hfsv, ← htyp]; exact List.mem_map_of_mem hq
          obtain ⟨s, hs⟩ := Stored.mem_views.mp this
          exact hix _ hs y hy hm)
        (by rw [hfst]; exact habs) hos
      rw [hfst, hsnd] at this
      exact this
    · contradiction
  · rename_i f a ja
    rcases hl with ⟨hΓ, ht, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i c he
      cases hc : namedMembers c with
      | none => simp [hc] at hr
      | some m =>
        simp only [hc, Option.map_some, Option.getD_some] at hr
        obtain ⟨_, hr⟩ := Stored.mem_views.mp hr
        exact .read ha he hc hr
    · contradiction
  · rename_i f a ja
    rcases hl with ⟨hΓ, ht, hlen, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i c he
      cases hc : namedMembers c with
      | none => simp [hc] at hr
      | some m => simp only [hc, Option.map_some, Option.getD_some] at hr; exact .readView ha he hc hr hlen
    · contradiction
  · rename_i P _ _ f a ja
    rcases hl with ⟨hΓ, ht, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i fs vs ks he
      obtain ⟨⟨K, hK, hf⟩, hpr, hP⟩ := hr
      unfold ProtoMember at hP
      split at hP
      · rename_i gs ws ks' hPe
        exact .readProto ha he hK hf hpr hPe hP
      · contradiction
    · contradiction
  · rename_i A U _ _ f a ja
    rcases hl with ⟨hΓ, ht, hUnd, eq, hinh, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i fs vs os he
      subst eq
      obtain ⟨⟨f', r, A'⟩, ho, hf, hA⟩ := hr
      simp only at hf hA
      subst hf hA
      exact .readOptional ha he ho hUnd hinh
    · contradiction
  · rename_i K A U _ _ f a ja
    rcases hl with ⟨hΓ, ht, hUnd, eq, hsure, hinh, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i fs vs ix os he
      subst eq
      exact .readDict ha he hr hsure hUnd hinh
    · contradiction
  · rename_i K KK E U _ _ a key ja jk
    rcases hl with ⟨hΓa, hta, hΓk, htk, hStr, hwithin, hUnd, eq, hns, hr⟩
    have ha := hp ja (by simp)
    have hk := hp jk (by simp)
    rw [hΓa, hta] at ha
    rw [hΓk, htk] at hk
    split at hr
    · rename_i fs vs ix os he
      subst eq
      exact .indexDict ha he hk hStr hwithin hr hUnd hns
    · contradiction
  · rename_i f a b ja jb
    rcases hl with ⟨hΓa, hta, hΓb, htb, hn, hr⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa, hta] at ha
    rw [hΓb, htb] at hb
    split at hr
    · rename_i fs vs os ms ks st he
      obtain ⟨_, hr⟩ := Stored.mem_views.mp hr
      exact .write ha he hr hb hn
    · contradiction
  · rename_i op a b ja jb
    rcases hl with ⟨hΓa, hta, hΓb, htb, hops⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa, hta] at ha
    rw [hΓb, htb] at hb
    exact .arith ha hb hops
  · rename_i k a ja
    rcases hl with ⟨hΓ, hta, ht, hf⟩
    have ha := hp ja (by simp)
    rw [hΓ, hta] at ha
    exact .test ha ht hf
  · rename_i _ psl x ps' inits
    split at hl
    · rename_i T hT
      obtain ⟨hterms, hctx, hreq, hbound, hpos⟩ := hl
      subst hterms
      have hmap : psl.map Sequent.term = (psl.map fun p => (p.type, p.term)).map Prod.snd := by
        simp [List.map_map, Function.comp_def]
      rw [hmap]
      refine HasTyUsing.arrLit (xs := psl.map fun p => (p.type, p.term)) hT
        (by simpa using hreq) (by simpa using hbound) ?_ ?_
      · intro q hq
        rw [List.zipIdx_map] at hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact hpos p hp
      · intro p hmem
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
        have := hp q hq
        rw [hctx q hq] at this
        exact this
    · contradiction
  · rename_i a i ja ji
    rcases hl with ⟨hΓa, hta, hΓi, hti, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    split at hr
    · rename_i T b hT hI
      simp only [requiredAt, Option.bind_eq_some_iff] at hr
      obtain ⟨k, hk, hA⟩ := hr
      exact .elem ha hT hi hI hk hA
    · contradiction
  · rename_i U _ _ a i ja ji
    rcases hl with ⟨hΓa, hta, hΓi, hti, hU, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    split at hr
    · rename_i T b hT hI
      simp only [optionalAt, Option.bind_eq_some_iff] at hr
      obtain ⟨k, hk, hr⟩ := hr
      split at hr
      · cases hr
      · rename_i hnone
        simp only [Option.map_eq_some_iff] at hr
        obtain ⟨A, hA, rfl⟩ := hr
        exact .elemOpt ha hT hi hI hk hnone hA hU
    · contradiction
  · rename_i U _ _ a i ja ji
    rcases hl with ⟨hΓa, hta, hΓi, hti, hU, hq, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    split at hr
    · rename_i E ro presence hT
      rw [hr]
      exact .elemAny ha hT hi hq hU
    · contradiction
  · rename_i a i v ja ji jv
    rcases hl with ⟨hΓa, hta, hΓi, hti, hΓv, htv, hty, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    have hv := hp jv (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    rw [hΓv, htv] at hv
    rw [hty]
    split at hr
    · rename_i T b hT hI
      obtain ⟨hr, hkle, hro⟩ := hr
      simp only [namedAt, Option.bind_eq_some_iff] at hr
      obtain ⟨k, hk, hA⟩ := hr
      rw [hk] at hkle
      exact .setElem ha hT hi hI hk hA hkle hro hv
    · contradiction
  · rename_i a ja
    rcases hl with ⟨hΓ, hta, hn, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, hta] at ha
    split at hr
    · rename_i T hT
      exact .len ha hT hn
    · contradiction
  · rename_i a ja
    rcases hl with ⟨hΓ, hta, hn, hs⟩
    have ha := hp ja (by simp)
    rw [hΓ, hta] at ha
    exact .lenStr ha hs hn
  · rename_i T U _ _ a i ja ji
    rcases hl with ⟨hΓa, hta, hΓi, hti, hs, hq, hT, hU, hty⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    rw [hty]
    exact .elemStr ha hs hi hq hT hU
  · rename_i c t e jc jt je
    rcases hl with ⟨hΓ, hc, hb, rfl, rfl⟩
    have hcond := hp jc (by simp)
    rw [hΓ, hc] at hcond
    exact .ifBool hcond hb (hp ⟨Γ,t,A⟩ (by simp)) (hp ⟨Γ,e,A⟩ (by simp))
  · rename_i q _ _ c t e jc jb
    rcases hl with ⟨hΓ,hc,hq,rfl⟩
    have hcond := hp jc (by simp)
    rw [hΓ,hc] at hcond
    exact .ifKnown hcond hq (hp ⟨Γ,(if q then t else e),A⟩ (by simp))
  · rename_i T F _ _ i t e jt je
    rcases hl with ⟨hb,hT,hF,rfl,rfl⟩
    split at hb
    · rename_i C hc
      exact .ifBoolVar hc hb hT hF (hp ⟨Γ.set i T,t,A⟩ (by simp)) (hp ⟨Γ.set i F,e,A⟩ (by simp))
    · contradiction
  · rename_i tag i u e ju
    rcases hl with ⟨rfl, hq⟩
    split at hq
    · rename_i D hd
      exact .ifTag hd hq (fun _ => hp ⟨Γ, u, A⟩ (by simp)) (by intro h; cases h)
    · contradiction
  · rename_i tag i u e je
    rcases hl with ⟨rfl, hq⟩
    split at hq
    · rename_i D hd
      exact .ifTag hd hq (by intro h; cases h) (fun _ => hp ⟨Γ, e, A⟩ (by simp))
    · contradiction
  · rename_i i ps _ _
    split at hl
    · rename_i C hi
      apply HasTyUsing.unionVar hi
      intro a ha
      apply hp ⟨Γ.set i [a], _, A⟩
      rw [hl]
      exact List.mem_map.mpr ⟨a,ha,rfl⟩
    · contradiction
  · rename_i f r args jf jr jas
    rcases hl with ⟨hΓf, htf, hΓr, htr, hargs, hundef, hcontexts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    have hrt := hp jr (by simp)
    rw [hΓr, htr] at hrt
    split at hL
    · rename_i P Ps L he
      -- The actual premises and the omitted-position premises are the same list,
      -- split at the number of actuals the call writes.
      have ha : ∀ p ∈ (jas.take args.length).map (fun ja => (ja.type,ja.term)),
          HasTyUsing G images (subtyping := subtyping) Γ p.2 p.1 := by
        intro p hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hja)))
        rw [hcontexts ja (List.mem_of_mem_take hja)] at h
        exact h
      have hu : ∀ A ∈ (jas.drop args.length).map Sequent.type, HasTyUsing G images (subtyping := subtyping) Γ .undef A := by
        intro A hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop hja)))
        rw [hcontexts ja (List.mem_of_mem_drop hja), hundef ja hja] at h
        exact h
      have hsplit : ((jas.take args.length).map (fun ja => (ja.type,ja.term))).map Prod.fst
          ++ (jas.drop args.length).map Sequent.type = jas.map Sequent.type := by
        simp only [List.map_map, Function.comp_def]
        rw [← List.map_append, List.take_append_drop]
      have h := HasTyUsing.callCallable hf he (xs := (jas.take args.length).map (fun ja => (ja.type,ja.term)))
        (Us := (jas.drop args.length).map Sequent.type)
        (by rw [hsplit]; exact hL.1) hrt ha hu hL.2
      simpa only [List.map_map,Function.comp_def,hargs] using h
    · contradiction
  · rename_i a ja
    rcases hl with ⟨hΓ,ht,hL⟩
    have ha := hp ja (by simp)
    rw [hΓ,ht] at ha
    split at hL
    · rename_i c he
      unfold Clause.bagFields at hL
      split at hL
      · rename_i P Ps hc
        obtain ⟨_, hL⟩ := Stored.mem_views.mp hL
        exact .readCallable ha he hc hL
      · simp [Stored.views] at hL
    · contradiction
  · rename_i a ja
    rcases hl with ⟨hΓ,ht,hL⟩
    have ha := hp ja (by simp)
    rw [hΓ,ht] at ha
    split at hL
    · rename_i c he
      exact .readBagView ha he hL
    · contradiction
  · rename_i a b ja jb
    rcases hl with ⟨hΓa,hta,hΓb,htb,hn,hL⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa,hta] at ha
    rw [hΓb,htb] at hb
    split at hL
    · rename_i c he
      unfold Clause.bagFields at hL
      split at hL
      · rename_i P Ps hc
        obtain ⟨_, hL⟩ := Stored.mem_views.mp hL
        exact .writeCallable ha he hc hL hb hn
      · simp [Stored.views] at hL
    · contradiction
  · rename_i E flags _ args
    rcases hl with ⟨hctx, hlen, rfl, hparts, hr⟩
    split at hr
    · rename_i ro presence hT
      subst hr
      have := HasTyUsing.arrParts (ro := ro) (presence := presence)
        (parts := (flags.zip ps).map fun q => (q.1, q.2.type, q.2.term))
        (by
          intro p hm
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
          have h := hp q.2 (List.of_mem_zip hq).2
          rw [hctx q.2 (List.of_mem_zip hq).2] at h
          exact h)
        (by
          intro p hm
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
          exact hparts q hq)
        hT
      simpa [List.map_map, Function.comp_def] using this
    · contradiction
  · rename_i k u flags P _ _ f r args jf jr jas
    rcases hl with ⟨hΓf, htf, hΓr, htr, hctx, hlen, hshort, rfl, hundef, hparts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    have hrt := hp jr (by simp)
    rw [hΓr, htr] at hrt
    have htake : jas.take (k + u) = jas.take k ++ (jas.drop k).take u := List.take_add ..
    have := HasTyUsing.callRest (xs := (jas.take k).map fun ja => (ja.type, ja.term))
      (Us := ((jas.drop k).take u).map Sequent.type) (P := P)
      (parts := (flags.zip (jas.drop (k + u))).map fun q => (q.1, q.2.type, q.2.term)) hf
      (by rw [htake] at hL; simpa [List.map_append, List.map_map, Function.comp_def] using hL.1) hrt
      (by
        intro p hm
        obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hja)))
        rw [hctx ja (List.mem_of_mem_take hja)] at h
        exact h)
      (by
        intro A hA
        obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hA
        have hmem : ja ∈ jas := List.mem_of_mem_drop (List.mem_of_mem_take hja)
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem))
        rw [hctx ja hmem, hundef ja hja] at h
        exact h)
      (by rcases hshort with h | h <;> simp [h])
      (by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        have hja := List.mem_of_mem_drop (List.of_mem_zip hq).2
        have h := hp q.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hja))
        rw [hctx q.2 hja] at h
        exact h)
      (by simpa [List.map_map, Function.comp_def] using hparts) hL.2
    simpa [List.map_map, Function.comp_def] using this
  · rename_i effect k t P _ _ f r args jf jr jas
    rcases hl with ⟨hΓf, htf, hΓr, htr, hctx, hlen, rfl, hpk, htP, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    have hrt := hp jr (by simp)
    rw [hΓr, htr] at hrt
    obtain ⟨ja, hja⟩ : ∃ ja, jas.drop k = [ja] := by
      have hl1 : (jas.drop k).length = 1 := by simp; omega
      match h : jas.drop k, hl1 with
      | [ja], _ => exact ⟨ja, rfl⟩
    have hjamem : ja ∈ jas := List.mem_of_mem_drop (by rw [hja]; simp)
    have ha := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hjamem))
    rw [hctx ja hjamem] at ha
    have := HasTyUsing.callPacked (xs := (jas.take k).map fun ja => (ja.type, ja.term)) hf
      (by simpa [List.map_map, Function.comp_def] using hL.1) htP hrt
      (by
        intro p hm
        obtain ⟨jb, hjb, rfl⟩ := List.mem_map.mp hm
        have h := hp jb (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hjb)))
        rw [hctx jb (List.mem_of_mem_take hjb)] at h
        exact h)
      ha (hpk ja (by rw [hja]; simp)) hL.2
    rw [hja]
    simpa [List.map_map, Function.comp_def] using this
  · obtain ⟨rfl, rfl, hl⟩ := hl
    split at hl
    · rename_i hsaved hT hRt hF
      obtain ⟨hmap, hne, hL⟩ := hl
      rw [varSlots_eq hsaved]
      exact HasTyUsing.bindE hT hRt hmap hne hL hF
    · contradiction
  · obtain ⟨rfl, rfl, hl⟩ := hl
    split at hl
    · rename_i hsaved hT hRt hF
      obtain ⟨hmap, ⟨Rt', ⟨Ps, E'⟩, R', ef⟩, hmem, h1, h2, h3, hk, hef, h4, El, hEl, h5⟩ := hl
      simp only at h1 h2 h3 hk hef h4 h5
      subst h1 h2 h3 hef h4
      rw [varSlots_eq hsaved]
      exact HasTyUsing.bindRestE hT hmem (by simpa using hEl) hRt hmap h5 hk hF
    · contradiction
  · obtain ⟨rfl, rfl, rfl, rfl, hl⟩ := hl
    unfold MemberProofsUsing at hl
    split at hl
    · rename_i O L S hO hF
      obtain ⟨m, hm, hlen, hL, hrlen, hS, hvlen, hV⟩ := hl
      exact HasTyUsing.bindMember hO (by simpa using hm) hF (fun q hq => by
        obtain ⟨pp, hpp⟩ := PositiveCertificates.exists_mem_zip hlen q hq
        obtain ⟨c, hc, hcp⟩ := hL _ hpp
        exact ⟨c, hc, hcp.covered⟩) (fun s hs => by
        obtain ⟨pp, hpp⟩ := PositiveCertificates.exists_mem_zip hrlen s hs
        obtain ⟨c, hc, hcp⟩ := hS _ hpp
        exact ⟨c, hc, hcp.covered⟩) (fun T hT => by
        obtain ⟨pp, hpp⟩ := PositiveCertificates.exists_mem_zip hvlen T hT
        exact ⟨pp, hV _ hpp⟩)
    · rename_i O hO _
      obtain ⟨-, -, -, hE, m, hm, hF⟩ := hl
      exact HasTyUsing.bindScheme hO (by simpa using hm) hF hE
    · contradiction
  · rename_i f args jf jas
    rcases hl with ⟨hΓf, htf, hterms, hundef, hctx, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    split at hL
    · rename_i L _ he
      have hxs : ∀ p ∈ (jas.take args.length).map (fun ja => (ja.type, ja.term)),
          HasTyUsing G images (subtyping := subtyping) Γ p.2 p.1 := by
        intro p hp'
        obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hp'
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_of_mem_take hja))
        rw [hctx ja (List.mem_of_mem_take hja)] at h
        exact h
      have hu : ∀ A ∈ (jas.drop args.length).map Sequent.type, HasTyUsing G images (subtyping := subtyping) Γ .undef A := by
        intro A hm
        obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_of_mem_drop hja))
        rw [hctx ja (List.mem_of_mem_drop hja), hundef ja hja] at h
        exact h
      have hsplit : ((jas.take args.length).map (fun ja => (ja.type, ja.term))).map Prod.fst
          ++ (jas.drop args.length).map Sequent.type = jas.map Sequent.type := by
        simp only [List.map_map, Function.comp_def]
        rw [← List.map_append, List.take_append_drop]
      obtain ⟨hpm, hpl⟩ := hL
      have hpl := hpl.resolve_right (by simp)
      have hc := HasTyUsing.construct (xs := (jas.take args.length).map fun ja => (ja.type, ja.term))
        (Us := (jas.drop args.length).map Sequent.type) hf he
        (by rw [hsplit]; exact hpm) hpl hxs hu
      simpa only [List.map_map, Function.comp_def, hterms] using hc
    · contradiction
  · rename_i k flags P _ _ f args jf jas
    rcases hl with ⟨hΓf, htf, hctx, hlen, rfl, hparts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    split at hL
    · rename_i L S he
      obtain ⟨⟨⟨⟩, sa, sr, se⟩, hsm, rfl, rfl, hpl⟩ := hL
      have := HasTyUsing.constructRest (xs := (jas.take k).map fun ja => (ja.type, ja.term)) (P := P)
        (parts := (flags.zip (jas.drop k)).map fun q => (q.1, q.2.type, q.2.term)) hf he
        (by simpa [List.map_map, Function.comp_def] using hsm) hpl
        (by
          intro p hm
          obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hm
          have h := hp ja (List.mem_cons_of_mem _ (List.mem_of_mem_take hja))
          rw [hctx ja (List.mem_of_mem_take hja)] at h
          exact h)
        (by
          intro p hm
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
          have hja := List.mem_of_mem_drop (List.of_mem_zip hq).2
          have h := hp q.2 (List.mem_cons_of_mem _ hja)
          rw [hctx q.2 hja] at h
          exact h)
        (by simpa [List.map_map, Function.comp_def] using hparts)
      simpa [List.map_map, Function.comp_def] using this
    · contradiction
  · rename_i proof _ t jt
    rcases hl with ⟨hΓ, ht, hc⟩
    have hj := hp jt (by simp)
    rw [hΓ, ht] at hj
    exact .sub hj hc
  · rename_i a ja
    rcases hl with ⟨hΓ, hta, hA⟩
    have ha := hp ja (by simp)
    rw [hΓ, hta] at ha
    exact .throw hA ha
  · rename_i d a b ja jb
    rcases hl with ⟨hΓa, hta, hΓb, htb, hm⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa, hta] at ha
    rw [hΓb, htb] at hb
    exact .merge ha hb hm
  · rename_i k a jk ja
    rcases hl with ⟨hΓk, htk, hΓa, hta, hm⟩
    have hk := hp jk (by simp)
    have ha := hp ja (by simp)
    rw [hΓk, htk] at hk
    rw [hΓa, hta] at ha
    exact .makeKey hk ha hm
  · rename_i i R hR
    obtain ⟨rfl, hnum, hr⟩ := hl
    split at hr
    · rename_i c he
      cases hc : namedMembers c with
      | none => simp [hc] at hr
      | some m =>
        simp only [hc, Option.map_some, Option.getD_some] at hr
        exact .lenView hR he hc hr hnum
    · contradiction
  · rename_i f i _ s hs
    obtain ⟨rfl, rfl, hi⟩ := hl
    exact readSummary_sound (hsums s (List.mem_of_getElem? hs)) hi hord

theorem checkTreeUsing_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (e : Evidence ι)
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} (he : checkTreeUsing G images e codes sums = true)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _)
    (hsums : SummariesSound G images sums := by exact Verification.ProgramCertificates.summariesSound_none _ _) :
    HasTyUsing G images (claim e).context (claim e).term (claim e).type := by
  cases e with
  | node j r ps =>
    simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at he
    apply local_sound he.1 hcodes hsums (fun h => h)
    intro p hp
    obtain ⟨e, he', rfl⟩ := List.mem_map.mp hp
    exact checkTreeUsing_sound e (he.2 ⟨e, he'⟩ (by simp)) hcodes hsums
termination_by sizeOf e

/-- Expression evidence under a body's subsumption rule. The rule and every
premise are checked, including closure captures and the checked code table. -/
@[nospecialize] def checkTreeWith [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G)
    (subtype : Ty ι → Ty ι → PositiveCertificates.SubtypeChoices ι → Bool)
    (e : Evidence ι) (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) : Bool :=
  match e with
  | .node j r ps => decide (LocalUsing G images j r (ps.map claim) codes subtype sums) &&
      ps.attach.all (fun p => checkTreeWith G images subtype p.val codes sums)
termination_by sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem p.property
  simp only [Evidence.node.sizeOf_spec]
  omega

theorem checkTreeWith_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (subtyping : BodySubtyping G)
    (e : Evidence ι) {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (he : checkTreeWith G images subtyping.check e codes sums = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (hord : ∀ {A B p}, PositiveCertificates.checkUsing G images A B p = true → subtyping.check A B p = true) :
    HasTyUsing G images (subtyping := subtyping)
      (claim e).context (claim e).term (claim e).type := by
  cases e with
  | node j r ps =>
    simp only [checkTreeWith, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at he
    apply local_sound he.1 hcodes hsums hord
    intro p hp
    obtain ⟨e, he', rfl⟩ := List.mem_map.mp hp
    exact checkTreeWith_sound subtyping e (he.2 ⟨e, he'⟩ (by simp)) hcodes hsums hord
termination_by sizeOf e


end Verification.ProgramCertificates
