import Verification.Semantics.TwoStateFormulas

/-! # Exit specifications and their schemas

A callable's guarantee per completion (the note *Tolerant frames*, §6, the
judgment $c:\Phi\mid\Phi^{e}$): for each exit a frame and a list of
two-state postconditions (`ExitSpec`). A signature states it as a schema
(`ExitSchema`) over its parameters, a rest parameter included: the note's
Call substitutes the call's actuals, so a schema's formulas name the actuals
from a position on (`WitnessSeq.restFrom`) and transports by a default
shift with finitely many replacements (`TransportSchema`), and a call
instantiates them at the number of its actuals and its entry scope
(`ExitSchema.instantiate`). Only instantiated formulas are interpreted. -/
namespace Verification.CallEffects
open Verification Footprints Parity

/-! ## Exits

A callable's specification bounds each of its two completions on its own
(the note *Tolerant frames*, §6, the judgment $c:\Phi\mid\Phi^{e}$, and Call
on both exits): a normal return and a throw each have an effect and a
postcondition, both read from the call's entry state. -/

/-- The two completions of a call. -/
inductive Completion where
  | normal
  | exceptional
  deriving DecidableEq, Repr

/-- One datum per completion. -/
structure Exits (α : Type) where
  normal : α
  exceptional : α
  deriving DecidableEq, Repr

def Exits.get {α : Type} (x : Exits α) : Completion → α
  | .normal => x.normal
  | .exceptional => x.exceptional

def Exits.map {α β : Type} (f : α → β) (x : Exits α) : Exits β := ⟨f x.normal, f x.exceptional⟩

@[simp] theorem Exits.get_map {α β : Type} (f : α → β) (x : Exits α) (c : Completion) :
    (x.map f).get c = f (x.get c) := by
  cases c <;> rfl

/-- **A completion's guarantee** (the note, §6): the frame bounding the old
locations it may change, read at the entry's environment, and the
postconditions it states. -/
structure ExitSpec where
  frame : Footprint
  ensures : List Formula
  deriving DecidableEq

/-- **The meaning of an exit specification**: the transition is an action of
the frame, and every postcondition holds, all in the same two-state
interpretation. -/
def ExitSpec.Holds (arena : AssertionArena) (q : ExitSpec) (s : TwoState) : Prop :=
  EffectAction q.frame s.beforeEnv s.before s.after ∧ ∀ F ∈ q.ensures, Parity.Holds arena s F

/-- A call's values by position: `0` the receiver, `i + 1` the `i`-th actual,
`undefined` past the last. -/
def callEnv (r : Tm) (args : List Tm) : Env := fun i => if i = 0 then r else args.getD (i - 1) .undef

/-- A return's values by position: `0` the result, `i + 1` the call's
position `i` (`callEnv`). -/
def ensuresEnv (v : Tm) (r : Tm) (args : List Tm) : Env := fun i => if i = 0 then v else callEnv r args (i - 1)

/-- The two-state interpretation of a call with receiver `r` and actuals
`args` completing with `v`, from the state `s` to the state `s'`, at the
mark `m`. -/
def callState (r : Tm) (args : List Tm) (v : Tm) (m : Nat) (s s' : TolerantFrames.IndexedHeap) : TwoState :=
  ⟨callEnv r args, ensuresEnv v r args, m, s, s'⟩

end Verification.CallEffects

namespace Verification.Parity
open Verification Footprints

/-! ## The payloads of a formula -/

/-- An operational post with its append's arguments mapped. -/
def OperationPostF.map {S S' : Type} (f : S → S') : OperationPostF S → OperationPostF S'
  | .arith op l r y => .arith op l r y
  | .stringLength x y => .stringLength x y
  | .stringRead x i y => .stringRead x i y
  | .lengthsKept x x' => .lengthsKept x x'
  | .boundedWrite x i x' => .boundedWrite x i x'
  | .push x x' args => .push x x' (f args)
  | .fact p l F => .fact p l F
  | .freshStore x => .freshStore x
  | .freshObject x => .freshObject x
  | .elementsWhen x v y R => .elementsWhen x v y R
  | .storeExtends x => .storeExtends x
  | .viewWrite x i v g => .viewWrite x i v g

/-- A formula with its appends' arguments and its transports mapped. -/
def FormulaF.map {S S' T T' : Type} (f : S → S') (g : T → T') : FormulaF S T → FormulaF S' T'
  | .at p a => .at p a
  | .transition Φ => .transition Φ
  | .operation q => .operation (q.map f)
  | .linear F => .linear F
  | .defined v => .defined v
  | .transport θ => .transport (g θ)
  | .and F G => .and (F.map f g) (G.map f g)
  | .truth => .truth
  | .falsity => .falsity

/-! ## Self-contained formulas

**A contract states no assertion-arena formula** (stated limit): a
signature's postconditions are operational posts, index facts, transitions,
transports and their conjunctions, so they are read at the empty arena
(`AssertionArena.empty`), and a schema is well formed only where it
references no arena node (`FormulaF.arenaFree`). A contract that needs an
assertion would carry its own arena. -/

/-- Whether a formula references no node of an assertion arena. -/
def FormulaF.arenaFree {S T : Type} : FormulaF S T → Bool
  | .at .. => false
  | .and F G => F.arenaFree && G.arenaFree
  | _ => true

/-- The arena with no node. -/
def AssertionArena.empty : AssertionArena := ⟨#[]⟩

theorem FormulaF.arenaFree_map {S S' T T' : Type} (f : S → S') (g : T → T') (F : FormulaF S T) :
    (F.map f g).arenaFree = F.arenaFree := by
  induction F with
  | and F G ihF ihG => simp only [FormulaF.map, FormulaF.arenaFree, ihF, ihG]
  | _ => rfl

/-- **A formula referencing no arena node means the same at every arena.** -/
theorem holds_arenaFree {F : Formula} (hF : F.arenaFree = true) (arena arena' : AssertionArena) (s : TwoState) :
    Holds arena s F ↔ Holds arena' s F := by
  induction F with
  | «at» _ _ => cases hF
  | and F G ihF ihG =>
    simp only [FormulaF.arenaFree, Bool.and_eq_true] at hF
    simp only [Holds, ihF hF.1, ihG hF.2]
  | _ => exact Iff.rfl

/-! ## Schemas -/

/-- **A sequence of a call's values** in a specification (the note's Call,
its actuals substituted for the parameters): fixed witnesses, the actuals
from call position `first` on (a rest parameter: `0` is the receiver, `i + 1`
the `i`-th actual), or two in turn. -/
inductive WitnessSeq where
  | fixed (xs : List Witness)
  | restFrom (first : Nat)
  | append (left right : WitnessSeq)
  deriving DecidableEq, Repr

/-- The sequence at a call of `n` actuals: a rest the actuals' positions from
`first`, through the last actual, the positions past it, where the call
passes none, excluded. -/
def WitnessSeq.instantiate (n : Nat) : WitnessSeq → List Witness
  | .fixed xs => xs
  | .restFrom first => (((List.range n).map (· + 1)).filter (first ≤ ·)).map fun i => .path ⟨i, []⟩
  | .append a b => a.instantiate n ++ b.instantiate n

/-- **A transport stated over every entry slot** (the note's Call, the names
of the entry read at the exit): entry slot `i` is exit slot `i + shift` but
for finitely many replacements. -/
structure TransportSchema where
  shift : Nat
  overrides : List (Nat × Witness)
  boxed : Bool := false
  stable : List Nat := []
  deriving DecidableEq, Repr

/-- The transport at an entry scope of `entrySlots` slots, each with its
image. -/
def TransportSchema.instantiate (t : TransportSchema) (entrySlots : Nat) : Substitution :=
  ⟨((List.range entrySlots).map fun i => match t.overrides.lookup i with
      | some w => w
      | none => .path ⟨i + t.shift, []⟩).toArray, t.boxed, t.stable⟩

/-- The entry slots a transport's replacements name. -/
def TransportSchema.slots (t : TransportSchema) : Nat :=
  t.overrides.foldr (fun p k => max (p.1 + 1) k) 0

/-- **A two-state formula of a specification**: its appends' arguments
sequences of the call's values, its transports stated over every entry
slot. -/
abbrev FormulaSchema := FormulaF WitnessSeq TransportSchema

/-- The entry slots a schema formula's transports name. -/
def FormulaF.slots : FormulaSchema → Nat
  | .transport t => t.slots
  | .and F G => max F.slots G.slots
  | _ => 0

end Verification.Parity

namespace Verification.CallEffects
open Verification Footprints Parity

/-- **The instantiation of a specification at a call** (the note's Call):
the number of its actuals, and the entry scope a transport ranges over, the
receiver and the actuals among it. -/
structure CallInstantiation where
  actualCount : Nat
  entrySlots : Nat
  containsActuals : actualCount + 1 ≤ entrySlots

/-- A schema formula at a call. -/
def instantiateFormula (ι : CallInstantiation) (F : FormulaSchema) : Formula :=
  F.map (WitnessSeq.instantiate ι.actualCount) (TransportSchema.instantiate · ι.entrySlots)

/-- **A completion's guarantee as a signature states it** (the note, §6): its
frame, read at the call's entry, and its postconditions over the call's
values. -/
structure ExitSchema where
  frame : Footprint
  ensures : List FormulaSchema
  deriving DecidableEq, Repr

/-- Whether an exit schema references no arena node. -/
def ExitSchema.arenaFree (q : ExitSchema) : Bool := q.ensures.all (·.arenaFree)

/-- Whether both exits reference no arena node: a well-formed contract. -/
def Exits.arenaFree (x : Exits ExitSchema) : Bool := x.normal.arenaFree && x.exceptional.arenaFree

/-- The exit specification at a call. -/
def ExitSchema.instantiate (ι : CallInstantiation) (q : ExitSchema) : ExitSpec :=
  ⟨q.frame, q.ensures.map (instantiateFormula ι)⟩

/-- The entry slots a schema's transports name. -/
def ExitSchema.slots (q : ExitSchema) : Nat := q.ensures.foldr (fun F k => max F.slots k) 0

/-- The slots a list of formulas names, appended, are the larger of each
part's. -/
theorem FormulaSchema.foldr_slots_append (a b : List FormulaSchema) :
    (a ++ b).foldr (fun (F : FormulaSchema) k => max F.slots k) 0 =
      max (a.foldr (fun (F : FormulaSchema) k => max F.slots k) 0) (b.foldr (fun (F : FormulaSchema) k => max F.slots k) 0) := by
  induction a with
  | nil => simp
  | cons F t ih => simp only [List.cons_append, List.foldr_cons, ih, Nat.max_assoc]

/-- The entry slots both exits' transports name. -/
def Exits.slots (x : Exits ExitSchema) : Nat := max x.normal.slots x.exceptional.slots

/-- **The instantiation at a call of `n` actuals**: its entry scope the
receiver, the actuals and the slots the transports name. -/
def Exits.callInstantiation (x : Exits ExitSchema) (n : Nat) : CallInstantiation :=
  ⟨n, max (n + 1) x.slots, Nat.le_max_left _ _⟩

/-- **The specification at a call of `n` actuals** (the note's Call). -/
def Exits.atArity (x : Exits ExitSchema) (n : Nat) : Exits ExitSpec :=
  x.map (ExitSchema.instantiate (x.callInstantiation n))

/-- **An instantiated exit of a schema referencing no arena node holds alike
at every arena.** -/
theorem ExitSchema.holds_instantiate_arenaFree {q : ExitSchema} (hq : q.arenaFree = true) (ι : CallInstantiation)
    (arena arena' : AssertionArena) (s : TwoState) :
    (q.instantiate ι).Holds arena s ↔ (q.instantiate ι).Holds arena' s := by
  simp only [ExitSpec.Holds, ExitSchema.instantiate, List.forall_mem_map]
  refine and_congr Iff.rfl (forall_congr' fun F => imp_congr_right fun hF => holds_arenaFree ?_ arena arena' s)
  rw [instantiateFormula, FormulaF.arenaFree_map]
  exact List.all_eq_true.mp hq F hF

end Verification.CallEffects
