import Std.Data.HashMap
import Verification.Source.Equations.ClaimWire

/-! Section references follow `RECURSIVE-EQUATIONS.md`. -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-! ### Heads under construction -/

inductive HeadKind where
  | primitive
  | declaration (index : Nat)
  | method (owner : Nat) (key : String)
  | literal
  | scheme
  | unit (key : String)
  | array (readonly : Bool)
  | proto
  deriving BEq, Repr, Inhabited

/-- A head as lowering builds it: `body` is filled once its row is lowered. -/
structure Draft where
  name : String
  kind : HeadKind
  kinds : List ParameterKind
  binders : List Binder := []
  body : Option (GraphRow Tree (List Tree)) := none
  /-- A scheme's declared binder defaults, by binder position, as its
  signatures read them: proposal metadata for the walk's instance choice
  (the producer's `default`, inference.ml:637-647), no part of the row. -/
  defaults : List (Nat × List Tree) := []
  deriving Inhabited

/-- A row still to lower. -/
inductive Job where
  | declaration (head index : Nat)
  | term (head : Nat) (ctx : Ctx) (term : Json)
  | store (head : Nat) (ctx : Ctx) (term : Json)
  | pack (head : Nat) (ctx : Ctx) (required : List Json) (rest : Option Json)
  | scheme (head : Nat) (ctx : Ctx) (term : Json)
  | unit (head : Nat) (ctx : Ctx) (node : Json)
  /-- A producer's row (§9.1): its index in the document's `types`. -/
  | row (head : Nat) (index : Nat)
  deriving Inhabited

def Job.head : Job → Nat
  | .declaration h _ | .term h .. | .store h .. | .pack h .. | .scheme h .. | .unit h .. | .row h _ => h

/-- A declared bound to check where an application is written (§8.2): the
actual union within the declared one. Inside a template, `owner` is the head
whose placeholders they hold. -/
structure Obligation where
  actual : Union
  upper : Union
  /-- The bounds of the placeholders `actual` and `upper` may hold. -/
  bounds : List (Tree × Union)
  site : String
  pos : Option Span

/-- An array or tuple annotation by its parts: what a reader of the
annotation's shape, a rest parameter's, needs (`Fragment.arrayElement`). -/
structure ArrayParts where
  required : List Union
  optional : List Union
  rest : Option Union
  readonly : Bool
  presence : Json
  deriving Inhabited

def ArrayParts.map (f : Union → Union) (a : ArrayParts) : ArrayParts :=
  { a with required := a.required.map f, optional := a.optional.map f, rest := a.rest.map f }

/-- An application's row: its head's template at its arguments, a local its
owned parameter (`Equations.baseRow`). -/
def instantiateRow (h : Nat) (args : Args) (body : GraphRow Tree (List Tree)) : GraphRow Tree :=
  let argF (i : Nat) : Union := ((args.toList[i]?).map Types.toList).getD []
  let locF (j : Nat) : Union := [.bound h args j]
  let sub (U : Union) : Union := U.flatMap (treeSubst argF locF)
  body.map (fun t => (sub [t]).headD t) sub

/-- A head's row at no arguments; an empty clause row for a head without a
body. -/
def nullaryRow (heads : Array Draft) (h : Nat) : GraphRow Tree :=
  match heads[h]?.bind (·.body) with
  | some body => instantiateRow h .nil body
  | none => .clauses []

/-- Each head's row at no arguments, instantiated when first read. -/
def nullaryOf (heads : Array Draft) : Array (Thunk (GraphRow Tree)) :=
  Array.ofFn (n := heads.size) fun h => Thunk.mk fun _ => nullaryRow heads h

/-- A pushed head keeps every other head's row read so far. -/
theorem nullaryOf_push (heads : Array Draft) (d : Draft) :
    nullaryOf (heads.push d) =
      (nullaryOf heads).push (Thunk.mk fun _ => nullaryRow (heads.push d) heads.size) := by
  apply Array.ext
  · simp [nullaryOf]
  · intro i h1 h2
    rw [Array.getElem_push]
    split
    · next hi =>
      have hi' : i < heads.size := by simpa [nullaryOf] using hi
      simp only [nullaryOf, Array.getElem_ofFn, nullaryRow, Array.getElem?_push_lt hi', Array.getElem?_eq_getElem hi']
    · next hi =>
      have : i = heads.size := by simp [nullaryOf] at h1 hi; omega
      subst this
      simp [nullaryOf]

/-- A head's body set keeps every other head's row read so far. -/
theorem nullaryOf_modify (heads : Array Draft) (h : Nat) (f : Draft → Draft) :
    nullaryOf (heads.modify h f) =
      (nullaryOf heads).set! h (Thunk.mk fun _ => nullaryRow (heads.modify h f) h) := by
  apply Array.ext
  · simp [nullaryOf]
  · intro i h1 h2
    have hi' : i < (nullaryOf heads).size := by simpa [nullaryOf] using h1
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hi']
    split
    · next hi => subst hi; simp [nullaryOf]
    · next hi =>
      simp only [nullaryOf, Array.getElem_ofFn, nullaryRow, Array.getElem?_modify, hi, if_false]

structure State where
  /-- Execution policy; the equation document records only the types. -/
  subtypeBudget : PositiveCertificates.SearchBudget := {}
  doc : Array Definition
  /-- `doc`'s indices by identity (`identityIndex doc`). -/
  identities : Std.HashMap Json (List Nat) := {}
  /-- `doc`'s packed parameters, by index (`packedParameters` of each
  declaration's expression): read at every reference, computed once. -/
  packings : Array (List Nat) := #[]
  heads : Array Draft := #[]
  /-- `heads`' rows at no arguments, each instantiated when first read and
  kept while its head is unchanged (`EquationStore.graph`). -/
  nullary : Array (Thunk (GraphRow Tree)) := nullaryOf heads
  nullary_eq : nullary = nullaryOf heads := by rfl
  keys : Std.HashMap String Nat := {}
  jobs : List Job := []
  processing : List Nat := []
  excluded : List PropKey := []
  arrays : Bool := false
  obligations : List Obligation := []
  /-- Each written intersection's union of meets, with where it is written:
  an intersection none of whose meets has a value is refused there. -/
  meetChecks : List (Union × String) := []
  /-- Each generic unit's binders, by the unit's path. -/
  scopes : List (String × List (String × Binding)) := []
  /-- Each generic unit's binders, by the unit's path: each an owned
  parameter of the unit's head, with its declared bound, if any, over those
  parameters. -/
  unitBinders : List (String × List (String × Tree × Option Union)) := []
  /-- The binder names the source spells, each with its kind: the slots of
  the name placeholders (`placeholder`). -/
  names : Array (String × ParameterKind) := #[]
  /-- The names of the fresh placeholders `EquationStore.binders` has made, by slot. -/
  fresh : Array String := #[]
  /-- The built-in array prototype head, once lowered. -/
  proto : Option Nat := none
  /-- The stable non-thenable family, the reviewed intrinsic `%Stable%`. -/
  nativeStable : Option Union := none
  /-- Each array or tuple annotation's parts, by its path. -/
  arrayAnnotations : List (String × ArrayParts) := []
  /-- The producer's rows the claims name (§9.1). -/
  rows : ProducerRows := default
  /-- The declaration document's entries for the standard library's
  `Symbol.toStringTag`, by index: the symbol keys no object the source makes
  holds. -/
  tags : List Nat := []

abbrev M := StateT State (Except String)

/-- The packed parameters of the declaration at `i` (`State.packings`); none
for an index the document does not hold, as `doc[i]!`'s default expression
has none. -/
def packedOf (i : Nat) : M (List Nat) := return (← get).packings[i]?.getD []


end Verification.EquationLowering
