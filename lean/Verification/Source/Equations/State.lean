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

structure State where
  /-- Execution policy; the equation document records only the types. -/
  subtypeBudget : PositiveCertificates.SearchBudget := {}
  doc : Array Definition
  heads : Array Draft := #[]
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

abbrev M := StateT State (Except String)


end Verification.EquationLowering
