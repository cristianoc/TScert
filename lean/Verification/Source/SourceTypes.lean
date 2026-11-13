import Verification.Types.Claim
import Verification.Source.Equations.Store

/-! Source types and the graph they are checked against. A program's types
are labels of the store (`EquationStore.State`): extraction interns each compound
type the program mentions, so a label exists only because something used it,
and a clause the store lacks has no label rather than a wrong one. Primitive
unions translate into the four primitive labels. -/
namespace Verification.SourceTypes
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)
open EquationStore (State)

/-- The field an array object holds its store in. No source name spells it. -/
def storeField : PropKey := CallArguments.arrayStoreField

/-- The field an object holds its prototype in. No source name spells it. -/
def protoField : PropKey := CallArguments.protoField

/-- A key the model keeps for itself: the array store, the prototype, and
every other name in double brackets (`RequestJson.reservedKey`). -/
abbrev reservedKey : PropKey → Bool := RequestJson.reservedKey

/-- The module value holding `Array.prototype`: a name no source identifier
spells, at `ArrayProto`. Every array a unit allocates takes its prototype from
it, as JavaScript takes the built-ins'. -/
def arrayPrototypeName : String := "[[Array.prototype]]"

/-- The module values holding the primitive wrappers' prototypes, each at its
contract (`StringProto`, `NumberProto`, `BigIntProto`, `BooleanProto`), named
as `[[Array.prototype]]` is: a member of a primitive of the tag's shape is read
from it, as JavaScript's `ToObject` reads it from the built-ins'. -/
def primitivePrototypes : List (Tag × String) :=
  [(.isStr, "[[String.prototype]]"), (.isNum, "[[Number.prototype]]"),
   (.isBigint, "[[BigInt.prototype]]"), (.isBool, "[[Boolean.prototype]]")]

/-- The module value holding `Function.prototype`, at its contract
`FunctionProto`: a function's `toString` is read from it, the program's
functions owning none (SOURCE-CONTRACTS.md, "Function.prototype.toString") and
external code's assumed to own none (DESIGN.md, "Trust surface"). -/
def functionPrototypeName : String := "[[Function.prototype]]"

/-- Every builtins prototype a unit may read through, whether or not it names it. -/
def prototypeNames : List String :=
  arrayPrototypeName :: functionPrototypeName :: primitivePrototypes.map (·.2)

/-- An array type: its store at `store`, invariant or, for a readonly array, a
view; the prototype as a view at `proto`, `ArrayProto`; and none of `excluded`,
the keys `ArrayProto` provides plus `constructor`, `then` and `toJSON` (`arrayExcludedKeys`), among
its own keys, so a read of one of them continues at the prototype. -/
def arrayClause (excluded : List PropKey) (store proto : ι) (readonly : Bool) : Clause (List ι) :=
  PositiveNormalization.arrayClauseOf [store] [proto] excluded readonly

/-- The keys an array cannot own: `constructor`, `then`, `toJSON` and those `ArrayProto`'s row
(`proto`) names, its fields, views, optional fields and methods, the reserved
keys aside. An array owns none of them, so reading one continues at the
prototype; any other own key an array may have. -/
def arrayExcludedKeys (G : NormalGraph ι) (proto : ι) : List PropKey :=
  RequestJson.arrayExcludedKeysOf (expand G [proto])
where
  /-- Canonical excluded array keys (`RequestJson.arrayExcludedKeys`). -/
  ofKeys (ks : List PropKey) : List PropKey := RequestJson.arrayExcludedKeys ks

section
variable {ι : Type} [Labels ι]

def graph (T : State) : NormalGraph Tree := StoreView.graph T

/-- The array type over `store` in the store's own graph. -/
def arrayOf (T : State) (store : Tree) (readonly : Bool) : Clause (List Tree) :=
  arrayClause (arrayExcludedKeys (graph T) (StoreView.arrayProto T)) store (StoreView.arrayProto T) readonly

/-- The one user-facing rendering boundary for graph types. Labels are
implementation references into the store, so diagnostics must call this
function rather than interpolate a `Ty ι`. The fallback names the semantic
kind and never exposes a label. -/
private def clauseName : Clause (List ι) → String
  | .nul => "null"
  | .bool => "boolean"
  | .refs .. => "object"
  | .dict .. => "indexed object"
  | .arrs .. => "function"
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .num => "number"
  | .numLit _ => "numeric literal"
  | .undef => "undefined"
  | .callable .. => "callable object"
  | .top => "calculus top"
  | .source => "unknown"
  | .str => "string"
  | .strLit _ => "string literal"
  | .list .. => "array"
  | .pack .. => "argument list"
  | .bigint => "bigint"
  | .bigintLit _ => "bigint literal"
  | .symbol => "symbol"
  | .symbolLit _ => "unique symbol"
  | .ctors .. => "constructor"
  | .numIn _ => "numeric literal"
  | .strIn _ => "string literal"

/-- A type of any graph by its clauses' kinds, as `render` names them, an
array's as `array`. -/
def renderIn {ι : Type} [Labels ι] (G : NormalGraph ι) (A : Ty ι) : String :=
  match expand G A with
  | [] => "never"
  | [.boolLit true, .boolLit false] | [.boolLit false, .boolLit true] => "boolean"
  | cs => String.intercalate " | " (cs.map fun c => match c with
      | .refs fs _ vs .. => if ((fs ++ vs).lookup storeField).isSome then "array" else clauseName c
      | _ => clauseName c).eraseDups

def render (T : State) (A : Ty Tree) : String :=
  match expand (graph T) A with
  | [] => "never"
  | [.boolLit true, .boolLit false] | [.boolLit false, .boolLit true] => "boolean"
  | cs => String.intercalate " | " (cs.map clauseName).eraseDups

/-- Translation grows the store as it goes. -/
abbrev Lowering := StateT State (Except String)

/-- A union of clauses' label, interning it if the store lacks it. It
remains a union of its clauses; this does not make it an intersection or
assert a producer equation. -/
def useRow (row : List (Clause (List Tree))) : Lowering Tree :=
  modifyGet fun T => let (T, l) := EquationStore.intern T row; (l, T)

def use (c : Clause (List Tree)) : Lowering Tree := useRow [c]

/-- What a binder's parameter is met with when its bound is another binder,
read as `r`: the parameter `r`, within `r`'s clauses and parameters when `r`
is itself a meet. `U extends T` is `U ⊓ T`, which is below `T`
(`PositiveRules.meetBelow`): at every instantiation within the bound, the
meet is the binder. -/
def dependentMeet (T : State) (r : Tree) : Option (List (Clause (List Tree)) × List Tree) :=
  match StoreView.row T r with
  | .param _ _ .value => some ([.top], [r])
  | .meet q cs ps => some (cs, q :: ps)
  | _ => none

/-- Factor common parameter parts from a union of bounded rows. Distribution
preserves the union of clause constraints and every shared parameter. -/
def boundParts (T : State) (B : List Tree) : Option (List (Clause (List Tree)) × List Tree) := do
  let G := graph T
  let arms ← B.mapM fun r => if G.plain r then some (G r, []) else dependentMeet T r
  let parts := arms.headD ([], []) |>.2
  if arms.all (fun a => a.2 == parts) then some (arms.flatMap (·.1), parts) else none

/-- A bounded binder's label: the parameter `p` within `cs` and the
parameters `also` (`EquationStore.bounded`). -/
def bounded (p : Tree) (cs : List (Clause (List Tree))) (also : List Tree := []) : Lowering Tree :=
  modifyGet fun T => let (T, l) := EquationStore.bounded T p cs also; (l, T)


end

def admits (t : Claim.Ty) (v : Claim.Val) : Bool := t.atoms.any (Claim.inhabits v)

section
variable {ι : Type} [Labels ι]

def encode (t : Claim.Ty) : Ty ι :=
  (if admits t .vnull then [Labels.nul] else []) ++
  (if admits t (.vbool true) then [Labels.tru] else []) ++
  (if admits t (.vbool false) then [Labels.fls] else []) ++
  (if admits t .vundef then [Labels.undef] else [])

def supportedAtom : Claim.Atom → Bool
  | .null | .undef | .bool | .boolLit _ => true
  | _ => false

def translate (t : Claim.Ty) : Except String (Ty ι) :=
  if !t.top && t.atoms.all supportedAtom then .ok (encode t)
  else .error "source type outside the null/undefined/boolean/singleton fragment"

def value : Claim.Val → Except String Tm
  | .vnull => .ok .nul
  | .vundef => .ok .undef
  | .vbool true => .ok .tru
  | .vbool false => .ok .fls
  | .vnum b => .ok (.num b)
  | .vstr s => .ok (.str s)
  | .vbigint i => .ok (.bigint i)

/-- Numbers, strings, bigints and symbols are interned rather than given fixed
labels, because their singletons are unbounded; the four fixed labels are the
primitive values. -/
def numberLabels (t : Claim.Ty) : Lowering (Ty Tree) := do
  let mut out := []
  -- Two or more literals of one primitive are one tag set (HOST-FAMILIES.md,
  -- "Tag sets"), each element's own label interned beside it.
  let mut nums : List UInt64 := []
  let mut strs : List String := []
  for a in t.atoms do
    match a with
    | .numLit b =>
      -- TypeScript's literal type 0 includes both runtime zeros. The graph's
      -- bit singletons remain exact, so state both rather than erase a sign.
      nums := nums ++ [b]
      if Float.ofBits b == 0.0 then nums := nums ++ [(9223372036854775808 : UInt64)]
    | .strLit s => strs := strs ++ [s]
    | _ => pure ()
  nums := (nums.mergeSort (· ≤ ·)).eraseDups
  strs := (strs.mergeSort fun a b => decide (a ≤ b)).eraseDups
  for b in nums do
    let l ← use (.numLit b)
    if nums.length == 1 then out := out ++ [l]
  if nums.length ≥ 2 then out := out ++ [← use (.numIn nums)]
  for v in strs do
    let l ← use (.strLit v)
    if strs.length == 1 then out := out ++ [l]
  if strs.length ≥ 2 then out := out ++ [← use (.strIn strs)]
  for a in t.atoms do
    match a with
    | .num => out := out ++ [← use .num]
    | .str => out := out ++ [← use .str]
    | .bigint => out := out ++ [← use .bigint]
    | .bigintLit i => out := out ++ [← use (.bigintLit i)]
    | .symbol => out := out ++ [← use .symbol]
    -- A void value is any source value: primitives and objects, including
    -- callable and constructible objects. Internal array stores are separate.
    | .void => out := out ++ [← useRow EquationLowering.sourceValueClauses]
    | _ => pure ()
  return out

/-- Numbers and strings are interned, as their singletons are unbounded. -/
def isNumberAtom : Claim.Atom → Bool
  | .num | .numLit _ | .str | .strLit _ | .void | .bigint | .bigintLit _ | .symbol => true
  | _ => false

/-- One arm of a union: its numbers and strings interned, its fixed
primitives translated to the four fixed labels (`translate`). -/
def translateArm (t : Claim.Ty) : Lowering (Ty Tree) := do
  -- Source unknown contains JavaScript values, including opaque objects.
  if t.top then return [← use .source]
  let numbers ← numberLabels ⟨t.top, t.atoms.filter isNumberAtom⟩
  let others ← match translate ⟨t.top, t.atoms.filter (fun a => !isNumberAtom a)⟩ with
    | .ok A => pure A
    | .error e => throw e
  return (numbers ++ others).mergeSort Labels.le |>.eraseDups

end

end Verification.SourceTypes
