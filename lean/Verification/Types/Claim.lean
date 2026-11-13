import Verification.Semantics.Calculus
import Verification.Types.Decode

/-! # The claim language

What a producer says a type is, and what a source annotation is written in:
primitive values, the atoms that denote them, and the types built from those
atoms. A claim surface, not a second program calculus. The source adapter
rejects unsupported primitives; its exact-translation lemmas relate accepted
claims to the current semantics.

The decoder below is this language's own. The plumbing it reads JSON with is
shared, and lives in `Decode.lean`; the identity it gives a numeric literal is
the calculus's, and lives in `Calculus.lean`. -/
namespace Verification

namespace Claim

inductive Val where
  | vnull
  | vundef
  | vnum (bits : UInt64)
  | vstr (s : String)
  | vbool (b : Bool)
  /-- A bigint, as the integer it is. -/
  | vbigint (value : Int)
  deriving DecidableEq, Repr

inductive Atom where
  | null
  | undef
  | num
  | str
  | bool
  | numLit (bits : UInt64)
  | strLit (s : String)
  | boolLit (b : Bool)
  /-- A `void` result: no usable guarantee about the value, which may be
  any JavaScript value. Source lowering excludes internal array stores. -/
  | void
  /-- Every bigint, and every symbol. -/
  | bigint
  | symbol
  /-- One bigint: a bigint literal type, `1n`. -/
  | bigintLit (value : Int)
  deriving DecidableEq, Repr

/-- A type: `unknown` (`top`), or the union of a finite list of atoms.
An empty atom list with `top = false` is `never`. -/
structure Ty where
  top : Bool
  atoms : List Atom
  deriving DecidableEq, Repr

/-! Primitive claim membership used by exact-translation lemmas. -/

/-- `inhabits v a` : the value `v` is one of the values the atom `a` denotes. -/
def inhabits : Val → Atom → Bool
  | .vnull, .null => true
  | .vundef, .undef => true
  | .vnum _, .num => true
  | .vstr _, .str => true
  | .vbool _, .bool => true
  | .vnum b, .numLit c => b == c
  | .vstr s, .strLit t => s == t
  | .vbool b, .boolLit c => b == c
  | .vbigint _, .bigint => true
  | .vbigint i, .bigintLit j => i == j
  | _, .void => true
  | _, _ => false

end Claim
open Lean Claim

/-! ### Property keys -/

/-- A string key is its JSON string, so a document naming only string keys
reads as it always has; a symbol key is `{"symbol": id}`. -/
instance : ToJson PropKey where
  toJson
    | .str name => .str name
    | .sym id => Json.mkObj [("symbol", toJson id)]

instance : FromJson PropKey where
  fromJson?
    | .str name => .ok (.str name)
    | j => do
      let fields ← j.getObj?
      if fields.size != 1 then throw "a symbol key has exactly the field 'symbol'"
      return .sym (← (← j.getObjVal? "symbol").getNat?)

/-- The least canonical symbol number: every number a symbol key carries
in the single pass is at least it, above every index of a document's
`symbols` (`Fragment.canonicalSymbols`). -/
def symbolBase : Nat := 2 ^ 40

/-- A `unique symbol` declaration identity's canonical symbol number, a
function of the identity alone. -/
def symbolNumber (identity : Json) : Nat := symbolBase + (hash identity.compress).toNat % symbolBase

/-- A field name: a string key as its JSON string, a symbol key as
`{"symbol": id}`. -/
def PropKey.decode (j : Json) : Except String PropKey :=
  match j with
  | .str name => .ok (.str name)
  | j => do
    fieldsExactly j ["symbol"]
    return .sym (← (← jField j "symbol").getNat?)

/-! ### Atoms and types -/

def decodeBoolLiteral (j : Json) : Except String Bool := do
  match ← jStr (← jField j "v") with
  | "true" => return true
  | "false" => return false
  | _ => throw "boolean literal must be exactly true or false"

/-- A bigint literal's value, written as its canonical decimal integer: an
optional minus sign, then digits without a leading zero. The parser writes
every spelling (`0x10n`, `1_000n`, `-5n`) this way, so one value has one
spelling. -/
def decodeBigint (text : String) : Except String Int :=
  match text.toInt? with
  | some i => if toString i == text then .ok i
    else .error s!"not a canonical bigint literal: {text}"
  | none => .error s!"not a bigint literal: {text}"

def decodeAtom (j : Json) : Except String Atom := do
  let a ← jStr (← jField j "a")
  match a with
  | "null" => return .null
  | "undefined" => return .undef
  | "number" => return .num
  | "string" => return .str
  | "boolean" => return .bool
  | "numberlit" => return .numLit (← Verification.numBits (← jStr (← jField j "v")))
  | "stringlit" => return .strLit (← jStr (← jField j "v"))
  | "booleanlit" => return .boolLit (← decodeBoolLiteral j)
  | "void" => return .void
  | "bigint" => return .bigint
  | "symbol" => return .symbol
  | "bigintlit" => return .bigintLit (← decodeBigint (← jStr (← jField j "v")))
  | other => .error s!"unknown type atom '{other}'"

/-- The literal forms. An `Expr.lit` node denotes one value, so a "literal"
whose atom is a whole base type (`number`, say) is not a literal at all and is
rejected here rather than being smuggled past the checker. Rejecting it in the
decoder avoids treating a base type as a runtime literal. -/
def decodeVal (j : Json) : Except String Claim.Val := do
  let a ← jStr (← jField j "a")
  match a with
  | "null" => return .vnull
  | "undefined" => return .vundef
  | "numberlit" => return .vnum (← Verification.literalBits (← jStr (← jField j "v")))
  | "stringlit" => return .vstr (← jStr (← jField j "v"))
  | "booleanlit" => return .vbool (← decodeBoolLiteral j)
  | "bigintlit" => return .vbigint (← decodeBigint (← jStr (← jField j "v")))
  | other => .error s!"'{other}' is not a literal value"

/-- A type a producer could not express in the supported fragment decodes as `none`; the
checker then rejects wherever that type is actually needed. -/
def decodeTyOpt (j : Json) : Except String (Option Ty) := do
  match j.getObjVal? "unsupported" with
  | .ok _ => return none
  | .error _ =>
    let top ← (← jField j "top").getBool?
    let raw ← jArr j "atoms"
    -- These exported types belong to the stateful decoder. Keep them explicitly
    -- unsupported here; the cell and function decoders handle them separately.
    if raw.any (fun a => [some "record", some "function"].contains
        ((a.getObjValAs? String "a").toOption)) then return none
    let atoms ← raw.mapM decodeAtom
    return some { top := top, atoms := atoms }

def decodeTy (j : Json) : Except String Ty := do
  match ← decodeTyOpt j with
  | some t => return t
  | none => .error "a type outside the supported fragment"


end Verification
