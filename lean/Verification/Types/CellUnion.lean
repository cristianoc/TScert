import Verification.Programs.CellClaims

/-! Exact absorption of redundant read/write record alternatives at the claim
boundary. This is a schema law about allowed reads and required writes, not an
inference rule for retaining observations of mutable storage. Every surviving
record must still have equal read/write meanings at the invariant-cell boundary. -/
namespace Verification.CellUnion
open Lean ProgramTyping PositiveRules LabelStore
open EquationGraphs (Tree)

variable {ι : Type}

/-- One field's read and write capabilities. A record alternative states one
of these per named field. -/
structure FieldContract (ι : Type) where
  name : PropKey
  read : List ι
  write : List ι
  deriving DecidableEq

abbrev Contract (ι : Type) := List (FieldContract ι)

def coversField [DecidableEq ι] (a b : FieldContract ι) : Bool :=
  a.name == b.name && a.read.all b.read.contains && decide (a.write = b.write)

/-- Every field the replacement states is covered by a field of the same name. -/
def covers [DecidableEq ι] (a b : Contract ι) : Bool := b.all fun f => a.any fun g => coversField g f

def invariant [DecidableEq ι] (c : Contract ι) : Bool := c.all fun f => f.read == f.write

/-- A readonly field accepts no write: its write capability is `never`. -/
def readonly [DecidableEq ι] (f : FieldContract ι) : Bool := f.write == []

/-- Every field is invariant or readonly: a record with views. -/
def viewed [DecidableEq ι] (c : Contract ι) : Bool := c.all fun f => f.read == f.write || readonly f

def select [DecidableEq ι] (cs : List (Contract ι)) (c : Contract ι) : Contract ι :=
  if invariant c then c else
    (cs.find? fun d => invariant d && covers c d).getD c

def normalize [DecidableEq ι] (cs : List (Contract ι)) : List (Contract ι) := cs.map (select cs)

/-- All arms are validated before absorption, including their field and object
modes. A remaining non-invariant arm rejects the entire union. A TypeScript
record type describes ordinary objects, so each invariant field's role is
`field`. -/
def lower (cs : List (Contract Tree)) : SourceTypes.Lowering (List (Ty Tree)) := do
  (normalize cs).mapM fun c => do
    if invariant c then return [← CellClaims.reference (c.map fun f => (f.name, .field, f.read))]
    if viewed c then
      let fields := (c.filter fun f => !readonly f).map fun f => (f.name, .field, f.read)
      let views := (c.filter readonly).map fun f => (f.name, f.read)
      return [← CellClaims.viewReference fields views]
    throw "cell read and write types do not describe the same invariant"

end Verification.CellUnion
