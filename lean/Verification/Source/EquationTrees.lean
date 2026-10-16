import Verification.Types.EquationFamilies
import Verification.Types.EquationValidator
import Verification.Types.EquationJson
import Verification.Programs.CertificateProducer
import Verification.Source.RequestJson

/-! Section references follow `RECURSIVE-EQUATIONS.md`. -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-- A union of trees: in a template, operands may hold placeholders; outside
one, every tree is closed. -/
abbrev Union := List Tree

def mkApp (h : Nat) (args : List Union) : Tree := .app h (Args.ofList (args.map Types.ofList))

def mkBound (h : Nat) (args : List Union) (j : Nat) : Tree :=
  .bound h (Args.ofList (args.map Types.ofList)) j

/-- A union in canonical order, each tree once. -/
def normUnion (u : Union) : Union :=
  (u.mergeSort fun a b => compare a b != .gt).eraseDups

/-- `normUnion`, under a name the tree traversals below read. -/
abbrev normUnionOf (u : Union) : Union := normUnion u

/-! ### Trees -/

/- Whether a tree holds a template placeholder. -/
mutual
partial def treeOpen : Tree → Bool
  | .app _ args | .bound _ args _ => argsOpen args
  | .argument _ | .local _ => true
  | .var .. => false
  | .meet ps => ps.toList.any treeOpen
partial def argsOpen (args : Args) : Bool :=
  args.toList.any fun ts => ts.toList.any treeOpen
end

/- Simultaneous substitution of placeholders. A meet is distributed over its
parts' images, each distributed meet in canonical form (§3.3). -/
mutual
partial def treeSubst (argF : Nat → Union) (locF : Nat → Union) : Tree → Union
  | .app h args => [.app h (argsSubst argF locF args)]
  | .bound h args j => [.bound h (argsSubst argF locF args) j]
  | .argument i => argF i
  | .local j => locF j
  | .var o s k => [.var o s k]
  | .meet ps => (choices (ps.toList.map (treeSubst argF locF))).map canonMeet
partial def argsSubst (argF : Nat → Union) (locF : Nat → Union) (args : Args) : Args :=
  Args.ofList (args.toList.map fun ts => Types.ofList (ts.toList.flatMap (treeSubst argF locF)))
end

/- Replacing closed subtrees: `f` gives the union a tree stands for, or
`none` to keep it and look inside. A meet is distributed over its parts'
images, each distributed meet in canonical form; each argument union is
kept canonical. -/
mutual
partial def treeReplace (f : Tree → Option Union) (t : Tree) : Union :=
  match f t with
  | some U => U
  | none => match t with
    | .app h args => [.app h (argsReplace f args)]
    | .bound h args j => [.bound h (argsReplace f args) j]
    | .meet ps => (choices (ps.toList.map (treeReplace f))).map canonMeet
    | t => [t]
partial def argsReplace (f : Tree → Option Union) (args : Args) : Args :=
  Args.ofList (args.toList.map fun ts => Types.ofList (normUnionOf (ts.toList.flatMap (treeReplace f))))
end

/- Renaming heads, meets and argument unions re-canonicalized: their order
depends on head indices, and one type has one spelling. -/
mutual
partial def treeRename (f : Nat → Nat) : Tree → Tree
  | .app h args => .app (f h) (argsRename f args)
  | .bound h args j => .bound (f h) (argsRename f args) j
  | .meet ps => canonMeet (ps.toList.map (treeRename f))
  | t => t
partial def argsRename (f : Nat → Nat) (args : Args) : Args :=
  Args.ofList (args.toList.map fun ts => Types.ofList (normUnion (ts.toList.map (treeRename f))))
end

/-- Whether a tree holds an owned parameter or a variable. -/
partial def hasRigid : Tree → Bool
  | .bound .. | .var .. => true
  | .app _ args => args.toList.any fun ts => ts.toList.any hasRigid
  | .meet ps => ps.toList.any hasRigid
  | _ => false

/-- The distributed meet of unions (§3.3): one canonical meet per choice. A
single part is itself. -/
def meetUnions : List Union → Union
  | [A] => A
  | parts => normUnion ((choices parts).map canonMeet)

/-- Rows over trees, mapped operand by operand. -/
def mapRow (f : Union → Union) (row : GraphRow Tree (List Tree)) : GraphRow Tree (List Tree) :=
  row.map id f

/-! ### Equation labels

Equation labels are closed trees (`Tree`), store-independent: the four
primitive values are the nullary heads 0 to 3, which `primitives` allocates
first and compaction keeps first. -/

instance : LabelStore.Labels Tree where
  -- An extracted label's store still grows: instances are proposed over the
  -- frozen equations (`EquationStore.Checked`).
  propose _ _ _ := none
  toJson := Tree.toJson
  fromJson? j := Tree.fromJson j
  decEq := inferInstance
  nul := mkApp 0 []
  tru := mkApp 1 []
  fls := mkApp 2 []
  undef := mkApp 3 []

end Verification.EquationLowering
