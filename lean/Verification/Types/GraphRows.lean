import Verification.Types.PositiveGraphs

/-! A label-independent row representation, shared by the finite source
protocol and parameterized graph presentations. This module only presents
`NormalGraph`; it does not define another interpretation of recursive types. -/
namespace Verification.PositiveGraphs
open CallEffects PositiveNormalization

/-- One row of a graph, independent of how its labels are represented. A
finite wire table uses natural-number labels; a parameterized equation can
use symbolic applications. Names on parameter rows are diagnostic metadata.
The four alternatives are the same in both representations. -/
inductive GraphRow (ι : Type) (Operand : Type := List ι) where
  | clauses (union : List (Clause Operand))
  | scheme (binders : List ι) (signatures : List (Arrow Operand))
      (bounds : List (ι × Operand)) (variadic : List (RestArrow Operand))
      (resolution : List ResolutionSlots := []) (construct : Bool := false)
  | param (label : ι) (name : String) (kind : ParameterKind)
  | meet (binder : ι) (union : List (Clause Operand)) (also : List ι := [])
  deriving DecidableEq, Repr, Inhabited

/-- Rename binding positions and type operands separately. In an equation,
a binding position denotes one label while a type parameter can stand for a
whole union. In a closed graph the operands are lists of labels. -/
def GraphRow.map (binding : ι → κ) (operand : α → β) : GraphRow ι α → GraphRow κ β
  | .clauses cs => .clauses (cs.map (Clause.map operand))
  | .scheme bs sigs bounds rests resolution construct => .scheme (bs.map binding)
      (sigs.map (Arrow.map operand))
      (bounds.map fun (b, T) => (binding b, operand T))
      (rests.map (RestArrow.map operand)) resolution construct
  | .param b name kind => .param (binding b) name kind
  | .meet b cs also => .meet (binding b) (cs.map (Clause.map operand)) (also.map binding)

/-- Only a clause row contributes ordinary clauses. Other row kinds have
separate interpretations; an unsupported kind must not turn into a clause. -/
def GraphRow.union : GraphRow ι α → List (Clause α)
  | .clauses cs => cs
  | .scheme .. | .param .. | .meet .. => []

/-- The types mentioned by a row, including scheme binders and bounds.
A parameter's identity is metadata, checked separately by the wire boundary. -/
def GraphRow.operands : GraphRow ι → List (List ι)
  | .clauses cs => cs.flatMap Clause.operands
  | .scheme bs sigs bounds rests _ _ => bs :: sigs.flatMap Arrow.operands ++
      bounds.map (fun b => b.1 :: b.2) ++ rests.flatMap RestArrow.operands
  | .param _ _ _ => []
  | .meet p cs ps => (p :: ps) :: cs.flatMap Clause.operands

/-- Interpret a single, exhaustive row description. This is shared by the
finite protocol and equation graphs: no representation gets its own choices
about parameters, quantification or dependent intersections. -/
def NormalGraph.ofRowMap (row : ι → GraphRow ι)
    (builtins : Option (ArrayBuiltins ι) := none)
    (domain : SchemeDomain ι .mixed := .ordinary)
    (literal : LitKey → Option ι := fun _ => none) : NormalGraph ι :=
  { builtins, domain, literal
    rows i := (row i).union
    schemes i := match row i with
      | .scheme bs sigs bounds rests resolution construct =>
        some ⟨bs, sigs, bounds, rests, resolution, construct⟩
      | .clauses .. | .param .. | .meet .. => none
    parameterKinds i := match row i with
      | .param _ _ k => some k
      | .clauses .. | .scheme .. | .meet .. => none
    meets i := match row i with
      | .meet p cs _ => some (p, cs)
      | .clauses .. | .scheme .. | .param .. => none
    meetParams i := match row i with
      | .meet _ _ ps => ps
      | .clauses .. | .scheme .. | .param .. => [] }

/-- Whether a row is a clause row, a scheme, a parameter or a meet. -/
inductive RowForm where
  | clauses | scheme | param | meet
  deriving DecidableEq

def GraphRow.form : GraphRow ι α → RowForm
  | .clauses .. => .clauses
  | .scheme .. => .scheme
  | .param .. => .param
  | .meet .. => .meet

theorem GraphRow.form_map (b : ι → κ) (o : α → β) (r : GraphRow ι α) :
    GraphRow.form (r.map b o) = GraphRow.form r := by
  cases r <;> rfl

/-- `ofRowMap` with each field read at a label of another form answered from
the form alone: a test of a row's form (`NormalGraph.plain`) reads `form`
and builds no row. Equal to `ofRowMap` when `form` is each row's form
(`ofRowMapForms_eq`). -/
def NormalGraph.ofRowMapForms (row : ι → GraphRow ι) (form : ι → RowForm)
    (builtins : Option (ArrayBuiltins ι) := none)
    (domain : SchemeDomain ι .mixed := .ordinary)
    (literal : LitKey → Option ι := fun _ => none) : NormalGraph ι :=
  let G := NormalGraph.ofRowMap row builtins domain literal
  { G with
    rows t := if form t == .clauses then G.rows t else []
    schemes t := if form t == .scheme then G.schemes t else none
    parameterKinds t := if form t == .param then G.parameterKinds t else none
    meets t := if form t == .meet then G.meets t else none
    meetParams t := if form t == .meet then G.meetParams t else [] }

theorem NormalGraph.ofRowMapForms_eq {row : ι → GraphRow ι} {form : ι → RowForm}
    (h : ∀ t, form t = (row t).form) (builtins : Option (ArrayBuiltins ι))
    (domain : SchemeDomain ι .mixed) (literal : LitKey → Option ι) :
    NormalGraph.ofRowMapForms row form builtins domain literal =
      NormalGraph.ofRowMap row builtins domain literal := by
  simp only [NormalGraph.ofRowMapForms, NormalGraph.ofRowMap]
  congr 1 <;> funext t <;> rw [h t] <;> cases row t <;> simp [GraphRow.form, GraphRow.union]

end Verification.PositiveGraphs
