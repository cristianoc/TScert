import Verification.Source.EquationDeclarations

/-! Section references follow `RECURSIVE-EQUATIONS.md`. -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-- The producer's rows, each with its own binders (a scheme row's) and the
binder names it mentions freely, in first-occurrence order. -/
structure ProducerRows where
  rows : Array (GraphRow Json (List Json))
  own : Array (List String)
  /-- The own binders whose argument lists, `T#pack`, the row reads: packed
  binders, one row read in both components. -/
  packed : Array (List String)
  free : Array (List String)
  deriving Inhabited

/-- Whether `own` binds the name `x`: a binder, or a binder's argument lists. -/
def ownsName (own : List String) (x : String) : Bool :=
  own.contains x || ((x.dropSuffix? "#pack").map fun b => own.contains b.toString).getD false

/-- The binder names and the rows a label mentions. A declaration's position
is no row. -/
partial def labelRefs (j : Json) : List String × List Nat :=
  let many (xs : List Json) : List String × List Nat :=
    xs.foldl (fun (ns, rs) x => let (n, r) := labelRefs x; (ns ++ n, rs ++ r)) ([], [])
  match j with
  | .num _ => ([], (j.getNat?).toOption.toList)
  | .arr xs => many xs.toList
  | .obj _ =>
    match (j.getObjValAs? String "binder").toOption with
    | some n => ([n], [])
    | none =>
      let unions (k : String) : List Json := ((j.getObjValAs? (Array Json) k).toOption.getD #[]).toList
      many (unions "args" ++ unions "meet" ++ ((j.getObjVal? "array").toOption.toList))
  | _ => ([], [])

/-- The producer's rows, decoded, with what each binds and names freely. -/
def producerRows (types : Array Json) : Except String ProducerRows := do
  let rows ← types.mapM fun j => (fromJson? j : Except String (GraphRow Json (List Json)))
  let own ← rows.mapM fun r => match r with
    | .scheme bs _ bounds _ resolution construct => do
      let binderName (b : Json) : Except String String := do
        fieldsExactly b ["binder"]
        str b "binder"
      let names ← bs.mapM binderName
      let boundNames ← bounds.mapM fun (b, _) => do
        return (← binderName b, ([] : List String))
      let scheme : SchemeRow String := ⟨names, [], boundNames, [], resolution, construct⟩
      if !scheme.resolutionValid then throw "invalid resolution slot metadata"
      return names
    | .clauses _ => pure []
    | _ => throw "a producer's row is a clause row or a scheme row; binders and intersections are labels"
  let direct := rows.map fun r => r.operands.foldl (fun (ns, rs) A =>
    let (n, r) := labelRefs (.arr A.toArray); (ns ++ n, rs ++ r)) (([] : List String), ([] : List Nat))
  if direct.any (fun (_, rs) => rs.any (· ≥ rows.size)) then throw "a label names no row of the table"
  -- The free names: a least fixpoint over the finitely many rows and names.
  let step (free : Array (List String)) : Array (List String) :=
    (Array.range rows.size).map fun n =>
      let (ns, rs) := direct[n]!
      ((ns ++ rs.flatMap fun m => free[m]!).filter (!ownsName own[n]! ·)).eraseDups
  let mut free : Array (List String) := rows.map fun _ => []
  let total := (direct.toList.flatMap (·.1)).eraseDups.length * rows.size + 1
  for _ in [0:total] do
    let next := step free
    if next == free then break
    free := next
  let packed := (Array.range rows.size).map fun n =>
    let (ns, rs) := direct[n]!
    let reads := ns ++ rs.flatMap fun m => free[m]!
    own[n]!.filter fun b => reads.contains (b ++ "#pack")
  -- A packed binder's argument lists, `T#pack`, are its row: one free name.
  let free' := free.map fun ns =>
    (ns.map fun x => ((x.dropSuffix? "#pack").map (·.toString)).getD x).eraseDups
  return { rows, own, packed, free := free' }

/-! ### Producer rows (§9.1)

A source-claims document's `types` rows are the producer's: clause rows, and
the scheme rows of classes' generic methods, whose binders are binder labels.
Each row is a head, lifted over the binder names it mentions freely (through
the rows it names too), as a literal is lifted over its binders (§8.1): a
row naming a binder of a unit is applied to that name's placeholder, and a
scheme row's own binders are its locals. -/

/-! ### The source-claims document's label lists -/

section
variable {m : Type → Type} [Monad m]

private def update (j : Json) (k : String) (f : Json → m Json) : m Json := do
  match j.getObjVal? k with
  | .ok v => return j.setObjVal! k (← f v)
  | .error _ => return j

private def each (f : Json → m Json) : Json → m Json
  | .arr xs => return .arr (← xs.mapM f)
  | j => return j

private def nullable (f : Json → m Json) : Json → m Json
  | .null => return .null
  | j => f j

/-- A claim type with each label list rewritten by `f`: labels, or a form
over claim types. With `pointForm`, `unitForm` and `documentForm`, the
claims document's label lists, in every unit: a claim's labels, what a point
asserts of each field, a call's type arguments. The traversal is the
document's shape (SOURCE-CLAIMS). -/
partial def claimForm (f : Json → m Json) (j : Json) : m Json := do
  match j with
  | .arr _ => f j
  | _ =>
    let j ← update j "union" (each (claimForm f))
    let j ← update j "array" (claimForm f)
    update j "scheme" fun s => do
      let s ← update s "typeParams" (each fun p => update p "bound" (nullable (claimForm f)))
      let s ← update s "this" (claimForm f)
      let s ← update s "params" (each (claimForm f))
      let s ← update s "rest" (nullable (claimForm f))
      update s "result" (claimForm f)

def pointForm (f : Json → m Json) (j : Json) : m Json := do
  let j ← update j "type" (claimForm f)
  let j ← update j "current" (nullable (each fun
    | .arr #[k, A] => do return .arr #[k, ← f A]
    | x => pure x))
  update j "instantiate" (nullable (each fun i => update i "type" (claimForm f)))

def unitForm (f : Json → m Json) (j : Json) : m Json := do
  let entries := each fun e => update e "bindings" (each (pointForm f))
  let j ← update j "params" (each (pointForm f))
  let j ← update j "result" (claimForm f)
  let j ← update j "entries" entries
  let j ← update j "expressions" (each (pointForm f))
  let j ← update j "contracts" (each fun c => update c "type" (claimForm f))
  update j "arrows" (each fun a => update a "rows" (each fun r => do
    let r ← update r "expressions" (each (pointForm f))
    let r ← update r "contracts" (each fun c => update c "type" (claimForm f))
    update r "entries" entries))

def documentForm (f : Json → m Json) (claims : Json) : m Json := do
  let claims ← update claims "functions" (each (unitForm f))
  update claims "init" (unitForm f)

end

/-- A union as its spelling (§9.2). -/
def unionJson (U : Union) : Json := .arr (U.map Tree.toJson).toArray


end Verification.EquationLowering
