import Verification.Source.Claims.Json
import Verification.Types.StoreMapsCheck

/-! # A module interface's rows and the store-map checks on them

An interface entry states the type its function is read at in its module's
store (its interface type) as rows of a table of its own: the module's rows
on the region its interface types reach, numbered from `0`, with the
built-ins. The module publishes an entry only where the store-map check
(`StoreMaps.matchStores`, proved sound by `matchStores_sound`) relates its
own store's interface type to the decoded table's; an importer reads an
entry only where the check relates the table's type to the type its own
store reads the import at. The two checks give the importer's slot type
the module's interface's meaning (`signatureAgrees_of_checks`,
docs/drafts/pass-unit-theorem.md, section 7). -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping SourceExtraction LabelStore PositiveGraphs
open EquationGraphs (Tree)

/-- A module's interface rows, decoded: the table's rows by position, its
built-ins, and each published function's interface type as positions. -/
structure RowTable where
  rows : Array (GraphRow Nat)
  builtins : Option (ArrayBuiltins Nat)
  interfaces : List (String × List Nat)

/-- The graph a table presents. -/
def RowTable.graph (t : RowTable) : NormalGraph Nat :=
  NormalGraph.ofRowMap (fun n => t.rows.getD n (.clauses [])) t.builtins

/-- The labels a label's row names, as the store-map check's region needs
them: what it reads, its meet's parts, its scheme's binders and bounds'
binders. -/
@[nospecialize] def rowNeighbours {ι : Type} (G : NormalGraph ι) (i : ι) : List ι :=
  PositiveRules.reads G i ++ PositiveRules.meetParts G i ++
    match G.schemes i with
    | some s => s.binders ++ s.bounds.map (·.1)
    | none => []

/-- The region of a graph the roots reach, with the built-ins' types, in
the order first reached. -/
@[nospecialize] def rowRegion {ι : Type} [BEq ι] [Hashable ι] (G : NormalGraph ι) (roots : List ι) : Array ι := Id.run do
  let start := roots ++ match G.builtins with
    | some b => b.proto ++ b.unknown
    | none => []
  let mut seen : Std.HashSet ι := {}
  let mut out : Array ι := #[]
  let mut stack := start.reverse
  -- (each label is pushed once per row naming it: the rows' total size bounds the loop)
  while true do
    match stack with
    | [] => break
    | i :: rest =>
      stack := rest
      if seen.contains i then continue
      seen := seen.insert i
      out := out.push i
      stack := (rowNeighbours G i).reverse ++ stack
  return out

/-- The built-ins on the wire. -/
def builtinsWire (b : Option (ArrayBuiltins Nat)) : Json :=
  match b with
  | some b => Json.mkObj [("proto", toJson b.proto), ("unknown", toJson b.unknown), ("keys", toJson b.keys)]
  | none => Json.null

/-- **A module's interface rows**: the rows of the store `T` on the region
the interface types `ifaces` reach, each label at its position in the
region, as a wire table (`types`, `builtins`), and each interface type as
positions in it. -/
def encodeRowTable {σ ι : Type} [Labels ι] [StoreView σ ι] (T : σ) (ifaces : List (String × List ι)) :
    Json × List (String × List Nat) :=
  let G := StoreView.graph T
  let region := rowRegion G (ifaces.flatMap (·.2))
  let pos : Std.HashMap ι Nat := region.zipIdx.foldl (fun m (l, n) => m.insert l n) {}
  let at_ := fun (l : ι) => pos.getD l 0
  let rows := region.toList.map fun l => (StoreView.row T l).map at_ (·.map at_)
  let builtins := G.builtins.map fun b => ({ proto := b.proto.map at_, unknown := b.unknown.map at_, keys := b.keys } :
    ArrayBuiltins Nat)
  (Json.mkObj [("types", toJson rows), ("builtins", builtinsWire builtins)], ifaces.map fun (n, A) => (n, A.map at_))

/-- A table's rows on the wire. -/
def RowTable.rowsWire (t : RowTable) : Json :=
  Json.mkObj [("types", toJson t.rows.toList), ("builtins", builtinsWire t.builtins)]

/-- Decode a module's interface rows, requiring their shape field by field
and every position in the table, with its functions' interface types. -/
def decodeRowTable (j : Json) (interfaces : List (String × List Nat)) : Except String RowTable := do
  fieldsExactly j ["types", "builtins"]
  let rows : List (GraphRow Nat) ← fromJson? (← jField j "types")
  let n := rows.length
  let inTable := fun (ls : List Nat) => ls.all (· < n)
  let named : GraphRow Nat → List Nat
    | .param l _ _ => [l]
    | r => r.operands.flatten
  unless rows.all (fun r => inTable (named r)) do throw "interface rows name a position outside their table"
  let builtins ← match ← jField j "builtins" with
    | .null => pure none
    | b => do
      fieldsExactly b ["proto", "unknown", "keys"]
      let proto : List Nat ← fromJson? (← jField b "proto")
      let unknown : List Nat ← fromJson? (← jField b "unknown")
      let keys : List PropKey ← fromJson? (← jField b "keys")
      unless inTable proto && inTable unknown do throw "interface built-ins outside their table"
      pure (some { proto, unknown, keys })
  unless interfaces.all (fun (_, A) => inTable A) do throw "an interface type outside its table"
  return ⟨rows.toArray, builtins, interfaces⟩

/-- The fuel of a store-map check from roots over a table of `n` rows. -/
def matchFuel (n : Nat) : Nat := 8 * n + 64

/-- **The module's check of an entry's rows**: the store-map check from the
module's interface type `I` in its store to the table's type for the
function, each table operand the module's renamed as the table lists it. -/
def moduleRowsAgree {σ ι : Type} [Labels ι] [StoreView σ ι] (T : σ) (t : RowTable) (name : String) (I : List ι) :
    Bool :=
  match t.interfaces.lookup name with
  | some A => (StoreMaps.matchStores (StoreView.graph T) t.graph id (matchFuel t.rows.size) I A).isSome
  | none => false

/-- **The importer's check of a read**: the store-map check from the
table's type for the function to the type `A` the importer's store reads it
at, each image operand a canonical union of the importer's store (sorted,
each label once). -/
def importerRowsAgree {σ ι : Type} [Labels ι] [StoreView σ ι] (T : σ) (t : RowTable) (name : String) (A : List ι) :
    Bool :=
  have : Inhabited ι := ⟨Labels.nul⟩
  match t.interfaces.lookup name with
  | some I => (StoreMaps.matchStores t.graph (StoreView.graph T) (fun S => (S.mergeSort Labels.le).eraseDups)
      (matchFuel t.rows.size) I A).isSome
  | none => false

/-- The module values unit `j`'s request captures, in its frame's order
after its parameters: the values its extraction reaches
(`extractMember`), each of those its body mentions (`moduleReadNames`). -/
def Front.captureNames (fr : Front) (j : Nat) : List String :=
  match fr.units[j]? with
  | none => []
  | some (fn, _, initClaims) =>
    let base := if initClaims.isSome then fr.moduleFunctions ++ fr.classSelves
      else fr.moduleFunctions ++ fr.moduleConstants
    let generic := (fr.generics.filter fun g => !(initClaims.isSome && fr.classNames.contains g.name)).filter fun g =>
      (fn.body.flatMap Fragment.Stmt.callees).any (·.2.2.1 == g.name) || (Fragment.stmtsFreeNames fn.body).contains g.name
    let mentioned := moduleReadNames fn.body
    (base.map (·.1) ++ generic.map (·.name)).filter mentioned.contains

/-- Each unit's captures by name: the module values it reads, each at the
type its request's frame states (`captureNames`). -/
def FilePlans.captures (f : FilePlans) (j : Nat) : List (String × Ty (EquationStore.CheckedLabel f.F.equations f.F.primitive)) :=
  match f.plans[j]? with
  | some (.ok (.graph _ _ r)) =>
    let names := f.fr.captureNames j
    if names.length > r.inputs.length then [] else names.zip (r.inputs.drop (r.inputs.length - names.length))
  | _ => []

end Verification.SourceClaimJson
