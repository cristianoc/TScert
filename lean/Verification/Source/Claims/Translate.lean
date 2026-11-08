import Verification.Source.Claims.Json

/-! Evidence searched over a unit's slice, written over its document's
store (STAGE-STORE.md, "Units of a check"). A slice's search writes its
evidence over the slice's store, whose heads are numbered as the slice's
extraction made them; the document's store numbers the same equations
otherwise. Each head of the slice is matched with a head of the document
that unfolds to the same infinite tree of names, parameters, binders and
rows (`signatures`), and every label of the evidence is renamed by that
match (`translate`).

Nothing here is trusted: the translated evidence is checked as any
evidence is (`unitVerdict`), so a wrong match, or a head without one, gives
evidence the check refuses. -/
namespace Verification.SourceClaimJson.Translate
open Lean EquationGraphs EquationLowering

mutual
/-- A tree with each head renamed by `f`, its meets made canonical again. -/
partial def mapTree (f : Nat → Nat) : Tree → Tree
  | .app h args => .app (f h) (mapArgs f args)
  | .bound h args j => .bound (f h) (mapArgs f args) j
  | .meet ps => canonMeet (mapTypes f ps).toList
  | t => t
partial def mapTypes (f : Nat → Nat) : Types → Types
  | .nil => .nil
  | .cons t ts => .cons (mapTree f t) (mapTypes f ts)
partial def mapArgs (f : Nat → Nat) : Args → Args
  | .nil => .nil
  | .cons ts args => .cons (mapTypes f ts) (mapArgs f args)
end

/-- A union in its canonical order, sorted and each tree once, as the
store keeps it: renaming heads changes the order. -/
def canonUnion (U : List Tree) : List Tree :=
  (U.mergeSort fun a b => compare a b != .gt).eraseDups

/-- A head's name with each run of digits read as one mark: a name holds
positions and table indices of the document it was made in, and its words
tell a declaration from a literal of the same row (`headMap`). -/
def spelling (name : String) : String :=
  String.ofList (name.toList.foldr (fun c acc => if c.isDigit then
    (match acc with | '#' :: _ => acc | _ => '#' :: acc) else c :: acc) [])

/-- One round of the heads' signatures: each head's parameter kinds,
binders, its previous signature and its row, with each head the row names
replaced by that head's previous signature. Equal signatures after `k`
rounds mean equal unfoldings `k` rows deep; the numbering of the store is
nowhere in them, nor are the heads' names: an interned row is named by the
site that made it first. -/
def round (heads : Array Draft) (previous : Array UInt64) : Array UInt64 :=
  heads.mapIdx fun i d =>
    let at_ (h : Nat) : Nat := (previous[h]?.getD 0).toNat
    let body := match d.body with
      | some b => (toJson (b.map (mapTree at_) (canonUnion ∘ List.map (mapTree at_)))).compress
      | none => "none"
    hash ((toJson d.kinds).compress,
      (toJson (d.binders.map fun b => (b.name, toJson b.kind))).compress, previous[i]?.getD 0, body)

/-- The number of distinct signatures. -/
def classes (sigs : Array UInt64) : Nat :=
  (sigs.foldl (fun (s : Std.HashSet UInt64) x => s.insert x) {}).size

/-- The signatures of a store's heads round by round, until a round
distinguishes no more heads than the one before: the rounds, the last one
stable. -/
def signatures (heads : Array Draft) : Array (Array UInt64) := Id.run do
  let mut rounds : Array (Array UInt64) := #[heads.map fun _ => 0]
  let mut count := 1
  for _ in [0:heads.size + 1] do
    let next := round heads rounds.back!
    rounds := rounds.push next
    let c := classes next
    if c == count then break
    count := c
  return rounds

/-- The signatures of `heads` after exactly `k` rounds, extending `rounds`. -/
def extend (heads : Array Draft) (rounds : Array (Array UInt64)) (k : Nat) : Array (Array UInt64) := Id.run do
  let mut rounds := rounds
  for _ in [0:k + 1 - rounds.size] do
    rounds := rounds.push (round heads rounds.back!)
  return rounds

/-- The document's heads with their signatures, computed once per check and
extended as a slice asks for more rounds. -/
structure Target where
  heads : Array Draft
  rounds : Array (Array UInt64)

def Target.of (heads : Array Draft) : Target := ⟨heads, signatures heads⟩

/-- The heads of the document each head of `slice` may be matched with:
those of the same signature at the rounds both stores need, in the
document's order. -/
def candidates (slice : Array Draft) (target : Target) : (Nat → Array Nat) × Target :=
  let own := signatures slice
  let k := max own.size target.rounds.size - 1
  let own := extend slice own k
  let rounds := extend target.heads target.rounds k
  let byHash := (rounds[k]!).foldl (init := (({} : Std.HashMap UInt64 (Array Nat)), 0))
    (fun (m, j) x => (m.insert x ((m.getD x #[]).push j), j + 1)) |>.1
  let mine := own[k]!
  (fun h => ((mine[h]?).bind byHash.get?).getD #[], ⟨target.heads, rounds⟩)

/-- How a head is chosen among several of the same signature, which the
document's checks may tell apart (a declaration's head and a literal's): one
of the same name (`spelling`), the latest made, or the earliest. -/
inductive Choice where
  | named | latest | earliest
  deriving BEq

/-- The head `choice` picks among `among` for a slice head named `name`. -/
def Choice.pick (choice : Choice) (heads : Array Draft) (name : String) (among : Array Nat) : Option Nat :=
  match choice with
  | .named => (among.find? fun j => (heads[j]?.map (spelling ·.name)) == some name) <|> among[0]?
  | .latest => among.back?
  | .earliest => among[0]?

/-- A label read from a slice's evidence and written as the document's. -/
structure Moved where
  tree : Tree
  /-- The label as the slice's evidence wrote it. -/
  original : Tree

instance : ToJson Moved := ⟨fun m => m.tree.toJson⟩

/-- Evidence over a slice's store, its heads `slice`, written over the
document's store, each label renamed by the head `choice` picks among its
candidates (`candidates`). A head with no candidate keeps its number, and
the evidence fails its check. -/
def translate (slice : Array Draft) (heads : Array Draft) (among : Nat → Array Nat) (choice : Choice)
    (evidence : Json) : Except String Json := do
  let f (h : Nat) : Nat := (choice.pick heads ((slice[h]?.map (spelling ·.name)).getD "") (among h)).getD h
  let _ : FromJson Moved := ⟨fun j => do let t ← Tree.fromJson j; return ⟨mapTree f t, t⟩⟩
  let d : EvidenceWire.Document Moved ← fromJson? evidence
  -- A union the slice wrote in its canonical order is written in the
  -- document's; any other keeps its order.
  let types := d.types.map fun ty =>
    let original := ty.map (·.original)
    if canonUnion original == original then (canonUnion (ty.map (·.tree))).map fun t => ⟨t, t⟩ else ty
  return toJson { d with types }

end Verification.SourceClaimJson.Translate

namespace Verification.SourceClaimJson
open Lean

/-- A slice's plans, for its search: its front at the qualified reads its
unit's reads document gives (`--produce-unit`), its imported modules left
out. Its claims are the producer's for the slice; claims that are the
producer's refusal refuse. -/
def slicePlans (ast claims qualified : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget) :
    Except String FilePlans := do
  if let .ok reason := claims.getObjValAs? String "refusal" then throw reason
  let qualified ← (← qualified.getArr?).toList.mapM fun q => do
    fieldsExactly q ["name", "footprint", "onThrow"]
    let footprint : Footprints.Closed ← fromJson? (← jField q "footprint")
    let onThrow : Bool ← fromJson? (← jField q "onThrow")
    return (← jStr (← jField q "name"), footprint, onThrow)
  let ast := ast.setObjVal! "modules" (Json.arr #[])
  let claims := claims.setObjVal! "modules" (Json.arr #[])
  let fr ← fileFront ast claims fileKey budget qualified
  let (T, plans) := fr.extractAll
  let F ← EquationStore.freeze T
  return ⟨⟨ast, claims, qualified, []⟩, fr, F, plans.map fun e => e.bind (FunctionPlan.over F)⟩

/-- A line of a slice's evidence: its unit, its evidence and the heads of
the slice's store it is written over. -/
def sliceLine (unit : String) (evidence : Json) (heads : EquationLowering.State) : Json :=
  Json.mkObj [("unit", toJson unit), ("evidence", evidence), ("heads", toJson heads)]

/-- A line of an evidence document: its unit and evidence, and, for a
slice's, the heads of the store its labels name. -/
def readLine (line : Json) : Except String (String × Json × Option (Array EquationLowering.Draft)) := do
  match line.getObjVal? "heads" with
  | .ok heads =>
    fieldsExactly line ["unit", "evidence", "heads"]
    let s : EquationLowering.State ← fromJson? heads
    return (← jStr (← jField line "unit"), ← jField line "evidence", some s.heads)
  | .error _ =>
    let (unit, evidence) ← readUnitLine line
    return (unit, evidence, none)

end Verification.SourceClaimJson
