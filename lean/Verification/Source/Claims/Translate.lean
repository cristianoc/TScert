import Verification.Source.Claims.Json

/-! Evidence searched over a unit's slice, written over its document's
store (STAGE-STORE.md, "Units of a check"). A slice's search writes its
evidence over the slice's store, whose heads are numbered as the slice's
extraction made them; the document's store numbers the same equations
otherwise. The unit's own requests, extracted from the same code in both,
are the anchors: each label a request of the slice names stands where the
document's request of the same unit names its label (`pairJson`), and each
pair of heads so found pairs their templates' labels in turn (`propagate`).
A union is paired member by member: a member whose image is known with that
image, and the others by their shape, each head read as the class of heads
whose rows unfold alike (`signatures`), in order among members of one
shape. Every label of the evidence is renamed by that correspondence
(`translate`), and a union the slice wrote in its canonical order is written
in the document's.

Nothing here is trusted: the translated evidence is checked as any
evidence is (`unitVerdict`), so a wrong correspondence, or a head without
one, gives evidence the check refuses. -/
namespace Verification.SourceClaimJson.Translate
open Lean EquationGraphs EquationLowering PositiveGraphs

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

/-- One round of the heads' signatures: each head's parameter kinds,
binders, its previous signature and its row, with each head the row names
replaced by that head's previous signature. Equal signatures after `k`
rounds mean equal unfoldings `k` rows deep; the numbering of the store is
nowhere in them, nor are the heads' names. -/
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

/-- The correspondence as it grows: each slice head's document head, and the
pairs whose templates are still to pair. -/
structure Pairing where
  map : Std.HashMap Nat Nat := {}
  pending : List (Nat × Nat) := []

/-- The two stores' heads and each head's class (`signatures`). -/
structure Sides where
  slice : Array Draft
  document : Array Draft
  sliceClass : Nat → UInt64
  documentClass : Nat → UInt64

abbrev PairM := ReaderT Sides (StateM Pairing)

/-- A tree's shape: each head read as its class. -/
def shape (cls : Nat → UInt64) (t : Tree) : UInt64 := hash (mapTree (fun h => (cls h).toNat) t)

/-- A slice tree's image, where every head it names has one. -/
partial def image (m : Std.HashMap Nat Nat) : Tree → Option Tree
  | .app h args => do return .app (← m.get? h) (← imageArgs m args)
  | .bound h args j => do return .bound (← m.get? h) (← imageArgs m args) j
  | .meet ps => do return canonMeet (← ps.toList.mapM (image m))
  | t => some t
where
  imageArgs (m : Std.HashMap Nat Nat) : Args → Option Args
    | .nil => some .nil
    | .cons ts rest => do
      return .cons (← ts.toList.foldr (fun t acc => do return .cons (← image m t) (← acc)) (some .nil))
        (← imageArgs m rest)

/-- Pair a slice head with a document head; a head already paired keeps its
first partner. -/
def pairHead (h h' : Nat) : PairM Unit := do
  let p ← get
  if p.map.contains h then return
  set { p with map := p.map.insert h h', pending := (h, h') :: p.pending }

mutual
/-- Pair two trees of the same form, head with head and argument with
argument. -/
partial def pairTree : Tree → Tree → PairM Unit
  | .app h args, .app h' args' => do pairHead h h'; pairArgs args args'
  | .bound h args j, .bound h' args' j' => if j == j' then do pairHead h h'; pairArgs args args' else pure ()
  | .meet ps, .meet ps' => pairUnion ps.toList ps'.toList
  | _, _ => pure ()
partial def pairArgs : Args → Args → PairM Unit
  | .cons U rest, .cons V rest' => do pairUnion U.toList V.toList; pairArgs rest rest'
  | _, _ => pure ()
/-- Pair two unions of as many members: a member whose image is known with
that image, then each other member with the first left of the same shape. -/
partial def pairUnion (U V : List Tree) : PairM Unit := do
  if U.length != V.length then return
  let sides ← read
  let m := (← get).map
  let mut left : List Tree := []
  let mut right := V
  for u in U do
    match image m u with
    | some v => if right.contains v then right := right.erase v else left := left ++ [u]
    | none => left := left ++ [u]
  for u in left do
    let su := shape sides.sliceClass u
    match right.find? (shape sides.documentClass · == su) with
    | some v =>
      right := right.erase v
      pairTree u v
    | none => pure ()
end

/-- Pair two anchor documents: a marked label with a marked label, an array
of marked labels (a union) as a union, any other array element by element
and an object field by field. -/
partial def pairJson (a b : Json) : PairM Unit := do
  let mark (j : Json) : Option Tree := match j.getObjVal? "§label" with
    | .ok t => (Tree.fromJson t).toOption
    | .error _ => none
  match a, b with
  | .arr xs, .arr ys =>
    if xs.size != ys.size then return
    let us := xs.toList.filterMap mark
    let vs := ys.toList.filterMap mark
    if us.length == xs.size && vs.length == ys.size && xs.size > 0 then pairUnion us vs
    else for (x, y) in xs.toList.zip ys.toList do pairJson x y
  | .obj kvs, .obj _ =>
    match mark a, mark b with
    | some s, some d => pairTree s d
    | _, _ =>
      for (k, x) in kvs.toList do
        if let .ok y := b.getObjVal? k then pairJson x y
  | _, _ => pure ()

/-- A row with every label and union erased: what two templates share when
they pair label for label. -/
def erased (d : Draft) : String :=
  (toJson (d.kinds, d.binders.map (fun b => toJson b.kind),
    d.body.map fun b => b.map (fun _ => Tree.argument 0) (fun (_ : List Tree) => ([] : List Tree)))).compress

/-- Pair the templates of each pair of heads found, until none is left. -/
partial def propagate : PairM Unit := do
  let p ← get
  match p.pending with
  | [] => return
  | (h, h') :: rest =>
    set { p with pending := rest }
    let sides ← read
    if let (some d, some d') := (sides.slice[h]?, sides.document[h']?) then
      if let (some b, some b') := (d.body, d'.body) then
        if erased d == erased d' then
          for (U, V) in b.operands.zip b'.operands do pairUnion U V
    propagate

/-- Pair each slice head whose row is a union of clauses at no parameter
(a literal's, a string set's) with the document head the store finds for
those clauses, its labels renamed: the first of the document's heads with
that row, as the store's `ground` key names it (`EquationStore.lookup`),
the head a search over the document reads a literal at. Repeated while a
pairing lets another row be renamed, its templates paired in turn. -/
partial def grounds : PairM Unit := do
  let sides ← read
  let key (b : GraphRow Tree (List Tree)) : String := (toJson b).compress
  let found : Std.HashMap String Nat := sides.document.zipIdx.foldl (fun m (d, j) =>
    match d.kinds, d.body with
    | [], some b@(.clauses _) => if m.contains (key b) then m else m.insert (key b) j
    | _, _ => m) {}
  let rec go : PairM Unit := do
    let m := (← get).map
    let mut grew := false
    for (d, h) in sides.slice.zipIdx do
      if m.contains h then continue
      match d.kinds, d.body with
      | [], some (.clauses cs) =>
        let renamed : Option (List (PositiveNormalization.Clause (List Tree))) := cs.mapM fun c =>
          c.operands.flatten.mapM (image m) |>.map fun _ =>
            c.map fun U => canonUnion (U.filterMap (image m))
        if let some cs' := renamed then
          if let some j := found.get? (key (.clauses cs')) then
            pairHead h j
            grew := true
      | _, _ => pure ()
    if grew then
      propagate
      go
  go

/-- The order the document writes each union in, by its members in
canonical order: as its anchors write it (`pairJson`'s unions) and as its
heads' rows do, the first writing of each with no member twice. -/
partial def orders (heads : Array Draft) (anchors : Json) : Std.HashMap (List Tree) (List Tree) := Id.run do
  let mut out : Std.HashMap (List Tree) (List Tree) := {}
  let note (out : Std.HashMap (List Tree) (List Tree)) (U : List Tree) :=
    if U.length < 2 || U.eraseDups.length != U.length || out.contains (canonUnion U) then out
    else out.insert (canonUnion U) U
  let mark (j : Json) : Option Tree := match j.getObjVal? "§label" with
    | .ok t => (Tree.fromJson t).toOption
    | .error _ => none
  let rec walk (out : Std.HashMap (List Tree) (List Tree)) (j : Json) : Std.HashMap (List Tree) (List Tree) :=
    match j with
    | .arr xs =>
      let us := xs.toList.filterMap mark
      if us.length == xs.size && xs.size > 0 then note out us else xs.foldl walk out
    | .obj kvs => kvs.toList.foldl (fun out (_, x) => walk out x) out
    | _ => out
  out := walk out anchors
  for d in heads do
    if let some b := d.body then
      for U in b.operands do
        out := note out U
  return out

/-- A label read from a slice's evidence and written as the document's. -/
structure Moved where
  tree : Tree
  /-- The label as the slice's evidence wrote it. -/
  original : Tree

instance : ToJson Moved := ⟨fun m => m.tree.toJson⟩

/-- Evidence over a slice's store, its heads `slice` and its unit's anchors
`anchors`, written over the document's store `target`, whose unit's anchors
are `documentAnchors`: each label renamed by the correspondence the anchors
give. A head with none keeps its number, and the evidence fails its check.
Also the document's signatures, extended. -/
def translate (slice : Array Draft) (anchors : Json) (target : Target) (documentAnchors : Json)
    (evidence : Json) : Except String Json × Target :=
  let own := signatures slice
  let k := max own.size target.rounds.size - 1
  let own := extend slice own k
  let rounds := extend target.heads target.rounds k
  let target : Target := ⟨target.heads, rounds⟩
  let sides : Sides := {
    slice, document := target.heads
    sliceClass := fun h => (own[k]!)[h]?.getD 0
    documentClass := fun h => (rounds[k]!)[h]?.getD 0 }
  let ((), p) := ((do pairJson anchors documentAnchors; propagate; grounds : PairM Unit).run sides).run {}
  let f (h : Nat) : Nat := p.map.getD h h
  let written : Except String Json := do
    let _ : FromJson Moved := ⟨fun j => do let t ← Tree.fromJson j; return ⟨mapTree f t, t⟩⟩
    let d : EvidenceWire.Document Moved ← fromJson? evidence
    -- A union the slice wrote in an order of its own keeps it, each member
    -- once. One it wrote in its canonical order is written as the document
    -- writes its members where its anchors or its heads' rows write them
    -- (`orders`), else in the document's canonical order.
    let known := orders target.heads documentAnchors
    let types := d.types.map fun ty =>
      let original := ty.map (·.original)
      let moved := ty.map (·.tree)
      let written := if canonUnion original != original then moved.eraseDups
        else (known.get? (canonUnion moved)).getD (canonUnion moved)
      written.map fun t => ⟨t, t⟩
    return toJson { d with types }
  (written, target)

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

/-- The anchors of a group's units (`Translate.pairJson`): each member's
request, with its labels marked and its store left out, its search hints and
its obligations' sequents. -/
def FilePlans.anchors (f : FilePlans) (group : List Nat) : Json :=
  let _ : ToJson (EquationStore.CheckedLabel f.F.equations f.F.primitive) :=
    ⟨fun l => Json.mkObj [("§label", l.tree.toJson)]⟩
  Json.arr (group.map fun i => match f.plans[i]? with
    | some (.ok (.graph _ _ r)) => Json.mkObj [
        ("request", toJson ({ r.toRequest with types := Json.null } : RequestJson.Request Json _)),
        ("hints", toJson r.hints),
        ("obligations", toJson (r.obligations.map fun o => (o.sequent.context, o.sequent.type)))]
    | _ => Json.null).toArray

/-- A line of a slice's evidence: its unit, its evidence, the heads of the
slice's store it is written over and the unit's anchors. -/
def sliceLine (unit : String) (evidence : Json) (heads : EquationLowering.State) (anchors : Json) : Json :=
  Json.mkObj [("unit", toJson unit), ("evidence", evidence), ("heads", toJson heads), ("anchors", anchors)]

/-- A line of an evidence document: its unit and evidence, and, for a
slice's, the heads of the store its labels name and the unit's anchors. -/
def readLine (line : Json) : Except String (String × Json × Option (Array EquationLowering.Draft × Json)) := do
  match line.getObjVal? "heads" with
  | .ok heads =>
    fieldsExactly line ["unit", "evidence", "heads", "anchors"]
    let s : EquationLowering.State ← fromJson? heads
    return (← jStr (← jField line "unit"), ← jField line "evidence", some (s.heads, ← jField line "anchors"))
  | .error _ =>
    let (unit, evidence) ← readUnitLine line
    return (unit, evidence, none)

/-- **The verdict of a unit's line** as `--check-units` gives it: a line of
the document's own evidence checked as written (`unitVerdict`); a slice's
line written over the document's store first (`Translate.translate`), its
unit's anchors paired with the group's in the document (`FilePlans.anchors`),
and checked at the evidence so written. Also the document's signatures, as
the translation extended them. -/
def lineVerdict (f : FilePlans) (budget : PositiveCertificates.SearchBudget) (target : Translate.Target)
    (unit : String) (evidence : Json) :
    Option (Array EquationLowering.Draft × Json) → Except String (List String) × Translate.Target
  | none => (unitVerdict f budget unit evidence, target)
  | some (slice, anchors) =>
    let group := ((List.range f.fr.units.length).find? (f.fr.unitId · == unit)).map f.fr.group
    let r := Translate.translate slice anchors target (f.anchors (group.getD [])) evidence
    (r.1 >>= unitVerdict f budget unit, r.2)

/-- An accepted line's unit is safe at the evidence its verdict checked:
the line's own, or its translation. -/
theorem lineVerdict_safe {f : FilePlans} {budget : PositiveCertificates.SearchBudget} {target : Translate.Target}
    {unit : String} {evidence : Json} {slice : Option (Array EquationLowering.Draft × Json)} {deps : List String}
    (h : (lineVerdict f budget target unit evidence slice).1 = .ok deps) : ∃ e, UnitSafe f budget unit e := by
  cases slice with
  | none => exact ⟨evidence, unitVerdict_safe h⟩
  | some s =>
    obtain ⟨slice, anchors⟩ := s
    simp only [lineVerdict] at h
    revert h
    generalize (Translate.translate slice anchors target _ evidence).1 = written
    intro h
    cases written with
    | error e => simp [Bind.bind, Except.bind] at h
    | ok e => exact ⟨e, unitVerdict_safe h⟩

/-- What the CLI checks of a unit: a group of a file, by the file's document,
claims and key, the unit's identity, the evidence its line gives and, for a
slice's line, the slice's heads and anchors (`--check-units`); or a module
run, by its wire form, and its evidence (`--check-module`). -/
inductive UnitInput where
  | file (ast claims : Json) (fileKey unit : String) (evidence : Json)
      (slice : Option (Array EquationLowering.Draft × Json))
  | module (run evidence : Json)

/-- The exact CLI condition for a unit's accepted verdict: a group's, the
file's one front (`filePlans`) and its line's verdict there (`lineVerdict`),
at the document's signatures as the check holds them; a module run's, its
decoding (`ModuleRun.decode`) and its document's check (`moduleVerdict`). -/
def UnitInput.Accepted (budget : PositiveCertificates.SearchBudget) : UnitInput → Prop
  | .file ast claims fileKey unit evidence slice =>
    ∃ f target deps, filePlans ast claims fileKey budget = .ok f ∧
      (lineVerdict f budget target unit evidence slice).1 = .ok deps
  | .module run evidence => ∃ m, ModuleRun.decode run = .ok m ∧ moduleVerdict m budget evidence = .ok ()

/-- What an accepted unit gives: a group's `UnitSafe` over its file's front,
at the evidence its verdict checked; a module run's `DocumentSafe` of its
restricted document. -/
def UnitInput.Safe (budget : PositiveCertificates.SearchBudget) : UnitInput → Prop
  | .file ast claims fileKey unit _ _ =>
    ∃ f e, filePlans ast claims fileKey budget = .ok f ∧ UnitSafe f budget unit e
  | .module run evidence => ∃ m, ModuleRun.decode run = .ok m ∧
    DocumentSafe m.ast m.claims m.location evidence budget m.qualified

/-- **The acceptance theorem.** A unit the CLI accepts (`UnitInput.Accepted`)
is safe (`UnitInput.Safe`): a group of a file, its certified requests safe
under `EnvOk` of their inputs (the file's module values at their claimed
signatures and effects, its qualified reads and every imported, ambient and
host value among them), and within their footprints where they claim one; a
module run, its restricted document's plans checked at its evidence. -/
theorem checkUnitJson_safe {budget : PositiveCertificates.SearchBudget} {i : UnitInput}
    (h : i.Accepted budget) : i.Safe budget := by
  cases i with
  | file ast claims fileKey unit evidence slice =>
    obtain ⟨f, _, _, hf, hv⟩ := h
    obtain ⟨e, he⟩ := lineVerdict_safe hv
    exact ⟨f, e, hf, he⟩
  | module run evidence =>
    obtain ⟨m, hm, hv⟩ := h
    refine ⟨m, hm, ?_⟩
    unfold moduleVerdict at hv
    cases hd : checkDocument m.ast m.claims m.location evidence budget m.qualified with
    | error err => simp [hd, Except.mapError] at hv
    | ok u => exact checkDocument_safe hd

end Verification.SourceClaimJson
