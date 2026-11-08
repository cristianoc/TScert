import Verification.Source.Claims.Json

/-! Evidence relocation from a unit slice to its document (STAGE-STORE.md,
"Units of a check"). Joint partition refinement compares complete row keys.
Corresponding request positions choose representatives of exact equation
classes. The document anchors and rows determine canonical union orders.
Heads without a candidate refuse translation.
The document's graph determines union-elimination premises and summary arms.

Relocation is untrusted. Every result crosses the whole-document checker;
no property of this algorithm is assumed by the acceptance theorem. -/
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

/-- One refinement round, comparing complete JSON rows. The document's
class dictionary is shared with the slice; hash collisions compare full keys. -/
def refine (heads : Array Draft) (previous : Array Nat)
    (keys : Std.HashMap Json Nat := {}) : Array Nat × Std.HashMap Json Nat := Id.run do
  let mut keys := keys
  let mut next := #[]
  for i in [0:heads.size] do
    let d := heads[i]!
    let at_ (h : Nat) : Nat := previous[h]?.getD heads.size
    let body := d.body.map fun b =>
      let mapped := b.map (mapTree at_) (canonUnion ∘ List.map (mapTree at_))
      -- A row's clauses form a union. Head allocation can change their
      -- order without changing the equation they describe.
      match mapped with
      | .clauses cs => GraphRow.clauses (cs.mergeSort fun a b => compare (toJson a).compress (toJson b).compress != Ordering.gt)
      | other => other
    let key := toJson (d.kinds, d.binders.map (·.kind), previous[i]!, body)
    let cls := (keys.get? key).getD keys.size
    keys := keys.insert key cls
    next := next.push cls
  return (next, keys)

/-- The document's refinement rounds, shared by its unit translations. -/
structure Target where
  store : EquationStore.State
  rounds : Array (Array Nat)
  keys : Array (Std.HashMap Json Nat) := #[]

def Target.heads (t : Target) : Array Draft := t.store.heads
def Target.of (store : EquationStore.State) : Target := ⟨store, #[store.heads.map fun _ => 0], #[]⟩

/-- Joint refinement to a fixed point; each document round is computed once.
The previous class in each key makes the partition monotonically finer. -/
def jointClasses (slice : Array Draft) (target : Target) : Array Nat × Array Nat × Target := Id.run do
  let mut target := target
  let mut own := slice.map fun _ => 0
  let mut count := 1
  let mut document := target.rounds[0]!
  for k in [0:slice.size + target.heads.size + 1] do
    if target.keys.size <= k then
      let (next, keys) := refine target.heads target.rounds[k]!
      target := { target with rounds := target.rounds.push next, keys := target.keys.push keys }
    document := target.rounds[k+1]!
    let (next, keys) := refine slice own target.keys[k]!
    own := next
    if keys.size == count then break
    count := keys.size
  return (own, document, target)

/-- The correspondence as it grows: each slice head's document head, and the
pairs whose templates are still to pair. -/
structure Pairing where
  map : Std.HashMap Nat Nat := {}
  pending : List (Nat × Nat) := []
  unions : Std.HashMap (List Tree) (List Tree) := {}
  approximate : Bool := false
  needsFallback : Bool := false

/-- The two stores' heads and each head's exact class (`jointClasses`). -/
structure Sides where
  slice : Array Draft
  document : Array Draft
  sliceClass : Nat → Nat
  documentClass : Nat → Nat

abbrev PairM := ReaderT Sides (StateM Pairing)

/-- A tree's shape: each head read as its class. -/
def shape (cls : Nat → Nat) (t : Tree) : Tree := mapTree cls t

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

/-- Pair heads with the same parameter and binder kinds. Exact classes are
paired first; the fallback pairs changed contracts at their anchor positions.
The whole-document checker validates every candidate. -/
def pairHead (h h' : Nat) : PairM Unit := do
  let p ← get
  let sides ← read
  if !p.approximate && sides.sliceClass h != sides.documentClass h' then return
  -- Several document heads can have the same exact equation class. Their
  -- first anchored occurrence chooses the representative; every occurrence
  -- must agree on the class, and the whole-document checker judges its uses.
  if p.map.contains h then return
  let shape (d : Option Draft) := d.map fun d => (d.kinds, d.binders.map (·.kind))
  if shape sides.slice[h]? != shape sides.document[h']? then return
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
that image, then a remaining member with the first remaining exact shape. -/
partial def pairUnion (U V : List Tree) : PairM Unit := do
  if U.length != V.length then return
  let sides ← read
  let p ← get
  let same := canonUnion (U.map (shape sides.sliceClass)) == canonUnion (V.map (shape sides.documentClass))
  if !p.unions.contains U && same then
    set { p with unions := p.unions.insert U V }
  else if !same then
    set { p with needsFallback := true }
  let m := (← get).map
  let mut left : List Tree := []
  let mut right := V
  for u in U do
    match image m u with
    | some v => if right.contains v then right := right.erase v else left := left ++ [u]
    | none => left := left ++ [u]
  for u in left do
    let su := shape sides.sliceClass u
    let approximate := (← get).approximate
    let candidate := (right.find? (shape sides.documentClass · == su)).orElse fun _ =>
      if approximate then right.head? else none
    match candidate with
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
  let key (b : GraphRow Tree (List Tree)) : Json := toJson b
  let found : Std.HashMap Json Nat := sides.document.zipIdx.foldl (fun m (d, j) =>
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

/-- Union images anchored at request and template positions, with the
canonical orders of other document unions. -/
structure UnionImages where
  anchored : Std.HashMap (List Tree) (List Tree)
  orders : Std.HashMap (List Tree) (List Tree)

/-- Preserve concatenation of anchored unions, such as a dictionary read's
value contract followed by its undefined alternative. Each longest anchored
prefix is written in the document's order. -/
partial def UnionImages.parts (unions : UnionImages) (pairs : List (Tree × Tree)) : List Tree := Id.run do
  for n in (List.range (pairs.length + 1)).reverse do
    if n < 2 then continue
    if let some written := unions.anchored.get? ((pairs.take n).map Prod.fst) then
      return written ++ unions.parts (pairs.drop n)
  match pairs with
  | [] => return []
  | (_, moved) :: rest => return moved :: unions.parts rest

/-- Relocate only typed labels, marked by the wire encoder. -/
partial def relocate (unions : UnionImages) (j : Json) : Json :=
  let marked (j : Json) : Option (Json × Json) := do
    let .arr pair ← (j.getObjVal? "§moved").toOption | none
    if pair.size != 2 then none else some (pair[0]!, pair[1]!)
  match marked j with
  | some (_, t) => t
  | none => match j with
    | .arr xs =>
      match xs.toList.mapM marked with
      | some pairs =>
        -- A singleton needs no sorting, coalescing or tree decoding.
        if pairs.length <= 1 then Json.arr (pairs.map (·.2)).toArray else Id.run do
        let some trees := pairs.mapM (fun (a, b) => do
          return (← (Tree.fromJson a).toOption, ← (Tree.fromJson b).toOption))
          | return j
        let merged := (trees.foldl (fun kept p =>
          if kept.any (fun q => q.2 == p.2 && q.1 != p.1) then kept else kept ++ [p]) []).map (·.2)
        let original := trees.map (·.1)
        let written := (unions.anchored.get? original).getD (
          if merged.eraseDups.length != merged.length then merged
          else if canonUnion original != original then
            if merged.length == trees.length then unions.parts trees else merged
          else (unions.orders.get? (canonUnion merged)).getD (canonUnion merged))
        return toJson written
      | none => Json.arr (xs.map (relocate unions))
    | .obj kvs => Json.mkObj (kvs.toList.map fun (k, v) => (k, relocate unions v))
    | _ => j

/-- Arguments inside an application are unions too. Their anchored images
preserve the document's argument spelling; meets are canonical trees. -/
partial def movedImage (m : Std.HashMap Nat Nat) (unions : UnionImages) : Tree → Option Tree
  | .app h args => do return .app (← m.get? h) (← argsImage args)
  | .bound h args j => do return .bound (← m.get? h) (← argsImage args) j
  | .meet ps => do return canonMeet (← ps.toList.mapM (movedImage m unions))
  | t => some t
where
  argsImage : Args → Option Args
    | .nil => some .nil
    | .cons ts rest => do
      let original := ts.toList
      let mapped ← original.mapM (movedImage m unions)
      let U := (unions.anchored.get? original).getD (
        if canonUnion original != original then mapped
        else (unions.orders.get? (canonUnion mapped)).getD (canonUnion mapped))
      return .cons (Types.ofList U) (← argsImage rest)

/-- Decode and relocate one label-bearing field. The final document decoder
checks the complete wire, including the fields passed through unchanged. -/
@[nospecialize] def moveJson {α : Type} [FromJson α] [ToJson α]
    (unions : UnionImages) (j : Json) : Except String Json := do
  let a : α ← fromJson? j
  return relocate unions (toJson a)

/-- Only the label-bearing columns need translation. In particular, contexts,
terms, heap knowledge, links, separations and references retain their JSON values.
Each field follows `EvidenceWire.Document`, `NodeRef`, `StepRef` and `Rule`.
The complete relocated document is decoded by the trusted checker. -/
def moveWire [FromJson Moved] [ToJson Moved]
    (unions : UnionImages) (j : Json) : Except String Json := do
  let array (f : Json → Except String Json) (j : Json) : Except String Json := do
    return .arr (← (← j.getArr?).mapM f)
  let field (k : String) (f : Json → Except String Json) (j : Json) : Except String Json := do
    return j.setObjVal! k (← f (← j.getObjVal? k))
  let choice (j : Json) : Except String Json :=
    if j == toJson ({} : PositiveCertificates.SubtypeChoices Tree) then pure j
    else moveJson (α := PositiveCertificates.SubtypeChoices Moved) unions j
  let edge := array choice
  let node (j : Json) : Except String Json := do
    let j ← field "edges" (array edge) j
    let j ← field "handler" (fun v => if v == .null then pure v else do
      let xs ← v.getArr?
      if xs.size != 2 then throw "expected handler type and edge"
      return .arr #[← moveJson (α := List Moved) unions xs[0]!, ← edge xs[1]!]) j
    let j ← field "implies" (moveJson (α := List (PromiseCalls.Implication Moved)) unions) j
    let j ← field "yields" (moveJson (α := List (PromiseCalls.Yield Moved)) unions) j
    let j ← field "effect" (moveJson (α := Option (EvidenceWire.StepRef Moved)) unions) j
    field "promise" (fun v => if v == .null then pure v else do
      let xs ← v.getArr?
      if xs.size != 2 then throw "expected promise slot and choices"
      return .arr #[xs[0]!, ← choice xs[1]!]) j
  let response (j : Json) : Except String Json := do
    let j ← field "certificate" (array node) j
    let j ← if (j.getObjVal? "codes").isOk then field "codes" (array (array node)) j else pure j
    if (j.getObjVal? "readSummaries").isOk then
      field "readSummaries" (moveJson (α := List (ProgramCertificates.ReadSummary Moved)) unions) j
    else pure j
  let j ← field "types" (moveJson (α := List (List Moved)) unions) j
  let j ← field "proofs" (array (field "rule" (moveJson (α := ProgramCertificates.Rule Moved) unions))) j
  field "functions" (array response) j

/-- Evidence over a slice's store, its heads `slice` and its unit's anchors
`anchors`, written over the document's store `target`, whose unit's anchors
are `documentAnchors`: each label renamed by the correspondence the anchors
give. Missing images refuse. The target caches its refinement rounds. -/
def translate (slice : Array Draft) (anchors : Json) (target : Target) (documentAnchors : Json)
    (evidence : Json) : Except String Json × Target := Id.run do
  -- A slice whose store is the document's, head for head and name for name,
  -- and whose anchors are the document's, is written over it already.
  let row (d : Draft) := toJson (d.name, d.kinds, d.binders.map (fun b => (b.name, b.kind)), d.body)
  if slice.size == target.heads.size && anchors == documentAnchors &&
      (slice.zipIdx.all fun (d, i) => row d == row target.heads[i]!) then
    return (.ok evidence, target)
  let (own, document, target) := jointClasses slice target
  let sides : Sides := {
    slice := slice
    document := target.heads
    sliceClass := fun h => own[h]?.getD (slice.size + target.heads.size)
    documentClass := fun h => document[h]?.getD (slice.size + target.heads.size) }
  let mut byClass : Std.HashMap Nat Nat := {}
  for j in [:target.heads.size] do
    let c := sides.documentClass j
    if !byClass.contains c then byClass := byClass.insert c j
  let pair : PairM Unit := do
    pairJson anchors documentAnchors
    propagate
    grounds
    -- Unmentioned heads can occur in intermediate evidence. Their exact
    -- equation class supplies a candidate, checked with the entire evidence.
    for h in [:slice.size] do
      if !(← get).map.contains h then
        if let some j := byClass.get? (sides.sliceClass h) then pairHead h j
    propagate
    grounds
    -- A changed contract may have no exact image. Anchored candidates remain
    -- untrusted and must discharge the document's unchanged obligations.
    if (← get).needsFallback || (← get).map.size < slice.size then
      modify fun p => { p with approximate := true }
      pairJson anchors documentAnchors
      propagate
  let ((), p) := (pair.run sides).run {}
  let written : Except String Json := do
    let unions : UnionImages := ⟨p.unions, orders target.heads documentAnchors⟩
    let _ : FromJson Moved := ⟨fun j => do
      let t ← Tree.fromJson j
      let some moved := movedImage p.map unions t | throw "evidence names a head without exact correspondence"
      return ⟨moved, t⟩⟩
    -- Mark typed labels before walking the wire: ordinary JSON arrays and
    -- terms cannot be mistaken for label unions. This covers unions inside
    -- rules, instantiations, handlers and summaries as well as type tables.
    let _ : ToJson Moved := ⟨fun m => Json.mkObj [("§moved", toJson (m.original, m.tree))]⟩
    let oldTypes : List (List Moved) ← evidence.getObjValAs? _ "types"
    let oldSets : List ValueSets.ValueSet ← evidence.getObjValAs? _ "valueSets"
    let relocated ← moveWire unions evidence
    -- Only these tables are needed to order elimination premises. The
    -- final whole-document decoder checks every field.
    let types : Array (List Tree) ← relocated.getObjValAs? _ "types"
    let contexts : Array (List Nat) ← relocated.getObjValAs? _ "contexts"
    let proofs : Array (EvidenceWire.ProofEntry Tree) ← relocated.getObjValAs? _ "proofs"
    let movedProofs ← proofs.mapM fun proof => do
      match proof.rule with
      | .unionVar slot =>
        let context ← EvidenceWire.entry "context" contexts proof.claim.context
        let C ← EvidenceWire.entries "type" types context
        let U ← EvidenceWire.entry "slot" C.toArray slot
        let expected := ProgramTyping.members (EquationStore.graph target.store) U
        let premises ← expected.mapM fun member => do
          let candidates ← proof.premises.filterM fun index => do
            let premise ← EvidenceWire.entry "proof" proofs index
            let pc ← EvidenceWire.entry "context" contexts premise.claim.context
            let pc ← EvidenceWire.entries "type" types pc
            let result ← EvidenceWire.entry "type" types proof.claim.type
            let premiseResult ← EvidenceWire.entry "type" types premise.claim.type
            return pc == C.set slot [member] && premise.claim.term == proof.claim.term &&
              premiseResult == result
          let some index := candidates.head? | throw "no relocated union elimination premise"
          return index
        return { proof with premises }
      | _ => pure proof
    let sourceGraph := EquationStore.graph { doc := #[], heads := slice }
    let targetGraph := EquationStore.graph target.store
    let functions ← relocated.getObjValAs? (Array Json) "functions"
    let originals ← evidence.getObjValAs? (Array Json) "functions"
    let functions ← (functions.zip originals).mapM fun (f, original) => do
      if !(f.getObjVal? "readSummaries").isOk then return f
      let old : List (ProgramCertificates.ReadSummary Tree) ← original.getObjValAs? _ "readSummaries"
      let moved : List (ProgramCertificates.ReadSummary Tree) ← f.getObjValAs? _ "readSummaries"
      let summaries ← (moved.zip old).mapM fun (s, old) => do
        let oldMembers := ProgramTyping.members sourceGraph old.receiver
        let movedMembers ← oldMembers.mapM fun t => match movedImage p.map unions t with
          | some t => pure t
          | none => throw "read summary member has no image"
        let expected := ProgramTyping.members targetGraph s.receiver
        let arms ← expected.mapM fun t => do
          let some i := movedMembers.idxOf? t | throw "read summary member has no arm"
          let some arm := s.arms[i]? | throw "read summary member has no arm"
          return arm
        if oldMembers.length != s.arms.length then throw "read summary has an extra arm"
        return { s with arms }
      return f.setObjVal! "readSummaries" (toJson summaries)
    -- Value sets carry literal order inherited from a type's expansion.
    -- Relocate that order through the same type correspondence.
    let mut sets : Std.HashMap ValueSets.ValueSet ValueSets.ValueSet := {}
    for (old, moved) in oldTypes.zip types.toList do
      if let (some a, some b) :=
          (HeapExpressionRules.typeValues sourceGraph [old.map (·.original)] 0,
           HeapExpressionRules.typeValues targetGraph [moved] 0) then
        sets := sets.insert a b
    let valueSets := oldSets.map fun v => (sets.get? v).getD v
    return ((relocated.setObjVal! "proofs" (toJson movedProofs)).setObjVal! "functions"
      (toJson functions)).setObjVal! "valueSets" (toJson valueSets)
  return (written, target)

end Verification.SourceClaimJson.Translate

namespace Verification.SourceClaimJson
open Lean EquationGraphs

/-- A slice's plans, for its search: its front at the qualified reads its
unit's reads document gives (`--produce-unit`), its imported modules left
out. Its claims are the producer's for the slice; claims that are the
producer's refusal refuse. -/
def slicePlans (ast claims qualified : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget) :
    Except String FilePlans := do
  if let .ok reason := claims.getObjValAs? String "refusal" then throw reason
  let qualified ← (← qualified.getArr?).toList.mapM fun q => do
    fieldsExactly q ["name", "footprint", "onThrow", "resultFootprint"]
    let footprint : Footprints.Closed ← fromJson? (← jField q "footprint")
    let onThrow : Bool ← fromJson? (← jField q "onThrow")
    let result : Footprints.Closed ← fromJson? (← jField q "resultFootprint")
    return (← jStr (← jField q "name"), footprint, onThrow, result)
  let ast := ast.setObjVal! "modules" (Json.arr #[])
  let claims := claims.setObjVal! "modules" (Json.arr #[])
  let fr ← fileFront ast claims fileKey budget qualified
  let (T, plans) := fr.extractAll
  let F ← EquationStore.freeze T
  return ⟨⟨ast, claims, qualified, []⟩, fr, F, plans.map fun e => e.bind (FunctionPlan.over F)⟩

/-- A union at its request position. Positions name graph nodes and slots,
independently of head numbering, so the slice's and the document's anchors
pair position by position. -/
structure AnchorState where
  fields : List (String × Json) := []

private def anchorUnion (key : Unit → String) (U : List Tree) : StateM AnchorState Unit := do
  if U.isEmpty then return
  let value := toJson (U.map fun t => Json.mkObj [("§label", t.toJson)])
  modify fun s => { fields := (key (), value) :: s.fields }

/-- A group's anchors: each type union of its requests at its position, and
its hints. -/
def FilePlans.anchors (f : FilePlans) (group : List Nat) : Json :=
  let _ : ToJson (EquationStore.CheckedLabel f.F.equations f.F.primitive) :=
    ⟨fun l => Json.mkObj [("§label", l.tree.toJson)]⟩
  Json.arr (group.map fun i => match f.plans[i]? with
    | some (.ok (.graph _ _ r)) => Id.run do
      let note (key : Unit → String) (U : List (EquationStore.CheckedLabel f.F.equations f.F.primitive)) :=
        anchorUnion key (U.map (·.tree))
      let context (key : String) (C : List (List (EquationStore.CheckedLabel f.F.equations f.F.primitive))) :
          StateM AnchorState Unit := do
        for (U, j) in C.zipIdx do note (fun _ => s!"{key}/{j}") U
      let points (key : String) (cs : List (CertificateProducer.PointClaim
          (EquationStore.CheckedLabel f.F.equations f.F.primitive))) : StateM AnchorState Unit := do
        for (c, j) in cs.zipIdx do
          context s!"{key}/{j}/context" c.context
          note (fun _ => s!"{key}/{j}/type") c.type
      let action : StateM AnchorState Unit := do
        context "inputs" r.inputs
        note (fun _ => "result") r.result
        if let some (_, _, U) := r.promise then note (fun _ => "promise") U
        points "claims" r.claims
        for (q, j) in r.codes.zipIdx do
          context s!"codes/{j}/captures" q.entry.captures
          note (fun _ => s!"codes/{j}/receiver") q.entry.row.receiver
          context s!"codes/{j}/arguments" q.entry.row.arguments
          note (fun _ => s!"codes/{j}/result") q.entry.row.result
          if let some U := q.entry.store then note (fun _ => s!"codes/{j}/store") U
          points s!"codes/{j}/claims" q.claims
        for (o, j) in r.obligations.zipIdx do
          context s!"obligations/{j}/context" o.sequent.context
          note (fun _ => s!"obligations/{j}/type") o.sequent.type
      let (_, state) := action.run {}
      return Json.mkObj [("unions", Json.mkObj state.fields), ("hints", toJson r.hints)]
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
and checked at the evidence so written, returning the refinement cache. -/
def lineVerdict (f : FilePlans) (budget : PositiveCertificates.SearchBudget) (target : Translate.Target)
    (unit : String) (evidence : Json) :
    Option (Array EquationLowering.Draft × Json) → Except String (List String) × Translate.Target
  | none => (unitVerdict f budget unit evidence, target)
  | some (slice, anchors) =>
    let group := ((List.range f.fr.units.length).find? (f.fr.unitId · == unit)).map f.fr.group
    let r := Translate.translate slice anchors target (f.anchors (group.getD [])) evidence
    (r.1 >>= unitVerdict f budget unit, r.2)

/-- The operation used for a decoded CLI unit line, including relocation
with the shared translation target. -/
def checkedUnit (f : FilePlans) (budget : PositiveCertificates.SearchBudget)
    (target : Translate.Target) (unit : String) (evidence : Json)
    (slice : Option (Array EquationLowering.Draft × Json)) :
    Except String (List String) × Translate.Target :=
  lineVerdict f budget target unit evidence slice

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

/-- A module's slice lines assembled over the restricted module's store.
Every member has one response and one obligation list; the complete bundle
is subsequently judged by `moduleVerdict`. -/
def moduleLines (m : ModuleRun) (budget : PositiveCertificates.SearchBudget) (lines : Json) : Except String Json := do
  let qualified := toJson (m.qualified.map fun (name, footprint, onThrow, result) =>
    Json.mkObj [("name", toJson name), ("footprint", toJson footprint), ("onThrow", toJson onThrow),
      ("resultFootprint", toJson result)])
  let f ← slicePlans m.ast m.claims qualified m.location budget
  let lines ← (← lines.getArr?).toList.mapM readLine
  let mut target := Translate.Target.of f.F.store.heads
  let mut responses : Std.HashMap Nat (RequestJson.Response Tree × List (ProgramCertificates.Evidence Tree)) := {}
  for i in f.fr.selected none do
    let group := f.fr.group i
    let unit := f.fr.unitId i
    let matching := lines.filter (·.1 == unit)
    let [(_, evidence, slice)] := matching | throw s!"expected one evidence line for module unit {unit}"
    let written ← match slice with
      | none => pure evidence
      | some (heads, anchors) => do
        let (written, next) := Translate.translate heads anchors target (f.anchors group) evidence
        target := next
        written
    let bundle : SourceExtraction.Bundle Tree ← EvidenceWire.decode written
    if bundle.functions.length != group.length || bundle.obligations.length != group.length then
      throw "evidence for another set of module units"
    for (j, response) in group.zip (bundle.functions.zip bundle.obligations) do
      if responses.contains j then throw "duplicate module unit"
      responses := responses.insert j response
  let ordered ← (List.range f.plans.length).mapM fun i => do
    let some response := responses.get? i | throw s!"no evidence for module member {i}"
    pure response
  return EvidenceWire.encode ⟨ordered.map (·.1), ordered.map (·.2)⟩

/-- The module CLI's acceptance operation, translation and whole-document
checking included. -/
def moduleLineVerdict (m : ModuleRun) (budget : PositiveCertificates.SearchBudget) (lines : Json) : Except String Unit :=
  ((moduleLines m budget lines).mapError (s!"module {m.location}: " ++ ·)) >>= moduleVerdict m budget

/-- What the CLI checks of a unit: a group of a file, by the file's document,
claims and key, the unit's identity, the evidence its line gives and, for a
slice's line, the slice's heads and anchors and the current translation target (`--check-units`); or a module
run, by its wire form, and its evidence (`--check-module`). -/
inductive UnitInput where
  | file (ast claims : Json) (fileKey unit : String) (evidence : Json)
      (slice : Option (Array EquationLowering.Draft × Json)) (target : Translate.Target)
  | module (run evidence : Json)

/-- The exact CLI condition for a unit's accepted verdict: a group's, the
file's one front (`filePlans`) and its line's verdict there (`lineVerdict`),
through `checkedUnit`; a module run's decoding (`ModuleRun.decode`) and
relocation followed by its document's check (`moduleLineVerdict`). -/
def UnitInput.Accepted (budget : PositiveCertificates.SearchBudget) : UnitInput → Prop
  | .file ast claims fileKey unit evidence slice target =>
    ∃ f deps, filePlans ast claims fileKey budget = .ok f ∧
      (checkedUnit f budget target unit evidence slice).1 = .ok deps
  | .module run evidence => ∃ m, ModuleRun.decode run = .ok m ∧ moduleLineVerdict m budget evidence = .ok ()

/-- What an accepted unit gives: a group's `UnitSafe` over its file's front,
at the evidence its verdict checked; a module run's `DocumentSafe` of its
restricted document. -/
def UnitInput.Safe (budget : PositiveCertificates.SearchBudget) : UnitInput → Prop
  | .file ast claims fileKey unit _ _ _ =>
    ∃ f e, filePlans ast claims fileKey budget = .ok f ∧ UnitSafe f budget unit e
  | .module run _ => ∃ m e, ModuleRun.decode run = .ok m ∧
    DocumentSafe m.ast m.claims m.location e budget m.qualified

/-- **The acceptance theorem.** A unit the CLI accepts (`UnitInput.Accepted`)
is safe (`UnitInput.Safe`): a group of a file, its certified requests safe
under `EnvOk` of their inputs (the file's module values at their claimed
signatures and effects, its qualified reads and every imported, ambient and
host value among them), and within their footprints where they claim one; a
module run, its restricted document's plans checked at its evidence. -/
theorem checkUnitJson_safe {budget : PositiveCertificates.SearchBudget} {i : UnitInput}
    (h : i.Accepted budget) : i.Safe budget := by
  cases i with
  | file ast claims fileKey unit evidence slice target =>
    obtain ⟨f, _, hf, hv⟩ := h
    obtain ⟨e, he⟩ := lineVerdict_safe hv
    exact ⟨f, e, hf, he⟩
  | module run evidence =>
    obtain ⟨m, hm, hv⟩ := h
    unfold moduleLineVerdict at hv
    cases he : (moduleLines m budget evidence).mapError (s!"module {m.location}: " ++ ·) with
    | error err => simp [he, Bind.bind, Except.bind] at hv
    | ok e =>
      simp only [he, Bind.bind, Except.bind] at hv
      refine ⟨m, e, hm, ?_⟩
      unfold moduleVerdict at hv
      cases hd : checkDocument m.ast m.claims m.location e budget m.qualified with
      | error err => simp [hd, Except.mapError] at hv
      | ok u => exact checkDocument_safe hd

end Verification.SourceClaimJson
