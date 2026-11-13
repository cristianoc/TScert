import Verification.Source.Claims.Json

/-! The regional tables a unit's loop heads are given (`SinglePass.Regional`'s
`heads`, `regionalFromJson`), inferred from its graph and claims where no
given file states them: the slots holding entry argument paths
(`SourceExtraction.regionTable`), the fresh values and cells
(`claimedFreshIterate`) and the fresh fields (`freshFieldsIterate`), each the
greatest fixed point the existing search computes from its certificate
(`regionalGiven`), here over the evidence each node's claim gives
(`claimedCertificate`). The field
names are those the unit's callees' store regions read through one field.
Each table reaches the pass as a proposal: the regional check
(`ArgumentRegionGraph.checkNode`) checks a loop head's entries on every edge
into it. -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- Each node's evidence as its claim states it: a call of a slot its
derivation read off the callee's signatures (`SinglePass.directCall`, each
precondition taken as admitted), any other node its sequent. -/
def claimedCertificate (r : SourceExtraction.SourceRequest σ ι) : ControlFlow.Certificate ι :=
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  (r.program.zip r.claims).map fun (n, c) =>
    let direct := match n.expression with
      | .invoke .. => (SinglePass.directCall G images c.context n.expression c.type (fun _ _ => true) none {}).1
      | _ => none
    match direct with
    | some (e, _) => ({ ordinary := some (.proof e), edges := [] } : ControlFlow.NodeEvidence ι)
    | none => ({ sequent := some ⟨c.context, n.expression, c.type⟩, edges := [] } : ControlFlow.NodeEvidence ι)

/-- One pass over candidate fresh values and cells, as the existing
search's (`SourceExtraction.freshTablesPass`), but a call whose derivation
the claims do not give (no `SinglePass.directCall` one) is taken to keep
its cells: the pass's own evidence decides it there, and a cell it does not
keep is an entry the edge into the head does not establish. -/
@[nospecialize] def claimedFreshPass (G : PositiveGraphs.NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (Φ : Footprints.Closed)
    (nodes : List ((ControlFlow.Node × ControlFlow.NodeEvidence ι) × Nat))
    (tables : Array (List Nat) × Array (List Nat)) : Array (List Nat) × Array (List Nat) :=
  nodes.foldr (fun ((node, c), l) (values, cells) =>
    let F := values.getD l []
    let C := cells.getD l []
    let open_ := match node.expression with
      | .invoke .. => true
      | _ => false
    let C := if open_ || GraphCode.ArgumentRegionGraph.cellsKept G images [] Φ F C c node.expression node.handler.isSome
      then C else []
    let cells := cells.set! l C
    let outF := GraphCode.ArgumentRegionGraph.freshOut G images [] F C c node.expression
    let outC := GraphCode.ArgumentRegionGraph.cellOut F C node.expression
    -- (a target's slot map read by position in constant time: `PointClaims.slot`)
    let slotOf := fun (m : Option (Array Nat)) (i : Nat) => match m with
      | none => i
      | some a => a.getD i 0
    -- (`GraphCode.freshSlot` over a set read in constant time: it reads of
    -- the set the one slot `q`)
    let mask := fun (S : List Nat) => S.foldl (fun (a : Array Bool) i => a.set! i true)
      (Array.replicate (S.foldl max 0 + 1) false)
    let freshAt := fun (S : Array Bool) (pushed out : Bool) (j : Nat) =>
      let q := if pushed then j - 1 else j
      GraphCode.freshSlot (if S.getD q false then [q] else []) pushed out j
    let edge := fun (D : List Nat) (S : List Nat) (out : Bool) (t : ControlFlow.Target) =>
      let m := t.mapping.map List.toArray
      let S := mask S
      D.filter fun i => freshAt S (GraphCode.pushes node.continuation) out (slotOf m i)
    let (values, cells) := (CertificateProducer.successors node.continuation).foldl (fun (values, cells) t =>
      (values.modify t.label fun D => edge D F outF t, cells.modify t.label fun D => edge D C outC t)) (values, cells)
    match node.handler with
    | some t =>
      let m := t.mapping.map List.toArray
      let handle := fun (D : List Nat) (S : List Nat) =>
        let S := mask S
        D.filter fun i => freshAt S true false (slotOf m i)
      (values.modify t.label fun D => handle D F, cells.modify t.label fun D => handle D C)
    | none => (values, cells)) tables

@[nospecialize] def claimedFreshIterate (G : PositiveGraphs.NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (Φ : Footprints.Closed)
    (nodes : List ((ControlFlow.Node × ControlFlow.NodeEvidence ι) × Nat)) :
    Nat → Array (List Nat) × Array (List Nat) → Option (Array (List Nat) × Array (List Nat))
  | 0, _ => none
  | fuel + 1, tables =>
    let next := claimedFreshPass G images Φ nodes tables
    if next = tables then some tables else claimedFreshIterate G images Φ nodes fuel next

/-- The field names the store regions of a unit's callees read through one
field: the effects each call node's context types state (`regionNames` over
a certificate's selected effects). -/
def calleeRegionNames (r : SourceExtraction.SourceRequest σ ι) : List String :=
  let G := RequestJson.graph r.toRequest
  let tys := ((r.program.zip r.claims).flatMap fun (n, c) => match n.expression with
    | .invoke .. => c.context
    | _ => []).eraseDups
  (tys.flatMap fun F => match PositiveRules.expand G F with
    | [PositiveNormalization.Clause.arrs L _] | [PositiveNormalization.Clause.callable _ _ L _ _] =>
      L.flatMap fun p => p.effect.regions.filterMap fun x => match x.path with
        | [f] => some f
        | _ => none
    | _ => []).eraseDups

/-- A regional check's tables at the unit's statement entries, inferred
(`regionalGiven`'s shape): `force` adds at each one an entry no edge
establishes (a fresh value, a fresh cell, an argument path or a fresh field,
by its kind), the adversarial proposal the pass's edge check refuses. -/
def regionalInferred (r : SourceExtraction.SourceRequest σ ι) (Φ : Footprints.Closed)
    (regions : List Footprints.ArgumentStoreRegion) (force : Option String := none) : Json :=
  let P := GraphCode.program (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
  let C := claimedCertificate r
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  let table := SourceExtraction.regionTable P C r.start regions
  let nodes := (P.zip C).zipIdx
  let init := (nodes.map fun ((_, c), l) =>
    if l = r.start then [] else List.range (ControlFlow.entry c).length).toArray
  let (values, cells) := (claimedFreshIterate G images Φ nodes (2 * P.length + 2) (init, init)).getD
    (#[], #[])
  let names := calleeRegionNames r
  let fields := if names.isEmpty || values.isEmpty then #[] else
    let start' := (nodes.map fun ((_, c), l) => if l = r.start then [] else
      (List.range (ControlFlow.entry c).length).flatMap fun j => names.map fun f => (j, f)).toArray
    (SourceExtraction.freshFieldsIterate G names values nodes (2 * P.length + 2) start').getD #[]
  let width := fun (l : Nat) => ((r.claims[l]?).map (·.context.length)).getD 0
  -- (forced: one slot past those the table states at the entry, each kind)
  let extra := fun (k : String) (xs : List Nat) (l : Nat) =>
    if force == some k then ((List.range (width l)).filter (!xs.contains ·)).take 1 else []
  Json.mkObj [("names", Lean.toJson names), ("heads", Json.arr (r.cuts.map fun l =>
    let facts := (GraphCode.ArgumentPathTracking.atLabel table l).map fun f => (f.slot, f.region.position, f.region.path)
    let factsF := if force == some "head-region-facts" then
        facts ++ (((List.range (width l)).filter (fun j => !facts.any (·.1 == j))).take 1).map fun j => (j, 0, ["forced"])
      else facts
    let vs := values.getD l []
    let cs := cells.getD l []
    let fs := fields.getD l []
    let fsF := match force, names with
      | some "head-region-fields", f :: _ => fs ++ (((List.range (width l)).filter (fun j => !fs.contains (j, f))).take 1).map (·, f)
      | _, _ => fs
    Json.mkObj [
    ("label", Lean.toJson l),
    ("facts", Lean.toJson factsF),
    ("values", Lean.toJson (vs ++ extra "head-region-values" vs l)),
    ("cells", Lean.toJson (cs ++ extra "head-region-cells" cs l)),
    ("fields", Lean.toJson fsF)]).toArray)]

/-- A unit's inferred regional lines: its store regions' (`regional`) and its
footprint's regional fallback's (`footprintRegional`), as `givenLines`
writes them. -/
def regionalLines (r : SourceExtraction.SourceRequest σ ι) (force : Option String := none) : List (String × Json) :=
  (match r.regional with
    | some (Φ, regions) => [("regional", regionalInferred r Φ regions force)]
    | none => []) ++
  (if !r.fresh && r.footprint != Footprints.Closed.top then [("footprintRegional", regionalInferred r r.footprint [] force)] else [])

/-- The slot whose array store a node writes an element of
(`a[k] = v`: a write of the store field through a slot). -/
def elementWritten : Tm → Option Nat
  | .writeAt (.str "[]") (.var w) _ => some w
  | _ => none

/-- The nodes of the loop at head `h`, by label: those the head reaches that reach it. -/
def loopBody (P : ControlFlow.Program) (h : Nat) : Array Bool := Id.run do
  let n := P.length
  let A := P.toArray
  let succ := fun (l : Nat) => ((A[l]?).map fun node =>
    (GraphCode.edgesOf node.continuation node.handler).map (·.1.label)).getD []
  let mut pred : Array (List Nat) := Array.replicate n []
  for l in List.range n do
    for t in succ l do
      if t < n then pred := pred.modify t (l :: ·)
  let reach := fun (next : Nat → List Nat) => Id.run do
    let mut seen : Array Bool := Array.replicate n false
    let mut work := [h]
    if h < n then seen := seen.set! h true
    for _ in List.range (n + 1) do
      match work with
      | [] => break
      | l :: rest =>
        work := rest
        for t in next l do
          if t < n && !seen[t]! then
            seen := seen.set! t true
            work := t :: work
    return seen
  let fwd := reach succ
  let bwd := reach fun l => pred.getD l []
  return (List.range n).toArray.map fun l => fwd[l]! && bwd[l]!

/-- Triples `(a, b, o)` carried forward from the start along every edge to
the slots whose mappings read `a` and `b` (a pushed result one slot deeper),
kept where every predecessor carries them: `made l` those node `l`'s pushed
result adds, `same` whether `a = b` is kept. -/
def carryForward (P : ControlFlow.Program) (start : Nat) (width : Nat → Nat)
    (made : Nat → List (Nat × Nat × Nat)) (same : Bool) : Array (Option (List (Nat × Nat × Nat))) := Id.run do
  let n := P.length
  let A := P.toArray
  let mut table : Array (Option (List (Nat × Nat × Nat))) := Array.replicate n none
  if start < n then table := table.set! start (some [])
  -- (a worklist: a label again only where what enters it changed; each
  -- label's triples only shrink once set)
  let mut work : Std.HashSet Nat := if start < n then ({} : Std.HashSet Nat).insert start else {}
  let mut queue : List Nat := if start < n then [start] else []
  for _ in [0:n * n + n + 1] do
    match queue with
    | [] => break
    | l :: rest =>
      queue := rest
      work := work.erase l
      let some node := A[l]? | continue
      let some here := table.getD l none | continue
      let mine := if GraphCode.pushes node.continuation then made l else []
      let edges := (GraphCode.edgesOf node.continuation none).map (·, false) ++ node.handler.toList.map fun t => ((t, true), true)
      for ((t, shifted), isHandler) in edges do
        let post := if shifted then here.map (fun (a, b, o) => (a + 1, b + 1, o)) ++ (if isHandler then [] else mine) else here
        -- Each source slot's readers at the target, by its mapping.
        let readers : Std.HashMap Nat (List Nat) := (List.range (width t.label)).foldl (fun m i =>
          let s := PointClaims.slot t.mapping i
          m.insert s (i :: (m.getD s []))) {}
        let carried := post.flatMap fun (a, b, o) => (readers.getD a []).flatMap fun i =>
          (readers.getD b []).filterMap fun j => if (i == j) == same then some (i, j, o) else none
        let merged := match table.getD t.label none with
          | none => (carried.foldl (fun (acc : List (Nat × Nat × Nat) × Std.HashSet (Nat × Nat × Nat)) x =>
              if acc.2.contains x then acc else (x :: acc.1, acc.2.insert x)) ([], {})).1.reverse
          | some cur =>
            let set : Std.HashSet (Nat × Nat × Nat) := carried.foldl (·.insert ·) {}
            cur.filter set.contains
        if table.getD t.label none != some merged then
          table := table.set! t.label (some merged)
          if !work.contains t.label then
            work := work.insert t.label
            queue := t.label :: queue
  return table

/-- **The region separations at a unit's loop heads**: the pairs of slots
whose regions an allocation states apart (`IndexWrites.regionAtoms`, a
literal's store apart from every array slot), each with its allocation,
carried along every edge to the slots whose mappings read them, those every
predecessor carries; at each loop head, the pairs of array slots
(`IndexWrites.arraySlot`) of an allocation whose array the loop writes an
element of outside every loop it holds (`elementWritten`: the write keeps a quantified fact over an
array apart from it, `IndexWrites.writeAtoms`), as `IndexFact.apart`. With
`force` (`TSCERT_FORCE=head-apart`), each such side also stated apart from
itself, the adversarial pair the pass's edge check refuses. -/
def freshApartAt (r : SourceExtraction.SourceRequest σ ι) (force : Bool := false) :
    List (Nat × List HeapKnowledge.IndexAtom) := Id.run do
  let G := RequestJson.graph r.toRequest
  let P := r.program
  let ctxOf := fun (l : Nat) => ((r.claims[l]?).map (·.context)).getD []
  let width := fun (l : Nat) => (ctxOf l).length
  let heads := (SinglePass.loopHeads P.toArray r.start).1
  -- (no element write in a loop: no pair to propose)
  if !P.any fun node => (elementWritten node.expression).isSome then return []
  let bodies := (r.cuts.filter (heads.getD · false)).map fun h => (h, loopBody P h)
  -- The element writes each loop holds outside every loop inside it.
  let A := P.toArray
  let writeNodes : List (Nat × Nat) := (List.range A.size).filterMap fun l => ((A[l]?).bind (elementWritten ·.expression)).map (l, ·)
  let writes := bodies.map fun (h, body) =>
    let inner := fun (l : Nat) => bodies.any fun (h', b) => h' != h && body.getD h' false && b.getD l false
    (h, writeNodes.filter fun (p : Nat × Nat) => body.getD p.1 false && !inner p.1)
  if writes.all (·.2.isEmpty) then return []
  let allocates := fun (l : Nat) => ((A[l]?).map fun node =>
    (IndexWrites.regionAtoms G (ctxOf l) {} node.expression).filterMap fun a => match a.fact with
      | .apart x y => some (x, y, l)
      | _ => none).getD []
  -- The slot each allocation's result is carried to, then the allocations
  -- a loop writes an element of: only their pairs are carried.
  let held := carryForward P r.start width (fun l => if (allocates l).isEmpty then [] else [(0, 0, l)]) true
  let writtenAt := fun (h : Nat) => ((writes.find? (·.1 == h)).map (·.2)).getD [] |>.flatMap fun (l, w) =>
    ((held.getD l none).getD []).filterMap fun (a, _, o) => if a == w then some o else none
  let written := (writes.map (·.1)).flatMap writtenAt
  if written.isEmpty then return []
  let table := carryForward P r.start width (fun l => if written.contains l then allocates l else []) false
  return r.cuts.filterMap fun h => do
    guard (heads.getD h false)
    let ps ← table.getD h none
    let written := writtenAt h
    let Γ := ctxOf h
    let ps := (ps.filter fun (a, b, o) => written.contains o && IndexWrites.arraySlot G Γ a && IndexWrites.arraySlot G Γ b).map
      fun (a, b, _) => (a, b)
    let ps := ps.eraseDups
    let ps := ps ++ (if force then (ps.map (·.1)).eraseDups.map fun a => (a, a) else [])
    if ps.isEmpty then none else
    some (h, ps.map fun (a, b) => ({ fact := .apart a b } : HeapKnowledge.IndexAtom))

end

/-- The plans with the loop heads of each unit of `group` proposed the region
separations its allocations state (`freshApartAt`), beside its other
candidates. -/
def FilePlans.withFreshApart (f : FilePlans) (force : Bool := false) (group : List Nat) : FilePlans :=
  { f with plans := f.plans.zipIdx.map fun (p, i) => if !group.contains i then p else p.map fun
    | .graph name pos r =>
      let extra := freshApartAt r force
      if extra.isEmpty then .graph name pos r else
      let cands := extra.foldl (fun (cs : List (Nat × List HeapKnowledge.IndexAtom)) (l, as) =>
        if cs.any (·.1 == l) then cs.map fun (l', bs) => if l' == l then (l', bs ++ as.filter (!bs.contains ·)) else (l', bs)
        else cs ++ [(l, as)]) r.candidates
      .graph name pos { r with candidates := cands } }

end Verification.SourceClaimJson
