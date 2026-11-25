import Verification.Source.Claims.Json

/-! The regional tables a unit's loop heads are given (`SinglePass.Regional`'s
`heads`, `regionalFromJson`), inferred from its graph and claims where no
given file states them: the slots holding entry argument paths
(`SourceElaboration.regionTable`), the fresh values and cells
and the fresh fields, each propagated by `graphWorklist` to the
fixed point of the existing transfers over its certificate
(`regionalGiven`), here over the evidence each node's claim gives
(`claimedCertificate`). The field
names are those the unit's callees' spine regions read through one field.
Each table reaches the pass as a proposal: the regional check
(`ArgumentRegionGraph.checkNode`) checks a loop head's entries on every edge
into it. -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- Each node's evidence as its claim states it: a call of a slot its
derivation read off the callee's signatures (`SinglePass.directCall`, each
precondition taken as admitted), any other node its sequent. -/
def claimedCertificate (r : SourceElaboration.SourceRequest σ ι) : ControlFlow.Certificate ι :=
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
search's (`SourceElaboration.freshTablesPass`), but a call whose derivation
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
    let FS := GraphCode.slotSet F
    let CS := GraphCode.slotSet C
    let edge := fun (D : List Nat) (S : Std.HashSet Nat) (out : Bool) (t : ControlFlow.Target) =>
      GraphCode.freshKept D S (GraphCode.pushes node.continuation) out t.mapping
    let (values, cells) := (CertificateProducer.successors node.continuation).foldl (fun (values, cells) t =>
      (values.modify t.label fun D => edge D FS outF t, cells.modify t.label fun D => edge D CS outC t)) (values, cells)
    match node.handler with
    | some t =>
      (values.modify t.label fun D => GraphCode.freshKept D FS true false t.mapping,
        cells.modify t.label fun D => GraphCode.freshKept D CS true false t.mapping)
    | none => (values, cells)) tables

/-- A worklist for the graph's monotone proposal transfers. A
node is revisited when its input table changes. The snapshots contain only
its affected entries, so each transfer can update its arrays in place.
The inferred data remains a proposal checked by the pass. -/
@[nospecialize] def graphWorklist {S A β : Type} [BEq A]
    (nodes : List ((ControlFlow.Node × β) × Nat))
    (step : ((ControlFlow.Node × β) × Nat) → S → S)
    (read : S → Nat → A) (limit : Nat) (initial : S) : Option S := Id.run do
  let ns := nodes.toArray
  let affected := ns.map fun ((node, _), l) =>
    (l :: (CertificateProducer.successors node.continuation).map (·.label) ++
      (node.handler.toList.map (·.label))).eraseDups.filter (· < ns.size)
  let mut pending := (List.range ns.size).reverse
  let mut queued := Array.replicate ns.size true
  let mut state := initial
  let mut remaining := limit * ns.size + 1
  while !pending.isEmpty do
    if remaining == 0 then return none
    remaining := remaining - 1
    let some l := pending.head? | return none
    pending := pending.tail
    queued := queued.set! l false
    let some node := ns[l]? | return none
    let snapshots := (affected.getD l []).map fun t => (t, read state t)
    state := step node state
    for (t, previous) in snapshots do
      if read state t != previous && !queued.getD t false then
        queued := queued.set! t true
        pending := t :: pending
  return some state

/-- The field names the spine regions of a unit's callees read through one
field: the effects each call node's context types state, read from their
normal frames (`regionNames` over a certificate's selected effects). -/
def calleeRegionNames (r : SourceElaboration.SourceRequest σ ι) : List String :=
  let G := RequestJson.graph r.toRequest
  let tys := ((r.program.zip r.claims).flatMap fun (n, c) => match n.expression with
    | .invoke .. => c.context
    | _ => []).eraseDups
  (tys.flatMap fun F => match PositiveRules.expand G F with
    | [PositiveNormalization.Clause.arrs L _] | [PositiveNormalization.Clause.callable _ _ L _ _] =>
      L.flatMap fun p => p.effect.schema.normal.frame.regionFields
    | _ => []).eraseDups

/-- A regional check's tables at the unit's statement entries, inferred
(`regionalGiven`'s shape): `force` adds at each one an entry no edge
establishes (a fresh value, a fresh cell, an argument path or a fresh field,
by its kind), the adversarial proposal the pass's edge check refuses. -/
def regionalInferred (r : SourceElaboration.SourceRequest σ ι) (Φ : Footprints.Closed)
    (regions : List Footprints.ArgumentSpineRegion) (force : Option String := none) : Json :=
  let P := GraphCode.program (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
  let C := claimedCertificate r
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  let table := SourceElaboration.regionTable P C r.start regions
  let nodes := (P.zip C).zipIdx
  let init := (nodes.map fun ((_, c), l) =>
    if l = r.start then [] else List.range (ControlFlow.entry c).length).toArray
  let (values, cells) := (graphWorklist nodes
    (fun node tables => claimedFreshPass G images Φ [node] tables)
    (fun tables l => (tables.1.getD l [], tables.2.getD l []))
    (2 * P.length + 2) (init, init)).getD (#[], #[])
  let names := calleeRegionNames r
  let fields := if names.isEmpty || values.isEmpty then #[] else
    let start' := (nodes.map fun ((_, c), l) => if l = r.start then [] else
      (List.range (ControlFlow.entry c).length).flatMap fun j => names.map fun f => (j, f)).toArray
    (graphWorklist nodes
      (fun node fields => SourceElaboration.freshFieldsPass G names values [node] fields)
      (fun fields l => fields.getD l []) (2 * P.length + 2) start').getD #[]
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

/-- A unit's inferred regional lines: its spine regions' (`regional`) and its
footprint's regional fallback's (`footprintRegional`), as `givenLines`
writes them. -/
def regionalLines (r : SourceElaboration.SourceRequest σ ι) (force : Option String := none) : List (String × Json) :=
  (match r.regional with
    | some (Φ, regions) => [("regional", regionalInferred r Φ regions force)]
    | none => []) ++
  (if !r.fresh && r.footprint != Footprints.Closed.top then [("footprintRegional", regionalInferred r r.footprint [] force)] else [])

/-- The slot whose array spine a node writes an element of
(`a[k] = v`: a write of the spine field through a slot). -/
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

/-- All call effects of a callee type `A` matching argument count `arity`,
covering both fixed (`arrows`) and variadic (`variadic`) signatures. This is a
proposal-side approximation of overload selection: proposals are computed
before the pass, from the callee's type alone, while the pass reads the
signature elaboration selected from the call's evidence
(`ExpressionEffects.selectedEffect`); elaboration selects inline per call
form (`Synthesis`) and states no selection function this could share. A
proposal is a candidate, kept at a point only where every edge into it
establishes it, so one made from a signature the call does not select
changes no verdict. -/
@[nospecialize] private def matchingCallEffects {ι : Type} (G : PositiveGraphs.NormalGraph ι)
    (A : Ty ι) (arity : Nat) : Option (List CallEffects.Effect) :=
  let cs := PositiveRules.expand G A
  if cs.isEmpty then none else
  let perClause : Option (List (List CallEffects.Effect)) := cs.mapM fun
    | .arrs arrows variadic | .callable _ _ arrows variadic _ =>
      let effs :=
        (arrows.filterMap fun (⟨_, ps, _, eff⟩ : CallEffects.Arrow (Ty ι)) => if ps.length == arity then some eff else none) ++
        (variadic.filterMap fun (⟨_, (ps, _), _, eff⟩ : CallEffects.RestArrow (Ty ι)) => if ps.length ≤ arity then some eff else none)
      if effs.isEmpty then none else some effs
    | _ => none
  perClause.map List.flatten

/-- Whether an expression is a call whose callee's matching signatures all
state a fresh array region (`ExitSchema.freshRegionResult`). -/
@[nospecialize] private def freshRegionCall {ι : Type} (G : PositiveGraphs.NormalGraph ι) (Γ : List (Ty ι)) :
    Tm → Bool
  | .invoke (.var f) _ args =>
    match Γ[f]?.bind (matchingCallEffects G · args.length) with
    | some effs => !effs.isEmpty && effs.all (·.schema.normal.freshRegionResult)
    | none => false
  | _ => false

/-- Whether an expression is a call whose callee's matching signatures all
state a fresh array spine (`ExitSchema.freshResult`). -/
@[nospecialize] private def freshSpineCall {ι : Type} (G : PositiveGraphs.NormalGraph ι) (Γ : List (Ty ι)) :
    Tm → Bool
  | .invoke (.var f) _ args =>
    match Γ[f]?.bind (matchingCallEffects G · args.length) with
    | some effs => !effs.isEmpty && effs.all (·.schema.normal.freshResult)
    | none => false
  | _ => false

/-- The receiver slot whose array spine a node grows via a call whose matching
signatures all state receiver extension (`PromiseCalls.statesExtension`, e.g. `push`). -/
@[nospecialize] private def spineGrown {ι : Type} (G : PositiveGraphs.NormalGraph ι) (Γ : List (Ty ι)) :
    Tm → Option Nat
  | .invoke (.var f) (.var w) args =>
    match Γ[f]?.bind (matchingCallEffects G · args.length) with
    | some effs =>
      if !effs.isEmpty && effs.all PromiseCalls.statesExtension then some w else none
    | none => none
  | _ => none

/-- **The region separations at a unit's loop heads**: the pairs of slots
whose regions an allocation or fresh-region call states apart
(`IndexWrites.regionAtoms`, `freshRegionCall`), each with its allocation,
carried along every edge to the slots whose mappings read them, those every
predecessor carries; at each loop head, the pairs of array slots
(`IndexWrites.arraySlot`) of an allocation (a literal, a split array wrapper,
`IndexWrites.freshApart`, or a fresh-region call) where the allocation's array
or either slot's array is written at an element somewhere in the unit
(`elementWritten`: the write keeps a quantified fact over an array apart from
it, `IndexWrites.overwriteAtoms`), as `IndexFact.apart`, together with any
path-level `spineApart` candidate already proposed for a written slot upgraded
to `IndexFact.apart`; for each fresh-spine array grown in a loop
(`spineGrown`), any `spineApart` candidate for that grown slot upgraded to
`IndexFact.elemSpineApart`; and, in a loop calling a function that states a
fresh array region, each nullable array slot `x` guarded apart from every
other array slot. With `force` (`--force-proposals head-apart`), each written
side also stated apart from
itself, the adversarial pair the pass's edge check refuses. -/
def freshApartAt (r : SourceElaboration.SourceRequest σ ι) (force : Bool := false) :
    List (Nat × List HeapKnowledge.Candidate) := Id.run do
  let G := RequestJson.graph r.toRequest
  let P := r.program
  let ctxOf := fun (l : Nat) => ((r.claims[l]?).map (·.context)).getD []
  let width := fun (l : Nat) => (ctxOf l).length
  let heads := (SinglePass.loopHeads P.toArray r.start).1
  let A := P.toArray
  let writeNodes : List (Nat × Nat) := (List.range A.size).filterMap fun l => ((A[l]?).bind (elementWritten ·.expression)).map (l, ·)
  let growNodes : List (Nat × Nat) := (List.range A.size).filterMap fun l => ((A[l]?).bind fun n => spineGrown G (ctxOf l) n.expression).map (l, ·)
  if writeNodes.isEmpty && growNodes.isEmpty then return []
  let bodies := (r.cuts.filter (heads.getD · false)).map fun h => (h, loopBody P h)
  let grows := bodies.map fun (h, body) =>
    let inner := fun (l : Nat) => bodies.any fun (h', b) => h' != h && body.getD h' false && b.getD l false
    (h, growNodes.filter fun (p : Nat × Nat) => body.getD p.1 false && !inner p.1)
  -- Region-apart allocations for element-written arrays.
  let isArrayWrap := fun (Γ : List (Ty ι)) (e : Tm) => match e with
    | .makeAt .absent [s, p] [.var 0, .var proto] =>
      s == arraySpineKey && p == CallArguments.protoField && decide (proto < Γ.length) && IndexWrites.spineSlot G Γ 0
    | _ => false
  let isArrayAlloc := fun (Γ : List (Ty ι)) (e : Tm) =>
    isArrayWrap Γ e || match e with
      | .arrLit _ | .letE (.arrLit _) (.makeAt .absent _ _) => true
      | _ => false
  let allocates := fun (l : Nat) => ((A[l]?).map fun node =>
    let Γ := ctxOf l
    let atoms :=
      if isArrayWrap Γ node.expression then IndexWrites.freshApart G Γ
      else IndexWrites.regionAtoms G Γ {} node.expression
    let lit := atoms.filterMap fun a => match a.fact with
      | .apart x [] y [] => some (x, y, l)
      | _ => none
    let call := if freshRegionCall G Γ node.expression then
        (IndexWrites.arrayPartners G Γ).map fun y => (0, y + 1, l)
      else []
    lit ++ call).getD []
  -- The slot each allocation's result is carried to, then the allocations
  -- written at an element anywhere in the unit. Carry every allocation's
  -- apart pairs so pairs where either side is written survive to loop heads.
  let held := carryForward P r.start width (fun l =>
    if (A[l]?).any (fun node => isArrayAlloc (ctxOf l) node.expression) || !(allocates l).isEmpty then [(0, 0, l)] else []) true
  let written := writeNodes.flatMap fun (l, w) =>
    ((held.getD l none).getD []).filterMap fun (a, _, o) => if a == w then some o else none
  let table : Array (Option (List (Nat × Nat × Nat))) :=
    if written.isEmpty then Array.replicate P.length none
    else carryForward P r.start width allocates false
  -- Fresh-spine allocations for grown loops.
  let isFreshSpine := fun (l : Nat) => ((A[l]?).map fun node =>
    let Γ := ctxOf l
    !(IndexWrites.regionAtoms G Γ {} node.expression).isEmpty || freshSpineCall G Γ node.expression).getD false
  let heldSpine := if grows.all (·.2.isEmpty) then #[] else
    carryForward P r.start width (fun l => if isFreshSpine l then [(0, 0, l)] else []) true
  let grownOrigsAt := fun (h : Nat) => ((grows.find? (·.1 == h)).map (·.2)).getD [] |>.flatMap fun (l, w) =>
    ((heldSpine.getD l none).getD []).filterMap fun (a, _, o) => if a == w then some o else none
  -- Loops that call a function stating a fresh array region (`freshRegionResult`,
  -- e.g. `new Array(n).fill(v)`) and hold a nullable array slot `x`: propose
  -- `x === null || apart(a, x)` for each other array slot `a` at the head. A call
  -- qualifies when some signature (fixed or variadic, call or construct) of its
  -- callee's type states the fresh region; each proposal is checked on every edge.
  let statesFreshRegion : PositiveNormalization.Clause (List ι) → Bool
    | .arrs L V | .callable _ _ L V _ =>
      L.any (·.effect.schema.normal.freshRegionResult) || V.any (·.effect.schema.normal.freshRegionResult)
    | .ctors S V .. =>
      S.any (·.effect.schema.normal.freshRegionResult) || V.any (·.effect.schema.normal.freshRegionResult)
    | _ => false
  let calleeStatesFreshRegion (l f : Nat) : Bool :=
    ((ctxOf l)[f]?).any fun F => (PositiveRules.expand G F).any statesFreshRegion
  let hasFreshRegionCall (l : Nat) : Bool := match A[l]? with
    | some node => match node.expression with
      | .invoke (.var f) _ _ | .construct (.var f) _ => calleeStatesFreshRegion l f
      | _ => false
    | none => false
  let nullableArraySlot (Γ : List (Ty ι)) (s : Nat) : Bool := match Γ[s]? with
    | some R =>
      let cs := PositiveRules.expand G R
      cs.any (· == .nul) && cs.any (fun | .refs fs [] vs .. => (Stored.views fs).any (·.1 == arraySpineKey) || vs.any (·.1 == arraySpineKey) | _ => false)
    | none => false
  return r.cuts.filterMap fun h => do
    guard (heads.getD h false)
    let Γ := ctxOf h
    let writtenSlots := ((held.getD h none).getD []).filterMap fun (s, _, o) =>
      if written.contains o then some s else none
    let ps : List (Nat × Nat) := match table.getD h none with
      | some ps => (ps.filter fun (a, b, o) =>
          (written.contains o || writtenSlots.contains a || writtenSlots.contains b) &&
            IndexWrites.arraySlot G Γ a && IndexWrites.arraySlot G Γ b).map
          fun (a, b, _) => (a, b)
      | none => []
    let ps := ps.eraseDups
    let ps := ps ++ (if force then (ps.map (·.1)).eraseDups.map fun a => (a, a) else [])
    let pathCands : List HeapKnowledge.Candidate :=
      ((r.candidates.filter (·.1 == h)).flatMap (·.2)).filterMap fun
        | .index ⟨.spineApart x px y py, none, false⟩ =>
          if (writtenSlots.contains x && px.isEmpty) || (writtenSlots.contains y && py.isEmpty) then
            some (HeapKnowledge.Candidate.index { fact := .apart x px y py })
          else none
        | _ => none
    let elemCands : List HeapKnowledge.Candidate :=
      let grownOrigs := grownOrigsAt h
      if grownOrigs.isEmpty then [] else
      let grownSlots := ((heldSpine.getD h none).getD []).filterMap fun (a, _, o) =>
        if grownOrigs.contains o then some a else none
      ((r.candidates.filter (·.1 == h)).flatMap (·.2)).flatMap fun
        | .index ⟨.spineApart x px y py, none, false⟩ =>
          (if grownSlots.contains x && px.isEmpty then [HeapKnowledge.Candidate.index { fact := .elemSpineApart x [] y py }] else []) ++
          (if grownSlots.contains y && py.isEmpty then [HeapKnowledge.Candidate.index { fact := .elemSpineApart y [] x px }] else [])
        | _ => []
    let bodyHasFresh := match bodies.find? (·.1 == h) with
      | some (_, body) => (List.range A.size).any fun l => body.getD l false && hasFreshRegionCall l
      | none => false
    let guardedApart : List HeapKnowledge.Candidate := if !bodyHasFresh then [] else
      let arrs := (List.range Γ.length).filter (IndexWrites.arraySlot G Γ)
      let nulls := (List.range Γ.length).filter (nullableArraySlot Γ)
      nulls.flatMap fun x => arrs.filterMap fun a =>
        if a == x then none else some (HeapKnowledge.Candidate.index { fact := .guarded x [] .null (.apart a [] x []) })
    let cands := (ps.map (fun (a, b) => HeapKnowledge.Candidate.index { fact := .apart a [] b [] }) ++
      pathCands ++ elemCands ++ guardedApart).eraseDups
    if cands.isEmpty then none else some (h, cands)
end

/-- The plans with the loop heads of each unit of `group` proposed the region
separations its allocations state (`freshApartAt`), beside its other
candidates. -/
def FilePlans.withFreshApart (f : FilePlans) (force : Bool := false) (group : List Nat) : FilePlans :=
  { f with plans := f.plans.zipIdx.map fun (p, i) => if !group.contains i then p else p.map (FunctionPlan.mapRequest fun r =>
      let extra := freshApartAt r force
      if extra.isEmpty then r else
      let cands := extra.foldl (fun (cs : List (Nat × List HeapKnowledge.Candidate)) (l, as) =>
        if cs.any (·.1 == l) then cs.map fun (l', bs) => if l' == l then (l', bs ++ as.filter (!bs.contains ·)) else (l', bs)
        else cs ++ [(l, as)]) r.candidates
      { r with candidates := cands }) }

end Verification.SourceClaimJson
