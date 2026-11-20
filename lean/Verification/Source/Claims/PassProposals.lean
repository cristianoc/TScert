import Verification.Source.Claims.MemberSettle
import Verification.Source.Synthesis.ExitProposals

/-! **Proposals by the pass** ([proposals by the pass](../../../../docs/drafts/proposals-by-the-pass.md)):
what the front proposes about a body's unwritten effect is computed with
the pass's own steps on that body. A function's unwritten effect is a
per-exit summary (`SourceElaboration.ClassSummary`): each checked step's
local summary, independent of any enclosing bound, composed over the body's
graph by the rules of `ClassSummary` (`composeGraph`: Seq-Eff on both
exits, choice at joins, a caught throw entering its handler). A step's
local summary is read on one of the two routes the pass checks a footprint
by: the direct node-by-node check, from its visit's certificate
(`localSummary`), and the regional fallback, whose alternatives
(`ArgumentRegionGraph.stepEffects`' kinds) are rebased to the entry
through the regional facts (`rebaseAll`) and read in the closed language
(`regional`). The returned function's footprint is read off the returned
value's checked type. A plan reads a summary's projection
(`ClassSummary.project`, whose schema is above the summary's,
`ClassSummary.project_entails`). A proposal decides nothing: the
function's own unit checks it, and its callers read it. -/
namespace Verification.SourceClaimJson

/-- A written-footprint stand-in: the effect a function or an import would
state if written, supplied apart from the source, as its complete per-exit
summary (`SourceElaboration.ClassSummary`), with the footprint of the
function it returns. The command line supplies none. -/
structure StandIn where
  name : String
  summary : SourceElaboration.ClassSummary := ⟨some .top, some .top⟩
  resultFootprint : Footprints.Closed := .top

/-- **A stand-in in today's effect format**: its summary's projection
(`ClassSummary.project`, an upper bound at each exit), where a plan's
footprint and throw bound are written. -/
def StandIn.effect (s : StandIn) : CallEffects.Effect := s.summary.project

/-- The closed footprint the claims document writes for a stand-in
(`ClassSummary.format`). -/
def StandIn.footprint (s : StandIn) : Footprints.Closed := s.summary.format.1

/-- The throw flag the claims document writes for a stand-in
(`ClassSummary.format`). -/
def StandIn.onThrow (s : StandIn) : Bool := s.summary.format.2

/-- The stand-in of today's format: the summary of a closed footprint and a
throw bound (`ClassSummary.ofFormat`). -/
def StandIn.ofFormat (name : String) (c : Footprints.Closed) (t : Bool) (r : Footprints.Closed := .top) : StandIn :=
  ⟨name, SourceElaboration.ClassSummary.ofFormat c t, r⟩

/-- The stand-ins of a file: for the file's functions and for its imports. -/
structure StandIns where
  functions : List StandIn := []
  imports : List StandIn := []

namespace PassProposals
open Lean ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open SourceElaboration LabelStore RequestJson
open HeapKnowledge (Knowledge)

abbrev Closed := Verification.Footprints.Closed

/-! ## The closed lattice -/

/-- Every closed footprint stating one change for both spines
(`Footprints.Closed.ofSpines`), each a change the closed footprint's wire
names (`EffectJson`: `keep`, `init`, `scalar`, `extend`, `grow`, `any`), in an order
extending the components' rank order: a footprint comes after every
footprint below it. -/
def ascending : List Closed :=
  let cs := [Footprints.Change.keep, .init, .scalar, .extend, .grow, .any]
  ((cs.flatMap fun v => cs.map fun s => Footprints.Closed.ofSpines v s).mergeSort fun a b =>
    a.value.rank + a.spines.rank ≤ b.value.rank + b.spines.rank)

def keepAll : Closed := ⟨.keep, .keep, .keep⟩

/-- The join: each component's larger change, an upper bound in `Closed.le`
and in the order `Footprint.le` reads changes in. -/
def join (a b : Closed) : Closed := ⟨a.value.max b.value, a.array.max b.array, a.view.max b.view⟩

def joinOpt : Option Closed → Option Closed → Option Closed
  | some a, some b => some (join a b)
  | _, _ => none

/-- The least footprint, by `ascending`, a monotone predicate accepts:
every footprint above an accepted one is accepted, so the first accepted is
minimal. -/
def leastAccepted (p : Closed → Bool) : Option Closed := ascending.find? p

/-- The closed language's reading of a frame: the least closed footprint
whose frame includes it, as `stepWithin` reads inclusion. -/
def ofFrame (fp : Footprints.Footprint) : Option Closed :=
  leastAccepted fun c => Footprints.Footprint.le GraphCode.ArgumentRegionGraph.noClasses (c.fp ++ fp) c.fp

section
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-! ## A step's local effect

Every step the pass checks has its local effect on each route, read from
its evidence: on the direct route its visit's certificate (`localSummary`),
on the regional route the least closed footprint its check accepts there. -/

/-- The parts of the regional route's closed check (`checkClosedNode`) that
read no bound, computed once for a step: its scope, whether it is an
inspection, its derivation's tree checked at its term, and an empty result
or entry. -/
structure ClosedParts where
  scope : Bool
  inspect : Bool
  tree : Bool
  empty : Bool
  emptyEntry : Bool

def closedParts (G : NormalGraph ι) (images : InstanceImageCheck G) (sums : List (ReadSummary ι))
    (c : NodeEvidence ι) (t : Tm) : ClosedParts :=
  { scope := ProgramCertificates.checkScope (ControlFlow.entry c).length t
    inspect := ExpressionEffects.check G (ControlFlow.entry c) t
    tree := decide ((ProgramCertificates.claim c.expression).term = t) &&
      (ProgramCertificates.checkTreeUsing G images c.expression (sums := sums) ||
        PromiseCalls.requiresTree G images (ControlFlow.entryFacts G c) (fun _ => false) sums c.expression)
    empty := ExpressionEffects.emptyType G (ControlFlow.result c)
    emptyEntry := (ControlFlow.entry c).any (fun A => ExpressionEffects.emptyType G A) }

/-- The closed check at `Φ` from its parts. -/
def ClosedParts.at (p : ClosedParts) (G : NormalGraph ι) (Φ : Closed) (c : NodeEvidence ι) (t : Tm) (thr : Bool) :
    Bool :=
  let w := GraphCode.writeWithinAt G Φ c t
  let sel := GraphCode.selectedWithinAt Φ [] c.expression
  let selT := GraphCode.selectedThrowsWithinAt Φ [] c.expression
  p.scope && (!thr || ((p.inspect || w) || (p.tree && selT) || p.emptyEntry)) &&
    (((p.inspect || w) || (p.tree && sel)) || p.empty)

omit [Hashable ι] [Instantiates ι] in
/-- **The closed check from its parts is the closed check** (proved). -/
theorem closedParts_at (G : NormalGraph ι) (images : InstanceImageCheck G) (sums : List (ReadSummary ι))
    (Φ : Closed) (c : NodeEvidence ι) (t : Tm) (thr : Bool) :
    (closedParts G images sums c t).at G Φ c t thr =
      GraphCode.ArgumentRegionGraph.checkClosedNode G images sums Φ c t thr := by
  simp only [closedParts, ClosedParts.at, GraphCode.ArgumentRegionGraph.checkClosedNode, GraphCode.throwsWithin,
    Bool.and_assoc]

/-- A step's local effect on the regional route, its throw bounded where
`thr`: the least of its alternatives, each rebased to the entry through the
regional facts `rs` and read in the closed language (`ofFrame`): the closed
check (`checkClosedNode`), a call's frame (`callStep`), an element write's
frame (`elemWriteStep`), a field write's (`fieldWriteStep`). -/
def regional (G : NormalGraph ι) (images : InstanceImageCheck G) (sums : List (ReadSummary ι))
    (rs : SinglePass.RegionState) (cEv : NodeEvidence ι) (t : Tm) (thr : Bool)
    (parts : ClosedParts := closedParts G images sums cEv t) : Option Closed :=
  -- (the parts no bound enters checked once, `closedParts_at`)
  let closed := leastAccepted fun Φ => parts.at G Φ cEv t thr
  let rebased := fun (se : GraphCode.ArgumentRegionGraph.StepEffect) =>
    let ev := GraphCode.ArgumentRegionGraph.nodeRebase [] rs.facts rs.values rs.fields se
    let n := ofFrame (Footprints.rebaseAll ev se.normal)
    if thr then joinOpt n (ofFrame (Footprints.rebaseAll ev se.raised)) else n
  let call := (GraphCode.ArgumentRegionGraph.callStep G images sums cEv t).bind rebased
  let write := (ExpressionEffects.elemWriteStep G (ControlFlow.entry cEv) t).bind fun w =>
    rebased (GraphCode.ArgumentRegionGraph.writeStepEffect w)
  let field := (ExpressionEffects.fieldWriteStep G (ControlFlow.entry cEv) t).bind fun w =>
    rebased (GraphCode.ArgumentRegionGraph.fieldStepEffect w)
  ascending.find? fun Φ => [closed, call, write, field].any fun a => a.any (·.le Φ)

/-- A step's local effects on the regional route with its throw bounded
where `handled` and with it bounded (`regional` at both, the bound-free
parts checked once): the same where `handled`. -/
def regionalBoth (G : NormalGraph ι) (images : InstanceImageCheck G) (sums : List (ReadSummary ι))
    (rs : SinglePass.RegionState) (cEv : NodeEvidence ι) (t : Tm) (handled : Bool) : Option Closed × Option Closed :=
  let parts := closedParts G images sums cEv t
  let raised := regional G images sums rs cEv t true parts
  (if handled then raised else regional G images sums rs cEv t false parts, raised)
end

/-! ## A member's interface -/

/-- What a member's own steps establish of its interface: its per-exit
summary (the closed bounds of its normal and exceptional exits), the
footprint of the function it returns, and the transfers its two runs
visited. -/
structure Established where
  summary : SourceElaboration.ClassSummary
  result : Closed
  visits : Nat

/-- The labels of a file's plans. -/
abbrev Label (f : FilePlans) : Type := EquationStore.CheckedLabel f.F.equations f.F.primitive

/-- What the direct route reads of a member's visited steps (`directRead`):
its body's summary composed over the graph (`composeGraph`), none where the
composition does not settle; the returned values' functions' footprint, and
whether any return was visited. -/
structure DirectRead where
  summary : Option SourceElaboration.ClassSummary
  result : Closed
  returns : Bool

/-- **A step's local summary from its visit's certificate**
(`SinglePass.StepCertificate`): at each exit, the meet of the closed bounds
below the mark (`Footprint.boundBelow`) of the exit specifications its
rules establish, each of which holds of the step (`Closed.holds_meet`);
`top` where no rule bounds that exit, and at both exits where the step's
scope check fails. Bound-independent: no enclosing bound is read. -/
def localSummary (q : SinglePass.StepCertificate) : SourceElaboration.ClassSummary :=
  let bound := fun (xs : List CallEffects.ExitSpec) =>
    match xs.map (fun x => Footprints.Footprint.boundBelow q.fresh x.frame) with
    | [] => Footprints.Closed.top
    | g :: gs => gs.foldl Footprints.Closed.meet g
  if q.scope then ⟨some (bound q.normal), some (bound q.exceptional)⟩
  else ⟨some .top, some .top⟩

/-- **A body's summary composed over its graph** (the note, §6: Seq-Eff on
both exits, choice at joins, a handler's entry at a caught throw; the rules
of `ClassSummary`): from the start label's entry, where nothing has
changed, each node `l` of local summary `S` at the bound `p` of the paths
reaching it passes `p ⊔ S.normal` to its successors (to the body's normal
exit at a return) and `p ⊔ S.exceptional` to its handler (to the body's
exceptional exit where it has none); the paths reaching a node join. A node
no visit reached has no local summary and passes nothing. The graph
worklist revisits a node when its entry rises, each at most 13 times (unreached, then three components of rank at
most 4). The composition is the least fixed point; an exit no visited
node reaches has no summary. -/
def composeGraph (nodes : Array Node) (start : Nat) (locals : Array (Option SourceElaboration.ClassSummary)) :
    Option SourceElaboration.ClassSummary :=
  let n := nodes.size
  let initial : Array (Option Closed) × SourceElaboration.ClassSummary :=
    ((Array.replicate n none).set! start (some keepAll), ⟨none, none⟩)
  let graph := (nodes.toList.map fun node => (node, ())).zipIdx
  let transfer := fun (((node, _), l) : (Node × Unit) × Nat)
      ((entry, out) : Array (Option Closed) × SourceElaboration.ClassSummary) => Id.run do
    match entry.getD l none, locals.getD l none with
    | some p, some S =>
      let N := SourceElaboration.ClassSummary.andThen (some p) S.normal
      let X := SourceElaboration.ClassSummary.andThen (some p) S.exceptional
      let mut entry := entry
      let mut out := out
      if node.continuation == .ret then out := { out with normal := SourceElaboration.ClassSummary.alt out.normal N }
      for t in successors node.continuation do
        entry := entry.set! t.label (SourceElaboration.ClassSummary.alt (entry.getD t.label none) N)
      match node.handler with
      | some t => entry := entry.set! t.label (SourceElaboration.ClassSummary.alt (entry.getD t.label none) X)
      | none => out := { out with exceptional := SourceElaboration.ClassSummary.alt out.exceptional X }
      return (entry, out)
    | _, _ => return (entry, out)
  (graphWorklist graph transfer (fun state l => state.1.getD l none) (13 * n + 2) initial).map (·.2)

/-- A step whose result type is empty never returns normally
(`ExpressionEffects.emptyType`, the pass's `deadNode`): its normal exit is
unreached. -/
def unreturning {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (claimed : Array (PointClaim ι)) (l : Nat)
    (S : SourceElaboration.ClassSummary) : SourceElaboration.ClassSummary :=
  match claimed[l]? with
  | some c => if ExpressionEffects.emptyType G c.type then { S with normal := none } else S
  | none => S

/-- The local summaries by label: each label's visits' summaries joined
(`ClassSummary.choice`). -/
def localsOf (n : Nat) (visits : List (Nat × SourceElaboration.ClassSummary)) :
    Array (Option SourceElaboration.ClassSummary) :=
  visits.foldl (init := Array.replicate n none) fun acc (l, S) =>
    if l < n then acc.set! l (some (match acc.getD l none with
      | some T => T.choice S
      | none => S)) else acc

section
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **The direct route's summary of a member** from each visit's record of
its step's local certificate (`records`, `SinglePass.Walk.visits`): the
local summaries (`localSummary`) composed over the graph (`composeGraph`);
at each return the returned value's checked type's footprint (the join of
its signatures', `top` for a value of no function type). -/
def directRead (G : NormalGraph ι) (nodes : Array Node) (claimed : Array (PointClaim ι)) (start : Nat)
    (records : Array SinglePass.VisitRecord) : DirectRead := Id.run do
  let n := nodes.size
  let mut result : Closed := keepAll
  let mut returns := false
  for r in records do
    let l := r.label
    if l ≥ n then continue
    let node := nodes[l]!
    let c := claimed[l]!
    if node.continuation == .ret then
      returns := true
      let T := match node.expression with
        | .var j => (c.context[j]?).getD c.type
        | _ => c.type
      result := join result (match PositiveRules.expand G T with
        | [.arrs L S] => if L.isEmpty && S.isEmpty then .top else
          ((L.map (·.effect)) ++ S.map (·.effect)).foldl (init := keepAll) fun acc e => join acc e.changeBound
        | _ => .top)
  let locals := localsOf n (records.toList.map fun r => (r.label, unreturning G claimed r.label (localSummary r.certificate)))
  return ⟨composeGraph nodes start locals, result, returns⟩

end

/-- **A member's interface from its own steps**, given its plans and given
lines settled with its footprint open (`settledInterface`) and, where its
last settling run was the walk with no bound, that run's visits' records
(`grades`): the direct route's footprint from them
(`directRead`), else from a walk with no bound; and the regional route's,
where the direct route's footprint is more than keep/keep (no footprint is
below it): the walk under the regional fallback at `top` (its tables
`regionalInferred` there), each visited step's least regional
alternative (`regional`). The less of the two routes' footprints, the
throw bound where that route's throws are within it; the returned value's
checked type's footprint at every return. None where a run stops: the pass
establishes nothing of the member. A qualified or async body is `top` by
the language (`passMember`, `RequestJson.asyncEffects`). -/
def interface (f : FilePlans) (fuel : Nat) (i : Nat) (given : Option (Std.HashMap String Json))
    (grades : Option (Array SinglePass.VisitRecord)) (visitsA : Nat) : Option Established := Id.run do
  let G : NormalGraph (Label f) := StoreView.graph f.F.store
  let I : PositiveCertificates.InstanceImageCheck G := StoreView.images f.F.store
  let answers : CertificateProducer.Answered G := {}
  let some (.ok plan) := f.plans[i]? | return none
  let .ok (.graph _ _ r) := plan.certify | return none
  if r.qualification.isSome || r.async then return some ⟨⟨some .top, some .top⟩, .top, 0⟩
  let nodes := r.program.toArray
  let claimed := r.claims.toArray
  let n := nodes.size
  -- The walk the regional route (and, with no grades, the direct route,
  -- its visits recording their steps' local effects) runs: the code
  -- requests run first, as `passMember` checks them.
  let prepared : Unit → Option ((Option SinglePass.Regional →
      Except (SinglePass.WalkStop (Label f) G) (SinglePass.WalkState (Label f) G × Nat)) × (CodeEntry (Label f) → Bool)) :=
      fun _ => SinglePass.work "propose: preparation" (f.fr.workItem i) fun _ => do
    let labels := r.searchLabels
    let .ok (e, next) := ExpressionClaims.produceUsing G I labels (StoreView.valid r.types)
      (StoreView.projection r.types) fuel r.obligations { answers with summaries := #[], summaryAnswers := {} }
      | none
    let (rendered, next) := ExpressionClaims.renderKnownUsing G I labels (StoreView.valid r.types) r.nodePlans next
    let pool := CertificateProducer.vocabulary G labels r.claims r.inputs
    let line := given.bind fun m => m.get? (f.fr.unitId i)
    let main : GivenHeads _ := match line with
      | some l => match (l.getObjVal? "graph").bind (GivenHeads.fromJson r.program.length) with
        | Except.ok g => g
        | Except.error _ => {}
      | none => {}
    let codeStep := fun (table : List (CodeEntry _)) (sumsAnswers : CertificateProducer.Answered G)
        ((q, ci) : CodeRequest _ × Nat) =>
      let hints := (r.codeHints[ci]?).getD {}
      let rq := q.asRequest r.toRequest
      let eff := q.entry.row.effect
      -- (the code's conditions and bound are the check's own,
      -- `ProgramTyping.codeConditions` and `ProgramTyping.codeBound`: a
      -- proposal's run is the run the check makes)
      let conditions := ProgramTyping.codeConditions q.entry
      if !conditions || !RequestJson.asyncAdmits q.async eff then
        ({ index := ci, outcome := .refused s!"code {ci}", answers := sumsAnswers, line := "" } : CodeRun _ _)
      else
      let codeBound := ProgramTyping.codeBound q.entry
      let codePool := CertificateProducer.vocabulary G labels rq.claims rq.inputs
      let codeGiven : GivenHeads _ := match line with
        | some l => match (l.getObjVal? "codes").bind fun cs => do
            let arr ← cs.getArr?
            GivenHeads.fromJson rq.program.length ((arr[ci]?).getD (Json.arr #[])) with
          | Except.ok g => g
          | Except.error _ => {}
        | none => {}
      let (o, _, a, _) := SinglePass.runRecorded "code" "direct"
          (runDigests r line s!"code {ci}" (boundText codeBound none)) (fun x => x.2.1.visited) fun _ =>
        SinglePass.run G I codePool fuel rq.program rq.claims rq.start rq.inputs q.entry.goal
        hints.requirements hints.cuts hints.candidates rq.entryIndices [] (e ++ rendered) (GraphCode.admits table)
        r.aliases .ordinary sumsAnswers #[] 1000000000 codeBound codeGiven.implies codeGiven.args
      { index := ci, outcome := o.asRefusal, answers := a, line := "" }
    let (codeRuns, table, sumsAnswers) := codesInOrder (·.1.entry) codeStep [] next r.codes.zipIdx
    if codeRuns.any fun c => !(c.outcome matches .accepted) then none
    let codes := GraphCode.admits table
    pure (fun (rg : Option SinglePass.Regional) =>
      SinglePass.work "propose: member run" (f.fr.workItem i) fun _ =>
      SinglePass.runRecorded "propose-walk" (if rg.isSome then "regional-top" else "direct")
        (runDigests r line "main" (boundText none rg)) (fun x => match x with | .ok (σ, _) => σ.walk.visited | .error _ => 0) fun _ =>
      SinglePass.runWalk G I pool fuel r.program r.claims r.start r.inputs r.goal r.assertions r.cuts r.candidates
        r.entryIndices [] (e ++ rendered) codes r.aliases .ordinary sumsAnswers #[] 1000000000 none
        main.implies main.args r.ensures main.inputs r.entrySeparation none false false rg rg.isNone, codes)
  -- (prepared once, where a walk needs it)
  let prepared := Thunk.mk prepared
  -- The direct route: the settling run's steps, else a walk with no bound.
  let (read, visits) ← match grades with
    | some gs => pure (SinglePass.work "propose: direct read" (f.fr.workItem i) fun _ => directRead G nodes claimed r.start gs, visitsA)
    | none =>
      let some (walk, codes) := prepared.get | return none
      let .ok (σ, reach) := walk none | return none
      if σ.walk.visited < reach then return none
      pure (directRead G nodes claimed r.start σ.walk.visits, σ.walk.visited)
  let normal := read.summary.bind (·.normal)
  -- The regional route: the walk under the regional fallback at `top`, run
  -- where the direct route's footprint is more than keep/keep (no footprint
  -- is below it).
  let (regionalS, visitsB) : Option SourceElaboration.ClassSummary × Nat :=
    if normal == some keepAll then (none, 0) else
    match prepared.get with
    | none => (none, 0)
    | some (walk, _) =>
    let tables := SinglePass.work "propose: regional tables" (f.fr.workItem i) fun _ => regionalInferred r .top [] none
    let (names, heads) := (regionalFromJson r.program.length tables).toOption.getD ([], #[])
    let rgTop : SinglePass.Regional := { Φ := .top, regions := [], exc := false, names, heads }
    match walk (some rgTop) with
    | .ok (σB, reachB) =>
      if σB.walk.visited < reachB then (none, σB.walk.visited) else
      let sumsB := σB.answers.summaries.toList
      -- (each visited step's local summary: its effect on normal return and
      -- with its throw bounded, `regionalBoth`, `top` where none bounds an
      -- exit; composed over the graph, `composeGraph`)
      let locals := SinglePass.work "propose: regional local effects" (f.fr.workItem i) fun _ =>
        (List.range n).foldl (init := (Array.replicate n none : Array (Option SourceElaboration.ClassSummary))) fun acc l =>
        match σB.walk.labels[l]? with
        | some (lw : SinglePass.LabelWalk (Label f)) => match lw.visited, lw.entry, lw.stepped, lw.region with
          | true, some entry, some st, some rs =>
            let node : Node := nodes[l]!
            let c : PointClaim (Label f) := claimed[l]!
            let width := c.context.length
            let ordinaryEv : Option (OrdinaryEvidence (Label f)) := match st.stepDeriv, st.stepEffect with
              | some dv, _ => some (.proof dv)
              | none, some _ => some .effect
              | none, none => none
            let cEv : NodeEvidence _ := ⟨ordinaryEv, some ⟨c.context, node.expression, c.type⟩, [],
              {}, st.stepEffect, {}, none, [], [], [], none⟩
            -- A scoped inspection satisfies ClosedParts.at at the first
            -- closed bound, on both exits. No fact of its entry is read.
            let Γ := ControlFlow.entry cEv
            let (a, b) := if ExpressionEffects.check G Γ node.expression &&
                ProgramCertificates.checkScope Γ.length node.expression then (some keepAll, some keepAll)
              else
                let kHere := (SinglePass.materialize entry width (List.range width) true).1
                regionalBoth G I sumsB rs { cEv with knowledge := SinglePass.regionalFacts kHere st.stepK }
                  node.expression false
            acc.set! l (some (unreturning G claimed l ⟨some (a.getD .top), some (b.getD .top)⟩))
          | _, _, _, _ => acc
        | none => acc
      (composeGraph nodes r.start locals, σB.walk.visited)
    | .error _ => (none, 0)
  -- The route of the less normal bound, its summary (`top` at an exit no
  -- composition settles): the member's summary.
  let topS : SourceElaboration.ClassSummary := ⟨some .top, some .top⟩
  let S := match read.summary, regionalS with
    | some a, some b => if (b.normal.getD .top).le (a.normal.getD .top) && !(a.normal.getD .top).le (b.normal.getD .top)
        then b else a
    | some a, none => a
    | none, some b => b
    | none, none => topS
  return some ⟨S, if read.returns then read.result else .top, visits + visitsB⟩

/-- A plan's request at `top` with no throw bound: its walk unbounded. -/
def openAt (f : FilePlans) (i : Nat) : FilePlans :=
  { f with plans := f.plans.zipIdx.map fun (p, j) => if j != i then p else p.map fun
    | .graph name pos r => .graph name pos { r with footprint := .top, onThrow := false }
    | p@(.framed ..) => p }

/-- Whether member `i`'s plan runs its main graph with no bound when open
(`passMember`'s `bounded`): no fresh result stated. -/
def openUnbounded (f : FilePlans) (i : Nat) : Bool :=
  match f.plans[i]? with
  | some (.ok (.graph _ _ r)) => !r.fresh && r.regional.isNone
  | _ => false

/-- Member `i`'s plans and given lines settled with its footprint open, as
`passGroupMode8` settles them (`inferredSettle`'s runs and next states),
each run reporting its visits' records (`passMember`'s `grading`),
then its interface from its steps there: from the last run's, where that
run walked its graph with no bound. -/
def settledInterface (f : FilePlans) (fuel : Nat) (i : Nat) : Option Established :=
  let f := openAt f i
  let group := f.fr.group i
  let given := some (f.computedGiven {} false false none group)
  let f := f.withFreshApart false group
  let candidates : List (Nat × List HeapKnowledge.IndexAtom) := match f.plans[i]? with
    | some (.ok (.graph _ _ r)) => r.candidates
    | _ => []
  let heads := (candidates.filter fun (c : Nat × List HeapKnowledge.IndexAtom) => !c.2.isEmpty).length
  let s := settleInferred
    (fun (g : FilePlans) gv => SinglePass.work "propose: settling run" (f.fr.workItem i) fun _ =>
      match g.passMember fuel i false 1000000000 1 gv none false true with
      | .ok m =>
        let why : Option (String × Option (Nat × List HeapKnowledge.IndexAtom)) := match m.outcome with
          | .refused w lacks _ => some (w, lacks)
          | _ => none
        -- The main graph's walk with no bound, where the run made it
        -- (`openUnbounded`, the direct route): its visits' records
        -- where it was accepted, its refusal kept (`none`) where not.
        let walked : Option (Option (Array SinglePass.VisitRecord × Nat)) :=
          if openUnbounded g i then match m.main with
            | some mr => if mr.route matches FootprintRoute.direct then
                (if mr.outcome matches .accepted then
                  (if (MainRun.counts mr).grades.isEmpty then none
                    else some (some ((MainRun.counts mr).grades, (MainRun.counts mr).visited)))
                  else some none) else none
            | none => none
          else none
        ((why, walked) : Option (String × Option (Nat × List HeapKnowledge.IndexAtom)) ×
          Option (Option (Array SinglePass.VisitRecord × Nat)))
      | .error _ => (none, none))
    (fun (res : Option (String × Option (Nat × List HeapKnowledge.IndexAtom)) ×
          Option (Option (Array SinglePass.VisitRecord × Nat))) => res.1)
    (fun (g : FilePlans) gv w => g.inferredNextAll fuel false [] gv i w)
    (4 * heads + 3) f given [] 0 0
  SinglePass.work "propose: member interface" (f.fr.workItem i) fun _ =>
    match s.last.2 with
    -- (the last run's walk with no bound refused: the walk `interface`
    -- would make is that walk, so the pass establishes nothing)
    | some none => none
    | some (some (gs, v)) => interface s.state fuel i s.given (some gs) v
    | none => interface s.state fuel i s.given none 0

/-- The search depth of a proposal's runs: the pipeline's
(`pipeline/verify-source.mts`, `searchDepth`), which every check is given. -/
def proposalDepth : Nat := 12

/-! ## The fold over a file's functions -/

/-- What the functions of a file read of each other while proposed: the
summary of a function's written closed footprint and throw bound where it
states one without regions (`ClassSummary.ofFormat`), `top` where it states
one with regions. This is the reading of a statement the claims document
gives the function (`fragmentClaims`, a footprint and a throw flag, which
`RequestJson.statedWithin` compares with the statement), and changes with
that document's format. -/
def written (f : Fragment.Fn) : Option SourceElaboration.ClassSummary :=
  f.stated.map fun s => if s.regions.isEmpty then .ofFormat s.closed s.onThrow else .ofFormat .top false

/-- **The inputs a proposal's runs read, digested**: of each member of
member `j`'s group in the plans `fp` the proposal planned, its name and
position and its plan (the program, claims, result, start, inputs,
statement entries' candidates and cuts, assertions, entry facts, the code
requests' goals, its declared footprint, throw bound, freshness, spine
regions, postcondition, stated effect, asyncness and qualification, and a
framed plan's document, `framedDocument`), and
the reads `reads` gives the functions the group reaches (their signatures
in the store): `settledInterface fp proposalDepth j` reads these alone. -/
def inputDigest (fp : FilePlans) (j : Nat) (reads : List StandIn) : UInt64 :=
  let reached := (((fp.fr.group j).flatMap fp.fr.reach).filterMap fun k =>
    (fp.fr.units[k]?).map (·.1.name)).eraseDups
  let read := (reads.filter (reached.contains ·.name)).map fun s =>
    (s.name, reprStr s.summary, reprStr s.resultFootprint)
  let members := (fp.fr.group j).map fun k =>
    let unit := (fp.fr.units[k]?).map fun (g, _, c) => (g.name, g.namePos, c.isSome)
    match fp.plans[k]? with
    | some (.ok p) =>
      let r := p.parts.2.2
      [hash (reprStr unit), hash (match p with | .graph .. => 0 | .framed .. => 1), hash (toJson r.program).compress, hash (r.claims.map fun c => (c.context, c.type)),
        hash r.result, hash r.start, hash r.inputs, hash (toJson r.candidates).compress, hash r.cuts,
        hash (reprStr r.assertions), hash (toJson r.entryIndices).compress, hash (reprStr (r.codes.map (·.entry.goal))),
        hash (reprStr (r.footprint, r.onThrow, r.fresh, r.regional, r.async, r.qualification.isSome)),
        hash (reprStr r.ensures), hash (reprStr r.stated), hash (reprStr r.promise),
        hash (match p with
          | .graph .. => ""
          | .framed _ _ _ spec => (framedDocument spec.C spec.entries spec.theta spec.psi spec.framed).compress)].foldl mixHash 11
    | some (.error e) => mixHash (hash (reprStr unit)) (hash e)
    | none => hash (reprStr unit)
  mixHash (hash (reprStr read)) (members.foldl mixHash (hash proposalDepth))

/-- **One function's proposal by the pass** (function `i`, of name and
position `f`): its member planned by `planOf` with each function `found`
names at its proposal, every other at `prior`'s, else at its written
effect, else `top`; a member of its own group (a cycle of two or more
functions) at its written effect or `top` whatever was found of it, so
the proposal is a function of the function and of the proposals of the
functions it reaches outside its group; its interface from its own steps
(`settledInterface`); the functions `controls` names at their stand-ins.
A written effect's footprint and throw bound are kept whole (their summary,
`ClassSummary.ofFormat`), its steps proposing its returned function's
footprint. A self-recursive function's own reads are found by a **bounded
search** of at most 25 rounds: a summary read, first both exits keeping
everything, joined exit by exit with what the steps establish
(`ClassSummary.choice`) until each exit they establish is within the one
read (`ClassSummary.within`); none where no round of the 25 stops. That 25
rounds suffice is argued, not proved: a round that does not stop raises a
component of an exit's bound, at most 4 times for each of the 3 components
of the 2 exits. The round that stops proposes the summary read; the
function's own unit checks it.
`memo` keys each run by its inputs, both exits of each summary read
included (`inputDigest`). None where the pass
establishes nothing of it (callers read it at its written effect or `top`).
With `results` (`--force-proposals`, the adversarial proposal), each returned
function's footprint keep/keep. -/
def proposeOne (fr : Front) (controls : List String) (force : List String) (prior : List StandIn)
    (found : List StandIn) (planOf : List StandIn → String → Except String FilePlans) (i : Nat) (f : Fragment.Fn)
    (memo : ProposalMemo) : Option StandIn × ProposalMemo :=
  let cycle := (fr.group i).filterMap fun j => match fr.units[j]? with
    | some (g, _, none) => if j != i && (fr.group i).length > 1 then some g.name else none
    | _ => none
  let declared : List (String × Option SourceElaboration.ClassSummary) := fr.units.filterMap fun (g, _, c) =>
    if c.isNone && !controls.contains g.name then some (g.name, written g) else none
  let reads := fun (own : Option StandIn) => (found.filter (!cycle.contains ·.name)) ++ declared.filterMap fun (nm, w) =>
    if nm == f.name then own
    else if !cycle.contains nm && found.any (·.name == nm) then none
    else match (if cycle.contains nm then none else prior.find? (·.name == nm)), w with
      | some p, _ => some p
      | none, some S => some { name := nm, summary := S }
      | none, none => some { name := nm }
  -- What the member's runs establish at its reads (`settledInterface`),
  -- read from `memo` where a proposal planned the same inputs
  -- (`inputDigest`), a refusal (`none`) included.
  let establish := fun (own : Option StandIn) (memo : ProposalMemo) =>
      SinglePass.work "propose: establish" (fr.nameItem f.name) fun _ =>
    match planOf (reads own) f.name with
    | .error _ => ((none : Option Established), memo)
    | .ok fp =>
      match (List.range fp.fr.units.length).find? fun j => match fp.fr.units[j]? with
        | some (g, _, none) => g.name == f.name && g.namePos == f.namePos
        | _ => false with
      | none => (none, memo)
      | some j =>
        let key := inputDigest fp j (reads own)
        match memo.get? key with
        | some got => (got.map fun (S, R, v) => ⟨S, R, v⟩, memo)
        | none =>
          let got := settledInterface fp proposalDepth j
          (got, memo.insert key (got.map fun e => (e.summary, e.result, e.visits)))
  let (r, memo) : Option Established × ProposalMemo := if let some S := written f then
      let (got, memo) := establish (some { name := f.name, summary := S }) memo
      (got.map fun got => { got with summary := S }, memo)
    else if (fr.mentions i).contains f.name then Id.run do
      -- A recursion assumption, per exit, found by a bounded search: first
      -- both exits keeping everything; kept where each exit of what the
      -- body establishes entails the assumption's (`ClassSummary.within`,
      -- `ClassSummary.within_weakens`), else widened to the join
      -- (`ClassSummary.choice`, `ClassSummary.within_choice`); none after
      -- 25 rounds that do not stop. (Argued, not proved: a round that does
      -- not stop raises a component of an exit's bound, at most 4 raises
      -- for each of the 3 components of the 2 exits.)
      let mut assumed : SourceElaboration.ClassSummary := .ofFormat keepAll true
      let mut memo := memo
      for _ in List.range 25 do
        let (got, memo') := establish (some { name := f.name, summary := assumed }) memo
        memo := memo'
        match got with
        | none => return (none, memo)
        | some got =>
          if got.summary.within assumed then
            return (some { got with summary := assumed }, memo)
          assumed := assumed.choice got.summary
      return (none, memo)
    else establish none memo
  (r.map fun got =>
    let R := if force.contains "results" then keepAll else got.result
    let R := if (resultWithFootprint fr.d.types f.ret R).isOk then R else .top
    { name := f.name, summary := got.summary, resultFootprint := R },
    memo)

/-- The functions a wanted unit reaches, callees first: each after every
function it reaches outside its group (a depth-first walk of `Front.edges`). -/
def calleesFirst (fr : Front) (wanted : List Nat) : List Nat := Id.run do
  let mut order : List Nat := []
  let mut seen : Std.HashSet Nat := {}
  let mut stack : List (Nat × Bool) := wanted.reverse.map (·, false)
  for _ in List.range (4 * fr.units.length * (fr.units.length + 1) + 4) do
    match stack with
    | [] => break
    | (i, true) :: rest => stack := rest; order := order ++ [i]
    | (i, false) :: rest =>
      if seen.contains i then stack := rest
      else
        seen := seen.insert i
        stack := (fr.edges i).filter (!seen.contains ·) |>.map (·, false) |>.append ((i, true) :: rest)
  return order

/-- **The declarations' proposals by the pass**: each function a wanted
unit reaches, callees first (`calleesFirst`; async functions `top` by the
language, stand-ins at their controls' footprints), proposed by
`proposeOne`; a function `known` names taken as known (`none`: nothing
proposed, read at its written effect or `top`). Every function proposed
and known, with its proposal. -/
def proposalsOf (fr : Front) (wanted : List Nat) (standIns : StandIns) (force : List String) (prior : List StandIn)
    (planOf : List StandIn → String → Except String FilePlans) (known : List (String × Option StandIn) := [])
    (memo : ProposalMemo := {}) : List (String × Option StandIn) × ProposalMemo := Id.run do
  let controls := standIns.functions.map (·.name)
  let mut out : List (String × Option StandIn) := []
  let mut memo := memo
  for i in calleesFirst fr wanted do
    let some (f, _, none) := fr.units[i]? | continue
    if f.async || controls.contains f.name || out.any (·.1 == f.name) then continue
    if let some (_, k) := known.find? (·.1 == f.name) then
      out := out ++ [(f.name, k)]
      continue
    let found := out.filterMap (·.2)
    let (got, memo') := proposeOne fr controls force prior found planOf i f memo
    memo := memo'
    out := out ++ [(f.name, got)]
  return (out, memo)

/-- The proposals that state more than the ordinary effect
(`proposalsOf`), and the memo of what was established. -/
def proposals (fr : Front) (wanted : List Nat) (standIns : StandIns) (force : List String) (prior : List StandIn)
    (planOf : List StandIn → String → Except String FilePlans) (known : List (String × Option StandIn) := [])
    (memo : ProposalMemo := {}) : List StandIn × ProposalMemo :=
  let (out, memo) := proposalsOf fr wanted standIns force prior planOf known memo
  (out.filterMap (·.2) |>.filter fun s => s.footprint != .top || s.resultFootprint != .top, memo)

end PassProposals

end Verification.SourceClaimJson
