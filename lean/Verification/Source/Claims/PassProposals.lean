import Verification.Source.Claims.MemberSettle

/-! **Proposals by the pass** ([proposals by the pass](../../../../docs/drafts/proposals-by-the-pass.md)):
what the front proposes about a body's unwritten effect is computed with
the pass's own steps on that body. A function's unwritten footprint and
throw bound are the join of its checked steps' local effects, each step's
local effect the least closed footprint its check accepts on one of the two
routes the pass checks a footprint by: the direct node-by-node check
(`SinglePass.footprintCheck`), and the regional fallback, whose
alternatives (`ArgumentRegionGraph.stepEffects`' kinds) are rebased to the
entry through the regional facts (`rebaseAll`) and read in the closed
language. The returned function's footprint is read off the returned
value's checked type. A proposal decides nothing: the function's own unit
checks it, and its callers read it. -/
namespace Verification.SourceClaimJson

/-- A written-footprint stand-in: the footprint a function or an import would
state if written, supplied apart from the source. The command line
supplies none. -/
structure StandIn where
  name : String
  footprint : Footprints.Closed
  onThrow : Bool := false
  resultFootprint : Footprints.Closed := .top

/-- The stand-ins of a file: for the file's functions and for its imports. -/
structure StandIns where
  functions : List StandIn := []
  imports : List StandIn := []

namespace PassProposals
open Lean ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open SourceExtraction LabelStore RequestJson
open HeapKnowledge (Knowledge)

abbrev Closed := Verification.Footprints.Closed

/-! ## The closed lattice -/

/-- Every closed footprint, in an order extending the components' rank
order: a footprint comes after every footprint below it. -/
def ascending : List Closed :=
  let cs := [Footprints.Change.keep, .init, .scalar, .grow, .any]
  ((cs.flatMap fun v => cs.map fun s => (⟨v, s⟩ : Closed)).mergeSort fun a b =>
    a.value.rank + a.store.rank ≤ b.value.rank + b.store.rank)

def keepAll : Closed := ⟨.keep, .keep⟩

/-- The join: each component's larger change, an upper bound in `Closed.le`
and in the order `Footprint.le` reads changes in. -/
def join (a b : Closed) : Closed := ⟨a.value.max b.value, a.store.max b.store⟩

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
its evidence: the least closed footprint the step's check accepts there. The
direct check's disjuncts are each a rule's own grade below the bound and a
side condition the bound does not enter (an inspection, a typed write, an
initializing write, a call at its selected signature, an unreachable
type), so the footprints it accepts are those above the least of them. -/

/-- A step's local effects on the direct route, read from its grades
(`SinglePass.stepGrades`, the footprint check at any bound,
`SinglePass.footprintCheck_eq_admits`): where no live handler catches its
throw and the bound states no throw bound (`normal`), where a live handler
catches it (`handled`), and where the bound bounds every throw (`raised`);
none where no bound admits it. -/
structure Direct where
  normal : Option Closed
  handled : Option Closed
  raised : Option Closed

def direct (g : SinglePass.StepGrades) (k : Continuation) : Direct :=
  let at_ := fun (live exc : Bool) => leastAccepted fun Φ => g.admits Φ live exc false false k
  { normal := at_ false false, handled := at_ true false, raised := at_ false true }

/-- A step's local effect on the regional route, its throw bounded where
`thr`: the least of its alternatives, each rebased to the entry through the
regional facts `rs` and read in the closed language (`ofFrame`): the closed
check (`checkClosedNode`), a call's frame (`callStep`), an element write's
frame (`writeStep`). -/
def regional (G : NormalGraph ι) (images : InstanceImageCheck G) (sums : List (ReadSummary ι))
    (rs : SinglePass.RegionState) (cEv : NodeEvidence ι) (t : Tm) (thr : Bool) : Option Closed :=
  let closed := leastAccepted fun Φ => GraphCode.ArgumentRegionGraph.checkClosedNode G images sums Φ cEv t thr
  let rebased := fun (se : GraphCode.ArgumentRegionGraph.StepEffect) =>
    let ev := GraphCode.ArgumentRegionGraph.nodeRebase [] rs.facts rs.values rs.fields se
    let n := ofFrame (Footprints.rebaseAll ev se.normal)
    if thr then joinOpt n (ofFrame (Footprints.rebaseAll ev se.raised)) else n
  let call := (GraphCode.ArgumentRegionGraph.callStep G images sums cEv t thr).bind rebased
  let write := (ExpressionEffects.writeStep G (ControlFlow.entry cEv) t).bind fun i =>
    rebased (GraphCode.ArgumentRegionGraph.writeStepEffect i)
  ascending.find? fun Φ => [closed, call, write].any fun a => a.any (·.le Φ)

end

/-! ## A member's interface -/

/-- What a member's own steps establish of its interface: its footprint, its
throw bound, the footprint of the function it returns, and the transfers
its two runs visited. -/
structure Established where
  footprint : Closed
  onThrow : Bool
  result : Closed
  visits : Nat

/-- The labels of a file's plans. -/
abbrev Label (f : FilePlans) : Type := EquationStore.CheckedLabel f.F.equations f.F.primitive

/-- What the direct route reads of a member's visited steps (`directRead`):
the join of their local effects on normal return, outside the region from
which no normal return is possible (none where a step of that region is not
`deadNode`), and on a throw; the returned values' functions' footprint, and
whether any return was visited. -/
structure DirectRead where
  normal : Option Closed
  thrown : Option Closed
  result : Closed
  returns : Bool

section
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **The direct route's footprint of a member** from each visited step's
local effect (`grades`, `SinglePass.walkGrades`): the join over the steps
outside the region with no normal return (`deadRegion`), each at its live
handler; the throws' join; at each return the returned value's checked
type's footprint (the join of its signatures', `top` for a value of no
function type). -/
def directRead (G : NormalGraph ι) (nodes : Array Node) (claimed : Array (PointClaim ι))
    (grades : Array (Option SinglePass.StepGrades)) : DirectRead := Id.run do
  let n := nodes.size
  let dead := GraphCode.deadIterate ((nodes.zip claimed).map fun (node, c) => (node, ExpressionEffects.emptyType G c.type))
    (n + 1) (Array.replicate n true)
  let mut normal : Option Closed := some keepAll
  let mut thrown : Option Closed := some keepAll
  let mut result : Closed := keepAll
  let mut returns := false
  for l in List.range n do
    let some (some g) := grades[l]? | continue
    let node := nodes[l]!
    let c := claimed[l]!
    let d := direct g node.continuation
    thrown := joinOpt thrown d.raised
    if dead.getD l false then
      if !GraphCode.deadNode G dead.toList node (SinglePass.deadEvidence c node) then normal := none
    else
      let live := match node.handler with
        | some t => !dead.getD t.label false
        | none => false
      normal := joinOpt normal (if live then d.handled else d.normal)
      if node.continuation == .ret then
        returns := true
        let T := match node.expression with
          | .var j => (c.context[j]?).getD c.type
          | _ => c.type
        result := join result (match PositiveRules.expand G T with
          | [.arrs L S] => if L.isEmpty && S.isEmpty then .top else
            ((L.map (·.effect)) ++ S.map (·.effect)).foldl (init := keepAll) fun acc e => join acc e.footprint
          | _ => .top)
  return ⟨normal, thrown, result, returns⟩

end

/-- **A member's interface from its own steps**, given its plans and given
lines settled with its footprint open (`settledInterface`) and, where its
last settling run was the walk with no bound, that run's steps' local
effects (`grades`): the direct route's footprint from them
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
    (grades : Option (Array (Option SinglePass.StepGrades))) (visitsA : Nat) : Option Established := Id.run do
  let G : NormalGraph (Label f) := StoreView.graph f.F.store
  let I : PositiveCertificates.InstanceImageCheck G := StoreView.images f.F.store
  let answers : CertificateProducer.Answered G := {}
  let some (.ok plan) := f.plans[i]? | return none
  let .ok (.graph _ _ r) := plan.certify | return none
  if r.qualification.isSome || r.async then return some ⟨.top, false, .top, 0⟩
  let nodes := r.program.toArray
  let claimed := r.claims.toArray
  let n := nodes.size
  -- The walk the regional route (and, with no grades, the direct route)
  -- runs: the code requests run first, as `passMember` checks them.
  let prepared : Unit → Option ((Option SinglePass.Regional →
      Except (SinglePass.WalkStop (Label f) G) (SinglePass.WalkState (Label f) G × Nat)) × (CodeEntry (Label f) → Bool)) := fun _ => do
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
      let conditions := decide (q.entry.arity ≤ q.entry.row.arguments.length) && eff.below q.entry.arity &&
        !eff.freshObject && eff.requires.isNone && eff.elements.isNone && !eff.receiverGrows && eff.elementWrite.isNone
      if !conditions || !RequestJson.asyncEffects q.async eff.footprint then
        ({ index := ci, outcome := .refused s!"code {ci}", answers := sumsAnswers, line := "" } : CodeRun _ _)
      else
      let codeBound := if eff.footprint == .top && !eff.fresh && !eff.onThrow then none
        else if !eff.fresh && q.entry.exprs.all Purity.pureTerm then none
        else some (eff.footprint, eff.fresh, eff.onThrow)
      let codePool := CertificateProducer.vocabulary G labels rq.claims rq.inputs
      let codeGiven : GivenHeads _ := match line with
        | some l => match (l.getObjVal? "codes").bind fun cs => do
            let arr ← cs.getArr?
            GivenHeads.fromJson rq.program.length ((arr[ci]?).getD (Json.arr #[])) with
          | Except.ok g => g
          | Except.error _ => {}
        | none => {}
      let (o, _, a, _) := SinglePass.run G I codePool fuel rq.program rq.claims rq.start rq.inputs q.entry.goal
        hints.requirements hints.cuts hints.candidates rq.entryIndices [] (e ++ rendered) (GraphCode.admits table)
        r.aliases .ordinary sumsAnswers #[] 1000000000 codeBound codeGiven.implies codeGiven.args
      { index := ci, outcome := o.asRefusal, answers := a, line := "" }
    let (codeRuns, table, sumsAnswers) := codesInOrder (·.1.entry) codeStep [] next r.codes.zipIdx
    if codeRuns.any fun c => !(c.outcome matches .accepted) then none
    let codes := GraphCode.admits table
    pure (fun (rg : Option SinglePass.Regional) =>
      SinglePass.work "propose: member run" (f.fr.workItem i) fun _ =>
      SinglePass.runWalk G I pool fuel r.program r.claims r.start r.inputs r.goal r.assertions r.cuts r.candidates
        r.entryIndices [] (e ++ rendered) codes r.aliases .ordinary sumsAnswers #[] 1000000000 none
        main.implies main.args r.ensures main.inputs r.entrySeparation none false false rg, codes)
  -- The direct route: the settling run's steps, else a walk with no bound.
  let (read, visits) ← match grades with
    | some gs => pure (directRead G nodes claimed gs, visitsA)
    | none =>
      let some (walk, codes) := prepared () | return none
      let .ok (σ, reach) := walk none | return none
      if σ.walk.visited < reach then return none
      pure (directRead G nodes claimed (SinglePass.walkGrades G I codes r.program r.claims σ), σ.walk.visited)
  let normal := read.normal
  let thrown := read.thrown
  -- The regional route: the walk under the regional fallback at `top`, run
  -- where the direct route's footprint is more than keep/keep (no footprint
  -- is below it).
  let (regionalΦ, regionalThrown, visitsB) := if normal == some keepAll then (none, none, 0) else
    match prepared () with
    | none => (none, none, 0)
    | some (walk, _) =>
    let tables := regionalInferred r .top [] none
    let (names, heads) := (regionalFromJson r.program.length tables).toOption.getD ([], #[])
    let rgTop : SinglePass.Regional := { Φ := .top, regions := [], exc := false, names, heads }
    match walk (some rgTop) with
    | .ok (σB, reachB) =>
      if σB.walk.visited < reachB then (none, none, σB.walk.visited) else
      let sumsB := σB.answers.summaries.toList
      let joined := fun (exc : Bool) => (List.range n).foldl (init := (some keepAll : Option Closed)) fun acc l =>
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
            let kHere := (SinglePass.materialize entry width (List.range width) true).1
            let cEv : NodeEvidence _ := ⟨ordinaryEv, some ⟨c.context, node.expression, c.type⟩, [],
              SinglePass.regionalFacts kHere st.stepK, st.stepEffect, {}, none, [], [], [], none⟩
            joinOpt acc (regional G I sumsB rs cEv node.expression (node.handler.isSome || exc))
          | _, _, _, _ => acc
        | none => acc
      (joined false, joined true, σB.walk.visited)
    | .error _ => (none, none, 0)
  let within := fun (Φ : Option Closed) (T : Option Closed) => match Φ, T with
    | some a, some b => b.le a && a != Footprints.Closed.top
    | _, _ => false
  let (Φ, ot) := match normal, regionalΦ with
    | some a, some b => if b.le a && !a.le b then (b, within regionalΦ regionalThrown) else (a, within normal thrown)
    | some a, none => (a, within normal thrown)
    | none, some b => (b, within regionalΦ regionalThrown)
    | none, none => (.top, false)
  return some ⟨Φ, ot, if read.returns then read.result else .top, visits + visitsB⟩

/-- A plan's request at `top` with no throw bound: its walk unbounded. -/
def openAt (f : FilePlans) (i : Nat) : FilePlans :=
  { f with plans := f.plans.zipIdx.map fun (p, j) => if j != i then p else p.map fun
    | .graph name pos r => .graph name pos { r with footprint := .top, onThrow := false } }

/-- Whether member `i`'s plan runs its main graph with no bound when open
(`passMember`'s `bounded`): no fresh result stated. -/
def openUnbounded (f : FilePlans) (i : Nat) : Bool :=
  match f.plans[i]? with
  | some (.ok (.graph _ _ r)) => !r.fresh && r.regional.isNone
  | _ => false

/-- Member `i`'s plans and given lines settled with its footprint open, as
`passGroupMode8` settles them (`inferredSettle`'s runs and next states),
each run reporting its steps' local effects (`passMember`'s `grading`),
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
    (fun (g : FilePlans) gv => SinglePass.work "check: member run" (f.fr.workItem i) fun _ =>
      match g.passMember fuel i false 1000000000 1 gv none false true with
      | .ok m =>
        let why : Option (String × Option (Nat × List HeapKnowledge.IndexAtom)) := match m.outcome with
          | .refused w lacks => some (w, lacks)
          | _ => none
        let grades : Option (Array (Option SinglePass.StepGrades) × Nat) :=
          if m.accepted && openUnbounded g i then match m.main with
            | some mr => if mr.route matches FootprintRoute.direct then
                some ((MainRun.counts mr).grades, (MainRun.counts mr).visited) else none
            | none => none
          else none
        ((why, grades.filter (!·.1.isEmpty)) : Option (String × Option (Nat × List HeapKnowledge.IndexAtom)) ×
          Option (Array (Option SinglePass.StepGrades) × Nat))
      | .error _ => (none, none))
    (fun (res : Option (String × Option (Nat × List HeapKnowledge.IndexAtom)) ×
          Option (Array (Option SinglePass.StepGrades) × Nat)) => res.1)
    (fun (g : FilePlans) gv w => g.inferredNextAll fuel false [] gv i w)
    (4 * heads + 3) f given [] 0 0
  SinglePass.work "propose: member interface" (f.fr.workItem i) fun _ =>
    interface s.state fuel i s.given (s.last.2.map (·.1)) ((s.last.2.map (·.2)).getD 0)

/-- The search depth of a proposal's runs: the pipeline's
(`pipeline/verify-source.mts`, `searchDepth`), which every check is given. -/
def proposalDepth : Nat := 12

/-! ## The fold over a file's functions -/

/-- What the functions of a file read of each other while proposed: a
function's written effect where it states one without regions, `top` where
it states one with regions. -/
def written (f : Fragment.Fn) : Option (Closed × Bool) :=
  f.stated.map fun s => if s.regions.isEmpty then ((s.closed, s.onThrow) : Closed × Bool) else (.top, false)

/-- **One function's proposal by the pass** (function `i`, of name and
position `f`): its member planned by `planOf` with each function `found`
names at its proposal, every other at `prior`'s, else at its written
effect, else `top`; a member of its own group (a cycle of two or more
functions) at its written effect or `top` whatever was found of it, so
the proposal is a function of the function and of the proposals of the
functions it reaches outside its group; its interface from its own steps
(`settledInterface`); the functions `controls` names at their stand-ins.
A written effect's footprint and throw bound are kept whole, its steps proposing its returned function's footprint. A
self-recursive function's own reads start at keep/keep with its throws
bounded and are joined with what its steps establish until they establish
no more, at most once per step of the lattice's height. None where the pass
establishes nothing of it (callers read it at its written effect or `top`).
With `results` (`TSCERT_FORCE`, the adversarial proposal), each returned
function's footprint keep/keep. -/
def proposeOne (fr : Front) (controls : List String) (force : List String) (prior : List StandIn)
    (found : List StandIn) (planOf : List StandIn → String → Except String FilePlans) (i : Nat) (f : Fragment.Fn) :
    Option StandIn :=
  let cycle := (fr.group i).filterMap fun j => match fr.units[j]? with
    | some (g, _, none) => if j != i && (fr.group i).length > 1 then some g.name else none
    | _ => none
  let declared : List (String × Option (Closed × Bool)) := fr.units.filterMap fun (g, _, c) =>
    if c.isNone && !controls.contains g.name then some (g.name, written g) else none
  let reads := fun (own : Option StandIn) => (found.filter (!cycle.contains ·.name)) ++ declared.filterMap fun (nm, w) =>
    if nm == f.name then own
    else if !cycle.contains nm && found.any (·.name == nm) then none
    else match (if cycle.contains nm then none else prior.find? (·.name == nm)), w with
      | some p, _ => some p
      | none, some (Φ, ot) => some { name := nm, footprint := Φ, onThrow := ot }
      | none, none => some { name := nm, footprint := .top }
  let establish := fun (own : Option StandIn) => (do
    let fp ← (planOf (reads own) f.name).toOption
    let j ← (List.range fp.fr.units.length).find? fun j => match fp.fr.units[j]? with
      | some (g, _, none) => g.name == f.name && g.namePos == f.namePos
      | _ => false
    settledInterface fp proposalDepth j : Option Established)
  let r : Option Established := if let some (Φ, ot) := written f then
      (establish (some { name := f.name, footprint := Φ, onThrow := ot })).map fun got => { got with footprint := Φ, onThrow := ot }
    else if (fr.mentions i).contains f.name then Id.run do
      let mut assumed : Closed × Bool := (keepAll, true)
      for _ in List.range 8 do
        match establish (some { name := f.name, footprint := assumed.1, onThrow := assumed.2 }) with
        | none => return none
        | some got =>
          if got.footprint.le assumed.1 && (got.onThrow || !assumed.2) then
            return some { got with footprint := assumed.1, onThrow := assumed.2 }
          assumed := (join assumed.1 got.footprint, assumed.2 && got.onThrow)
      return none
    else establish none
  r.map fun got =>
    let R := if force.contains "results" then keepAll else got.result
    let R := if (resultWithFootprint fr.d.types f.ret R).isOk then R else .top
    { name := f.name, footprint := got.footprint, onThrow := got.onThrow && got.footprint != .top, resultFootprint := R }

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
    (planOf : List StandIn → String → Except String FilePlans) (known : List (String × Option StandIn) := []) :
    List (String × Option StandIn) := Id.run do
  let controls := standIns.functions.map (·.name)
  let mut out : List (String × Option StandIn) := []
  for i in calleesFirst fr wanted do
    let some (f, _, none) := fr.units[i]? | continue
    if f.async || controls.contains f.name || out.any (·.1 == f.name) then continue
    if let some (_, k) := known.find? (·.1 == f.name) then
      out := out ++ [(f.name, k)]
      continue
    let found := out.filterMap (·.2)
    out := out ++ [(f.name, proposeOne fr controls force prior found planOf i f)]
  return out

/-- The proposals that state more than the ordinary effect
(`proposalsOf`). -/
def proposals (fr : Front) (wanted : List Nat) (standIns : StandIns) (force : List String) (prior : List StandIn)
    (planOf : List StandIn → String → Except String FilePlans) (known : List (String × Option StandIn) := []) :
    List StandIn :=
  (proposalsOf fr wanted standIns force prior planOf known).filterMap (·.2) |>.filter fun s =>
    s.footprint != .top || s.resultFootprint != .top

end PassProposals

end Verification.SourceClaimJson
