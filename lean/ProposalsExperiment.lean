/- MEASUREMENT, NOT PART OF THE VERIFIER: the feasibility experiment of
docs/drafts/proposals-by-the-pass.md, section 8. A separate executable
(`proposals-experiment`), so the verifier's command line and its verdicts are
untouched. Over a stage-8 input (a fragment and its interfaces) it computes
each function's unwritten interface from the pass's own steps, compares it with
today's walk proposal, checks it with the ordinary member run (the oracle), and
runs the whole file with every function read at its inferred interface
(generic and rest functions included). Its commit can be dropped. -/
import Verification.Source.RequestCli

namespace Verification.ProposalsExperiment
open Lean ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open SourceClaimJson RequestJson SourceExtraction LabelStore
open Footprints (Change)
abbrev FC := Verification.Footprints.Closed
open HeapKnowledge (Knowledge)

/-! ## The closed lattice -/

/-- Every closed footprint, as the wire may state it. -/
def allClosed : List FC :=
  [Change.keep, .init, .scalar, .grow, .any].flatMap fun v => [Change.keep, .init, .scalar, .grow, .any].map fun s => ⟨v, s⟩

def bot : FC := ⟨.keep, .keep⟩

/-- The join: each component's larger change (rank order), which is an upper
bound in `Closed.le` and in the raw order `Footprint.le` reads. -/
def cjoin (a b : FC) : FC := ⟨a.value.max b.value, a.store.max b.store⟩

def ojoin : Option FC → Option FC → Option FC
  | some a, some b => some (cjoin a b)
  | _, _ => none

/-- The least of a list by `Closed.le`, where one is below every other; else
the first minimal one and `false`. -/
def least (xs : List (FC × String)) : Option ((FC × String) × Bool) :=
  let minimal := xs.filter fun x => !xs.any fun y => y.1.le x.1 && !x.1.le y.1
  match minimal with
  | [] => none
  | m :: _ => some (m, minimal.all fun y => y.1.le m.1 && m.1.le y.1)

def showC (c : FC) : String := s!"{(toJson c).compress}"

/-- The interface language's reading of a frame: the least closed footprint
`c` (by `Closed.le`, among the raw ones) whose frame includes it, as
`stepWithin` reads inclusion. -/
def alpha (fp : Footprints.Footprint) : Option FC :=
  (least (allClosed.filter (fun c => Footprints.Footprint.le GraphCode.ArgumentRegionGraph.noClasses (c.fp ++ fp) c.fp)
    |>.map (·, ""))).map (·.1.1)

section
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-! ## A step's local effect, read from its evidence

Every disjunct of the closed checks (`SinglePass.footprintCheck`,
`ArgumentRegionGraph.checkClosedNode`) is a rule's own grade below the bound
and a side condition: an inspection or an unreachable type keeps everything,
a typed field write `⟨any, keep⟩`, an element write `⟨any, keep⟩` or
`⟨any, grow⟩`, an element write at a run-time index `⟨any, grow⟩`, an
initializing write `⟨init, keep⟩`, a call its selected signature's footprint
(with its receiver's own change, or `top` where it excepts its receiver's
store and the receiver is not fresh). The step's grades are those, closed
under join; its local effect is the least of them the step's check accepts. -/

/-- The rule grades of a step, from its term and its derivation's selected
signature, with the rule's name; closed under join. -/
def grades (t : Tm) (deriv : ProgramCertificates.Evidence ι) (F : List Nat) : List (FC × String) :=
  let base : List (FC × String) :=
    [(bot, "inspection or unreachable"), (⟨.init, .keep⟩, "initializing write"), (⟨.any, .keep⟩, "field or element write"),
      (⟨.any, .grow⟩, "element write, growing")] ++
    (match ExpressionEffects.selectedEffect deriv with
      | some eff =>
        let extra := if eff.receiverOwn then eff.ownChange
          else if eff.receiverStore && !GraphCode.receiverFresh F (ProgramCertificates.claim deriv).term then .top else bot
        [(cjoin eff.footprint extra, "call at its selected signature")]
      | none => [])
  let _ := t
  (base ++ base.flatMap fun a => base.map fun b => (cjoin a.1 b.1, s!"{a.2} + {b.2}"))

/-- Which rule decides: the rule whose check holds at the least accepted grade. -/
def directRule (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (g : FC) (F : List Nat) (c : PointClaim ι) (node : Node) (stepK : Knowledge)
    (deriv : ProgramCertificates.Evidence ι) : String :=
  let t := node.expression
  if ExpressionEffects.check G c.context t then "inspection"
  else if ExpressionEffects.emptyType G c.type || c.context.any (ExpressionEffects.emptyType G ·) then "unreachable"
  else if ExpressionEffects.writeWithin G c.context g t then "typed write"
  else if ExpressionEffects.initWriteWithin G c.context stepK g t then "initializing write"
  else if GraphCode.selectedWithinAt g F deriv && SinglePass.derivChecked G images codes sums c node stepK deriv then
    "call at its selected signature"
  else "none"

/-- The step evidence's kind, for the tally of question (a). -/
def evidenceKind (st : SinglePass.Stepped ι) : String :=
  if st.copied then "copy" else match st.stepEffect with
  | none => "none"
  | some (.ordinary _) => "ordinary"
  | some (.pure _) => "pure"
  | some (.reading _) => "reading"
  | some (.created _) => "created"
  | some (.typedRead ..) => "typedRead"
  | some (.observedRead ..) => "observedRead"
  | some (.slicedRead ..) => "slicedRead"
  | some (.knownValue ..) => "knownValue"
  | some (.linkedRead ..) => "linkedRead"
  | some (.allocated _) => "allocated"
  | some (.written ..) => "written"
  | some (.boundedWrite ..) => "boundedWrite"

/-- One label's local effects on the direct route: on normal return with no
live handler (`normal`), where a live handler catches its throw
(`handled`), where every throw is bounded (`raised`); none where no grade of
the step is accepted. -/
structure DirectNode where
  normal : Option FC
  handled : Option FC
  raised : Option FC
  rule : String
  unique : Bool

def directNode (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (entry : SinglePass.State)
    (st : SinglePass.Stepped ι) : DirectNode :=
  let deriv := SinglePass.derivOf c node st
  let F := SinglePass.recvFresh node entry
  let gs := grades node.expression deriv F
  let at_ := fun (live exc : Bool) => least (gs.filter fun (g, _) =>
    SinglePass.footprintCheck G images codes sums g F c node st.stepK deriv live exc false false)
  let n := at_ false false
  { normal := n.map (·.1.1), handled := (at_ true false).map (·.1.1), raised := (at_ false true).map (·.1.1),
    rule := match n with
      | some ((g, _), _) => directRule G images codes sums g F c node st.stepK deriv
      | none => "none",
    unique := n.all (·.2) }

/-- One label's local effect on the regional route, where its throw is
bounded (`thr`): the least of its alternatives (`stepEffects`' kinds) each
rebased to the entry through the regional facts and read in the closed
language (`alpha`): the closed check at the step's grades, a call's frame,
an element write's frame. -/
def regionalNode (G : NormalGraph ι) (images : InstanceImageCheck G) (sums : List (ReadSummary ι))
    (gs : List (FC × String)) (rs : SinglePass.RegionState) (cEv : NodeEvidence ι) (t : Tm) (thr : Bool) :
    Option ((FC × String) × Bool) :=
  let closed := (least (gs.filter fun (g, _) => GraphCode.ArgumentRegionGraph.checkClosedNode G images sums g cEv t thr)).map
    fun ((g, _), _) => (g, "closed check")
  let rebased := fun (se : GraphCode.ArgumentRegionGraph.StepEffect) =>
    let ev := GraphCode.ArgumentRegionGraph.nodeRebase [] rs.facts rs.values rs.fields se
    let n := alpha (Footprints.rebaseAll ev se.normal)
    if thr then ojoin n (alpha (Footprints.rebaseAll ev se.raised)) else n
  let call := (GraphCode.ArgumentRegionGraph.callStep G images sums cEv t thr).bind fun se =>
    (rebased se).map (·, "call frame")
  let write := (ExpressionEffects.writeStep G (ControlFlow.entry cEv) t).bind fun i =>
    (rebased (GraphCode.ArgumentRegionGraph.writeStepEffect i)).map (·, "element write frame")
  least ([closed, call, write].filterMap id)

end

/-! ## A member's inferred interface -/

structure Inferred where
  footprint : FC
  onThrow : Bool
  fresh : Bool
  result : FC
  route : String
  visits : Nat
  /-- Labels whose step admits no grade on the route taken, and why. -/
  open_ : List String := []
  /-- Per step: (evidence kind, deciding rule). -/
  rules : List (String × String) := []
  notUnique : Nat := 0
  /-- Labels whose regional freshness differs at the inferred bound. -/
  cellsDiffer : Nat := 0
  regionalAgain : Option FC := none
  note : String := ""

def topInferred (why : String) : Inferred :=
  { footprint := .top, onThrow := false, fresh := false, result := .top, route := why, visits := 0 }

/-- **A member's interface from the pass's own steps**: the member's code
requests as `passMember` runs them, then its graph walked with no footprint
bound (run A, the direct route) and with the regional fallback at `top`
(run B); each visited step's local effect from its evidence; their join. -/
def inferMember (f : FilePlans) (fuel : Nat) (i : Nat) (given : Option (Std.HashMap String Json)) :
    Except String Inferred := do
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := StoreView.graph f.F.store
  let I : PositiveCertificates.InstanceImageCheck G := StoreView.images f.F.store
  let answers : CertificateProducer.Answered G := {}
  let plan ← (f.plans[i]?).getD (.error s!"no unit {i}")
  let .graph _ _ r ← plan.certify
  if r.qualification.isSome then return topInferred "qualified body: top by the language"
  if r.async then return topInferred "async: top by the language"
  let labels := r.searchLabels
  let (e, next) ← ExpressionClaims.produceUsing G I labels (StoreView.valid r.types)
    (StoreView.projection r.types) fuel r.obligations { answers with summaries := #[], summaryAnswers := {} }
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
    let refuse := fun (o : SinglePass.Outcome _) => ({ index := ci, outcome := o, answers := sumsAnswers, line := "" } : CodeRun _ _)
    let hints := (r.codeHints[ci]?).getD {}
    let rq := q.asRequest r.toRequest
    let eff := q.entry.row.effect
    let conditions := decide (q.entry.arity ≤ q.entry.row.arguments.length) && eff.below q.entry.arity &&
      !eff.freshObject && eff.requires.isNone && eff.elements.isNone && !eff.receiverGrows && eff.elementWrite.isNone
    if !conditions then refuse (.refused s!"code {ci}: its signature")
    else if !RequestJson.asyncEffects q.async eff.footprint then refuse (.refused s!"code {ci}: async")
    else
    let codeBound := if eff.footprint == Footprints.Closed.top && !eff.fresh && !eff.onThrow then none
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
    let (o, _, a, _) := SinglePass.run G I codePool fuel rq.program rq.claims rq.start rq.inputs q.entry.goal hints.requirements
      hints.cuts hints.candidates rq.entryIndices [] (e ++ rendered) (GraphCode.admits table) r.aliases
      .ordinary sumsAnswers #[] 1000000000 codeBound codeGiven.implies codeGiven.args
    match o.asRefusal with
    | .accepted => { index := ci, outcome := .accepted, answers := a, line := "" }
    | o => { index := ci, outcome := o, answers := a, line := "" }
  let (codeRuns, table, sumsAnswers) := codesInOrder (·.1.entry) codeStep [] next r.codes.zipIdx
  if let some c := codeRuns.find? fun c => !(c.outcome matches .accepted) then
    throw s!"a code request: {c.outcome}"
  let codes := GraphCode.admits table
  let walk := fun (regional : Option SinglePass.Regional) =>
    SinglePass.runWalk G I pool fuel r.program r.claims r.start r.inputs r.goal r.assertions r.cuts r.candidates
      r.entryIndices [] (e ++ rendered) codes r.aliases .ordinary sumsAnswers #[] 1000000000 none
      main.implies main.args r.ensures main.inputs r.entrySeparation none false false regional
  -- Run A: no bound, no regional check.
  let (σA, _) ← match walk none with
    | .ok (σ, reach) => if σ.walk.visited < reach then throw s!"run A: {reach - σ.walk.visited} nodes not reached" else pure (σ, reach)
    | .error stop => throw s!"run A stopped: {stop.outcome.outcome}"
  let nodes := r.program.toArray
  let claimed := r.claims.toArray
  let n := nodes.size
  let sumsA := σA.answers.summaries.toList
  -- The region with no normal return, as `deadRegion` computes it under a
  -- bound stating no throw bound.
  let flags := (nodes.zip claimed).map fun (node, c) => (node, ExpressionEffects.emptyType G c.type)
  let dead := GraphCode.deadIterate flags (n + 1) (Array.replicate n true)
  let visited := (List.range n).filter fun l => (σA.walk.labels[l]?).any (·.visited)
  let mut normal : Option FC := some bot
  let mut thrown : Option FC := some bot
  let mut fresh := true
  let mut opens : List String := []
  let mut rules : List (String × String) := []
  let mut notUnique := 0
  let mut result : FC := bot
  let mut returns := 0
  for l in visited do
    let some lw := σA.walk.labels[l]? | continue
    let some entry := lw.entry | continue
    let some st := lw.stepped | continue
    let node := nodes[l]!
    let c := claimed[l]!
    let d := directNode G I codes sumsA c node entry st
    rules := rules ++ [(evidenceKind st, d.rule)]
    if !d.unique then notUnique := notUnique + 1
    let live := match node.handler with
      | some t => !dead.getD t.label false
      | none => false
    if dead.getD l false then
      if !GraphCode.deadNode G dead.toList node (SinglePass.deadEvidence c node) then
        normal := none
        opens := opens ++ [s!"{l}: no-return region"]
    else
      let g := if live then d.handled else d.normal
      if g.isNone then opens := opens ++ [s!"{l}: {(reprStr node.expression).take 80}"]
      normal := ojoin normal g
      if node.continuation == .ret then
        returns := returns + 1
        fresh := fresh && SinglePass.outFreshOf G I codes sumsA c node entry st.stepK (SinglePass.derivOf c node st)
        -- The returned value's checked type: its signatures' footprints.
        let T := match node.expression with
          | .var j => (c.context[j]?).getD c.type
          | _ => c.type
        let R : FC := match PositiveRules.expand G T with
          | [.arrs L S] => if L.isEmpty && S.isEmpty then .top else
            ((L.map (·.effect)) ++ S.map (·.effect)).foldl (init := bot) fun acc e => cjoin acc e.footprint
          | _ => .top
        result := cjoin result R
    thrown := ojoin thrown d.raised
  let directΦ := normal
  let directThrow := match normal, thrown with
    | some Φ, some T => T.le Φ && Φ != Footprints.Closed.top
    | _, _ => false
  -- Run B: the regional fallback's walk at `top`, its tables inferred at `top`.
  let regionalAt := fun (Φ : FC) =>
    let j := regionalInferred r Φ [] none
    let (names, heads) := (regionalFromJson r.program.length j).toOption.getD ([], #[])
    ({ Φ, regions := [], exc := false, names, heads } : SinglePass.Regional)
  let regionalJoin := fun (σ : SinglePass.WalkState _ G) (exc : Bool) =>
    let sums := σ.answers.summaries.toList
    (List.range n).foldl (init := ((some bot : Option FC), (0 : Nat))) fun (acc, k) l =>
      match σ.walk.labels[l]? with
      | some lw => match lw.visited, lw.entry, lw.stepped, lw.region with
        | true, some entry, some st, some rs =>
          let node := nodes[l]!
          let c := claimed[l]!
          let width := c.context.length
          let ordinaryEv : Option (OrdinaryEvidence _) := match st.stepDeriv, st.stepEffect with
            | some dv, _ => some (.proof dv)
            | none, some _ => some .effect
            | none, none => none
          let kHere := (SinglePass.materialize entry width (List.range width) true).1
          let cEv : NodeEvidence _ := ⟨ordinaryEv, some ⟨c.context, node.expression, c.type⟩, [],
            SinglePass.regionalFacts kHere st.stepK, st.stepEffect, {}, none, [], [], [], none⟩
          let gs := grades node.expression (SinglePass.derivOf c node st) []
          let g := regionalNode G I sums gs rs cEv node.expression (node.handler.isSome || exc)
          (ojoin acc (g.map (·.1.1)), k + (if rs.cells.isEmpty then 0 else 1))
        | _, _, _, _ => (acc, k)
      | none => (acc, k)
  let (regionalΦ, regionalThrow, visitsB, cellsTop, σB?) := match walk (some (regionalAt .top)) with
    | .ok (σB, reach) =>
      if σB.walk.visited < reach then (none, false, σB.walk.visited, 0, none) else
      let (Φ, cells) := regionalJoin σB false
      let (Φt, _) := regionalJoin σB true
      (Φ, (match Φ, Φt with | some a, some b => b.le a && a != Footprints.Closed.top | _, _ => false), σB.walk.visited, cells, some σB)
    | .error _ => (none, false, 0, 0, none)
  let _ := σB?
  let (Φ, onThrow, route) := match directΦ, regionalΦ with
    | some a, some b => if a.le b then (a, directThrow, "direct") else if b.le a then (b, regionalThrow, "regional")
      else (a, directThrow, "direct (regional incomparable)")
    | some a, none => (a, directThrow, "direct")
    | none, some b => (b, regionalThrow, "regional")
    | none, none => (.top, false, "none: top")
  -- The regional route again at the inferred bound: its freshness and
  -- tables there (question (b): `cellsKept` reads the bound).
  let (again, cellsAgain, visitsB') := if route != "regional" then (none, cellsTop, 0) else
    match walk (some (regionalAt Φ)) with
    | .ok (σ', reach) => if σ'.walk.visited < reach then (none, cellsTop, σ'.walk.visited) else
      let (Φ', k) := regionalJoin σ' false; (Φ', k, σ'.walk.visited)
    | .error _ => (none, cellsTop, 0)
  return { footprint := Φ, onThrow := onThrow && Φ != Footprints.Closed.top, fresh := fresh && returns > 0,
           result := if returns == 0 then .top else result, route,
           visits := σA.walk.visited + visitsB + visitsB', open_ := opens, rules, notUnique,
           cellsDiffer := if cellsAgain != cellsTop then 1 else 0, regionalAgain := again,
           note := s!"direct {directΦ.map showC} regional {regionalΦ.map showC}" }

/-! ## The fold over a file's functions -/

/-- A plan's request at `top` with no throw bound: its walk unbounded. -/
def _root_.Verification.SourceClaimJson.FilePlans.atTop (f : FilePlans) (i : Nat) : FilePlans :=
  { f with plans := f.plans.zipIdx.map fun (p, j) => if j != i then p else p.map fun
    | .graph name pos r => .graph name pos { r with footprint := .top, onThrow := false } }

def unitOf (fr : Front) (name : String) : Option Nat :=
  (List.range fr.units.length).find? fun i => match fr.units[i]? with
    | some (f, _, none) => f.name == name
    | _ => false

/-- Member `i`'s settled run (`passGroupMode8`'s inference of heads, as one
member): its plans and given lines after the dropped candidates. -/
def settle (f : FilePlans) (fuel : Nat) (i : Nat) : FilePlans × Option (Std.HashMap String Json) × String :=
  let group := f.fr.group i
  let given := some (f.computedGiven {} false false none group)
  let g := f.withFreshApart false group
  let s := g.inferredSettle fuel (fun _ => []) false false 1000000000 1 none false false given i
  (s.state, s.given, s.last.1 ++ s!" [runs {s.runs} dropped {s.dropped} lines {s.lines.map (·.take 160)}]")

def accepted (line : String) : Bool := (line.splitOn ": accepted;").length > 1

def verdictOf (f : FilePlans) (fuel : Nat) (i : Nat) : String × Nat :=
  let (g, given, line) := settle f fuel i
  let visits := match g.passMember fuel i false 1000000000 1 given with
    | .ok m => (m.main.map (·.counts.visited)).getD 0
    | .error _ => 0
  let group := f.fr.group i
  let given0 := some (f.computedGiven {} false false none group)
  let f0 := f.withFreshApart false group
  let first := match f0.passMember fuel i false 1000000000 1 given0 with
    | .ok m => s!" firstRun {m.outcome}"
    | .error w => s!" firstRun error {w}"
  let again := if accepted line then "" else first ++ match inferMember f0 fuel i given0 with
    | .ok r => s!" inferOnOracle {showC r.footprint} {r.route} again {r.regionalAgain.map showC} {r.note}"
    | .error w => s!" inferOnOracle error {w.take 100}"
  (line ++ again, visits)

/-- The fold, callees first; returns the stand-ins and the report lines. -/
def inferAll (ast : Json) (key : String) (budget : SearchBudget) (fuel : Nat) (est : Established)
    (tables : List (String × RowTable)) (base : FilePlans) (oracle : Bool) : List StandIn × List String := Id.run do
  let fr := base.fr
  let prepare := fun (f : FilePlans) => f.withHeadFacts {} false (inferred := true)
  -- Callees first, as `declarationWalks` orders them.
  let wanted := (List.range fr.units.length).filter fun i => match fr.units[i]? with
    | some (_, _, none) => true
    | _ => false
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
  let written := fun (f : Fragment.Fn) => f.stated.map fun s =>
    if s.regions.isEmpty then ((s.closed, s.onThrow) : FC × Bool) else (.top, false)
  let mut found : List StandIn := []
  let mut out : List String := []
  let names := order.filterMap fun i => (fr.units[i]?).map (·.1.name)
  for i in order do
    let some (f, tps, none) := fr.units[i]? | continue
    -- Every function not yet inferred at its written effect, else at `top`
    -- (a member of a cycle reads the others at the worst case).
    let others := fun (own : Option StandIn) => names.filterMap fun nm =>
      if nm == f.name then own
      else if found.any (·.name == nm) then none
      else match fr.units.find? (fun (g, _, c) => c.isNone && g.name == nm) with
        | some (g, _, _) => match written g with
          | some (Φ, ot) => some ({ name := nm, footprint := Φ, onThrow := ot } : StandIn)
          | none => some { name := nm, footprint := .top }
        | none => none
    let planAt := fun (own : Option StandIn) => (do
      let fp ← fragmentPlansFromInterfaces ast key budget (some [f.name]) { functions := found ++ others own } []
        est tables
      let fp := prepare fp
      let some j := unitOf fp.fr f.name | throw "no unit"
      return (fp, j) : Except String (FilePlans × Nat))
    let inferAt := fun (own : Option StandIn) => (do
      let (fp, j) ← planAt own
      let (g, given, _) := settle (fp.atTop j) fuel j
      inferMember g fuel j given : Except String Inferred)
    let recursive := (fr.mentions i).contains f.name
    let mut res : Except String Inferred := .error "not run"
    let mut rounds := 0
    if recursive then
      let mut assumed : StandIn := { name := f.name, footprint := bot, onThrow := true }
      for _ in List.range 8 do
        rounds := rounds + 1
        let own := match written f with
          | some (Φ, ot) => { assumed with footprint := Φ, onThrow := ot }
          | none => assumed
        res := inferAt (some own)
        match res with
        | .ok got =>
          if got.footprint.le assumed.footprint && (got.onThrow || !assumed.onThrow) then break
          let next : StandIn := { name := f.name, footprint := cjoin assumed.footprint got.footprint, onThrow := assumed.onThrow && got.onThrow }
          assumed := next
        | .error _ => break
    else
      rounds := 1
      res := inferAt (match written f with
        | some (Φ, ot) => some { name := f.name, footprint := Φ, onThrow := ot }
        | none => none)
    let walkClaim := fr.d.functions.find? fun c => c.name == f.name
    let walkShow := match walkClaim with
      | some c => s!"{showC c.footprint} onThrow {c.onThrow} result {showC c.resultFootprint}"
      | none => "-"
    match res with
    | .error why =>
      out := out ++ [s!"INFER {f.name} generic={!tps.isEmpty} rest={f.params.any (·.rest)} error {why.take 160}"]
      found := found ++ [match written f with
        | some (Φ, ot) => { name := f.name, footprint := Φ, onThrow := ot }
        | none => { name := f.name, footprint := .top }]
    | .ok got =>
      let (Φ, ot) := match written f with
        | some w => w
        | none => (got.footprint, got.onThrow)
      let R := if (SourceExtraction.resultWithFootprint fr.d.types f.ret got.result).isOk then got.result else .top
      let si : StandIn := { name := f.name, footprint := Φ, onThrow := ot && Φ != Footprints.Closed.top, resultFootprint := R }
      found := found ++ [si]
      let cmp := match walkClaim with
        | some c =>
          let a := (Φ, si.onThrow, R)
          let b := (c.footprint, c.onThrow, c.resultFootprint)
          let le := fun (x y : FC × Bool × FC) => x.1.le y.1 && (x.2.1 || !y.2.1) && x.2.2.le y.2.2
          if le a b && le b a then "equal" else if le a b then "more-precise" else if le b a then "less-precise"
          else "incomparable"
        | none => "-"
      let oracleLine := if !oracle then "" else
        match planAt (some si) with
        | .ok (fp, j) => let (line, v) := verdictOf fp fuel j; s!" oracle {accepted line} visitsCheck {v} [{line.take 1200}]"
        | .error why => s!" oracle error {why.take 100}"
      let tally := (got.rules.map fun (k, r) => s!"{k}/{r}").foldl (fun (m : List (String × Nat)) x =>
        match m.lookup x with
        | some k => (m.filter (·.1 != x)) ++ [(x, k + 1)]
        | none => m ++ [(x, 1)]) []
      out := out ++ [s!"INFER {f.name} generic={!tps.isEmpty} rest={f.params.any (·.rest)} async={f.async} written={(written f).isSome} rec={recursive} rounds={rounds} inferred {showC Φ} onThrow {si.onThrow} fresh {got.fresh} result {showC R} route {got.route} visits {got.visits} notUnique {got.notUnique} open {got.open_} again {got.regionalAgain.map showC} cellsDiffer {got.cellsDiffer} | walk {walkShow} | {cmp}{oracleLine} | {got.note} | rules {tally}"]
  return (found, out)

end Verification.ProposalsExperiment

open Lean Verification in
def main (args : List String) : IO UInt32 := do
  -- proposals-experiment <compare|use|both> <ast.json> <interfaces.json> <key> <depth>
  let [mode, astPath, interfacesPath, key, depth] := args | IO.eprintln "usage"; return 2
  let some fuel := depth.toNat? | return 2
  let budget : PositiveCertificates.SearchBudget := { rounds := 4096 }
  let ast ← RequestCli.readJson astPath
  let ast := ast >>= fun a => do
    Fragment.symbolNumbersApart [a]
    pure (Fragment.canonicalSymbols a)
  let interfaces ← RequestCli.readJson interfacesPath
  let res : Except String (List String) := do
    let a ← ast
    let cached ← interfaces
    let sc ← if (← jArr cached "modules").isEmpty then
        pure (⟨[], {}⟩ : SourceClaimJson.ImportScope)
      else SourceClaimJson.ImportScope.of a
    let (est, tables) ← SourceClaimJson.decodeInterfaces sc cached
    let prepare := fun (f : SourceClaimJson.FilePlans) => f.withHeadFacts {} false (inferred := true)
    let base ← SourceClaimJson.fragmentPlansFromInterfaces a key budget none {} [] est tables
    let base := prepare base
    let verdicts := fun (f : SourceClaimJson.FilePlans) (tag : String) =>
      (f.fr.leaders).map fun i =>
        let (_, v, _, _) := f.passGroupMode8 true [] (fun _ => []) fuel (f.fr.group i)
        s!"{tag} {f.fr.unitId i} {match v with | .ok _ => "accepted" | .error w => s!"refused {w.take 240}"}"
    let baseLines := if mode == "compare" then [] else verdicts base "BASE"
    let (found, lines) := ProposalsExperiment.inferAll a key budget fuel est tables base (mode != "use")
    let useLines := if mode == "compare" then [] else
      match SourceClaimJson.fragmentPlansFromInterfaces a key budget none { functions := found } [] est tables with
      | .ok f => verdicts (prepare f) "USE"
      | .error w => [s!"USE error {w}"]
    return baseLines ++ lines ++ useLines
  match res with
  | .ok ls => for l in ls do IO.println l
              return 0
  | .error e => IO.eprintln s!"error: {e}"; return 1
