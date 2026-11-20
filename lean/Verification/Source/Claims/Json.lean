-- Claims/Wire.lean defines the strict claim document wire and decoder.
import Verification.Source.Claims.Wire
-- Claims/Diagnostics.lean writes located source and quantified-call diagnostics.
import Verification.Source.Claims.Diagnostics
-- Claims/Schemes.lean prepares schemes, generic instances and binder rows.
import Verification.Source.Claims.Schemes
-- Claims/Sites.lean checks claim sites and module initialization order.
import Verification.Source.Claims.Sites
-- Claims/Preparation.lean lowers source annotations and claims into their equations.
import Verification.Source.Claims.Preparation
-- Claims/Plans.lean owns the exhaustive certification boundary and frozen plans.
import Verification.Source.Claims.Plans
import Verification.Source.Claims.FramedBinding
import Verification.Source.Claims.FramedPassChecks
import Verification.Source.Claims.FramedNodeChecks
-- Claims/Extraction.lean coordinates source units and reconstructs graph requests.
import Verification.Source.Claims.Extraction
-- Claims/Imports.lean plans certified imports: the module runs and the qualified reads.
import Verification.Source.Claims.Imports
import Verification.Programs.SinglePass
import Verification.Programs.CodeConditions
import Verification.Programs.SinglePassStats
import Verification.Source.Lowering.ExitProposals

/-! Source claim validation, evidence production and the theorem relating
exact accepted plans to modeled graph safety. -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)

/-- An observation's line: its tag and its record, written where every
effect it holds reads back as one (`EffectCodec.document`), otherwise the
refusal of the whole record naming the place. -/
def observationLine (tag : String) (record : Json) : String :=
  match EffectCodec.document record with
  | .ok j => tag ++ j.compress
  | .error e => tag ++ "refused: " ++ e

/-- The refusal of a spine region at a path of another kind (the note's
§3, "Regions"; `ArgumentPathTracking.regionKindOk`). -/
def kindRefusal : String :=
  "states a spine region at a path whose declared type is no collection type: a member of it is not an array, null or undefined"

/-- The located refusal of a footprint a unit claims for its declaration, or
for a closure of its code, that its graph and certificate do not establish:
at the first node the node-by-node bound check refuses, else at the
closure's region, else at the declaration. Search and checking report it
alike. A check that ran out of search rounds is no refusal: it is left to the
exhaustion diagnostic. -/
def footprintRefusal {σ ι : Type} [Labels ι] [StoreView σ ι] (name : String) (namePos : Span)
    (r : SourceRequest σ ι) (c : Response ι) : Option String :=
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  let firstBad (B : ProgramTyping.RunBound) (start : Nat) (P : Program) (C : Certificate ι)
      (sourceMap : SourceMap) : Option SourceMapEntry :=
    let facts := GraphCode.inferFresh G images c.readSummaries P C start
    let dead := GraphCode.inferDead G P C B.1.exceptional
    ((P.zip C).zipIdx.find? fun ((node, point), l) =>
      !GraphCode.nodeChecked G images c.readSummaries B.1.normal B.1.exceptional facts dead B.2 l node point).bind
      fun (_, l) => (sourceMap[l]?).bind id
  let refuse (what : String) (pos : Span) :=
    s!"source effect refusal at [{pos.1},{pos.2}): the footprint claimed for {what} is not established by its body"
  -- An async definition's footprint is `top` whatever its body does
  -- (`RequestJson.asyncEffects`): refused at the definition.
  let refuseAsync (what : String) (pos : Span) :=
    s!"source effect refusal at [{pos.1},{pos.2}): the footprint claimed for {what} is not `top`, and an async definition's is"
  if !RequestJson.asyncEffects r.async r.footprint then some (refuseAsync s!"'{name}'" namePos) else
  -- A stated declaration's claim lies within its statement
  -- (`RequestJson.statedWithin`): refused at the definition.
  if !RequestJson.statedWithin r.async r.footprint r.onThrow r.fresh r.stated then
    some s!"source effect refusal at [{namePos.1},{namePos.2}): the footprint claimed for '{name}' is not within the effect its result annotation states" else
  let asyncCode := (r.toRequest.codes.zipIdx.find? fun (q, _) =>
    !RequestJson.asyncAdmits q.async q.entry.row.effect).map fun (_, i) =>
      refuseAsync s!"a closure in '{name}'"
        ((((r.codeSources[i]?).bind fun code => sourceMapRegion code.sourceMap).map (·.pos)).getD namePos)
  if asyncCode.isSome then asyncCode else
  let unit := effectResult r c
  if !unit.accepted then
    if unit.exhaustion.isSome then none else
    some (refuse s!"'{name}'" (((firstBad (ProgramTyping.RunBound.ofRequest r.footprint r.onThrow r.fresh) r.start r.program c.certificate
      r.sourceMap).map (·.pos)).getD namePos))
  else
  -- A statement with spine regions: at the first node the regional check
  -- refuses (`regionalResult`), else at the declaration.
  if !(regionalResult r c).accepted then
    let fieldsOk := (r.regional.map fun (_, regions) =>
      GraphCode.ArgumentPathTracking.checkEntryFields G r.inputs regions).getD true
    let place := r.regional.bind fun (Φ, regions) =>
      let P := GraphCode.program (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
      let table := regionTable P c.certificate r.start regions
      let ft := freshTables G images c.readSummaries Φ P c.certificate r.start
      (GraphCode.ArgumentRegionGraph.firstRefusedNode G images c.readSummaries Φ regions table ft
        (r.stated.any (·.onThrow)) P c.certificate).bind fun (_, l) => (r.sourceMap[l]?).bind id
    let pos := (place.map (·.pos)).getD namePos
    let kindsOk := (r.regional.map fun (_, regions) =>
      regions.all (GraphCode.ArgumentPathTracking.regionKindOk G r.inputs)).getD true
    if !kindsOk then
      some s!"source effect refusal at [{namePos.1},{namePos.2}): the frame stated for '{name}' {kindRefusal}"
    else if !fieldsOk then
      some s!"source effect refusal at [{namePos.1},{namePos.2}): the frame stated for '{name}' reads a spine region through a field that is no present stable field of its parameter's type, or through more than one field"
    else
    some s!"source effect refusal at [{pos.1},{pos.2}): the frame stated for '{name}' is not established by its body: a step changes a location outside its spine regions beyond the statement's bound"
  else
    (r.toRequest.codes.zip c.codes).zipIdx.findSome? fun ((q, C), i) =>
      let code := GraphCode.effectCheckedResult G images c.readSummaries q.entry C
      if code.accepted || code.exhaustion.isSome then none else
        let sourceMap := ((r.codeSources[i]?).map (·.sourceMap)).getD []
        let place := (ProgramTyping.codeBound q.entry).bind (fun B =>
            firstBad B q.entry.start (GraphCode.program q.entry.exprs q.entry.conts) C sourceMap) <|>
          sourceMapRegion sourceMap
        some (refuse s!"a closure in '{name}'" ((place.map (·.pos)).getD namePos))

/-! ### A file's units, checked each on its own over one front -/

/-- A unit member's name as a selection names it: a function's name, or
`:init` for the module's initialization. -/
def memberName (member : String) : String :=
  if member == "init" then ":init" else (member.splitOn "@").headD member

/-- The units of a file a selection names: each group with a member it
names, or every group. -/
def Front.selected (fr : Front) (names : Option (List String)) : List Nat :=
  fr.leaders.filter fun i => match names with
    | none => true
    | some ns => (fr.group i).any fun j => ns.contains (memberName (fr.unitId j))

/-- `extractAll` over the units `wanted` names, by index, only: another
unit's plan is a refusal no check of the wanted units reads. -/
def Front.extractSome (fr : Front) (wanted : Std.HashSet Nat) (retype : Option Retype := none)
    (instances : Option Instances := none) (closureSchemes : Option ClosureSchemes := none) :
    EquationStore.State × List (Except String (FunctionPlan EquationStore.State Tree)) :=
  (fr.units.zipIdx.foldl (init := (fr.d.types, #[])) fun (T, plans) (u, i) =>
    if !wanted.contains i then (T, plans.push (.error "not extracted")) else
    match SinglePass.work "prepare: extraction" (fr.workItem i) fun _ =>
        extractMember fr T u retype instances closureSchemes with
    | .ok (next, plan) => (next, plans.push (.ok plan))
    | .error reason => (T, plans.push (.error reason))).map id (·.toList)

/-- What proposals established, by their inputs' digest (`FilePlans.proposed`). -/
abbrev ProposalMemo := Std.HashMap UInt64 (Option (SourceExtraction.ClassSummary × Footprints.Closed × Nat))

/-- A file's plans over one frozen store: the import plan, the front, the
frozen store, and each unit's plan or refusal, in the front's order. -/
structure FilePlans where
  p : ImportPlan
  fr : Front
  F : EquationStore.Frozen
  plans : List (Except String (FunctionPlan (EquationStore.Checked F.equations F.primitive)
    (EquationStore.CheckedLabel F.equations F.primitive)))
  /-- The types of the file's functions as their callers read them, in the
  store, where the planning lowered them (`fragmentPlansCore`'s
  `interfaceSlots`): a module's interface types. -/
  slots : List (String × Ty (EquationStore.CheckedLabel F.equations F.primitive)) := []
  /-- What the proposals made while planning established of each function
  (`PassProposals.proposeOne`), by the digest of the inputs its runs read
  (`PassProposals.inputDigest`): its footprint, throw bound, returned
  function's footprint and transfers, or `none` where they establish
  nothing. A later planning reads an entry only for the same inputs. -/
  proposed : ProposalMemo := {}

/-- A group's dependencies on the wire: the groups its members reach, where
its code names a qualified read, the module runs, and the module units the
reads it mentions rest on (`ImportPlan.depends`). -/
def FilePlans.dependencies (f : FilePlans) (group : List Nat) : List String :=
  (f.fr.dependencies group).map f.fr.unitId ++
    (if f.fr.readsQualified group then f.p.modules.map ("module:" ++ ·.location) else []) ++
    -- The module units a read of an import the group's code mentions rests on.
    ((f.p.depends.filter fun (n, _) => group.any fun i => (f.fr.mentions i).contains n).flatMap (·.2)).eraseDups

/-- The first extraction refusal among the groups `names` selects: a check
reports it before any refusal at the evidence. -/
def FilePlans.extractionRefusal (f : FilePlans) (names : Option (List String)) : Option String :=
  ((f.fr.selected names).flatMap f.fr.group).findSome? fun i =>
    match (f.plans[i]?).getD (.error "no unit") with
    | Except.error reason => some reason
    | Except.ok _ => none

/-- `produceGroup` and the check of its bundle, nothing encoded (`unchecked`: the
search leaves the graph's check to that check). Search evidence for one group: each member's request searched in turn,
the search's memo kept within the group only; the group's evidence, and its
refusal: the first member's search refused, or the checker's refusal of
what the searches left unchecked; and the account of the candidate
search over the members searched to the end (`CertificateProducer.Answered`):
its passes, the most over one graph, and the candidates it left out. -/
def FilePlans.searchGroup (f : FilePlans) (fuel : Nat) (group : List Nat) (unchecked : Bool) :
    Except String (Bundle (EquationStore.CheckedLabel f.F.equations f.F.primitive)) := Id.run do
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := StoreView.graph f.F.store
  let I : PositiveCertificates.InstanceImageCheck G := StoreView.images f.F.store
  let mut answers : CertificateProducer.Answered G := {}
  let mut cs := #[]
  let mut es := #[]
  let mut failed : Option String := none
  for i in group do
    let searched : Except String (Response _ × List (ProgramCertificates.Evidence _) × CertificateProducer.Answered G) :=
      do
      let (name, namePos, r) := (← (f.plans[i]?).getD (.error s!"no unit {i}")).parts
      let labels := r.searchLabels
      let (e, next) ← ExpressionClaims.produceUsing G I labels (StoreView.valid r.types)
        (StoreView.projection r.types) fuel r.obligations { answers with summaries := #[], summaryAnswers := {} }
      let (rendered, next) := ExpressionClaims.renderKnownUsing G I labels (StoreView.valid r.types)
        r.nodePlans next
      let known := e ++ rendered
      -- A qualified body's checker is stated over the request's own image
      -- check: its search keeps that check, and the request's summaries.
      let (c, kept) ← if r.qualification.isNone then
          RequestJson.produceResponseUsing G I (HeapExpressionRules.Checker.ordinary G I) r.toRequest
            fuel [] known r.sourceMap (some labels) r.assertions r.cuts r.candidates r.codeHints r.checker r.aliases next
            (searched := true) (recheck := some (HeapExpressionRules.Checker.ordinary G)) (unchecked := unchecked)
        else do
          let (c, own) ← RequestJson.produceResponseUsing (RequestJson.graph r.toRequest) (StoreView.images r.types)
            r.checker r.toRequest fuel [] known r.sourceMap (some labels) r.assertions r.cuts r.candidates
            r.codeHints r.checker r.aliases { summaries := next.summaries, summaryAnswers := next.summaryAnswers }
            (searched := true) (unchecked := unchecked)
          pure (c, { next with
            candidatePasses := next.candidatePasses + own.candidatePasses
            candidatePassesMax := max next.candidatePassesMax own.candidatePassesMax
            candidatesLeftOut := next.candidatesLeftOut + own.candidatesLeftOut })
      if let some refusal := footprintRefusal name namePos r c then throw refusal
      return (c, e, kept)
    match searched with
    | .ok (c, e, next) =>
      answers := next
      cs := cs.push c
      es := es.push e
    | .error reason =>
      if failed.isNone then failed := some reason
      cs := cs.push { certificate := [] }
      es := es.push []
  if let some reason := failed then return .error reason
  return .ok (Bundle.mk cs.toList es.toList)

/-- What a graph's statement entries are given beyond their written
assertions and the claims' facts, by label: the implications they hold,
the slots holding a promise goal's input, and the slots holding an input's
entry value a postcondition names. An input of the single pass. -/
structure GivenHeads (ι : Type) where
  implies : Array (List (PromiseCalls.Implication ι)) := #[]
  args : Array (List Nat) := #[]
  inputs : Array (List (Nat × Nat)) := #[]

section
variable {ι : Type} [Labels ι]

def GivenHeads.fromJson (n : Nat) (j : Json) : Except String (GivenHeads ι) := do
  let entries ← j.getArr?
  let mut g : GivenHeads ι := ⟨Array.replicate n [], Array.replicate n [], Array.replicate n []⟩
  for e in entries do
    let l ← e.getObjValAs? Nat "label"
    let xs ← (← e.getObjVal? "implies").getArr?
    let implies ← xs.toList.mapM fun x => do
      pure (⟨← x.getObjValAs? Nat "test", ← x.getObjValAs? Nat "target", ← x.getObjValAs? (Ty ι) "type"⟩ :
        PromiseCalls.Implication ι)
    let args ← e.getObjValAs? (List Nat) "arguments"
    let inputs ← e.getObjValAs? (List (List Nat)) "inputs"
    if l < n then
      g := ⟨g.implies.set! l implies, g.args.set! l args,
        g.inputs.set! l (inputs.filterMap fun p => match p with | [a, b] => some (a, b) | _ => none)⟩
  return g

end

/-- A regional check's given facts read back (`regionalGiven`). -/
def regionalFromJson (n : Nat) (j : Json) : Except String (List String × Array (Option SinglePass.RegionState)) := do
  let names ← j.getObjValAs? (List String) "names"
  let mut heads : Array (Option SinglePass.RegionState) := Array.replicate n none
  for e in (← (← j.getObjVal? "heads").getArr?) do
    let l ← e.getObjValAs? Nat "label"
    let facts ← e.getObjValAs? (List (Nat × Nat × List String)) "facts"
    let st : SinglePass.RegionState := ⟨facts.map fun (sl, pos, path) => ⟨sl, ⟨pos, path⟩⟩,
      ← e.getObjValAs? (List Nat) "values", ← e.getObjValAs? (List Nat) "cells",
      ← e.getObjValAs? (List (Nat × String)) "fields"⟩
    if l < n then heads := heads.set! l (some st)
  return (names, heads)

/-- A given file's loop-head facts read back (`headFacts`), each at the
statement entries of `cuts` that start where the given one does and hold as
many slots (a `for`'s head and its declarations' entry share a start): a
graph lowered over other types numbers its nodes otherwise. -/
def headFactsFromJson (sourceMap : SourceMap) (cuts : List Nat) (j : Json) : List (Nat × List HeapKnowledge.IndexAtom) :=
  let startOf := fun (l : Nat) => ((sourceMap[l]?).bind id).map (·.pos.1)
  ((j.getArr?).toOption.getD #[]).toList.flatMap fun e => match do
      let start ← (e.getObjValAs? (Option Nat) "start").toOption
      let width ← (e.getObjValAs? (Option Nat) "width").toOption
      let atoms ← (e.getObjValAs? (List HeapKnowledge.IndexAtom) "atoms").toOption
      pure (start, width, atoms) with
    | some (start, width, atoms) =>
      (cuts.filter fun l => startOf l == start && (((sourceMap[l]?).bind id).map (·.context.length)) == width).map (·, atoms)
    | none => []

/-- A member's counts, and where asked (`counting`) also as a JSON line. -/
def countsLine (counting : Bool) (name : String) (c : SinglePass.Counts) : String :=
  if counting then s!"{c}\ncounts: {name} {c.json}" else toString c

/-- The read summaries a run leaves, checked as a response's are
(`validSummary`, `checkReadSummariesResult`) over the request's graph and
image check. -/
def summariesChecked {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι)
    (sums : List (ProgramCertificates.ReadSummary ι)) : Bool :=
  sums.all (RequestJson.validSummary (StoreView.valid r.types)) &&
    (ProgramCertificates.checkReadSummariesResult (RequestJson.graph r.toRequest) (StoreView.images r.types) sums).accepted

/-- How the main graph's footprint is established (`effectResult`): by the
walk at its bound and stated regions; or, the walk refusing the bound at a
node for a result that is not fresh, by the footprint's regional fallback
with no regions; or by that fallback followed by the stated regions' walk. -/
inductive FootprintRoute where
  | direct
  | fallback
  | fallbackThenRegions
  deriving BEq, Repr

/-- A walk of a member's main graph (`FilePlans.passMember`): at its
footprint (`footprint`), by the footprint's regional fallback (`fallback`),
or at the stated regions after that fallback (`regions`). -/
inductive WalkKind where
  | footprint
  | fallback
  | regions
  deriving BEq, Repr

/-- The walk whose outcome a route concludes with. -/
def FootprintRoute.lastWalk : FootprintRoute → WalkKind
  | .direct => .footprint
  | .fallback => .fallback
  | .fallbackThenRegions => .regions

/-- What a framed probe (`framed=L;what`) observes: `what`, or the framed
node `L` itself (`node:L`); an observation other than a framed probe,
itself. -/
def framedWhat (w : String) : String :=
  if w.startsWith "framed=" then
    match (w.drop 7).toString.splitOn ";" with
    | l :: rest => let q := ";".intercalate rest; if q.isEmpty then s!"node:{l}" else q
    | [] => w
  else w

/-- An observation (`TSCERT_OBSERVE=[walk@]what`): what it observes
(`refusal`, `node:L`, `offset:K`), its walk prefix removed. -/
def observedWhat (w : String) : String :=
  match w.splitOn "@" with
  | [_, what] => what
  | _ => framedWhat w

/-- The node a framed probe (`framed=L[;what]`) frames, or none. -/
def framedProbeOf (observe : Option String) : Option Nat :=
  observe.bind fun w => if w.startsWith "framed=" then
    (((w.drop 7).toString.splitOn ";").head?.bind String.toNat?) else none

/-- The walk an observation names (`footprint@`, `fallback@`, `regions@`),
or none: every walk observes. -/
def observedWalk (w : String) : Option WalkKind :=
  match w.splitOn "@" with
  | [k, _] => [("footprint", WalkKind.footprint), ("fallback", .fallback), ("regions", .regions)].lookup k
  | _ => none

/-- The node walk `k` observes: `observed`, where the observation names no
walk or names `k`. -/
def observedIn (observe : Option String) (k : WalkKind) (observed : Option Nat) : Option Nat :=
  match observe.bind observedWalk with
  | some k' => if k' == k then observed else none
  | none => observed

/-- One code request's run, as `FilePlans.passMember` makes it: its position,
its conclusion (accepted, or the located refusal), the answers its run
leaves (the answers it was given where its signature's conditions refuse
it), and the observation record of a refusal where asked. -/
structure CodeRun (ι α : Type) where
  index : Nat
  outcome : SinglePass.Outcome ι
  answers : α
  line : String

/-- The code requests in order, each passed by `step` against the entries of
those accepted before it and the answers the previous run left: the runs
made, up to and with the first not accepted; the entries of the accepted
ones; the answers the last run left. -/
def codesInOrder {κ ε ι α : Type} (entry : κ → ε) (step : List ε → α → κ → CodeRun ι α) :
    List ε → α → List κ → List (CodeRun ι α) × List ε × α
  | table, a, [] => ([], table, a)
  | table, a, q :: rest =>
    let c := step table a q
    match c.outcome with
    | .accepted =>
      let (cs, t, a') := codesInOrder entry step (table ++ [entry q]) c.answers rest
      (c :: cs, t, a')
    | _ => ([c], table, c.answers)

/-- The main graph's runs, as `FilePlans.passMember` makes them: the route
its footprint took, the last run's outcome (`Outcome.asRefusal`), counts,
answers and trace, and on `fallbackThenRegions` the fallback run's answers. -/
structure MainRun (ι α : Type) where
  route : FootprintRoute
  outcome : SinglePass.Outcome ι
  counts : SinglePass.Counts
  after : α
  trace : SinglePass.Trace
  fallbackAfter : Option α

/-- **What the wrapper checked and concluded of one member**
(`FilePlans.passMember`): its name; the first of the request's own
conditions refusing it before any run (`request`); qualified, its one run's
outcome; unqualified, each code request's run in order (`codes`) and the
main graph's (`main`); the read summaries' check of each final run
(`summaries`: the main run's, and on `fallbackThenRegions` the fallback's;
the qualified run's); the expression obligations' check (`obligations`);
the member's conclusion (`outcome`) and its diagnostic line (`line`). A
check not reached is `none`. -/
structure MemberRun (ι α : Type) where
  name : String
  request : Option (SinglePass.Outcome ι) := none
  qualified : Option (SinglePass.Outcome ι) := none
  codes : List (CodeRun ι α) := []
  main : Option (MainRun ι α) := none
  summaries : Option Bool := none
  obligations : Option Bool := none
  outcome : SinglePass.Outcome ι
  line : String := ""

/-- The member accepted: its conclusion is acceptance. -/
def MemberRun.accepted {ι α : Type} (m : MemberRun ι α) : Bool := m.outcome matches .accepted

/-- The member's outcome where the request's own conditions refuse it before
any run. -/
def MemberRun.before {ι α : Type} (name : String) (o : SinglePass.Outcome ι) : MemberRun ι α :=
  { name, request := some o, outcome := o }

/-- A graph run's inputs digested, as `SinglePass.runRecorded` records them:
its body's (`part`: the main graph or which code request; the program,
claims, result, start, inputs, statement entries' candidates and cuts, entry
facts, the code requests' goals and the given line but its regional
tables), followed by each of these parts' own digest, then with its bound
(`bound`, as text) and those tables. A measurement. -/
def runDigests {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι) (line : Option Json)
    (part bound : String) : Unit → String × String := fun _ =>
  let parts : List UInt64 := [hash part, hash (toJson r.program).compress,
    hash (r.claims.map fun c => (c.context, c.type)), hash r.result, hash r.start, hash r.inputs,
    hash (toJson r.candidates).compress, hash r.cuts, hash (toJson r.entryIndices).compress,
    hash (reprStr (r.codes.map (·.entry.goal))), hash ((line.map fun l => (heads l).compress).getD "")]
  let h := parts.foldl mixHash 7
  let hex := fun (x : UInt64) => SinglePass.digestOf (toString x)
  -- (each part's digest too, its first four digits, `.`-separated: which
  -- inputs two runs differ in)
  (hex h ++ "/" ++ ".".intercalate (parts.map fun x => ((hex x).take 4).toString),
    hex (mixHash h (hash (bound ++ "|" ++ (line.map fun l => (tables l).compress).getD ""))))
where
  /-- The given line but its regional tables, which only the regional
  routes read: the inputs of every route. -/
  heads (l : Json) : Json := match l with
    | .obj kvs => .obj ((kvs.erase "regional").erase "footprintRegional")
    | j => j
  /-- The given line's regional tables. -/
  tables (l : Json) : Json := Json.mkObj [("regional", l.getObjValD "regional"),
    ("footprintRegional", l.getObjValD "footprintRegional")]

/-- A bound and a regional check, as text, for `runDigests`. -/
def boundText (bound : Option RunBound) (regional : Option SinglePass.Regional) : String :=
  s!"{reprStr bound}|{reprStr (regional.map fun rg => (rg.Φ, rg.exc, rg.names, rg.regions.length))}"

/-- The facts a refused edge lacks, shown (the framed probe's). -/
def outcomeLacks {ι : Type} : SinglePass.Outcome ι → String
  | .refused _ (some (t, xs)) _ => s!" (at {t}: {(toJson xs).compress})"
  | _ => ""

/-- **The framed probe's settling**: the walk `runAt` from the candidates
`cands₀`, a refusal at a head lacking candidates there leaving them out and
the framed node's supports taken again (`framedAt`, with `framed`), as the
member's run settles (`inferredNext`); each run's outcome and what it left
out, and at `observed` the settled walk's entry and step facts. -/
def framedProbeSettle {ι : Type}
    (runAt : List (Nat × List HeapKnowledge.IndexAtom) → List (Nat × List Footprints.Footprint) → Option Nat → SinglePass.Outcome ι)
    (framedAt : List (Nat × List HeapKnowledge.IndexAtom) → List (Nat × List Footprints.Footprint))
    (cands₀ : List (Nat × List HeapKnowledge.IndexAtom)) (observed : Option Nat) (framed : Bool) : String := Id.run do
  let mut cands := cands₀
  let mut lines : List String := []
  for _ in List.range 12 do
    let fr := if framed then framedAt cands else []
    let o := runAt cands fr none
    lines := lines ++ [s!"    run (framed {fr.map fun (p : Nat × List Footprints.Footprint) => p.2.length}): {o}{outcomeLacks o}"]
    match o with
    | .refused _ (some (t, xs)) _ =>
      let held := (cands.filter (·.1 == t)).flatMap (·.2)
      let drop := held.filter xs.contains
      if drop.isEmpty then break
      lines := lines ++ [s!"    dropped at {t}: {(toJson drop).compress}"]
      cands := cands.map fun (l', as) => if l' == t then (l', as.filter (!drop.contains ·)) else (l', as)
    | _ => break
  let fr := if framed then framedAt cands else []
  let seen := match observed with
    | some ob => match runAt cands fr (some ob) with
      | .observed o => s!"\n    entry of node {ob}: {(toJson o.before.indices).compress}\n    after node {ob}: {(toJson o.after.indices).compress}"
      | o => s!"\n    node {ob} not observed: {o}"
    | none => ""
  return "\n".intercalate lines ++ seen

/-- **The framed probe's report** (`TSCERT_OBSERVE=framed=L[;what]`): the
walk `runAt` once with node `L` framed keeping the produced support of each
index fact on its entry (`framedAt`) and once with none, the facts a
refused edge lacks, and each walk settled (`framedProbeSettle`). -/
def framedProbeReport {ι : Type}
    (runAt : List (Nat × List HeapKnowledge.IndexAtom) → List (Nat × List Footprints.Footprint) → Option Nat → SinglePass.Outcome ι)
    (framedAt : List (Nat × List HeapKnowledge.IndexAtom) → List (Nat × List Footprints.Footprint))
    (cands : List (Nat × List HeapKnowledge.IndexAtom)) (L : Nat) (observed : Option Nat) : String :=
  let fr := framedAt cands
  s!"framed probe: node {L} keeps {fr.map fun (p : Nat × List Footprints.Footprint) => p.2.length} supports\n  ordinary walk: {runAt cands [] none}{outcomeLacks (runAt cands [] none)}\n  framed walk: {runAt cands fr none}{outcomeLacks (runAt cands fr none)}\n  settled ordinary:\n{framedProbeSettle runAt framedAt cands observed false}\n  settled framed:\n{framedProbeSettle runAt framedAt cands observed true}"

/-- **A framed probe's trace**: no framed node, the main walk unchanged;
at a framed probe of node `L`, its report printed. -/
def probeTrace (probe : Option Nat) (report : Nat → String) : List (Nat × List Footprints.Footprint) :=
  match probe with
  | none => []
  | some L => dbgTrace (report L) fun _ => []

theorem probeTrace_nil (probe : Option Nat) (report : Nat → String) : probeTrace probe report = [] := by
  cases probe <;> rfl

/-- **One member's single pass** (`SinglePass.run`), no certificate built:
its plan through the exhaustive conversion (`FunctionPlan.certify`), the
request's own conditions, each code request's run against the codes
admitted before it, the main graph's runs and the read summaries' and
expression obligations' checks; with the diagnostics asked for (`observe`,
`counting`) as its line; with `grading`, the main graph's runs report each
visit's record of its step's local effect in their counts (`SinglePass.Walk.visits`);
with `framed`, the main graph's walks frame those nodes, keeping those
supports at their returns (`SinglePass.framedAt`), which only a framed
plan's check reads (`FilePlans.framedRefusal`, `FilePlans.framedCheck`):
the verdict's graph plans' runs frame none. -/
def FilePlans.passMemberGraph (f : FilePlans) (fuel : Nat) (i : Nat) (compare : Bool := false)
    (debugNode : Nat := 1000000000) (repeats : Nat := 1) (given : Option (Std.HashMap String Json) := none)
    (observe : Option String := none) (counting : Bool := false) (grading : Bool := false)
    (framed : List (Nat × List Footprints.Footprint) := []) :
    Except String (MemberRun (EquationStore.CheckedLabel f.F.equations f.F.primitive)
      (CertificateProducer.Answered (StoreView.graph f.F.store))) := do
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := StoreView.graph f.F.store
  let I : PositiveCertificates.InstanceImageCheck G := StoreView.images f.F.store
  let answers : CertificateProducer.Answered G := {}
  let plan ← (f.plans[i]?).getD (.error s!"no unit {i}")
  let cert ← plan.certify
  -- A framed plan: no check of the pass certifies the read-only frame's
  -- obligations, so it is refused at its name.
  let .graph name _ r := cert
    | match cert with
      | .framed name .. => return .before name (.refused "a framed plan, which no check certifies")
      | .graph name .. => return .before name (.refused "a framed plan, which no check certifies")
  -- The request's own checks over its whole certificate the pass does
  -- not make: the graph is passed, and its verdict is not handled.
  -- A footprint (`effectResult`): its request-level conditions here, its
  -- graph's bound at each node in the pass (`GraphCode.compositionalChecked`),
  -- a pure program's shortcut first.
  let bounded := !(r.footprint == .top && !r.onThrow && !r.fresh) &&
    !(!r.fresh && r.program.all fun n => Purity.pureTerm n.expression)
  if !(RequestJson.asyncEffects r.async r.footprint && (!r.async || !r.fresh) &&
      RequestJson.statedWithin r.async r.footprint r.onThrow r.fresh r.stated) then
    return .before name (.refused "the declared effect")
  if bounded && !(r.footprint != .top || r.fresh) then return .before name (.refused "the declared effect")
  let bound := if bounded then some (RunBound.ofRequest r.footprint r.onThrow r.fresh) else none
  -- A postcondition (`ensuresResult`): checked at each return in the pass.
  if !r.ensures.isEmpty && r.qualification.isSome then return .before name (.refused "a postcondition")
  let labels := SinglePass.timedKind "outside: search labels" fun _ => r.searchLabels
  let (e, next) ← SinglePass.timedKind "outside: expression claims searched" fun _ =>
    ExpressionClaims.produceUsing G I labels (StoreView.valid r.types)
    (StoreView.projection r.types) fuel r.obligations { answers with summaries := #[], summaryAnswers := {} }
  let (rendered, next) := SinglePass.timedKind "outside: node plans rendered" fun _ =>
    ExpressionClaims.renderKnownUsing G I labels (StoreView.valid r.types) r.nodePlans next
  let pool := SinglePass.timedKind "outside: vocabulary" fun _ => CertificateProducer.vocabulary G labels r.claims r.inputs
  let reference : Array HeapKnowledge.Knowledge := if !compare then #[] else
    match f.searchGroup fuel [i] true with
    | .ok b => match b.functions.head? with
      | some resp => (resp.certificate.map (·.knowledge)).toArray
      | none => #[]
    | .error _ => #[]
  -- The statement entries' given facts beyond the written ones and the
  -- claims': read from the given file's line of this unit, where given.
  let line := given.bind fun m => m.get? (f.fr.unitId i)
  let main : GivenHeads _ := match line with
    | some l => match (l.getObjVal? "graph").bind (GivenHeads.fromJson r.program.length) with
      | Except.ok g => g
      | Except.error _ => {}
    | none => {}
  let givenImplies := main.implies
  let givenArgs := main.args
  let givenInputs := main.inputs
  -- A qualified body (`SourceRequest.checker`): the walk over the
  -- request's own graph and image check, at its checker and aliases;
  -- the request-level conditions a qualified body meets
  -- (`effectResult`, `regionalResult`, `ensuresResult`).
  if let some q := r.qualification then
    if !(r.footprint == .top && !r.onThrow && !r.fresh) then return .before name (.refused "the declared effect")
    if r.regional.isSome then return .before name (.refused "spine regions of a qualified body")
    if !r.codes.isEmpty then return .before name (.notHandled "codes of a qualified body")
    let G' := RequestJson.graph r.toRequest
    let I' := StoreView.images r.types
    let pool' := CertificateProducer.vocabulary G' labels r.claims r.inputs
    let (o, counts, after, _) := CertificateProducer.timed SinglePass.passNanos fun _ =>
      SinglePass.runRecorded "main" "qualified" (runDigests r line "main" "qualified") (fun x => x.2.1.visited) fun _ =>
      SinglePass.run G' I' pool' fuel r.program r.claims r.start r.inputs r.goal r.assertions r.cuts r.candidates
        r.entryIndices [] (e ++ rendered) (GraphCode.admits []) r.aliases (.qualified q.body q.ordinary)
        { summaries := next.summaries, summaryAnswers := next.summaryAnswers } #[] debugNode none
        givenImplies givenArgs r.ensures givenInputs r.entrySeparation none false false
    let sums := after.summaries.toList
    let sumsOk := summariesChecked r sums
    let obligations := ExpressionClaims.checkAllResult G' I' (StoreView.valid r.types) r.obligations e
      (GraphCode.admits []) sums
    let outcome : SinglePass.Outcome _ := match o with
      | .accepted => if !sumsOk then .refused "a read summary"
        else if !obligations.accepted then .refused "an expression claim" else .accepted
      | .refused w lacks pre => .refused w lacks pre
      | .outsideBound l => .refused s!"footprint at node {l}"
      | .notHandled w => .notHandled w
      | .observed _ => .notHandled "observing a qualified body"
    return { name, qualified := some o, summaries := some sumsOk, obligations := some obligations.accepted,
             outcome, line := countsLine counting name counts }
  -- Each code request, in order, passed over its own graph with the codes
  -- admitted before it (`produceResponseUsing`'s loop, `codeCheckedResult`):
  -- its signature's conditions, its graph against its goal and frame, its
  -- effect's bound; then the unit's graph over the admitted table. The
  -- read summaries the searches add are kept from run to run: the unit's
  -- are checked once (`checkReadSummariesResult`).
  let codeStep := fun (table : List (CodeEntry _)) (sumsAnswers : CertificateProducer.Answered G)
      ((q, ci) : CodeRequest _ × Nat) =>
    let refuse := fun (o : SinglePass.Outcome _) => ({ index := ci, outcome := o, answers := sumsAnswers, line := "" } : CodeRun _ _)
    let hints := (r.codeHints[ci]?).getD {}
    let rq := q.asRequest r.toRequest
    let eff := q.entry.row.effect
    let conditions := ProgramTyping.codeConditions q.entry
    if !conditions then refuse (.refused s!"code {ci}: its signature")
    -- An async code's footprint is `top` (`RequestJson.asyncEffects`, as
    -- `codeTableResult` requires of every code): its call returns
    -- normally where its body throws.
    else if !RequestJson.asyncAdmits q.async eff then
      refuse (.refused s!"code {ci}: an async definition's footprint")
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
    let codeImplies := codeGiven.implies
    let codeArgs := codeGiven.args
    let (o, _, a, _) := SinglePass.runRecorded "code" "direct"
        (runDigests r line s!"code {ci}" (boundText codeBound none)) (fun x => x.2.1.visited) fun _ =>
      SinglePass.run G I codePool fuel rq.program rq.claims rq.start rq.inputs q.entry.goal hints.requirements
      hints.cuts hints.candidates rq.entryIndices [] (e ++ rendered) (GraphCode.admits table) r.aliases
      .ordinary sumsAnswers #[] 1000000000 codeBound codeImplies codeArgs
    -- A code run makes no observation (it is given none): any outcome
    -- but acceptance is the code's located refusal.
    match o.asRefusal with
    | .accepted => { index := ci, outcome := .accepted, answers := a, line := "" }
    | .notHandled w => { index := ci, outcome := .notHandled s!"{w} (in code {ci})", answers := a, line := "" }
    | .refused w lacks pre =>
      -- A refusal observed in a code request: its obligation, the facts
      -- over its names and those it lacks, as for the unit's own graph.
      let record := if observe.map observedWhat != some "refusal" then "" else
        let (_, _, _, trace) := SinglePass.run G I codePool fuel rq.program rq.claims rq.start rq.inputs q.entry.goal hints.requirements
          hints.cuts hints.candidates rq.entryIndices [] (e ++ rendered) (GraphCode.admits table) r.aliases
          .ordinary a #[] 1000000000 codeBound codeImplies codeArgs [] #[] {}
          (some 1000000000) true
        let l := trace.node
        let mentioned := ((rq.claims[l]?).map RequestJson.PointClaim.mentions).getD []
        let p := StoreView.projection r.types mentioned.eraseDups
        let width := trace.names.length
        let slotOf := fun (x : Nat) => trace.names.idxOf? x
        let shown := fun (as : List SinglePass.Atom) =>
          toJson (SinglePass.ofAtoms (as.filterMap fun a => a.rename slotOf) width)
        let here := (trace.afters[l]?).join.orElse fun _ => (trace.entries[l]?).join
        let focus := (here.map fun st => st.store.connected trace.focus).getD []
        let facts := (here.map fun st => st.store.toList.filter fun a => a.names.any focus.contains).getD []
        let place := fun l => [("label", toJson l), ("sourceMap", toJson ((hints.sourceMap[l]?).bind id))]
        let missingJson := trace.missing.map fun a => Json.mkObj [("fact", shown [a]),
          ("where", Json.arr ((trace.locate l a 3 false).map fun (q, why) => Json.mkObj (place q ++ [("why", toJson why)])).toArray)]
        let record := Json.mkObj ([("refusal", toJson s!"code {ci}: {w}"), ("observed", Json.mkObj (place l)),
          ("node", toJson rq.program[l]?),
          ("claim", toJson ((rq.claims[l]?).map (RequestJson.PointClaim.shown p))),
          ("facts", shown facts), ("missing", Json.arr missingJson.toArray)] ++ p.fields)
        observationLine "refusal-observation: " record
      { index := ci, outcome := .refused s!"code {ci}: {w}" lacks pre, answers := a, line := record }
    | o => { index := ci, outcome := .refused s!"code {ci}: {o}", answers := a, line := "" }
  let (codeRuns, table, sumsAnswers) := codesInOrder (·.1.entry) codeStep [] next r.codes.zipIdx
  if let some c := codeRuns.find? fun c => !(c.outcome matches .accepted) then
    return { name, codes := codeRuns, outcome := c.outcome, line := c.line }
  let codes := GraphCode.admits table
  -- Observing (`observe`): the node of that label (`node:L`), or the
  -- innermost node whose source span holds that offset (`offset:K`).
  let observed : Option Nat := (observe.map observedWhat).bind fun w =>
    if w == "refusal" then some 1000000000 else
    if w.startsWith "node:" then (w.drop 5).toString.toNat? else
    if w.startsWith "offset:" then (w.drop 7).toString.toNat?.bind fun k =>
      let holding := r.sourceMap.zipIdx.filterMap fun (e, l) => e.bind fun e =>
        if e.pos.1 ≤ k && k < e.pos.2 then some (e.pos.2 - e.pos.1, l) else none
      (holding.foldl (fun (b : Option (Nat × Nat)) x => match b with
        | some y => if x.1 < y.1 then some x else some y
        | none => some x) none).map (·.2)
    else none
  if observe.isSome && observed.isNone then
    return { name, codes := codeRuns, outcome := .notHandled "no node to observe" }
  -- Profiling: the pass run `repeats` times, the last run's result kept.
  for k in List.range (repeats - 1) do
    let (o, _, _, _) := SinglePass.run G I pool fuel r.program r.claims r.start r.inputs r.goal r.assertions r.cuts r.candidates
      r.entryIndices [] (e ++ rendered) codes r.aliases .ordinary sumsAnswers #[] (debugNode + k)
    if let .notHandled w := o then throw w
  let tracing := observe.map observedWhat == some "refusal"
  -- The regional checks (`regionalChecked`), made in the walk: the
  -- unit's spine regions, and its footprint's regional fallback
  -- (`effectResult`); each loop head's given regional facts read from
  -- the given line. Their entry conditions (`checkEntryFields`, the
  -- regions' own conditions) are checked here.
  let regionalOf := fun (key : String) (Φ : Footprints.Closed) (regions : List Footprints.ArgumentSpineRegion) (exc : Bool) =>
    let (names, heads) := match line.bind fun l => (l.getObjVal? key).toOption with
      | some j => (regionalFromJson r.program.length j).toOption.getD ([], #[])
      | none => ([], #[])
    ({ Φ, regions, exc, names, heads } : SinglePass.Regional)
  let regional := r.regional.map fun (Φ, regions) => regionalOf "regional" Φ regions (r.stated.any (·.onThrow))
  if let some (_, regions) := r.regional then
    if r.async || r.fresh || !GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions then
      return { name, codes := codeRuns, outcome := .refused "spine regions" }
  let walk := fun (k : WalkKind) (bound : Option RunBound) (regional : Option SinglePass.Regional) =>
    -- (each run recorded: more than one per member run is a regional
    -- check beside the first, `mainRun`)
    SinglePass.work "check: main graph run" (f.fr.workItem i) fun _ =>
    SinglePass.runRecorded "main" (match regional with
        | none => "direct"
        | some rg => if rg.regions.isEmpty then "fallback" else "regions")
      (runDigests r line "main" (boundText bound regional)) (fun x => x.2.1.visited) fun _ =>
    SinglePass.run G I pool fuel r.program r.claims r.start r.inputs r.goal r.assertions r.cuts r.candidates
      r.entryIndices [] (e ++ rendered) codes r.aliases .ordinary sumsAnswers reference debugNode bound
      givenImplies givenArgs r.ensures givenInputs r.entrySeparation (observedIn observe k observed) tracing false regional grading
      (framed ++ probeTrace (framedProbeOf observe) fun L =>
        let framedAt := fun (cands : List (Nat × List HeapKnowledge.IndexAtom)) =>
          match (SinglePass.run G I pool fuel r.program r.claims r.start r.inputs r.goal r.assertions r.cuts
            cands r.entryIndices [] (e ++ rendered) codes r.aliases .ordinary sumsAnswers reference debugNode bound
            givenImplies givenArgs r.ensures givenInputs r.entrySeparation (some L) false false regional).1 with
          | .observed o => [(L, o.before.indices.filterMap fun a => a.fact.support? {})]
          | _ => []
        let runAt := fun (cands : List (Nat × List HeapKnowledge.IndexAtom)) (fr : List (Nat × List Footprints.Footprint))
            (ob : Option Nat) => (SinglePass.run G I pool fuel r.program r.claims r.start r.inputs r.goal r.assertions r.cuts
            cands r.entryIndices [] (e ++ rendered) codes r.aliases .ordinary sumsAnswers reference debugNode bound
            givenImplies givenArgs r.ensures givenInputs r.entrySeparation ob false false regional false fr).1
        framedProbeReport runAt framedAt r.candidates L observed)
  let (o, counts, after, trace) := CertificateProducer.timed SinglePass.passNanos fun _ => walk .footprint bound regional
  -- A footprint the walk refuses node by node, checked regionally with no
  -- regions where the result is not fresh; then the unit's own regions,
  -- the fallback's answers kept for their read summaries' check.
  let mainRun : MainRun _ _ := match o with
    | .outsideBound l => if !r.fresh then
        let fallback := regionalOf "footprintRegional" r.footprint [] r.onThrow
        match walk .fallback none (some fallback) with
        | (.accepted, c, a, t) => match regional with
          | some rg => let (o', c', a', t') := walk .regions none (some rg)
            { route := .fallbackThenRegions, outcome := o'.asRefusal, counts := c', after := a', trace := t', fallbackAfter := some a }
          | none => { route := .fallback, outcome := .accepted, counts := c, after := a, trace := t, fallbackAfter := none }
        | (.refused w' lacks pre, c, a, t) =>
          { route := .fallback, outcome := .refused s!"footprint by spine regions: {w'} (after footprint at node {l})" lacks pre,
            counts := c, after := a, trace := t, fallbackAfter := none }
        | (o', c, a, t) => { route := .fallback, outcome := o'.asRefusal, counts := c, after := a, trace := t, fallbackAfter := none }
      else { route := .direct, outcome := o.asRefusal, counts, after, trace, fallbackAfter := none }
    | _ => { route := .direct, outcome := o.asRefusal, counts, after, trace, fallbackAfter := none }
  let counts := mainRun.counts
  let trace := mainRun.trace
  -- The unit's own expression claims, as the check reads them.
  let obligations := SinglePass.timedKind "outside: expression claims checked" fun _ => ExpressionClaims.checkAllResult (RequestJson.graph r.toRequest) (StoreView.images r.types)
    (StoreView.valid r.types) r.obligations e codes mainRun.after.summaries.toList
  -- The read summaries every step's check read, checked as a response's
  -- are (`validSummary`, `checkReadSummariesResult`); after the regional
  -- fallback and the unit's regions, the fallback run's too: its
  -- footprint rests on them.
  let sumsOk := summariesChecked r mainRun.after.summaries.toList &&
    mainRun.fallbackAfter.all fun a => summariesChecked r a.summaries.toList
  let o : SinglePass.Outcome _ := match mainRun.outcome with
    | .accepted => if !sumsOk then .refused "a read summary" else if !obligations.accepted then .refused "an expression claim"
      else .accepted
    | o => o
  -- A node observed whose step is refused, or that is not reached past
  -- the refusal: the walk that concluded again (its route's last), stopping
  -- on its entry; the refusal kept where that walk accepts.
  let o : SinglePass.Outcome _ := match o, observed with
    | .refused _ _ _, some _ => if tracing then o else
      let (bound', regional') := match mainRun.route with
        | .direct => (bound, regional)
        | .fallback => (none, some (regionalOf "footprintRegional" r.footprint [] r.onThrow))
        | .fallbackThenRegions => (none, regional)
      match (SinglePass.run G I pool fuel r.program r.claims r.start r.inputs r.goal r.assertions r.cuts r.candidates
        r.entryIndices [] (e ++ rendered) codes r.aliases .ordinary sumsAnswers #[] debugNode bound'
        givenImplies givenArgs r.ensures givenInputs r.entrySeparation (observedIn observe mainRun.route.lastWalk observed)
        false true regional' false framed).1.asRefusal with
      | .accepted => o
      | o' => o'
    | o, _ => o
  let checked := fun (outcome : SinglePass.Outcome _) (line : String) =>
    ({ name, codes := codeRuns, main := some mainRun, summaries := some sumsOk,
       obligations := some obligations.accepted, outcome, line } : MemberRun _ _)
  -- A refusal observed: its obligation's facts, the facts it lacks, and
  -- each fact over its names an earlier state held, where last present
  -- and what removed it (`Trace.locate`, `Trace.lost`).
  if let .refused w _ _ := o then
    if tracing then
      let l := trace.node
      let mentioned := ((r.claims[l]?).map RequestJson.PointClaim.mentions).getD []
      let p := StoreView.projection r.types mentioned.eraseDups
      let width := trace.names.length
      let slotOf := fun (x : Nat) => trace.names.idxOf? x
      let shown := fun (as : List SinglePass.Atom) =>
        toJson (SinglePass.ofAtoms (as.filterMap fun a => a.rename slotOf) width)
      let here := (trace.afters[l]?).join.orElse fun _ => (trace.entries[l]?).join
      let focus := (here.map fun st => st.store.connected trace.focus).getD []
      let facts := (here.map fun st => st.store.toList.filter fun a => a.names.any focus.contains).getD []
      let place := fun l => [("label", toJson l), ("sourceMap", toJson ((r.sourceMap[l]?).bind id))]
      let lostJson := (trace.lost.map fun (a, ws) => Json.mkObj [("fact", shown [a]),
        ("where", Json.arr (ws.map fun (q, why) => Json.mkObj (place q ++ [("why", toJson why)])).toArray)])
      let missingJson := trace.missing.map fun a => Json.mkObj [("fact", shown [a]),
        ("where", Json.arr ((trace.locate l a 3 false).map fun (q, why) => Json.mkObj (place q ++ [("why", toJson why)])).toArray)]
      let record := Json.mkObj ([("refusal", toJson w), ("observed", Json.mkObj (place l)),
        ("edge", toJson (trace.edge.map fun t => Json.mkObj (place t))),
        ("node", toJson r.program[l]?),
        ("claim", toJson ((r.claims[l]?).map (RequestJson.PointClaim.shown p))),
        ("facts", shown facts), ("missing", Json.arr missingJson.toArray), ("lost", Json.arr lostJson.toArray)] ++ p.fields)
      return checked o (observationLine "refusal-observation: " record)
  if let .observed ob := o then
    let claimAt := fun l => (r.claims[l]? : Option (CertificateProducer.PointClaim _))
    let mentioned := ((claimAt ob.label).map RequestJson.PointClaim.mentions).getD [] ++
      ob.implies.flatMap (·.type)
    let p := StoreView.projection r.types mentioned.eraseDups
    let place := fun l => [("label", toJson l), ("sourceMap", toJson ((r.sourceMap[l]?).bind id))]
    let record := Json.mkObj ([("observed", Json.mkObj (place ob.label)),
      ("node", toJson r.program[ob.label]?),
      ("claim", toJson ((claimAt ob.label).map (RequestJson.PointClaim.shown p))),
      ("before", toJson ob.before), ("after", toJson ob.after), ("slotNames", toJson ob.names),
      ("implies", Json.arr (ob.implies.map fun x => Json.mkObj [("test", toJson x.test),
        ("target", toJson x.target), ("type", toJson (p.shown x.type))]).toArray),
      ("preds", Json.arr (ob.preds.map fun (pl, k) => Json.mkObj (place pl ++ [("knowledge", toJson k)])).toArray)] ++ p.fields)
    return checked (.notHandled "observed") (observationLine "observation: " record)
  return checked o (countsLine counting name counts)

/-- **The effect a call node's callee states**, read at the caller's slots
(`PromiseCalls.callerFrame`): the union over the callee type's signatures,
fixed and variadic; none where the node calls no slot of a function type. -/
def callEffectAt {ι : Type} [LabelStore.Labels ι] (G : NormalGraph ι) (c : CertificateProducer.PointClaim ι) (e : Tm) :
    Option Footprints.Footprint :=
  match e with
  | .invoke (.var j) _ _ => (c.context[j]?).bind fun T => match PositiveRules.expand G T with
    | [PositiveNormalization.Clause.arrs L S] | [PositiveNormalization.Clause.callable _ _ L S _] =>
      let effs := L.map (·.effect) ++ S.map (·.effect)
      if effs.isEmpty then none else some (effs.flatMap fun eff => PromiseCalls.callerFrame eff e)
    | _ => none
  | _ => none

/-- **The effects the callees of a request's call nodes state** (`callEffectAt`
at each node's claim and expression). -/
def callEffects {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι] (G : NormalGraph ι) (r : SourceExtraction.SourceRequest σ ι) :
    Nat → Option Footprints.Footprint :=
  fun l => (r.claims[l]?).bind fun c => (r.program[l]?).bind fun n => callEffectAt G c n.expression

/-- Plan `i`'s candidates at label `l` less `drop`. -/
def FilePlans.dropCandidates (f : FilePlans) (i l : Nat) (drop : List HeapKnowledge.IndexAtom) : FilePlans :=
  { f with plans := f.plans.zipIdx.map fun (p, j) => if j != i then p else p.map (FunctionPlan.mapRequest fun r =>
      { r with candidates := r.candidates.map fun (l', as) =>
        if l' == l then (l', as.filter (!drop.contains ·)) else (l', as) }) }

/-- Plan `i` replaced by `p`. -/
def FilePlans.withPlan (f : FilePlans) (i : Nat)
    (p : FunctionPlan (EquationStore.Checked f.F.equations f.F.primitive) (EquationStore.CheckedLabel f.F.equations f.F.primitive)) :
    FilePlans :=
  { f with plans := f.plans.set i (.ok p) }

/-- A text's first line: a framed plan's refusal is one line, the
diagnostic records of the run it read left to that run. -/
def firstLine (t : String) : String := (t.splitOn "\n").headD t

open Verification.TolerantFrames.ReadOnly in
/-- **A framed plan's check by the pass** (the draft, "What the pass
checks"): the binding checks that read the component alone
(`componentBindingRefusal`: `FFlow.check`, `marksB`, `codesCoverB`,
`allocB`, `initB`, (S), (K) and (O)), evaluated once per component and
shared by its plans, the plan carrying the evaluation with its value
(`FramedSpec.componentRefusal`); then those that read the request, in order: the entry's start
`entryB`, the request's tag `compB`, the request's code covered
`codesCoverB`, the entry's signatures `entryFnB` at the sibling slots and
the closure's own, `realizedFlowB`, the wire's $`\Theta_C`$ the
`@clients` rows' by kind `clientsB` and the wire's $`\Psi_C`$ at least
the component's protocol as defined `protocolAtLeastB`, both at the flow's
sites, and the read-only types `readOnlyB`; its framed call nodes, those
of the realized code the flow frames (`framedCallNodes`); at each, every
support it keeps passing the frame's check at the call's protocol, from
the wire's $`\Psi_C`$ and $`\Theta_C`$, and the callee's stated effect
(`framedSupportsAt`); then its main graph walked with those nodes framed
(`passMemberGraph` at the request's graph plan), settled as a member's
run is (the candidates an edge lacks left out). Its text is the first that
fails, and otherwise the obligation the framed claim still needs:
`FramedObligations.reached`, the framed returns at the executions the
claim is about (`ret_reached`), which no check establishes. A framed plan
is never accepted here. -/
def FilePlans.framedRefusal (f : FilePlans) (fuel i : Nat) (name : String) (pos : Span)
    (r : SourceRequest (EquationStore.Checked f.F.equations f.F.primitive) (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (spec : FramedSpec (EquationStore.CheckedLabel f.F.equations f.F.primitive)) : String := Id.run do
  if let some w := spec.componentRefusal.val then return w
  let F := spec.checked
  let m := realizedCode r
  let entry := m.1.length - 1
  let c0 := capSlot spec.arity false 0
  -- (the sibling slots, then the closure's own slot)
  let sib := (List.range (r.siblings.length + 1)).map (c0 + ·)
  let U := flowSites F
  let ΨC : Protocol (markedPackage spec.ofC spec.marks) := protocolOfParts id (partsIndex spec.psi)
  let Θ : Protocol (markedPackage spec.ofC spec.marks) := protocolOfKinds spec.theta
  let checks : List (String × (Unit → Bool) × (Unit → String)) := [
    ("its entry's start (entryB)", fun _ => F.entryB m entry, fun _ => ""),
    ("its component (compB)", fun _ => compB spec.C r,
      fun _ => s!" (the request's tag {r.comp}, the plan's component {spec.C})"),
    ("its request's code covered (codesCoverB)", fun _ => codesCoverB F [requestCode r], fun _ => ""),
    ("its entry's signatures (entryFnB)", fun _ => entryFnB F m entry sib, fun _ =>
      -- (the entry's slots naming a signature, at each context)
      let named := ((F.at m entryCx).map fun c =>
        (List.range (c.node entry).fn.size).filter fun j => ((c.node entry).fnAt j).isSome).getD []
      s!" (the entry's slots naming a signature {named}, its sibling slots {sib})"),
    ("its realized code's proposals (realizedFlowB)", fun _ => realizedFlowB F r, fun _ => ""),
    ("its client obligation (clientsB)", fun _ => clientsB U Θ (componentRows spec.family spec.C), fun _ => ""),
    ("its protocol (protocolAtLeastB)", fun _ => protocolAtLeastB U (protocolOfParts id (partsIndex spec.psiDef)) ΨC, fun _ => ""),
    ("its read-only types (readOnlyB)", fun _ => readOnlyB spec.family spec.C name r.inputs spec.readOnly, fun _ => "")]
  if let some (w, _, detail) := checks.find? (!·.2.1 ()) then
    return s!"framed plan: the binding check of {w} fails{detail ()}"
  let nodes := framedCallNodes F spec.host m
  if nodes != spec.framed.map (·.1) then
    return s!"framed plan: its framed call nodes {spec.framed.map (·.1)} are not the flow's {nodes}"
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := StoreView.graph f.F.store
  for (l, Ss) in spec.framed do
    let some Φ := (r.claims[l]?).bind fun c => (r.program[l]?).bind fun n => callEffectAt G c n.expression
      | return s!"framed plan: its framed call node {l} has no stated effect of its callee"
    let kept := framedSupportsAt F spec.lay spec.host ΨC Θ m l Φ Ss
    if kept.length != Ss.length then
      return s!"framed plan: at its framed call node {l}, {Ss.length - kept.length} of the supports it keeps fail the frame's check"
  let mut g := f.withPlan i (.graph name pos r)
  for _ in List.range 12 do
    match g.passMemberGraph fuel i (framed := spec.framed) with
    | .error e => return s!"framed plan: {firstLine e}"
    | .ok run => match run.outcome with
      | .accepted =>
        -- (the checks the returns at reached executions read at the request)
        let eff := callEffects G r
        let reqChecks : List (String × (Unit → Bool)) := [
          ("its request's node expressions source terms (sourceTermsB)", fun _ => sourceTermsB r),
          ("its client obligation keeping every part (thetaKeepB)", fun _ => thetaKeepB spec.theta),
          ("its start a label of its program", fun _ => decide (r.start < r.program.length)),
          ("its realized code's proposals at the frame's flow (realizedFlowB)", fun _ => realizedFlowB spec.fflowC r),
          ("its framed call nodes at the frame's flow (framedNodesAt)", fun _ =>
            framedNodesAt spec.fflowC spec.lay spec.theta spec.framed (requestCode r) eff)]
        if let some (w, _) := reqChecks.find? (!·.2 ()) then
          return s!"framed plan: the binding check of {w} fails"
        return s!"framed plan of {name}: its binding checks pass, its framed call nodes {nodes} keep only supports the frame's check passes, and its main graph's framed walk is accepted; refused: the obligations FramedObligations (the slots' values at the frame's calls, ChkSound, StartInv, EntryFits, NoKeys) are not established"
      | .refused w (some (t, xs)) _ =>
        let held := match g.plans[i]? with
          | some (.ok p) => (p.parts.2.2.candidates.filter fun (q : Nat × List HeapKnowledge.IndexAtom) => q.1 == t).flatMap
              fun (q : Nat × List HeapKnowledge.IndexAtom) => q.2
          | _ => []
        let drop := held.filter xs.contains
        if drop.isEmpty then return s!"framed plan: its framed walk is refused: {firstLine w}"
        g := g.dropCandidates i t drop
      | o => return s!"framed plan: its framed walk is refused: {firstLine (toString o)}"
  return "framed plan: its framed walk is not settled in 12 runs"

/-- **One member's single pass**: a graph plan's (`passMemberGraph`); a
framed plan's check (`framedRefusal`), which refuses it. -/
def FilePlans.passMember (f : FilePlans) (fuel : Nat) (i : Nat) (compare : Bool := false)
    (debugNode : Nat := 1000000000) (repeats : Nat := 1) (given : Option (Std.HashMap String Json) := none)
    (observe : Option String := none) (counting : Bool := false) (grading : Bool := false)
    (framed : List (Nat × List Footprints.Footprint) := []) :
    Except String (MemberRun (EquationStore.CheckedLabel f.F.equations f.F.primitive)
      (CertificateProducer.Answered (StoreView.graph f.F.store))) :=
  match f.plans[i]? with
  | some (.ok (.framed name pos r spec)) => .ok (.before name (.refused (f.framedRefusal fuel i name pos r spec)))
  | _ => f.passMemberGraph fuel i compare debugNode repeats given observe counting grading framed

/-- The node label a pass refusal's text names after `key` (`expression at
node 8: …` names `8`). -/
def refusalLabel (w key : String) : Option Nat :=
  match w.splitOn key with
  | _ :: rest :: _ => (rest.takeWhile Char.isDigit).toNat?
  | _ => none

/-- **A pass refusal, located** (the verdict's text): the obligation a
refusal of the single pass names (`expression at node l`, `return at node
l`, an edge into node `t`, `footprint at node l`, `spine regions at node l`,
`handler of node l`, in the unit's graph or, after `code i: `, in its code `i`'s) at the source
span of its node, in the wording the search's refusal of the same
obligation has (`produceGraphUsing`, `footprintRefusal`, `ensuresRefusal`);
a statement's spine regions refused at their entry conditions (`spine
regions`) at the declaration; none where the refusal names no node with a
source span. -/
def FilePlans.locatedRefusal (f : FilePlans) (i : Nat) (w : String) : Option String := do
  let .ok plan := (f.plans[i]?).getD (.error "") | none
  let (name, _, r) := plan.parts
  let (ci, w) : Option Nat × String := if w.startsWith "code " then
      match (w.drop 5).toString.splitOn ": " with
      | n :: rest => ((n.toNat?), ": ".intercalate rest)
      | [] => (none, w)
    else (none, w)
  let sourceMap : SourceMap := match ci with
    | some c => ((r.codeSources[c]?).map (·.sourceMap)).getD []
    | none => r.sourceMap
  let at_ := fun (l : Nat) => (sourceMap[l]?).bind id
  let what := if ci.isSome then s!"a closure in '{name}'" else s!"'{name}'"
  if w.startsWith "expression at node " then
    let l ← refusalLabel w "expression at node "
    let o ← at_ l
    -- The types the node's claim states (its operands' slots, which the
    -- refused term names as `Tm.var k`, and its result), named by kind
    -- (`SourceTypes.renderIn`); of the unit's own graph only.
    let claimed : String := if ci.isSome then "" else
      match r.claims[l]? with
      | none => ""
      | some c =>
        let G := RequestJson.graph r.toRequest
        let term := ((w.splitOn " with ").head?.getD "")
        let slots := ((term.splitOn "Tm.var ").drop 1).filterMap (fun t => (t.takeWhile Char.isDigit).toNat?) |>.eraseDups
        let operands := slots.filterMap fun k => c.context[k]?.map (SourceTypes.renderIn G)
        let ops := if operands.isEmpty then "" else s!"its operands' claims are {", ".intercalate operands}; "
        s!"\nobligation: {ops}its claim is {SourceTypes.renderIn G c.type}"
    return s!"source expression obligation at [{o.pos.1},{o.pos.2}): evidence search failed: no derivation of its {o.role} claim{claimed}"
  if w.startsWith "return at node " then
    let o ← at_ (← refusalLabel w "return at node ")
    if (w.splitOn ": the promise").length > 1 then
      return s!"source expression obligation at [{o.pos.1},{o.pos.2}): evidence search failed: the promised argument is not within the promise at this return"
    if (w.splitOn ": the postcondition").length > 1 then
      return s!"source ensures refusal at [{o.pos.1},{o.pos.2}): a return of '{name}' does not establish the postcondition stated by its declaration"
    return s!"source expression obligation at [{o.pos.1},{o.pos.2}): evidence search failed: no derivation of its {o.role} claim"
  if w.startsWith "edge from node " || w.startsWith "handler edge from node " then
    let l ← refusalLabel w "edge from node "
    let t ← refusalLabel w " to node " <|> refusalLabel w " into statement entry " <|> refusalLabel w " into node "
    let o ← at_ t
    return s!"source incoming edge obligation at [{o.pos.1},{o.pos.2}): evidence search failed: the edge from node {l} does not establish the claims at this point"
  if w.startsWith "footprint at node " || w.startsWith "footprint by spine regions: " then
    let l ← refusalLabel w "footprint at node "
    let o := at_ l
    let pos := (o.map (·.pos)).getD (f.fr.units[i]?.map (·.1.namePos) |>.getD (0, 0))
    return s!"source effect refusal at [{pos.1},{pos.2}): the footprint claimed for {what} is not established by its body"
  if w.startsWith "spine regions at node " then
    let o ← at_ (← refusalLabel w "spine regions at node ")
    return s!"source effect refusal at [{o.pos.1},{o.pos.2}): the frame stated for {what} is not established by its body: a step changes a location outside its spine regions beyond the statement's bound"
  -- The regions' entry conditions, refused before the walk (`passMember`),
  -- at the declaration, as `effectRefusal` words them.
  if w == "spine regions" then
    let (_, regions) ← r.regional
    let pos := f.fr.units[i]?.map (·.1.namePos) |>.getD (0, 0)
    if !regions.all (GraphCode.ArgumentPathTracking.regionKindOk (RequestJson.graph r.toRequest) r.inputs) then
      return s!"source effect refusal at [{pos.1},{pos.2}): the frame stated for {what} {kindRefusal}"
    if !GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions then
      return s!"source effect refusal at [{pos.1},{pos.2}): the frame stated for {what} reads a spine region through a field that is no present stable field of its parameter's type, or through more than one field"
    return s!"source effect refusal at [{pos.1},{pos.2}): the frame stated for {what} is not established by its body"
  if w.startsWith "handler of node " then
    let o ← at_ (← refusalLabel w "handler of node ")
    return s!"source expression obligation at [{o.pos.1},{o.pos.2}): evidence search failed: no derivation of its {o.role} claim"
  none

/-- A refused step's preconditions as the record's `preconditions` field
states them: the step's form; per precondition, its elements precondition
on the receiver slot and each atom of its index facts at the step's slots
(null where it names a position the step holds no slot for), each with
whether it holds; and the facts connected to the step's slots. -/
def preconditionsJson (d : SinglePass.StepPreconditions) : Json :=
  Json.mkObj [("step", toJson (match d.step with
      | .call => "call" | .construction => "construction" | .write => "write")),
    ("signatures", Json.arr (d.signatures.map fun s => Json.mkObj [
      ("requires", match s.requires with
        | some (x, R, held) => Json.mkObj [("slot", toJson x), ("pred", toJson R), ("entailed", toJson held)]
        | none => Json.null),
      ("atoms", Json.arr (s.atoms.map fun (F, held) =>
        Json.mkObj [("fact", toJson F), ("entailed", toJson held)]).toArray)]).toArray),
    ("known", toJson d.known)]

/-- A refused edge's facts as the record's `edgeFacts` field states them,
all at the target's slots: what the edge is refused for; the facts of the
target's requirement it establishes and those it does not; the facts it
holds over the requirement's slots. -/
def edgeFactsJson {ι : Type} (d : SinglePass.EdgeFacts ι) : Json :=
  Json.mkObj [("requirement", match d.requirement with
      | .facts => Json.mkObj [("kind", toJson "facts")]
      | .implication a b => Json.mkObj [("kind", toJson "implication"), ("test", toJson a), ("target", toJson b)]
      | .inputValue j q => Json.mkObj [("kind", toJson "input-value"), ("slot", toJson j), ("input", toJson q)]
      | .promisedInput j => Json.mkObj [("kind", toJson "promised-input"), ("slot", toJson j)]),
    ("established", toJson d.established), ("lacking", toJson d.lacking), ("known", toJson d.known)]

/-- A return's postcondition facts as the record's `postcondition` field
states them: each fact at the return's pushed slots (null where it names
an input no slot holds the entry value of), with whether the return's
facts entail it; and those facts. -/
def returnFactsJson (d : SinglePass.ReturnFacts) : Json :=
  Json.mkObj [("facts", Json.arr (d.facts.map fun (F, held) =>
      Json.mkObj [("fact", toJson F), ("entailed", toJson held)]).toArray),
    ("known", toJson d.known)]

/-- **The record of a refusal carrying its diagnostic's data**, of unit
`i`'s own graph or, after `code c: `, of its code `c`'s (over that graph's
request and source map, `RequestJson.failureDiagnostic`), the deferred
`detail` forced here: of a step refused for having no derivation
(`expression at node l`) whose preconditions do not all hold, the node's
obligation with the step's preconditions (`preconditionsJson`); of a
return refused for its postcondition, the return's node obligation with
the postcondition's facts (`returnFactsJson`); of an edge refused for what
its target requires (`edge from node l into …`, also as the regional
fallback's refusal), the edge's obligation, its target requiring the facts
it requires, with the edge's facts (`edgeFactsJson`). -/
def FilePlans.refusalRecord (f : FilePlans) (fuel : Nat) (i : Nat) (w : String)
    (detail : Option (Thunk (Option (SinglePass.RefusalDetail (EquationStore.CheckedLabel f.F.equations f.F.primitive))))) :
    Option (List (String × Json)) := do
  let .ok (.graph _ _ r) := (f.plans[i]?).getD (.error "") | none
  -- (the regional fallback's refusal, its walk's refusal after its prefix)
  let w := if w.startsWith "footprint by spine regions: " then (w.drop 28).toString else w
  let (ci, w) : Option Nat × String := if w.startsWith "code " then
      match (w.drop 5).toString.splitOn ": " with
      | n :: rest => (n.toNat?, ": ".intercalate rest)
      | [] => (none, w)
    else (none, w)
  let diagnostic := fun (e : CertificateProducer.Failure _) (requirements : List (Nat × HeapKnowledge.Knowledge))
      (thrown : Option (Ty _)) => match ci with
    | some c => do
      let q ← r.codes[c]?
      let code ← r.codeSources[c]?
      pure (RequestJson.failureDiagnostic (q.asRequest r.toRequest) fuel code.sourceMap e requirements (thrown := thrown))
    | none => pure (RequestJson.failureDiagnostic r.toRequest fuel r.sourceMap e requirements (thrown := thrown))
  if w.startsWith "expression at node " then
    let l ← refusalLabel w "expression at node "
    let .step d ← (← detail).get | none
    guard (d.signatures.any fun s => s.atoms.any (!·.2) || s.requires.any (!·.2.2))
    let fields ← diagnostic (.expression l) [] none
    return fields ++ [("preconditions", preconditionsJson d)]
  if w.startsWith "return at node " then
    let l ← refusalLabel w "return at node "
    let .postcondition d ← (← detail).get | none
    guard (d.facts.any (!·.2))
    let fields ← diagnostic (.expression l) [] none
    return fields ++ [("postcondition", returnFactsJson d)]
  guard (w.startsWith "edge from node ")
  let .edge d ← (← detail).get | none
  let fields ← diagnostic (.edge d.source d.target d.exit) [(d.target, d.required)] d.thrown
  return fields ++ [("edgeFacts", edgeFactsJson d)]

/-- **A pass refusal as a check reports it**: with `located`, the source
obligation it names (`locatedRefusal`) before the pass's own text `raw`,
and, for a refusal carrying its diagnostic's data (`refusalRecord`), that
obligation's record after them; the pass's own text alone otherwise. -/
def FilePlans.placeRefusal (f : FilePlans) (fuel : Nat) (located : Bool) (i : Nat) (w raw : String)
    (detail : Option (Thunk (Option (SinglePass.RefusalDetail (EquationStore.CheckedLabel f.F.equations f.F.primitive))))) :
    String :=
  if !located then raw else match f.locatedRefusal i w with
    | some l => match f.refusalRecord fuel i w detail with
      | some fields => RequestJson.withDiagnostic s!"{l}\n{raw}" fields
      | none => s!"{l}\n{raw}"
    | none => raw

/-- The single forward pass over each member of a group
(`FilePlans.passMember`), no certificate built: per member its line, its
outcome and counts; the group's verdict, the first member's refusal or
construct not handled, else the group's dependencies. -/
def FilePlans.passGroup (f : FilePlans) (fuel : Nat) (group : List Nat) (compare : Bool := false) (debugNode : Nat := 1000000000) (repeats : Nat := 1) (given : Option (Std.HashMap String Json) := none)
    (observe : Option String := none) (counting : Bool := false) (located : Bool := false) :
    List String × Except String (List String) :=
  -- (`located`: a refusal's text the source obligation it names, the
  -- pass's own text on the next line, `FilePlans.locatedRefusal`; a
  -- refusal before the pass named at its unit where it names no place)
  let (lines, failed) := group.foldl (init := (([] : List String), (none : Option String))) fun (lines, failed) i =>
    match f.passMember fuel i compare debugNode repeats given observe counting with
    | .ok m =>
      let failure := match m.outcome with
        | .accepted => none
        | .refused w _ pre => some (f.placeRefusal fuel located i w s!"single pass: {m.outcome} ({w.length})" pre)
        | .notHandled w => some s!"single pass: {m.outcome} ({w.length})"
        | o => some s!"single pass: {o} ({(toString o).length})"
      (lines ++ [s!"{m.name}: {m.outcome}; {m.line}"], failed.orElse fun _ => failure)
    | .error reason =>
      let reason := if !located || (reason.splitOn " at [").length > 1 then reason else
        match f.fr.units[i]? with
        | some (fn, _, _) => s!"source refusal at [{fn.namePos.1},{fn.namePos.2}): {reason}"
        | none => reason
      (lines ++ [s!"refused before the pass: {reason.take 200}"], failed.orElse fun _ => some reason)
  (lines, match failed with
    | some reason => .error reason
    | none => .ok (f.dependencies group))

end Verification.SourceClaimJson
