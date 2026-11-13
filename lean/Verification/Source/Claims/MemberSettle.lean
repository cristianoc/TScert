import Verification.Source.Claims.Json
import Verification.Source.Claims.TypeComparison
import Verification.Source.Claims.HeadInference
import Verification.Source.Claims.RegionInference
import Verification.Source.Claims.InterfaceRows
import Verification.Source.Claims.HeadDiagnosis

/-! A member's runs until accepted or its refusal stands: the loop heads'
given facts and the computed given lines (`withHeadFacts`,
`computedGiven`), a refusal's next state (`inferredNext`), the settle loop
(`inferredSettle`), and mode 8's check of a group (`passGroupMode8`). -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping SourceExtraction
open EquationGraphs (Tree)

/-- The plans with each unit's loop-head facts the given file states
(`headFacts`, `headFactsOfCodes`) as its statement entries' candidates, its
own graph's and each code request's: the search's and the single pass's
given invariants, in place of the claims'. With `entries` (the referee,
mode 9), the other statement entries' facts too (`entryFacts`): the search
holds at each statement entry only what its candidates there give. -/
def FilePlans.withHeadFacts (f : FilePlans) (given : Std.HashMap String Json) (entries : Bool := false)
    (inferred : Bool := false) : FilePlans :=
  { f with plans := f.plans.zipIdx.map fun (p, i) => p.map fun
    | .graph name pos r =>
      let line := given.get? (f.fr.unitId i)
      let field := fun (k : String) => (line.bind fun l => (l.getObjVal? k).toOption)
      let facts := fun (k : String) (sm : RequestJson.SourceMap) (cuts : List Nat) =>
        headFactsFromJson sm cuts ((field k).getD (Json.arr #[]))
      let ofCodes := fun (k : String) (ci : Nat) =>
        (((field k).bind fun cs => (cs.getArr?).toOption).bind (·[ci]?)).getD (Json.arr #[])
      .graph name pos { r with
        -- With `inferred`, the loop heads' proposals the lowering recorded
        -- (`HeadInference`) kept beside the given file's.
        candidates := (if inferred then r.candidates else []) ++ facts "headFacts" r.sourceMap (r.start :: r.cuts) ++
          (if entries then facts "entryFacts" r.sourceMap (r.start :: r.cuts) else [])
        codeSources := r.codeSources.zipIdx.map fun (c, ci) =>
          let start := ((r.codes[ci]?).map fun q => (q.asRequest r.toRequest).start).getD 0
          { c with candidates := headFactsFromJson c.sourceMap (start :: c.cuts) (ofCodes "headFactsOfCodes" ci) ++
            (if entries then headFactsFromJson c.sourceMap (start :: c.cuts) (ofCodes "entryFactsOfCodes" ci) else []) } } }

/-- **The slots holding an input's entry value** at each node: the pairs
`(slot, input)` the seed states at the entry, carried along every edge to
each slot whose mapping reads a slot holding the input, those every
predecessor carries (`GraphCode.trackTable`'s propagation, each node's width
its claimed context's). Untrusted: the pass checks every edge into a head
against the pairs there. -/
def inputsTable (P : ControlFlow.Program) (widths : Array Nat) (start : Nat) (seed : GraphCode.Tracked) :
    List (Option GraphCode.Tracked) := Id.run do
  let mut table : Array (Option GraphCode.Tracked) := Array.replicate P.length none
  table := table.set! start (some seed)
  for _ in List.range (2 * P.length + 2) do
    let mut changed := false
    for (node, l) in P.zipIdx do
      let some here := table.getD l none | continue
      for e in GraphCode.edgesOf node.continuation node.handler do
        let sources := if e.2 then GraphCode.shiftTracked here else here
        let carried := (List.range (widths.getD e.1.label 0)).flatMap fun i =>
          sources.filterMap fun p => if p.1 == PointClaims.slot e.1.mapping i then some (i, p.2) else none
        let current := table.getD e.1.label none
        let merged := match current with
          | none => some carried
          | some old => some (old.filter carried.contains)
        if merged != current then
          table := table.set! e.1.label merged
          changed := true
    if !changed then break
  return table.toList

/-- **The implications a statement entry is proposed to hold**
(`PromiseCalls.Implication`, the given lines' `implies`): of each
`branchBind` whose `true` edge's target claims a slot at a type other than
the one the edge's source context holds there (a binding the test narrows
through a constant holding its value: `const p = x === 'a'; … if (p)`
claims `x : 'a'` on the `true` arm), `p = true ⟹ x : T`, `T` the target's
claim, at each statement entry whose source span holds the test's or ends
before it and whose context describes both bindings, by descriptor. The search guesses at a
loop's head, in its first waiting round, the implications its entry edge
establishes (`CertificateProducer`'s `meetImplications` over the stating
edges); these are the ones a branch inside the loop reads. Untrusted: the
pass checks each on every edge into the entry (`SinglePass.run`, "an
implication"), and the front drops those an edge refuses
(`passGroupInferred`). -/
def branchImplications {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι] (r : SourceRequest σ ι) :
    List (Nat × List (PromiseCalls.Implication ι)) :=
  let entryAt := fun (l : Nat) => ((r.sourceMap[l]?).bind id : Option RequestJson.SourceMapEntry)
  let narrowed := r.program.zipIdx.flatMap fun (node, l) => match node.continuation with
    | .branchBind y _ => match r.claims[l]?, r.claims[y.label]?, entryAt l, entryAt y.label with
      | some c, some cy, some e, some ey =>
        let Γ := c.type :: c.context
        let width := cy.context.length
        match (List.range width).find? (PointClaims.slot y.mapping · == 0) with
        | none => []
        | some tested => match ey.context[tested]? with
          | some dt => if !dt.describes then [] else
            (List.range width).filterMap fun a => do
              guard (a != tested)
              let B ← cy.context[a]?
              let da ← ey.context[a]?
              guard da.describes
              guard (Γ[PointClaims.slot y.mapping a]? != some B)
              pure (e.pos, dt, da, B)
          | none => []
      | _, _, _, _ => []
    | _ => []
  let within := fun (a b : Nat × Nat) => b.1 ≤ a.1 && a.2 ≤ b.2
  if narrowed.isEmpty then [] else
  r.cuts.filterMap fun h => do
    let eh ← entryAt h
    let xs := narrowed.filterMap fun (p, dt, da, B) => do
      -- (a head holding the branch, or one before it whose context holds
      -- both bindings: the cut the implication crosses to reach the branch)
      guard (within p eh.pos || eh.pos.2 ≤ p.1)
      let t ← eh.context.findIdx? (· == dt)
      let a ← eh.context.findIdx? (· == da)
      pure (⟨t, a, B⟩ : PromiseCalls.Implication ι)
    -- (one per tested and narrowed slot: the first branch's)
    let xs := xs.foldl (fun (acc : List (PromiseCalls.Implication ι)) x =>
      if acc.any fun y => y.test == x.test && y.target == x.target then acc else acc ++ [x]) []
    if xs.isEmpty then none else some (h, xs)

/-- Each unit of `group`'s given line computed from its plan where `given` has none: for
a unit whose postcondition names inputs (`@ensures`), the slots holding each
input's entry value at its statement entries (`inputsTable` from
`GraphCode.namedInputs`), the `graph` rows' `inputs` the pass reads; at its
statement entries, the implications its branches read
(`branchImplications`), the rows' `implies`; with `falseImplications`
(`TSCERT_FORCE=head-implications`), each also stated at `undefined`
(`p = true ⟹ x : undefined`), the adversarial implication the pass's edge
check refuses. With
`falseInputs` (`TSCERT_FORCE=head-inputs`), each pair also restated at the
next slot (`(s + 1, q)` beside `(s, q)`), the adversarial pair the pass's
edge check refuses, in place of a given line's. The regional checks'
tables at its statement entries (`regionalLines`), its `regional` and
`footprintRegional`; with `falseRegional` (`TSCERT_FORCE=head-region-…`),
an entry of that kind no edge establishes added at each. -/
def FilePlans.computedGiven (f : FilePlans) (given : Std.HashMap String Json) (falseInputs : Bool := false)
    (falseImplications : Bool := false) (falseRegional : Option String := none) (group : List Nat) :
    Std.HashMap String Json :=
  f.plans.zipIdx.foldl (init := given) fun m (p, i) =>
    let u := f.fr.unitId i
    -- (only the group's members: a member's run reads its own line alone,
    -- `passMember`)
    if !group.contains i then m else
    -- (forced, the given file's line replaced: the control holds beside it too)
    if m.contains u && !falseInputs && !falseImplications && falseRegional.isNone then m else match p with
    | .ok (.graph _ _ r) =>
      let implied := (branchImplications r).map fun (l, xs) =>
        (l, if falseImplications then xs ++ xs.map fun (x : PromiseCalls.Implication _) =>
          ({ x with type := [LabelStore.Labels.undef] } : PromiseCalls.Implication _) else xs)
      -- The regional checks' tables at the statement entries
      -- (`regionalLines`).
      let regional := regionalLines r falseRegional
      if r.ensures.isEmpty && implied.isEmpty && regional.isEmpty then m else
      let widths := (r.claims.map (·.context.length)).toArray
      let table := if r.ensures.isEmpty then [] else inputsTable r.program widths r.start (GraphCode.namedInputs r.ensures)
      let inputs := table.zipIdx.filterMap fun (t, l) => match t with
        | some ps@(_ :: _) => if l == r.start || r.cuts.contains l then
            let ps := if falseInputs && l != r.start then
              ps ++ ps.filterMap fun (s, q) => if s + 1 < widths.getD l 0 && !ps.contains (s + 1, q) then some (s + 1, q) else none
              else ps
            some (l, ps) else none
        | _ => none
      let rows := ((inputs.map (·.1)) ++ implied.map (·.1)).eraseDups.map fun l =>
        let ps := ((inputs.find? (·.1 == l)).map (·.2)).getD []
        let xs := ((implied.find? (·.1 == l)).map (·.2)).getD []
        Json.mkObj [("label", toJson l), ("implies", Json.arr (xs.map fun x => Json.mkObj [("test", toJson x.test),
            ("target", toJson x.target), ("type", toJson x.type)]).toArray), ("arguments", Json.arr #[]),
          ("inputs", toJson (ps.map fun (a, b) => [a, b]))]
      m.insert u (Json.mkObj ([("unit", toJson u), ("graph", Json.arr rows.toArray), ("codes", Json.arr #[])] ++ regional))
    | .error _ => m

/-- The given file's loop-head facts of plan `i` (`headFacts`), by label:
the candidates no rerun drops. -/
def FilePlans.givenAt (f : FilePlans) (given : Std.HashMap String Json) (i : Nat) :
    List (Nat × List HeapKnowledge.IndexAtom) :=
  match f.plans[i]?, given.get? (f.fr.unitId i) with
  | some (.ok (.graph _ _ r)), some line =>
    headFactsFromJson r.sourceMap (r.start :: r.cuts) ((line.getObjVal? "headFacts").toOption.getD (Json.arr #[]))
  | _, _ => []

/-- Plan `i`'s candidates at label `l` less `drop`. -/
def FilePlans.dropCandidates (f : FilePlans) (i l : Nat) (drop : List HeapKnowledge.IndexAtom) : FilePlans :=
  { f with plans := f.plans.zipIdx.map fun (p, j) => if j != i then p else p.map fun
    | .graph name pos r => .graph name pos { r with candidates := r.candidates.map fun (l', as) =>
        if l' == l then (l', as.filter (!drop.contains ·)) else (l', as) } }

/-- The candidates of plan `i` at the heads that read the facts of the head
at label `l` (each a label whose source span lies inside `l`'s, or after it
inside the loop holding `l`'s, the walk carrying a head's facts past its
loop) that state a fact of `drop` over the same bindings: each atom's slots
carried by their descriptors from `l`'s context to the other head's, by
label. -/
def FilePlans.laterDrops (f : FilePlans) (i l : Nat) (drop : List HeapKnowledge.IndexAtom) :
    List (Nat × List HeapKnowledge.IndexAtom) :=
  match f.plans[i]? with
  | some (.ok (.graph _ _ r)) =>
    let entryAt := fun (l : Nat) => ((r.sourceMap[l]?).bind id : Option RequestJson.SourceMapEntry)
    match entryAt l with
    | none => []
    | some e =>
      let within := fun (a b : Nat × Nat) => b.1 ≤ a.1 && a.2 ≤ b.2 && a != b
      -- (the innermost head's span holding `l`'s)
      let outer := (r.candidates.filterMap fun (l', _) => (entryAt l').bind fun e' =>
        if within e.pos e'.pos then some e'.pos else none).foldl (fun (acc : Option (Nat × Nat)) p =>
          match acc with
          | some q => if within p q then some p else some q
          | none => some p) none
      r.candidates.filterMap fun (l', as) =>
        if l' == l || as.isEmpty then none else match entryAt l' with
        | none => none
        | some e' =>
          let after := e.pos.2 ≤ e'.pos.1 && (outer.map fun q => within e'.pos q).getD true
          if !(within e'.pos e.pos || after) then none else
          let σ := fun (s : Nat) => do
            let d ← e.context[s]?
            if !d.describes then none else e'.context.findIdx? (· == d)
          let moved := drop.filterMap fun (a : HeapKnowledge.IndexAtom) => do
            pure { a with fact := ← a.fact.mapM σ, cond := ← a.cond.mapM σ }
          match moved.filter as.contains with
          | [] => none
          | ds => some (l', ds)
  | _ => []

/-- An edge's refusal into a statement entry for an implication it does not
establish (`SinglePass.run`): the entry's label. -/
def implicationAt (why : String) : Option Nat :=
  match why.splitOn "into statement entry " with
  | _ :: rest :: _ => match rest.splitOn ": an implication" with
    | t :: _ :: _ => t.toNat?
    | _ => none
  | _ => none

/-- The given line of unit `u` with the implications at label `l` left out. -/
def withoutImplications (given : Std.HashMap String Json) (u : String) (l : Nat) : Option (Std.HashMap String Json) := do
  let line ← given.get? u
  let rows ← ((line.getObjVal? "graph").bind Json.getArr?).toOption
  let at_ := fun (row : Json) => (row.getObjValAs? Nat "label").toOption == some l
  let held := rows.any fun row => at_ row &&
    (((row.getObjVal? "implies").bind Json.getArr?).toOption.map (!·.isEmpty)).getD false
  guard held
  let rows := rows.map fun row => if at_ row then row.setObjVal! "implies" (Json.arr #[]) else row
  pure (given.insert u (line.setObjVal! "graph" (Json.arr rows)))

/-- The given line of unit `u` with its regional checks' tables
(`regional`, `footprintRegional`) left out, where it states any. -/
def withoutRegional (given : Std.HashMap String Json) (u : String) : Option (Std.HashMap String Json) := do
  let line ← given.get? u
  let .obj kvs := line | none
  guard (kvs.contains "regional" || kvs.contains "footprintRegional")
  pure (given.insert u (.obj ((kvs.erase "regional").erase "footprintRegional")))

/-- A member's run as the inferred route reads it (`passGroup`'s wording):
its line, its refusal where refused, and its failure, the refusal's text
located with `located` (`FilePlans.locatedRefusal`). -/
def FilePlans.inferredRun (g : FilePlans) (fuel : Nat) (compare : Bool) (debugNode repeats : Nat)
    (observe : Option String) (counting located : Bool) (given : Option (Std.HashMap String Json)) (i : Nat) :
    String × Option (String × Option (Nat × List HeapKnowledge.IndexAtom)) × Option String :=
  match g.passMember fuel i compare debugNode repeats given observe counting with
  | .ok m =>
    let failure := match m.outcome with
      | .accepted => none
      | .refused w _ =>
        let raw := s!"single pass: {m.outcome} ({w.length})"
        some (if !located then raw else match g.locatedRefusal i w with
          | some l => s!"{l}\n{raw}"
          | none => raw)
      | .notHandled w => some s!"single pass: {m.outcome} ({w.length})"
      | o => some s!"single pass: {o} ({(toString o).length})"
    let why := match m.outcome with
      | .refused w lacks => some (w, lacks)
      | _ => none
    (s!"{m.name}: {m.outcome}; {m.line}", why, failure)
  | .error reason =>
    let reason := if !located || (reason.splitOn " at [").length > 1 then reason else
      match g.fr.units[i]? with
      | some (fn, _, _) => s!"source refusal at [{fn.namePos.1},{fn.namePos.2}): {reason}"
      | none => reason
    (s!"refused before the pass: {reason.take 200}", none, some reason)

/-- What a refusal `w` of member `i`'s run calls for (its text, and the entry
and lacking facts of a refusal of an edge into a statement entry, as data):
the plans and given lines of its next run, the lines saying what was left
out and how many facts, or none where the refusal stands. An implication an
edge refuses: the entry's proposed ones left out. A regional check refused
at the tables inferred for it (`regionalLines`), stating no lacking facts:
the member without them, as with no given line. An edge into a statement
entry lacking facts, on any route (the regional fallback's included): the
candidates there among the lacking facts left out, the given file's
(`protect`) kept, and the same facts at the heads that read that head's
facts (`laterDrops`); a refusal lacking none of them stands. With `fixed` (an adversarial proposal forced)
the forced fact is never left out, nor an implication or a regional table. -/
def FilePlans.inferredNext (f : FilePlans) (fixed : Bool) (protect : List (Nat × List HeapKnowledge.IndexAtom))
    (given : Option (Std.HashMap String Json)) (i : Nat) (w : String × Option (Nat × List HeapKnowledge.IndexAtom)) :
    Option (FilePlans × Option (Std.HashMap String Json) × List String × Nat) :=
  if let some l := implicationAt w.1 then
    if fixed then none else do
    let g ← given.bind (withoutImplications · (f.fr.unitId i) l)
    pure (f, some g, [s!"inferred heads: dropped at {l}: its implications"], 1)
  -- (a refusal stating the facts an edge lacks is that edge's, whichever
  -- route's run made it: the regional fallback's included)
  else if w.2.isNone && (w.1.splitOn "store regions").length > 1 then
    if fixed then none else do
    let g ← given.bind (withoutRegional · (f.fr.unitId i))
    pure (f, some g, ["inferred heads: dropped the regional tables"], 0)
  else do
    let (l, missing) ← w.2
    let candidates := match f.plans[i]? with
      | some (.ok (.graph _ _ r)) => r.candidates
      | _ => []
    let held := (candidates.filter (·.1 == l)).flatMap (·.2)
    let kept := (protect.filter (·.1 == l)).flatMap (·.2)
    -- (forced: the adversarial fact, a term at most `-1`, a store or a
    -- region apart from itself or every element at most `-1`, kept)
    let forced := fun (a : HeapKnowledge.IndexAtom) => fixed && match a.fact with
      | .linear (.le [(_, 1)] (-1)) => true
      | .storeApart a p b q => a == b && p == q
      | .apart a b => a == b
      | .every _ _ _ [.atom (.le [(.elem, 1)] (-1))] => true
      | _ => false
    let open_ := held.filter fun a => !kept.contains a && !forced a
    guard !open_.isEmpty
    -- The candidates the edge lacks; a refusal lacking only facts no
    -- rerun leaves out (written, kept or forced) stands.
    let drop := open_.filter missing.contains
    guard !drop.isEmpty
    let shown := fun (a : HeapKnowledge.IndexAtom) => (reprStr a.fact).replace "\n" " " |>.replace "  " ""
    let f₁ := f.dropCandidates i l drop
    -- A fact an edge into a head refuses is left out at the heads that
    -- read that head's facts too (`laterDrops`: nested in its loop, or
    -- after it in the loop holding it), over the same bindings, the given
    -- file's kept: the pass would refuse it there in turn, a run each.
    let later := (f₁.laterDrops i l drop).filterMap fun (l', ds) =>
      let kept' := (protect.filter (·.1 == l')).flatMap (·.2)
      let ds := ds.filter fun a => !kept'.contains a && !forced a
      if ds.isEmpty then none else some (l', ds)
    let f₂ := later.foldl (fun (g : FilePlans) (l', ds) => g.dropCandidates i l' ds) f₁
    let lines := drop.map (fun a => s!"inferred heads: dropped at {l}: {shown a}") ++
      later.flatMap fun (l', ds) => ds.map fun a => s!"inferred heads: dropped at {l'} (later): {shown a}"
    let dropped := drop.length + (later.map (·.2.length)).sum
    pure (f₂, given, lines, dropped)

/-- Plan `i` with the candidates `ds` names left out, head by head. -/
def FilePlans.dropAll (f : FilePlans) (i : Nat) (ds : List (Nat × List HeapKnowledge.IndexAtom)) : FilePlans :=
  ds.foldl (fun (g : FilePlans) (x : Nat × List HeapKnowledge.IndexAtom) => g.dropCandidates i x.1 x.2) f

/-- **A refusal's next state, every lacking proposal left out at once**:
`inferredNext`'s, then the proposals the diagnosing walk over it finds
lacking on some edge into their head (`lackingAt`, the given file's
facts `protect` kept), those facts at the heads that read their head's
(`laterDrops`), and the implications of the heads it finds refusing one,
left out. With `fixed` (an adversarial proposal forced),
`inferredNext`'s alone. -/
def FilePlans.inferredNextAll (f : FilePlans) (fuel : Nat) (fixed : Bool)
    (protect : List (Nat × List HeapKnowledge.IndexAtom)) (given : Option (Std.HashMap String Json)) (i : Nat)
    (w : String × Option (Nat × List HeapKnowledge.IndexAtom)) :
    Option (FilePlans × Option (Std.HashMap String Json) × List String × Nat) :=
  match f.inferredNext fixed protect given i w with
  | none => none
  | some (f₁, g₁, ls, d) =>
    if fixed then some (f₁, g₁, ls, d) else
    let candidates := match f₁.plans[i]? with
      | some (.ok (.graph _ _ r)) => r.candidates
      | _ => []
    let droppable := fun (l : Nat) =>
      let kept := (protect.filter (·.1 == l)).flatMap (·.2)
      ((candidates.filter (·.1 == l)).flatMap (·.2)).filter (!kept.contains ·)
    let all := SinglePass.timedKind "inferred heads: diagnosing walk" fun _ =>
      SinglePass.work "check: diagnosing walk" (f₁.fr.workItem i) fun _ => f₁.lackingAt fuel i g₁ droppable
    let lacking := all.filterMap fun (l, x) => x.map (l, ·)
    let implied := (all.filterMap fun (l, x) => if x.isNone then some l else none).eraseDups
    let g₂ := implied.foldl (fun (g : Option (Std.HashMap String Json)) l =>
      match g.bind (withoutImplications · (f₁.fr.unitId i) l) with
      | some g' => some g'
      | none => g) g₁
    let heads := (lacking.map (·.1)).eraseDups
    let found := heads.map fun l => (l, ((lacking.filter (·.1 == l)).flatMap (·.2)).eraseDups)
    let later := found.flatMap fun (l, drop) => (f₁.laterDrops i l drop).filterMap fun (l', ds) =>
      let kept := (protect.filter (·.1 == l')).flatMap (·.2)
      let ds := ds.filter (!kept.contains ·)
      if ds.isEmpty then none else some (l', ds)
    let shown := fun (a : HeapKnowledge.IndexAtom) => (reprStr a.fact).replace "\n" " " |>.replace "  " ""
    let lines := implied.map (fun l => s!"inferred heads: dropped at {l} (lacking): its implications") ++
      found.flatMap (fun (l, ds) => ds.map fun a => s!"inferred heads: dropped at {l} (lacking): {shown a}") ++
      later.flatMap fun (l', ds) => ds.map fun a => s!"inferred heads: dropped at {l'} (later): {shown a}"
    some (f₁.dropAll i (found ++ later), g₂, ls ++ lines,
      d + implied.length + (found.map (·.2.length)).sum + (later.map (·.2.length)).sum)

/-- What `settleInferred` ends with: the last state and given lines, the
lines saying what was left out, the facts dropped, the runs made, and the
last run. -/
structure Settled (S G R : Type) where
  state : S
  given : G
  lines : List String
  dropped : Nat
  runs : Nat
  last : R

/-- A member's runs until one is accepted or its refusal stands, at most
`n + 1`: each run `run` of the current plans and given lines, made once and
both read for its refusal and returned, a refusal's next state from
`next`. -/
def settleInferred {S G R W : Type} (run : S → G → R) (refusal : R → Option W)
    (next : S → G → W → Option (S × G × List String × Nat)) :
    Nat → S → G → List String → Nat → Nat → Settled S G R
  | 0, f, g, ls, d, runs => ⟨f, g, ls, d, runs + 1, run f g⟩
  | n + 1, f, g, ls, d, runs =>
    let r := run f g
    match refusal r with
    | none => ⟨f, g, ls, d, runs + 1, r⟩
    | some w => match next f g w with
      | none => ⟨f, g, ls, d, runs + 1, r⟩
      | some (f', g', ls', d') => settleInferred run refusal next n f' g' (ls ++ ls') (d + d') (runs + 1)

/-- Member `i`'s runs (`settleInferred`): each `inferredRun`, a refusal's
next state from `inferredNextAll`, at most `4·h + 4` of a member with `h`
statement entries holding candidates. -/
def FilePlans.inferredSettle (f : FilePlans) (fuel : Nat) (keep : Nat → List (Nat × List HeapKnowledge.IndexAtom))
    (fixed compare : Bool) (debugNode repeats : Nat) (observe : Option String) (counting located : Bool)
    (given : Option (Std.HashMap String Json)) (i : Nat) :
    Settled FilePlans (Option (Std.HashMap String Json))
      (String × Option (String × Option (Nat × List HeapKnowledge.IndexAtom)) × Option String) :=
  let candidates : List (Nat × List HeapKnowledge.IndexAtom) := match f.plans[i]? with
    | some (.ok (.graph _ _ r)) => r.candidates
    | _ => []
  let heads := (candidates.filter fun (c : Nat × List HeapKnowledge.IndexAtom) => !c.2.isEmpty).length
  settleInferred
    (fun (g : FilePlans) gv => SinglePass.work "check: member run" (f.fr.workItem i) fun _ =>
      g.inferredRun fuel compare debugNode repeats observe counting located gv i)
    (fun res => res.2.1)
    (fun (g : FilePlans) gv w => g.inferredNextAll fuel fixed (keep i) gv i w)
    (4 * heads + 3) f given [] 0 0

/-- The state `passGroupInferred` carries across a group's members: the
plans, the given lines, the lines printed, the first failure, the facts
dropped and the runs made. -/
structure InferredAcc where
  plans : FilePlans
  given : Option (Std.HashMap String Json)
  lines : List String
  failed : Option String
  dropped : Nat
  runs : Nat

/-- One member `i` of `passGroupInferred`'s fold: its runs until accepted
or its refusal stands (`settleInferred`, `inferredNext`), at most `4·h + 4`
of a member with `h` statement entries holding candidates. -/
def FilePlans.inferredStep (fuel : Nat) (keep : Nat → List (Nat × List HeapKnowledge.IndexAtom)) (fixed compare : Bool)
    (debugNode repeats : Nat) (observe : Option String) (counting located : Bool) (acc : InferredAcc) (i : Nat) :
    InferredAcc :=
  let observe' := if observe == some "heads" then none else observe
  let f := acc.plans
  let candidates : List (Nat × List HeapKnowledge.IndexAtom) := match f.plans[i]? with
    | some (.ok (.graph _ _ r)) => r.candidates
    | _ => []
  let shown : List String := if observe != some "heads" then [] else
    let names := fun (l : Nat) => match f.plans[i]? with
      | some (.ok (.graph _ _ r)) =>
        ((((r.sourceMap[l]?).bind id).map fun (e : RequestJson.SourceMapEntry) =>
          e.context.map RequestJson.Descriptor.name).getD [])
      | _ => []
    let span := fun (l : Nat) => match f.plans[i]? with
      | some (.ok (.graph _ _ r)) => (((r.sourceMap[l]?).bind id).map (RequestJson.SourceMapEntry.pos))
      | _ => none
    candidates.flatMap fun (l, as) =>
      s!"inferred heads: span at {l}: {span l}" :: s!"inferred heads: slots at {l}: {names l}" :: as.map fun a =>
        s!"inferred heads: at {l}: {(reprStr a.fact).replace "\n" " " |>.replace "  " ""}"
  let s := f.inferredSettle fuel keep fixed compare debugNode repeats observe' counting located acc.given i
  { plans := s.state, given := s.given, lines := acc.lines ++ shown ++ s.lines ++ [s.last.1],
    failed := acc.failed.orElse fun _ => s.last.2.2, dropped := acc.dropped + s.dropped, runs := acc.runs + s.runs }

/-- **The pass over a group with proposed loop-head facts dropped where an
edge refuses them** (`passGroup`'s verdicts and lines): each member run
until accepted or its refusal stands (`inferredStep`). Each run is the pass
over the member's plan, so its verdict is the pass's on the facts that run
states: an accepted run needs no other. Beside the lines and the verdict,
the facts dropped and the runs made. -/
def FilePlans.passGroupInferred (f : FilePlans) (fuel : Nat) (group : List Nat)
    (keep : Nat → List (Nat × List HeapKnowledge.IndexAtom)) (fixed : Bool := false) (compare : Bool := false)
    (debugNode : Nat := 1000000000) (repeats : Nat := 1) (given : Option (Std.HashMap String Json) := none)
    (observe : Option String := none) (counting : Bool := false) (located : Bool := false) :
    List String × Except String (List String) × Nat × Nat :=
  let acc := group.foldl (FilePlans.inferredStep fuel keep fixed compare debugNode repeats observe counting located)
    ⟨f, given, [], none, 0, 0⟩
  (acc.lines, (match acc.failed with
    | some reason => .error reason
    | none => .ok (acc.plans.dependencies group)), acc.dropped, acc.runs)

/-- **Mode 8's check of a group**: with `infer` (no given file, or a forced
head proposal), the given lines inference computes (`computedGiven`) and the
region separations allocations state at the group's loop heads
(`withFreshApart`), the pass run with proposed facts dropped where an edge
refuses them (`passGroupInferred`, the given file's facts `keep` kept);
else the pass at the given lines (`passGroup`). Beside the lines and the
verdict, the facts dropped and the runs made. -/
def FilePlans.passGroupMode8 (f : FilePlans) (infer : Bool) (force : List String)
    (keep : Nat → List (Nat × List HeapKnowledge.IndexAtom)) (fuel : Nat) (group : List Nat)
    (compare : Bool := false) (debugNode : Nat := 1000000000) (repeats : Nat := 1)
    (given : Option (Std.HashMap String Json) := none) (observe : Option String := none)
    (counting : Bool := false) (located : Bool := false) :
    List String × Except String (List String) × Nat × Nat :=
  if infer then
    let given := some (f.computedGiven (given.getD {}) (force.contains "head-inputs")
      (force.contains "head-implications") (force.find? (·.startsWith "head-region-")) group)
    (f.withFreshApart (force.contains "head-apart") group).passGroupInferred fuel group keep
      (force.any (·.startsWith "head-")) compare debugNode repeats given observe counting located
  else
    let r := f.passGroup fuel group compare debugNode repeats given observe counting located
    (r.1, r.2, 0, 0)

/-- The plans with a false fact (`x - x ≤ -1` over slot 0) supplied at each
graph's start, the adversarial proposal of `TSCERT_FORCE=start-facts`: the
pass's entry check refuses it. -/
def FilePlans.withFalseStartFact (f : FilePlans) : FilePlans :=
  let fact : HeapKnowledge.IndexAtom :=
    { fact := .linear (.le [(HeapKnowledge.Term.value 0, 1), (HeapKnowledge.Term.value 0, -1)] (-1)) }
  { f with plans := f.plans.map fun p => p.map fun
    | .graph name pos r => .graph name pos { r with candidates := (r.start, [fact]) :: r.candidates } }

end Verification.SourceClaimJson
