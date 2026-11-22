import Verification.Source.Claims.Json
import Verification.Types.InhabitedTypes
import Verification.Source.Claims.FramedFlow
import Verification.Source.EffectCodec
import Verification.Semantics.Survival
import Verification.Paper.TolerantFrames.ReadOnlyFlowSolve
import Verification.Paper.TolerantFrames.ReadOnlyCallFrame
import Verification.Paper.TolerantFrames.ReadOnlyCharges

/-! # The flow of a unit's codes, probed

A diagnostic (`TSCERT_FLOW_PROBE`): for each member of a group, the flow the
read-only frame's checks read (`ReadOnly.SolveStart.propose`, the flow
`ReadOnly.solveFlow` proposes) of its component's codes and the closures
they create, and, at the marks the flow gives (`FFlow.MarksFrom`), whether
its checks hold (`ReadOnly.FFlow.check`, the nodes they refuse), each
entry's start (`FFlow.entryB`) and the marks' conditions (`FFlow.marksB`).
With `TSCERT_FRAME_PROBE` naming a
file of facts, at each call of outside code it names, the frame's check
(`frameCheckAt`) of each fact's support (`Footprints.linearSupport`), part
by part. It decides nothing a verdict reads. -/
namespace Verification.SourceClaimJson
open Lean Verification.TolerantFrames.ReadOnly ControlFlow

def markName {ofC : ComponentTag → Bool} {O : List (Option Nat)} (s : Option Nat) : String :=
  match s with
  | none => "outside"
  | some n => match (markedPackage ofC O).mark n with
    | .local => s!"{n} local" | .released => s!"{n} released" | .internal => s!"{n} internal"
    | .exposed => s!"{n} exposed"

/-- A fact of the frame probe: a linear fact over source variables. -/
structure FrameFact where
  name : String
  terms : List (String × List String × HeapKnowledge.Term.Kind × Int)
  bound : Int
  ne : Bool

/-- The frame probe's request for a member: the source offset of the calls
it reads (the start of the call's node), the call's effect, the facts. -/
structure FrameSpec where
  unit : String
  at_ : Nat
  effect : Footprints.Footprint
  facts : List FrameFact
  /-- Also evaluate the predicate at the named call when no outside-call
  obligation arises there. -/
  inspect : Bool := false

def frameSpecs (j : Json) : Except String (List FrameSpec) := do
  let arr ← j.getArr?
  arr.toList.mapM fun u => do
    let facts ← (← u.getObjVal? "facts").getArr?
    let facts ← facts.toList.mapM fun f => do
      let terms ← (← f.getObjVal? "terms").getArr?
      let terms ← terms.toList.mapM fun t => do
        let path ← (← t.getObjVal? "path").getArr?
        pure (← t.getObjValAs? String "var", ← path.toList.mapM (·.getStr?),
          ← EffectCodec.kindOf (← t.getObjVal? "kind"), ← t.getObjValAs? Int "coeff")
      pure ⟨← f.getObjValAs? String "name", terms, ← f.getObjValAs? Int "bound",
        (f.getObjValAs? Bool "ne").toOption.getD false⟩
    pure ⟨← u.getObjValAs? String "unit", ← u.getObjValAs? Nat "at",
      ← EffectCodec.frameOf 64 (← u.getObjVal? "effect"), facts, (u.getObjValAs? Bool "inspect").toOption.getD false⟩

/-- **The frame's check at each call the spec names**, in the code `c` of a
flow, of graph `m` and source map `sm` (`frameCheckAt`, at the class
query, the probe's protocol and each region's keys, no region read as
protected): per call node, per fact, its result, and each part its
support's regions may have that fails, with the check it fails. The check
is required at each node of the call node's continuation and handler (a
frame of that node runs at one of them, `NodeOf`) where the node may call
outside code (`CodeFlow.out`, `ClientFrame.framed_at_call`), read at that
node's slots; elsewhere it is not required. -/
def probeFrames {ofC : ComponentTag → Bool} (O : List (Option Nat)) (F : FFlow (markedPackage ofC O))
    (ΨC : Protocol (markedPackage ofC O)) (lay : List (Nat × Bool × Nat × Nat)) (host : Nat → Bool)
    (c : FCode (markedPackage ofC O)) (m : Code)
    (sm : RequestJson.SourceMap) (sp : FrameSpec) : List String :=
  let top := flowSites F
  -- the calls of a node: its callee's, receiver's and arguments' sets
  let callsAt (l : Nat) : List (Sites (markedPackage ofC O) × Sites (markedPackage ofC O) × List (Sites (markedPackage ofC O))) :=
    match m.1[l]?, m.2[l]? with
    | some e, some kx => callSets F top (c.node l).envAt (fun i => c.sigAt ((c.node l).fnAt i)) (c.flow.at l kx)
        (c.node l).cx 0 (fun _ => none) e
    | _, _ => []
  -- a framed call: a call of the node reaches outside code
  let framedAt (l : Nat) : Bool := (callsAt l).any fun (f, _, _) => reachesOut F top (segCodes F top host f) f
  let names (l : Nat) : List String := ((sm[l]?).bind id).map (·.context.map (·.name)) |>.getD []
  let calls := m.1.zipIdx.filterMap fun (e, l) => match e with
    | .invoke (.var j) _ _ => if ((c.node l).fnAt j).isNone then some (l, j) else none
    | _ => none
  let pos (l : Nat) : String := match (sm[l]?).bind id with
    | some en => s!"{en.pos}"
    | none => "none"
  s!"frame probe, {sp.unit}: calls of a slot naming no signature (node, callee slot, source span) {calls.map fun (l, j) => (l, j, pos l)}" ::
  m.1.zipIdx.flatMap fun (e, l₀) => match e with
    | .invoke _ _ _ =>
      let pos := ((sm[l₀]?).bind id).map (·.pos.1)
      if pos != some sp.at_ then [] else
      -- the nodes a frame of this node's continuation and handler may run at
      let kx := m.2[l₀]?
      let sharing := (List.range m.2.length).filter fun l => m.2[l]? == kx
      let required := sharing.filter fun l => (c.node l).out || framedAt l
      let slotOf (x : String) : Option Nat := (names l₀).idxOf? x
      -- the call's protocol Ψ_c = Ψ_C ⊔ Θ_C ⊔ W_c, at Θ_C = keep (no `@clients` row)
      let (Sf, Sr, args) := (callsAt l₀).head?.getD ([], [], [])
      let seg := segCodes F top host Sf
      let L := callReach F lay Sf Sr args
      let Wc := depthCharges F L
      let Ψ : Protocol (markedPackage ofC O) := fun p => Footprints.Change.max (ΨC p) (Wc p)
      s!"frame probe, {sp.unit}, at node {l₀} (nodes of its continuation and handler {sharing}, which may call outside code or make a framed call {required}; framed {framedAt l₀}; seg {seg}; L(c) {(L.map (markName (ofC := ofC) (O := O)))})" ::
      if required.isEmpty && !sp.inspect then
        sp.facts.map fun ff => s!"  {ff.name}: not required, no node of the call's continuation and handler may call outside code here"
      else (if required.isEmpty then [l₀] else required).flatMap fun l =>
      let τ := (c.node l).envAt
      let slotSites := (List.range (names l₀).length).map fun i => ((names l₀)[i]?.getD "", τ i)
      (if required.isEmpty then s!"frame probe, {sp.unit}, inspected at node {l}"
       else s!"frame probe, {sp.unit}, read at node {l}: slots {repr slotSites}") ::
      sp.facts.map fun ff =>
        match ff.terms.mapM (fun (x, p, k, a) => (slotOf x).map fun i => (HeapKnowledge.Term.now k i p, a)) with
        | none => s!"  {ff.name}: a variable is not a slot here"
        | some G =>
          let fact : Linear.Fact HeapKnowledge.Term := if ff.ne then .ne G ff.bound else .le G ff.bound
          let S := Footprints.linearSupport {} fact
          let ok := frameCheckAt classQuery Ψ sp.effect S F.flow.H τ (fun _ => false)
          let per := S.map fun (r, δ) =>
            match regionSites F.flow.H τ r with
            | none => s!"{repr r} at {repr δ}: no sites"
            | some T =>
              let parts := callParts F.flow.H τ r
              let reasons (p : Part (markedPackage ofC O)) :=
                (p.mayIn && !(Ψ p).le δ,
                  p.mayOut false && sp.effect.any fun f => !(f.2.le δ) && !classQuery.disjoint r f.1)
              let describe (p : Part (markedPackage ofC O)) :=
                let (inside, outside) := reasons p
                s!"part ({markName (ofC := ofC) (O := O) p.site}, {repr p.kind}) fails {if inside then s!"Ψ = {repr (Ψ p)}" else ""}{if outside then " the call's effect" else ""}"
              if required.isEmpty then
                let witnesses := [(true, false), (false, true), (true, true)].filterMap fun pair =>
                  (parts.find? (fun p => reasons p == pair)).map describe
                s!"{repr r} at {repr δ}: {(Std.HashSet.ofList T).size} sites{if witnesses.isEmpty then ", passes" else s!", {witnesses}"}"
              else
                let bad := parts.filterMap fun p => if reasons p == (false, false) then none else some (describe p)
                s!"{repr r} at {repr δ}: sites {T.map (markName (ofC := ofC) (O := O))}{if bad.isEmpty then ", passes" else s!", {bad}"}"
          let obligation := if required.isEmpty then "not required; diagnostic " else ""
          s!"  {ff.name}: {obligation}frameCheckAt {ok}; support {per}"
    | _ => []

/-- **A module function's closure code** (`PassUnit.dropReceiver`): the
request's node lists behind one prologue node, appended, evaluating
`undefined` and continuing at the request's start with the frame past the
receiver; its arity, the module values it names (its captures), its
component and whether it collects a rest parameter. A function declaring
`this` has none here. -/
structure ProbeModule where
  name : String
  code : Code
  ar : Nat
  siblings : List String
  comp : ComponentTag
  sm : RequestJson.SourceMap := []
  rest : Bool := false
  /-- Per slot, in the siblings' order, whether the inhabitance check
  (`InhabitedTypes.typeWitnessB`) passes the type its request reads the slot
  at, in its request's graph (`slotsWitnessed`). -/
  witnessed : List Bool := []

/-- **The inhabitance of a request's slots**: per sibling, whether the type
the request reads it at (its inputs past its parameters, one per sibling)
passes the inhabitance check in the request's graph. -/
def slotsWitnessed {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι]
    (r : SourceElaboration.SourceRequest σ ι) : List Bool :=
  (List.range r.siblings.length).map fun k =>
    (r.inputs[r.inputs.length - r.siblings.length + k]?).any
      (InhabitedTypes.typeWitnessB (LabelStore.StoreView.graph r.types))

def ProbeModule.ofRequest {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι] (name : String)
    (r : SourceElaboration.SourceRequest σ ι) : Option ProbeModule :=
  if r.receiver then none else
  -- (the rest's spine is one input, past the arity)
  let ar := r.inputs.length - r.siblings.length - (if r.restParam then 1 else 0)
  let exprs := r.program.map (·.expression)
  let conts := r.program.map fun n => (n.continuation, n.handler)
  let code : Code := (exprs ++ [.undef],
    conts ++ [(.effect ⟨r.start, some ((List.range (r.inputs.length + 1)).map (· + 1))⟩, none)])
  some ⟨name, code, ar, r.siblings, r.comp, r.sourceMap, r.restParam, slotsWitnessed r⟩

/-- The signature of a module function's closure. -/
def ProbeModule.sig (g : ProbeModule) : FnSig := ⟨g.code, g.ar, g.code.1.length - 1, g.rest, g.siblings.length⟩

/-- **A native's step model** (the contract of an audited native, as code
of the component): the graph whose run the native's call performs, with its
arity. The rule `Read-only frame` reads an audited native at its audited
effect, not as code that is not `C`'s; its call is then a call of a
closure of a known signature (`Fits.invokeC`), its actuals at its entry's
slots, its value at its return set. Each row is trusted input, audited
against the native's definition:

- `%ElementAt%(xs, k)`: the element of `xs`'s spine at `k`, `undefined`
  where none (`tools/intrinsics.mts`: on an array of the program the read
  runs no code; no accessor or proxy, DESIGN.md "Trust surface"). Of an
  array or a tuple only: the model reads the spine field. -/
def hostModel? (name : String) : Option (Code × Nat) :=
  if name == "%ElementAt%" then
    some (([.elemAt (.readAt arraySpineKey (.var 1)) (.var 2)], [(.ret, none)]), 2)
  else none

/-- The module functions whose closures are values: those on no cycle of
the module's names (a cycle's closures capture each other). -/
def closable (mods : List ProbeModule) : List ProbeModule :=
  mods.filter fun g =>
    let rec reach : Nat → List String → List String → List String
      | 0, seen, _ => seen
      | _ + 1, seen, [] => seen
      | n + 1, seen, x :: work =>
        if seen.contains x then reach n seen work
        else reach n (x :: seen) (((mods.find? (·.name == x)).map (·.siblings)).getD [] ++ work)
    !(reach (mods.length * mods.length + mods.length + 1) [] g.siblings).contains g.name

/-- **A component's codes, as the flow's solver reads them**: the module
functions of `C`'s modules (`ofC`), the natives with a step model they name
(`hostModel?`), the closures their codes create, and the component's
initialization where one is given (`init`: its code and the names of the
realm values its slots hold, a unit entered at its node `0`, each slot
holding a native's closure naming that native's signature); each code's
signatures, sites and entry. A code is a term: module functions of one
code, arity, rest and number of captures are one code of the flow (`reps`, the
first of each, beside `modCodes`), its entry's slots naming a signature
where every one of them names the same, and an entry where one of them is.
Code `i`'s object and array sites are `3i` and `3i + 1`, its closures'
token `3i + 2`; each continuation and handler's first node allocates at
its own pair past them. -/
structure ComponentCodes (ofC : ComponentTag → Bool) where
  mods : List ProbeModule
  reps : List ProbeModule
  hosts : List (String × Code × Nat)
  closures : List (Code × Nat × Bool × Nat × Nat)
  modCodes : List (SolveCode (probePackage ofC))
  cs : List (SolveCode (probePackage ofC))

def componentCodes (ofC : ComponentTag → Bool) (mods : List ProbeModule) (entryNames : List String)
    (body : Code → Code := id) (init : Option (Code × List String) := none) : ComponentCodes ofC :=
  let P := probePackage ofC
  let mods := mods.filter fun g => P.ofC g.comp
  let closed := closable mods
  let found := mods.flatMap fun g => g.code.1.flatMap (closureLayouts P.ofC)
  let closures := found.foldl (fun acc c => if acc.any (·.1 == c.1) then acc else acc ++ [c]) []
  let alloc : Nat → Alloc P := fun i => ⟨some (3 * i), some (3 * i + 1)⟩
  let tok (i : Nat) : Option P.Site := some (3 * i + 2)
  -- the natives with a step model the module functions name
  let hostNames := (mods.flatMap (·.siblings)).filter (fun x => (hostModel? x).isSome) |>.eraseDups
  let hosts : List (String × Code × Nat) := hostNames.filterMap fun x => (hostModel? x).map fun (c, ar) => (x, c, ar)
  let hostSig (x : String) : Option FnSig :=
    (hosts.find? (·.1 == x)).map fun (_, c, ar) => ⟨c, ar, 0, false, 0⟩
  let sibSig (x : String) : Option FnSig :=
    ((closed.find? (·.name == x)).map ProbeModule.sig).orElse fun _ => hostSig x
  -- (one code per term, arity and number of captures)
  let same (g g' : ProbeModule) : Bool :=
    g'.code == g.code && g'.ar == g.ar && g'.rest == g.rest && g'.siblings.length == g.siblings.length
  let reps := mods.foldl (fun acc g => if acc.any (same g) then acc else acc ++ [g]) []
  let modCodes : List (SolveCode P) := reps.zipIdx.map fun (g, i) =>
    let group := mods.filter (same g)
    let c0 := capSlot g.ar g.rest 0
    let seedOf (g' : ProbeModule) (j : Nat) : Option FnSig :=
      if c0 ≤ j then (g'.siblings[j - c0]?).bind sibSig else none
    let seeds := (List.range (c0 + g.siblings.length)).map fun j =>
      if group.all fun g' => seedOf g' j == seedOf g j then seedOf g j else none
    ⟨g.code, g.ar, g.rest, g.siblings.length, g.code.1.length - 1, seeds, alloc i, true, tok i, entryCx,
      fun _ => alloc i, group.any fun g' => entryNames.contains g'.name, false⟩
  let hostCodes : List (SolveCode P) := hosts.zipIdx.map fun ((_, c, ar), i) =>
    ⟨c, ar, false, 0, 0, [], alloc (i + reps.length), true, tok (i + reps.length), entryCx,
      fun _ => alloc (i + reps.length), false, false⟩
  let base' := reps.length + hosts.length
  let cs : List (SolveCode P) := modCodes ++ hostCodes ++ closures.zipIdx.map fun ((c, ar, rest, n, s), i) =>
    { code := c, ar, rest, ncaps := n, start := s, seeds := [], alloc := alloc (i + base'), tok := tok (i + base'),
      allocAt := fun _ => alloc (i + base'), lowered := true }
  -- (the initialization, a unit past the other codes)
  let base'' := base' + closures.length
  let cs : List (SolveCode P) := cs ++ match init with
    | some (c, realmNames) =>
      [⟨c, 0, false, 0, 0, realmNames.map hostSig, alloc base'', false, tok base'', entryCx, fun _ => alloc base'',
        false, false⟩]
    | none => []
  -- each node's allocation sites: one object site and one array site per
  -- continuation and handler of a code's body (`body`, a realized code's
  -- its request's), numbered past the codes' sites (`canonSite` at the
  -- base `3 * cs.length` over the bodies)
  let offs := (cs.map fun c => (body c.code).2.length).foldl (fun (acc : List Nat) n => acc ++ [acc.getLast?.getD 0 + n]) [0]
  let cs : List (SolveCode P) := cs.zipIdx.map fun (c, i) =>
    -- (each continuation and handler's first node, read once per code)
    let first : Std.HashMap NodeKey Nat := (body c.code).2.zipIdx.foldl
      (fun m (kx, l) => if m.contains kx then m else m.insert kx l) {}
    { c with allocAt := fun kx => match first[kx]? with
      | some l => let k := 3 * cs.length + 2 * (offs.getD i 0 + l); ⟨some k, some (k + 1)⟩
      | none => c.alloc }
  ⟨mods, reps, hosts, closures, modCodes, cs⟩

/-- **The probe of a member at a component**, timed: the solver's, the
merge's and the check's milliseconds. The component `C` is a set of modules
(the tags `ofC` names) entered through its entries `E` (`entry`, by the
module functions' names); every module function of `C`'s modules a probe
reaches is a code of the flow, and the closures of `C`'s code they create.
An entry's closure is held by outside code (its token in `O`): outside
code may call it, at any time, with what it holds (`OpenAt`), and each
execution starts at a call of one (`EntryShape`, decided by `FFlow.entryB`
at the entry's first node). A module function no entry names is entered
only by `C`'s code that names it. The member is the module function
`member`, read at its closure's code. -/
def probeProgram (ofC : ComponentTag → Bool) (member : String) (mods : List ProbeModule)
    (specs : List FrameSpec := []) (entryNames : List String := []) : IO String := do
  let P := probePackage ofC
  let cc := componentCodes ofC mods entryNames
  let (mods, reps, hosts, closures, modCodes, cs) := (cc.mods, cc.reps, cc.hosts, cc.closures, cc.modCodes, cc.cs)
  -- (each entry at its code's representative, `reps`)
  let entries := entryNames.filterMap fun x => (mods.find? (·.name == x)).bind fun g =>
    ((reps.zip modCodes).find? fun (g', _) => g'.code == g.code).map fun (_, c) => (g, c)
  let t0 ← IO.monoNanosNow
  let s : SolveStart P ← IO.lazyPure fun _ => solveStart cs
  let _ ← IO.lazyPure fun _ => (s.fns.map fun ns => (ns.map fun x => x.size).sum).sum + s.succ.size
  let ts ← IO.monoNanosNow
  IO.eprintln s!"flow probe, start: {s.cs.size} copies of {cs.length} codes, {(s.codes.toList.map (·.1.size)).sum} nodes over the copies, {s.st.classes.size} slot and value occurrences, {s.succ.size} variables, {(ts - t0) / 1000000} ms"
  let fuel := ((← IO.getEnv "TSCERT_PROBE_FUEL").bind String.toNat?).getD 10000000
  let (st, rounds, batches) ← IO.lazyPure fun _ => solveLoop s fuel s.st
  let _ ← IO.lazyPure fun _ => st.sites.size + st.stores.size + st.vars.size
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"flow probe, solve: {(t1 - ts) / 1000000} ms, {rounds} copies, {batches} node evaluations"
  let F ← IO.lazyPure fun _ => s.propose st
  let _ ← IO.lazyPure fun _ => F.O.length + F.heap.length + (F.codes.map fun c => (c.2.map (·.2.nodes.size)).sum).sum
  let t2 ← IO.monoNanosNow
  -- (the checks at the marks the flow gives: a bound function's and a
  -- closure of outside code's parts reach no local site, which the marks
  -- decide)
  IO.eprintln s!"flow probe, merge: {(t2 - t1) / 1000000} ms"
  let marked := remark F
  let ok ← IO.lazyPure fun _ => marked.check
  let t3 ← IO.monoNanosNow
  IO.eprintln s!"flow probe, check: {ok} {(t3 - t2) / 1000000} ms"
  let nodes := (cs.map fun c => c.code.1.length).sum
  let names := reps.map (·.name) ++ hosts.map (·.1) ++ closures.map fun _ => "closure"
  let named : List (String × Code × RequestJson.SourceMap) := reps.map fun g => (g.name, g.code, g.sm)
  -- the call site a context stands for (the first of its class): its caller and the caller's source span
  let siteOf (κ : Nat) : String :=
    if κ == entryCx then " (entry)" else
    match (s.nodeCx.toList.zipIdx.flatMap fun (row, b) =>
        row.toList.zipIdx.filterMap fun (k, l) => if k == κ then some (b, l) else none).head? with
    | some (b, l) =>
      let pos := match (named[b]?).bind fun (_, _, msm) => (msm[l]?).bind id with
        | some en => s!"{en.pos}"
        | none => "none"
      s!" (call site: {names.getD b "?"} node {l} at {pos})"
    | none => ""
  let report (tag : String) : String :=
    -- each entry's start: its first node, the closure's prologue
    let entryOk := entryNames.map fun name =>
      (name, (entries.find? fun (g, _) => g.name == name).any fun (g, c) => F.entryB g.code c.start)
    let F' := marked
    let marks := F'.marksB
    -- (the refused nodes are read again only where the check fails)
    let bad := if ok then [] else F.codes.zipIdx.flatMap fun ((code, cs), ci) => cs.flatMap fun (κ, c) =>
      (code.1.zip code.2).zipIdx.filterMap fun ((e, k, x), l) =>
        if nodeAtB F' (remarkCode F c) l e k x then none else some s!"{ci}@{κ}:{l}"
    let contexts := (F.codes.map (·.2.length)).sum
    let ctxNodes := (F.codes.map fun (m, cs) => m.1.length * cs.length).sum
    let lay := cs.map fun c => (c.ar, c.rest, c.ncaps, c.start)
    let held := (Std.HashSet.ofList (captureSites F' lay)).toList
    let host (i : Nat) : Bool := reps.length ≤ i && i < reps.length + hosts.length
    let unitCode (x : String) : Option Code := (mods.find? (·.name == x)).map (·.code)
    let frames := String.join <| specs.flatMap fun sp => match named.zipIdx.find? (some ·.1.2.1 == unitCode sp.unit) with
      | some ((_, mc, msm), ci) => match (F'.codes[ci]?).map (·.2) with
        | some cxs => cxs.flatMap fun (κ, c) =>
          s!"\nframe probe, {sp.unit}: {tag} context {κ}{siteOf κ}" :: (probeFrames F.O F' (componentProtocol F' lay) lay host c mc msm sp).map ("\n" ++ ·)
        | none => []
      | none => []
    s!"{tag}: {contexts} contexts, {ctxNodes} nodes over the contexts; entry {entryOk.all (·.2)}; entries {entryOk}; at the marks O gives: marks {marks}; refused nodes {bad}; captured {repr held}{frames}"
  let present := if mods.any (·.name == member) then "" else s!" (the member {member} has no closure code here)"
  return s!"flow probe: {cs.length} codes {names}, {nodes} nodes{present}; siblings {mods.map fun g => (g.name, g.siblings)}; solve {(t1 - t0) / 1000000} ms (signatures {(ts - t0) / 1000000} ms, {rounds} copies, {batches} nodes run); merge {(t2 - t1) / 1000000} ms; check {ok} {(t3 - t2) / 1000000} ms; O {repr F.O} (code i's closures 3i+2; a node's object site 3n+2k, array site 3n+2k+1, n codes, k the first node of its continuation and handler over all codes)\n{report "proposed"}"

/-- The probe of each member of a group, the component's module functions'
codes `mods`, its tags `ofC` and its entries `entry`. -/
def FilePlans.flowProbe (f : FilePlans) (group : List Nat) (mods : List ProbeModule)
    (ofC : ComponentTag → Bool) (entryNames : List String) : IO (List String) := do
  let specs ← match ← IO.getEnv "TSCERT_FRAME_PROBE" with
    | some path => do
      match Json.parse (← IO.FS.readFile path) >>= frameSpecs with
      | .ok sp => pure sp
      | .error e => IO.eprintln s!"frame probe: {e}"; pure []
    | none => pure []
  group.filterMapM fun j => match (f.plans.drop j).head? with
    | some (.ok p) => match p with
      | .graph name _ _ => do
        let line ← probeProgram ofC name mods specs entryNames
        return some s!"{name}: {line}"
      | .framed .. | .callbackDemands .. => return none
    | _ => return none

/-- The module codes of a file's planned members. -/
def FilePlans.moduleCodes (f : FilePlans) (units : List Nat) : List ProbeModule :=
  units.filterMap fun j => match (f.plans.drop j).head? with
    | some (.ok (.graph name _ r)) => if name.isEmpty then none else ProbeModule.ofRequest name r
    | _ => none

/-- The siblings of a file's planned members. -/
def FilePlans.siblingsOf (f : FilePlans) (units : List Nat) : List String :=
  units.flatMap fun j => match (f.plans.drop j).head? with
    | some (.ok (.graph _ _ r)) => r.siblings
    | _ => []

/-- The module codes of the groups planned so far in this process, where
the probe is on. -/
initialize probeModulesSeen : IO.Ref (List ProbeModule) ← IO.mkRef []

/-- Keep a planned group's module codes for the probe. -/
def FilePlans.keepModuleCodes (f : FilePlans) (units : List Nat) : IO Unit := do
  let found := f.moduleCodes units
  probeModulesSeen.modify fun seen => seen ++ found.filter fun m => !seen.any (·.name == m.name)

end Verification.SourceClaimJson
