import Verification.Source.Claims.Json
import Verification.Source.EffectCodec
import Verification.Semantics.Survival
import Verification.Paper.TolerantFrames.ReadOnlyFlowSolve
import Verification.Paper.TolerantFrames.ReadOnlyCallFrame

/-! # The flow of a unit's codes, probed

A diagnostic (`TSCERT_FLOW_PROBE`): for each member of a group, the flow the
read-only frame's checks read (`ReadOnly.solveFlow`) of its program and the
closures of its component's code it creates, and whether its checks hold
(`ReadOnly.FFlow.check`, the nodes they refuse), the member's entry
(`FFlow.entryB`), and at the marks the flow gives (`FFlow.MarksFrom`) the
bindings check (`FFlow.bindingsB`). With `TSCERT_FRAME_PROBE` naming a
file of facts, at each call of outside code it names, the frame's check
(`frameCheckAt`) of each fact's support (`Footprints.linearSupport`), part
by part. It decides nothing a verdict reads. -/
namespace Verification.SourceClaimJson
open Lean Verification.TolerantFrames.ReadOnly ControlFlow

/-- The package a unit's probe reads: sites numbered, the unit's component
its code. -/
abbrev probePackage (comp : ComponentTag) : TolerantFrames.ReadOnly.Package :=
  ⟨Nat, fun _ => .released, fun c => c.isSome && c == comp⟩

/-- **The package at the marks a flow gives**: a site of `O` released, every
other site local (`FFlow.MarksFrom`). -/
abbrev markedPackage (comp : ComponentTag) (O : List (Option Nat)) : TolerantFrames.ReadOnly.Package :=
  ⟨Nat, fun s => if some s ∈ O then .released else .local, fun c => c.isSome && c == comp⟩

/-- A finite flow read at the marks its `O` gives. -/
def remark {comp : ComponentTag} (F : FFlow (probePackage comp)) : FFlow (markedPackage comp F.O) :=
  let node (x : FNode (probePackage comp)) : FNode (markedPackage comp F.O) := ⟨x.env, x.dflt, x.val, x.fn, x.vfn⟩
  ⟨F.O, F.heap, F.codes.map fun (m, c) => (m, ⟨c.nodes.map node, node c.dflt, ⟨c.alloc.obj, c.alloc.arr⟩, c.sigs, c.ret⟩)⟩

theorem remark_marksFrom {comp : ComponentTag} (F : FFlow (probePackage comp)) : (remark F).MarksFrom := fun _ => rfl

/-! ## The frame at a call, probed -/

section frames
variable {P : TolerantFrames.ReadOnly.Package} [DecidableEq P.Site]

/-- The writes of a term at a node's slots: the sites of each written
location's object or spine, `true` for an element write. -/
partial def writesIn (F : FFlow P) (τ : Nat → Sites P) (φ : Nat → Option FnSig) (a : Alloc P) (d : Nat)
    (Γ : Nat → Option (Sites P)) : Tm → List (Sites P × Bool)
  | .writeAt _ x y => ((syn F τ φ a d Γ x).map fun S => [(S, false)]).getD [([none], false)] ++
      writesIn F τ φ a d Γ x ++ writesIn F τ φ a d Γ y
  | .setElem x i v => ((syn F τ φ a d Γ x).map fun S => [(S, true)]).getD [([none], true)] ++
      writesIn F τ φ a d Γ x ++ writesIn F τ φ a d Γ i ++ writesIn F τ φ a d Γ v
  | .letE x b => writesIn F τ φ a d Γ x ++ match syn F τ φ a d Γ x with
    | some Sx => writesIn F τ φ a (d + 1) (consSites Sx Γ) b
    | none => []
  | .invoke f r args => writesIn F τ φ a d Γ f ++ writesIn F τ φ a d Γ r ++ args.flatMap (writesIn F τ φ a d Γ)
  | .construct f args => writesIn F τ φ a d Γ f ++ args.flatMap (writesIn F τ φ a d Γ)
  | .makeAt _ _ inits | .arrLit inits => inits.flatMap (writesIn F τ φ a d Γ)
  | .indexAt x y | .arith _ x y | .elemAt x y | .merge _ x y | .makeKey x y =>
    writesIn F τ φ a d Γ x ++ writesIn F τ φ a d Γ y
  | .ite x y z => writesIn F τ φ a d Γ x ++ writesIn F τ φ a d Γ y ++ writesIn F τ φ a d Γ z
  | .readAt _ x | .test _ x | .lenOf x | .spread x | .throw x => writesIn F τ φ a d Γ x
  | _ => []

/-- The writes of every node of every code of a flow. -/
def flowWrites (F : FFlow P) : List (Sites P × Bool) :=
  F.codes.flatMap fun (m, c) => m.1.zipIdx.flatMap fun (e, l) =>
    writesIn F (c.node l).envAt (fun i => c.sigAt ((c.node l).fnAt i)) c.alloc 0 (fun _ => none) e

/-- **The probe's protocol**: a part of a local site kept (no code a call of
outside code may run reaches local storage existing at the call); any
other part changed as the writes of the flow's codes reaching its site
may change it: a field by a field write, a cell or element by an element
write, a spine grown by an element write. -/
def probeProtocol (W : List (Sites P × Bool)) : Protocol P := fun p =>
  match p.site with
  | some s => if P.mark s = .local then .keep else charge p
  | none => charge p
where
  charge (p : Part P) : Footprints.Change :=
    let hits := W.filter fun (S, _) => p.site ∈ S
    if hits.any (fun (_, e) => !e) && p.kind == some .field then .any
    else if hits.any (·.2) && (p.kind == some .cell || p.kind == some .elem) then .any
    else if hits.any (·.2) && p.kind == some .spine then .grow
    else .keep

end frames

def markName {comp : ComponentTag} {O : List (Option Nat)} (s : Option Nat) : String :=
  match s with
  | none => "outside"
  | some n => match (markedPackage comp O).mark n with
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
      ← EffectCodec.frameOf 64 (← u.getObjVal? "effect"), facts⟩

/-- **The frame's check at each call the spec names**, in the code `c` of a
flow, of graph `m` and source map `sm` (`frameCheckAt`, at the class
query, the probe's protocol and the keys `noKeys`, no region read as
protected): per call node, per fact, its result, and each part its
support's regions may have that fails, with the check it fails. -/
def probeFrames {comp : ComponentTag} (O : List (Option Nat)) (F : FFlow (markedPackage comp O))
    (Ψ : Protocol (markedPackage comp O)) (c : FCode (markedPackage comp O)) (m : Code)
    (sm : RequestJson.SourceMap) (sp : FrameSpec) : List String :=
  let names (l : Nat) : List String := ((sm[l]?).bind id).map (·.context.map (·.name)) |>.getD []
  let calls := m.1.zipIdx.filterMap fun (e, l) => match e with
    | .invoke (.var j) _ _ => if ((c.node l).fnAt j).isNone then some (l, j) else none
    | _ => none
  let pos (l : Nat) : String := match (sm[l]?).bind id with
    | some en => s!"{en.pos}"
    | none => "none"
  s!"frame probe, {sp.unit}: calls of a slot naming no signature (node, callee slot, source span) {calls.map fun (l, j) => (l, j, pos l)}" ::
  m.1.zipIdx.flatMap fun (e, l) => match e with
    | .invoke (.var j) _ _ =>
      let pos := ((sm[l]?).bind id).map (·.pos.1)
      if pos != some sp.at_ || ((c.node l).fnAt j).isSome then [] else
      let τ := (c.node l).envAt
      let slotOf (x : String) : Option Nat := (names l).idxOf? x
      let slotSites := (List.range (names l).length).map fun i => ((names l)[i]?.getD "", τ i)
      s!"frame probe, {sp.unit}, at node {l} (callee slot {j}): slots {repr slotSites}" ::
      sp.facts.map fun ff =>
        match ff.terms.mapM (fun (x, p, k, a) => (slotOf x).map fun i => (HeapKnowledge.Term.now k i p, a)) with
        | none => s!"  {ff.name}: a variable is not a slot here"
        | some G =>
          let fact : Linear.Fact HeapKnowledge.Term := if ff.ne then .ne G ff.bound else .le G ff.bound
          let S := Footprints.linearSupport {} fact
          let ok := frameCheckAt classQuery Ψ sp.effect S F.flow.H τ noKeys (fun _ => false)
          let per := S.map fun (r, δ) =>
            match regionSites F.flow.H τ r with
            | none => s!"{repr r} at {repr δ}: no sites"
            | some T =>
              let bad := (callParts F.flow.H τ noKeys r).filterMap fun (p : Part (markedPackage comp O)) =>
                let inOk := !p.mayIn || (Ψ p).le δ
                let outOk := !p.mayOut false || sp.effect.all fun f => f.2.le δ || classQuery.disjoint r f.1
                if inOk && outOk then none
                else some s!"part ({markName (comp := comp) (O := O) p.site}, {repr p.kind}) fails {if inOk then "" else s!"Ψ = {repr (Ψ p)}"}{if outOk then "" else " the call's effect"}"
              s!"{repr r} at {repr δ}: sites {T.map (markName (comp := comp) (O := O))}{if bad.isEmpty then ", passes" else s!", {bad}"}"
          s!"  {ff.name}: frameCheckAt {ok}; support {per}"
    | _ => []

/-- The closures of the component's code a term creates, with their entry
layouts. -/
partial def probeClosures (ofC : ComponentTag → Bool) : Tm → List (Code × Nat × Bool × Nat × Nat)
  | .makeAt (.graph ar E K s caps _ rest comp) _ inits =>
    (if ofC comp then [((E, K), ar, rest, caps.length, s)] else []) ++ E.flatMap (probeClosures ofC) ++
      inits.flatMap (probeClosures ofC)
  | .invoke f r args => probeClosures ofC f ++ probeClosures ofC r ++ args.flatMap (probeClosures ofC)
  | .construct f args => probeClosures ofC f ++ args.flatMap (probeClosures ofC)
  | .makeAt _ _ inits | .arrLit inits => inits.flatMap (probeClosures ofC)
  | .letE a b | .indexAt a b | .writeAt _ a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
    probeClosures ofC a ++ probeClosures ofC b
  | .ite a b c | .setElem a b c => probeClosures ofC a ++ probeClosures ofC b ++ probeClosures ofC c
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => probeClosures ofC a
  | _ => []

/-- **A module function's closure code** (`PassUnit.dropReceiver`): the
request's node lists behind one prologue node, appended, evaluating
`undefined` and continuing at the request's start with the frame past the
receiver; its arity, the module values it names (its captures) and its
component. A function declaring `this` or collecting a rest parameter has
none here. -/
structure ProbeModule where
  name : String
  code : Code
  ar : Nat
  siblings : List String
  comp : ComponentTag
  sm : RequestJson.SourceMap := []

def ProbeModule.ofRequest {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι] (name : String)
    (r : SourceExtraction.SourceRequest σ ι) : Option ProbeModule :=
  if r.receiver || r.restParam then none else
  let ar := r.inputs.length - r.siblings.length
  let ncaps := r.siblings.length
  let exprs := r.program.map (·.expression)
  let conts := r.program.map fun n => (n.continuation, n.handler)
  some ⟨name, (exprs ++ [.undef], conts ++ [(.effect ⟨r.start, some ((List.range (ar + ncaps + 1)).map (· + 1))⟩, none)]),
    ar, r.siblings, r.comp, r.sourceMap⟩

/-- The signature of a module function's closure. -/
def ProbeModule.sig (g : ProbeModule) : FnSig := ⟨g.code, g.ar, g.code.1.length - 1, false, g.siblings.length⟩

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

/-- The probe of a program at a component, timed: the solver's and the
check's milliseconds. The module's closures sit at the slots of the module
functions the program names (`mods`, the module functions its siblings
reach). -/
def probeProgram (m : Code) (start : Nat) (comp : ComponentTag) (inputs : Nat) (siblings : List String)
    (mods : List ProbeModule) (name : String := "") (sm : RequestJson.SourceMap := []) (specs : List FrameSpec := []) :
    IO String := do
  let P := probePackage comp
  -- The module functions the program's siblings reach.
  let rec reach : Nat → List String → List String → List String
    | 0, seen, _ => seen
    | _ + 1, seen, [] => seen
    | n + 1, seen, x :: work =>
      if seen.contains x then reach n seen work
      else reach n (x :: seen) (((mods.find? (·.name == x)).map (·.siblings)).getD [] ++ work)
  let reached := reach (mods.length * mods.length + mods.length + 1) [] siblings
  let mods := closable (mods.filter fun g => P.ofC g.comp && reached.contains g.name)
  let found := (m.1 ++ mods.flatMap (·.code.1)).flatMap (probeClosures P.ofC)
  let closures := found.foldl (fun acc c => if acc.any (·.1 == c.1) then acc else acc ++ [c]) []
  let alloc : Nat → Alloc P := fun i => ⟨some (2 * i), some (2 * i + 1)⟩
  let sibSig (x : String) : Option FnSig := (mods.find? (·.name == x)).map ProbeModule.sig
  let base := inputs - siblings.length
  let unitSeeds : List (Option FnSig) :=
    (List.range inputs).map fun i => if base ≤ i then (siblings[i - base]?).bind sibSig else none
  let unit : SolveCode P := ⟨m, 0, false, 0, start, unitSeeds, alloc 0, false⟩
  let modCodes : List (SolveCode P) := mods.zipIdx.map fun (g, i) =>
    let c0 := capSlot g.ar false 0
    let seeds := (List.range (c0 + g.siblings.length)).map fun j =>
      if c0 ≤ j then (g.siblings[j - c0]?).bind sibSig else none
    ⟨g.code, g.ar, false, g.siblings.length, g.code.1.length - 1, seeds, alloc (i + 1), true⟩
  let cs : List (SolveCode P) := unit :: modCodes ++ closures.zipIdx.map fun ((c, ar, rest, n, s), i) =>
    ⟨c, ar, rest, n, s, [], alloc (i + 1 + mods.length), true⟩
  let t0 ← IO.monoNanosNow
  let s ← IO.lazyPure fun _ => solveStart cs
  let _ ← IO.lazyPure fun _ => (s.fns.map fun ns => (ns.map fun x => x.size).sum).sum + s.succ.size
  let ts ← IO.monoNanosNow
  let (st, rounds, batches) ← IO.lazyPure fun _ => solveLoop s 10000000 s.st
  let F := s.flow st
  let _ ← IO.lazyPure fun _ => F.O.length + F.heap.length + (F.codes.map fun c => c.2.nodes.size).sum
  let t1 ← IO.monoNanosNow
  let ok ← IO.lazyPure fun _ => F.check
  let t2 ← IO.monoNanosNow
  let entry := F.entryB m start
  let bindings := (remark F).bindingsB
  let marks := (remark F).marksB
  let bad := F.codes.zipIdx.flatMap fun ((code, c), ci) =>
    (code.1.zip code.2).zipIdx.filterMap fun ((e, k, x), l) =>
      if nodeAtB F c l e k x then none else some s!"{ci}:{l}"
  let nodes := (cs.map fun c => c.code.1.length).sum
  let names := "unit" :: mods.map (·.name) ++ closures.map fun _ => "closure"
  let F' := remark F
  let Ψ := probeProtocol (flowWrites F')
  let named : List (String × Code × RequestJson.SourceMap) := (name, m, sm) :: mods.map fun g => (g.name, g.code, g.sm)
  let frames := String.join <| specs.flatMap fun sp => match named.zipIdx.find? (·.1.1 == sp.unit) with
    | some ((_, mc, msm), ci) => match (F'.codes[ci]?).map (·.2) with
      | some c => (probeFrames F.O F' Ψ c mc msm sp).map ("\n" ++ ·)
      | none => []
    | none => []
  return s!"flow probe: {cs.length} codes {names}, {nodes} nodes; solve {(t1 - t0) / 1000000} ms (signatures {(ts - t0) / 1000000} ms, {rounds} copies, {batches} nodes run); check {ok} {(t2 - t1) / 1000000} ms; entry {entry}; at the marks O gives: marks {marks}, bindings {bindings}; O {repr F.O} (code i's object site 2i, array site 2i+1); refused nodes {bad}{frames}"

/-- The probe of each member of a group, the module functions' codes
`mods`. -/
def FilePlans.flowProbe (f : FilePlans) (group : List Nat) (mods : List ProbeModule) : IO (List String) := do
  let specs ← match ← IO.getEnv "TSCERT_FRAME_PROBE" with
    | some path => do
      match Json.parse (← IO.FS.readFile path) >>= frameSpecs with
      | .ok sp => pure sp
      | .error e => IO.eprintln s!"frame probe: {e}"; pure []
    | none => pure []
  group.filterMapM fun j => match (f.plans.drop j).head? with
    | some (.ok p) => match p with
      | .graph name _ r => do
        let line ← probeProgram (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler))
          r.start r.comp r.inputs.length r.siblings mods name r.sourceMap specs
        return some s!"{name}: {line}"
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
