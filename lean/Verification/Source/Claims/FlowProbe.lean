import Verification.Source.Claims.Json
import Verification.Paper.TolerantFrames.ReadOnlyFlowSolve

/-! # The flow of a unit's codes, probed

A diagnostic (`TSCERT_FLOW_PROBE`): for each member of a group, the flow the
read-only frame's checks read (`ReadOnly.solveFlow`) of its program and the
closures of its component's code it creates, and whether its checks hold
(`ReadOnly.FFlow.check`, the nodes they refuse). It decides nothing a
verdict reads. -/
namespace Verification.SourceClaimJson
open Lean Verification.TolerantFrames.ReadOnly ControlFlow

/-- The package a unit's probe reads: sites numbered, the unit's component
its code. -/
abbrev probePackage (comp : ComponentTag) : TolerantFrames.ReadOnly.Package :=
  ⟨Nat, fun _ => .released, fun c => c.isSome && c == comp⟩

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

def ProbeModule.ofRequest {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι] (name : String)
    (r : SourceExtraction.SourceRequest σ ι) : Option ProbeModule :=
  if r.receiver || r.restParam then none else
  let ar := r.inputs.length - r.siblings.length
  let ncaps := r.siblings.length
  let exprs := r.program.map (·.expression)
  let conts := r.program.map fun n => (n.continuation, n.handler)
  some ⟨name, (exprs ++ [.undef], conts ++ [(.effect ⟨r.start, some ((List.range (ar + ncaps + 1)).map (· + 1))⟩, none)]),
    ar, r.siblings, r.comp⟩

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
    (mods : List ProbeModule) : IO String := do
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
  let marks ← IO.lazyPure fun _ => F.marksB
  let bad := F.codes.zipIdx.flatMap fun ((code, c), ci) =>
    (code.1.zip code.2).zipIdx.filterMap fun ((e, k, x), l) =>
      if nodeAtB F c l e k x then none else some s!"{ci}:{l}"
  let nodes := (cs.map fun c => c.code.1.length).sum
  let names := "unit" :: mods.map (·.name) ++ closures.map fun _ => "closure"
  return s!"flow probe: {cs.length} codes {names}, {nodes} nodes; solve {(t1 - t0) / 1000000} ms (signatures {(ts - t0) / 1000000} ms, {rounds} copies, {batches} nodes run); check {ok} {(t2 - t1) / 1000000} ms; marks {marks}; O {repr F.O} (code i's object site 2i, array site 2i+1); refused nodes {bad}"

/-- The probe of each member of a group, the module functions' codes
`mods`. -/
def FilePlans.flowProbe (f : FilePlans) (group : List Nat) (mods : List ProbeModule) : IO (List String) :=
  group.filterMapM fun j => match (f.plans.drop j).head? with
    | some (.ok p) => match p with
      | .graph name _ r => do
        let line ← probeProgram (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler))
          r.start r.comp r.inputs.length r.siblings mods
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
