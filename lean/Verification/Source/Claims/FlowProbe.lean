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

/-- The probe of a program at a component. -/
def probeProgram (m : Code) (start : Nat) (comp : ComponentTag) : List String :=
  let P := probePackage comp
  let found := m.1.flatMap (probeClosures P.ofC)
  let closures := found.foldl (fun acc c => if acc.any (·.1 == c.1) then acc else acc ++ [c]) []
  let alloc : Nat → Alloc P := fun i => ⟨some (2 * i), some (2 * i + 1)⟩
  let unit : SolveCode P := ⟨m, 0, false, 0, start, [], alloc 0⟩
  let cs : List (SolveCode P) := unit :: closures.zipIdx.map fun ((c, ar, rest, n, s), i) =>
    let self := capSlot ar rest n
    ⟨c, ar, rest, n, s, (List.range (self + 1)).map fun j =>
      if j = self then some ⟨c, ar, s, rest, n⟩ else none, alloc (i + 1)⟩
  let F := solveFlow cs 200
  let bad := F.codes.zipIdx.flatMap fun ((code, c), ci) =>
    (List.range code.1.length).filterMap fun l =>
      if nodeB F c code l then none else some s!"{ci}:{l}"
  [s!"flow probe: {cs.length} codes; check {F.check}; marks {F.marksB}; O {repr F.O}; refused nodes {bad}"]

/-- The probe of each member of a group. -/
def FilePlans.flowProbe (f : FilePlans) (group : List Nat) : List String :=
  group.flatMap fun j => match (f.plans.drop j).head? with
    | some (.ok p) => match p with
      | .graph name _ r => (probeProgram (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) r.start
          r.comp).map (s!"{name}: " ++ ·)
    | _ => []

end Verification.SourceClaimJson
