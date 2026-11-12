import Verification.Programs.TolerantFramesWalkExtends

/-! # A node and its successful exit computation

The record retains successful computations at the original graph and
the cached vacuity answer's empty-context witness. Edge-check extraction
and reassignment are separate obligations.
-/
namespace Verification.TolerantFrames
open Verification ControlFlow PositiveGraphs PositiveCertificates LabelStore ProgramTyping CertificateProducer

/-- **What a node's `here` answer states**: its context has a slot of an
empty type, or is unsatisfiable (`unsat`, as an edge into the node sets it). -/
@[nospecialize] def HereEmpty {ι : Type} (G : NormalGraph ι) (C : List (Ty ι)) : Prop :=
  ControlFlow.unsatisfiable G C = true ∨ ∃ (i : Nat) (B : Ty ι), C[i]? = some B ∧ ControlFlow.unsatisfiable G [B] = true

/-- Every cached refusal to admit an environment has an empty-context witness. -/
@[nospecialize] def CachedVacuity {ι : Type} (G : NormalGraph ι) (claimed : Array (PointClaim ι))
    (cache : Array (Option Bool)) : Prop :=
  ∀ l : Nat, cache[l]! = some true → HereEmpty G (claimed[l]!).context

/-- The incoming arrays and processed edges returned by the exit computation. -/
@[nospecialize] def exitsWalk {ι : Type} [BEq ι] [Hashable ι] {G : NormalGraph ι}
    (ex : SinglePass.ExitsDone ι G) : SinglePass.Walk ι :=
  { labels := #[], incoming := ex.incoming, incomingImpl := ex.incomingImpl,
    incomingEdges := ex.incomingEdges, edges := ex.edges }

/-- Every indexed exit succeeds at these values, and its output arrays
persist in `raw`. The exit index fixes which branch receives refinement. -/
@[nospecialize] def ExitStepsChecked {ι : Type} [Labels ι] (G : NormalGraph ι) (I : InstanceImageCheck G)
    (env : SinglePass.WalkEnv ι G I) (l : Nat) (en : SinglePass.Entered ι) (sd : SinglePass.StepDone ι G)
    (raw : SinglePass.Walk ι) : Prop :=
  ∀ e ∈ (SinglePass.Exit.ofNode env.nodes[l]!).zipIdx, ∃ a b,
    SinglePass.exitStep G I env l en sd
      (SinglePass.yieldsAtSlots en.entry.names ((SinglePass.exitsYields G I env l en sd).1.getD []))
      (Thunk.mk fun _ => SinglePass.outAllOf G env.claimed[l]! sd.st.stepOut) a e = .ok b ∧
    WalkExtends (exitsWalk b) raw

/-- Each indexed exit owns a record in the visit's final array, appended
by that exit's successful computation. The same computation's incoming
arrays and processed edges persist in the final visit. -/
@[nospecialize] def ExitRecordsChecked {ι : Type} [Labels ι] (G : NormalGraph ι) (I : InstanceImageCheck G)
    (env : SinglePass.WalkEnv ι G I) (l : Nat) (en : SinglePass.Entered ι) (sd : SinglePass.StepDone ι G)
    (ex : SinglePass.ExitsDone ι G) : Prop :=
  ∀ e ∈ (SinglePass.Exit.ofNode env.nodes[l]!).zipIdx, ∃ r ∈ ex.exits.toList,
    r.index = e.2 ∧ r.target = e.1.target ∧ ∃ a b,
    SinglePass.exitStep G I env l en sd
      (SinglePass.yieldsAtSlots en.entry.names ((SinglePass.exitsYields G I env l en sd).1.getD []))
      (Thunk.mk fun _ => SinglePass.outAllOf G env.claimed[l]! sd.st.stepOut) a e = .ok b ∧
    b.exits = a.exits.push r ∧ WalkExtends (exitsWalk b) (exitsWalk ex)

/-- A successful entry, step, and exit visit at this very node's values.
The exit arrays extend to the walk used by the node's check. This keeps the
step and exit witnesses in the same existential when a checked node is chosen.
The equations are about execution at `G`, not execution at reassigned graphs. -/
@[nospecialize] def NodeExitTrace {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}
    (c : Target.RunCall G I)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    {w : Walk ι} {ctx : Nat → List (Ty ι)} {l : Nat}
    (r : NodeChecked G I c.codes c.passChecker c.P w (List.range c.inputs.length) ctx l) : Prop :=
  ∃ (raw : SinglePass.Walk ι) (env : SinglePass.WalkEnv ι G I) (σ : SinglePass.WalkState ι G)
      (en : SinglePass.Entered ι) (sd : SinglePass.StepDone ι G) (ex : SinglePass.ExitsDone ι G),
    w = ofPass raw (passHeads c) ∧ edgesIn = passEdgesIn raw ∧
    env.nodes = c.P.toArray ∧ env.claimed = c.claims.toArray ∧ env.codes = c.codes ∧
    env.passChecker = c.passChecker ∧
    (∀ t, (env.isHead[t]?).getD false = passHeads c t) ∧
    (∀ t, env.stated[t]! = passStated c t) ∧
    SinglePass.visitEntry G I env σ l = .ok en ∧
    SinglePass.visitStep G I env σ l en = .ok sd ∧
    SinglePass.visitExits G I env σ l en sd = .ok ex ∧
    r.node = env.nodes[l]! ∧ r.c = env.claimed[l]! ∧ r.entry = en.entry ∧ r.st = sd.st ∧
    r.ans = sd.steppedAnswers ∧ r.ys = sd.yields.getD [] ∧ en.implies = w.implies l ∧
    σ.walk.incoming.size = σ.walk.incomingImpl.size ∧ WalkExtends (exitsWalk ex) raw ∧
    ExitStepsChecked G I env l en sd raw ∧
    (en.here = true → HereEmpty G (env.claimed[l]!).context) ∧
    ExitRecordsChecked G I env l en sd ex

end Verification.TolerantFrames
