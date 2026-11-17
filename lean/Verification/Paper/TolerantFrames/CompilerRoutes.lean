import Verification.Paper.TolerantFrames.CompilerSegments

/-! # Finite administrative exit routes

Routes record actual finite site lookups and stack structure. Their meaning is
proved using zero-weight command-machine traces and real shared slot maps.
Compilation must generate this evidence; it is not a command/safety summary.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification ControlFlow

/-- Select a residual command or loop header, or reach the function boundary.
Recursion consumes only a finite stack; another loop iteration is not unfolded. -/
def route : CommandMachine.Stack → Exit → Env → CommandMachine.Control × Env
  | [], e, ρ => (.exit e [], ρ)
  | .sequence b :: stack, .normal, ρ => (front b stack, ρ)
  | .sequence _ :: stack, e, ρ => route stack e ρ
  | .loop b :: stack, .normal, ρ => (.run (.loop b) stack, ρ)
  | .loop _ :: stack, .break, ρ => route stack .normal ρ
  | .loop _ :: stack, e, ρ => route stack e ρ
  | .catcher x d :: stack, .thrown v, ρ => (front d stack, bindName ρ x v)
  | .catcher _ _ :: stack, e, ρ => route stack e ρ

theorem route_trace (host : NativeCode) (stack : CommandMachine.Stack) (e : Exit) (ρ : Env) (h : Heap) :
    CommandMachine.Runs host (.exit e stack) ρ h 0 (route stack e ρ).1 (route stack e ρ).2 h := by
  induction stack generalizing e ρ with
  | nil => exact .refl
  | cons frame stack ih =>
    cases frame with
    | sequence b =>
      cases e with
      | normal => exact .next .seq_normal (front_trace b stack host ρ h)
      | «break» => exact .next (.seq_exit (by decide)) (ih .break ρ)
      | returned v => exact .next (.seq_exit (by intro h; cases h)) (ih (.returned v) ρ)
      | thrown v => exact .next (.seq_exit (by intro h; cases h)) (ih (.thrown v) ρ)
    | loop b =>
      cases e with
      | normal => exact .next .loop_normal .refl
      | «break» => exact .next .loop_break (ih .normal ρ)
      | returned v => exact .next .loop_return (ih (.returned v) ρ)
      | thrown v => exact .next .loop_throw (ih (.thrown v) ρ)
    | catcher x d =>
      cases e with
      | thrown v => exact .next .catch_throw (front_trace d stack host (bindName ρ x v) h)
      | normal => exact .next (.catch_exit (fun _ h => by cases h)) (ih .normal ρ)
      | «break» => exact .next (.catch_exit (fun _ h => by cases h)) (ih .break ρ)
      | returned v => exact .next (.catch_exit (fun _ h => by cases h)) (ih (.returned v) ρ)

theorem route_returned (stack : CommandMachine.Stack) (v : Val) (ρ : Env) :
    route stack (.returned v) ρ = (.exit (.returned v) [], ρ) := by
  induction stack with
  | nil => rfl
  | cons frame stack ih => cases frame <;> exact ih

theorem route_normal_env (stack : CommandMachine.Stack) (ρ : Env) : (route stack .normal ρ).2 = ρ := by
  induction stack with
  | nil => rfl
  | cons frame stack ih => cases frame <;> first | rfl | exact ih

theorem route_break_env (stack : CommandMachine.Stack) (ρ : Env) : (route stack .break ρ).2 = ρ := by
  induction stack with
  | nil => rfl
  | cons frame stack ih =>
    cases frame with
    | sequence | catcher => exact ih
    | loop => exact route_normal_env stack ρ

/-- A syntactic derivation of destinations. Sink SITE lookups justify control
routing only; full sink-node equality is separately required for execution. -/
inductive Routes (nodes : List AnnotatedNode) (bound : Nat) :
    CommandMachine.Stack → Nat → Nat → Nat → Target → Prop where
  | root {normal broken returned thrown} :
      (nodes[normal]?).map AnnotatedNode.site = some .normal →
      (nodes[broken]?).map AnnotatedNode.site = some .broken →
      (nodes[returned]?).map AnnotatedNode.site = some .returned →
      (nodes[thrown]?).map AnnotatedNode.site = some .thrown →
      Routes nodes bound [] normal broken returned (payloadTarget bound thrown)
  | sequence {b stack next broken returned thrown entry} :
      Routes nodes bound stack next broken returned thrown →
      (nodes[entry]?).map AnnotatedNode.site = some (frontSite b stack) →
      Routes nodes bound (.sequence b :: stack) entry broken returned thrown
  | loop {b stack next broken returned thrown header} :
      Routes nodes bound stack next broken returned thrown →
      (nodes[header]?).map AnnotatedNode.site = some (.command (.loop b) stack) →
      Routes nodes bound (.loop b :: stack) header next returned thrown
  | catcher {x d stack next broken returned thrown entry} :
      Routes nodes bound stack next broken returned thrown → x < bound →
      (nodes[entry]?).map AnnotatedNode.site = some (frontSite d stack) →
      Routes nodes bound (.catcher x d :: stack) next broken returned (resultTarget bound entry x)

def targetEnv (target : Target) (v : Tm) (graph : Env) : Env :=
  PointClaims.mapEnv target.mapping (push v graph)

theorem payload_read (bound : Nat) (label : Nat) (v : Tm) (graph : Env) :
    targetEnv (payloadTarget bound label) v graph (bound + 3) = v := by
  unfold targetEnv payloadTarget resultTarget
  rw [mapped_replace (by unfold width; omega)]
  simp [bindName]

theorem Routes.normal_site {nodes bound stack next broken returned thrown}
    (routing : Routes nodes bound stack next broken returned thrown) (graph ρ : Env) :
    ∃ site, (nodes[next]?).map AnnotatedNode.site = some site ∧
      site.control bound graph = (route stack .normal ρ).1 := by
  induction routing with
  | root hn _ _ _ => exact ⟨.normal, hn, rfl⟩
  | sequence _ entry _ => exact ⟨_, entry, frontSite_control _ _ _ _⟩
  | loop _ header _ => exact ⟨_, header, rfl⟩
  | catcher _ _ _ ih => exact ih

theorem Routes.break_site {nodes bound stack next broken returned thrown}
    (routing : Routes nodes bound stack next broken returned thrown) (graph ρ : Env) :
    ∃ site, (nodes[broken]?).map AnnotatedNode.site = some site ∧
      site.control bound graph = (route stack .break ρ).1 := by
  induction routing with
  | root _ hb _ _ => exact ⟨.broken, hb, rfl⟩
  | sequence _ _ ih => exact ih
  | loop outer _ _ => exact outer.normal_site graph ρ
  | catcher _ _ _ ih => exact ih

theorem Routes.return_site {nodes bound stack next broken returned thrown}
    (routing : Routes nodes bound stack next broken returned thrown) :
    (nodes[returned]?).map AnnotatedNode.site = some .returned := by
  induction routing <;> assumption

/-- The real exception map matches the stack interpreter, including the
caught binding. It preserves original names beyond the finite frame. -/
theorem Routes.throw_site {nodes bound stack next broken returned thrown}
    (routing : Routes nodes bound stack next broken returned thrown) (outer graph : Env) (v : Val) :
    ∃ site, (nodes[thrown.label]?).map AnnotatedNode.site = some site ∧
      (site.control bound (targetEnv thrown v graph), restore bound outer (targetEnv thrown v graph)) =
        route stack (.thrown v) (restore bound outer graph) := by
  induction routing with
  | root _ _ _ ht =>
    refine ⟨.thrown, ht, ?_⟩
    have envEq (label : Nat) : restore bound outer (targetEnv (payloadTarget bound label) v graph) = restore bound outer graph :=
      restore_payload bound outer graph v
    simp only [Site.control, payload_read, envEq, route]
  | sequence _ _ ih => exact ih
  | loop _ _ ih => exact ih
  | catcher _ hx entry _ =>
    refine ⟨_, entry, ?_⟩
    rw [frontSite_control]
    exact congrArg (Prod.mk _) (restore_replace hx outer graph v)

theorem Routes.throw_host {nodes bound stack next broken returned thrown}
    (routing : Routes nodes bound stack next broken returned thrown) (graph : Env) (v : Val) :
    (hostTemplate bound).close (targetEnv thrown v graph) = (hostTemplate bound).close graph := by
  induction routing with
  | root => exact host_payload bound graph v
  | sequence _ _ ih | loop _ _ ih => exact ih
  | catcher _ hx _ _ => exact host_replace hx graph v

theorem Routes.normal_trace {nodes bound stack next broken returned thrown}
    (routing : Routes nodes bound stack next broken returned thrown) (host : NativeCode)
    (outer graph : Env) (h : Heap) :
    ∃ site, (nodes[next]?).map AnnotatedNode.site = some site ∧
      CommandMachine.Runs host (.exit .normal stack) (restore bound outer graph) h 0
        (site.control bound graph) (restore bound outer graph) h := by
  obtain ⟨site, lookup, control⟩ := routing.normal_site graph (restore bound outer graph)
  refine ⟨site, lookup, ?_⟩
  have run := route_trace host stack .normal (restore bound outer graph) h
  rw [route_normal_env, ← control] at run
  exact run

theorem Routes.break_trace {nodes bound stack next broken returned thrown}
    (routing : Routes nodes bound stack next broken returned thrown) (host : NativeCode)
    (outer graph : Env) (h : Heap) :
    ∃ site, (nodes[broken]?).map AnnotatedNode.site = some site ∧
      CommandMachine.Runs host (.exit .break stack) (restore bound outer graph) h 0
        (site.control bound graph) (restore bound outer graph) h := by
  obtain ⟨site, lookup, control⟩ := routing.break_site graph (restore bound outer graph)
  refine ⟨site, lookup, ?_⟩
  have run := route_trace host stack .break (restore bound outer graph) h
  rw [route_break_env, ← control] at run
  exact run

theorem Routes.return_trace {nodes bound stack next broken returned thrown}
    (routing : Routes nodes bound stack next broken returned thrown) (host : NativeCode)
    (outer graph : Env) (v : Val) (h : Heap) :
    (nodes[returned]?).map AnnotatedNode.site = some .returned ∧
      CommandMachine.Runs host (.exit (.returned v) stack) (restore bound outer graph) h 0
        (Site.returned.control bound (targetEnv (payloadTarget bound returned) v graph))
        (restore bound outer (targetEnv (payloadTarget bound returned) v graph)) h := by
  refine ⟨routing.return_site, ?_⟩
  have run := route_trace host stack (.returned v) (restore bound outer graph) h
  rw [route_returned] at run
  have envEq : restore bound outer (targetEnv (payloadTarget bound returned) v graph) = restore bound outer graph :=
    restore_payload bound outer graph v
  simpa only [Site.control, payload_read, envEq] using run

theorem Routes.throw_trace {nodes bound stack next broken returned thrown}
    (routing : Routes nodes bound stack next broken returned thrown) (host : NativeCode)
    (outer graph : Env) (v : Val) (h : Heap) :
    ∃ site, (nodes[thrown.label]?).map AnnotatedNode.site = some site ∧
      CommandMachine.Runs host (.exit (.thrown v) stack) (restore bound outer graph) h 0
        (site.control bound (targetEnv thrown v graph)) (restore bound outer (targetEnv thrown v graph)) h := by
  obtain ⟨site, lookup, states⟩ := routing.throw_site outer graph v
  refine ⟨site, lookup, ?_⟩
  have run := route_trace host stack (.thrown v) (restore bound outer graph) h
  rw [← states] at run
  exact run

end Verification.Paper.TolerantFrames.Compiler
