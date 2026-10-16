import Verification.Programs.Parametricity
import Verification.Programs.ExpressionEffects

/-! # Graph code: a closure whose body is a checked graph

A closure's code may be a control-flow graph (`CallCode.graph`), the body form
a module function has. Invoking it starts a run of that graph at its entry
(`Tm.goto`), which the term machine executes node by node (`Tm.frame`), with
the graph machine's transitions as its steps. This file proves that the two
machines agree: a run of graph code simulates `ControlFlow.Transition`
step for step, so the graph checker's safety theorem (`accepted_inputs_safe`)
is safety of the term that runs the code. -/
namespace Verification.GraphCode
open ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

/-- The graph a code's node lists describe. -/
def program (E : List Tm) (K : List (Continuation × Option Target)) : Program :=
  (E.zip K).map fun (e, k, x) => ⟨e, k, x⟩

theorem program_node {E : List Tm} {K : List (Continuation × Option Target)} {l : Nat}
    {node : Node} (h : (program E K)[l]? = some node) :
    E[l]? = some node.expression ∧ K[l]? = some (node.continuation, node.handler) := by
  simp only [program, List.getElem?_map] at h
  obtain ⟨⟨e, k, x⟩, hz, rfl⟩ := Option.map_eq_some_iff.mp h
  have := List.getElem?_zip_eq_some.mp hz
  exact ⟨this.1, this.2⟩

theorem push_envOf (v : Tm) (L : List Tm) (d : Tm) : push v (envOf L d) = envOf (v :: L) d := by
  funext i; cases i <;> rfl

theorem mapEnv_envOf (m : Option (List Nat)) (L : List Tm) (d : Tm) :
    mapEnv m (envOf L d) = envOf (envMap m L d).1 (envMap m L d).2 := by
  funext i
  cases m with
  | none => rfl
  | some slots =>
    simp only [mapEnv, slot, envOf, envMap]
    by_cases hi : i < slots.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    · have hn : slots[i]? = none := List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hn]

/-- A term that runs graph code, and the graph machine's state it stands for. -/
inductive Sim (E : List Tm) (K : List (Continuation × Option Target)) : Tm → State → Prop where
  | goto : Sim E K (.goto E K l L d) (.at l (envOf L d))
  | frame : Sim E K (.frame E K t L d k x) (.eval t (envOf L d) k x)
  | done : isVal v = true → Sim E K v (.done v)
  | raised : isVal v = true → isSourceVal v = true → Sim E K (.throw v) (.raised v)

theorem sim_goto {E K l m L d} :
    Sim E K (.goto E K l (envMap m L d).1 (envMap m L d).2) (.at l (mapEnv m (envOf L d))) := by
  rw [mapEnv_envOf]; exact .goto

/-- Each transition of the graph is one step of the term that runs it. -/
theorem sim_step {E K ts s h h' s'} (hs : Sim E K ts s)
    (step : Transition (program E K) h s h' s') : ∃ ts', Step h ts h' ts' ∧ Sim E K ts' s' := by
  cases hs with
  | goto =>
    cases step with
    | enter hn =>
      obtain ⟨he, hk⟩ := program_node hn
      exact ⟨_, .gotoEnter he hk, .frame⟩
  | frame =>
    cases step with
    | expr st => exact ⟨_, .frameC st, .frame⟩
    | ret hv => exact ⟨_, .frameRet hv, .done hv⟩
    | bind hv =>
      refine ⟨_, .frameBind hv, ?_⟩
      rw [push_envOf]; exact sim_goto
    | effect hv => exact ⟨_, .frameEffect hv, sim_goto⟩
    | yes => exact ⟨_, .frameYes, sim_goto⟩
    | no => exact ⟨_, .frameNo, sim_goto⟩
    | yesBind =>
      refine ⟨_, .frameYesBind, ?_⟩
      rw [push_envOf]; exact sim_goto
    | noBind =>
      refine ⟨_, .frameNoBind, ?_⟩
      rw [push_envOf]; exact sim_goto
    | tagBind hv =>
      refine ⟨_, .frameTag hv, ?_⟩
      rw [push_envOf]; exact sim_goto
    | handle hr =>
      refine ⟨_, .frameHandle hr, ?_⟩
      rw [push_envOf]; exact sim_goto
    | raise hr => exact ⟨_, .frameRaise hr, .raised (raises_val hr) (raises_sourceVal hr)⟩
  | done hv => cases step
  | raised _ _ => cases step

/-- **The term running graph code is as safe as the graph.** -/
theorem safe_of_sim {E K T} : ∀ (n : Nat) (W : WorldT n) (h : Heap) {ts s},
    Sim E K ts s → SafeGraph Ξ (program E K) T n W h s → Safe Ξ T n W h ts := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ts s hs hg
    rcases hg with (⟨v, rfl, hv, hT⟩ | ⟨v, rfl, hsc⟩) | ⟨U, h', s', hx, hu, step, hh, hg⟩
    · cases hs; exact Or.inl (Or.inl ⟨hv, hT⟩)
    · cases hs with
      | raised hv hj => exact Or.inl (Or.inr ⟨v, .throwV hv hj, hsc⟩)
    · obtain ⟨ts', st, hs'⟩ := sim_step hs step
      exact Or.inr ⟨U, h', ts', hx, hu, st, hh, ih U h' hs' hg⟩

/-- A graph run started at an entry the checker accepted is safe. -/
theorem goto_safe {G : NormalGraph ι} [DecidableEq ι] {images : InstanceImageCheck G} {Rty : Ty ι}
    {E K C start inputs} {codes : CodeEntry ι → Bool}
    (hc : checkEntryUsing G images Rty (program E K) C start inputs codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes)
    (n W h L d) (he : EnvOk G inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W h) :
    Safe (excOf G) (meaning G Rty) n W h (.goto E K start L d) :=
  safe_of_sim n W h .goto (accepted_inputs_safe hc n W h (envOf L d) he hw hh hcodes)

/-- A normal-return postcondition up to the current budget, independent of the
world chosen by a parallel safety derivation. Throws impose no postcondition. -/
def ReturnsPost (Q : HeapObservations.Post) (n : Nat) (h : Heap) (t : Tm) : Prop :=
  ∀ k h' v, k < n → HeapObservations.Steps k h t h' v → isVal v = true → Q h' v

theorem returnsPost_of_safePost {T Q} : ∀ {n W h t},
    HeapObservations.SafePost Ξ T Q n W h t → ReturnsPost Q n h t := by
  intro n
  induction n with
  | zero => intro W h t hs k h' v hk; omega
  | succ n ih =>
    intro W h t hs k h' v hk run hv
    cases run with
    | refl =>
      rcases hs with (⟨_, _, hq⟩ | hr) | ⟨_, _, _, _, _, st, _, _⟩
      · exact hq
      · exact absurd hr (val_not_thrown hv)
      · exact False.elim (value_no_step hv st)
    | next st run =>
      rcases hs with (⟨ht, _, _⟩ | hr) | ⟨U, h'', t'', _, _, st', _, hs'⟩
      · exact False.elim (value_no_step ht st)
      · exact absurd st hr.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st st'
        exact ih hs' _ _ _ (by omega) run hv

theorem ReturnsPost.step {Q n h t h' t'} (hp : ReturnsPost Q (n+1) h t)
    (st : Step h t h' t') : ReturnsPost Q n h' t' := by
  intro k h'' v hk run hv
  exact hp (k+1) h'' v (by omega) (.next st run) hv

theorem ReturnsPost.value {Q n h v} (hp : ReturnsPost Q (n+1) h v)
    (hv : isVal v = true) : Q h v := hp 0 h v (by omega) .refl hv

/-- An effect annotation on a checked graph node. The precondition is the same
point context and knowledge that ordinary graph checking established. -/
def NodePreserves [DecidableEq ι] (G : NormalGraph ι) (c : NodeEvidence ι) (t : Tm) : Prop :=
  ∀ n W h ρ, EnvOk G (entry c) ρ n W → HeapKnowledge.Holds c.knowledge ρ h →
    WorldAdm W → HeapOk n W h →
    HeapObservations.SafePost (excOf G) (meaning G (result c))
      (CallEffects.Effect.preservesInputHeap.post h) n W h (instantiate 0 ρ t)

/-- While a call is running its entry heap need not be preserved yet. Only the
postcondition on normal return can justify the next graph node. -/
def PreservingState (initial : Heap) (n : Nat) (h : Heap) : State → Prop
  | .at .. | .done _ => initial.IsPrefix h
  | .eval t _ _ handler => handler = none ∧
      ReturnsPost (CallEffects.Effect.preservesInputHeap.post initial) n h t
  | .raised _ => True

theorem preserving_step [DecidableEq ι] {G : NormalGraph ι} {Rty : Ty ι} {P : Program} {C : Certificate ι}
    (hnodes : ∀ (l : Nat) (node : Node) (c : NodeEvidence ι), P[l]? = some node → C[l]? = some c →
      node.handler = none ∧ NodePreserves G c node.expression)
    {initial n W h s h' s'} (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hs : StateOk G Rty C (n+1) W h s) (hp : PreservingState initial (n+1) h s)
    (st : Transition P h s h' s') : PreservingState initial n h' s' := by
  cases st with
  | enter hn =>
    obtain ⟨c, hc, he, hf⟩ := hs
    obtain ⟨hx, ht⟩ := hnodes _ _ c hn hc
    refine ⟨hx, ?_⟩
    apply returnsPost_of_safePost
    apply HeapObservations.weaken (fun _ _ hpost => hp.trans hpost)
    exact ht n _ h _ (he.transfer n (Nat.le_succ n) _ (WExt_refl _)) hf
      (WorldAdm_trunc _ hw) (HeapOk_trunc n W h hh)
  | expr st => exact ⟨hp.1, hp.2.step st⟩
  | ret hv | bind hv | effect hv | tagBind hv => exact hp.2.value hv
  | yes | no | yesBind | noBind => exact hp.2.value rfl
  | handle _ => cases hp.1
  | raise _ => trivial

/-- The effect proof reuses ordinary graph progress and its point assertions.
There is one control-flow checker, including for cycles and branch refinements. -/
theorem preserving_safe_of_sim [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Rty : Ty ι} {E : List Tm} {K : List (Continuation × Option Target)}
    {C : Certificate ι}
    {codes : CodeEntry ι → Bool} (hg : checkGraphUsing G images Rty (program E K) C codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes)
    (hnodes : ∀ (l : Nat) (node : Node) (c : NodeEvidence ι), (program E K)[l]? = some node → C[l]? = some c →
      node.handler = none ∧ NodePreserves G c node.expression) :
    ∀ n W h ts s initial, Sim E K ts s → WorldAdm W → HeapOk n W h →
      StateOk G Rty C n W h s → PreservingState initial n h s →
      HeapObservations.SafePost (excOf G) (meaning G Rty)
        (CallEffects.Effect.preservesInputHeap.post initial) n W h ts := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ts s initial sim hw hh hs hp
    rcases state_progress hg hcodes hw hh hs with
      (⟨v, rfl, hv, ht⟩ | ⟨v, rfl, hsc⟩) | ⟨U, h', s', hx, hu, st, hok, hs'⟩
    · cases sim; exact .inl (.inl ⟨hv, ht, hp⟩)
    · cases sim with
      | raised hv hj => exact .inl (.inr ⟨v, .throwV hv hj, hsc⟩)
    · obtain ⟨ts', step, sim'⟩ := sim_step sim st
      exact .inr ⟨U, h', ts', hx, hu, step, hok,
        ih U h' ts' s' initial sim' hu hok hs'
          (preserving_step hnodes hw hh hs hp st)⟩

theorem goto_preserving [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Rty : Ty ι} {E : List Tm} {K : List (Continuation × Option Target)}
    {C : Certificate ι} {start inputs}
    {codes : CodeEntry ι → Bool}
    (hc : checkEntryUsing G images Rty (program E K) C start inputs codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes)
    (hnodes : ∀ (l : Nat) (node : Node) (c : NodeEvidence ι), (program E K)[l]? = some node → C[l]? = some c →
      node.handler = none ∧ NodePreserves G c node.expression)
    (n W h L d) (he : EnvOk G inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W h) :
    HeapObservations.SafePost (excOf G) (meaning G Rty)
      (CallEffects.Effect.preservesInputHeap.post h) n W h (.goto E K start L d) := by
  simp only [checkEntryUsing_eq, Bool.and_eq_true] at hc
  have hx := hc.2
  split at hx
  · rename_i c hstart
    have hem : entry c = inputs ∧ c.knowledge = ⟨[],[],[]⟩ := of_decide_eq_true hx
    apply preserving_safe_of_sim hc.1 hcodes hnodes n W h _ _ h .goto hw hh
    · refine ⟨c, hstart, ?_, ?_⟩
      · simpa only [hem.1] using he
      · rw [hem.2]; exact HeapKnowledge.empty _ h
    · exact ⟨[], by simp⟩
  · contradiction

/-! ## A unit's table of checked code

Graph code is checked by the graph checker, and its creation is typed by
naming what was checked (`ProgramCertificates.Rule.funGraph`). A unit's
certificate therefore checks its codes in order, each against the table of the
ones before it — a code creates only code nested in it, whose check comes
first — and the unit's own graph against the whole table. -/

/-- A table as the evidence checker reads it. -/
def admits [DecidableEq ι] (table : List (CodeEntry ι)) (c : CodeEntry ι) : Bool :=
  table.contains c

/-- Each executed node must establish preservation on normal return. A handler
could turn a throwing call into a normal return after untracked mutation, so
this composition rule admits only graphs without handlers. Pure graphs retain
the independent operational rule, which also covers their handlers. -/
@[nospecialize] def compositionalCheckedResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι) : ProgramCertificates.CheckResult ι Unit :=
  ProgramCertificates.CheckResult.allLocated (P.zip C) .node fun (node,c) =>
    (ProgramCertificates.CheckResult.ofBool (node.handler.isNone &&
      ProgramCertificates.checkScope (entry c).length node.expression)).bind fun _ =>
    (ProgramCertificates.CheckResult.ofBool (ExpressionEffects.check G (entry c) node.expression)).orElse fun _ =>
    (ProgramCertificates.CheckResult.ofBool (decide ((ProgramCertificates.claim c.expression).term = node.expression))).bind fun _ =>
    (ProgramCertificates.checkTreeResult G images c.expression).bind fun _ =>
    ProgramCertificates.CheckResult.ofBool (ExpressionEffects.selectedCallPreserves c.expression)

@[nospecialize] def compositionalChecked [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι) : Bool :=
  (compositionalCheckedResult G images P C).accepted

theorem compositionalChecked_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι) :
    compositionalChecked G images P C = (
  (P.zip C).all fun (node,c) => node.handler.isNone &&
    ProgramCertificates.checkScope (entry c).length node.expression &&
    (ExpressionEffects.check G (entry c) node.expression ||
      (decide ((ProgramCertificates.claim c.expression).term = node.expression) &&
        ProgramCertificates.checkTreeUsing G images c.expression &&
        ExpressionEffects.selectedCallPreserves c.expression))
  ) := by
  simp only [compositionalChecked, compositionalCheckedResult, ProgramCertificates.CheckResult.accepted_allLocated,
    ProgramCertificates.CheckResult.accepted_bind, ProgramCertificates.CheckResult.accepted_orElse,
    ProgramCertificates.CheckResult.accepted_ofBool, ProgramCertificates.checkTreeUsing, Bool.and_assoc]

@[simp] theorem compositionalChecked_reassign [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (η : MixedAssignment ι) (P : Program) (C : Certificate ι) :
    compositionalChecked (reassign G η) (images.reassign η) P C = compositionalChecked G images P C := by
  simp only [compositionalChecked_eq, ExpressionEffects.check, ExpressionEffects.readable,
    Parametricity.expand_reassign, Parametricity.checkTree_reassign]

/-- Definition effects supplement, rather than replace, ordinary safety. -/
@[nospecialize] def effectCheckedResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (c : CodeEntry ι) (C : Certificate ι) : ProgramCertificates.CheckResult ι Unit :=
  match c.row.effect with
  | .unrestricted => pure ()
  | .preservesInputHeap =>
      (ProgramCertificates.CheckResult.ofBool (c.exprs.all Purity.pureTerm)).orElse fun _ =>
      compositionalCheckedResult G images (program c.exprs c.conts) C

@[nospecialize] def effectChecked [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (c : CodeEntry ι) (C : Certificate ι) : Bool :=
  (effectCheckedResult G images c C).accepted

theorem effectChecked_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (c : CodeEntry ι) (C : Certificate ι) :
    effectChecked G images c C = (
  match c.row.effect with
  | .unrestricted => true
  | .preservesInputHeap => c.exprs.all Purity.pureTerm ||
      compositionalChecked G images (program c.exprs c.conts) C
  ) := by
  cases h : c.row.effect <;>
    simp only [effectChecked, effectCheckedResult, h, ProgramCertificates.CheckResult.accepted_orElse,
      ProgramCertificates.CheckResult.accepted_ofBool, compositionalChecked] <;> rfl

@[simp] theorem effectChecked_reassign [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (η : MixedAssignment ι) (c : CodeEntry ι) (C : Certificate ι) :
    effectChecked (reassign G η) (images.reassign η) c C = effectChecked G images c C := by
  simp only [effectChecked_eq, compositionalChecked_reassign]

/-- One code entry, checked at its signature from the frame the signature
describes, against an earlier table. -/
@[nospecialize] def codeCheckedResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (table : List (CodeEntry ι)) (c : CodeEntry ι) (C : ControlFlow.Certificate ι) : ProgramCertificates.CheckResult ι Unit :=
  (ProgramCertificates.CheckResult.ofBool (decide (c.arity ≤ c.row.arguments.length))).bind fun _ =>
  (effectCheckedResult G images c C).bind fun _ =>
  checkEntryResult G images c.row.result (program c.exprs c.conts) C c.start
    (codeFrame c.arity c.row c.captures c.store) (admits table)

@[nospecialize] def codeCheckedUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (table : List (CodeEntry ι)) (c : CodeEntry ι) (C : ControlFlow.Certificate ι) : Bool :=
  (codeCheckedResult G images table c C).accepted

theorem codeCheckedUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (table : List (CodeEntry ι)) (c : CodeEntry ι) (C : ControlFlow.Certificate ι) :
    codeCheckedUsing G images table c C = (
  decide (c.arity ≤ c.row.arguments.length) && effectChecked G images c C &&
    checkEntryUsing G images c.row.result (program c.exprs c.conts) C c.start
      (codeFrame c.arity c.row c.captures c.store) (admits table)
  ) := by
  simp only [codeCheckedUsing, codeCheckedResult, ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_ofBool, effectChecked, checkEntryUsing, Bool.and_assoc]

/-- A checked entry meets its signature in the graph reassigned at every
assignment: the check reads none (`Parametricity.checkEntry_reassign`). -/
theorem codeChecked_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {table c C} (htable : ProgramCertificates.CodesSound G (admits table))
    (h : codeCheckedUsing G images table c C = true) : ∀ η, c.Spec (reassign G η) := by
  intro η
  simp only [codeCheckedUsing_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  have hc : checkEntryUsing (reassign G η) (images.reassign η) c.row.result
      (program c.exprs c.conts) C c.start
      (codeFrame c.arity c.row c.captures c.store) (admits table) = true := by
    exact (Parametricity.checkEntry_reassign G η images _ _ _ _ _ _).trans h.2
  have ht : ProgramCertificates.CodesSound (reassign G η) (admits table) :=
    fun e he η' => htable e he η'
  refine ⟨h.1.1, ?_⟩
  intro n W heap L he hw hh hvalues
  have hs := goto_safe hc ht n W heap L .nul he hw hh
  cases heffect : c.row.effect with
  | unrestricted =>
    simpa [heffect, CallEffects.Effect.post] using HeapObservations.forget hs
  | preservesInputHeap =>
    have hp : c.exprs.all Purity.pureTerm = true ∨
        compositionalChecked (reassign G η) (images.reassign η) (program c.exprs c.conts) C = true := by
      simpa [effectChecked_eq, heffect, Bool.or_eq_true] using h.1.2
    rcases hp with hp | hp
    · have hp : ∀ e ∈ c.exprs, Purity.pureTerm e = true := List.all_eq_true.mp hp
      simpa [heffect] using CallEffects.pure_safe (.goto hp hvalues rfl) hs
    · rw [compositionalChecked_eq] at hp
      apply goto_preserving hc ht _ n W heap L .nul he hw hh
      intro l node point hn hpoint
      have hzip : ((program c.exprs c.conts).zip C)[l]? = some (node,point) :=
        List.getElem?_zip_eq_some.mpr ⟨hn,hpoint⟩
      have hmem := List.mem_of_getElem? hzip
      have hp := List.all_eq_true.mp hp (node,point) hmem
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
      refine ⟨hp.1.1, ?_⟩
      intro j V h' ρ henv hknowledge hworld hheap
      have hgraph : checkGraphUsing (reassign G η) (images.reassign η) c.row.result
          (program c.exprs c.conts) C (admits table) = true := by
        have hchecked := hc
        simp only [checkEntryUsing_eq, Bool.and_eq_true] at hchecked
        exact hchecked.1
      obtain ⟨actual,hactual,hterm,-⟩ := graph_node hgraph ht hpoint
      cases hn.symm.trans hactual
      have hcases := hp.2
      simp only [Bool.or_eq_true] at hcases
      rcases hcases with hexpr | hcall
      · exact ExpressionEffects.sound hexpr hp.1.2 henv hheap
          (HeapObservations.erase (hterm j V h' ρ henv hknowledge hworld hheap))
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcall
        have hs := ExpressionEffects.selectedCall_sound point.expression hcall.1.2 hcall.2
          (ProgramCertificates.codesSound_none _) henv hworld hheap
        simpa only [ControlFlow.result, hcall.1.1] using hs

/-- Check codes in order, each against the table of those before it. -/
@[nospecialize] def extendTableResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) :
    List (CodeEntry ι) → List (CodeEntry ι × ControlFlow.Certificate ι) →
      ProgramCertificates.CheckResult ι (List (CodeEntry ι))
  | table, [] => pure table
  | table, (c, C) :: rest =>
      ((codeCheckedResult G images table c C).at (.code table.length)).bind fun _ => extendTableResult G images (table ++ [c]) rest

@[nospecialize] def extendTable [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (table : List (CodeEntry ι)) (checks : List (CodeEntry ι × ControlFlow.Certificate ι)) :
    Option (List (CodeEntry ι)) :=
  (extendTableResult G images table checks).value

theorem extendTable_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (table : List (CodeEntry ι)) (checks : List (CodeEntry ι × ControlFlow.Certificate ι)) :
    extendTable G images table checks = match checks with
    | [] => some table
    | (c, C) :: rest =>
        if codeCheckedUsing G images table c C then extendTable G images (table ++ [c]) rest else none := by
  cases checks with
  | nil => rfl
  | cons pair rest =>
    rcases pair with ⟨c, C⟩
    rw [extendTable, extendTableResult, ProgramCertificates.CheckResult.value_bind_const]
    rfl

theorem extendTable_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} :
    ∀ {table checks result}, ProgramCertificates.CodesSound G (admits table) →
      extendTable G images table checks = some result →
      ProgramCertificates.CodesSound G (admits result)
  | table, [], result, ht, h => by
    rw [extendTable_eq] at h
    simp only [Option.some.injEq] at h; subst h; exact ht
  | table, (c, C) :: rest, result, ht, h => by
    rw [extendTable_eq] at h
    dsimp only at h
    split at h
    · rename_i hc
      apply extendTable_sound _ h
      intro e he
      simp only [admits, List.contains_append, Bool.or_eq_true, List.contains_cons,
        List.contains_nil, Bool.or_false, beq_iff_eq] at he
      rcases he with he | rfl
      · exact ht e he
      · exact codeChecked_sound ht hc
    · contradiction

/-- A unit's codes, checked from the empty table. -/
@[nospecialize] def checkCodesResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (checks : List (CodeEntry ι × ControlFlow.Certificate ι)) :
    ProgramCertificates.CheckResult ι (List (CodeEntry ι)) :=
  extendTableResult G images [] checks

@[nospecialize] def checkCodesUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (checks : List (CodeEntry ι × ControlFlow.Certificate ι)) : Option (List (CodeEntry ι)) :=
  (checkCodesResult G images checks).value

/-- A checked table is sound at every reassignment of the graph's parameter
rows, since `CodesSound` quantifies over all of them. -/
theorem checkCodes_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checks table} (h : checkCodesUsing G images checks = some table) :
    ProgramCertificates.CodesSound G (admits table) :=
  extendTable_sound (fun c hc => by simp [admits] at hc) h

#print axioms safe_of_sim
#print axioms goto_safe
#print axioms checkCodes_sound
end Verification.GraphCode
