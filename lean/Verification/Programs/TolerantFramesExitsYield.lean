import Verification.Programs.TolerantFramesExitExecution
import Verification.Programs.TolerantFramesExitWidths

/-! # Assembly of checked exits into the graph's exit obligation -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Assembly
variable {ι : Type} [Labels ι]

namespace ExitChecks

/-- The witnesses of `NodeExitTrace`, shared by all field obligations. -/
structure Site {G : NormalGraph ι} {I : InstanceImageCheck G} (c : Target.RunCall G I)
    (r : RunWalkA G I c) (l : Nat) (hl : r.w.visited l) where
  raw : SinglePass.Walk ι
  env : SinglePass.WalkEnv ι G I
  σ : SinglePass.WalkState ι G
  en : SinglePass.Entered ι
  sd : SinglePass.StepDone ι G
  ex : SinglePass.ExitsDone ι G
  facts : r.w = ofPass raw (passHeads c) ∧ r.edgesIn = passEdgesIn raw ∧
    env.nodes = c.P.toArray ∧ env.claimed = c.claims.toArray ∧ env.codes = c.codes ∧
    env.passChecker = c.passChecker ∧
    (∀ t, (env.isHead[t]?).getD false = passHeads c t) ∧
    (∀ t, env.stated[t]! = passStated c t) ∧
    SinglePass.visitEntry G I env σ l = .ok en ∧
    SinglePass.visitStep G I env σ l en = .ok sd ∧
    SinglePass.visitExits G I env σ l en sd = .ok ex ∧
    (r.node l hl).node = env.nodes[l]! ∧ (r.node l hl).c = env.claimed[l]! ∧
    (r.node l hl).entry = en.entry ∧ (r.node l hl).st = sd.st ∧
    (r.node l hl).ans = sd.steppedAnswers ∧ (r.node l hl).ys = sd.yields.getD [] ∧ en.implies = r.w.implies l ∧
    σ.walk.incoming.size = σ.walk.incomingImpl.size ∧ WalkExtends (exitsWalk ex) raw ∧
    ExitStepsChecked G I env l en sd raw ∧
    (en.here = true → HereEmpty G (env.claimed[l]!).context) ∧
    ExitRecordsChecked G I env l en sd ex ∧
    env.startNames = List.range c.inputs.length ∧
    env.argName = c.goal.slot.bind ((List.range c.inputs.length)[·]?)

/-- A trace supplies a common site, without extracting any exit checks. -/
theorem site_of_trace {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I}
    {r : RunWalkA G I c} {l : Nat} {hl : r.w.visited l}
    (h : NodeExitTrace c r.edgesIn (r.node l hl)) : Nonempty (Site c r l hl) := by
  obtain ⟨raw, env, σ, en, sd, ex, h⟩ := h
  exact ⟨⟨raw, env, σ, en, sd, ex, h⟩⟩

variable {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I}
    {r : RunWalkA G I c} {l : Nat} {hl : r.w.visited l}

/-- The name-indexed yields whose slot translation is passed to `exitStep`. -/
@[nospecialize] def Site.ysA (s : Site c r l hl) : List (PromiseCalls.Yield ι) :=
  (SinglePass.exitsYields G I s.env l s.en s.sd).1.getD []

/-- The empty-context answer and judged initial exit yields. -/
@[nospecialize] def Here (s : Site c r l hl) (η : MixedAssignment ι) : Prop :=
  let n := r.node l hl
  let H := reassign G η
  (s.en.here = true → HereEmpty H n.c.context) ∧
    ExitYieldsJudged H r.w (List.range c.inputs.length) l n.node n.c n.entry n.st s.ysA

/-- Normal and handler mappings stay within their source names. -/
@[nospecialize] def Widths (s : Site c r l hl) (_η : MixedAssignment ι) : Prop :=
  let n := r.node l hl
  (∀ (i : Nat) t pushed observed promote,
    (Exit.ofNode n.node)[i]? = some (Exit.normal t pushed observed promote) →
    ∀ slots, t.mapping = some slots → ∀ j ∈ slots, j < (normalNames n.entry n.st pushed).length) ∧
  (∀ t, n.node.handler = some t → ∀ slots, t.mapping = some slots → ∀ j ∈ slots,
    j < (s.sd.thrown :: n.entry.names).length)

/-- Each non-head exit has a judged cache and its recorded checks. -/
@[nospecialize] def NonHead (s : Site c r l hl) (η : MixedAssignment ι) : Prop :=
  let n := r.node l hl
  let H := reassign G η
  ∀ (i : Nat) t pushed observed promote,
    (Exit.ofNode n.node)[i]? = some (Exit.normal t pushed observed promote) →
    r.given t.label = false → ∃ ysE : List (PromiseCalls.Yield ι),
      ExitYieldsJudged H r.w (List.range c.inputs.length) l n.node n.c n.entry n.st ysE ∧
        NonHeadExitChecked H (I.reassign η) r.w r.ctx r.stated r.edgesIn l n.node n.c n.entry n.st n.ys
          s.ysA ysE s.en.here s.sd.outFresh i t pushed observed promote

/-- Each head exit has a judged cache and its checked head contract. -/
@[nospecialize] def Head (s : Site c r l hl) (η : MixedAssignment ι) : Prop :=
  let n := r.node l hl
  let H := reassign G η
  ∀ (i : Nat) t pushed observed promote,
    (Exit.ofNode n.node)[i]? = some (Exit.normal t pushed observed promote) →
    r.given t.label = true → ∃ ysE : List (PromiseCalls.Yield ι),
      ExitYieldsJudged H r.w (List.range c.inputs.length) l n.node n.c n.entry n.st ysE ∧
      ∃ (req written : HeapKnowledge.Knowledge) (cf : List HeapKnowledge.IndexAtom)
        (gimp : List (PromiseCalls.Implication ι)) (argName : Option Nat) (argSlots : List Nat)
        (inputSlots : List (Nat × Nat)) (hwidth hfresh : Nat),
        HeadExitChecked H (I.reassign η) r.w (List.range c.inputs.length) r.ctx r.stated l n.node n.c n.entry n.st
          n.ys ysE s.en.here i t pushed observed promote req written cf gimp argName argSlots inputSlots hwidth hfresh ∧
        (∀ y ∈ List.range c.inputs.length, y < hfresh) ∧
        (∀ a, argName = some a → ∃ q : Nat, (List.range c.inputs.length)[q]? = some a)

/-- Handler checks and the bound on its thrown name. -/
@[nospecialize] def Handler (s : Site c r l hl) (η : MixedAssignment ι) : Prop :=
  let n := r.node l hl
  let H := reassign G η
  (∀ t, n.node.handler = some t →
    HandlerExitChecked H (I.reassign η) r.w (List.range c.inputs.length) r.ctx r.stated r.given r.edgesIn l
      n.c n.entry n.st s.en.here s.sd.outFresh (s.sd.thrownTy.getD []) s.sd.thrown t) ∧
  (n.node.handler.isSome = true → NamesBelow n.entry (r.w.implies l) (List.range c.inputs.length) s.sd.thrown)

/-- The visit's freshness flag is the checked step flag. -/
@[nospecialize] def Fresh (s : Site c r l hl) : Prop :=
  let n := r.node l hl
  s.sd.outFresh = passOutFreshChecked G I c.codes n.ans.summaries.toList n.c n.node n.entry n.st.stepK
    (SinglePass.derivOf n.c n.node n.st)

/-- The explicit judgment-to-final-world bridge. -/
@[nospecialize] def Realization (s : Site c r l hl) (η : MixedAssignment ι) : Prop :=
  let n := r.node l hl
  ExitYieldRealization (reassign G η) r.w (List.range c.inputs.length) l n.node n.c n.entry n.st n.ys s.sd.outFresh

/-- The exact local extraction target, with witnesses fixed by execution. -/
@[nospecialize] def Extracted (s : Site c r l hl) (η : MixedAssignment ι) : Prop :=
  let n := r.node l hl
  NodeExitsChecked (reassign G η) (I.reassign η) r.w (List.range c.inputs.length) r.ctx r.stated r.given r.edgesIn l
    n.node n.c n.entry n.st n.ys s.en.here s.sd.outFresh s.ysA s.sd.thrown (s.sd.thrownTy.getD []) ∧
    Fresh s ∧ Realization s η

/-- The site's step equation fixes its checked freshness flag. -/
theorem exitChecks_fresh (s : Site c r l hl) : Fresh s := by
  obtain ⟨_, _, _, _, hcodes, _, _, _, _, hstep, _, hnode, hclaim,
    hentry, hst, hans, _⟩ := s.facts
  unfold Fresh
  simp only [hans, hclaim, hnode, hentry, hst]
  rw [← hcodes]
  exact visitStep_outFresh hstep

/-- The trace proves the empty-context half of `Here`; the initial exit
cache's judgment is the explicit remaining premise. -/
theorem exitChecks_here (s : Site c r l hl) (η : MixedAssignment ι)
    (initialYieldsJudged : ExitYieldsJudged (reassign G η) r.w (List.range c.inputs.length) l
      (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st s.ysA) : Here s η := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hclaim, _, _, _, _, _, _, _, _, hhere, _⟩ := s.facts
  refine ⟨?_, initialYieldsJudged⟩
  intro hh
  rw [hclaim]
  exact (hhere hh).reassign η

/-- Every source slot read by a successful indexed exit is in bounds. -/
theorem exitChecks_widths (s : Site c r l hl) (η : MixedAssignment ι) : Widths s η := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hnode, _, hentry, hst, _, _, _, _, _, hsteps, _⟩ := s.facts
  have bound : ∀ e ∈ Exit.ofNode s.env.nodes[l]!, ∀ slots, e.target.mapping = some slots →
      ∀ j ∈ slots, j < (exitNames s.en s.sd e).length := by
    intro e he slots hs j hj
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
    have hei : (e, i) ∈ (Exit.ofNode s.env.nodes[l]!).zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
    obtain ⟨a, b, hb, _⟩ := hsteps (e, i) hei
    obtain ⟨tc, _, hw⟩ := exitStep_mappingWidth hb
    simp only [hs, mappingWidthOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
    exact hw.2 j hj
  constructor
  · intro i t pushed observed promote hm slots hs j hj
    rw [hnode] at hm
    have hb := bound _ (List.mem_of_getElem? hm) slots hs j hj
    cases pushed <;> simpa only [exitNames, Exit.isHandler, Exit.pushed, Bool.false_eq_true, if_false,
      if_true, normalNames, hentry, hst] using hb
  · intro t ht slots hs j hj
    rw [hnode] at ht
    have hm : Exit.handler t ∈ Exit.ofNode s.env.nodes[l]! := by
      simp only [Exit.ofNode, ht, Option.toList_some, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton]
      exact Or.inr trivial
    have hb := bound _ hm slots hs j hj
    simpa only [exitNames, Exit.isHandler, if_true, hentry] using hb

/-- The checked step bounds every entry name below its handler name. -/
theorem exitChecks_thrownBelow (s : Site c r l hl) :
    NamesBelow (r.node l hl).entry (r.w.implies l) (List.range c.inputs.length) s.sd.thrown := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hstep, _, _, _, _, hst, _⟩ := s.facts
  rw [visitStep_thrown hstep, ← hst]
  exact namesBelow_mono (r.node l hl).hstep.fresh_le (r.node l hl).below

/-- The handler name bound comes from the checked step. Extraction of the
handler's edge checks is the explicit remaining premise. -/
theorem exitChecks_handler (s : Site c r l hl) (η : MixedAssignment ι)
    (handlerEdgeChecks : ∀ t, (r.node l hl).node.handler = some t →
      HandlerExitChecked (reassign G η) (I.reassign η) r.w (List.range c.inputs.length)
        r.ctx r.stated r.given r.edgesIn l (r.node l hl).c (r.node l hl).entry (r.node l hl).st
        s.en.here s.sd.outFresh (s.sd.thrownTy.getD []) s.sd.thrown t) : Handler s η :=
  ⟨handlerEdgeChecks, fun _ => exitChecks_thrownBelow s⟩

/-- The field obligations compose without any extraction assumption hidden in the proof. -/
theorem assemble (s : Site c r l hl) (η : MixedAssignment ι)
    (hh : Here s η) (hw : Widths s η) (hn : NonHead s η) (hhead : Head s η) (hx : Handler s η)
    (hf : Fresh s) (hr : Realization s η) : Extracted s η := by
  refine ⟨⟨hh.1, hh.2, hw.1, hw.2, ?_, hx.1, hx.2⟩, hf, hr⟩
  intro i t pushed observed promote hm
  cases hg : r.given t.label with
  | false =>
    obtain ⟨ysE, hy, hc⟩ := hn i t pushed observed promote hm hg
    exact ⟨ysE, hy, fun _ => hc, fun ht => by simp at ht⟩
  | true =>
    obtain ⟨ysE, hy, hc⟩ := hhead i t pushed observed promote hm hg
    exact ⟨ysE, hy, (fun ht => by simp at ht), fun _ => hc⟩

end ExitChecks

/-- Extraction at admitted reassigned graphs. Judged yields are semantic,
so their extraction has the run's sound-code and admitted-graph premises. -/
@[nospecialize] def ExitChecks.Extraction (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, WalkChecked c r → ∀ η, admits η →
      ∀ l (hl : r.w.visited l) (s : ExitChecks.Site c r l hl), ExitChecks.Extracted s η

/-- Field groups at every admitted site give the exact extraction premise. -/
theorem ExitChecks.extraction_of_fields
    (fields : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
      RunPremises G I c after admits → ∀ r : RunWalkA G I c, WalkChecked c r → ∀ η, admits η →
        ∀ l (hl : r.w.visited l) (s : ExitChecks.Site c r l hl),
          ExitYieldsJudged (reassign G η) r.w (List.range c.inputs.length) l
            (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st s.ysA ∧
          ExitChecks.NonHead s η ∧ ExitChecks.Head s η ∧
          (∀ t, (r.node l hl).node.handler = some t →
            HandlerExitChecked (reassign G η) (I.reassign η) r.w (List.range c.inputs.length)
              r.ctx r.stated r.given r.edgesIn l (r.node l hl).c (r.node l hl).entry (r.node l hl).st
              s.en.here s.sd.outFresh (s.sd.thrownTy.getD []) s.sd.thrown t) ∧
          ExitChecks.Realization s η) : ExitChecks.Extraction ι := by
  intro G I c after admits hp r hc η ha l hl s
  obtain ⟨hh, hn, hhead, hx, hr⟩ := fields G I c after admits hp r hc η ha l hl s
  exact ExitChecks.assemble s η (ExitChecks.exitChecks_here s η hh) (ExitChecks.exitChecks_widths s η)
    hn hhead (ExitChecks.exitChecks_handler s η hx) (ExitChecks.exitChecks_fresh s) hr

/-- The exit obligation from the explicit local extraction premise. -/
theorem exitsYield_of_checks (checks : ExitChecks.Extraction ι) : ExitsYield ι := by
  intro G I c after admits hp r hchecked η ha ρ0 m l hl
  obtain ⟨dead, hnodes⟩ := hchecked
  obtain ⟨s⟩ := ExitChecks.site_of_trace (hnodes l hl).2
  obtain ⟨hc, hf, hr⟩ := checks G I c after admits hp r ⟨dead, hnodes⟩ η ha l hl s
  have hsums := (r.node l hl).hstep.summaries (r.node l hl).sums
  have hcodes := codesSound_reassign hp.2.2.1 η
  exact nodeExitsY_of_checks η hc hf (r.node l hl).hshape (r.node l hl).wf
    (r.node l hl).width List.nodup_range hr (subtypeAnswersAll _ _) hcodes
    (Parametricity.summariesSound_reassign G η I hsums) m

end Assembly
end Verification.TolerantFrames
