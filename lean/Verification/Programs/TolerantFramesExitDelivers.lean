import Verification.Programs.TolerantFramesExitTyped
import Verification.Programs.TolerantFramesMapNames

/-! # Tolerant frames: a normal exit into a node other than a loop head delivers from its checks

What `exitStep` checks on a normal exit into a node other than a loop
head, stated at the node's values (`NonHeadExitChecked`): the exit's
types (`ExitTyped`, where the exit is not vacuous), the state and
implications it pushed among the target's incoming, the target's written
assertion over the edge's facts at the context the yields refine, and at
a merge the edge as the merge reads it. Proved (`nonHeadExit_delivers`):
from those checks, the subtype answers sound and the mapping's names
sound, the exit delivers `edgePreAJ` from the state after the step, its
kept yields, its output and, where the step's result is fresh, its
freshness (`FreshAt`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section NonHead
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- The edge's context of a normal exit: the claim's type pushed where the
exit pushes the result. -/
def exitCtx (c : PointClaim ι) (pushed : Bool) : List (Ty ι) := if pushed then c.type :: c.context else c.context

/-- The edge's names of a normal exit: the step's result pushed where the
exit pushes it. -/
def normalNames (entry : SinglePass.State) (st : Stepped ι) (pushed : Bool) : List Nat :=
  if pushed then st.result :: entry.names else entry.names

/-- The edge's facts of a normal exit (`exitStep`'s `edgeStore`). -/
def exitStore (G : NormalGraph ι) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι) (pushed : Bool)
    (observed : Option BranchRefinement.Observation) (promote : Option Bool) : Store :=
  edgeStoreOf G (exitCtx c pushed) entry.store st.store (normalNames entry st pushed) (st.result :: entry.names)
    c.context.length pushed false observed promote

/-- The edge's width: the claim's context, with the result where pushed. -/
def exitWidth (c : PointClaim ι) (pushed : Bool) : Nat := if pushed then c.context.length + 1 else c.context.length

/-- The facts the edge search reads (`exitTypes`' `ko`). -/
def exitSearchFacts (G : NormalGraph ι) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι) (pushed : Bool)
    (observed : Option BranchRefinement.Observation) (promote : Option Bool) (Δ : List (Ty ι))
    (m : PointClaims.Mapping) : HeapKnowledge.Knowledge :=
  KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G (exitCtx c pushed))
    (materialize { names := normalNames entry st pushed, store := exitStore G c entry st pushed observed promote }
      (exitWidth c pushed) (0 :: (differing (exitCtx c pushed) Δ m).map (·.2)) false).1

/-- The facts the target's written assertion `req` is checked over
(`assertionExit`'s `k`). -/
def exitAssertFacts (G : NormalGraph ι) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι) (pushed : Bool)
    (observed : Option BranchRefinement.Observation) (promote : Option Bool) (req : HeapKnowledge.Knowledge)
    (m : PointClaims.Mapping) : HeapKnowledge.Knowledge :=
  (materialize { names := normalNames entry st pushed, store := exitStore G c entry st pushed observed promote }
    (exitWidth c pushed) (((atomsOf req).flatMap Atom.names).map (PointClaims.slot m)) false).1

/-- **What `exitStep` checks on the normal exit at position `i`** into a
node other than a loop head, at the node's claim `c`, entry, step `st`, the
yields `ys` the visit kept, those the exits' contexts read (`ysA`), those
the exit's implications read (`ysE`), the node's `here` answer and the
step's `outFresh`: where the exit is not vacuous, its types
(`ExitTyped`, the refined context at `ys`) and the target's written
assertion at the context `ysA` refine; the state it carries and its
implications among the target's incoming; at a merge, the edge as the
merge reads it. -/
structure NonHeadExitChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (w : Walk ι)
    (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι)
    (ys ysA ysE : List (PromiseCalls.Yield ι)) (here outFresh : Bool) (i : Nat) (t : Target) (pushed : Bool)
    (observed : Option BranchRefinement.Observation) (promote : Option Bool) : Prop where
  typed : vacuousOf G here c.type (exitCtx c pushed) pushed observed = false →
    ExitTyped G images (exitCtx c pushed) (ctx t.label) t observed
      (exitSearchFacts G c entry st pushed observed promote (ctx t.label) t.mapping)
      (SinglePass.refinedContext G c node.continuation (yieldsAtSlots entry.names ys) (SinglePass.outAllOf G c st.stepOut)
        (i == 0))
      (SinglePass.outAllOf G c st.stepOut)
  asserted : vacuousOf G here c.type (exitCtx c pushed) pushed observed = false → ∀ req, stated t.label = some req →
    KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (ctx t.label))
      (assertionSource G (SinglePass.refinedContext G c node.continuation (yieldsAtSlots entry.names ysA)
          (SinglePass.outAllOf G c st.stepOut) (i == 0)) req
        (exitAssertFacts G c entry st pushed observed promote req t.mapping) t.mapping observed) req t.mapping = true
  pushedIn : (edgeTransfer (normalNames entry st pushed) t.mapping pushed false outFresh entry st.result
    (exitStore G c entry st pushed observed promote)
    (w.implies l ++ freshImplOf pushed false ysE entry.names st.result)) ∈ w.incoming t.label
  merged : 2 ≤ (w.incoming t.label).length →
    (SinglePass.refinedContext G c node.continuation (yieldsAtSlots entry.names ysA) (SinglePass.outAllOf G c st.stepOut)
        (i == 0),
      atSlotsOf (normalNames entry st pushed) (w.implies l ++ freshImplOf pushed false ysE entry.names st.result),
      t.mapping) ∈ edgesIn t.label

/-- **The checks at a reassigned graph**: the same checks there
(`ExitTyped.reassign`, `assertionQuery_reassign`; the edge's facts, the
refined context and the vacuity read no type's meaning). -/
theorem NonHeadExitChecked.reassign {G : NormalGraph ι} {images : InstanceImageCheck G} {w : Walk ι}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι}
    {ys ysA ysE : List (PromiseCalls.Yield ι)} {here outFresh : Bool} {i : Nat} {t : Target} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    (hc : NonHeadExitChecked G images w ctx stated edgesIn l node c entry st ys ysA ysE here outFresh i t pushed
      observed promote) (η : MixedAssignment ι) :
    NonHeadExitChecked (PositiveRules.reassign G η) (images.reassign η) w ctx stated edgesIn l node c entry st ys ysA
      ysE here outFresh i t pushed observed promote where
  typed hv := (hc.typed hv).reassign η
  asserted hv req hr := by
    have := hc.asserted hv req hr
    unfold assertionSource at this ⊢
    exact (assertionQuery_reassign G η _ _ req _ t.mapping observed).trans this
  pushedIn := hc.pushedIn
  merged := hc.merged

/-- **The state after a step a normal exit reads, with the result's
freshness**: `NodeExitsY`'s state, kept yields and output, and, where the
step states its result fresh and the result's name is not already fresh,
the result fresh at the mark. -/
def AfterStep (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (l : Nat) (entry : SinglePass.State)
    (st : Stepped ι) (ys : List (PromiseCalls.Yield ι)) (outFresh : Bool) (ρ : Env) : Assertion :=
  fun ρ' m' s' => StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ρ0 ρ' m' s' ∧
    PromiseCalls.YieldsOk G ys ρ s'.n s'.W (ρ' 0) ∧ HeapKnowledge.Holds st.stepOut ρ' s'.h ∧
    (outFresh = true → st.result ∉ entry.fresh → FreshAt m' (ρ' 0))

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
theorem yieldsOk_of_or {G : NormalGraph ι} {ys ys' : List (PromiseCalls.Yield ι)} {ρ : Env} {n : Nat}
    {W : WorldT n} {u : Tm} (h : ys' = [] ∨ ys' = ys) (hy : PromiseCalls.YieldsOk G ys ρ n W u) :
    PromiseCalls.YieldsOk G ys' ρ n W u := by
  rcases h with rfl | rfl
  · intro y hy; cases hy
  · exact hy

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
theorem slotsNamed_tail {names : List Nat} {x : Nat} {v : Tm} {ρ η : Env} (h : SlotsNamed (x :: names) (push v ρ) η) :
    SlotsNamed names ρ η :=
  fun i y hy => h (i + 1) y (by simpa using hy)

/-- **A normal exit into a node other than a loop head delivers
`edgePreAJ`** from what `exitStep` checked on it (`NonHeadExitChecked`),
the subtype answers sound, the mapping's names sound, the node's `here`
answer stating its context empty and the yields the exits read the kept
ones or none. -/
theorem nonHeadExit_delivers {G : NormalGraph ι} {images : InstanceImageCheck G} {w : Walk ι}
    {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι}
    {ys ysA ysE : List (PromiseCalls.Yield ι)} {here outFresh : Bool} {i : Nat} {t : Target} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    (hm : (Exit.ofNode node)[i]? = some (Exit.normal t pushed observed promote))
    (hc : NonHeadExitChecked G images w ctx stated edgesIn l node c entry st ys ysA ysE here outFresh i t pushed
      observed promote)
    (hshape : SinglePass.passShapeCheck' G c.type node.continuation = true)
    (hsub : SubtypeAnswersSound G images) (hmap : MapNamesSound (normalNames entry st pushed) t.mapping)
    (hhere : here = true → HereEmpty G c.context) (hA : ysA = [] ∨ ysA = ys) (hE : ysE = [] ∨ ysE = ys)
    (ρ : Env) (m : Nat) :
    ExitDelivers (edgePreAJ G w startNames ρ0 ctx stated given edgesIn) G c.type c.context
      (AfterStep G w startNames ρ0 l entry st ys outFresh ρ) ρ m t pushed observed promote := by
  intro s' v _ hF he ho
  obtain ⟨hS, hY, hout, hfr⟩ := hF
  obtain ⟨hpo, hpp⟩ := ofNode_flags (List.mem_of_getElem? hm)
  cases hvac : vacuousOf G here c.type (exitCtx c pushed) pushed observed with
  | true => exact (vacuous_false (C := c.context) hvac hhere hpo he ho).elim
  | false =>
  obtain ⟨n, W, h, pos, adm, hh⟩ := s'
  cases n with
  | zero => exact absurd pos (Nat.lt_irrefl 0)
  | succ n =>
  simp only at he hY hout hfr ⊢
  obtain ⟨η, hn, -⟩ := id hS
  have hnames : SlotsNamed entry.names ρ η := slotsNamed_tail hn
  have hshv : ShapeOk v node.continuation := nodeShape_of hshape (he.2 0 _ rfl)
  have hΓ : EnvOk G (exitCtx c pushed) (if pushed then push v ρ else ρ) (n + 1) W := by
    unfold exitCtx
    cases pushed with
    | true => simpa using he
    | false => simpa using envOk_tail he
  have ho' : ∀ o, observed = some o → o.holds ((if pushed then push v ρ else ρ) 0) := by
    intro o hob
    have hp : pushed = true := hpo (by rw [hob]; rfl)
    subst hp
    simpa [push, ObservedOk, hob] using ho
  have heo : observed.isSome = true → EnvOk G (exitCtx c pushed) (push v ρ) (n + 1) W := fun hs => by
    have hp : pushed = true := hpo hs
    subst hp; simpa [exitCtx] using he
  -- The target's types from the exit's checks.
  have hr := passRefined_env (s := ⟨n + 1, W, h, pos, adm, hh⟩) hm he hshv ho (yieldsOk_atSlots hnames hY) hout
  have hko : HeapKnowledge.Holds (exitSearchFacts G c entry st pushed observed promote (ctx t.label) t.mapping)
      (if pushed then push v ρ else ρ) h := by
    unfold exitSearchFacts
    exact KnowledgeExpand.expandLinks_holds (KnowledgeExpand.ctxOf_ok hΓ)
      (edgeFacts_holds (s := ⟨n + 1, W, h, pos, adm, hh⟩) (width := c.context.length) hS ho hpo hpp heo)
  have houtL : observed.isSome = true →
      HeapKnowledge.Holds (SinglePass.outAllOf G c st.stepOut) (if pushed then push v ρ else ρ) h := fun hs => by
    have hp : pushed = true := hpo hs
    subst hp
    exact KnowledgeExpand.expandLinks_holds (setsCtx_push_ok (envOk_tail he) v) hout
  have htc := (hc.typed hvac).env hsub hΓ hko hr houtL hh ho'
  -- The edge's state.
  have hYE : PromiseCalls.YieldsOk G ysE ρ (n + 1) W v := yieldsOk_of_or hE hY
  have hT := normal_edge_delivers (w := w) (ctx := ctx) (s := ⟨n + 1, W, h, pos, adm, hh⟩) (width := c.context.length)
    hS ho hpo hpp heo (fun _ => hYE) hmap (fun _ hf hn => hfr hf hn) hc.pushedIn htc
  -- The written assertion at the context the yields `ysA` refine.
  have hrA := passRefined_env (s := ⟨n + 1, W, h, pos, adm, hh⟩) hm he hshv ho
    (yieldsOk_atSlots hnames (yieldsOk_of_or hA hY)) hout
  have hAs : AssertsAt stated t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ))
      ⟨n + 1, W, h, pos, adm, hh⟩ := fun req hreq =>
    assertion_query_sound (hc.asserted hvac req hreq)
      (edgeFacts_holds (s := ⟨n + 1, W, h, pos, adm, hh⟩) (width := c.context.length) hS ho hpo hpp heo) hrA hh ho' htc
  -- The merge's joined implications.
  obtain ⟨η', hn', -, hI', -⟩ := stateHolds_freshImpl (pushed := pushed) (s := ⟨n + 1, W, h, pos, adm, hh⟩) hS
    (fun _ => hYE)
  have hss : SlotsNamed (normalNames entry st pushed) (if pushed then push v ρ else ρ) η' := by
    unfold normalNames
    cases pushed with
    | true => simpa using hn'
    | false => simpa using slotsNamed_tail hn'
  exact ⟨⟨hT, hAs⟩, fun hg hlen =>
    joinedAt_of_exit (given := given) (k := m) (hc.merged hlen) hrA hss hI' hg hlen⟩

/-- **What `exitStep` checks on the normal exit at position `i` into a
loop head** (`headExit`), the head's given facts `req` (its written
assertion `written` with index facts `cf`), implications `gimp`, promised
argument `argName` at its slots `argSlots` and inputs at `inputSlots`,
entered by `headEntry` at width `hwidth` from the counter `hfresh`: where
the exit is not vacuous, its types (`ExitTyped`), each given implication
held by one the edge carries (of the same type or below it by an accepted
subtype answer), the inputs' and the argument's slots holding their names,
the given facts entailed over the edge's facts; the head's own entry among
its incoming. -/
structure HeadExitChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (w : Walk ι)
    (startNames : List Nat) (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge)
    (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι)
    (ys ysE : List (PromiseCalls.Yield ι)) (here : Bool) (i : Nat) (t : Target) (pushed : Bool)
    (observed : Option BranchRefinement.Observation) (promote : Option Bool)
    (req written : HeapKnowledge.Knowledge) (cf : List HeapKnowledge.IndexAtom)
    (gimp : List (PromiseCalls.Implication ι)) (argName : Option Nat) (argSlots : List Nat)
    (inputSlots : List (Nat × Nat)) (hwidth hfresh : Nat) : Prop where
  typed : vacuousOf G here c.type (exitCtx c pushed) pushed observed = false →
    ExitTyped G images (exitCtx c pushed) (ctx t.label) t observed
      (exitSearchFacts G c entry st pushed observed promote (ctx t.label) t.mapping)
      (SinglePass.refinedContext G c node.continuation (yieldsAtSlots entry.names ys) (SinglePass.outAllOf G c st.stepOut)
        (i == 0))
      (SinglePass.outAllOf G c st.stepOut)
  implied : vacuousOf G here c.type (exitCtx c pushed) pushed observed = false → ∀ x ∈ gimp,
    ∃ y ∈ w.implies l ++ freshImplOf pushed false ysE entry.names st.result,
      (normalNames entry st pushed)[PointClaims.slot t.mapping x.test]? = some y.test ∧
      (normalNames entry st pushed)[PointClaims.slot t.mapping x.target]? = some y.target ∧
      (y.type = x.type ∨ ∃ a, ((subtypeUsing G images y.type x.type a).1).value.isSome = true)
  inputs : vacuousOf G here c.type (exitCtx c pushed) pushed observed = false → ∀ p ∈ inputSlots,
    (normalNames entry st pushed)[PointClaims.slot t.mapping p.1]? = startNames[p.2]?
  args : vacuousOf G here c.type (exitCtx c pushed) pushed observed = false → ∀ j ∈ argSlots,
    (normalNames entry st pushed)[PointClaims.slot t.mapping j]? = argName
  query : vacuousOf G here c.type (exitCtx c pushed) pushed observed = false →
    KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (ctx t.label))
      (HeapKnowledge.withTypedLinks G (exitCtx c pushed) (ControlFlow.withTypedCells G (exitCtx c pushed) req t.mapping
        (materialize { names := normalNames entry st pushed, store := exitStore G c entry st pushed observed promote }
          (exitWidth c pushed) (((atomsOf req).flatMap Atom.names).map (PointClaims.slot t.mapping)) true).1))
      req t.mapping = true
  entered : (w.entry t.label, w.implies t.label) ∈ w.incoming t.label
  entry : w.entry t.label = (SinglePass.headEntry req false hwidth hfresh startNames argName argSlots inputSlots gimp).1 ∧
    w.implies t.label = (SinglePass.headEntry req false hwidth hfresh startNames argName argSlots inputSlots gimp).2.1
  written : (stated t.label).getD {} = written ∧ req = { written with indices := written.indices ++ cf }

/-- **The head checks at a reassigned graph** (`ExitTyped.reassign`,
`subtypeUsing_reassign`, `headQuery_reassign`). -/
theorem HeadExitChecked.reassign {G : NormalGraph ι} {images : InstanceImageCheck G} {w : Walk ι}
    {startNames : List Nat} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι}
    {ys ysE : List (PromiseCalls.Yield ι)} {here : Bool} {i : Nat} {t : Target} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    {req written : HeapKnowledge.Knowledge} {cf : List HeapKnowledge.IndexAtom}
    {gimp : List (PromiseCalls.Implication ι)} {argName : Option Nat} {argSlots : List Nat}
    {inputSlots : List (Nat × Nat)} {hwidth hfresh : Nat}
    (hc : HeadExitChecked G images w startNames ctx stated l node c entry st ys ysE here i t pushed observed promote
      req written cf gimp argName argSlots inputSlots hwidth hfresh) (η : MixedAssignment ι) :
    HeadExitChecked (PositiveRules.reassign G η) (images.reassign η) w startNames ctx stated l node c entry st ys ysE
      here i t pushed observed promote req written cf gimp argName argSlots inputSlots hwidth hfresh where
  typed hv := (hc.typed hv).reassign η
  implied hv x hx := by
    obtain ⟨y, hy, h1, h2, h3⟩ := hc.implied hv x hx
    refine ⟨y, hy, h1, h2, ?_⟩
    rcases h3 with h3 | ⟨a, ha⟩
    · exact .inl h3
    · exact .inr ⟨Answered.reassign a η, by rw [subtypeUsing_reassign]; exact ha⟩
  inputs := hc.inputs
  args := hc.args
  query hv := (headQuery_reassign G η _ _ req _ t.mapping).trans (hc.query hv)
  entered := hc.entered
  entry := hc.entry
  written := hc.written

/-- **A normal exit into a loop head delivers `edgePreAJ`** from what
`headExit` checked on it (`HeadExitChecked`): the head's entry by
`headEstablishes_of_edge` and `headEntry_holds`, its written assertion by
`assertsAt_of_head`, its types from the exit's checks; a head joins no
implications. -/
theorem headExit_delivers {G : NormalGraph ι} {images : InstanceImageCheck G} {w : Walk ι}
    {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι}
    {ys ysE : List (PromiseCalls.Yield ι)} {here outFresh : Bool} {i : Nat} {t : Target} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    {req written : HeapKnowledge.Knowledge} {cf : List HeapKnowledge.IndexAtom}
    {gimp : List (PromiseCalls.Implication ι)} {argName : Option Nat} {argSlots : List Nat}
    {inputSlots : List (Nat × Nat)} {hwidth hfresh : Nat}
    (hm : (Exit.ofNode node)[i]? = some (Exit.normal t pushed observed promote))
    (hc : HeadExitChecked G images w startNames ctx stated l node c entry st ys ysE here i t pushed observed promote
      req written cf gimp argName argSlots inputSlots hwidth hfresh)
    (hgiven : given t.label = true)
    (hshape : SinglePass.passShapeCheck' G c.type node.continuation = true)
    (hsub : SubtypeAnswersSound G images)
    (hhere : here = true → HereEmpty G c.context) (hE : ysE = [] ∨ ysE = ys)
    (hnd : startNames.Nodup) (hlt : ∀ x ∈ startNames, x < hfresh)
    (hargs : ∀ a, argName = some a → ∃ q : Nat, startNames[q]? = some a)
    (ρ : Env) (m : Nat) :
    ExitDelivers (edgePreAJ G w startNames ρ0 ctx stated given edgesIn) G c.type c.context
      (AfterStep G w startNames ρ0 l entry st ys outFresh ρ) ρ m t pushed observed promote := by
  intro s' v _ hF he ho
  obtain ⟨hS, hY, hout, -⟩ := hF
  obtain ⟨hpo, hpp⟩ := ofNode_flags (List.mem_of_getElem? hm)
  cases hvac : vacuousOf G here c.type (exitCtx c pushed) pushed observed with
  | true => exact (vacuous_false (C := c.context) hvac hhere hpo he ho).elim
  | false =>
  obtain ⟨n, W, h, pos, adm, hh⟩ := s'
  cases n with
  | zero => exact absurd pos (Nat.lt_irrefl 0)
  | succ n =>
  simp only at he hY hout ⊢
  obtain ⟨η, hn, -⟩ := id hS
  have hnames : SlotsNamed entry.names ρ η := slotsNamed_tail hn
  have hshv : ShapeOk v node.continuation := nodeShape_of hshape (he.2 0 _ rfl)
  have hΓ : EnvOk G (exitCtx c pushed) (if pushed then push v ρ else ρ) (n + 1) W := by
    unfold exitCtx
    cases pushed with
    | true => simpa using he
    | false => simpa using envOk_tail he
  have ho' : ∀ o, observed = some o → o.holds ((if pushed then push v ρ else ρ) 0) := by
    intro o hob
    have hp : pushed = true := hpo (by rw [hob]; rfl)
    subst hp
    simpa [push, ObservedOk, hob] using ho
  have heo : observed.isSome = true → EnvOk G (exitCtx c pushed) (push v ρ) (n + 1) W := fun hs => by
    have hp : pushed = true := hpo hs
    subst hp; simpa [exitCtx] using he
  have hr := passRefined_env (s := ⟨n + 1, W, h, pos, adm, hh⟩) hm he hshv ho (yieldsOk_atSlots hnames hY) hout
  have hko : HeapKnowledge.Holds (exitSearchFacts G c entry st pushed observed promote (ctx t.label) t.mapping)
      (if pushed then push v ρ else ρ) h := by
    unfold exitSearchFacts
    exact KnowledgeExpand.expandLinks_holds (KnowledgeExpand.ctxOf_ok hΓ)
      (edgeFacts_holds (s := ⟨n + 1, W, h, pos, adm, hh⟩) (width := c.context.length) hS ho hpo hpp heo)
  have houtL : observed.isSome = true →
      HeapKnowledge.Holds (SinglePass.outAllOf G c st.stepOut) (if pushed then push v ρ else ρ) h := fun hs => by
    have hp : pushed = true := hpo hs
    subst hp
    exact KnowledgeExpand.expandLinks_holds (setsCtx_push_ok (envOk_tail he) v) hout
  have htc := (hc.typed hvac).env hsub hΓ hko hr houtL hh ho'
  have hYE : PromiseCalls.YieldsOk G ysE ρ (n + 1) W v := yieldsOk_of_or hE hY
  have hSe := edgeStore_normal (Γ := exitCtx c pushed) (width := c.context.length)
    (stateHolds_freshImpl (pushed := pushed) (s := ⟨n + 1, W, h, pos, adm, hh⟩) hS (fun _ => hYE)) ho hpo hpp heo
  have hest := headEstablishes_of_edge hSe hΓ htc (hc.query hvac)
    (fun x hx => by
      obtain ⟨y, hy, h1, h2, h3⟩ := hc.implied hvac x hx
      refine ⟨y, hy, h1, h2, ?_⟩
      rcases h3 with h3 | ⟨a, ha⟩
      · rw [h3]; exact fun _ _ _ hv => hv
      · exact hsub _ _ a ha)
    (hc.inputs hvac) (hc.args hvac)
  refine ⟨⟨⟨⟨_, hc.entered, ?_⟩, htc⟩, ?_⟩, fun hg => absurd (hg.symm.trans hgiven) (by decide)⟩
  · rw [hc.entry.1, hc.entry.2]
    exact (headEntry_holds hnd hlt hargs hest).1
  · obtain ⟨hw, hreq⟩ := hc.written
    subst hreq
    exact assertsAt_of_head hw hest

/-- The handler edge's context: the thrown value's type `TT` pushed. -/
def handlerCtx (c : PointClaim ι) (TT : Ty ι) : List (Ty ι) := TT :: c.context

/-- The handler edge's facts (`exitStep`'s `edgeStore` of a handler). -/
def handlerStore (G : NormalGraph ι) (c : PointClaim ι) (TT : Ty ι) (entry : SinglePass.State) (st : Stepped ι)
    (x : Nat) : Store :=
  edgeStoreOf G (handlerCtx c TT) entry.store st.store (x :: entry.names) (st.result :: entry.names)
    c.context.length true true none none

/-- The facts the handler edge's search reads (`exitTypes`' `ko`). -/
def handlerSearchFacts (G : NormalGraph ι) (c : PointClaim ι) (TT : Ty ι) (entry : SinglePass.State) (st : Stepped ι)
    (x : Nat) (Δ : List (Ty ι)) (m : PointClaims.Mapping) : HeapKnowledge.Knowledge :=
  KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G (handlerCtx c TT))
    (materialize { names := x :: entry.names, store := handlerStore G c TT entry st x } (c.context.length + 1)
      (0 :: (differing (handlerCtx c TT) Δ m).map (·.2)) false).1

/-- The facts a handler edge checks the target's written assertion `req`
over (`assertionExit`'s `k`). -/
def handlerAssertFacts (G : NormalGraph ι) (c : PointClaim ι) (TT : Ty ι) (entry : SinglePass.State) (st : Stepped ι)
    (x : Nat) (req : HeapKnowledge.Knowledge) (m : PointClaims.Mapping) : HeapKnowledge.Knowledge :=
  (materialize { names := x :: entry.names, store := handlerStore G c TT entry st x } (c.context.length + 1)
    (((atomsOf req).flatMap Atom.names).map (PointClaims.slot m)) false).1

/-- **What `exitStep` checks on a node's handler exit** into `t`, the
thrown value's type `TT` and name `x`: `TT` admits every thrown value; where
the exit is not vacuous, its types (`diffSubtypes` or the edge search at
the thrown context); into a node other than a loop head, the target's
written assertion over the edge's facts, the state carried among the
target's incoming and, at a merge, the edge as the merge reads it; into a
loop head, `headExit`'s checks (as `HeadExitChecked`) with the start names
below the head's counter. -/
structure HandlerExitChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (w : Walk ι)
    (startNames : List Nat) (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge)
    (given : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (l : Nat) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι) (here outFresh : Bool) (TT : Ty ι)
    (x : Nat) (t : Target) : Prop where
  admits : ControlFlow.admitsAll G TT = true
  typed : (here || ControlFlow.unsatisfiable G [TT]) = false →
    SubtypesPass G images (handlerCtx c TT) (ctx t.label) (differing (handlerCtx c TT) (ctx t.label) t.mapping) ∨
      EdgeFound G images (ctx t.label) (handlerCtx c TT) t none
        (handlerSearchFacts G c TT entry st x (ctx t.label) t.mapping)
  asserted : given t.label = false → (here || ControlFlow.unsatisfiable G [TT]) = false → ∀ req,
    stated t.label = some req →
    KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (ctx t.label))
      (assertionSource G (handlerCtx c TT) req (handlerAssertFacts G c TT entry st x req t.mapping) t.mapping none) req
      t.mapping = true
  pushedIn : given t.label = false → (edgeTransfer (x :: entry.names) t.mapping true true outFresh entry st.result
    (handlerStore G c TT entry st x) (w.implies l)) ∈ w.incoming t.label
  merged : given t.label = false → 2 ≤ (w.incoming t.label).length →
    (handlerCtx c TT, atSlotsOf (x :: entry.names) (w.implies l), t.mapping) ∈ edgesIn t.label
  head : given t.label = true → ∃ (req written : HeapKnowledge.Knowledge) (cf : List HeapKnowledge.IndexAtom)
    (gimp : List (PromiseCalls.Implication ι)) (argName : Option Nat) (argSlots : List Nat)
    (inputSlots : List (Nat × Nat)) (hwidth hfresh : Nat),
    ((here || ControlFlow.unsatisfiable G [TT]) = false → ∀ y ∈ gimp, ∃ z ∈ w.implies l,
      (x :: entry.names)[PointClaims.slot t.mapping y.test]? = some z.test ∧
      (x :: entry.names)[PointClaims.slot t.mapping y.target]? = some z.target ∧
      (z.type = y.type ∨ ∃ a, ((subtypeUsing G images z.type y.type a).1).value.isSome = true)) ∧
    ((here || ControlFlow.unsatisfiable G [TT]) = false → ∀ p ∈ inputSlots,
      (x :: entry.names)[PointClaims.slot t.mapping p.1]? = startNames[p.2]?) ∧
    ((here || ControlFlow.unsatisfiable G [TT]) = false → ∀ j ∈ argSlots,
      (x :: entry.names)[PointClaims.slot t.mapping j]? = argName) ∧
    ((here || ControlFlow.unsatisfiable G [TT]) = false →
      KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (ctx t.label))
        (HeapKnowledge.withTypedLinks G (handlerCtx c TT) (ControlFlow.withTypedCells G (handlerCtx c TT) req t.mapping
          (materialize { names := x :: entry.names, store := handlerStore G c TT entry st x } (c.context.length + 1)
            (((atomsOf req).flatMap Atom.names).map (PointClaims.slot t.mapping)) true).1))
        req t.mapping = true) ∧
    (w.entry t.label, w.implies t.label) ∈ w.incoming t.label ∧
    (w.entry t.label = (SinglePass.headEntry req false hwidth hfresh startNames argName argSlots inputSlots gimp).1 ∧
      w.implies t.label =
        (SinglePass.headEntry req false hwidth hfresh startNames argName argSlots inputSlots gimp).2.1) ∧
    ((stated t.label).getD {} = written ∧ req = { written with indices := written.indices ++ cf }) ∧
    (∀ y ∈ startNames, y < hfresh) ∧ (∀ a, argName = some a → ∃ q : Nat, startNames[q]? = some a)

/-- **A node's handler exit delivers `edgePreAJ`** from the throw state,
from what `exitStep` checked on it (`HandlerExitChecked`): into a node
other than a loop head by `handler_edge_delivers`, its written assertion
by `assertion_query_sound`, a merge's joined implications by
`joinedAt_of_exit` at the state with the thrown value pushed
(`stateHolds_handler`); into a loop head by `headEstablishes_of_edge`. -/
theorem handlerExit_delivers {G : NormalGraph ι} {images : InstanceImageCheck G} {w : Walk ι}
    {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {l : Nat} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι} {here outFresh : Bool} {TT : Ty ι}
    {x : Nat} {t : Target}
    (hc : HandlerExitChecked G images w startNames ctx stated given edgesIn l c entry st here outFresh TT x t)
    (hsub : SubtypeAnswersSound G images) (hmap : MapNamesSound (x :: entry.names) t.mapping)
    (hhere : here = true → HereEmpty G c.context) (wf : StoreWF entry.store)
    (hb : NamesBelow entry (w.implies l) startNames x) (hnd : startNames.Nodup)
    (ρ : Env) (m : Nat) (s' : IndexedHeap) (e : Tm)
    (hS : StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ρ0
      ρ m s')
    (he : EnvOk G c.context ρ s'.n s'.W) (hsc : Scoped 0 e) (hx : excOf G s'.n s'.W e) :
    edgePreAJ G w startNames ρ0 ctx stated given edgesIn t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s' := by
  have hTT : meaning G TT s'.n s'.W e := ControlFlow.admitsAll_sound hc.admits hx
  have heh : EnvOk G (handlerCtx c TT) (push e ρ) s'.n s'.W := he.push hTT
  cases hvac : (here || ControlFlow.unsatisfiable G [TT]) with
  | true =>
    exfalso
    rcases Bool.or_eq_true_iff.mp hvac with hh | hu
    · exact hereEmpty_false (hhere hh) he
    · exact unsatisfiable_sound hu (Γ := [TT]) (ρ := fun _ => e) ⟨fun _ => hsc, fun j X hj => by
        cases j with
        | zero => exact (Option.some.inj hj) ▸ hTT
        | succ j => simp at hj⟩
  | false =>
  obtain ⟨n, W, h, pos, adm, hh⟩ := s'
  cases n with
  | zero => exact absurd pos (Nat.lt_irrefl 0)
  | succ n =>
  simp only at he hTT heh hx ⊢
  have hSh := stateHolds_handler (v := e) hS (namesBelow_dropHeap wf _ hb)
  have hSe : StateHolds G ⟨x :: entry.names, handlerStore G c TT entry st x, entry.fresh⟩ (w.implies l) startNames ρ0
      (push e ρ) m ⟨n + 1, W, h, pos, adm, hh⟩ := hSh
  have hko : HeapKnowledge.Holds (handlerSearchFacts G c TT entry st x (ctx t.label) t.mapping) (push e ρ) h :=
    KnowledgeExpand.expandLinks_holds (KnowledgeExpand.ctxOf_ok heh)
      (stateHolds_materialize (stateHolds_edge hSe) _ _ true)
  have hty : ExitTyped G images (handlerCtx c TT) (ctx t.label) t none
      (handlerSearchFacts G c TT entry st x (ctx t.label) t.mapping) (handlerCtx c TT)
      (handlerSearchFacts G c TT entry st x (ctx t.label) t.mapping) := by
    rcases hc.typed hvac with h1 | h1
    · exact .inl h1
    · exact .inr (.inl h1)
  have htc := hty.env hsub heh hko heh (fun h => by cases h) hh (fun o ho => by cases ho)
  cases hg : given t.label with
  | false =>
    have hrec := hc.pushedIn hg
    have hT := handler_edge_delivers (w := w) (ctx := ctx) (ys := ([] : List (PromiseCalls.Yield ι)))
      (s := ⟨n + 1, W, h, pos, adm, hh⟩) hS wf hb hmap
      (by rw [freshImplOf_handler, List.append_nil]; exact hrec) htc
    have hAs : AssertsAt stated t.label (PointClaims.mapEnv t.mapping (push e ρ)) ⟨n + 1, W, h, pos, adm, hh⟩ :=
      fun req hreq => assertion_query_sound (hc.asserted hg hvac req hreq)
        (stateHolds_materialize (stateHolds_edge hSe) _ _ true) heh hh (fun o ho => by cases ho) htc
    obtain ⟨η', hn', -, hI', -⟩ := hSh
    exact ⟨⟨hT, hAs⟩, fun hg' hlen =>
      joinedAt_of_exit (given := given) (k := m) (hc.merged hg hlen) heh hn' hI' hg' hlen⟩
  | true =>
    obtain ⟨req, written, cf, gimp, argName, argSlots, inputSlots, hwidth, hfresh, himp, hin, harg, hq, hent, hentry,
      hwr, hlt, hargs⟩ := hc.head hg
    have hest := headEstablishes_of_edge hSe heh htc (hq hvac)
      (fun y hy => by
        obtain ⟨z, hz, h1, h2, h3⟩ := himp hvac y hy
        refine ⟨z, hz, h1, h2, ?_⟩
        rcases h3 with h3 | ⟨a, ha⟩
        · rw [h3]; exact fun _ _ _ hv => hv
        · exact hsub _ _ a ha)
      (hin hvac) (harg hvac)
    refine ⟨⟨⟨⟨_, hent, ?_⟩, htc⟩, ?_⟩, fun hg' => absurd (hg'.symm.trans hg) (by decide)⟩
    · rw [hentry.1, hentry.2]
      exact (headEntry_holds hnd hlt hargs hest).1
    · obtain ⟨hw, hreq⟩ := hwr
      subst hreq
      exact assertsAt_of_head hw hest

theorem SubtypesPass.reassign {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ Δ : List (Ty ι)}
    {diff : List (Nat × Nat)} (h : SubtypesPass G images Γ Δ diff) (η : MixedAssignment ι) :
    SubtypesPass (PositiveRules.reassign G η) (images.reassign η) Γ Δ diff := fun p hp => by
  obtain ⟨A, B, a, hA, hB, hs⟩ := h p hp
  exact ⟨A, B, Answered.reassign a η, hA, hB, by rw [subtypeUsing_reassign]; exact hs⟩

omit [Hashable ι] [Instantiates ι] in
theorem EdgeFound.reassign {G : NormalGraph ι} {images : InstanceImageCheck G} {Δ Γ : List (Ty ι)} {t : Target}
    {observed : Option BranchRefinement.Observation} {k : HeapKnowledge.Knowledge}
    (h : EdgeFound G images Δ Γ t observed k) (η : MixedAssignment ι) :
    EdgeFound (PositiveRules.reassign G η) (images.reassign η) Δ Γ t observed k :=
  let ⟨p, hp⟩ := h
  ⟨p, (edgeEvidenceChecked_reassign G η images _ _ t observed _ _ _ p).trans hp⟩

/-- **The handler checks at a reassigned graph.** -/
theorem HandlerExitChecked.reassign {G : NormalGraph ι} {images : InstanceImageCheck G} {w : Walk ι}
    {startNames : List Nat} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {l : Nat} {c : PointClaim ι} {entry : SinglePass.State} {st : Stepped ι} {here outFresh : Bool} {TT : Ty ι}
    {x : Nat} {t : Target}
    (hc : HandlerExitChecked G images w startNames ctx stated given edgesIn l c entry st here outFresh TT x t)
    (η : MixedAssignment ι) :
    HandlerExitChecked (PositiveRules.reassign G η) (images.reassign η) w startNames ctx stated given edgesIn l c entry
      st here outFresh TT x t where
  admits := hc.admits
  typed hv := (hc.typed hv).imp (·.reassign η) (·.reassign η)
  asserted hg hv req hr := by
    have := hc.asserted hg hv req hr
    unfold assertionSource at this ⊢
    exact (assertionQuery_reassign G η _ _ req _ t.mapping none).trans this
  pushedIn := hc.pushedIn
  merged := hc.merged
  head hg := by
    obtain ⟨req, written, cf, gimp, argName, argSlots, inputSlots, hwidth, hfresh, himp, hin, harg, hq, hent, hentry,
      hwr, hlt, hargs⟩ := hc.head hg
    refine ⟨req, written, cf, gimp, argName, argSlots, inputSlots, hwidth, hfresh, fun hv y hy => ?_, hin, harg,
      fun hv => (headQuery_reassign G η _ _ req _ t.mapping).trans (hq hv), hent, hentry, hwr, hlt, hargs⟩
    obtain ⟨z, hz, h1, h2, h3⟩ := himp hv y hy
    refine ⟨z, hz, h1, h2, ?_⟩
    rcases h3 with h3 | ⟨a, ha⟩
    · exact .inl h3
    · exact .inr ⟨Answered.reassign a η, by rw [subtypeUsing_reassign]; exact ha⟩

end NonHead

end Verification.TolerantFrames
