import Verification.Source.Claims.FramedBinding
import Verification.Paper.TolerantFrames.ReadOnlyRealize
import Verification.Paper.TolerantFrames.ReadOnlyPending
import Verification.Paper.TolerantFrames.ReadOnlyEnterRoots

/-! # The realization of a framed plan's request

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Realization", `prologue_sim` and
`chk_sim`). A receiverless module function's realized code
(`realizedCode`) is its request's tables (`requestCode`) with one prologue
node past the body. Where the request's nodes target only its own labels
(`bodyTargetsB`), the two codes agree on the body (`realized_agree`):

- **The prologue** (`prologue_steps`): from the realized code's run at the
  prologue's label, two steps (entering its node, `undefined`, and its
  continuation) reach the realized code's run at the request's start, its
  slots the receiver's dropped.
- **The simulation** (`prologue_sim`): from there, every execution of the
  realized code is the same execution of the request's, on the same heaps,
  to related terms (`TabRel`), and where one takes no step the other takes
  none.
- **The same sites and crossings out** (`chk_site_sim`, `chk_actual_sim`,
  the site and crossings-out parts of `chk_sim`): in any context, related
  runs allocate at the same site, the flow holding both codes and their
  sites one per body allocation (`allocB`), and a step of related runs
  crosses out the same values.
- **The same crossings in** (`chk_entry_sim`): a step of related runs to
  related runs has the same entering crossings; with the two above, the
  checks' data of related steps agree (`chk_sim`).
- **The frame's starts from the program** (`lay_start`, `wok_start`): at
  every call the frame's claim is about, layout provenance and the
  residual invariant hold where they hold at initial configurations, read
  along the public call and its realization (`entry_run`); an initial
  configuration meets both where the initialization's node expressions and
  the realm do and the client is lowered source (`initial_starts`); the
  checks read the flow's sites (`flowSites`). -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly HeapObservations

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

instance (n : Nat) : DecidablePred (ContBelow n) := fun k => by cases k <;> unfold ContBelow <;> infer_instance

/-- **A code's nodes target its own labels**, decided: each continuation's
and handler's target is a label of the code's first `n` nodes. -/
def bodyTargetsB (m : Code) (n : Nat) : Bool :=
  m.2.all fun (k, x) => decide (ContBelow n k) && x.all (·.label < n)

/-- **The targets check is sound** (proved). -/
theorem bodyTargetsB_sound {m : Code} {n : Nat} (h : bodyTargetsB m n = true) :
    ∀ (l : Nat) k x, m.2[l]? = some (k, x) → ContBelow n k ∧ HandlerBelow n x := by
  intro l k x hl
  simp only [bodyTargetsB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hk, hx⟩ := h (k, x) (List.mem_of_getElem? hl)
  refine ⟨hk, fun t ht => ?_⟩
  subst ht
  simpa using hx

/-- **The realized code and its request's agree on the body** (proved): the
realized code's tables are the request's with one node appended. -/
theorem realized_agree {r : SourceRequest σ ι} (h : bodyTargetsB (requestCode r) r.program.length = true) :
    BodyAgree (realizedCode r) (requestCode r) r.program.length := by
  refine ⟨fun l hl => ⟨?_, ?_⟩, fun l _ k x hk => bodyTargetsB_sound h l k x hk⟩
  · simp only [realizedCode, requestCode]
    rw [List.getElem?_append_left (by simpa using hl)]
  · simp only [realizedCode, requestCode]
    rw [List.getElem?_append_left (by simpa using hl)]

/-- The prologue's target: the request's start, the slots past the
receiver. -/
def prologueTarget (r : SourceRequest σ ι) : Target :=
  ⟨r.start, some ((List.range (r.inputs.length + 1)).map (· + 1))⟩

/-- **The prologue's steps** (proved): the realized code's run at the
prologue's label enters its node, which evaluates `undefined`, and continues
at the request's start with the slots the target maps. -/
theorem prologue_steps (r : SourceRequest σ ι) (h : Heap) (L : List Tm) (d : Tm) (c : ComponentTag) :
    Steps 2 h (.goto (realizedCode r).1 (realizedCode r).2 r.program.length L d c) h
      (.goto (realizedCode r).1 (realizedCode r).2 r.start (envMap (prologueTarget r).mapping L d).1
        (envMap (prologueTarget r).mapping L d).2 c) := by
  have he : (realizedCode r).1[r.program.length]? = some .undef := by
    simp [realizedCode]
  have hk : (realizedCode r).2[r.program.length]? = some (.effect (prologueTarget r), none) := by
    simp [realizedCode, prologueTarget]
  refine .next (.gotoEnter he hk) (.next ?_ .refl)
  have hi : instantiate 0 (envOf L d) Tm.undef = .undef := by simp [instantiate]
  rw [hi]
  exact .frameEffect rfl

/-- **The prologue's simulation** (proved, `prologue_steps`, `tabRel_steps`,
`tabRel_stuck`; the draft's `prologue_sim`): where the request's nodes
target its own labels and its start is one of them, two steps from the
realized code's run at the prologue's label reach a run related to the
request's run at its start, at the slots the prologue maps; every
execution from there is the same execution of the request's code, to
related terms, and where one takes no step the other takes none. -/
theorem prologue_sim {r : SourceRequest σ ι} (ht : bodyTargetsB (requestCode r) r.program.length = true)
    (hs : r.start < r.program.length) (h : Heap) (L : List Tm) (d : Tm) (c : ComponentTag) :
    let L' := (envMap (prologueTarget r).mapping L d).1
    let d' := (envMap (prologueTarget r).mapping L d).2
    Steps 2 h (.goto (realizedCode r).1 (realizedCode r).2 r.program.length L d c) h
        (.goto (realizedCode r).1 (realizedCode r).2 r.start L' d' c) ∧
      TabRel (realizedCode r) (requestCode r) r.program.length
        (.goto (realizedCode r).1 (realizedCode r).2 r.start L' d' c) (PassUnit.gotoOf r.program r.start L' d' c) ∧
      (∀ {j h₁ h₂ t₁}, Steps j h₁ (.goto (realizedCode r).1 (realizedCode r).2 r.start L' d' c) h₂ t₁ →
        ∃ t₂, Steps j h₁ (PassUnit.gotoOf r.program r.start L' d' c) h₂ t₂ ∧
          TabRel (realizedCode r) (requestCode r) r.program.length t₁ t₂ ∧
          ((∀ h₃ t₃, ¬ Step h₂ t₁ h₃ t₃) → ∀ h₃ t₃, ¬ Step h₂ t₂ h₃ t₃)) := by
  intro L' d'
  have hA := realized_agree ht
  have hrel : TabRel (realizedCode r) (requestCode r) r.program.length
      (.goto (realizedCode r).1 (realizedCode r).2 r.start L' d' c) (PassUnit.gotoOf r.program r.start L' d' c) := by
    rw [gotoOf_requestCode]; exact .goto hs
  refine ⟨prologue_steps r h L d c, hrel, fun hst => ?_⟩
  obtain ⟨t₂, hs₂, hr₂⟩ := tabRel_steps hA hrel hst
  exact ⟨t₂, hs₂, hr₂, tabRel_stuck hA hr₂⟩

/-- **Related runs allocate at the same site** (proved, `stepSite_tabRel`
and `allocB_realized`; the site part of the draft's `chk_sim`): where the
flow holds both codes at their entry and numbers their allocation sites by
the body (`allocB`), a step of related terms in any context reads the same
site. -/
theorem chk_site_sim {P : TolerantFrames.ReadOnly.Package} [DecidableEq P.Site] {num : P.Site → Nat}
    (hnum : ∀ a b, num a = num b → a = b) {F : FFlow P} {r : SourceRequest σ ι} {base : Nat}
    {bodies : List Code} (hb : allocB num F r base bodies = true)
    (h₁ : (F.at (realizedCode r) entryCx).isSome = true) (h₂ : (F.at (requestCode r) entryCx).isSome = true)
    {K : Tm → Tm} (hK : EvalCtx K) {t₁ t₂ : Tm} (hr : TabRel (realizedCode r) (requestCode r) r.program.length t₁ t₂) :
    stepSite F.flow none (K t₁) = stepSite F.flow none (K t₂) := by
  refine stepSite_tabRel hK hr fun comp l _ kx hkx => ?_
  obtain ⟨f₁, hf₁⟩ := Option.isSome_iff_exists.mp h₁
  obtain ⟨f₂, hf₂⟩ := Option.isSome_iff_exists.mp h₂
  have hs := allocB_realized hnum hb hf₁ hf₂ (List.mem_of_getElem? hkx)
  simp only [allocOf, FFlow.flow, hf₁, hf₂, Option.map_some, Option.getD_some, FCode.flow, hs]

/-- The prologue's node holds no value, so the realized code's node
expressions hold its request's (proved). -/
theorem realized_vals (ofC : ComponentTag → Bool) (r : SourceRequest σ ι) :
    valsArgs ofC true (realizedCode r).1 = valsArgs ofC true (requestCode r).1 := by
  simp [realizedCode, requestCode, vals]

/-- **Related steps cross the same values out** (proved, `vals_tabRel`,
`vals_ctx`, `actualXs_congr`; the crossings-out part of the draft's
`chk_sim`): in any context, a step of related runs to related runs crosses
out the same values at the same type. -/
theorem chk_actual_sim {F : TolerantFrames.ReadOnly.Family} {C : Nat} {tv : TypeView} (T : tv.Ty) (h h' : Heap)
    {r : SourceRequest σ ι} {K : Tm → Tm} (hK : EvalCtx K) {t₁ t₂ t₁' t₂' : Tm}
    (hr : TabRel (realizedCode r) (requestCode r) r.program.length t₁ t₂)
    (hr' : TabRel (realizedCode r) (requestCode r) r.program.length t₁' t₂') :
    actualXs F C T h (K t₁) h' (K t₁') = actualXs F C T h (K t₂) h' (K t₂') :=
  actualXs_congr T h h' (vals_ctx hK (vals_tabRel (realized_vals _ r) hr))
    (vals_ctx hK (vals_tabRel (realized_vals _ r) hr'))

/-- **Related steps cross the same values in** (proved; the entering
crossings of the draft's `chk_sim`): in any context, a step of related runs
to related runs has the same entering crossings. The active frame's tag and
redex and the calls of `C` active are read from the tags of the paths,
which related runs share (`tabRel_tags`, `depthC_ctx`, `activeFrame_ctx`);
the code entered differs only where the realized code's frame continues at
its own node, a step that keeps the calls of `C` active
(`frame_goto_tags`), so neither is an entering step; and a step of the same
term is the same step (`Step_det`). -/
theorem chk_entry_sim (spec : FramedSpec ι) (r : SourceRequest σ ι) {K : Tm → Tm} (hK : EvalCtx K)
    {h h' : Heap} {t₁ t₂ t₁' t₂' : Tm}
    (hr : TabRel (realizedCode r) (requestCode r) r.program.length t₁ t₂) (hs₁ : Step h t₁ h' t₁')
    (hs₂ : Step h t₂ h' t₂') (hr' : TabRel (realizedCode r) (requestCode r) r.program.length t₁' t₂') :
    spec.entryXs r (K t₁) (K t₁') = spec.entryXs r (K t₂) (K t₂') := by
  obtain ⟨c', hc'⟩ := activeFrame_ctx hK none
  cases hr with
  | same => obtain ⟨-, rfl⟩ := Step_det hs₁ hs₂; rfl
  | @goto l L d c hl =>
    have e : ∀ m : Code, (activeFrame none (K (.goto m.1 m.2 l L d c))).2 = .goto m.1 m.2 l L d c := by
      intro m; rw [hc' _ rfl]; simp [activeFrame]
    unfold FramedSpec.entryXs
    rw [e, e]
    simp only [ite_self]
  | @frame l u L d k x c hl hk =>
    -- The active frame's tag and redex.
    have hA := (activeFrame_innermost u (some (((realizedCode r), c), (k, x)))).1
    have hB := (activeFrame_innermost u (some (((requestCode r), c), (k, x)))).1
    have htag : frameTag (activeFrame none (K (.frame (realizedCode r).1 (realizedCode r).2 u L d k x c))).1 =
        frameTag (activeFrame none (K (.frame (requestCode r).1 (requestCode r).2 u L d k x c))).1 := by
      rw [hc' _ rfl, hc' _ rfl]
      simp only [activeFrame]
      rw [hA, hB]
      cases (innermost u).bind frameOf <;> rfl
    have hred : (activeFrame none (K (.frame (realizedCode r).1 (realizedCode r).2 u L d k x c))).2 =
        (activeFrame none (K (.frame (requestCode r).1 (requestCode r).2 u L d k x c))).2 := by
      rw [hc' _ rfl, hc' _ rfl]
      simp only [activeFrame]
      exact activeFrame_snd u _ _
    have hd : depthC spec.F spec.C none (K (.frame (realizedCode r).1 (realizedCode r).2 u L d k x c)) =
        depthC spec.F spec.C none (K (.frame (requestCode r).1 (requestCode r).2 u L d k x c)) :=
      depthC_ctx hK none rfl rfl (tabRel_tags (.frame hl hk))
    cases hr' with
    | same =>
      unfold FramedSpec.entryXs
      rw [htag, hred, hd]
    | @goto l' L' d' c'' hl' =>
      have hd' : depthC spec.F spec.C none (K (.goto (realizedCode r).1 (realizedCode r).2 l' L' d' c'')) =
          depthC spec.F spec.C none (K (.frame (realizedCode r).1 (realizedCode r).2 u L d k x c)) :=
        depthC_ctx hK none rfl rfl fun c => (frame_goto_tags hs₁ c).symm
      have hd'' : depthC spec.F spec.C none (K (.goto (requestCode r).1 (requestCode r).2 l' L' d' c'')) =
          depthC spec.F spec.C none (K (.goto (realizedCode r).1 (realizedCode r).2 l' L' d' c'')) :=
        depthC_ctx hK none rfl rfl fun c => (tabRel_tags (A := realizedCode r) (B := requestCode r) (.goto hl') c).symm
      unfold FramedSpec.entryXs
      rw [if_neg (fun h => by have := h.2.2; omega), if_neg (fun h => by have := h.2.2; omega)]
    | @frame l' u' L' d' k' x' c'' hl' hk' =>
      have hd' : depthC spec.F spec.C none (K (.frame (realizedCode r).1 (realizedCode r).2 u' L' d' k' x' c'')) =
          depthC spec.F spec.C none (K (.frame (requestCode r).1 (requestCode r).2 u' L' d' k' x' c'')) :=
        depthC_ctx hK none rfl rfl (tabRel_tags (.frame hl' hk'))
      have he : entered none (K (.frame (realizedCode r).1 (realizedCode r).2 u' L' d' k' x' c'')) =
          entered none (K (.frame (requestCode r).1 (requestCode r).2 u' L' d' k' x' c'')) := entered_frame hK none
      unfold FramedSpec.entryXs
      rw [htag, hred, hd, hd', he]

/-- **Related steps have the same checks' data** (proved; the draft's
`chk_sim`, by `chk_site_sim`, `chk_actual_sim` and `chk_entry_sim`): in any
context, a step of related runs to related runs allocates at the same site
with no key, and has the same crossings, entering and outgoing. -/
theorem chk_sim (spec : FramedSpec ι) (r : SourceRequest σ ι) {num : (spec.F.at spec.C).Site → Nat}
    (hnum : ∀ a b, num a = num b → a = b) {base : Nat} {bodies : List Code}
    (hb : allocB num spec.fflow r base bodies = true)
    (h₁ : (spec.fflow.at (realizedCode r) entryCx).isSome = true)
    (h₂ : (spec.fflow.at (requestCode r) entryCx).isSome = true) {K : Tm → Tm} (hK : EvalCtx K)
    {h h' : Heap} {t₁ t₂ t₁' t₂' : Tm}
    (hr : TabRel (realizedCode r) (requestCode r) r.program.length t₁ t₂) (hs₁ : Step h t₁ h' t₁')
    (hs₂ : Step h t₂ h' t₂') (hr' : TabRel (realizedCode r) (requestCode r) r.program.length t₁' t₂') :
    spec.chk r h (K t₁) h' (K t₁') = spec.chk r h (K t₂) h' (K t₂') := by
  have hs : stepSite spec.flow none (K t₁) = stepSite spec.flow none (K t₂) := chk_site_sim hnum hb h₁ h₂ hK hr
  simp only [FramedSpec.chk, hs, chk_entry_sim spec r hK hr hs₁ hs₂ hr',
    chk_actual_sim (F := spec.F) (C := spec.C) (tv := spec.view.view) spec.outType h h' hK hr hr']

namespace FramedSpec
variable (spec : FramedSpec ι)

/-- **The run an entry realizes** (proved): at an entry of the request, the
state the public call reaches holds, in a context, the realized code's run
at the request's start, with the frame's slots and default, and the frame's
term is the request's run there. -/
theorem entry_run (r : SourceRequest σ ι) {k : Nat} {W : WorldT k} {h : Heap} {t : Tm}
    {a₂ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)} (he : spec.EntryAt r k W h t a₂) :
    ∃ x₀ n x a₁ L d K, (spec.core r).PublicCall spec.Initial (realizedCode r) x₀ n x a₁ ∧
      (∃ j, Ex (spec.core r).KStep (fun _ => True) j a₁ a₂) ∧ EvalCtx K ∧
      a₂.1.t = K (.goto (realizedCode r).1 (realizedCode r).2 r.start L d r.comp) ∧ h = a₂.1.s.h ∧
      t = PassUnit.gotoOf r.program r.start L d r.comp := by
  obtain ⟨x₀, n, x, a₁, L, d, hp, ⟨-, ⟨j, hj⟩, hin⟩, -, -, hh, ht⟩ := he
  obtain ⟨K, hK, hK'⟩ := innermostGoto_ctx hin
  exact ⟨x₀, n, x, a₁, L, d, K, hp, ⟨j, hj.mono fun _ _ => trivial⟩, hK, hK', hh, ht⟩

/-- **Layout provenance at the frame's calls** (proved, `lay_program`,
`lay_ex`, `EvalCtx.layP_hole`; the start premise of `lay_reached`): from
initial configurations meeting it, every call the frame's claim is about
meets it, its term the request's run whose node expressions are the
realized code's below the prologue. -/
theorem lay_start (r : SourceRequest σ ι) {q : Code → ComponentTag → Layout → Bool}
    (hinit : ∀ x, spec.Initial x → layP q x.t = true ∧ HeapLay q x.s.h) :
    ∀ (a : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)),
      (spec.frame r).Call a.1.s.n a.1.s.W a.1.s.h a.1.t → (spec.frame r).start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 →
      layP q a.1.t = true ∧ HeapLay q a.1.s.h := by
  intro a hc _
  obtain ⟨a₂, he⟩ := hc.2
  obtain ⟨x₀, n, x, a₁, L, d, K, hp, ⟨j, hj⟩, hK, ht₂, hh, ht⟩ := spec.entry_run r he
  have h₁ := FrameCore.lay_program hinit hp
  have h₂ := FrameCore.lay_ex hj h₁
  have hg := hK.layP_hole (by rw [← ht₂]; exact h₂.1)
  refine ⟨?_, by rw [hh]; exact h₂.2⟩
  rw [ht]
  simp only [layP, layPs_eq, realizedCode, List.all_append, Bool.and_eq_true] at hg
  simp only [PassUnit.gotoOf, layP, layPs_eq, Bool.and_eq_true]
  exact ⟨⟨hg.1.1.1, hg.1.2⟩, hg.2⟩

/-- **The residual invariant at the frame's calls** (proved, `wok_program`,
`wok_ex`, `EvalCtx.wok_hole`; the start premise of `wok_reached`): from
initial configurations meeting it, every call the frame's claim is about
meets it. -/
theorem wok_start (r : SourceRequest σ ι) (hinit : ∀ x, spec.Initial x → WOk x.t ∧ HeapW x.s.h) :
    ∀ (a : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)),
      (spec.frame r).Call a.1.s.n a.1.s.W a.1.s.h a.1.t → (spec.frame r).start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 →
      WOk a.1.t ∧ HeapW a.1.s.h := by
  intro a hc _
  obtain ⟨a₂, he⟩ := hc.2
  obtain ⟨x₀, n, x, a₁, L, d, K, hp, ⟨j, hj⟩, hK, ht₂, hh, ht⟩ := spec.entry_run r he
  have h₁ := FrameCore.wok_program hinit hp
  have h₂ := FrameCore.wok_ex hj h₁
  have hg := hK.wok_hole (by rw [← ht₂]; exact h₂.1)
  refine ⟨?_, by rw [hh]; exact h₂.2⟩
  rw [ht]
  simp only [WOk, wOks_iff, realizedCode, List.mem_append] at hg
  simp only [PassUnit.gotoOf, WOk, wOks_iff]
  exact ⟨fun e he => hg.1 e (.inl he), hg.2⟩

/-- **The frame's calls are reached terms** (proved, `entry_run`): the
term of every call the frame's claim is about is the request's run, whose
parts the call discipline gives free of runs. -/
theorem wfS_start (r : SourceRequest σ ι) :
    ∀ (a : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)),
      (spec.frame r).Call a.1.s.n a.1.s.W a.1.s.h a.1.t → (spec.frame r).start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 →
      wfS a.1.t = true := by
  intro a hc _
  obtain ⟨a₂, he⟩ := hc.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ht⟩ := spec.entry_run r he
  have hw := hc.1.2.1.1
  rw [ht] at hw ⊢
  simpa [PassUnit.gotoOf, wf, wfS] using hw

/-- **No run of `C`'s code waits as a binding's body at the frame's calls**
(proved, `entry_run`): the term of every call the frame's claim is about is
the request's run. -/
theorem noPend_start (r : SourceRequest σ ι) :
    ∀ (a : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)),
      (spec.frame r).Call a.1.s.n a.1.s.W a.1.s.h a.1.t → (spec.frame r).start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 →
      NoPend ((spec.frame r).F.at (spec.frame r).C) a.1.t := by
  intro a hc _
  obtain ⟨a₂, he⟩ := hc.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ht⟩ := spec.entry_run r he
  rw [ht]
  exact noPend_goto

omit [Labels ι] in
/-- **An initial configuration meets layout provenance and the residual
invariant** (proved, `lay_initial`, `wok_initial`): where the
initialization's node expressions and the realm's identities its slots
hold meet both, the realm's heap meets both, and the client is lowered
source. -/
theorem initial_starts {q : Code → ComponentTag → Layout → Bool}
    (hq : ∀ m c l, spec.F.ofC spec.C c = false → q m c l = true) {x₀ : Conf} (hx : spec.Initial x₀)
    (hsrc : ∀ client, x₀.t = .letE (.goto spec.initE spec.initK 0 spec.initL .undef (some spec.C)) client →
      LoweredSrc (spec.F.ofC spec.C) client)
    (hEl : ∀ e ∈ spec.initE, layP q e = true) (hEw : ∀ e ∈ spec.initE, WOk e)
    (hLl : ∀ v ∈ spec.initL, layP q v = true) (hLw : ∀ v ∈ spec.initL, Plain v)
    (hRl : HeapLay q spec.realm) (hRw : HeapW spec.realm) :
    (layP q x₀.t = true ∧ HeapLay q x₀.s.h) ∧ (WOk x₀.t ∧ HeapW x₀.s.h) := by
  obtain ⟨client, hh, ht, -, -⟩ := hx
  have hc := hsrc client ht
  rw [ht, hh]
  exact ⟨⟨lay_initial hq hEl hLl hc, hRl⟩,
    ⟨wok_initial (Fl := spec.flow) hEw hLw (LoweredSrc.lowered (P := spec.F.at spec.C) (Fl := spec.flow) hc), hRw⟩⟩

/-- **The checks read the flow's sites** (proved, by definition). -/
theorem flowSites (r : SourceRequest σ ι) : (spec.frame r).FlowSites spec.flow := fun _ _ _ _ => rfl

/-- **A call the frame's claim is about is at a typed configuration**
(proved): its entry is a configuration of the program, whose budget is
positive, whose world is admissible and types its heap. -/
theorem call_typed (r : SourceRequest σ ι) :
    ∀ n (W : WorldT n) h t, (spec.frame r).Call n W h t → 0 < n ∧ WorldAdm W ∧ HeapOk n W h := by
  intro n W h t hc
  obtain ⟨-, a₂, -, -, -, -, -, -, -, -, hn, hW, hh, -⟩ := hc
  subst hn
  cases eq_of_heq hW
  subst hh
  exact ⟨a₂.1.s.pos, a₂.1.s.adm, a₂.1.s.ok⟩

omit [Labels ι] in
/-- **The initial configurations meet layout provenance at the plan's
layouts and the residual invariant** (proved, `initial_starts` at
`initial_lowered`): where the initialization's node expressions, the
realm's identities its slots hold and the realm's heap meet both. -/
theorem initial_lay (hEl : ∀ e ∈ spec.initE, layP (layQ spec.fflow spec.lay) e = true)
    (hEw : ∀ e ∈ spec.initE, WOk e)
    (hLi : ∀ v ∈ spec.initL, layP (layQ spec.fflow spec.lay) v = true ∧ Plain v ∧ free false v = true)
    (hRl : HeapLay (layQ spec.fflow spec.lay) spec.realm) (hRw : HeapW spec.realm) :
    ∀ x, spec.Initial x →
      (layP (layQ spec.fflow spec.lay) x.t = true ∧ HeapLay (layQ spec.fflow spec.lay) x.s.h) ∧
        (WOk x.t ∧ HeapW x.s.h) := fun _ hx =>
  spec.initial_starts (fun _ _ _ hc => by
    show (!(spec.F.ofC spec.C _) || _) = true
    rw [hc]; rfl) hx (spec.initial_lowered hx) hEl hEw (fun v hv => (hLi v hv).1) (fun v hv => (hLi v hv).2.1)
    hRl hRw

end FramedSpec

end
end Verification.SourceClaimJson
