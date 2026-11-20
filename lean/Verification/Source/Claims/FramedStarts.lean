import Verification.Source.Claims.FramedReturns
import Verification.Source.Claims.FramedHistory

/-! # The frame's starts from the program

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The flow along a program"). The
invariants of a framed plan's frame at its starts are read along the
program's executions from its initial configurations:

- **The program's states** (`ProgOk`, `progOk_ex`): a reached term, a heap
  free of runs, layout provenance, no run of `C` waiting as a binding's
  body (where no code collects a rest), and the fit of the flow, kept by
  every step from initial configurations meeting them (`progOk_initial`,
  the fit there a named check premise, `InitialFits`).
- **The entry's run** (`entry_hole`): the entering step pushes the
  realized code's run at a position of outside code (`enter_hole_out`),
  the realization is the prologue's two steps (`prologue_det`, the closure
  entered at the prologue's label), so the run fits `O` there, at a
  proposal that is the request's at its body labels (`realizedFlowB`).
- **The frame's invariants**: every entry fits the flow (`entryFits`), its
  slots are values (`slotVals`), the checks give (S), (K) and (O)
  (`chkSound`), no key (`noKeys`), and its start meets the invariants of
  states (`startInv`), the program's history meeting them at the program's
  frame (`progFrame`, from initial configurations that are entries,
  `InitialEntry`) and its truncation keeping them.
- `ret_reachedW_public`: `ret_reachedW_spec` with these premises
  discharged, at the frame check's class separation (`classQuery`). -/

namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow HeapObservations

/-- **The innermost run of a context around a run** (proved, `path_ctx`). -/
theorem innermostGoto_ctx_goto {K : Tm → Tm} (hK : EvalCtx K) (E : List Tm)
    (Kc : List (Continuation × Option Target)) (l : Nat) (L : List Tm) (d : Tm) (cc : ComponentTag) :
    innermostGoto (K (.goto E Kc l L d cc)) = some ((E, Kc), l, L, d, cc) := by
  obtain ⟨c', g, S, hP⟩ := path_ctx hK none
  unfold innermostGoto
  rw [hP _ rfl]
  simp [path, wrap, mapLast]

/-- **A context around a frame running `undefined` has no innermost run**
(proved, `path_ctx`). -/
theorem innermostGoto_ctx_frame {K : Tm → Tm} (hK : EvalCtx K) (E : List Tm)
    (Kc : List (Continuation × Option Target)) (L : List Tm) (d : Tm) (k : Continuation) (x : Option Target)
    (cc : ComponentTag) : innermostGoto (K (.frame E Kc .undef L d k x cc)) = none := by
  obtain ⟨c', g, S, hP⟩ := path_ctx hK none
  unfold innermostGoto
  rw [hP _ rfl]
  simp [path, wrap, mapLast]

/-- **A step pushing a run from a reached term enters it from outside
code** (proved, by the step pushing the run at its hole, `step_hole_inv`,
as `entry_roots` reads it): where a step raises the calls of `C` active by
one to a context around a run, the hole's path is read at a tag outside
`C`. The step is a call of graph code (`depth_push`); a binding's body is
no run of `C` (`NoPend`), and a frame's step keeps the calls of `C`
active (`depthC_ctx`). -/
theorem enter_hole_out {F : Family} {C : Nat} {h h' : Heap} {t t' : Tm} (hs : Step h t h' t')
    (hw : wfS t = true) (hh : HeapFree h) (hnp : NoPend (F.at C) t)
    (hd : depthC F C none t' = depthC F C none t + 1) {K : Tm → Tm} (hK : EvalCtx K) {E : List Tm}
    {Kc : List (Continuation × Option Target)} {l : Nat} {L : List Tm} {d : Tm} {cc : ComponentTag}
    (ht' : t' = K (.goto E Kc l L d cc)) {c' : ComponentTag} (hP : PathAt K none c') : F.ofC C c' = false := by
  obtain ⟨u, hat, hu⟩ := step_hole_inv hs hw hh hK ht' rfl (by simp [free])
  have hnu := not_val_of_step hu
  have hwu := hK.wfS_hole hnu (by rw [← hat]; exact hw)
  have hdepth : depthC F C none (K (.goto E Kc l L d cc)) = depthC F C none (K u) + 1 := by
    rw [← ht', ← hat]; exact hd
  have hgv : isVal (Tm.goto E Kc l L d cc) = false := rfl
  have hpg : ∀ c, (path c (Tm.goto E Kc l L d cc)).map Prod.fst = [cc, c] := fun c => by simp [path]
  generalize eg : Tm.goto E Kc l L d cc = gt at hu
  cases hu
  all_goals first
    | (exfalso; cases eg; done)
    | skip
  case callGraph hr' hargs hbind =>
    revert eg; unfold CallArguments.graphEntry; split
    · intro eg
      simp only [Tm.goto.injEq] at eg
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := eg
      exact (depth_push hP hnu hgv (by simp [path, hr', pathArgs_vals _ hargs]) (hpg c') hdepth).2
    · intro eg; simp at eg
  case constructGraph hargs =>
    revert eg; unfold CallArguments.graphEntry; split
    · intro eg
      simp only [Tm.goto.injEq] at eg
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := eg
      exact (depth_push hP hnu hgv (by simp [path, pathArgs_vals _ hargs]) (hpg c') hdepth).2
    · intro eg; simp at eg
  case letV ha =>
    exfalso
    simp only [wfS, ha, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true, bodyOk, Bool.or_eq_true] at hwu
    rcases hwu.2 with hb | ⟨-, hb⟩
    · have := subst_free hwu.1 _ 0 false hb; rw [← eg] at this; simp [free] at this
    · rename_i b
      cases b <;> simp only [isRun, Bool.false_eq_true] at hb
      simp only [subst, Tm.goto.injEq] at eg
      obtain ⟨-, -, -, -, -, rfl⟩ := eg
      have h1 := hnp K _ _ _ _ _ _ cc hK hat
      obtain ⟨h2, -⟩ := depth_push hP hnu hgv (by simp [path, ha]) (hpg c') hdepth
      simp_all [Family.at]
  all_goals try (
    exfalso
    simp only [Tm.goto.injEq] at eg
    obtain ⟨-, -, -, -, -, rfl⟩ := eg
    have := depthC_ctx (F := F) (C := C) hK none hnu hgv fun c => by
      first
        | simp [path, path_val ‹isVal _ = true›, wrap, mapLast]
        | simp [path, raises_path ‹Raises _ _›, wrap, mapLast]
        | simp [path, wrap, mapLast]
    omega)
  all_goals exfalso
  case readField hl hv' => simpa [← eg, free] using hh.get hv'
  case indexField hk hl hv' => simpa [← eg, free] using hh.get hv'
  case elemRead hl hv' => simpa [← eg, free] using hh.get hv'
  case testV => split at eg <;> cases eg
  case arithV hb =>
    obtain ⟨-, -, hres⟩ := binop_result hb
    rcases hres with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> cases eg
  case elemStr => simp only [codeUnitAt] at eg; split at eg <;> cases eg
  case iteT => subst eg; simp [wfS, free] at hwu
  case iteF => subst eg; simp [wfS, free] at hwu
  case frameRet hv' => subst eg; simp [isVal] at hv'

/-- **A part of a closure's code is free of runs** (proved). -/
theorem codePart_free {t : Tm} (h : CodePart t) (p : Bool) : ReadOnly.free p t = true := by
  rcases h with ⟨i, rfl⟩ | h
  · rfl
  · cases t <;> simp_all [primVal, ReadOnly.free]

/-- **Lowered source is free of runs** (proved, by induction on the term):
it holds no run and no located value. -/
theorem loweredSrc_free {ofC : ComponentTag → Bool} : ∀ {e : Tm}, LoweredSrc ofC e → ∀ p, ReadOnly.free p e = true := by
  intro e
  induction e using Tm.induct
  all_goals intro h p
  all_goals try simp only [LoweredSrc, loweredSrcArgs_iff] at h
  all_goals try simp only [ReadOnly.free, frees_eq, List.all_eq_true, Bool.and_eq_true]
  all_goals first
    | grind [codePart_free]
    | trivial
    | skip

/-- **No context around a binding is a run** (proved). -/
theorem _root_.Verification.HeapObservations.EvalCtx.letE_ne_goto {K : Tm → Tm} (hK : EvalCtx K) (a b : Tm) {E : List Tm}
    {Kc : List (Continuation × Option Target)} {l : Nat} {L : List Tm} {d : Tm} {c : ComponentTag} :
    K (.letE a b) ≠ .goto E Kc l L d c := by
  cases hK <;> simp

/-- **No run of `C` waits as a binding's body at a binding of lowered source
behind a run** (proved): the only binding on the path is the term's own,
whose body is lowered source. -/
theorem noPend_letGoto {P : Package} {E : List Tm} {Kc : List (Continuation × Option Target)} {l : Nat}
    {L : List Tm} {d : Tm} {c : ComponentTag} {client : Tm} (hc : LoweredSrc P.ofC client) :
    NoPend P (.letE (.goto E Kc l L d c) client) := by
  intro K a E' Kc' l' L' d' cc hK ht
  cases hK with
  | hole =>
    simp only [Tm.letE.injEq] at ht
    obtain ⟨-, rfl⟩ := ht
    simp [LoweredSrc] at hc
  | letC b hK' =>
    simp only [Tm.letE.injEq] at ht
    exact absurd ht.1.symm (hK'.letE_ne_goto _ _)
  | _ => simp at ht

end Verification.TolerantFrames.ReadOnly

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly HeapObservations

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

namespace FramedSpec
variable (spec : FramedSpec ι)

/-- **The invariants of a program's states**: a reached term, a heap free
of runs, layout provenance at the plan's layouts, no run of `C` waiting as
a binding's body, and the fit of the flow. -/
def ProgOk (r : SourceRequest σ ι) (a : Conf × Ghost ((spec.core r).F.at (spec.core r).C)) : Prop :=
  wfS a.1.t = true ∧ HeapFree a.1.s.h ∧
    (layP (layQ spec.fflow spec.lay) a.1.t = true ∧ HeapLay (layQ spec.fflow spec.lay) a.1.s.h) ∧
    NoPend ((spec.core r).F.at (spec.core r).C) a.1.t ∧ (spec.frame r).FitsAt spec.flow a

/-- **Every step keeps the invariants of a program's states** (proved,
`step_wfS`, `step_wf`, `step_layP`, `noPend_step`, `fitsAt_step`): where no
code of the plan's flow collects a rest. -/
theorem progOk_step (r : SourceRequest σ ι) (hr : noRestB spec.lay = true) (hF : spec.flow.Facts)
    {a b : Conf × Ghost ((spec.core r).F.at (spec.core r).C)} (hk : (spec.core r).KStep a b)
    (ha : spec.ProgOk r a) : spec.ProgOk r b :=
  ⟨(step_wfS hk.1.step ha.1 ha.2.1).1, (step_wf hk.1.step (wfS_wf _ ha.1) ha.2.1).2.1,
    step_layP hk.1.step ha.2.2.1.1 ha.2.2.1.2,
    noPend_step hr hk.1.step ha.1 ha.2.1 ha.2.2.1.1 ha.2.2.2.1,
    ClientFrame.fitsAt_step (fr := spec.frame r) hF (spec.flowSites r) hk ha.2.2.2.2⟩

/-- **An execution keeps the invariants of a program's states** (proved,
`progOk_step`). -/
theorem progOk_ex (r : SourceRequest σ ι) (hr : noRestB spec.lay = true) (hF : spec.flow.Facts)
    {q : Conf × Ghost ((spec.core r).F.at (spec.core r).C) → Prop} {n : Nat}
    {a b : Conf × Ghost ((spec.core r).F.at (spec.core r).C)} (hex : Ex (spec.core r).KStep q n a b)
    (ha : spec.ProgOk r a) : spec.ProgOk r b :=
  hex.carry (r := spec.ProgOk r) (fun _ _ _ hk h => spec.progOk_step r hr hF hk h) ha

/-- **An initial configuration meets the invariants of a program's states**
(proved, `initial_lay`, `loweredSrc_free`, `noPend_letGoto`): where the
initialization's node expressions are free of runs and meet layout
provenance and the residual invariant, the realm meets both, the initial
configurations fit the flow and their heap is free of runs. -/
theorem progOk_initial (r : SourceRequest σ ι) (hEf : ∀ e ∈ spec.initE, TolerantFrames.ReadOnly.free false e = true)
    (hEl : ∀ e ∈ spec.initE, layP (layQ spec.fflow spec.lay) e = true)
    (hEw : ∀ e ∈ spec.initE, WOk e)
    (hLi : ∀ v ∈ spec.initL, layP (layQ spec.fflow spec.lay) v = true ∧ Plain v ∧ free false v = true)
    (hRl : HeapLay (layQ spec.fflow spec.lay) spec.realm) (hRw : HeapW spec.realm)
    (hinit : spec.InitialFits r) {x₀ : Conf} (hx : spec.Initial x₀) (hRf : HeapFree x₀.s.h) :
    spec.ProgOk r (x₀, bareStart (spec.core r).F (spec.core r).C x₀.t) := by
  have hl := (spec.initial_lay hEl hEw hLi hRl hRw x₀ hx).1
  have hfit := hinit x₀ hx
  obtain ⟨client, hh, ht, hc, -⟩ := hx
  refine ⟨?_, hRf, hl, ?_, hfit⟩
  · rw [ht]
    simp only [wfS, isVal, ↓reduceIte, runParts, frees_eq, List.all_eq_true,
      Bool.and_eq_true, bodyOk, Bool.or_eq_true]
    exact ⟨⟨⟨hEf, fun v hv => (hLi v hv).2.2⟩, rfl⟩, .inl (loweredSrc_free hc false)⟩
  · rw [ht]; exact noPend_letGoto hc

/-- **The realization runs the prologue** (proved, `Step_det` at the
prologue's two steps, `innermostGoto_ctx_goto`): from the realized code's
run at the prologue's label in a context, the first state whose innermost
run is the realized code at the request's start is the same context around
that run. -/
theorem prologue_det (r : SourceRequest σ ι) (hst : r.start < r.program.length)
    {a₁ a₂ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)} {K : Tm → Tm} (hK : EvalCtx K)
    {L₁ : List Tm} {d₁ : Tm} {c₁ : ComponentTag}
    (ht₁ : a₁.1.t = K (.goto (realizedCode r).1 (realizedCode r).2 r.program.length L₁ d₁ c₁)) {j : Nat}
    (hex : Ex (spec.core r).KStep
      (fun a => ¬ ∃ L' d' c', innermostGoto a.1.t = some (realizedCode r, r.start, L', d', c')) j a₁ a₂)
    {L : List Tm} {d : Tm} {c : ComponentTag}
    (h₂ : innermostGoto a₂.1.t = some (realizedCode r, r.start, L, d, c)) :
    a₂.1.t = K (.goto (realizedCode r).1 (realizedCode r).2 r.start L d c) := by
  have he : (realizedCode r).1[r.program.length]? = some .undef := by simp [realizedCode]
  have hk : (realizedCode r).2[r.program.length]? = some (.effect (prologueTarget r), none) := by
    simp [realizedCode, prologueTarget]
  have hi : instantiate 0 (envOf L₁ d₁) Tm.undef = .undef := by simp [instantiate]
  cases hex with
  | refl =>
    rw [ht₁, innermostGoto_ctx_goto hK] at h₂
    simp only [Option.some.injEq, Prod.mk.injEq] at h₂
    omega
  | next _ k1 hex1 =>
    have s1 := k1.1.step
    rw [ht₁] at s1
    obtain ⟨-, e1⟩ := Step_det s1 (hK.step (.gotoEnter (h := a₁.1.s.h) (L := L₁) (d := d₁) (comp := c₁) he hk))
    rw [hi] at e1
    cases hex1 with
    | refl => rw [e1, innermostGoto_ctx_frame hK] at h₂; cases h₂
    | next _ k2 hex2 =>
      have s2 := k2.1.step
      rw [e1] at s2
      obtain ⟨-, e2⟩ := Step_det s2 (hK.step (.frameEffect (h := _) (E := (realizedCode r).1)
        (K := (realizedCode r).2) (L := L₁) (d := d₁) (x := none) (comp := c₁) (l := prologueTarget r) rfl))
      cases hex2 with
      | refl =>
        rw [e2, innermostGoto_ctx_goto hK] at h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h₂
        obtain ⟨-, -, hL, hd, hc⟩ := h₂
        rw [e2, ← hL, ← hd, ← hc]
        rfl
      | next q3 _ _ =>
        exact absurd ⟨_, _, _, by rw [e2, innermostGoto_ctx_goto hK]; rfl⟩ q3

/-- **The fit of an entry's run** (proved): at an entry of the request, the
program's state fits the flow (`progOk_ex` from the initial
configurations), the entering step pushes the realized code's run at a
position of outside code (`enter_hole_out`), the prologue keeps it there
(`prologue_det`), so the run fits `O` there (`fits_ctx`) at a proposal of
the realized code, which is the request's at its body labels
(`realizedFlowB_sound`): the slots meet the proposal's sets at the
request's start and its returns lie within `O`. -/
theorem entry_hole (r : SourceRequest σ ι) (hr : noRestB spec.lay = true) (hF : spec.flow.Facts)
    (hst : r.start < r.program.length) (hreal : realizedFlowB spec.fflow r = true)
    (hcomp : (spec.F.at spec.C).ofC r.comp = true)
    (hinit : ∀ x, spec.Initial x → spec.ProgOk r (x, bareStart (spec.core r).F (spec.core r).C x.t))
    {k : Nat} {W : WorldT k} {h : Heap} {t : Tm} {a₂ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)}
    (he : spec.EntryAt r k W h t a₂) :
    ∃ L d c π, t = PassUnit.gotoOf r.program r.start L d r.comp ∧ h = a₂.1.s.h ∧
      spec.flow.code (requestCode r) c = some π ∧
      (∀ i, VJ spec.flow a₂.2 a₂.1.s.h.length (π.env r.start i) (envOf L d i)) ∧
      EnvFn π r.start L d ∧ Sub π.ret spec.flow.O ∧ HeapInv spec.flow a₂.2 a₂.1.s.h := by
  obtain ⟨x₀, n, x, a₁, L, d, hp, ⟨⟨L₁, d₁, c₁, hin₁⟩, ⟨j, hj⟩, hin₂⟩, -, -, hh, ht⟩ := he
  have hx := spec.progOk_ex r hr hF hp.2.1 (hinit x₀ hp.1)
  have ha₁ := spec.progOk_step r hr hF hp.2.2.1 hx
  obtain ⟨K, hK, ht₁⟩ := innermostGoto_ctx hin₁
  have ht₂ := spec.prologue_det r hst hK ht₁ hj hin₂
  have ha₂ := spec.progOk_ex r hr hF hj ha₁
  obtain ⟨c', hP, hFc⟩ := fits_ctx (Fl := spec.flow) (V := VJ spec.flow a₂.2 a₂.1.s.h.length) hK none
  have hout : spec.F.ofC spec.C c' = false :=
    enter_hole_out (F := spec.F) (C := spec.C) hp.2.2.1.1.step hx.1 hx.2.1 hx.2.2.2.1 hp.2.2.2.2.2 hK ht₁ hP
  have hO : (spec.F.at spec.C).ofC none = false := by simp [Family.at, Family.ofC, Family.Runs]
  obtain ⟨a', S', hfit⟩ := hFc rfl (by rw [hO, ← ht₂]; exact ha₂.2.2.2.2.1)
  rw [show (spec.F.at spec.C).ofC c' = spec.F.ofC spec.C c' from rfl, hout] at hfit
  cases hfit with
  | val hv => simp [isVal] at hv
  | gotoOut hc => exact absurd (hcomp.symm.trans hc) (by simp)
  | gotoC c π _ hcode henv hfn hret ho =>
    obtain ⟨π₂, hc₂, hr₂, -, hl₂⟩ := realizedFlowB_sound (F := spec.fflow) hreal hcode
    obtain ⟨he₂, -, hf₂, -, -⟩ := hl₂ r.start hst
    refine ⟨L, d, c, π₂, ht, hh, hc₂, fun i => ?_, fun i σ hσ => hfn i σ (by rw [hf₂]; exact hσ), ?_,
      ha₂.2.2.2.2.2⟩
    · rw [← he₂]; exact (henv i).top
    · rw [← hr₂]; exact fun s hs => ho rfl s (hret s hs)

/-- **Every entry of a framed plan's frame fits the flow** (proved,
`entry_hole`; the draft's `entryFits_public`): the frame's start at an
entry is the program's history truncated, which keeps its sites, so the
request's run at the entry's slots fits `O` at the proposal `entry_hole`
gives, and the heap meets the flow. -/
theorem entryFits (r : SourceRequest σ ι) (hr : noRestB spec.lay = true) (hF : spec.flow.Facts)
    (hst : r.start < r.program.length) (hreal : realizedFlowB spec.fflow r = true)
    (hcomp : (spec.F.at spec.C).ofC r.comp = true)
    (hinit : ∀ x, spec.Initial x → spec.ProgOk r (x, bareStart (spec.core r).F (spec.core r).C x.t)) :
    (spec.frame r).EntryFits spec.flow := by
  intro x g hc hs
  rcases hs with ⟨a₂, he, rfl⟩ | ⟨hne, -⟩
  · obtain ⟨L, d, c, π, ht, hh, hcode, henv, hfn, hret, hH⟩ := spec.entry_hole r hr hF hst hreal hcomp hinit he
    refine ⟨?_, ?_⟩
    · rw [ht, hh]
      exact .gotoC c π hcomp hcode (fun i => .inl (VJ.congr (g := a₂.2) (g' := truncate a₂.2) (fun _ _ => rfl) (henv i))) hfn hret
        (fun _ => Sub.refl _)
    · rw [hh]; exact HeapInv.congr (g := a₂.2) (g' := truncate a₂.2) (fun _ _ => rfl) hH
  · exact absurd hc.2 hne

/-- **The slots of every call the frame's claim is about are values**
(proved, `entry_hole`): each meets a set of the proposal's, as a value. -/
theorem slotVals (r : SourceRequest σ ι) (hr : noRestB spec.lay = true) (hF : spec.flow.Facts)
    (hst : r.start < r.program.length) (hreal : realizedFlowB spec.fflow r = true)
    (hcomp : (spec.F.at spec.C).ofC r.comp = true)
    (hinit : ∀ x, spec.Initial x → spec.ProgOk r (x, bareStart (spec.core r).F (spec.core r).C x.t)) :
    ∀ n (W : WorldT n) h (L : List Tm) (d : Tm),
      (spec.frame r).Call n W h (PassUnit.gotoOf r.program r.start L d r.comp) → SlotVals L d := by
  intro n W h L d hc
  obtain ⟨a₂, he⟩ := hc.2
  obtain ⟨L', d', c, π, ht, -, -, henv, -⟩ := spec.entry_hole r hr hF hst hreal hcomp hinit he
  simp only [PassUnit.gotoOf, Tm.goto.injEq] at ht
  obtain ⟨-, -, -, rfl, rfl, -⟩ := ht
  refine ⟨fun v hv => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have := (henv i).val
    simpa [envOf, List.getD_eq_getElem?_getD, hi] using this
  · have := (henv L.length).val
    rwa [envOf_default] at this

/-- **The frame's checks give no key, and its starts none** (proved): the
checks' keys are `none` by definition, the history before any entry has
none, and every step of the program keeps them (`stepAt_key`). -/
theorem noKeys (r : SourceRequest σ ι) : (spec.frame r).NoKeys := by
  have hck : ∀ h t h' t', (spec.chk r h t h' t').key = fun _ => none := fun _ _ _ _ => rfl
  refine ⟨hck, fun k W h t g hs => ?_⟩
  rcases hs with ⟨a₂, he, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨x₀, n, x, a₁, L, d, hp, ⟨-, ⟨j, hj⟩, -⟩, -⟩ := he
    have hstep : ∀ (a b : Conf × Ghost ((spec.core r).F.at (spec.core r).C)), True → (spec.core r).KStep a b →
        a.2.key = (fun _ => none) → b.2.key = fun _ => none := by
      intro a b _ hab ha
      obtain ⟨-, hg, -⟩ := hab
      rw [hg]
      simp only [FrameCore.next, stepAt_key, Ghost.alloc, ha]
      funext l; split
      · rfl
      · exact congrFun (hck _ _ _ _) l
    exact (hj.mono fun _ _ => trivial).carry hstep (hp.ex.carry hstep rfl)
  · rfl

/-- **What the checks give, at a framed plan's frame** (proved,
`chkSound_of_sitesIn`): where every entry fits the flow and its marks lend
`O` and hold local storage locally, the flow's sites give the checks at the
incoming crossings (`entryXs_roots`) and the actual ones. -/
theorem chkSound (r : SourceRequest σ ι) (hF : spec.flow.Facts)
    (hm : Lendable spec.flow.O ∧ LocalHeld spec.flow.H) (hE : (spec.frame r).EntryFits spec.flow) :
    (spec.frame r).ChkSound :=
  ClientFrame.chkSound_of_sitesIn (T := spec.outType) (inc := fun _ t _ t' => spec.entryXs r t t')
    (spec.actualCrossingsIn r) (fun s hs s' h' => hF.closed s hs s' h') hm.1 hm.2
    (ClientFrame.sitesSound_of_fits hF (spec.flowSites r) hE)
    (fun _ ha => ClientFrame.sitesAt_reached hF (spec.flowSites r) hE ha) (spec.entryXs_roots r)

/-- **The program's frame**: the plan's core and codes, its calls the
initial configurations, started from the history before any entry. Its
reached states are the program's. -/
noncomputable def progFrame (r : SourceRequest σ ι) : ClientFrame (Ty ι) where
  toFrameCore := spec.core r
  codes := (spec.frame r).codes
  start _ _ _ t g := g = bareStart (spec.core r).F (spec.core r).C t
  start_total _ _ _ _ := ⟨_, rfl⟩
  enters _ _ h t := ∃ client, h = spec.realm ∧ t = .letE (.goto spec.initE spec.initK 0 spec.initL .undef (some spec.C)) client ∧
    LoweredSrc (spec.F.ofC spec.C) client ∧ Scoped 1 client

/-- **The program's frame starts from the entry history with no argument**
(proved, by definition). -/
theorem progFrame_starts (r : SourceRequest σ ι) : (spec.progFrame r).StartsEntry fun _ _ => [] :=
  fun _ _ _ _ _ => Iff.rfl

/-- **The program's states fit the flow from initial configurations
fitting it** (proved, by definition). -/
theorem progFrame_entryFits (r : SourceRequest σ ι) (hinit : spec.InitialFits r) :
    (spec.progFrame r).EntryFits spec.flow := by
  intro x g hc hs
  subst hs
  exact hinit x hc.2

/-- **What the checks give at the program's steps** (proved,
`chkSound_of_sitesIn`; the draft's `chkSound_program`). -/
theorem progFrame_chkSound (r : SourceRequest σ ι) (hF : spec.flow.Facts)
    (hm : Lendable spec.flow.O ∧ LocalHeld spec.flow.H) (hinit : spec.InitialFits r) :
    (spec.progFrame r).ChkSound :=
  have hE := spec.progFrame_entryFits r hinit
  have hS : (spec.progFrame r).FlowSites spec.flow := fun _ _ _ _ => rfl
  ClientFrame.chkSound_of_sitesIn (T := spec.outType) (inc := fun _ t _ t' => spec.entryXs r t t')
    (fun _ _ _ _ => rfl) (fun s hs s' h' => hF.closed s hs s' h') hm.1 hm.2
    (ClientFrame.sitesSound_of_fits hF hS hE) (fun _ ha => ClientFrame.sitesAt_reached hF hS hE ha)
    (fun _ _ _ _ _ _ hc => spec.entryXs_root r hc)

/-- **The history a framed call starts from meets the invariants of
states** (proved; the draft's `startInv_public`): at an entry, the
program's history meets them (`reached_ok` at the program's frame), and
its truncation to the entered call's one set keeps the protected set, the
sites and the heap, the request's run at the top holding no root of
outside code; before any entry, the history before any entry meets them
(`entryStart_inv`). -/
theorem startInv (r : SourceRequest σ ι) (hF : spec.flow.Facts)
    (hm : Lendable spec.flow.O ∧ LocalHeld spec.flow.H) (hinit : spec.InitialFits r)
    (hinitE : spec.InitialEntry r) (hcomp : (spec.F.at spec.C).ofC r.comp = true) :
    (spec.frame r).StartInv := by
  intro x g _ hs
  rcases hs with ⟨a₂, he, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨x₀, n, x', a₁, L, d, hp, ⟨-, ⟨j, hj⟩, -⟩, -, -, hh, ht⟩ := he
    have hreach : (spec.progFrame r).Reached a₂ :=
      ⟨(x₀, bareStart (spec.core r).F (spec.core r).C x₀.t), n + 1 + j, ⟨hinitE x₀ hp.1, hp.1⟩, rfl,
        hp.ex.trans (hj.mono fun _ _ => trivial)⟩
    obtain ⟨-, hI, -⟩ := ClientFrame.reached_ok (spec.progFrame_chkSound r hF hm hinit)
      (ClientFrame.startInv_of_entry (spec.progFrame_starts r)) hreach
    have hc' : (spec.frame r).F.ofC (spec.frame r).C r.comp = true := hcomp
    have hn' : (spec.frame r).F.ofC (spec.frame r).C none = false := by simp [Family.ofC, Family.Runs]
    have hroots : ∀ v, v ∈ rootsOf (spec.frame r).F (spec.frame r).C none x.t → False := by
      intro v hv
      rw [ht] at hv
      simp [rootsOf, PassUnit.gotoOf, vals, hc'] at hv
    refine ⟨⟨fun X hX l => ?_, fun l ⟨v, hv, _⟩ => (hroots v hv).elim, fun l ⟨v, hv, _⟩ => (hroots v hv).elim,
      fun v hv => (hroots v hv).elim, fun w u hw => ?_, fun w u hw => ?_⟩, ?_⟩
    · have hX' : X = fun l => a₂.2.Prot l := List.mem_singleton.mp hX
      subst hX'
      show a₂.2.Prot l ↔ (∃ Y ∈ [fun l => a₂.2.Prot l], Y l) ∨ a₂.2.B l
      simp only [List.mem_singleton, exists_eq_left]
      exact ⟨.inl, fun h => h.elim id fun hb => .inr hb⟩
    · exact hI.localClosed w u (by simpa [lift, hh] using hw)
    · exact hI.bindings w u (by simpa [lift, hh] using hw)
    · rw [ht]
      simp [truncate, depthC, PassUnit.gotoOf, path, blocks, hc', hn']
  · exact ⟨entryStart_inv (tv := (spec.frame r).view.view) x [], by simp only [bareStart, List.length_replicate]; rfl⟩

/-! ## The initialization's code and the flow

Both named premises on the initial configurations read the
initialization's code at the plan's flow: an initial configuration's
term runs it at a tag of `C`, so code provenance (`InitialEntry`) needs
it among `C`'s codes, the codes the flow proposes for, and its fit
(`InitialFits`) needs a proposal of the flow for it (`gotoC`). -/

/-- **The initialization's tag runs `C`'s code** (proved, `framePkg_ofC`). -/
theorem init_ofC (r : SourceRequest σ ι) : (spec.frame r).F.ofC (spec.frame r).C (some spec.C) = true := by
  change (oneComponent spec.C spec.mark).family.ofC spec.C (some spec.C) = true
  rw [← framePkg_ofC spec.C spec.mark]
  simp

/-- **An initial configuration that is an entry runs a code of the flow**
(proved, by code provenance at the initialization's run). -/
theorem initialEntry_code (r : SourceRequest σ ι) {x : Conf} (hx : spec.Initial x)
    (he : (spec.frame r).Entry x.s.h x.t) : ∃ cx π, spec.flow.code (spec.initE, spec.initK) cx = some π := by
  obtain ⟨client, -, ht, -, -⟩ := hx
  have hp := he.1.1
  rw [ht] at hp
  simp only [prov, Bool.and_eq_true] at hp
  have hok := hp.1.1.1.1
  simp only [ClientFrame.ok, decide_eq_true_eq] at hok
  have hruns : (spec.frame r).F.Runs (some spec.C) (spec.frame r).C := by
    have := spec.init_ofC r
    simpa [Family.ofC] using this
  exact hok hruns

/-- **An initial configuration that fits the flow runs a code of the flow**
(proved, by the rules of `Fits` at a `letE` and at a run of `C`'s code). -/
theorem initialFits_code (r : SourceRequest σ ι) {x : Conf} (hx : spec.Initial x)
    (hf : (spec.frame r).FitsAt spec.flow (x, bareStart (spec.core r).F (spec.core r).C x.t)) :
    ∃ cx π, spec.flow.code (spec.initE, spec.initK) cx = some π := by
  obtain ⟨client, -, ht, -, -⟩ := hx
  have h := hf.1
  simp only at h
  rw [ht] at h
  cases h with
  | val hv _ _ => simp [isVal] at hv
  | letE hx _ _ =>
    cases hx with
    | val hv _ _ => simp [isVal] at hv
    | gotoC c π _ hcode _ _ _ _ => exact ⟨c, π, hcode⟩
    | gotoOut hc _ _ _ _ =>
      have h2 : ((spec.frame r).F.at (spec.frame r).C).ofC (some spec.C) = true := spec.init_ofC r
      rw [hc] at h2; cases h2

/-- **A closure creation whose code names a signature at a capture slot is
not lowered code** (proved): lowered code's closures of `C`'s code name a
signature only at their own slot (`SelfFn`). The initialization, which
creates such closures (P22's `walk`, its slot of `%ElementAt%` naming the
native's signature), is no lowered code; the flow's codes are checked to
hold no located value (`CodesLowered`) and their node expressions to fit
openly (`OFits.makeGraphC`, whose `OCapFn` admits a capture slot naming
the signature its capture names). -/
theorem capSig_not_lowered {P : Package} {Fl : Flow P} {ar s j c : Nat} {E : List Tm}
    {K : List (Continuation × Option Target)} {caps : List Tm} {k} {rest : Bool} {comp : ComponentTag} {ns}
    {xs : List Tm} {π : CodeFlow P} {σ : FnSig} (hC : P.ofC comp = true) (hπ : Fl.code (E, K) c = some π)
    (hj : j < caps.length) (hσ : π.fn s (capSlot ar rest j) = some σ) :
    ¬ Lowered Fl (.makeAt (.graph ar E K s caps k rest comp) ns xs) := by
  intro h
  simp only [Lowered] at h
  have := (((h.1 hC).2 c π hπ).1 _ σ hσ).1
  simp only [capSlot, Nat.add_left_cancel_iff] at this
  omega

end FramedSpec
end
end Verification.SourceClaimJson

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open Verification.TolerantFrames.ReadOnly
open HeapObservations

/-- **The returns at reached executions of a framed plan, its frame's
invariants from the program** (proved, `ret_reachedW_spec` at the frame
check's class separation): from initial configurations that are entries
and fit the flow (`InitialEntry`, `InitialFits`, named check premises),
through the program's executions, every entry fits the flow
(`FramedSpec.entryFits`), so its slots are values (`FramedSpec.slotVals`)
and the checks give (S), (K) and (O) (`FramedSpec.chkSound`); its start
meets the invariants of states (`FramedSpec.startInv`); no step and no
start has a key (`FramedSpec.noKeys`); the class separation is sound at
every state (`classQuery_sound`). What it reads besides
`ret_reachedW_spec`'s other premises: the request's start a body label,
the realized code's proposals the request's (`realizedFlowB`) and the
marks (`marksB`) at the plan's flow, and the initialization's node
expressions free of runs. -/
theorem ret_reachedW_public {σ ι : Type} [Labels ι] [StoreView σ ι] (spec : FramedSpec ι) (r : SourceRequest σ ι)
    {F : Nat → Bool} {S : Nat → List Footprints.Footprint}
    (hsrc : r.program.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (hcomp₀ : spec.componentRefusal.val = none)
    (hEl : ∀ e ∈ spec.initE, layP (layQ spec.fflow spec.lay) e = true) (hEw : ∀ e ∈ spec.initE, WOk e)
    (hLi : ∀ v ∈ spec.initL, layP (layQ spec.fflow spec.lay) v = true ∧ Plain v ∧ free false v = true)
    (hRl : HeapLay (layQ spec.fflow spec.lay) spec.realm) (hRw : HeapW spec.realm)
    (hFa : spec.fflow.flow.Facts) (hmk : spec.fflow.marksB = true)
    (hst : r.start < r.program.length) (hreal : realizedFlowB spec.fflow r = true)
    (hEf : ∀ e ∈ spec.initE, TolerantFrames.ReadOnly.free false e = true)
    (hinitF : spec.InitialFits r) (hinitE : spec.InitialEntry r)
    (htok : tokensSomeB spec.fflow = true) (hlow : codesLoweredB spec.fflow = true)
    (hcomp : (spec.frame r).F.ofC (spec.frame r).C r.comp = true)
    (hatom : ∀ l e, F l = true → (r.program.map (·.expression))[l]? = some e → ClientFrame.atomCallB e = true)
    {S₀ T : Nat → Sites ((spec.frame r).F.at (spec.frame r).C)}
    {Ψc : Nat → Protocol ((spec.frame r).F.at (spec.frame r).C)}
    (hT : ∀ l, F l = true → capClosedB spec.fflow (tokenCaps spec.fflow spec.lay) (S₀ l) (T l) = true)
    (hle : ∀ l, F l = true → ∀ p, (probeProtocol (flowKinds spec.fflow) (T l) p).le (Ψc l p) = true)
    (hslots : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      spec.fflow.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ j ∈ ClientFrame.atomSlots e, Sub (π.env l' j) (T l))
    {Φ : Nat → Footprints.Footprint}
    (hcheck : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      spec.fflow.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ T ∈ S l, frameCheckAt classQuery (Ψc l) (Φ l) T spec.fflow.flow.H (π.env l') noKeys (fun _ => false) = true)
    (hTm : capClosedB spec.fflow (tokenCaps spec.fflow spec.lay) (captureSites spec.fflow spec.lay ++ spec.fflow.O)
      (capClose spec.fflow (tokenCaps spec.fflow spec.lay) (captureSites spec.fflow spec.lay ++ spec.fflow.O)) = true)
    (hΘ : ∀ p, ((spec.frame r).Θ p).le (componentProtocol spec.fflow spec.lay p) = true)
    (hW : ∀ l p, (componentProtocol spec.fflow spec.lay p).le (Ψc l p) = true)
    (hΦ : ∀ l (b₀ a : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)) m e L d k x v, F l = true →
      (spec.frame r).Reached b₀ →
      (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → SlotVals L d →
      b₀.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        (instantiate 0 (envOf L d) e) L d k x r.comp →
      Ex (spec.frame r).KStep (fun s => Inside (spec.frame r).F (spec.frame r).C (r.program.map (·.expression))
        (r.program.map fun n => (n.continuation, n.handler)) L d k x r.comp s.1.t) m b₀ a →
      a.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler)) v L d k x
        r.comp → isVal v = true → TolerantFrames.Action (Φ l) (envOf L d) b₀.1.s a.1.s) :
    FramedReturnsReachedW r (spec.frame r) F (fun l ρ h₀ h₁ => ∀ T ∈ S l, Footprints.Supported T ρ h₀ h₁)
      (fun _ _ _ _ => True) := by
  have hnone := componentBindingRefusal_none (spec.componentRefusal_none hcomp₀)
  have hr : noRestB spec.lay = true := hnone.2.2.2.2.2.1
  have hinit : ∀ x, spec.Initial x → spec.ProgOk r (x, bareStart (spec.core r).F (spec.core r).C x.t) :=
    fun x hx => spec.progOk_initial r hEf hEl hEw hLi hRl hRw hinitF hx (hinitE x hx).2.1.2
  have hE := spec.entryFits r hr hFa hst hreal hcomp hinit
  exact ret_reachedW_spec spec r hsrc (spec.slotVals r hr hFa hst hreal hcomp hinit)
    (spec.chkSound r hFa (FFlow.marksB_sound hmk) hE)
    (spec.startInv r hFa (FFlow.marksB_sound hmk) hinitF hinitE hcomp) hcomp₀ hEl hEw hLi hRl hRw hFa hE (spec.noKeys r) htok hlow
    hcomp hatom hT hle hslots hcheck (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => classQuery_sound _ _) hTm hΘ hW hΦ

end Verification.SourceClaimJson.PassUnit
