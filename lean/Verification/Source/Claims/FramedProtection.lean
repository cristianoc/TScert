import Verification.Source.Claims.FramedStarts

/-! # The protection a framed call starts with

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Milestone 2: the protected
reading", the theorem chain's steps 3 and 4). A call the frame's claim is
about is the realization of an entering step of the realized code from
outside code (`FramedSpec.EntryAt`); its slots and the history it starts
from are read from that step:

- **The entered call** (`enter_call`): an entering step from a term whose
  path holds no pending binding pushes a run in an evaluation context by a
  call or a `new` of a closure whose code it runs, from a position of
  outside code; the run's slots are the receiver, the closure's
  parameters of the actuals, its captures and the closure itself
  (`CallArguments.graphEntry`), and the heap is kept.
- **The entry's slots** (`FramedSpec.enter_args`): at an entry, each slot
  `j` below the arity holds `undefined` or the call's argument `j`, which
  the entering step records crossing in at its entry type (`entryTy`);
  the closure's arity is the plan's (`arityB`, layout provenance).
- **The protection at the start** (`FramedSpec.start_protects`): every
  location a slot `j` at a read-only position reaches at the entry's heap
  is of no local or internal site, is protected or exposed and recorded in
  `E` at the frame's start, and has a live witness there where it is
  released or outside storage: the crossing reached it read-only
  (`crosses_witness`, `crosses_covers`, `CrossOk` of the entering step),
  the prologue grows the history (`Ex.grows`), and the start is its
  truncation (`truncate_grows`). -/

namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow HeapObservations

/-- **The active frame of a term in a context is the hole's, at the tag
the hole's path is read at** (proved, by induction on the context, as
`activeFrame_ctx` and `fits_ctx`). -/
theorem activeFrame_pathAt {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ cur, ∃ c', (∀ u, isVal u = false → activeFrame cur (K u) = activeFrame c' u) ∧
      PathAt K (frameTag cur) (frameTag c') := by
  induction hK with
  | hole =>
    refine fun cur => ⟨cur, fun _ _ => rfl, id, [], fun t _ => ?_⟩
    have e : (fun p : ComponentTag × Tm => (p.1, id p.2)) = fun p => p := funext fun _ => rfl
    simp only [wrap, List.append_nil, e, mapLast_self]
  | frameC E Kc L d k x comp hK ih =>
    intro cur
    obtain ⟨c', hc', g, S, hP⟩ := ih (some (((E, Kc), comp), (k, x)))
    obtain ⟨g', S', hw⟩ := wrap_wrap_append (fun s => .frame E Kc s L d k x comp) g S
    refine ⟨c', fun u hu => by simp only [activeFrame]; exact hc' u hu, g', S' ++ [(frameTag cur, hole)],
      fun t ht => ?_⟩
    simp only [path]
    rw [show frameTag (some (((E, Kc), comp), (k, x))) = comp from rfl] at hP
    rw [hP t ht, hw, List.append_assoc]
  | @callArg K₀ f r args i hf hr hi hpre hK ih =>
    intro cur
    obtain ⟨c', hc', hP⟩ := ih cur
    refine ⟨c', fun u hu => ?_, hP.keep ⟨fun s => .invoke f r (args.set i s), fun t ht => ?_⟩⟩
    · simp only [activeFrame, hf, hr, Bool.true_eq_false, ite_false]
      rw [activeArgs_at (List.getElem?_set_self hi) (set_prefix hpre) (hK.not_val hu)]
      exact hc' u hu
    · simp only [path, hf, hr, Bool.true_eq_false, ite_false]
      rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre (hK.not_val ht)]
  | @constructArg K₀ f args i hf hi hpre hK ih =>
    intro cur
    obtain ⟨c', hc', hP⟩ := ih cur
    refine ⟨c', fun u hu => ?_, hP.keep ⟨fun s => .construct f (args.set i s), fun t ht => ?_⟩⟩
    · simp only [activeFrame, hf, Bool.true_eq_false, ite_false]
      rw [activeArgs_at (List.getElem?_set_self hi) (set_prefix hpre) (hK.not_val hu)]
      exact hc' u hu
    · simp only [path, hf, Bool.true_eq_false, ite_false]
      rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre (hK.not_val ht)]
  | @makeArg K₀ cc ns inits i hi hpre hK ih =>
    intro cur
    obtain ⟨c', hc', hP⟩ := ih cur
    refine ⟨c', fun u hu => ?_, hP.keep ⟨fun s => .makeAt cc ns (inits.set i s), fun t ht => ?_⟩⟩
    · simp only [activeFrame]
      rw [activeArgs_at (List.getElem?_set_self hi) (set_prefix hpre) (hK.not_val hu)]
      exact hc' u hu
    · simp only [path]
      rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre (hK.not_val ht)]
  | @arrArg K₀ inits i hi hpre hK ih =>
    intro cur
    obtain ⟨c', hc', hP⟩ := ih cur
    refine ⟨c', fun u hu => ?_, hP.keep ⟨fun s => .arrLit (inits.set i s), fun t ht => ?_⟩⟩
    · simp only [activeFrame]
      rw [activeArgs_at (List.getElem?_set_self hi) (set_prefix hpre) (hK.not_val hu)]
      exact hc' u hu
    · simp only [path]
      rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre (hK.not_val ht)]
  | _ =>
    rename_i hK ih
    intro cur
    obtain ⟨c', hc', hP⟩ := ih cur
    refine ⟨c', fun u hu => ?_, hP.keep ⟨?_, fun t ht => ?_⟩⟩
    rotate_left 2
    · simp only [path, hK.not_val ht, *, ite_true, ite_false, Bool.true_eq_false]
      rfl
    · simp only [activeFrame, hK.not_val hu, *, ite_true, ite_false, Bool.true_eq_false]

/-- **An entering step is a call of graph code from outside code**
(proved, as `entry_roots` decomposes it): where a step from a term free of
pending bindings of `C`'s runs raises the calls of `C` active by one to a
context around a run, the term is the context around a call (or `new`) of
a closure of the run's code, whose callee, receiver and actuals are values,
read at a tag outside `C`, which is the term's active frame's tag and its
redex; the step keeps the heap, and the run's slots are the receiver, the
closure's parameters of the actuals, its captures and the closure
(`CallArguments.graphEntry`, no rest), its default `null`. -/
theorem enter_call {F : Family} {C : Nat} {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') (hw : wfS t = true)
    (hh : HeapFree h) (hnp : NoPend (F.at C) t) (hd : depthC F C none t' = depthC F C none t + 1)
    {K : Tm → Tm} {E : List Tm} {Kc : List (Continuation × Option Target)} {l : Nat} {L : List Tm} {d : Tm}
    {cc : ComponentTag} (hK : EvalCtx K) (ht' : t' = K (.goto E Kc l L d cc)) :
    ∃ (u : Tm) (fs : List (PropKey × Nat)) (n : Nat) (caps : List Tm) (kk : Invoke) (oid : Nat) (recv : Tm)
      (args : List Tm),
      t = K u ∧ h' = h ∧ isVal recv = true ∧ (∀ a ∈ args, isVal a = true) ∧ F.ofC C cc = true ∧
      F.ofC C (frameTag (activeFrame none t).1) = false ∧ (activeFrame none t).2 = u ∧
      (u = .invoke (.objAt fs (.graph n E Kc l caps kk false cc) oid) recv args ∨
        u = .construct (.objAt fs (.graph n E Kc l caps kk false cc) oid) args) ∧
      L = recv :: CallArguments.parameters n args ++ (caps ++ [.objAt fs (.graph n E Kc l caps kk false cc) oid]) ∧
      d = .nul := by
  obtain ⟨u, hat, hu⟩ := step_hole_inv hs hw hh hK ht' rfl (by simp [free])
  have hnu := not_val_of_step hu
  have hwu := hK.wfS_hole hnu (by rw [← hat]; exact hw)
  have hheap : h' = h := enter_keeps_heap (F := F) (C := C) (c := none) hs hw hh (by omega)
  obtain ⟨c', hc', hP⟩ := activeFrame_pathAt hK none
  have hdepth : depthC F C none (K (.goto E Kc l L d cc)) = depthC F C none (K u) + 1 := by
    rw [← ht', ← hat]; exact hd
  have hgv : isVal (Tm.goto E Kc l L d cc) = false := rfl
  have hpg : ∀ c, (path c (Tm.goto E Kc l L d cc)).map Prod.fst = [cc, c] := fun c => by simp [path]
  have hact : ∀ f r args, isVal f = true → isVal r = true → (∀ a ∈ args, isVal a = true) →
      u = .invoke f r args → activeFrame none t = (c', u) := by
    intro f r args hf hr ha hu'
    rw [hat, hc' u hnu, hu']
    simp only [activeFrame, hf, hr, Bool.true_eq_false, ite_false]
    exact activeArgs_vals ha
  have hactC : ∀ f args, isVal f = true → (∀ a ∈ args, isVal a = true) →
      u = .construct f args → activeFrame none t = (c', u) := by
    intro f args hf ha hu'
    rw [hat, hc' u hnu, hu']
    simp only [activeFrame, hf, Bool.true_eq_false, ite_false]
    exact activeArgs_vals ha
  generalize eg : Tm.goto E Kc l L d cc = gt at hu
  generalize eh₀ : h = h₀ at hu
  generalize eh₁ : h' = h₁ at hu
  cases hu
  all_goals first
    | (exfalso; cases eg; done)
    | skip
  case callGraph hr' hargs hbind =>
    revert eg; unfold CallArguments.graphEntry; split
    · intro eg
      simp only [Tm.goto.injEq] at eg
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := eg
      obtain ⟨hcc, hc⟩ := depth_push hP hnu hgv (by simp [path, hr', pathArgs_vals _ hargs]) (hpg _) hdepth
      have ha := hact _ _ _ rfl hr' hargs rfl
      exact ⟨_, _, _, _, _, _, _, _, hat, rfl, hr', hargs, hcc, by rw [ha]; exact hc, by rw [ha],
        .inl rfl, rfl, rfl⟩
    · intro eg; simp at eg
  case constructGraph hargs =>
    revert eg; unfold CallArguments.graphEntry; split
    · intro eg
      simp only [Tm.goto.injEq] at eg
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := eg
      obtain ⟨hcc, hc⟩ := depth_push hP hnu hgv (by simp [path, pathArgs_vals _ hargs]) (hpg _) hdepth
      have ha := hactC _ _ rfl hargs rfl
      exact ⟨_, _, _, _, _, _, _, _, hat, rfl, rfl, hargs, hcc, by rw [ha]; exact hc, by rw [ha],
        .inr rfl, rfl, rfl⟩
    · intro eg; simp at eg
  -- A binding's body: outside code.
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
      obtain ⟨h2, -⟩ := depth_push hP hnu hgv (by simp [path, ha]) (hpg _) hdepth
      simp_all [Family.at]
  -- A frame's step to its code's next node: the calls of `C` active kept.
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
  -- Every other step to a run's term yields no run.
  all_goals exfalso
  all_goals subst eh₀
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

end Verification.TolerantFrames.ReadOnly

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly HeapObservations

/-- A closure's parameters at a position below its arity are the actuals'
or `undefined` (proved). -/
theorem parameters_getD : ∀ (n : Nat) (args : List Tm) (j : Nat), j < n →
    (CallArguments.parameters n args).getD j .undef = args.getD j .undef
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], 0, _ => rfl
  | n + 1, [], j + 1, h => by
    simp only [CallArguments.parameters, List.getD_cons_succ]
    exact (parameters_getD n [] j (by omega)).trans (by simp)
  | n + 1, a :: args, 0, _ => rfl
  | n + 1, a :: args, j + 1, h => by
    simp only [CallArguments.parameters, List.getD_cons_succ]
    exact parameters_getD n args j (by omega)

theorem parameters_length : ∀ (n : Nat) (args : List Tm), (CallArguments.parameters n args).length = n
  | 0, _ => rfl
  | n + 1, [] => by simp [CallArguments.parameters, parameters_length n []]
  | n + 1, _ :: args => by simp [CallArguments.parameters, parameters_length n args]

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

namespace FramedSpec
variable (spec : FramedSpec ι)

/-- **The prologue's run** (proved, `Step_det` at the prologue's two
steps, as `prologue_det`): from the realized code's run at the prologue's
label in a context, the first state whose innermost run is the realized
code at the request's start holds the slots the prologue maps, at the same
heap, along steps keeping the calls of `C` active. -/
theorem prologue_run (r : SourceRequest σ ι) (hst : r.start < r.program.length)
    {a₁ a₂ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)} {K : Tm → Tm} (hK : EvalCtx K)
    {L₁ : List Tm} {d₁ : Tm} {c₁ : ComponentTag}
    (ht₁ : a₁.1.t = K (.goto (realizedCode r).1 (realizedCode r).2 r.program.length L₁ d₁ c₁)) {j : Nat}
    (hex : Ex (spec.core r).KStep
      (fun a => ¬ ∃ L' d' c', innermostGoto a.1.t = some (realizedCode r, r.start, L', d', c')) j a₁ a₂)
    {L : List Tm} {d : Tm} {c : ComponentTag}
    (h₂ : innermostGoto a₂.1.t = some (realizedCode r, r.start, L, d, c)) :
    L = (envMap (prologueTarget r).mapping L₁ d₁).1 ∧ d = (envMap (prologueTarget r).mapping L₁ d₁).2 ∧
      c = c₁ ∧ a₂.1.s.h = a₁.1.s.h ∧
      depthC (spec.core r).F (spec.core r).C none a₂.1.t = depthC (spec.core r).F (spec.core r).C none a₁.1.t ∧
      Ex (spec.core r).KStep (fun y => depthC (spec.core r).F (spec.core r).C none y.1.t =
        depthC (spec.core r).F (spec.core r).C none a₁.1.t) j a₁ a₂ := by
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
    obtain ⟨eh1, e1⟩ := Step_det s1 (hK.step (.gotoEnter (h := a₁.1.s.h) (L := L₁) (d := d₁) (comp := c₁) he hk))
    rw [hi] at e1
    cases hex1 with
    | refl => rw [e1, innermostGoto_ctx_frame hK] at h₂; cases h₂
    | next _ k2 hex2 =>
      have s2 := k2.1.step
      rw [e1] at s2
      obtain ⟨eh2, e2⟩ := Step_det s2 (hK.step (.frameEffect (h := _) (E := (realizedCode r).1)
        (K := (realizedCode r).2) (L := L₁) (d := d₁) (x := none) (comp := c₁) (l := prologueTarget r) rfl))
      cases hex2 with
      | refl =>
        rw [e2, innermostGoto_ctx_goto hK] at h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h₂
        obtain ⟨-, -, hL, hd, hc⟩ := h₂
        have hmid : depthC (spec.core r).F (spec.core r).C none
            (K (.frame (realizedCode r).1 (realizedCode r).2 .undef L₁ d₁ (.effect (prologueTarget r)) none c₁)) =
            depthC (spec.core r).F (spec.core r).C none a₁.1.t := by
          rw [ht₁]
          exact depthC_ctx hK none rfl rfl fun c => by simp [path, wrap, mapLast]
        refine ⟨hL.symm, hd.symm, hc.symm, eh2.trans eh1, ?_, .next rfl k1 (.next ?_ k2 (.refl _))⟩
        · rw [e2, ht₁]
          exact depthC_ctx hK none rfl rfl fun c => by simp [path]
        · rw [e1]; exact hmid
      | next q3 _ _ =>
        exact absurd ⟨_, _, _, by rw [e2, innermostGoto_ctx_goto hK]; rfl⟩ q3

omit [Labels ι] in
/-- The frame's flow has the checked flow's layouts (proved): renaming the
sites keeps the codes. -/
theorem layAt_fflow (m : Code) : layAt spec.fflow spec.lay m = layAt spec.checked spec.lay m := by
  simp [layAt, FramedSpec.fflow, FFlow.mapSites, List.map_map, Function.comp_def]

/-- **The entry's slots** (proved, `enter_call`, `prologue_run`, layout
provenance at the program's state): at an entry of the request, the
public call's entering step from a program's state `x` to `a₁` keeps the
heap and records, for each slot `j` below the arity, the slot's value
crossing in at its entry type, where the slot does not hold `undefined`:
the entered closure's arity is the plan's (`arityB`), its parameters the
call's arguments; the prologue maps them to the request's start, keeping
the heap and the calls of `C` active. -/
theorem enter_args (r : SourceRequest σ ι) (hr : noRestB spec.lay = true) (hF : spec.flow.Facts)
    (hst : r.start < r.program.length) (hcomp : (spec.F.at spec.C).ofC r.comp = true)
    (har : spec.arityB r = true)
    (hinit : ∀ x, spec.Initial x → spec.ProgOk r (x, bareStart (spec.core r).F (spec.core r).C x.t))
    {k : Nat} {W : WorldT k} {h : Heap} {t : Tm} {a₂ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)}
    (he : spec.EntryAt r k W h t a₂) :
    ∃ (x₀ : Conf) (n : Nat) (x a₁ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)) (L : List Tm) (d : Tm)
      (m : Nat),
      spec.Initial x₀ ∧ Ex (spec.core r).KStep (fun _ => True) n (x₀, bareStart (spec.core r).F (spec.core r).C x₀.t) x ∧
      (spec.core r).KStep x a₁ ∧
      depthC (spec.core r).F (spec.core r).C none a₁.1.t = depthC (spec.core r).F (spec.core r).C none x.1.t + 1 ∧
      depthC (spec.core r).F (spec.core r).C none a₂.1.t = depthC (spec.core r).F (spec.core r).C none a₁.1.t ∧
      Ex (spec.core r).KStep (fun y => depthC (spec.core r).F (spec.core r).C none y.1.t =
        depthC (spec.core r).F (spec.core r).C none a₁.1.t) m a₁ a₂ ∧
      t = PassUnit.gotoOf r.program r.start L d r.comp ∧ h = x.1.s.h ∧ a₁.1.s.h = x.1.s.h ∧ a₂.1.s.h = x.1.s.h ∧
      ∀ j, j < spec.arity → envOf L d j = .undef ∨
        (⟨.into, spec.entryTy r j, envOf L d j⟩ : Crossing spec.view.view) ∈ spec.entryXs r x.1.t a₁.1.t := by
  obtain ⟨x₀, n, x, a₁, L, d, hp, ⟨⟨L₁, d₁, c₁, hin₁⟩, ⟨m, hm⟩, hin₂⟩, -, -, hh, ht⟩ := he
  obtain ⟨hx₀, hex, hent⟩ := hp
  obtain ⟨hk, hout, hentered, hdep⟩ := hent
  have hx := spec.progOk_ex r hr hF hex (hinit x₀ hx₀)
  obtain ⟨K, hK, ht₁⟩ := innermostGoto_ctx hin₁
  obtain ⟨hL, hd, hc, hh₂, hda₂, hm'⟩ := spec.prologue_run r hst hK ht₁ hm hin₂
  obtain ⟨u, fs, nn, caps, kk, oid, recv, args, hxu, hh₁, -, -, -, htag, hred, hu, hL₁, hd₁⟩ :=
    enter_call (F := (spec.core r).F) (C := (spec.core r).C) hk.1.step hx.1 hx.2.1 hx.2.2.2.1 hdep hK ht₁
  -- The entered closure's arity is the plan's.
  have hlay : layP (layQ spec.fflow spec.lay) u = true := hK.layP_hole (by rw [← hxu]; exact hx.2.2.1.1)
  have hq : layQ spec.fflow spec.lay (realizedCode r) c₁ (nn, false, caps.length, r.program.length) = true := by
    rcases hu with rfl | rfl <;> simp only [layP, layPs_eq, Bool.and_eq_true] at hlay
    · exact hlay.1.1.1.1
    · exact hlay.1.1.1
  have hc₁ : (spec.F.at spec.C).ofC c₁ = true := hc ▸ hcomp
  simp only [layQ, hc₁, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hq
  simp only [FramedSpec.arityB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at har
  rw [← spec.layAt_fflow, hq] at har
  obtain ⟨har, hlen⟩ := har
  simp only [Option.map_some, Option.some.injEq] at har
  subst har
  refine ⟨x₀, n, x, a₁, L, d, m, hx₀, hex, hk, hdep, hda₂, hm', ht, hh.trans (hh₂.trans hh₁), hh₁, hh₂.trans hh₁,
    fun j hj => ?_⟩
  -- Slot `j` is the call's argument `j`, or `undefined`.
  have hslot : envOf L d j = args.getD j .undef := by
    have hji : j < r.inputs.length + 1 := by omega
    rw [hL, hL₁]
    simp only [envOf, envMap, prologueTarget, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hji, Option.map_some, Option.getD_some]
    have hpl : j < (CallArguments.parameters spec.arity args).length := by rw [parameters_length]; exact hj
    rw [List.getElem?_append_left (by simp only [List.length_cons]; omega), List.getElem?_cons_succ,
      List.getElem?_eq_getElem hpl, Option.getD_some]
    have := parameters_getD spec.arity args j hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpl, Option.getD_some] at this
    exact this
  by_cases hja : j < args.length
  · refine .inr ?_
    have hcond : spec.F.ofC spec.C (frameTag (activeFrame none x.1.t).1) = false ∧
        entered none a₁.1.t = some (realizedCode r) ∧
        depthC spec.F spec.C none a₁.1.t = depthC spec.F spec.C none x.1.t + 1 := ⟨htag, hentered, hdep⟩
    unfold FramedSpec.entryXs
    rw [ite_eq_left hcond, hred]
    have hmem : (⟨.into, spec.entryTy r j, envOf L d j⟩ : Crossing spec.view.view) ∈
        (args.take spec.arity).mapIdx fun j v => (⟨.into, spec.entryTy r j, v⟩ : Crossing spec.view.view) := by
      refine List.mem_mapIdx.mpr ⟨j, by simp; omega, ?_⟩
      rw [hslot, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hja]
      simp
    rcases hu with rfl | rfl <;> exact hmem
  · exact .inl (by rw [hslot, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl)

/-- **`undefined` reaches no location** (proved): it has no field, spine,
cell or code. -/
theorem _root_.Verification.TolerantFrames.ReadOnly.undef_reaches {ofC : ComponentTag → Bool} {h : Heap} {l : Nat} :
    ¬ Reaches ofC h .undef l := by
  have hn : ∀ a, next .undef a = none := by
    intro a; cases a <;> simp [next, Footprints.fieldsOf, HeapKnowledge.descriptorSpine, spineEntries]
  rintro ⟨π, hf⟩
  match π, hf with
  | [a], hf => simp [Follows, hn a] at hf
  | a :: _ :: _, ⟨_, hs, _⟩ =>
    rcases hs with ⟨_, hn', _⟩ | ⟨_, -, hc⟩
    · rw [hn a] at hn'; cases hn'
    · simp [codeVals] at hc

/-- **A run's slots have valid references where the run does** (proved). -/
theorem _root_.Verification.TolerantFrames.ReadOnly.goto_rootsOk {n : Nat} {W : WorldT n} {E : List Tm}
    {K : List (Continuation × Option Target)} {l : Nat} {L : List Tm} {d : Tm} {comp : ComponentTag}
    (h : RefsOk W (.goto E K l L d comp)) : RootsOk W (envOf L d) := by
  intro i r hr
  refine h r ?_
  simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
  rcases getD_mem_or L i d with hm | hm
  · simp only [envOf] at hr; rw [List.getD_eq_getElem?_getD] at hm hr
    exact .inl (.inr ⟨_, hm, hr⟩)
  · simp only [envOf] at hr; rw [hm] at hr; exact .inr hr

/-- **The protection a framed call starts with** (proved, `enter_args`,
`crosses_witness`, `crosses_covers`, the entering step's `CrossOk`,
`Ex.grows` along the prologue, `truncate_grows`): at an entry of the
request whose term is the request's run at the slots `L` and default `d`,
from a configuration at it, every location the slot `j` reaches at the
entry's heap, for `j` a read-only position below the arity, is allocated,
of no local or internal site at the frame's start, protected or exposed and
in `E` there (`RowProtects`), and witnessed there where it is released or
outside storage. -/
theorem start_protects (r : SourceRequest σ ι) (hr : noRestB spec.lay = true) (hF : spec.flow.Facts)
    (hst : r.start < r.program.length) (hcomp : (spec.F.at spec.C).ofC r.comp = true)
    (har : spec.arityB r = true) (hro : readOnlyB r.inputs spec.readOnly spec.roPositions spec.outType = true)
    (hm : Lendable spec.flow.O ∧ LocalHeld spec.flow.H) (hinitF : spec.InitialFits r) (hinitE : spec.InitialEntry r)
    (hinit : ∀ x, spec.Initial x → spec.ProgOk r (x, bareStart (spec.core r).F (spec.core r).C x.t))
    {k : Nat} {W : WorldT k} {h : Heap} {t : Tm} {a₂ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)}
    (he : spec.EntryAt r k W h t a₂) (y : Conf) (hyt : y.t = t) (hyh : y.s.h = h) :
    ∃ L d, t = PassUnit.gotoOf r.program r.start L d r.comp ∧
      ∀ j, j < spec.arity → spec.roPos j = true → ∀ ℓ, Reaches (spec.F.at spec.C).ofC h (envOf L d j) ℓ →
        ℓ < h.length ∧ (truncate a₂.2).origin ℓ ≠ some .local ∧ (truncate a₂.2).origin ℓ ≠ some .internal ∧
        RowProtects (truncate a₂.2) ℓ ∧
        ((truncate a₂.2).Lent ℓ → ∀ st : St (spec.F.at spec.C), st.g = truncate a₂.2 → Witness spec.view.view 1 st ℓ) := by
  obtain ⟨x₀, n, x, a₁, L, d, m, hx₀, hex, hk, hdep, hda₂, hm', ht, hh, hh₁, hh₂, hcross⟩ :=
    spec.enter_args r hr hF hst hcomp har hinit he
  refine ⟨L, d, ht, fun j hj hpos ℓ hreach => ?_⟩
  -- The slot's value is the argument crossing in at the entering step.
  have hρ : RootsOk y.s.W (envOf L d) := goto_rootsOk (by have := y.ok; rw [hyt, ht] at this; exact this)
  have hlt : ℓ < h.length := by
    obtain ⟨π, hf⟩ := hreach
    rw [← hyh]; exact follows_lt (RefsOk.refsOkN (hρ j)) (by rw [hyh]; exact hf)
  rcases hcross j hj with hu | hc
  · exact absurd (hu ▸ hreach) undef_reaches
  -- The program's frame at the entering step.
  have hreachx : (spec.progFrame r).Reached x :=
    ⟨(x₀, bareStart (spec.core r).F (spec.core r).C x₀.t), n, ⟨hinitE x₀ hx₀, hx₀⟩, rfl, hex⟩
  have hcs := spec.progFrame_chkSound r hF hm hinitF
  have hsi := ClientFrame.startInv_of_entry (spec.progFrame_starts r)
  have hkind : kind (spec.core r).F (spec.core r).C none x.1 a₁.1 ≠ .outside := fun ho => by
    have := ((kind_spec (F := (spec.core r).F) (C := (spec.core r).C) (c := none) x.1 a₁.1).1 ho).2
    omega
  have hp := hcs x a₁ hreachx hk hkind
  have hreach₁ : (spec.progFrame r).Reached a₁ := ClientFrame.Reached.step hreachx hk
  have hinvx := (ClientFrame.reached_ok hcs hsi hreachx).2.1
  obtain ⟨hlen₁, hinv₁, -⟩ := ClientFrame.reached_ok hcs hsi hreach₁
  -- The history after the entering step: the call's set pushed, then the crossings.
  have hstep : stepKind (spec.core r).F (spec.core r).C none x.1.t a₁.1.t = .enter := by
    unfold stepKind
    rw [ite_eq_right (fun h => by have := h.2; omega), ite_eq_left (by omega)]
  have ha₁ : a₁.2 = Ghost.crosses spec.view.view a₁.1.s.h (spec.chk r x.1.s.h x.1.t a₁.1.s.h a₁.1.t).xs
      ((x.2.alloc x.1.s.h.length (spec.chk r x.1.s.h x.1.t a₁.1.s.h a₁.1.t).site).enter) := by
    rw [hk.2.1]
    simp only [FrameCore.next, Ghost.stepAt, hstep]
    rfl
  have hxs : (⟨.into, spec.entryTy r j, envOf L d j⟩ : Crossing spec.view.view) ∈
      (spec.chk r x.1.s.h x.1.t a₁.1.s.h a₁.1.t).xs := List.mem_append_left _ hc
  -- The origins agree along the entering step and the prologue.
  have hxlt : ℓ < x.1.s.h.length := by rw [← hh]; exact hlt
  have hsite₂ : a₂.2.site ℓ = a₁.2.site ℓ :=
    (ClientFrame.ex_sites (fr := spec.progFrame r) (Fl := spec.flow) (fun _ _ _ _ => rfl) hm').2 ℓ
      (by rw [hh₁]; exact hxlt)
  have hsite₁ : a₁.2.site ℓ = x.2.site ℓ := by
    rw [ha₁, Ghost.crosses_site]
    exact Ghost.alloc_old hxlt
  have horig : (truncate a₂.2).origin ℓ = x.2.origin ℓ := by
    simp only [Ghost.origin, truncate, hsite₂, hsite₁]
  -- The crossing's marks: no local or internal location is reached.
  have hok := hp.crossOk _ hxs ℓ (show Reaches _ a₁.1.s.h _ ℓ by rw [hh₁, ← hh]; exact hreach)
  have hmid : (midOf (spec.progFrame r).chkConf x.1 a₁.1 x.2).origin ℓ = x.2.origin ℓ := by
    simp only [midOf, Ghost.origin, Ghost.alloc, hxlt, ite_true]
    rfl
  rw [hmid] at hok
  -- The entry type is read-only.
  have hRO : spec.view.RO (spec.entryTy r j) := by
    have hjr : j < spec.roPositions.length := by
      rcases Nat.lt_or_ge j spec.roPositions.length with hjr | hjr
      · exact hjr
      · simp [FramedSpec.roPos, List.getD_eq_getElem?_getD, List.getElem?_eq_none hjr] at hpos
    simp only [FramedSpec.arityB, Bool.and_eq_true, decide_eq_true_eq] at har
    have hji : j < r.inputs.length := by omega
    simp only [readOnlyB, Bool.and_eq_true, List.all_eq_true] at hro
    have := hro.1.2 (r.inputs[j], spec.roPositions[j]) (List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩)
    have hb : spec.roPositions[j] = true := by
      simpa [FramedSpec.roPos, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjr] using hpos
    simp only [hb, Bool.not_true, Bool.false_or, List.contains_iff_mem] at this
    show spec.entryTy r j ∈ spec.readOnly
    simp only [FramedSpec.entryTy, hpos, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hji,
      Option.getD_some]
    exact this
  have hRR : ReachRO spec.view.view (spec.F.at spec.C).ofC (spec.entryTy r j) a₁.1.s.h (envOf L d j) ℓ := by
    obtain ⟨π, hf⟩ := hreach
    exact ⟨π, by rw [hh₁, ← hh]; exact hf, (spec.view.view.roPath_iff).mpr (spec.view.view.ro_at hRO)⟩
  -- The history grows along the prologue, and the start is its truncation.
  have hgrow : Grows 1 a₁.2 a₂.2 := by
    have hxa := ClientFrame.ex_xstep hcs hreach₁ (hm'.mono fun _ _ => trivial)
    have hxq := ClientFrame.ex_xstep (q := fun y => depthC (spec.core r).F (spec.core r).C none y.1.t =
      depthC (spec.core r).F (spec.core r).C none a₁.1.t) hcs hreach₁ hm'
    exact Ex.grows Nat.one_pos (fun y hy => by simp only [δ]; omega) hxq hlen₁ hinv₁ (by simp only [δ]; omega)
      (by simp only [δ]; omega)
  have hA₂ : 1 ≤ a₂.2.A.length := by
    have := hgrow.len'; exact this
  have hgrow' := hgrow.trans (truncate_grows hA₂)
  have e : (x.2.alloc x.1.s.h.length (spec.chk r x.1.s.h x.1.t a₁.1.s.h a₁.1.t).site).enter.origin ℓ =
      x.2.origin ℓ := by
    show Option.map _ ((x.2.alloc _ _).site ℓ) = Option.map _ (x.2.site ℓ)
    exact congrArg (Option.map _) (Ghost.alloc_old hxlt)
  -- A released or outside location: the crossing's witness.
  have hwit : (truncate a₂.2).Lent ℓ → ∀ st : St (spec.F.at spec.C), st.g = truncate a₂.2 →
      Witness spec.view.view 1 st ℓ := by
    intro hL st hst
    have hL₀ : (x.2.alloc x.1.s.h.length (spec.chk r x.1.s.h x.1.t a₁.1.s.h a₁.1.t).site).enter.Lent ℓ := by
      unfold Ghost.Lent at hL ⊢
      rw [horig] at hL
      rw [e]; exact hL
    have hw := crosses_witness (st := lift (spec.core r).F (spec.core r).C none a₁.1 a₁.2) (d := 1) Nat.one_pos
      (spec.chk r x.1.s.h x.1.t a₁.1.s.h a₁.1.t).xs
      (x.2.alloc x.1.s.h.length (spec.chk r x.1.s.h x.1.t a₁.1.s.h a₁.1.t).site).enter (by simp [Ghost.enter])
      ((HStep.enter (tv := spec.view.view) (h := a₁.1.s.h)
        (x.2.alloc x.1.s.h.length (spec.chk r x.1.s.h x.1.t a₁.1.s.h a₁.1.t).site)).uniform
        (fun X hX l => hinvx.1 X hX l))
      _ hxs rfl hRR hL₀ ha₁
    obtain ⟨g₀, T₀, h₀, v₀, hA, hr₀, hL', hg⟩ := hw
    exact ⟨g₀, T₀, h₀, v₀, hA, hr₀, hL', by rw [hst]; exact hg.trans hgrow'⟩
  refine ⟨hlt, by rw [horig]; exact hok.1, by rw [horig]; exact hok.2.1, ?_, hwit⟩
  -- Protected where released or outside storage, in `E` where exposed.
  cases ho : x.2.origin ℓ with
  | none =>
    have hL : (truncate a₂.2).Lent ℓ := .inr (horig.trans ho)
    exact .inr ⟨hL, (hwit hL ⟨y.s, truncate a₂.2, []⟩ rfl).prot⟩
  | some mk =>
    cases mk with
    | «local» => exact absurd ho hok.1
    | internal => exact absurd ho hok.2.1
    | released =>
      have hL : (truncate a₂.2).Lent ℓ := .inl (horig.trans ho)
      exact .inr ⟨hL, (hwit hL ⟨y.s, truncate a₂.2, []⟩ rfl).prot⟩
    | exposed =>
      have hE : a₁.2.E ℓ := by
        rw [ha₁]
        exact Ghost.crosses_covers _ _ _ hxs ℓ hRR (e.trans ho)
      exact .inl ⟨horig.trans ho, hgrow'.exposed ℓ hE⟩

end FramedSpec
end
end Verification.SourceClaimJson
