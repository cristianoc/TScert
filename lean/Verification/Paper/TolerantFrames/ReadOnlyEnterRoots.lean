import Verification.Paper.TolerantFrames.ReadOnlyMemberCert

/-! # Read-only handles: the values of a run an entering step pushes

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Certificates", `hroots`; the
restriction "No rest in a framed component").

- **A run after a step came from the step's hole** (`step_hole_inv`): at a
  reached term, where the term after a step is a context around a term
  holding a run, the term before it is the same context around a term
  stepping to that one, since the positions off the evaluation path are
  free of runs.
- **No run of `C`'s code waits as a binding's body** (`NoPend`,
  `noPend_step`, `ClientFrame.noPend_reached`): such a run is a graph
  call's rest binding, of a closure collecting a rest; where no code of
  the flow collects one (`noRestB`), every binding's run is outside code's
  (`layQ_noRest`).
- **A fitting term's hole fits at its frame's tag** (`fits_ctx`): at a
  position of outside code exactly when the tag the hole's path is read at
  is not `C`'s.
- **The values of the run an entering step pushes**
  (`ClientFrame.entry_roots`): the step is a call of a closure of `C`'s code
  from a position of outside code (`depth_push`), whose callee, receiver
  and actuals meet sets within `O`, so the run's values, theirs and those
  the callee holds (`deep_entry`), meet the closure of the capture sites
  and `O` in depth. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification HeapObservations

/-! ## A run in the term after a step came from its hole -/

/-- **A context around a term free of runs is around a term free of runs**
(proved, by induction on the context). -/
theorem _root_.Verification.HeapObservations.EvalCtx.free_hole {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ {w : Tm}, free false (K w) = true → free false w = true := by
  induction hK with
  | hole => exact fun h => h
  | frameC => intro w h; simp [free] at h
  | callArg _ _ hi _ _ ih | constructArg _ hi _ _ ih | arrArg hi _ _ ih =>
    intro w h
    simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true] at h
    first | exact ih (h.2 _ (set_mem hi)) | exact ih (h _ (set_mem hi))
  | @makeArg _ c _ _ _ hi _ _ ih =>
    intro w h
    cases c <;> simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true] at h <;>
      first | exact ih (h _ (set_mem hi)) | exact ih (h.2 _ (set_mem hi))
  | _ =>
    rename_i ih
    intro w h
    simp only [free, Bool.and_eq_true] at h
    first | exact ih h | exact ih h.1 | exact ih h.2 | exact ih h.1.1 | exact ih h.1.2 | exact ih h.2.1

/-- A context around a term holding a run holds it (proved). -/
theorem _root_.Verification.HeapObservations.EvalCtx.not_free {K : Tm → Tm} (hK : EvalCtx K) {w : Tm}
    (hf : free false w = false) : free false (K w) = false := by
  cases e : free false (K w)
  · rfl
  · simp [hK.free_hole e] at hf

/-- A context around a term holding a run is no term free of runs. -/
theorem noRun {K : Tm → Tm} (hK : EvalCtx K) {w t' : Tm} (ht : t' = K w) (hf : free false w = false)
    (h : free false t' = true) : False := by
  subst ht; simp [hK.free_hole h] at hf

/-- **The position of a list a run after a step is at** (proved): where a
list stepping at its first term that is not a value is, after the step, a
list holding a term with a run at a position, that position is the stepped
one; every other term of the list is free of runs. -/
theorem list_hole_inv {xs ys : List Tm} {i j : Nat} {a a' x : Tm} (hw : wfArgsS xs = true) (ha : xs[i]? = some a)
    (hpre : ∀ k, k < i → ∀ v, xs[k]? = some v → isVal v = true) (hna : isVal a = false) (hj : j < ys.length)
    (he : xs.set i a' = ys.set j x) (hfx : free false x = false) :
    j = i ∧ a' = x ∧ xs = ys.set j a ∧ wfS a = true := by
  obtain ⟨wa, hoth⟩ := wfArgsS_split hw ha hpre hna
  have hlen : xs.length = ys.length := by
    have := congrArg List.length he; simpa using this
  have hj' : (xs.set i a')[j]? = some x := by rw [he]; simp [hj]
  have hji : j = i := by
    by_cases hne : j = i
    · exact hne
    · rw [List.getElem?_set_ne (Ne.symm hne)] at hj'
      simp [hoth j x hj' hne] at hfx
  subst hji
  have hi : j < xs.length := hlen ▸ hj
  refine ⟨rfl, ?_, ?_, wa⟩
  · simpa [hi] using hj'
  · apply List.ext_getElem?
    intro k
    by_cases hk : k = j
    · subst hk; rw [ha]; simp [hj]
    · rw [List.getElem?_set_ne (Ne.symm hk)]
      have := congrArg (·[k]?) he
      simp only [List.getElem?_set_ne (Ne.symm hk)] at this
      exact this

theorem wfS_invokeArgs {f r : Tm} {args : List Tm} (hf : isVal f = true) (hr : isVal r = true)
    (h : wfS (.invoke f r args) = true) : wfArgsS args = true := by
  simp only [wfS, hf, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at h; exact h.2

theorem wfS_constructArgs {f : Tm} {args : List Tm} (hf : isVal f = true)
    (h : wfS (.construct f args) = true) : wfArgsS args = true := by
  simp only [wfS, hf, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at h; exact h.2

theorem wfS_makeArgs {c : CallCode} {ns : List PropKey} {xs : List Tm}
    (h : wfS (.makeAt c ns xs) = true) : wfArgsS xs = true := by
  cases c <;> simp only [wfS, Bool.and_eq_true] at h <;> first | exact h | exact h.2

theorem wfS_arrArgs {xs : List Tm} (h : wfS (.arrLit xs) = true) : wfArgsS xs = true := by
  simpa only [wfS] using h

/-- **A run in the term after a step came from its hole** (proved, by
induction on the step): at a reached term, where the term after a step is
a context around a term holding a run, the term before it is the same
context around a term stepping to that one. The positions off the
evaluation path are free of runs, so a context's hole is never one of
them. -/
theorem step_hole_inv {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    wfS t = true → HeapFree h → ∀ {K : Tm → Tm} {w : Tm}, EvalCtx K → t' = K w → isVal w = false →
      free false w = false → ∃ u, t = K u ∧ Step h u h' w := by
  have hs0 := hs
  induction hs
  all_goals intro hw hh K w hK ht hv hf
  -- Steps to a term free of runs.
  case readField hl hv' => exact (noRun hK ht hf (hh.get hv')).elim
  case indexField hk hl hv' => exact (noRun hK ht hf (hh.get hv')).elim
  case elemRead hl hv' => exact (noRun hK ht hf (hh.get hv')).elim
  case readProto h1 h2 hp => exact (noRun hK ht hf (by simp only [free]; exact hh.get hp)).elim
  case indexProto hk h1 h2 hp =>
    simp only [wfS, isVal_objAt, propertyKey_val hk, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    exact (noRun hK ht hf (by simp only [free, Bool.and_eq_true]; exact ⟨hh.get hp, hw.2⟩)).elim
  case testV => exact (noRun hK ht hf (by split <;> rfl)).elim
  case arithV hb =>
    obtain ⟨-, -, hres⟩ := binop_result hb
    exact (noRun hK ht hf (by rcases hres with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl)).elim
  case elemStr => exact (noRun hK ht hf (by simp only [codeUnitAt]; split <;> rfl)).elim
  case iteT => exact (noRun hK ht hf (by simp_all [wfS])).elim
  case iteF => exact (noRun hK ht hf (by simp_all [wfS])).elim
  case frameRet hv' =>
    simp only [wfS, Bool.and_eq_true] at hw
    exact (noRun hK ht hf (free_wfS_val hv' hw.2)).elim
  case frameRaise hr =>
    simp only [wfS, runParts, Bool.and_eq_true] at hw
    exact (noRun hK ht hf (by simp only [free]; exact raises_free hr (wfS_wf _ hw.2))).elim
  case callBound hr hargs =>
    simp only [wfS, isVal_objAt, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true, free, frees_eq,
      List.all_eq_true] at hw
    have hpa := wfArgsS_vals hw.2 hargs
    refine (noRun hK ht hf ?_).elim
    simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    grind
  case callSpread hf' hr heq hpre hre =>
    simp only [wfS, hf', hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    rw [heq] at hw
    obtain ⟨hp1, hp2⟩ := wfArgsS_mid isVal_spread hw.2 hpre
    have hvs := readElems_free hh hre
    refine (noRun hK ht hf ?_).elim
    simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    grind
  case constructSpread hf' heq hpre hre =>
    simp only [wfS, hf', Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    rw [heq] at hw
    obtain ⟨hp1, hp2⟩ := wfArgsS_mid isVal_spread hw.2 hpre
    have hvs := readElems_free hh hre
    refine (noRun hK ht hf ?_).elim
    simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    grind
  case arrSpread heq hpre hre =>
    simp only [wfS] at hw
    rw [heq] at hw
    obtain ⟨hp1, hp2⟩ := wfArgsS_mid isVal_spread hw hpre
    have hvs := readElems_free hh hre
    refine (noRun hK ht hf ?_).elim
    simp only [free, frees_eq, List.all_eq_true, List.mem_append]
    grind
  case mergeV ha hb hm =>
    refine (noRun hK ht hf ?_).elim
    simp only [free, frees_eq, List.all_eq_true]
    exact mergeParts_free hh hm
  case makeKeyV ha hk =>
    simp only [wfS, propertyKey_val hk, ha, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    exact (noRun hK ht hf (by simp [free, hw.2])).elim
  case arrAllocThrow => exact (noRun hK ht hf (by simp [free, thrownError])).elim
  case lenStrThrow => exact (noRun hK ht hf (by simp [free, thrownError])).elim
  case arithThrow => exact (noRun hK ht hf (by simp [free, thrownError])).elim
  -- A graph call: a run, or the binding of its rest's spine around one.
  case callGraph hr hargs hbind =>
    simp only [wfS, isVal_objAt, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    have hpa := wfArgsS_vals hw.2 hargs
    revert ht; unfold CallArguments.graphEntry; split
    all_goals intro ht; cases hK
    all_goals first
      | (exact ⟨_, rfl, by simp only at ht; subst ht; exact hs0⟩)
      | (exfalso; simp at ht; done)
      | skip
    simp only [Tm.letE.injEq] at ht
    refine (noRun ‹EvalCtx _› ht.1 hf ?_).elim
    simp only [free, frees_eq, List.all_eq_true]
    exact fun x hx => hpa x (List.mem_of_mem_drop hx)
  case constructGraph hargs =>
    simp only [wfS, isVal_objAt, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    have hpa := wfArgsS_vals hw.2 hargs
    revert ht; unfold CallArguments.graphEntry; split
    all_goals intro ht; cases hK
    all_goals first
      | (exact ⟨_, rfl, by simp only at ht; subst ht; exact hs0⟩)
      | (exfalso; simp at ht; done)
      | skip
    simp only [Tm.letE.injEq] at ht
    refine (noRun ‹EvalCtx _› ht.1 hf ?_).elim
    simp only [free, frees_eq, List.all_eq_true]
    exact fun x hx => hpa x (List.mem_of_mem_drop hx)
  -- A binding's step: a body free of runs, or a run not yet entered.
  case letV ha =>
    simp only [wfS, ha, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true, bodyOk, Bool.or_eq_true] at hw
    rcases hw.2 with hb | ⟨-, hb⟩
    · exact (noRun hK ht hf (subst_free hw.1 _ 0 false hb)).elim
    · rename_i b
      cases b <;> simp only [isRun, Bool.false_eq_true] at hb
      simp only [subst] at ht
      cases hK
      all_goals first
        | (exact ⟨_, rfl, by simp only at ht; subst ht; exact hs0⟩)
        | (exfalso; simp at ht; done)
  all_goals cases hK
  all_goals first
    | (exact ⟨_, rfl, by simp only at ht; subst ht; exact hs0⟩)
    | (exfalso; simp at ht; done)
    | skip
  all_goals revert ht
  all_goals simp only [Tm.invoke.injEq, Tm.construct.injEq, Tm.letE.injEq, Tm.spread.injEq, Tm.readAt.injEq,
    Tm.indexAt.injEq, Tm.writeAt.injEq, Tm.test.injEq, Tm.ite.injEq, Tm.arith.injEq, Tm.elemAt.injEq,
    Tm.setElem.injEq, Tm.lenOf.injEq, Tm.throw.injEq, Tm.merge.injEq, Tm.makeKey.injEq, Tm.frame.injEq,
    Tm.makeAt.injEq, Tm.arrLit.injEq, and_imp]
  all_goals intros
  all_goals (try subst_vars)
  all_goals clear hs0
  -- The hole at a value: no context's hole is.
  all_goals try (exfalso; have := ‹EvalCtx _›.not_val hv; simp_all; done)
  -- The hole at the stepped position: the step below it.
  all_goals try (
    rename_i ih
    have hn := not_val_of_step ‹Step _ _ _ _›
    obtain ⟨u, rfl, hu⟩ := ih ‹_› (by simp_all only [wfS, Bool.and_eq_true, ↓reduceIte, Bool.true_eq_false]) hh
      ‹EvalCtx _› rfl hv hf
    exact ⟨u, by simp, hu⟩)
  -- The hole at a position off the path: free of runs.
  all_goals try (
    exfalso
    rename_i ih
    clear ih
    have := not_val_of_step ‹Step _ _ _ _›
    have hK' := ‹EvalCtx _›.free_hole (w := w)
    simp_all [wfS]
    done)
  -- A run in a list: at the stepped position, or at a pending one.
  all_goals try (
    exfalso
    rename_i ih
    clear ih
    have := not_val_of_step ‹Step _ _ _ _›
    have hm := set_mem (x := (‹Tm → Tm›) w) ‹_ < List.length _›
    have hK' := ‹EvalCtx _›.free_hole (w := w)
    simp_all [wfS]
    done)
  -- The entry of a node: its expression, instantiated, is free of runs.
  case gotoEnter.frameC =>
    rename_i he _ hi
    simp only [wfS, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true] at hw
    have henv : ∀ i, free false (envOf _ _ i) = true := fun i => by
      rcases getD_mem_or _ i _ with h | h
      · simp only [envOf]; exact hw.1.2 _ h
      · simp only [envOf]; rw [h]; exact hw.2
    exact (noRun ‹EvalCtx _› hi hf (instantiate_free henv _ 0 false (hw.1.1 _ (List.mem_of_getElem? he)))).elim
  all_goals try (
    have hn := not_val_of_step ‹Step _ _ _ _›
    have hwl := wfS_invokeArgs (by assumption) (by assumption) hw
    obtain ⟨rfl, rfl, rfl, wa⟩ := list_hole_inv hwl ‹(_ : List Tm)[_]? = some _› (by assumption) hn
      ‹_ < List.length _› ‹List.set _ _ _ = List.set _ _ _› (‹EvalCtx _›.not_free hf)
    obtain ⟨u, hu1, hu⟩ : ∃ u, _ = (‹Tm → Tm›) u ∧ Step _ u _ w := by
      apply_assumption <;> first | assumption | rfl
    subst hu1
    exact ⟨u, by simp, hu⟩)
  all_goals try (
    have hn := not_val_of_step ‹Step _ _ _ _›
    have hwl := wfS_constructArgs (by assumption) hw
    obtain ⟨rfl, rfl, rfl, wa⟩ := list_hole_inv hwl ‹(_ : List Tm)[_]? = some _› (by assumption) hn
      ‹_ < List.length _› ‹List.set _ _ _ = List.set _ _ _› (‹EvalCtx _›.not_free hf)
    obtain ⟨u, hu1, hu⟩ : ∃ u, _ = (‹Tm → Tm›) u ∧ Step _ u _ w := by
      apply_assumption <;> first | assumption | rfl
    subst hu1
    exact ⟨u, by simp, hu⟩)
  all_goals try (
    have hn := not_val_of_step ‹Step _ _ _ _›
    have hwl := wfS_makeArgs hw
    obtain ⟨rfl, rfl, rfl, wa⟩ := list_hole_inv hwl ‹(_ : List Tm)[_]? = some _› (by assumption) hn
      ‹_ < List.length _› ‹List.set _ _ _ = List.set _ _ _› (‹EvalCtx _›.not_free hf)
    obtain ⟨u, hu1, hu⟩ : ∃ u, _ = (‹Tm → Tm›) u ∧ Step _ u _ w := by
      apply_assumption <;> first | assumption | rfl
    subst hu1
    exact ⟨u, by simp, hu⟩)
  all_goals try (
    have hn := not_val_of_step ‹Step _ _ _ _›
    have hwl := wfS_arrArgs hw
    obtain ⟨rfl, rfl, rfl, wa⟩ := list_hole_inv hwl ‹(_ : List Tm)[_]? = some _› (by assumption) hn
      ‹_ < List.length _› ‹List.set _ _ _ = List.set _ _ _› (‹EvalCtx _›.not_free hf)
    obtain ⟨u, hu1, hu⟩ : ∃ u, _ = (‹Tm → Tm›) u ∧ Step _ u _ w := by
      apply_assumption <;> first | assumption | rfl
    subst hu1
    exact ⟨u, by simp, hu⟩)

/-! ## Runs not yet entered of the component -/

/-- **A context's hole of a reached term is a reached term** (proved, by
induction on the context). -/
theorem _root_.Verification.HeapObservations.EvalCtx.wfS_hole {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ {u : Tm}, isVal u = false → wfS (K u) = true → wfS u = true := by
  induction hK with
  | hole => exact fun _ h => h
  | callArg hf hr hi hpre hK ih =>
    intro u hu h
    exact ih hu (wfArgsS_split (wfS_invokeArgs hf hr h) (List.getElem?_set_self hi) (set_prefix hpre)
      (hK.not_val hu)).1
  | constructArg hf hi hpre hK ih =>
    intro u hu h
    exact ih hu (wfArgsS_split (wfS_constructArgs hf h) (List.getElem?_set_self hi) (set_prefix hpre)
      (hK.not_val hu)).1
  | makeArg hi hpre hK ih =>
    intro u hu h
    exact ih hu (wfArgsS_split (wfS_makeArgs h) (List.getElem?_set_self hi) (set_prefix hpre) (hK.not_val hu)).1
  | arrArg hi hpre hK ih =>
    intro u hu h
    exact ih hu (wfArgsS_split (wfS_arrArgs h) (List.getElem?_set_self hi) (set_prefix hpre) (hK.not_val hu)).1
  | _ =>
    rename_i hK ih
    intro u hu h
    have hn := hK.not_val hu
    have hw := @ih u hu
    clear ih
    simp_all only [wfS, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false]

section Flow
variable {P : Package}

/-- **No code of the flow collects a rest**, decided: every layout's rest
is `false`. -/
def noRestB (lay : List Layout) : Bool := lay.all fun l => !l.2.1

/-- **A closure of `C`'s code collects no rest** (proved): its layout is
its code's (`layQ`), one of `lay`, none of which collects one. -/
theorem layQ_noRest {F : FFlow P} {lay : List Layout} (hr : noRestB lay = true) {m : Code} {c : ComponentTag}
    {ar nc s : Nat} (hq : layQ F lay m c (ar, true, nc, s) = true) : P.ofC c = false := by
  cases hc : P.ofC c
  · rfl
  · simp only [layQ, hc, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hq
    obtain ⟨_, hz, -⟩ := look_zip F.codes lay hq
    have := List.all_eq_true.mp hr _ (List.of_mem_zip hz).2
    simp at this

/-- **No run of `C`'s code waits as a binding's body**: every binding on
the evaluation path whose body is a run not yet entered runs outside
code. -/
def NoPend (P : Package) (t : Tm) : Prop :=
  ∀ (K : Tm → Tm) a E Kc l L d cc, EvalCtx K → t = K (.letE a (.goto E Kc l L d cc)) → P.ofC cc = false

/-- **A run not yet entered has no binding on its path** (proved). -/
theorem noPend_goto {E : List Tm} {Kc : List (ControlFlow.Continuation × Option ControlFlow.Target)} {l : Nat}
    {L : List Tm} {d : Tm} {c : ComponentTag} : NoPend P (.goto E Kc l L d c) := by
  intro K a E' Kc' l' L' d' cc hK h
  cases hK <;> simp at h

/-- **Every step keeps it, where no code of the flow collects a rest**
(proved, `step_hole_inv`): the binding is the one before the step, its
head stepped, or a graph call's rest binding, of a closure collecting a
rest, so of outside code (`layQ_noRest`). Every other step to a binding
yields a term free of runs. -/
theorem noPend_step {F : FFlow P} {lay : List Layout} (hr : noRestB lay = true) {h h' : Heap} {t t' : Tm}
    (hs : Step h t h' t') (hw : wfS t = true) (hh : HeapFree h) (hl : layP (layQ F lay) t = true)
    (hn : NoPend P t) : NoPend P t' := by
  intro K a E Kc l L d cc hK ht'
  have hfw : free false (.letE a (.goto E Kc l L d cc)) = false := by simp [free]
  obtain ⟨u, rfl, hu⟩ := step_hole_inv hs hw hh hK ht' rfl hfw
  have hwu := hK.wfS_hole (not_val_of_step hu) hw
  have hlu := hK.layP_hole hl
  generalize e : Tm.letE a (.goto E Kc l L d cc) = w at hu
  have hn' : ∀ a', u = .letE a' (.goto E Kc l L d cc) → P.ofC cc = false := fun a' hu' => hn K a' E Kc l L d cc hK
    (by rw [hu'])
  clear hn hs hw hl
  cases hu
  all_goals first
    | (exfalso; simp at e; done)
    | skip
  case letC => simp only [Tm.letE.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact hn' _ rfl
  case letV ha =>
    simp only [wfS, ha, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true, bodyOk, Bool.or_eq_true] at hwu
    rcases hwu.2 with hb | ⟨-, hb⟩
    · exact (noRun .hole e.symm hfw (subst_free hwu.1 _ 0 false hb)).elim
    · rename_i b
      cases b <;> simp only [isRun, Bool.false_eq_true] at hb
      simp [subst] at e
  case callGraph =>
    revert e; unfold CallArguments.graphEntry; split
    · intro e; simp at e
    · intro e
      simp only [Tm.letE.injEq, Tm.goto.injEq] at e
      obtain ⟨-, rfl, rfl, rfl, -, -, rfl⟩ := e
      simp only [layP, layPs_eq, Bool.and_eq_true] at hlu
      exact layQ_noRest hr hlu.1.1.1.1
  case constructGraph =>
    revert e; unfold CallArguments.graphEntry; split
    · intro e; simp at e
    · intro e
      simp only [Tm.letE.injEq, Tm.goto.injEq] at e
      obtain ⟨-, rfl, rfl, rfl, -, -, rfl⟩ := e
      simp only [layP, layPs_eq, Bool.and_eq_true] at hlu
      exact layQ_noRest hr hlu.1.1.1
  all_goals exfalso
  case readField hl hv' => exact noRun .hole e.symm hfw (hh.get hv')
  case indexField hk hl hv' => exact noRun .hole e.symm hfw (hh.get hv')
  case elemRead hl hv' => exact noRun .hole e.symm hfw (hh.get hv')
  case testV => exact noRun .hole e.symm hfw (by split <;> rfl)
  case arithV hb =>
    obtain ⟨-, -, hres⟩ := binop_result hb
    exact noRun .hole e.symm hfw (by rcases hres with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl)
  case elemStr => exact noRun .hole e.symm hfw (by simp only [codeUnitAt]; split <;> rfl)
  case iteT => exact noRun .hole e.symm hfw (by simp_all [wfS])
  case iteF => exact noRun .hole e.symm hfw (by simp_all [wfS])
  case frameRet hv' =>
    simp only [wfS, Bool.and_eq_true] at hwu
    exact noRun .hole e.symm hfw (free_wfS_val hv' hwu.2)

end Flow

/-! ## A fitting term's hole fits, at its frame's tag -/

section Fits
variable {P : Package} {Fl : Flow P} {V : Sites P → Val → Prop}

/-- **The path through a context, at the tag its hole's path is read
at.** -/
def PathAt (K : Tm → Tm) (c c' : ComponentTag) : Prop :=
  ∃ g S, ∀ t, isVal t = false → path Realm.empty c false (K t) = wrap g (path Realm.empty c' false t) ++ S

/-- A context rebuilding its hole's path keeps the tag the hole's path is
read at (proved, `wrap_wrap_append`). -/
theorem PathAt.keep {K K₀ : Tm → Tm} {c c₀ c' : ComponentTag} (hP : PathAt K c c')
    (h : ∃ hh : Tm → Tm, ∀ t, isVal t = false → path Realm.empty c₀ false (K₀ t) = wrap hh (path Realm.empty c false (K t))) :
    PathAt K₀ c₀ c' := by
  obtain ⟨g, S, hP⟩ := hP
  obtain ⟨hh, hK⟩ := h
  obtain ⟨g', S', hw⟩ := wrap_wrap_append hh g S
  exact ⟨g', S', fun t ht => by rw [hK t ht, hP t ht, hw]⟩

/-- **A fitting term's hole fits, at a position of the code its frame
runs** (proved, by induction on the context): where the whole term fits at
a position of outside code exactly when its top segment's tag is not
`C`'s, the context's hole fits at the same variables' sites, at a position
of outside code exactly when the tag the hole's path is read at is not
`C`'s. -/
theorem fits_ctx {K : Tm → Tm} (hK : EvalCtx K) : ∀ c : ComponentTag, ∃ c', PathAt K c c' ∧
    ∀ {Γ a S u}, isVal u = false → Fits Fl V Γ a (!P.ofC c) S (K u) →
      ∃ a' S', Fits Fl V Γ a' (!P.ofC c') S' u := by
  induction hK with
  | hole =>
    refine fun c => ⟨c, ⟨id, [], fun t _ => ?_⟩, fun _ h => ⟨_, _, h⟩⟩
    have e : (fun p : ComponentTag × Tm => (p.1, id p.2)) = fun p => p := funext fun _ => rfl
    simp only [wrap, List.append_nil, e, mapLast_self]
  | frameC E Kc L d k x comp hK ih =>
    intro c
    obtain ⟨c', ⟨g, S, hP⟩, hF⟩ := ih comp
    obtain ⟨g', S', hw⟩ := wrap_wrap_append (fun s => .frame E Kc s L d k x comp) g S
    refine ⟨c', ⟨g', S' ++ [(c, hole)], fun t ht => by
      simp only [path, Realm.own_empty, Realm.native_empty]; rw [hP t ht, hw, List.append_assoc]⟩,
      fun hu hf => ?_⟩
    cases hf with
    | val hv => simp [isVal] at hv
    | frameC _ _ _ hc _ _ _ _ _ ht _ _ =>
      rw [show false = !P.ofC comp by simp [hc]] at ht; exact hF hu ht
    | frameOut hc _ _ ht _ _ =>
      rw [show true = !P.ofC comp by simp [hc]] at ht; exact hF hu ht
  | @callArg K₀ f r args i hf hr hi hpre hK ih =>
    intro c
    obtain ⟨c', hP, hF⟩ := ih c
    refine ⟨c', hP.keep ⟨fun s => .invoke f r (args.set i s), fun t ht => ?_⟩, fun hu hfit => ?_⟩
    · simp only [path, hf, hr, Bool.true_eq_false, ite_false]
      rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre (hK.not_val ht)]
    cases hfit with
    | val hv => simp [isVal] at hv
    | invoke _ _ ha => exact hF hu (ha _ (set_mem hi))
    | invokeC _ _ _ _ _ _ _ _ _ _ ha => exact hF hu (ha i _ (List.getElem?_set_self hi))
  | @constructArg K₀ f args i hf hi hpre hK ih =>
    intro c
    obtain ⟨c', hP, hF⟩ := ih c
    refine ⟨c', hP.keep ⟨fun s => .construct f (args.set i s), fun t ht => ?_⟩, fun hu hfit => ?_⟩
    · simp only [path, hf, Bool.true_eq_false, ite_false]
      rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre (hK.not_val ht)]
    cases hfit with
    | val hv => simp [isVal] at hv
    | construct _ ha => exact hF hu (ha _ (set_mem hi))
  | @makeArg K₀ cc ns inits i hi hpre hK ih =>
    intro c
    obtain ⟨c', hP, hF⟩ := ih c
    refine ⟨c', hP.keep ⟨fun s => .makeAt cc ns (inits.set i s), fun t ht => ?_⟩, fun hu hfit => ?_⟩
    · simp only [path]
      rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre (hK.not_val ht)]
    cases hfit with
    | val hv => simp [isVal] at hv
    | makeAbsent _ _ ha => exact hF hu (ha _ (set_mem hi))
    | makeView _ _ ha => exact hF hu (ha _ (set_mem hi))
    | makeBound _ _ ha => exact hF hu (ha _ (set_mem hi))
    | makeGraphC _ _ _ ha => exact hF hu (ha _ (set_mem hi))
    | makeGraphOut _ _ ha => exact hF hu (ha _ (set_mem hi))
  | @arrArg K₀ inits i hi hpre hK ih =>
    intro c
    obtain ⟨c', hP, hF⟩ := ih c
    refine ⟨c', hP.keep ⟨fun s => .arrLit (inits.set i s), fun t ht => ?_⟩, fun hu hfit => ?_⟩
    · simp only [path]
      rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre (hK.not_val ht)]
    cases hfit with
    | val hv => simp [isVal] at hv
    | arrLit _ _ ha => exact hF hu (ha _ (set_mem hi))
  | _ =>
    rename_i hK ih
    intro c
    obtain ⟨c', hP, hF⟩ := ih c
    refine ⟨c', hP.keep ⟨?_, fun t ht => ?_⟩, fun hu hfit => ?_⟩
    rotate_left
    · simp only [path, hK.not_val ht, *, ite_true, ite_false, Bool.true_eq_false]
      rfl
    have hn := hK.not_val hu
    cases hfit <;> first
      | exact hF hu (by assumption)
      | (exfalso; simp_all [isVal]; done)
      | (exfalso; have := (‹FnIs _ _ _›).val; simp_all; done)

end Fits

/-! ## The values of a run an entering step pushes -/

/-- **A step pushing a run onto a call of outside code enters `C`**
(proved): around a context whose hole's path is read at `c'`, a step from
a term with one path entry to a run with one more raises the calls of `C`
active by one exactly when the run is `C`'s and `c'` is not. -/
theorem depth_push {F : Family} {C : Nat} {K : Tm → Tm} {c' cc : ComponentTag} (hrn : ∀ t, F.realm.tags t = false)
    (hP : PathAt K none c')
    {u w : Tm} (hu : isVal u = false) (hw : isVal w = false) (hpu : (path Realm.empty c' false u).map Prod.fst = [c'])
    (hpw : (path Realm.empty c' false w).map Prod.fst = [cc, c'])
    (hd : depthC F C none (K w) = depthC F C none (K u) + 1) : F.ofC C cc = true ∧ F.ofC C c' = false := by
  obtain ⟨g, S, hP⟩ := hP
  have e : ∀ t, isVal t = false → depthC F C none (K t) =
      blocks (((path Realm.empty c' false t).map Prod.fst ++ S.map Prod.fst).map (F.ofC C)) := by
    intro t ht
    rw [depthC_noRealm hrn, hP t ht, List.map_append, List.map_append,
      show (fun p : ComponentTag × Tm => F.ofC C p.1) = F.ofC C ∘ Prod.fst from rfl, ← List.map_map,
      ← List.map_map, wrap_fst]
  rw [e w hw, e u hu, hpw, hpu] at hd
  simp only [List.cons_append, List.map_cons, blocks_cons_cons] at hd
  revert hd
  cases F.ofC C cc <;> cases F.ofC C c' <;> simp

/-- **The values of a graph call's run meet a set in depth where its
callee's, receiver's and actuals' do** (proved, `DeepIn.held`): its code's
values and captures are values its callee holds. -/
theorem deep_entry {α : Type} {site : Nat → α} {T : List α} {fs : List (PropKey × Nat)} {n : Nat} {E : List Tm}
    {Kc : List (ControlFlow.Continuation × Option ControlFlow.Target)} {s : Nat} {caps : List Tm} {k : Invoke}
    {cc : ComponentTag} {oid : Nat} {r : Tm} {args : List Tm}
    (hdf : DeepIn site T (.objAt fs (.graph n E Kc s caps k false cc) oid)) (hdr : DeepIn site T r)
    (hrv : isVal r = true) (hda : ∀ x ∈ args, DeepIn site T x) (hav : ∀ x ∈ args, isVal x = true) :
    ∀ x ∈ vals allC Realm.empty true false (.goto E Kc s (r :: CallArguments.parameters n args ++
      (caps ++ [.objAt fs (.graph n E Kc s caps k false cc) oid])) .nul cc), DeepIn site T x := by
  have hf : ∀ x, x ∈ vals allC Realm.empty true false (.objAt fs (.graph n E Kc s caps k false cc) oid) → DeepIn site T x :=
    fun x hx => hdf.held rfl hx
  intro x hx
  simp only [vals, Realm.flag_empty, allC, Bool.not_false, ↓reduceIte, valsArgs_eq, List.mem_append, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ⟨e, he, hx⟩ | ⟨y, hy, hx⟩
  · exact hf x (by simp only [vals, allC, Bool.false_eq_true, ↓reduceIte, valsArgs_eq, List.mem_cons,
      List.mem_append, List.mem_flatMap]; exact .inr (.inl ⟨e, he, hx⟩))
  · rcases hy with (rfl | hy) | hy | rfl
    · exact hdr.held hrv hx
    · rcases Kinds.parameters_mem hy with hy | rfl
      · exact (hda y hy).held (hav y hy) hx
      · simp [vals] at hx
    · exact hf x (by simp only [vals, allC, Bool.false_eq_true, ↓reduceIte, valsArgs_eq, List.mem_cons,
        List.mem_append, List.mem_flatMap]; exact .inr (.inr ⟨y, hy, hx⟩))
    · exact hf x hx

namespace ClientFrame
variable {τ : Type} {fr : ClientFrame τ}

/-- **No run of `C`'s code waits as a binding's body at a reached state**
(proved, `noPend_step` at each step): where no code of the flow collects a
rest, from the frame's starts meeting it, reached terms and layout
provenance. -/
theorem noPend_reached {F : FFlow (fr.F.at fr.C)} {lay : List Layout} (hr : noRestB lay = true)
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → wfS a.1.t = true)
    (hly : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → layP (layQ F lay) a.1.t = true ∧ HeapLay (layQ F lay) a.1.s.h)
    (hnp : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → NoPend (fr.F.at fr.C) a.1.t)
    {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b) : NoPend (fr.F.at fr.C) b.1.t := by
  obtain ⟨a, n, hc, hs, hex⟩ := hb
  refine (hex.carry (r := fun x : Conf × Ghost (fr.F.at fr.C) => fr.Entry x.1.s.h x.1.t ∧ wfS x.1.t = true ∧
    (layP (layQ F lay) x.1.t = true ∧ HeapLay (layQ F lay) x.1.s.h) ∧ NoPend (fr.F.at fr.C) x.1.t) ?_
    ⟨hc.1, hst a hc hs, hly a hc hs, hnp a hc hs⟩).2.2.2
  intro x y _ hxy hx
  exact ⟨Entry.step fr hx.1 hxy.1.step, (step_wfS hxy.1.step hx.2.1 hx.1.2.1.2).1,
    step_layP hxy.1.step hx.2.2.1.1 hx.2.2.1.2,
    noPend_step hr hxy.1.step hx.2.1 hx.1.2.1.2 hx.2.2.1.1 hx.2.2.2⟩

theorem layP_invoke {q : Code → ComponentTag → Layout → Bool} {f r : Tm} {args : List Tm} :
    layP q (.invoke f r args) = (layP q f && layP q r && layPs q args) := by
  simp only [layP]

theorem layP_construct {q : Code → ComponentTag → Layout → Bool} {f : Tm} {args : List Tm} :
    layP q (.construct f args) = (layP q f && layPs q args) := by
  simp only [layP]

/-- **The values of the run an entering step pushes meet the closure of the
capture sites and `O` in depth** (proved; the draft's `hroots`): where no
code of the flow collects a rest. The step pushes the run at its hole
(`step_hole_inv`), from a call of graph code, a binding's body or a frame
of the run's code; the binding's body is outside code (`noPend_reached`),
and a frame's step keeps the calls of `C` active (`depthC_ctx`), so the
step is a call of a closure of `C` from a position of outside code
(`depth_push`, `fits_ctx`), whose callee, receiver and actuals meet sets
within `O` (`Fits.invoke`), hence the closure in depth
(`deepIn_of_checks`), and the run's values are theirs and those its callee
holds (`deep_entry`). -/
theorem entry_roots [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    [LawfulHashable (Option (fr.F.at fr.C).Site)] {F : FFlow (fr.F.at fr.C)} {lay : List Layout}
    (hrn : ∀ t, fr.F.realm.tags t = false)
    (hFa : F.flow.Facts) (hS : fr.FlowSites F.flow) (hE : fr.EntryFits F.flow)
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → wfS a.1.t = true)
    (hly : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → layP (layQ F lay) a.1.t = true ∧ HeapLay (layQ F lay) a.1.s.h)
    (hnp : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → NoPend (fr.F.at fr.C) a.1.t)
    (hT : capClosedB F (tokenCaps F lay) (captureSites F lay ++ F.O)
      (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O)) = true)
    (htok : tokensSomeB F = true) (hlow : codesLoweredB F = true) (hr : noRestB lay = true) :
    ∀ (a a₁ : Conf × Ghost (fr.F.at fr.C)), fr.Reached a → XStep fr.F fr.C none fr.Θ fr.chkConf a a₁ →
      δ fr.F fr.C none a₁ = δ fr.F fr.C none a + 1 → ∀ (K : Tm → Tm) E Kc l L d cc, EvalCtx K →
      a₁.1.t = K (.goto E Kc l L d cc) → ∀ x ∈ vals allC Realm.empty true false (.goto E Kc l L d cc),
        DeepIn a₁.2.site (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O)) x := by
  intro a a₁ hA hx hd K E Kc l L d cc hK ht₁
  have hw := reached_wfS hst hA
  have hh := (Reached.entry hA).2.1.2
  have hstep := hx.1.step
  obtain ⟨u, hat, hu⟩ := step_hole_inv hstep hw hh hK ht₁ rfl (by simp [free])
  have hnu := not_val_of_step hu
  have hnp' := noPend_reached hr hst hly hnp hA
  have hlu := hK.layP_hole (by rw [← hat]; exact (lay_reached hly hA).1)
  have hwu := hK.wfS_hole hnu (by rw [← hat]; exact hw)
  have hfa := fitsAt_reached hFa hS hE hA
  obtain ⟨c', hP, hF⟩ := fits_ctx (Fl := F.flow) (V := VJ F.flow a.2 a.1.s.h.length) hK none
  have hO : (fr.F.at fr.C).ofC none = false := by simp [Family.at, Family.ofC, Family.Runs]
  obtain ⟨a', S', hfit⟩ := hF hnu (by rw [hO, ← hat]; exact hfa.1)
  have hdepth : depthC fr.F fr.C none (K (.goto E Kc l L d cc)) = depthC fr.F fr.C none (K u) + 1 := by
    rw [← ht₁, ← hat]; simpa only [δ] using hd
  have hheap : a₁.1.s.h = a.1.s.h :=
    enter_keeps_heap (F := fr.F) (C := fr.C) (c := none) hstep hw hh (by simp only [δ] at hd; omega)
  have hsite : ∀ l, l < a.1.s.h.length → a₁.2.site l = a.2.site l := by
    intro l hl
    rw [next_site hS (kstep_of_xstep hx) l (by rw [hheap]; exact hl)]
    exact (Ghost.alloc_old hl)
  have hOT : Sub F.flow.O (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O)) :=
    fun s hs => (capClosedB_sound hT).1 s (List.mem_append_right _ hs)
  have hdeep : ∀ v S₁, VJ F.flow a.2 a.1.s.h.length S₁ v → Sub S₁ F.flow.O → layP (layQ F lay) v = true →
      DeepIn a₁.2.site (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O)) v :=
    fun v S₁ hv hS₁ hl => deepIn_of_checks hT htok hlow (hv.congr hsite) (Sub.trans hS₁ hOT) hl
  have hgv : isVal (Tm.goto E Kc l L d cc) = false := rfl
  have hpg : ∀ c, (path Realm.empty c false (Tm.goto E Kc l L d cc)).map Prod.fst = [cc, c] := fun c => by simp [path]
  generalize eg : Tm.goto E Kc l L d cc = gt at hu
  generalize eh₀ : a.1.s.h = h₀ at hu
  generalize eh₁ : a₁.1.s.h = h₁ at hu
  cases hu
  all_goals first
    | (exfalso; cases eg; done)
    | skip
  -- A call of graph code from a position of outside code.
  case callGraph hr' hargs hbind =>
    revert eg; unfold CallArguments.graphEntry; split
    · intro eg
      simp only [Tm.goto.injEq] at eg
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := eg
      obtain ⟨-, hc'⟩ := depth_push hrn hP hnu hgv (by simp [path, hr', pathArgs_vals _ hargs]) (hpg c') hdepth
      rw [show (fr.F.at fr.C).ofC c' = fr.F.ofC fr.C c' from rfl, hc'] at hfit
      rw [layP_invoke] at hlu
      simp only [layPs_eq, Bool.and_eq_true, List.all_eq_true] at hlu
      cases hfit with
      | val hv => simp [isVal] at hv
      | invoke hff hfr hfa' _ _ _ hSf _ =>
        refine deep_entry (hdeep _ _ (hff.value rfl) hSf hlu.1.1) (hdeep _ _ (hfr.value hr') (Sub.refl _) hlu.1.2)
          hr' (fun x hx => hdeep _ _ ((hfa' x hx).value (hargs x hx)) (Sub.refl _) (hlu.2 x hx)) hargs
      | invokeC _ _ _ _ _ ho => simp at ho
    · intro eg; simp at eg
  case constructGraph hargs =>
    revert eg; unfold CallArguments.graphEntry; split
    · intro eg
      simp only [Tm.goto.injEq] at eg
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := eg
      obtain ⟨-, hc'⟩ := depth_push hrn hP hnu hgv (by simp [path, pathArgs_vals _ hargs]) (hpg c') hdepth
      rw [show (fr.F.at fr.C).ofC c' = fr.F.ofC fr.C c' from rfl, hc'] at hfit
      rw [layP_construct] at hlu
      simp only [layPs_eq, Bool.and_eq_true, List.all_eq_true] at hlu
      cases hfit with
      | val hv => simp [isVal] at hv
      | construct hff hfa' _ _ _ hSf _ =>
        exact deep_entry (hdeep _ _ (hff.value rfl) hSf hlu.1)
          (hdeep .undef [] (VJ.prim rfl) (fun _ h => by cases h) rfl) rfl
          (fun x hx => hdeep _ _ ((hfa' x hx).value (hargs x hx)) (Sub.refl _) (hlu.2 x hx)) hargs
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
      have h1 := hnp' K _ _ _ _ _ _ cc hK hat
      obtain ⟨h2, -⟩ := depth_push hrn hP hnu hgv (by simp [path, ha]) (hpg c') hdepth
      simp_all [Family.at]
  -- A frame's step to its code's next node: the calls of `C` active kept.
  all_goals try (
    exfalso
    simp only [Tm.goto.injEq] at eg
    obtain ⟨-, -, -, -, -, rfl⟩ := eg
    have := depthC_ctx (F := fr.F) (C := fr.C) hK none hnu hgv fun c => by
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

end ClientFrame

end Verification.TolerantFrames.ReadOnly
