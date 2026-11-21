import Verification.Paper.TolerantFrames.ReadOnlyRuns

/-! # Read-only handles: runs not yet entered sit only as a binding's body

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Certificates"). A step of outside
code that evaluates a write just before a pending run enters a call while
it writes (`enterWrite_step`); the reached states of a program have no such
run.

- **A reached term** (`wfS`): along its evaluation path, each position's
  other subterms are free of runs, but the body of a binding, which may be
  a run not yet entered (`isRun`) whose head is a value, a throw of a
  value, or a literal of values (`restHead`): the rest binding of
  `graphEntry`. It is well formed (`wfS_wf`); a term free of runs meets it
  (`wfS_of_free`).
- **Every step keeps it, and a step that changes the heap keeps the
  path's frames** (`step_wfS`): it changes the innermost entry of the path
  alone, at its tag, so it enters no call (`enter_keeps_heap`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification

/-- **A run not yet entered** whose parts are free of runs. -/
def isRun : Tm → Bool
  | .goto E _ _ L d _ => runParts E L d
  | _ => false

/-- **The head of a binding whose body may be a run**: a value, a throw of
a value, or a literal of values, as `graphEntry`'s rest binding has. -/
def restHead : Tm → Bool
  | .arrLit xs => xs.all isVal
  | .throw a => isVal a
  | t => isVal t

/-- **The body a binding with the head `a` may have**: free of runs, or a
run not yet entered when the head is a rest's. -/
def bodyOk (a b : Tm) : Bool := free false b || (free false a && restHead a && isRun b)

mutual
/-- **A reached term**: along its evaluation path every other subterm of a
position is free of runs, but a binding's body (`bodyOk`); a `goto` and a
`frame` have their parts free of runs, and a frame's running term is again
a reached term. -/
def wfS : Tm → Bool
  | .invoke f r args =>
    if isVal f = false then wfS f && free false r && frees false args
    else if isVal r = false then free false f && wfS r && frees false args
    else free false f && free false r && wfArgsS args
  | .construct f args =>
    if isVal f = false then wfS f && frees false args else free false f && wfArgsS args
  | .letE a b => if isVal a = false then wfS a && bodyOk a b else free false a && bodyOk a b
  | .makeAt (.bound t r pre) _ xs => free false t && free false r && frees false pre && wfArgsS xs
  | .makeAt (.graph _ E _ _ caps _ _ _) _ xs => frees false E && frees false caps && wfArgsS xs
  | .makeAt .absent _ xs => wfArgsS xs
  | .makeAt (.view _ _ _) _ xs => wfArgsS xs
  | .readAt _ a => if isVal a = false then wfS a else free false a
  | .indexAt a b =>
    if isVal a = false then wfS a && free false b
    else if isVal b = false then free false a && wfS b else free false a && free false b
  | .writeAt _ a b =>
    if isVal a = false then wfS a && free false b
    else if isVal b = false then free false a && wfS b else free false a && free false b
  | .test _ a => if isVal a = false then wfS a else free false a
  | .ite x a b => if isVal x = false then wfS x && free false a && free false b
    else free false x && free false a && free false b
  | .arith _ a b =>
    if isVal a = false then wfS a && free false b
    else if isVal b = false then free false a && wfS b else free false a && free false b
  | .arrLit xs => wfArgsS xs
  | .elemAt a b =>
    if isVal a = false then wfS a && free false b
    else if isVal b = false then free false a && wfS b else free false a && free false b
  | .setElem a b x =>
    if isVal a = false then wfS a && free false b && free false x
    else if isVal b = false then free false a && wfS b && free false x
    else if isVal x = false then free false a && free false b && wfS x
    else free false a && free false b && free false x
  | .lenOf a => if isVal a = false then wfS a else free false a
  | .spread a => if isVal a = false then wfS a else free false a
  | .throw a => if isVal a = false then wfS a else free false a
  | .merge _ a b =>
    if isVal a = false then wfS a && free false b
    else if isVal b = false then free false a && wfS b else free false a && free false b
  | .makeKey a b =>
    if isVal a = false then wfS a && free false b
    else if isVal b = false then free false a && wfS b else free false a && free false b
  | .goto E _ _ L d _ => runParts E L d
  | .frame E _ t L d _ _ _ => runParts E L d && wfS t
  | t => free false t
termination_by structural t => t

def wfArgsS : List Tm → Bool
  | [] => true
  | a :: as => if isVal a = false then wfS a && frees false as else free false a && wfArgsS as
termination_by structural xs => xs
end

/-! ## Basic facts -/

theorem wfS_val {v : Tm} (hv : isVal v = true) : wfS v = free false v := by
  cases v <;> simp_all [isVal, wfS]

theorem wfArgsS_of {xs : List Tm} (ih : ∀ a ∈ xs, free false a = true → wfS a = true)
    (h : ∀ a ∈ xs, free false a = true) : wfArgsS xs = true := by
  induction xs with
  | nil => rfl
  | cons a as iha =>
    simp only [wfArgsS]
    split
    · simp only [Bool.and_eq_true, frees_eq, List.all_eq_true]
      exact ⟨ih a List.mem_cons_self (h a List.mem_cons_self), fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
    · simp only [Bool.and_eq_true]
      exact ⟨h a List.mem_cons_self, iha (fun x hx => ih x (List.mem_cons_of_mem _ hx))
        (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

/-- **A term free of runs is a reached term** (proved). -/
theorem wfS_of_free : ∀ (t : Tm), free false t = true → wfS t = true := by
  intro t
  induction t using Tm.induct
  all_goals intro h
  all_goals first
    | (simp only [free, Bool.false_eq_true, Bool.false_and] at h; done)
    | skip
  all_goals simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true] at h
  all_goals simp only [wfS, bodyOk, frees_eq, Bool.and_eq_true, List.all_eq_true]
  all_goals (repeat' split) <;> (try simp only [Bool.and_eq_true, Bool.or_eq_true]) <;>
    first
      | rfl
      | (simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true]; exact h)
      | (exact wfArgsS_of (by grind) (by grind))
      | (exact ⟨by grind, wfArgsS_of (by grind) (by grind)⟩)
      | grind

theorem isRun_free {b : Tm} (h : isRun b = true) : free true b = true := by
  cases b <;> simp_all [isRun, free, runParts]

theorem bodyOk_free {a b : Tm} (h : bodyOk a b = true) : free true b = true := by
  simp only [bodyOk, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨-, h⟩
  · exact free_mono _ h
  · exact isRun_free h

theorem wfArgsS_wf {xs : List Tm} (ih : ∀ a ∈ xs, wfS a = true → wf a = true) (h : wfArgsS xs = true) :
    wfArgs xs = true := by
  induction xs with
  | nil => rfl
  | cons a as iha =>
    simp only [wfArgsS] at h
    simp only [wfArgs]
    split
    · rename_i hv; rw [ite_eq_left hv] at h
      simp only [Bool.and_eq_true, frees_eq, List.all_eq_true] at h ⊢
      exact ⟨ih a List.mem_cons_self h.1, fun x hx => free_mono _ (h.2 x hx)⟩
    · rename_i hv; rw [ite_eq_right hv] at h
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨free_mono _ h.1, iha (fun x hx => ih x (List.mem_cons_of_mem _ hx)) h.2⟩

/-- **A reached term is well formed** (proved). -/
theorem wfS_wf : ∀ (t : Tm), wfS t = true → wf t = true := by
  intro t
  induction t using Tm.induct
  all_goals intro h
  all_goals simp only [wfS, runParts, frees_eq, Bool.and_eq_true, List.all_eq_true] at h
  all_goals simp only [wf, runParts, frees_eq, Bool.and_eq_true, List.all_eq_true]
  all_goals (repeat' split) <;> (repeat' split at h) <;> (try simp only [Bool.and_eq_true] at h ⊢) <;>
    first
      | rfl
      | (exact pf_wf _ (free_mono _ h))
      | (exact wfArgsS_wf (by grind) h)
      | (exact ⟨h.1, wfArgsS_wf (by grind) h.2⟩)
      | grind [free_mono, bodyOk_free, pf_wf, wfArgsS_wf]

/-! ## Lists and paths -/

theorem wfArgsS_split : ∀ {xs : List Tm} {i : Nat} {a : Tm}, wfArgsS xs = true → xs[i]? = some a →
    (∀ j, j < i → ∀ w, xs[j]? = some w → isVal w = true) → isVal a = false →
      wfS a = true ∧ ∀ j x, xs[j]? = some x → j ≠ i → free false x = true
  | [], _, _, _, h, _, _ => by simp at h
  | b :: bs, 0, a, hw, h, _, ha => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [wfArgsS, ha, ite_true, Bool.and_eq_true, frees_eq, List.all_eq_true] at hw
    refine ⟨hw.1, fun j x hx hj => ?_⟩
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact hw.2 x (List.mem_of_getElem? (by simpa using hx))
  | b :: bs, i + 1, a, hw, h, hpre, ha => by
    have hb : isVal b = true := hpre 0 (Nat.succ_pos _) b rfl
    simp only [wfArgsS, hb, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    obtain ⟨hwa, hrest⟩ := wfArgsS_split hw.2 (by simpa using h)
      (fun j hj w hw' => hpre (j + 1) (by omega) w (by simpa using hw')) ha
    refine ⟨hwa, fun j x hx hj => ?_⟩
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx; exact hw.1
    | succ j => exact hrest j x (by simpa using hx) (by omega)

theorem wfArgsS_mk : ∀ {xs : List Tm} {i : Nat} {a : Tm}, xs[i]? = some a →
    (∀ j, j < i → ∀ w, xs[j]? = some w → isVal w = true) → wfS a = true →
    (∀ j x, xs[j]? = some x → j ≠ i → free false x = true) → wfArgsS xs = true
  | [], _, _, h, _, _, _ => by simp at h
  | b :: bs, 0, a, h, _, hwa, hrest => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have hbs : ∀ x ∈ bs, free false x = true := fun x hx => by
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      exact hrest (j + 1) x (by simpa using hj) (by omega)
    simp only [wfArgsS]
    split
    · simp only [Bool.and_eq_true, frees_eq, List.all_eq_true]; exact ⟨hwa, hbs⟩
    · rename_i hv
      simp only [Bool.not_eq_false] at hv
      simp only [Bool.and_eq_true]
      exact ⟨by rw [← wfS_val hv]; exact hwa, wfArgsS_of (fun x _ hx => wfS_of_free x hx) hbs⟩
  | b :: bs, i + 1, a, h, hpre, hwa, hrest => by
    have hb : isVal b = true := hpre 0 (Nat.succ_pos _) b rfl
    simp only [wfArgsS, hb, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true]
    exact ⟨hrest 0 b rfl (by omega), wfArgsS_mk (by simpa using h)
      (fun j hj w hw' => hpre (j + 1) (by omega) w (by simpa using hw')) hwa
      (fun j x hx hj => hrest (j + 1) x (by simpa using hx) (by omega))⟩

theorem wfArgsS_vals {xs : List Tm} (hw : wfArgsS xs = true) (hv : ∀ x ∈ xs, isVal x = true) :
    ∀ x ∈ xs, free false x = true := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := hv a List.mem_cons_self
    simp only [wfArgsS, ha, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hw.1
    · exact ih hw.2 (fun y hy => hv y (List.mem_cons_of_mem _ hy)) x hx

theorem wfArgsS_mid {a : Tm} {post : List Tm} (ha : isVal a = false) :
    ∀ {pre : List Tm}, wfArgsS (pre ++ a :: post) = true → (∀ v ∈ pre, isVal v = true) →
      (∀ x ∈ pre, free false x = true) ∧ ∀ x ∈ post, free false x = true
  | [], hw, _ => by
    simp only [List.nil_append, wfArgsS, ha, ↓reduceIte, Bool.and_eq_true, frees_eq, List.all_eq_true] at hw
    exact ⟨by simp, hw.2⟩
  | b :: bs, hw, hpre => by
    have hb := hpre b List.mem_cons_self
    simp only [List.cons_append, wfArgsS, hb, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    obtain ⟨h2, h3⟩ := wfArgsS_mid ha hw.2 (fun v hv => hpre v (List.mem_cons_of_mem _ hv))
    refine ⟨fun x hx => ?_, h3⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hw.1
    · exact h2 x hx

/-- **A step keeping the path's frames**: it changes the innermost entry
alone, at its tag. -/
def Stay (P P' : List (ComponentTag × Tm)) : Prop :=
  ∃ F F' rest, P = F :: rest ∧ P' = F' :: rest ∧ F'.1 = F.1

theorem Stay.wrap {P P' : List (ComponentTag × Tm)} (g : Tm → Tm) (h : Stay P P') :
    Stay (ReadOnly.wrap g P) (ReadOnly.wrap g P') := by
  obtain ⟨F, F', rest, rfl, rfl, ht⟩ := h
  by_cases hr : rest = []
  · subst hr
    exact ⟨(F.1, g F.2), (F'.1, g F'.2), [], rfl, rfl, ht⟩
  · exact ⟨F, F', ReadOnly.wrap g rest, by simp only [ReadOnly.wrap, mapLast_cons hr],
      by simp only [ReadOnly.wrap, mapLast_cons hr], ht⟩

theorem Stay.append {P P' : List (ComponentTag × Tm)} (Q : List (ComponentTag × Tm)) (h : Stay P P') :
    Stay (P ++ Q) (P' ++ Q) := by
  obtain ⟨F, F', rest, rfl, rfl, ht⟩ := h
  exact ⟨F, F', rest ++ Q, rfl, rfl, ht⟩

/-- Two terms whose paths are their top segments. -/
theorem Stay.base {c : ComponentTag} {t t' : Tm} (h : (path rl c nk t).length = 1) (h' : (path rl c nk t').length = 1) :
    Stay (path rl c nk t) (path rl c nk t') := by
  obtain ⟨i, s, hl⟩ := path_last t c nk
  obtain ⟨i', s', hl'⟩ := path_last t' c nk
  have hi : i = [] := by have := congrArg List.length hl; rw [h] at this; simpa using this
  have hi' : i' = [] := by have := congrArg List.length hl'; rw [h'] at this; simpa using this
  subst hi hi'
  exact ⟨(c, s), (c, s'), [], hl, hl', rfl⟩

/-- **A step inside an evaluation context that is no run**. -/
theorem Stay.ctx {c : ComponentTag} {a a' A A' : Tm} {g : Tm → Tm}
    (hrel : Stay (path rl c nk a) (path rl c nk a')) (hA : path rl c nk A = ReadOnly.wrap g (path rl c nk a))
    (hA' : isVal a' = false → path rl c nk A' = ReadOnly.wrap g (path rl c nk a'))
    (hv : isVal a' = true → (path rl c nk A').length = 1) : Stay (path rl c nk A) (path rl c nk A') := by
  cases e : isVal a'
  · rw [hA, hA' e]; exact hrel.wrap g
  · rw [path_val e] at hrel
    obtain ⟨F, F', rest, hP, hP', ht⟩ := hrel
    obtain ⟨rfl, rfl⟩ : F' = (c, a') ∧ rest = [] := by simp at hP'; exact ⟨hP'.1.symm, hP'.2⟩
    refine Stay.base ?_ (hv e)
    rw [hA, hP]; rfl

/-- The head of a rest's binding steps to one (proved). -/
theorem restHead_step {h h' : Heap} {a a' : Tm} (hs : Step h a h' a') (hr : restHead a = true) :
    restHead a' = true ∧ free false a' = true := by
  cases hs with
  | arrAlloc => exact ⟨rfl, rfl⟩
  | arrAllocThrow => exact ⟨rfl, rfl⟩
  | arrArg ha _ hs' =>
    simp only [restHead, List.all_eq_true] at hr
    exact absurd hs' (value_no_step (hr _ (List.mem_of_getElem? ha)))
  | arrSpread heq =>
    simp only [restHead, List.all_eq_true] at hr
    subst heq
    have := hr _ (List.mem_append_right _ List.mem_cons_self)
    simp at this
  | throwC hs' => simp only [restHead] at hr; exact absurd hs' (value_no_step hr)
  | _ => simp_all [restHead, isVal]

/-- **A graph call yields a reached term** (proved): a run not yet entered,
or the binding of its rest's spine around it. -/
theorem graphEntry_wfS {n : Nat} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {s : Nat} {caps : List Tm} {self : Tm} {rest : Bool} {comp : ComponentTag} {recv : Tm} {args : List Tm}
    (hE : ∀ x ∈ E, free false x = true) (hc : ∀ x ∈ caps, free false x = true) (hs : free false self = true)
    (hr : free false recv = true) (ha : ∀ x ∈ args, free false x = true) (hv : ∀ x ∈ args, isVal x = true) :
    wfS (CallArguments.graphEntry n E K s caps self rest comp recv args) = true := by
  have hpar : ∀ x ∈ CallArguments.parameters n args, free false x = true := fun x hx =>
    (Kinds.parameters_mem hx).elim (ha x) (fun h => h ▸ rfl)
  have hdrop : ∀ x ∈ args.drop n, free false x = true := fun x hx => ha x (List.mem_of_mem_drop hx)
  have hdv : ∀ x ∈ args.drop n, isVal x = true := fun x hx => hv x (List.mem_of_mem_drop hx)
  have hlit : wfArgsS (args.drop n) = true := wfArgsS_of (fun x _ hx => wfS_of_free x hx) hdrop
  have henv : ∀ x ∈ recv :: CallArguments.parameters n args ++ (caps ++ [self]), free false x = true := by
    intro x hx
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | hx) | hx | rfl
    · exact hr
    · exact hpar x hx
    · exact hc x hx
    · exact hs
  have hrun : ∀ L : List Tm, (∀ x ∈ L, free false x = true) → runParts E L .nul = true := by
    intro L hL
    simp only [runParts, frees_eq, Bool.and_eq_true, List.all_eq_true]
    exact ⟨⟨hE, hL⟩, rfl⟩
  unfold CallArguments.graphEntry
  split
  · exact hrun _ henv
  · have hfa : free false (.arrLit (args.drop n)) = true := by
      simp only [free, frees_eq, List.all_eq_true]; exact hdrop
    simp only [wfS, isVal, Bool.and_eq_true, bodyOk, Bool.or_eq_true, ↓reduceIte]
    refine ⟨hlit, .inr ⟨⟨hfa, ?_⟩, ?_⟩⟩
    · simp only [restHead, List.all_eq_true]; exact hdv
    · simp only [isRun]
      exact hrun _ fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact henv x hx

/-! ## Every step keeps a reached term -/

theorem free_wfS_val {v : Tm} (hv : isVal v = true) (hw : wfS v = true) : free false v = true := by
  rwa [← wfS_val hv]

/-- **Every step keeps a reached term, and a step that changes the heap
keeps the path's frames** (proved, by induction on the step): the
positions other than the evaluation path are free of runs, so a subterm
reaching a value enters no run, and the only runs a step pushes are those a
graph call or a binding's step produces, neither of which changes the
heap. -/
theorem step_wfS {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    wfS t = true → HeapFree h → wfS t' = true ∧ (h' = h ∨ ∀ rl c nk, Stay (path rl c nk t) (path rl c nk t')) := by
  induction hs
  case callArg hf hr ha hpre hs ih =>
    intro hw hh
    simp only [wfS, hf, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    have hna := not_val_of_step hs
    obtain ⟨wa, hoth⟩ := wfArgsS_split hw.2 ha hpre hna
    obtain ⟨w', hp⟩ := ih wa hh
    have ho := set_others (b := ‹Tm›) hoth
    refine ⟨?_, hp.imp id fun hp rl c nk => Stay.ctx (hp rl c nk) (by simp only [path, hf, hr]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path, hf, hr]; exact pathArgs_set _ ha hpre hv) (fun hv => nr_path _ ?_ c nk)⟩
    · simp only [wfS, hf, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true]
      exact ⟨hw.1, wfArgsS_mk (set_at ha) (set_pre hpre) w' ho⟩
    · simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true]
      exact ⟨hw.1, all_set ho (free_wfS_val hv w')⟩
  case constructArg hf ha hpre hs ih =>
    intro hw hh
    simp only [wfS, hf, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    have hna := not_val_of_step hs
    obtain ⟨wa, hoth⟩ := wfArgsS_split hw.2 ha hpre hna
    obtain ⟨w', hp⟩ := ih wa hh
    have ho := set_others (b := ‹Tm›) hoth
    refine ⟨?_, hp.imp id fun hp rl c nk => Stay.ctx (hp rl c nk) (by simp only [path, hf]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path, hf]; exact pathArgs_set _ ha hpre hv) (fun hv => nr_path _ ?_ c nk)⟩
    · simp only [wfS, hf, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true]
      exact ⟨hw.1, wfArgsS_mk (set_at ha) (set_pre hpre) w' ho⟩
    · simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true]
      exact ⟨hw.1, all_set ho (free_wfS_val hv w')⟩
  case arrArg ha hpre hs ih =>
    intro hw hh
    simp only [wfS] at hw
    have hna := not_val_of_step hs
    obtain ⟨wa, hoth⟩ := wfArgsS_split hw ha hpre hna
    obtain ⟨w', hp⟩ := ih wa hh
    have ho := set_others (b := ‹Tm›) hoth
    refine ⟨?_, hp.imp id fun hp rl c nk => Stay.ctx (hp rl c nk) (by simp only [path]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path]; exact pathArgs_set _ ha hpre hv) (fun hv => nr_path _ ?_ c nk)⟩
    · simp only [wfS]
      exact wfArgsS_mk (set_at ha) (set_pre hpre) w' ho
    · simp only [free, frees_eq, List.all_eq_true]
      exact all_set ho (free_wfS_val hv w')
  case makeArg c ns inits i h₀ h₁ a a' ha hpre hs ih =>
    intro hw hh
    have hna := not_val_of_step hs
    have hcode : ∀ xs, wfArgsS xs = true → wfS (.makeAt c ns xs) = true := by
      intro xs hx; cases c <;> simp_all [wfS]
    have hcode' : ∀ xs, (∀ x ∈ xs, free false x = true) → free false (.makeAt c ns xs) = true := by
      intro xs hx; cases c <;> simp_all [wfS, free]
    have hw' : wfArgsS inits = true := by
      cases c <;> simp only [wfS, Bool.and_eq_true] at hw <;> first | exact hw | exact hw.2
    obtain ⟨wa, hoth⟩ := wfArgsS_split hw' ha hpre hna
    obtain ⟨w', hp⟩ := ih wa hh
    have ho := set_others (b := a') hoth
    exact ⟨hcode _ (wfArgsS_mk (set_at ha) (set_pre hpre) w' ho), hp.imp id fun hp rl c' nk => Stay.ctx (hp rl c' nk)
      (by simp only [path]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path]; exact pathArgs_set _ ha hpre hv)
      (fun hv => nr_path _ (hcode' _ (all_set ho (free_wfS_val hv w'))) c' nk)⟩
  case letC h₀ a h₁ a' b hs ih =>
    intro hw hh
    have hna := not_val_of_step hs
    simp only [wfS, hna, ↓reduceIte, Bool.and_eq_true] at hw
    obtain ⟨w', hp⟩ := ih hw.1 hh
    have hb : bodyOk a' b = true := by
      simp only [bodyOk, Bool.or_eq_true, Bool.and_eq_true] at hw ⊢
      rcases hw.2 with h | ⟨⟨h₁, h₂⟩, h₃⟩
      · exact .inl h
      · obtain ⟨r₁, r₂⟩ := restHead_step hs h₂
        exact .inr ⟨⟨r₂, r₁⟩, h₃⟩
    refine ⟨?_, hp.imp id fun hp rl c nk => Stay.ctx (g := fun s => Tm.letE s b) (hp rl c nk) (by simp [path, hna])
      (fun hv => by simp [path, hv]) (fun hv => by simp [path, hv])⟩
    simp only [wfS]
    split
    · simp only [Bool.and_eq_true]; exact ⟨w', hb⟩
    · rename_i hv
      simp only [Bool.not_eq_false] at hv
      simp only [Bool.and_eq_true]; exact ⟨free_wfS_val hv w', hb⟩
  case callBound =>
    rename_i hr hargs
    intro hw hh
    simp only [wfS, isVal_objAt, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true, free, frees_eq,
      List.all_eq_true] at hw
    have hpa := wfArgsS_vals hw.2 hargs
    refine ⟨wfS_of_free _ ?_, .inl rfl⟩
    simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    grind
  case letV ha =>
    intro hw hh
    simp only [wfS, ha, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    refine ⟨?_, .inl rfl⟩
    simp only [bodyOk, Bool.or_eq_true, Bool.and_eq_true] at hw
    rcases hw.2 with hb | ⟨-, hb⟩
    · exact wfS_of_free _ (subst_free hw.1 _ 0 false hb)
    · rename_i b
      cases b <;> simp only [isRun, Bool.false_eq_true] at hb
      simp only [runParts, frees_eq, Bool.and_eq_true, List.all_eq_true] at hb
      simp only [subst, wfS, runParts, frees_eq, substArgs_eq_map, Bool.and_eq_true, List.all_eq_true,
        List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact ⟨⟨hb.1.1, fun x hx => subst_free hw.1 _ 0 false (hb.1.2 x hx)⟩, subst_free hw.1 _ 0 false hb.2⟩
  case gotoEnter E l e K k x _ L d comp he hK =>
    intro hw hh
    simp only [wfS, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true] at hw
    have henv : ∀ i, free false (envOf L d i) = true := fun i => by
      rcases getD_mem_or L i d with h | h
      · simp only [envOf]; exact hw.1.2 _ h
      · simp only [envOf]; rw [h]; exact hw.2
    have hnr := instantiate_free henv e 0 false (hw.1.1 e (List.mem_of_getElem? he))
    refine ⟨?_, .inl rfl⟩
    simp only [wfS, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true]
    exact ⟨hw, wfS_of_free _ hnr⟩
  case frameC ih =>
    intro hw hh
    simp only [wfS, Bool.and_eq_true] at hw
    obtain ⟨w', hp⟩ := ih hw.2 hh
    refine ⟨by simp only [wfS, Bool.and_eq_true]; exact ⟨hw.1, w'⟩, hp.imp id fun hp rl c nk => ?_⟩
    simp only [path]
    exact Stay.append _ (Stay.wrap _ (hp _ _ _))
  case frameRet hv =>
    intro hw hh
    simp only [wfS, Bool.and_eq_true] at hw
    exact ⟨hw.2, .inl rfl⟩
  case frameHandle hr =>
    intro hw hh
    simp only [wfS, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true] at hw
    have hv := raises_free hr (wfS_wf _ hw.2)
    refine ⟨?_, .inl rfl⟩
    simp only [wfS, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true]
    refine ⟨⟨hw.1.1.1, fun x hx => ?_⟩, ?_⟩ <;>
      first
        | (rcases envMap_mem (.inl hx) with hx | rfl
           · rcases List.mem_cons.mp hx with rfl | hx
             · exact hv
             · exact hw.1.1.2 x hx
           · exact hw.1.2)
        | (rcases envMap_mem (.inr rfl) with hx | hx
           · rcases List.mem_cons.mp hx with hx | hx
             · rw [hx]; exact hv
             · exact hw.1.1.2 _ hx
           · rw [hx]; exact hw.1.2)
  case frameRaise hr =>
    intro hw hh
    simp only [wfS, runParts, Bool.and_eq_true] at hw
    have hv := raises_free hr (wfS_wf _ hw.2)
    exact ⟨wfS_of_free _ (by simp only [free]; exact hv), .inl rfl⟩
  case callSpread =>
    rename_i hf hr heq hpre hre
    intro hw hh
    simp only [wfS, hf, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    rw [heq] at hw
    obtain ⟨hp1, hp2⟩ := wfArgsS_mid isVal_spread hw.2 hpre
    have hvs := readElems_free hh hre
    refine ⟨wfS_of_free _ ?_, .inl rfl⟩
    simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    grind
  case constructSpread =>
    rename_i hf heq hpre hre
    intro hw hh
    simp only [wfS, hf, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    rw [heq] at hw
    obtain ⟨hp1, hp2⟩ := wfArgsS_mid isVal_spread hw.2 hpre
    have hvs := readElems_free hh hre
    refine ⟨wfS_of_free _ ?_, .inl rfl⟩
    simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    grind
  case arrSpread =>
    rename_i heq hpre hre
    intro hw hh
    simp only [wfS] at hw
    rw [heq] at hw
    obtain ⟨hp1, hp2⟩ := wfArgsS_mid isVal_spread hw hpre
    have hvs := readElems_free hh hre
    refine ⟨wfS_of_free _ ?_, .inl rfl⟩
    simp only [free, frees_eq, List.all_eq_true, List.mem_append]
    grind
  case makeFields c ns vs h₀ hvs hlen =>
    intro hw hh
    have hargs : wfArgsS vs = true := by
      cases c <;> simp only [wfS, Bool.and_eq_true] at hw <;> first | exact hw | exact hw.2
    refine ⟨wfS_of_free _ ?pf, .inr fun rl c' nk => Stay.base (by simp [path, pathArgs_vals _ hvs]) (nr_path _ ?pf c' nk)⟩
    case pf => cases c <;> simp_all [wfS, free]
  case readField =>
    rename_i hl hv
    intro _ hh
    exact ⟨wfS_of_free _ (hh.get hv), .inl rfl⟩
  case readProto =>
    rename_i h1 h2 hp
    intro _ hh
    exact ⟨wfS_of_free _ (by simp only [free]; exact hh.get hp), .inl rfl⟩
  case indexField =>
    rename_i hk hl hv
    intro _ hh
    exact ⟨wfS_of_free _ (hh.get hv), .inl rfl⟩
  case indexProto =>
    rename_i hk h1 h2 hp
    intro hw hh
    simp only [wfS, isVal_objAt, propertyKey_val hk, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    exact ⟨wfS_of_free _ (by simp only [free, Bool.and_eq_true]; exact ⟨hh.get hp, hw.2⟩), .inl rfl⟩
  case writeField =>
    rename_i hv hl hlt
    intro hw hh
    exact ⟨rfl, .inr fun rl c nk => Stay.base (by simp [path, hv]) (by simp [path])⟩
  case testV =>
    rename_i hv
    intro _ hh
    exact ⟨wfS_of_free _ (by split <;> rfl), .inl rfl⟩
  case arithV =>
    rename_i hb
    intro _ hh
    obtain ⟨ha, hb', hres⟩ := binop_result hb
    exact ⟨wfS_of_free _ (by rcases hres with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl), .inl rfl⟩
  case arrAlloc =>
    rename_i hvs hlen
    intro hw hh
    exact ⟨rfl, .inr fun rl c nk => Stay.base (by simp [path, pathArgs_vals _ hvs]) (by simp [path])⟩
  case arrAllocThrow =>
    rename_i hvs hlen
    intro _ hh
    exact ⟨by simp [wfS, free, thrownError], .inr fun rl c nk => Stay.base (by simp [path, pathArgs_vals _ hvs])
      (by simp [path, thrownError])⟩
  case elemRead =>
    rename_i hl hv
    intro _ hh
    exact ⟨wfS_of_free _ (hh.get hv), .inl rfl⟩
  case setPresent =>
    rename_i hv hl hlt
    intro hw hh
    exact ⟨rfl, .inr fun rl c nk => Stay.base (by simp [path, hv]) (by simp [path])⟩
  case setGrow =>
    rename_i hv hk hl
    intro hw hh
    exact ⟨rfl, .inr fun rl c nk => Stay.base (by simp [path, hv]) (by simp [path])⟩
  case lenStrThrow =>
    intro _ hh
    exact ⟨by simp [wfS, free, thrownError], .inr fun rl c nk => Stay.base (by simp [path]) (by simp [path, thrownError])⟩
  case elemStr =>
    intro _ hh
    exact ⟨wfS_of_free _ (by simp only [codeUnitAt]; split <;> rfl), .inl rfl⟩
  case arithThrow =>
    rename_i hb
    intro _ hh
    obtain ⟨ha, hb'⟩ := binopThrows_values hb
    exact ⟨by simp [wfS, free, thrownError], .inr fun rl c nk => Stay.base (by simp [path, ha, hb'])
      (by simp [path, thrownError])⟩
  case mergeV =>
    rename_i ha hb hm
    intro _ hh
    refine ⟨wfS_of_free _ ?_, .inl rfl⟩
    simp only [free, frees_eq, List.all_eq_true]
    exact mergeParts_free hh hm
  case makeKeyV =>
    rename_i ha hk
    intro hw hh
    simp only [wfS, propertyKey_val hk, ha, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    exact ⟨wfS_of_free _ (by simp [free, hw.2]), .inl rfl⟩
  case callGraph =>
    rename_i hr hargs hbind
    intro hw hh
    simp only [wfS, isVal_objAt, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true, free, frees_eq,
      List.all_eq_true] at hw
    have hpa := wfArgsS_vals hw.2 hargs
    exact ⟨graphEntry_wfS hw.1.1.1 hw.1.1.2 (by simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true]; exact hw.1.1)
      hw.1.2 hpa hargs, .inl rfl⟩
  case constructGraph =>
    rename_i hargs
    intro hw hh
    simp only [wfS, isVal_objAt, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true, free, frees_eq,
      List.all_eq_true] at hw
    have hpa := wfArgsS_vals hw.2 hargs
    exact ⟨graphEntry_wfS hw.1.1 hw.1.2 (by simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true]; exact hw.1)
      rfl hpa hargs, .inl rfl⟩
  all_goals try (
    intro hw hh
    simp only [wfS, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true] at hw
    refine ⟨?_, .inl rfl⟩
    simp only [wfS, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true]
    have hv : ∀ v, isVal v = true → wfS v = true → free false v = true := fun v hv hw => free_wfS_val hv hw
    refine ⟨⟨hw.1.1.1, (envMap_free ?_ hw.1.2).1⟩, (envMap_free ?_ hw.1.2).2⟩ <;>
      first
        | exact hw.1.1.2
        | (intro x hx; rcases List.mem_cons.mp hx with rfl | hx
           · first | rfl | exact hv _ ‹_› hw.2
           · exact hw.1.1.2 x hx)
    done)
  all_goals try (
    rename_i ih
    intro hw hh
    have hna := not_val_of_step ‹Step _ _ _ _›
    simp [wfS, *] at hw
    obtain ⟨w', hp⟩ := ih (by simp_all) hh
    refine ⟨?_, hp.imp id fun hp rl c nk => Stay.ctx (hp rl c nk) (by simp [path, *] <;> rfl)
      (fun hv => by simp [path, *] <;> rfl) (fun hv => nr_path _ ?_ c nk)⟩
    · simp only [wfS]; (repeat' split) <;> simp_all [free_wfS_val, wfS_of_free, wfArgsS_of]
    · simp_all [free, free_wfS_val]
    done)
  -- A redex to a term free of runs.
  all_goals try (
    intro hw hh
    refine ⟨wfS_of_free _ ?pf, ?heap⟩
    case pf => simp_all [wfS, free]
    case heap => first | exact .inl rfl | exact .inr fun rl c nk => Stay.base (by simp [path, *]) (nr_path _ ?pf c nk)
    done)

end Verification.TolerantFrames.ReadOnly
