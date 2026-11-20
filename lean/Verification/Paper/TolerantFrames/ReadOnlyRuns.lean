import Verification.Paper.TolerantFrames.ReadOnlyExec

/-! # Read-only handles: runs sit at evaluation positions

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "Actual
executions"): the call discipline (`Disc`) of the steps of the paper
model's reduction (`Step`), from terms whose runs sit at evaluation
positions.

- **A term free of runs** (`free false`) holds no `goto` and no `frame`,
  in the code of its values included. A term whose runs are pending
  (`free true`) holds no `frame`, and each `goto` it holds has its code,
  environment and default free of runs: a run not yet entered, as a call
  of graph code with a rest leaves one under the binding of its rest.
- **A well-formed runtime term** (`wf`): along its evaluation path, each
  position's other subterms are pending, a `goto` and a `frame` on the
  path have their code, environment and default free of runs, and a
  frame's running term is again well formed. A heap is free of runs
  (`HeapFree`) when every value it holds is.
- **Every step keeps both** (`step_runs_wf`), and changes the runs of the
  path as `PathRuns` states (the run it changes keeps its code and tag, it
  pushes at most one run, not yet entered), so it pushes at most one frame
  on the path (`step_wf`, `PathStep1`, the strengthening of `step_path`'s
  `PathStep`).
- **The discipline** (`disc_of_wf`): a step of a well-formed term on a
  heap free of runs obeys `Disc` at every component of a family.
- **A safe term's step is an actual step** (`astep_of_safe`): its world
  transition is the one the step clause of `Safe` gives.
- Computed checks of the call structure on re-entry, throw and return to
  either kind of top level, and the counter-model for terms that are not
  well formed (`twoCalls_step`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification

/-! ## Terms free of runs -/

mutual
/-- **Free of runs** (`p = false`): no `goto` and no `frame`, the code of
values included. **Pending runs** (`p = true`): no `frame`, and every
`goto` with its code, environment and default free of runs. -/
def free (p : Bool) : Tm → Bool
  | .invoke f r args => free p f && free p r && frees p args
  | .construct f args => free p f && frees p args
  | .letE a b => free p a && free p b
  | .objAt _ (.bound t r pre) _ => free false t && free false r && frees false pre
  | .objAt _ (.graph _ E _ _ caps _ _ _) _ => frees false E && frees false caps
  | .makeAt (.bound t r pre) _ xs => free false t && free false r && frees false pre && frees p xs
  | .makeAt (.graph _ E _ _ caps _ _ _) _ xs => frees false E && frees false caps && frees p xs
  | .makeAt .absent _ xs => frees p xs
  | .makeAt (.view _ _ _) _ xs => frees p xs
  | .readAt _ a => free p a
  | .indexAt a b => free p a && free p b
  | .writeAt _ a b => free p a && free p b
  | .test _ a => free p a
  | .ite x a b => free p x && free p a && free p b
  | .arith _ a b => free p a && free p b
  | .arrLit xs => frees p xs
  | .elemAt a b => free p a && free p b
  | .setElem a b x => free p a && free p b && free p x
  | .lenOf a => free p a
  | .spread a => free p a
  | .throw a => free p a
  | .merge _ a b => free p a && free p b
  | .makeKey a b => free p a && free p b
  | .goto E _ _ L d _ => p && frees false E && frees false L && free false d
  | .frame .. => false
  | _ => true
termination_by structural t => t

def frees (p : Bool) : List Tm → Bool
  | [] => true
  | x :: xs => free p x && frees p xs
termination_by structural xs => xs
end

@[simp] theorem frees_eq (p : Bool) (xs : List Tm) : frees p xs = xs.all (free p) := by
  induction xs <;> simp_all [frees]

/-- A run's parts are free of runs. -/
def runParts (E L : List Tm) (d : Tm) : Bool := frees false E && frees false L && free false d

mutual
/-- **A well-formed runtime term**: along its evaluation path (`path`) every
other subterm of a position is pending (`free true`); a `goto` and a
`frame` have their parts free of runs, and a frame's running term is well
formed. -/
def wf : Tm → Bool
  | .invoke f r args =>
    if isVal f = false then wf f && free true r && frees true args
    else if isVal r = false then free true f && wf r && frees true args
    else free true f && free true r && wfArgs args
  | .construct f args =>
    if isVal f = false then wf f && frees true args else free true f && wfArgs args
  | .letE a b => if isVal a = false then wf a && free true b else free true a && free true b
  | .makeAt (.bound t r pre) _ xs => free false t && free false r && frees false pre && wfArgs xs
  | .makeAt (.graph _ E _ _ caps _ _ _) _ xs => frees false E && frees false caps && wfArgs xs
  | .makeAt .absent _ xs => wfArgs xs
  | .makeAt (.view _ _ _) _ xs => wfArgs xs
  | .readAt _ a => if isVal a = false then wf a else free true a
  | .indexAt a b =>
    if isVal a = false then wf a && free true b
    else if isVal b = false then free true a && wf b else free true a && free true b
  | .writeAt _ a b =>
    if isVal a = false then wf a && free true b
    else if isVal b = false then free true a && wf b else free true a && free true b
  | .test _ a => if isVal a = false then wf a else free true a
  | .ite x a b => if isVal x = false then wf x && free true a && free true b
    else free true x && free true a && free true b
  | .arith _ a b =>
    if isVal a = false then wf a && free true b
    else if isVal b = false then free true a && wf b else free true a && free true b
  | .arrLit xs => wfArgs xs
  | .elemAt a b =>
    if isVal a = false then wf a && free true b
    else if isVal b = false then free true a && wf b else free true a && free true b
  | .setElem a b x =>
    if isVal a = false then wf a && free true b && free true x
    else if isVal b = false then free true a && wf b && free true x
    else if isVal x = false then free true a && free true b && wf x
    else free true a && free true b && free true x
  | .lenOf a => if isVal a = false then wf a else free true a
  | .spread a => if isVal a = false then wf a else free true a
  | .throw a => if isVal a = false then wf a else free true a
  | .merge _ a b =>
    if isVal a = false then wf a && free true b
    else if isVal b = false then free true a && wf b else free true a && free true b
  | .makeKey a b =>
    if isVal a = false then wf a && free true b
    else if isVal b = false then free true a && wf b else free true a && free true b
  | .goto E _ _ L d _ => runParts E L d
  | .frame E _ t L d _ _ _ => runParts E L d && wf t
  | t => free true t
termination_by structural t => t

def wfArgs : List Tm → Bool
  | [] => true
  | a :: as => if isVal a = false then wf a && frees true as else free true a && wfArgs as
termination_by structural xs => xs
end

/-- **A heap free of runs**: every value it holds is. -/
def HeapFree (h : Heap) : Prop := ∀ v ∈ h, free false v = true

/-! ## Basic facts -/

theorem free_mono : ∀ (t : Tm), free false t = true → free true t = true := by
  intro t
  induction t using Tm.induct
  all_goals intro h
  all_goals simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true] at h ⊢
  all_goals grind

theorem free_val {v : Tm} (hv : isVal v = true) (p : Bool) : free p v = free false v := by
  cases v <;> simp_all [isVal, free] <;> rename_i cc _ <;> cases cc <;> simp [free]

theorem free_val' {v : Tm} (hv : isVal v = true) (h : free true v = true) : free false v = true := by
  rwa [← free_val hv true]

theorem wf_val {v : Tm} (hv : isVal v = true) : wf v = free true v := by
  cases v <;> simp_all [isVal, wf]

theorem wfArgs_of {xs : List Tm} (ih : ∀ a ∈ xs, free true a = true → wf a = true)
    (h : ∀ a ∈ xs, free true a = true) : wfArgs xs = true := by
  induction xs with
  | nil => rfl
  | cons a as iha =>
    simp only [wfArgs]
    split
    · simp only [Bool.and_eq_true, frees_eq, List.all_eq_true]
      exact ⟨ih a List.mem_cons_self (h a List.mem_cons_self), fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
    · simp only [Bool.and_eq_true]
      exact ⟨h a List.mem_cons_self, iha (fun x hx => ih x (List.mem_cons_of_mem _ hx))
        (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem pf_wf : ∀ (t : Tm), free true t = true → wf t = true := by
  intro t
  induction t using Tm.induct
  all_goals intro h
  all_goals first
    | (simp only [free, Bool.false_eq_true] at h; done)
    | skip
  all_goals simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true] at h
  all_goals simp only [wf, runParts, frees_eq, Bool.and_eq_true, List.all_eq_true]
  all_goals (repeat' split) <;> (try simp only [Bool.and_eq_true]) <;>
    first
      | rfl
      | (simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true]; exact h)
      | (exact wfArgs_of (by grind) (by grind))
      | (exact ⟨by grind, wfArgs_of (by grind) (by grind)⟩)
      | grind

theorem wrap_length {g : Tm → Tm} (P : List (ComponentTag × Tm)) : (wrap g P).length = P.length := by
  have := congrArg List.length (wrap_fst (g := g) P)
  simpa using this

theorem pathArgs_len {c : ComponentTag} :
    ∀ {xs : List Tm} (k : List Tm → Tm), (∀ a ∈ xs, ∀ c, free true a = true → (path c a).length ≤ 2) →
      (∀ a ∈ xs, free true a = true) → (pathArgs c k xs).length ≤ 2
  | [], _, _, _ => by simp [pathArgs]
  | a :: as, k, ih, h => by
    simp only [pathArgs]
    split
    · rw [wrap_length]; exact ih a List.mem_cons_self c (h a List.mem_cons_self)
    · exact pathArgs_len _ (fun x hx => ih x (List.mem_cons_of_mem _ hx)) (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **A pending term enters at most one run**: its path holds at most one
frame. -/
theorem pf_path : ∀ (t : Tm), free true t = true → ∀ c, (path c t).length ≤ 2 := by
  intro t
  induction t using Tm.induct
  all_goals intro h c
  all_goals simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true] at h
  all_goals simp only [path]
  all_goals (repeat' split) <;> (try rw [wrap_length]) <;>
    first
      | (simp; done)
      | (apply pathArgs_len <;> grind)
      | grind

/-! ## Substitution keeps terms free of runs -/

theorem subst_free {a : Tm} (ha : free false a = true) :
    ∀ (b : Tm) (j : Nat) (p : Bool), free p b = true → free p (subst j a b) = true := by
  intro b
  induction b using Tm.induct
  all_goals intro j p hb
  all_goals simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true] at hb
  all_goals simp only [subst, free, frees_eq, substArgs_eq_map, Bool.and_eq_true, List.all_eq_true,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  all_goals first
    | (split <;> (try split) <;> first | rfl | (cases p <;> first | exact ha | exact free_mono _ ha))
    | grind

theorem instantiate_free {ρ : Env} (hρ : ∀ i, free false (ρ i) = true) :
    ∀ (b : Tm) (d : Nat) (p : Bool), free p b = true → free p (instantiate d ρ b) = true := by
  intro b
  induction b using Tm.induct
  all_goals intro d p hb
  all_goals simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true] at hb
  all_goals simp only [instantiate, free, frees_eq, instantiateArgs_eq_map, Bool.and_eq_true, List.all_eq_true,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  all_goals first
    | (split <;> first | rfl | (cases p <;> first | exact hρ _ | exact free_mono _ (hρ _)))
    | grind

/-! ## Heaps, copies and throws -/

theorem HeapFree.append {h xs : Heap} (hh : HeapFree h) (hx : ∀ v ∈ xs, free false v = true) : HeapFree (h ++ xs) := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hh v hv
  · exact hx v hv

theorem HeapFree.set {h : Heap} {l : Nat} {v : Tm} (hh : HeapFree h) (hv : free false v = true) :
    HeapFree (h.set l v) := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact hh x hx
  · exact hv

theorem HeapFree.get {h : Heap} {l : Nat} {v : Tm} (hh : HeapFree h) (hl : h[l]? = some v) : free false v = true :=
  hh v (List.mem_of_getElem? hl)

theorem readElems_free {h : Heap} (hh : HeapFree h) :
    ∀ {ls : List (Option Nat)} {vs : List Tm}, readElems h ls = some vs → ∀ v ∈ vs, free false v = true
  | [], vs, hr => by simp [readElems] at hr; subst hr; simp
  | none :: ls, vs, hr => by
    simp only [readElems, Option.map_eq_some_iff] at hr
    obtain ⟨ws, hws, rfl⟩ := hr
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · rfl
    · exact readElems_free hh hws v hv
  | some l :: ls, vs, hr => by
    simp only [readElems, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
    obtain ⟨w, hw, ws, hws, rfl⟩ := hr
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hh.get hw
    · exact readElems_free hh hws v hv

theorem mergeParts_free {h : Heap} (hh : HeapFree h) {d : List PropKey} {a b : Tm} {ps : List (PropKey × Tm)}
    (hm : mergeParts h d a b = some ps) : ∀ x ∈ ps.map Prod.snd, free false x = true := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  rcases Verification.mergeParts_vals hm p hp with he | ⟨hm', -⟩ | ⟨u, he⟩
  · rw [he]; rfl
  · exact hh _ hm'
  · rw [he]; rfl

/-- **A list whose first term that is not a value is at `i`**: well formed
exactly when that term is, and every other is pending. -/
theorem wfArgs_split : ∀ {xs : List Tm} {i : Nat} {a : Tm}, wfArgs xs = true → xs[i]? = some a →
    (∀ j, j < i → ∀ w, xs[j]? = some w → isVal w = true) → isVal a = false →
      wf a = true ∧ ∀ j x, xs[j]? = some x → j ≠ i → free true x = true
  | [], _, _, _, h, _, _ => by simp at h
  | b :: bs, 0, a, hw, h, _, ha => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [wfArgs, ha, ite_true, Bool.and_eq_true, frees_eq, List.all_eq_true] at hw
    refine ⟨hw.1, fun j x hx hj => ?_⟩
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact hw.2 x (List.mem_of_getElem? (by simpa using hx))
  | b :: bs, i + 1, a, hw, h, hpre, ha => by
    have hb : isVal b = true := hpre 0 (Nat.succ_pos _) b rfl
    simp only [wfArgs, hb, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    obtain ⟨hwa, hrest⟩ := wfArgs_split hw.2 (by simpa using h)
      (fun j hj w hw' => hpre (j + 1) (by omega) w (by simpa using hw')) ha
    refine ⟨hwa, fun j x hx hj => ?_⟩
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx; exact hw.1
    | succ j => exact hrest j x (by simpa using hx) (by omega)

theorem wfArgs_mk : ∀ {xs : List Tm} {i : Nat} {a : Tm}, xs[i]? = some a →
    (∀ j, j < i → ∀ w, xs[j]? = some w → isVal w = true) → wf a = true →
    (∀ j x, xs[j]? = some x → j ≠ i → free true x = true) → wfArgs xs = true
  | [], _, _, h, _, _, _ => by simp at h
  | b :: bs, 0, a, h, _, hwa, hrest => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have hbs : ∀ x ∈ bs, free true x = true := fun x hx => by
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      exact hrest (j + 1) x (by simpa using hj) (by omega)
    simp only [wfArgs]
    split
    · simp only [Bool.and_eq_true, frees_eq, List.all_eq_true]; exact ⟨hwa, hbs⟩
    · rename_i hv
      simp only [Bool.not_eq_false] at hv
      simp only [Bool.and_eq_true]
      exact ⟨by rw [← wf_val hv]; exact hwa, wfArgs_of (fun x _ hx => pf_wf x hx) hbs⟩
  | b :: bs, i + 1, a, h, hpre, hwa, hrest => by
    have hb : isVal b = true := hpre 0 (Nat.succ_pos _) b rfl
    simp only [wfArgs, hb, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true]
    exact ⟨hrest 0 b rfl (by omega), wfArgs_mk (by simpa using h)
      (fun j hj w hw' => hpre (j + 1) (by omega) w (by simpa using hw')) hwa
      (fun j x hx hj => hrest (j + 1) x (by simpa using hx) (by omega))⟩

theorem wfArgs_vals {xs : List Tm} (hw : wfArgs xs = true) (hv : ∀ x ∈ xs, isVal x = true) :
    ∀ x ∈ xs, free true x = true := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := hv a List.mem_cons_self
    simp only [wfArgs, ha, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hw.1
    · exact ih hw.2 (fun y hy => hv y (List.mem_cons_of_mem _ hy)) x hx

/-- **A thrown value is free of runs.** -/
theorem raises_free {t v : Tm} (hr : Raises t v) (hw : wf t = true) : free false v = true := by
  induction hr
  case throwV hv _ =>
    simp only [wf, hv, Bool.true_eq_false, ↓reduceIte] at hw
    exact free_val' hv hw
  case callArg ha hpre hr' ih =>
    rename_i hf hrv
    simp only [wf, hf, hrv, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    exact ih (wfArgs_split hw.2 ha hpre (raises_not_val hr')).1
  case constructArg ha hpre hr' ih =>
    rename_i hf
    simp only [wf, hf, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    exact ih (wfArgs_split hw.2 ha hpre (raises_not_val hr')).1
  case makeArg c ns inits i a v ha hpre hr' ih =>
    have hw' : wfArgs inits = true := by
      cases c <;> simp only [wf, Bool.and_eq_true] at hw <;> first | exact hw | exact hw.2
    exact ih (wfArgs_split hw' ha hpre (raises_not_val hr')).1
  case arrArg ha hpre hr' ih =>
    simp only [wf] at hw
    exact ih (wfArgs_split hw ha hpre (raises_not_val hr')).1
  all_goals
    rename_i ih
    have hn := raises_not_val ‹Raises _ _›
    exact ih (by simp_all [wf])

/-! ## A step pushes at most one frame -/

/-- **A step's change of the path, pushing at most one frame**: `PathStep`
with at most one frame pushed. -/
def PathStep1 (P P' : List (ComponentTag × Tm)) : Prop :=
  (∃ new F F' rest, P = F :: rest ∧ P' = new ++ F' :: rest ∧ F'.1 = F.1 ∧ new.length ≤ 1) ∨
  (∃ new F G G' rest, P = F :: G :: rest ∧ P' = new ++ G' :: rest ∧ G'.1 = G.1 ∧ new.length ≤ 1)

theorem init_short {P : List (ComponentTag × Tm)} {init : List (ComponentTag × Tm)} {x : ComponentTag × Tm}
    (hP : P = init ++ [x]) (hl : P.length ≤ 2) : init.length ≤ 1 := by
  subst hP; simp at hl; omega

theorem pathArgs_len1 {c : ComponentTag} :
    ∀ {xs : List Tm} (k : List Tm → Tm), (∀ a ∈ xs, ∀ c, free false a = true → (path c a).length = 1) →
      (∀ a ∈ xs, free false a = true) → (pathArgs c k xs).length = 1
  | [], _, _, _ => by simp [pathArgs]
  | a :: as, k, ih, h => by
    simp only [pathArgs]
    split
    · rw [wrap_length]; exact ih a List.mem_cons_self c (h a List.mem_cons_self)
    · exact pathArgs_len1 _ (fun x hx => ih x (List.mem_cons_of_mem _ hx)) (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **A term free of runs enters none**: its path is its top segment. -/
theorem nr_path : ∀ (t : Tm), free false t = true → ∀ c, (path c t).length = 1 := by
  intro t
  induction t using Tm.induct
  all_goals intro h c
  all_goals simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true, Bool.false_eq_true, false_and] at h
  all_goals simp only [path]
  all_goals (repeat' split) <;> (try rw [wrap_length]) <;>
    first
      | (simp; done)
      | (apply pathArgs_len1 <;> grind)
      | grind

theorem wfArgs_of_pf {xs : List Tm} (h : ∀ x ∈ xs, free true x = true) : wfArgs xs = true :=
  wfArgs_of (fun x _ hx => pf_wf x hx) h

theorem pf_of_wf_val {v : Tm} (hv : isVal v = true) (hw : wf v = true) : free true v = true := by
  rwa [← wf_val hv]

theorem nr_of_wf_val {v : Tm} (hv : isVal v = true) (hw : wf v = true) : free false v = true :=
  free_val' hv (pf_of_wf_val hv hw)

theorem nr_frees_true {xs : List Tm} (h : ∀ x ∈ xs, free false x = true) : ∀ x ∈ xs, free true x = true :=
  fun x hx => free_mono x (h x hx)

theorem all_set {P : Tm → Prop} {xs : List Tm} {i : Nat} {b : Tm}
    (h : ∀ j x, (xs.set i b)[j]? = some x → j ≠ i → P x) (hb : P b) : ∀ x ∈ xs.set i b, P x := by
  intro x hx
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
  by_cases hji : j = i
  · subst hji
    simp only [List.getElem?_set, ite_true] at hj
    split at hj <;> simp_all
  · exact h j x hj hji

theorem set_others {P : Tm → Prop} {xs : List Tm} {i : Nat} {b : Tm} (h : ∀ j x, xs[j]? = some x → j ≠ i → P x) :
    ∀ j x, (xs.set i b)[j]? = some x → j ≠ i → P x := by
  intro j x hx hj
  rw [List.getElem?_set_ne (Ne.symm hj)] at hx
  exact h j x hx hj

theorem wfArgs_mid {a : Tm} {post : List Tm} (ha : isVal a = false) :
    ∀ {pre : List Tm}, wfArgs (pre ++ a :: post) = true → (∀ v ∈ pre, isVal v = true) →
      wf a = true ∧ (∀ x ∈ pre, free true x = true) ∧ ∀ x ∈ post, free true x = true
  | [], hw, _ => by
    simp only [List.nil_append, wfArgs, ha, ↓reduceIte, Bool.and_eq_true, frees_eq, List.all_eq_true] at hw
    exact ⟨hw.1, by simp, hw.2⟩
  | b :: bs, hw, hpre => by
    have hb := hpre b List.mem_cons_self
    simp only [List.cons_append, wfArgs, hb, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    obtain ⟨h1, h2, h3⟩ := wfArgs_mid ha hw.2 (fun v hv => hpre v (List.mem_cons_of_mem _ hv))
    refine ⟨h1, fun x hx => ?_, h3⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hw.1
    · exact h2 x hx

theorem envMap_free {m : Option (List Nat)} {L : List Tm} {d : Tm} (hL : ∀ x ∈ L, free false x = true)
    (hd : free false d = true) : (∀ x ∈ (envMap m L d).1, free false x = true) ∧ free false (envMap m L d).2 = true := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases envMap_mem (.inl hx) with hx | rfl
    · exact hL x hx
    · exact hd
  · rcases envMap_mem (m := m) (L := L) (d := d) (.inr rfl) with hx | hx
    · exact hL _ hx
    · rw [hx]; exact hd

theorem graphEntry_free {n : Nat} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {s : Nat} {caps : List Tm} {self : Tm} {rest : Bool} {comp : ComponentTag} {recv : Tm} {args : List Tm}
    (hE : ∀ x ∈ E, free false x = true) (hc : ∀ x ∈ caps, free false x = true) (hs : free false self = true)
    (hr : free false recv = true) (ha : ∀ x ∈ args, free false x = true) :
    free true (CallArguments.graphEntry n E K s caps self rest comp recv args) = true := by
  have hpar : ∀ x ∈ CallArguments.parameters n args, free false x = true := fun x hx =>
    (Kinds.parameters_mem hx).elim (ha x) (fun h => h ▸ rfl)
  have hdrop : ∀ x ∈ args.drop n, free true x = true := fun x hx => free_mono _ (ha x (List.mem_of_mem_drop hx))
  have hv : free false (.var 0) = true := rfl
  unfold CallArguments.graphEntry
  split <;> simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.mem_append,
    Bool.true_and] <;> grind

section
open ControlFlow
/-! ## The runs of a path -/

/-- **The run of a path entry**: the top segment, a run not yet entered, or
a frame. -/
inductive RunHead where
  | top
  | goto (code : Code) (comp : ComponentTag) (label : Nat)
  | frame (code : Code) (comp : ComponentTag) (k : Continuation) (x : Option Target)

/-- The run an entry's term is. -/
def runHead : Tm → RunHead
  | .goto E K l _ _ comp => .goto (E, K) comp l
  | .frame E K _ _ _ k x comp => .frame (E, K) comp k x
  | _ => .top

/-- **A node of a code a frame runs**: the code has a node at the label,
whose continuation and handler are the frame's. -/
def NodeOf (m : Code) (l : Nat) (k : Continuation) (x : Option Target) : Prop :=
  m.2[l]? = some (k, x) ∧ ∃ e, m.1[l]? = some e

/-- **A step of an entry's run**: its tag kept; the top segment stays one; a
frame stays a frame of the same code, continuation and handler, or becomes
a run of its code at a node; a run not yet entered becomes a frame at its
node. -/
def HeadStep (p p' : ComponentTag × Tm) : Prop :=
  p'.1 = p.1 ∧
    match runHead p.2, runHead p'.2 with
    | .top, .top => True
    | .frame m c k x, .frame m' c' k' x' => m' = m ∧ c' = c ∧ k' = k ∧ x' = x
    | .frame m c _ _, .goto m' c' _ => m' = m ∧ c' = c
    | .goto m c l, .frame m' c' k x => m' = m ∧ c' = c ∧ NodeOf m l k x
    | _, _ => False

/-- An entry that is a run not yet entered. -/
def IsGoto (p : ComponentTag × Tm) : Prop := ∃ m c l, runHead p.2 = .goto m c l

/-- **A step's change of the path's runs**: the innermost entry changed, or
popped and the one under it changed, at most one run not yet entered
pushed. -/
def PathRuns (P P' : List (ComponentTag × Tm)) : Prop :=
  (∃ new F F' rest, P = F :: rest ∧ P' = new ++ F' :: rest ∧ HeadStep F F' ∧ new.length ≤ 1 ∧
    ∀ p ∈ new, IsGoto p) ∨
  (∃ new F G G' rest, P = F :: G :: rest ∧ P' = new ++ G' :: rest ∧ HeadStep G G' ∧ new.length ≤ 1 ∧
    ∀ p ∈ new, IsGoto p)

/-! ### The shape of a path's runs -/

theorem HeadStep.top {a : ComponentTag} {s s' : Tm} (h : runHead s = .top) (h' : runHead s' = .top) :
    HeadStep (a, s) (a, s') := by
  simp [HeadStep, h, h']

theorem HeadStep.wrapLast {g : Tm → Tm} (hg : ∀ a s s', HeadStep (a, g s) (a, g s'))
    {F F' : ComponentTag × Tm} (hF : HeadStep F F') : HeadStep (F.1, g F.2) (F'.1, g F'.2) := by
  rw [hF.1]; exact hg _ _ _

theorem wrap_top {g : Tm → Tm} (hg : ∀ s, runHead (g s) = .top) {c : ComponentTag} {P : List (ComponentTag × Tm)}
    (h : ∃ init s, P = init ++ [(c, s)]) : ∃ init s, wrap g P = init ++ [(c, s)] ∧ runHead s = .top := by
  obtain ⟨init, s, rfl⟩ := h
  exact ⟨init, g s, wrap_snoc, hg s⟩

theorem pathArgs_top {c : ComponentTag} :
    ∀ {xs : List Tm} (k : List Tm → Tm), (∀ ys, runHead (k ys) = .top) →
      ∃ init s, pathArgs c k xs = init ++ [(c, s)] ∧ runHead s = .top
  | [], k, hk => ⟨[], k [], rfl, hk []⟩
  | a :: as, k, hk => by
    simp only [pathArgs]
    split
    · exact wrap_top (fun _ => hk _) (path_last a c)
    · exact pathArgs_top _ (fun _ => hk _)

/-- **The top segment is no run**: the last entry of a path. -/
theorem path_top (t : Tm) (c : ComponentTag) : ∃ init s, path c t = init ++ [(c, s)] ∧ runHead s = .top := by
  cases t
  all_goals simp only [path]
  all_goals repeat' split
  all_goals first
    | exact ⟨[], _, rfl, rfl⟩
    | exact ⟨[_], _, rfl, rfl⟩
    | exact ⟨_, _, rfl, rfl⟩
    | exact wrap_top (fun _ => rfl) (path_last _ _)
    | exact pathArgs_top _ (fun _ => rfl)

theorem mapLast_dropLast {α : Type} {g : α → α} : ∀ P : List α, (mapLast g P).dropLast = P.dropLast
  | [] => rfl
  | [_] => rfl
  | x :: y :: xs => by
    rw [mapLast_cons_cons, List.dropLast_cons_of_ne_nil (by cases xs <;> simp [mapLast]),
      List.dropLast_cons_of_ne_nil (by simp), mapLast_dropLast (y :: xs)]

theorem wrap_dropLast {g : Tm → Tm} (P : List (ComponentTag × Tm)) : (wrap g P).dropLast = P.dropLast :=
  mapLast_dropLast P

theorem pathArgs_goto {c : ComponentTag} :
    ∀ {xs : List Tm} (k : List Tm → Tm),
      (∀ a ∈ xs, ∀ c, free true a = true → ∀ p ∈ (path c a).dropLast, IsGoto p) →
      (∀ a ∈ xs, free true a = true) → ∀ p ∈ (pathArgs c k xs).dropLast, IsGoto p
  | [], k, _, _ => by simp [pathArgs]
  | a :: as, k, ih, h => by
    simp only [pathArgs]
    split
    · rw [wrap_dropLast]; exact ih a List.mem_cons_self c (h a List.mem_cons_self)
    · exact pathArgs_goto _ (fun x hx => ih x (List.mem_cons_of_mem _ hx)) (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **A pending term's runs are runs not yet entered**: every entry of its
path but the top segment. -/
theorem pf_goto : ∀ (t : Tm), free true t = true → ∀ c, ∀ p ∈ (path c t).dropLast, IsGoto p := by
  intro t
  induction t using Tm.induct
  all_goals intro h c
  all_goals simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true] at h
  all_goals simp only [path]
  all_goals (repeat' split) <;> (try rw [wrap_dropLast]) <;>
    first
      | (simp; done)
      | (simp [IsGoto, runHead]; done)
      | (apply pathArgs_goto <;> grind)
      | grind

/-- **The shape of a pending term's path**: runs not yet entered, at most
one, then the top segment. -/
theorem pf_shape {t : Tm} (h : free true t = true) (c : ComponentTag) :
    ∃ init s, path c t = init ++ [(c, s)] ∧ runHead s = .top ∧ init.length ≤ 1 ∧ ∀ p ∈ init, IsGoto p := by
  obtain ⟨init, s, hl, hs⟩ := path_top t c
  have hi := pf_goto t h c
  rw [hl, List.dropLast_concat] at hi
  exact ⟨init, s, hl, hs, init_short hl (hl ▸ pf_path t h c), hi⟩

/-! ### A step's change of the runs -/

theorem PathRuns.wrap {P P' : List (ComponentTag × Tm)} (g : Tm → Tm) (hg : ∀ a s s', HeadStep (a, g s) (a, g s'))
    (h : PathRuns P P') : PathRuns (ReadOnly.wrap g P) (ReadOnly.wrap g P') := by
  rcases h with ⟨new, F, F', rest, rfl, rfl, ht, hn, hgo⟩ | ⟨new, F, G, G', rest, rfl, rfl, ht, hn, hgo⟩
  · by_cases hr : rest = []
    · subst hr
      refine .inl ⟨new, (F.1, g F.2), (F'.1, g F'.2), [], rfl, ?_, ht.wrapLast hg, hn, hgo⟩
      simp only [ReadOnly.wrap, mapLast_append (List.cons_ne_nil _ _)]; rfl
    · refine .inl ⟨new, F, F', ReadOnly.wrap g rest, ?_, ?_, ht, hn, hgo⟩
      · simp only [ReadOnly.wrap, mapLast_cons hr]
      · simp only [ReadOnly.wrap, mapLast_append (List.cons_ne_nil _ _), mapLast_cons hr]
  · by_cases hr : rest = []
    · subst hr
      refine .inr ⟨new, F, (G.1, g G.2), (G'.1, g G'.2), [], rfl, ?_, ht.wrapLast hg, hn, hgo⟩
      simp only [ReadOnly.wrap, mapLast_append (List.cons_ne_nil _ _)]; rfl
    · refine .inr ⟨new, F, G, G', ReadOnly.wrap g rest, ?_, ?_, ht, hn, hgo⟩
      · simp only [ReadOnly.wrap, mapLast_cons (List.cons_ne_nil _ _), mapLast_cons hr]
      · simp only [ReadOnly.wrap, mapLast_append (List.cons_ne_nil _ _), mapLast_cons hr]

theorem PathRuns.append {P P' : List (ComponentTag × Tm)} (Q : List (ComponentTag × Tm)) (h : PathRuns P P') :
    PathRuns (P ++ Q) (P' ++ Q) := by
  rcases h with ⟨new, F, F', rest, rfl, rfl, ht, hn, hg⟩ | ⟨new, F, G, G', rest, rfl, rfl, ht, hn, hg⟩
  · exact .inl ⟨new, F, F', rest ++ Q, rfl, by simp, ht, hn, hg⟩
  · exact .inr ⟨new, F, G, G', rest ++ Q, rfl, by simp, ht, hn, hg⟩

/-- **A step inside an evaluation context that is no run**, the context's
term with a value at the position pending. -/
theorem PathRuns.ctx {c : ComponentTag} {a a' A A' : Tm} {g : Tm → Tm}
    (hrel : PathRuns (path c a) (path c a')) (hA : path c A = ReadOnly.wrap g (path c a))
    (hA' : isVal a' = false → path c A' = ReadOnly.wrap g (path c a'))
    (hpf : isVal a' = true → free true A' = true) (hg : ∀ s, runHead (g s) = .top) :
    PathRuns (path c A) (path c A') := by
  cases hv : isVal a'
  · rw [hA, hA' hv]; exact hrel.wrap g (fun _ s s' => HeadStep.top (hg s) (hg s'))
  · rw [path_val hv] at hrel
    obtain ⟨init, s, hl, hs, hi, hgo⟩ := pf_shape (hpf hv) c
    rw [hA, hl]
    rcases hrel with ⟨new, F, F', rest, hP, hP', ht, -⟩ | ⟨new, F, G, G', rest, hP, hP', ht, -⟩
    · obtain ⟨rfl, rfl, rfl⟩ : new = [] ∧ F' = (c, a') ∧ rest = [] := by
        cases new with
        | nil => simp at hP'; exact ⟨rfl, hP'.1.symm, hP'.2⟩
        | cons _ _ => simp at hP'
      rw [hP]
      have hc : c = F.1 := ht.1
      refine .inl ⟨init, (F.1, g F.2), (c, s), [], rfl, by simp, ?_, hi, hgo⟩
      rw [hc]; exact HeadStep.top (hg _) hs
    · obtain ⟨rfl, rfl, rfl⟩ : new = [] ∧ G' = (c, a') ∧ rest = [] := by
        cases new with
        | nil => simp at hP'; exact ⟨rfl, hP'.1.symm, hP'.2⟩
        | cons _ _ => simp at hP'
      rw [hP]
      have hc : c = G.1 := ht.1
      refine .inr ⟨init, F, (G.1, g G.2), (c, s), [], rfl, by simp, ?_, hi, hgo⟩
      rw [hc]; exact HeadStep.top (hg _) hs

/-- A step of a redex outside runs to a pending term. -/
theorem PathRuns.base {c : ComponentTag} {t t' : Tm} (h : (path c t).length = 1) (h' : free true t' = true) :
    PathRuns (path c t) (path c t') := by
  obtain ⟨init, s, hl, hs⟩ := path_top t c
  have : init = [] := by
    have := congrArg List.length hl
    rw [h] at this; simpa using this
  subst this
  obtain ⟨init', s', hl', hs', hi, hgo⟩ := pf_shape h' c
  rw [hl, hl']
  exact .inl ⟨init', (c, s), (c, s'), [], rfl, rfl, HeadStep.top hs hs', hi, hgo⟩

/-- A step at a frame that pops it to a pending term. -/
theorem PathRuns.framePop {c : ComponentTag} {t t' : Tm} {F : ComponentTag × Tm} (h : path c t = [F, (c, hole)])
    (h' : free true t' = true) : PathRuns (path c t) (path c t') := by
  obtain ⟨init, s, hl, hs, hi, hgo⟩ := pf_shape h' c
  rw [h, hl]
  exact .inr ⟨init, F, (c, hole), (c, s), [], rfl, rfl, HeadStep.top rfl hs, hi, hgo⟩

/-- A frame becoming a run of its code. -/
theorem PathRuns.frameGoto {c : ComponentTag} {t u : Tm} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {l : Nat} {L L' : List Tm} {d d' : Tm}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    (h : path c t = [(comp, .frame E K u L d k x comp), (c, hole)]) :
    PathRuns (path c t) (path c (.goto E K l L' d' comp)) :=
  .inl ⟨[], _, (comp, .goto E K l L' d' comp), [(c, hole)], h, rfl, by simp [HeadStep, runHead], by simp, by simp⟩

theorem step_runs_wf {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    wf t = true → HeapFree h → wf t' = true ∧ HeapFree h' ∧ ∀ c, PathRuns (path c t) (path c t') := by
  induction hs
  case callArg hf hr ha hpre hs ih =>
    intro hw hh
    simp only [wf, hf, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    have hna := not_val_of_step hs
    obtain ⟨wa, hoth⟩ := wfArgs_split hw.2 ha hpre hna
    obtain ⟨w', hh', hp⟩ := ih wa hh
    have ho := set_others (b := ‹Tm›) hoth
    refine ⟨?_, hh', fun c => PathRuns.ctx (hp c) (by simp only [path, hf, hr]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path, hf, hr]; exact pathArgs_set _ ha hpre hv) (fun hv => ?_) (by intro _; rfl)⟩
    · simp only [wf, hf, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true]
      exact ⟨hw.1, wfArgs_mk (set_at ha) (set_pre hpre) w' ho⟩
    · simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true]
      exact ⟨hw.1, all_set ho (pf_of_wf_val hv w')⟩
  case constructArg hf ha hpre hs ih =>
    intro hw hh
    simp only [wf, hf, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    have hna := not_val_of_step hs
    obtain ⟨wa, hoth⟩ := wfArgs_split hw.2 ha hpre hna
    obtain ⟨w', hh', hp⟩ := ih wa hh
    have ho := set_others (b := ‹Tm›) hoth
    refine ⟨?_, hh', fun c => PathRuns.ctx (hp c) (by simp only [path, hf]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path, hf]; exact pathArgs_set _ ha hpre hv) (fun hv => ?_) (by intro _; rfl)⟩
    · simp only [wf, hf, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true]
      exact ⟨hw.1, wfArgs_mk (set_at ha) (set_pre hpre) w' ho⟩
    · simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true]
      exact ⟨hw.1, all_set ho (pf_of_wf_val hv w')⟩
  case arrArg ha hpre hs ih =>
    intro hw hh
    simp only [wf] at hw
    have hna := not_val_of_step hs
    obtain ⟨wa, hoth⟩ := wfArgs_split hw ha hpre hna
    obtain ⟨w', hh', hp⟩ := ih wa hh
    have ho := set_others (b := ‹Tm›) hoth
    refine ⟨?_, hh', fun c => PathRuns.ctx (hp c) (by simp only [path]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path]; exact pathArgs_set _ ha hpre hv) (fun hv => ?_) (by intro _; rfl)⟩
    · simp only [wf]
      exact wfArgs_mk (set_at ha) (set_pre hpre) w' ho
    · simp only [free, frees_eq, List.all_eq_true]
      exact all_set ho (pf_of_wf_val hv w')
  case makeArg c ns inits i h₀ h₁ a a' ha hpre hs ih =>
    intro hw hh
    have hna := not_val_of_step hs
    have hcode : ∀ xs, wfArgs xs = true → wf (.makeAt c ns xs) = true := by
      intro xs hx; cases c <;> simp_all [wf]
    have hcode' : ∀ xs, (∀ x ∈ xs, free true x = true) → free true (.makeAt c ns xs) = true := by
      intro xs hx; cases c <;> simp_all [wf, free]
    have hw' : wfArgs inits = true := by
      cases c <;> simp only [wf, Bool.and_eq_true] at hw <;> first | exact hw | exact hw.2
    obtain ⟨wa, hoth⟩ := wfArgs_split hw' ha hpre hna
    obtain ⟨w', hh', hp⟩ := ih wa hh
    have ho := set_others (b := a') hoth
    exact ⟨hcode _ (wfArgs_mk (set_at ha) (set_pre hpre) w' ho), hh', fun c' => PathRuns.ctx (hp c')
      (by simp only [path]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path]; exact pathArgs_set _ ha hpre hv)
      (fun hv => hcode' _ (all_set ho (pf_of_wf_val hv w'))) (by intro _; rfl)⟩
  case letV ha =>
    intro hw hh
    simp only [wf, ha, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    have hpf := subst_free (free_val' ha hw.1) _ 0 true hw.2
    exact ⟨pf_wf _ hpf, hh, fun c => PathRuns.base (by simp [path, ha]) hpf⟩
  case gotoEnter E l e K k x _ L d comp he hK =>
    intro hw hh
    simp only [wf, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true] at hw
    have henv : ∀ i, free false (envOf L d i) = true := fun i => by
      rcases getD_mem_or L i d with h | h
      · simp only [envOf]; exact hw.1.2 _ h
      · simp only [envOf]; rw [h]; exact hw.2
    have hnr := instantiate_free henv e 0 false (hw.1.1 e (List.mem_of_getElem? he))
    refine ⟨?_, hh, fun c => ?_⟩
    · simp only [wf, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true]
      exact ⟨hw, pf_wf _ (free_mono _ hnr)⟩
    · obtain ⟨init, s, hl⟩ := path_last (instantiate 0 (envOf L d) e) comp
      have : init = [] := by
        have h1 := nr_path _ hnr comp
        rw [hl] at h1; simpa using h1
      subst this
      refine .inl ⟨[], (comp, .goto E K l L d comp), (comp, .frame E K s L d k x comp), [(c, hole)], rfl, ?_,
        ⟨rfl, ?_⟩, by simp, by simp⟩
      · simp only [path, hl, wrap_snoc, List.append_assoc]; rfl
      · simp only [runHead, NodeOf]
        simp [hK, he]
  case frameRet hv =>
    intro hw hh
    simp only [wf, Bool.and_eq_true] at hw
    exact ⟨hw.2, hh, fun c => PathRuns.framePop (path_frame (path_val hv)) (pf_of_wf_val hv hw.2)⟩
  case frameHandle hr =>
    intro hw hh
    simp only [wf, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true] at hw
    have hv := raises_free hr hw.2
    refine ⟨?_, hh, fun c => PathRuns.frameGoto (path_frame (raises_path hr _))⟩
    simp only [wf, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true]
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
    simp only [wf, runParts, Bool.and_eq_true] at hw
    have hv := raises_free hr hw.2
    have hval := sourceVal_isVal (raises_sourceVal hr)
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.framePop (path_frame (raises_path hr _)) ?pf⟩
    case pf => simp only [free]; exact free_mono _ hv
  case callBound =>
    rename_i hr hargs
    intro hw hh
    simp only [wf, isVal_objAt, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true, free, frees_eq,
      List.all_eq_true] at hw
    have hpa := wfArgs_vals hw.2 hargs
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base ?len ?pf⟩
    case len => simp [path, hr, pathArgs_vals _ hargs]
    case pf =>
      simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append]
      grind [free_mono]
  case callSpread =>
    rename_i hf hr heq hpre hre
    intro hw hh
    simp only [wf, hf, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    rw [heq] at hw
    obtain ⟨-, hp1, hp2⟩ := wfArgs_mid isVal_spread hw.2 hpre
    have hvs := readElems_free hh hre
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base ?len ?pf⟩
    case pf =>
      simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append]
      grind [free_mono]
    case len =>
      subst heq; simp [path, *]; rw [pathArgs_append _ _ hpre]; simp [pathArgs, path, wrap, mapLast]
  case constructSpread =>
    rename_i hf heq hpre hre
    intro hw hh
    simp only [wf, hf, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    rw [heq] at hw
    obtain ⟨-, hp1, hp2⟩ := wfArgs_mid isVal_spread hw.2 hpre
    have hvs := readElems_free hh hre
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base ?len ?pf⟩
    case pf =>
      simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append]
      grind [free_mono]
    case len =>
      subst heq; simp [path, *]; rw [pathArgs_append _ _ hpre]; simp [pathArgs, path, wrap, mapLast]
  case arrSpread =>
    rename_i heq hpre hre
    intro hw hh
    simp only [wf] at hw
    rw [heq] at hw
    obtain ⟨-, hp1, hp2⟩ := wfArgs_mid isVal_spread hw hpre
    have hvs := readElems_free hh hre
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base ?len ?pf⟩
    case pf =>
      simp only [free, frees_eq, List.all_eq_true, List.mem_append]
      grind [free_mono]
    case len =>
      subst heq; simp [path]; rw [pathArgs_append _ _ hpre]; simp [pathArgs, path, wrap, mapLast]
  case makeFields c ns vs h₀ hvs hlen =>
    intro hw hh
    have hargs : wfArgs vs = true := by
      cases c <;> simp only [wf, Bool.and_eq_true] at hw <;> first | exact hw | exact hw.2
    have hnr : ∀ v ∈ vs, free false v = true := fun v hv => free_val' (hvs v hv) (wfArgs_vals hargs hvs v hv)
    refine ⟨pf_wf _ ?pf, (hh.append hnr).append (by simp [free]), fun c' => PathRuns.base ?len ?pf⟩
    case pf => cases c <;> simp_all [wf, free]
    case len => simp [path, pathArgs_vals _ hvs]
  case readField =>
    rename_i hl hv
    intro _ hh
    exact ⟨pf_wf _ (free_mono _ (hh.get hv)), hh, fun c => PathRuns.base (by simp [path])
      (free_mono _ (hh.get hv))⟩
  case readProto =>
    rename_i h1 h2 hp
    intro _ hh
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base (by simp [path]) ?pf⟩
    case pf => simp only [free]; exact free_mono _ (hh.get hp)
  case indexField =>
    rename_i hk hl hv
    intro _ hh
    exact ⟨pf_wf _ (free_mono _ (hh.get hv)), hh, fun c => PathRuns.base (by simp [path, propertyKey_val hk])
      (free_mono _ (hh.get hv))⟩
  case indexProto =>
    rename_i hk h1 h2 hp
    intro hw hh
    simp only [wf, isVal_objAt, propertyKey_val hk, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base (by simp [path, propertyKey_val hk]) ?pf⟩
    case pf => simp only [free, Bool.and_eq_true]; exact ⟨free_mono _ (hh.get hp), hw.2⟩
  case indexMissing =>
    rename_i hk h1 h2
    intro _ hh
    exact ⟨rfl, hh, fun c => PathRuns.base (by simp [path, propertyKey_val hk]) (by first | rfl | simp [free, thrownError])⟩
  case writeField =>
    rename_i hv hl hlt
    intro hw hh
    simp only [wf, isVal_objAt, hv, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    exact ⟨rfl, hh.set (free_val' hv hw.2), fun c => PathRuns.base (by simp [path, hv]) (by first | rfl | simp [free, thrownError])⟩
  case testV =>
    rename_i hv
    intro _ hh
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base (by simp [path, hv]) ?pf⟩
    case pf => split <;> rfl
  case arithV =>
    rename_i hb
    intro _ hh
    obtain ⟨ha, hb', hres⟩ := binop_result hb
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base (by simp [path, ha, hb']) ?pf⟩
    case pf => rcases hres with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  case arrAlloc =>
    rename_i hvs hlen
    intro hw hh
    simp only [wf] at hw
    exact ⟨rfl, hh.append fun v hv => free_val' (hvs v hv) (wfArgs_vals hw hvs v hv),
      fun c => PathRuns.base (by simp [path, pathArgs_vals _ hvs]) (by first | rfl | simp [free, thrownError])⟩
  case arrAllocThrow =>
    rename_i hvs hlen
    intro _ hh
    exact ⟨rfl, hh.append (by simp [free]), fun c => PathRuns.base (by simp [path, pathArgs_vals _ hvs])
      (by first | rfl | simp [free, thrownError])⟩
  case elemRead =>
    rename_i hl hv
    intro _ hh
    exact ⟨pf_wf _ (free_mono _ (hh.get hv)), hh, fun c => PathRuns.base (by simp [path])
      (free_mono _ (hh.get hv))⟩
  case setPresent =>
    rename_i hv hl hlt
    intro hw hh
    simp only [wf, isVal_arr, isVal_num, hv, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    exact ⟨rfl, hh.set (free_val' hv hw.2), fun c => PathRuns.base (by simp [path, hv]) (by first | rfl | simp [free, thrownError])⟩
  case setGrow =>
    rename_i hv hk hl
    intro hw hh
    simp only [wf, isVal_arr, isVal_num, hv, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    exact ⟨rfl, hh.append (by simpa using free_val' hv hw.2), fun c => PathRuns.base (by simp [path, hv])
      (by first | rfl | simp [free, thrownError])⟩
  case lenStrThrow =>
    intro _ hh
    exact ⟨rfl, hh.append (by simp [free]), fun c => PathRuns.base (by simp [path]) (by first | rfl | simp [free, thrownError])⟩
  case elemStr =>
    intro _ hh
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base (by simp [path]) ?pf⟩
    case pf => simp only [codeUnitAt]; split <;> rfl
  case arithThrow =>
    rename_i hb
    intro _ hh
    obtain ⟨ha, hb'⟩ := binopThrows_values hb
    exact ⟨rfl, hh.append (by simp [free]), fun c => PathRuns.base (by simp [path, ha, hb'])
      (by first | rfl | simp [free, thrownError])⟩
  case mergeV =>
    rename_i ha hb hm
    intro _ hh
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base (by simp [path, ha, hb]) ?pf⟩
    case pf =>
      simp only [free, frees_eq, List.all_eq_true]
      exact nr_frees_true (mergeParts_free hh hm)
  case makeKeyV =>
    rename_i ha hk
    intro hw hh
    simp only [wf, propertyKey_val hk, ha, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base (by simp [path, propertyKey_val hk, ha]) ?pf⟩
    case pf => simp [free, hw.2]
  case callGraph =>
    rename_i hr hargs hbind
    intro hw hh
    simp only [wf, isVal_objAt, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true, free, frees_eq,
      List.all_eq_true] at hw
    have hpa := wfArgs_vals hw.2 hargs
    have hra := free_val' hr hw.1.2
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base (by simp [path, hr, pathArgs_vals _ hargs]) ?pf⟩
    case pf =>
      exact graphEntry_free hw.1.1.1 hw.1.1.2 (by simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true]; exact hw.1.1)
        hra (fun x hx => free_val' (hargs x hx) (hpa x hx))
  case constructGraph =>
    rename_i hargs
    intro hw hh
    simp only [wf, isVal_objAt, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true, free, frees_eq,
      List.all_eq_true] at hw
    have hpa := wfArgs_vals hw.2 hargs
    refine ⟨pf_wf _ ?pf, hh, fun c => PathRuns.base (by simp [path, pathArgs_vals _ hargs]) ?pf⟩
    case pf =>
      exact graphEntry_free hw.1.1 hw.1.2 (by simp only [free, frees_eq, Bool.and_eq_true, List.all_eq_true]; exact hw.1)
        rfl (fun x hx => free_val' (hargs x hx) (hpa x hx))
  all_goals try (
    intro hw hh
    simp only [wf, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true] at hw
    refine ⟨?_, hh, fun c => PathRuns.frameGoto (path_frame (path_val (by first | assumption | rfl)))⟩
    simp only [wf, runParts, Bool.and_eq_true, frees_eq, List.all_eq_true]
    have hv : ∀ v, isVal v = true → wf v = true → free false v = true := fun v hv hw => nr_of_wf_val hv hw
    refine ⟨⟨hw.1.1.1, (envMap_free ?_ hw.1.2).1⟩, (envMap_free ?_ hw.1.2).2⟩ <;>
      first
        | exact hw.1.1.2
        | (intro x hx; rcases List.mem_cons.mp hx with rfl | hx
           · first | rfl | exact hv _ ‹_› hw.2
           · exact hw.1.1.2 x hx)
    done)
  case frameC ih =>
    intro hw hh
    simp only [wf, Bool.and_eq_true] at hw
    obtain ⟨w', hh', hp⟩ := ih hw.2 hh
    refine ⟨by simp only [wf, Bool.and_eq_true]; exact ⟨hw.1, w'⟩, hh', fun c => ?_⟩
    simp only [path]
    refine PathRuns.append _ (PathRuns.wrap _ ?_ (hp _))
    intro _ _ _
    simp [HeadStep, runHead]
  all_goals try (
    rename_i ih
    intro hw hh
    have hna := not_val_of_step ‹Step _ _ _ _›
    simp [wf, *] at hw
    obtain ⟨w', hh', hp⟩ := ih (by simp_all) hh
    refine ⟨?_, hh', fun c => PathRuns.ctx (hp c) (by simp [path, *] <;> rfl) (fun hv => by simp [path, *] <;> rfl)
      (fun hv => ?_) (by intro _; rfl)⟩
    · simp only [wf]; (repeat' split) <;> simp_all [pf_of_wf_val, pf_wf, wfArgs_of_pf]
    · simp_all [free, pf_of_wf_val]
    done)
  -- A redex to a pending term, the path entering at most one run.
  all_goals try (
    intro hw hh
    refine ⟨pf_wf _ ?pf, ?heap, fun c => PathRuns.base ?len ?pf⟩
    case pf => simp_all [wf, free]
    case heap => first | exact hh | skip
    case len => simp [path, *]
    done)
end

/-! ## Every step keeps well-formedness -/

/-- **A change of the runs is a change of the path pushing at most one
frame** (proved). -/
theorem PathRuns.step1 {P P' : List (ComponentTag × Tm)} (h : PathRuns P P') : PathStep1 P P' := by
  rcases h with ⟨new, F, F', rest, hP, hP', hF, hn, -⟩ | ⟨new, F, G, G', rest, hP, hP', hG, hn, -⟩
  · exact .inl ⟨new, F, F', rest, hP, hP', hF.1, hn⟩
  · exact .inr ⟨new, F, G, G', rest, hP, hP', hG.1, hn⟩

/-- **Every step keeps a well-formed term and a heap free of runs, and
pushes at most one frame on the path** (proved, `step_runs_wf`). -/
theorem step_wf {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    wf t = true → HeapFree h → wf t' = true ∧ HeapFree h' ∧ ∀ c, PathStep1 (path c t) (path c t') :=
  fun hw hh =>
    let h := step_runs_wf hs hw hh
    ⟨h.1, h.2.1, fun c => (h.2.2 c).step1⟩


/-! ## The call discipline -/

theorem blocks_cons_cons (a b : Bool) (R : List Bool) :
    blocks (a :: b :: R) = (if a && !b then 1 else 0) + blocks (b :: R) := rfl

/-- **The blocks across a step of the path**: with its innermost element
`f` kept and at most one element pushed, or popped and at most one pushed,
the number of blocks of `true` moves by at most one, up when `f` is
`false` and down when it is `true`. -/
theorem blocks_step {f : Bool} {T T' : List Bool}
    (h : (∃ N R, T = f :: R ∧ T' = N ++ f :: R ∧ N.length ≤ 1) ∨
      (∃ N g R, T = f :: g :: R ∧ T' = N ++ g :: R ∧ N.length ≤ 1)) :
    (f = false → blocks T ≤ blocks T' ∧ blocks T' ≤ blocks T + 1) ∧
    (f = true → blocks T' ≤ blocks T ∧ blocks T ≤ blocks T' + 1) := by
  rcases h with ⟨N, R, rfl, rfl, hN⟩ | ⟨N, g, R, rfl, rfl, hN⟩
  · match N, hN with
    | [], _ => simp
    | [n], _ =>
      simp only [List.cons_append, List.nil_append, blocks_cons_cons]
      cases n <;> cases f <;> simp <;> omega
  · match N, hN with
    | [], _ =>
      simp only [List.nil_append, blocks_cons_cons]
      cases f <;> cases g <;> simp <;> omega
    | [n], _ =>
      simp only [List.cons_append, List.nil_append, blocks_cons_cons]
      cases n <;> cases f <;> cases g <;> simp <;> omega

/-- **The call discipline of a step** (`Disc`): a step of a well-formed term
on a heap free of runs keeps or raises by one the calls of `C` active when
its active frame runs no code of `C`, and keeps or lowers them by one when
it does, at every component of every family. -/
theorem disc_of_wf {F : Family} {C : Nat} {c : ComponentTag} {x y : Conf}
    (hs : Step x.s.h x.t y.s.h y.t) (hw : wf x.t = true) (hh : HeapFree x.s.h) : Disc F C c x y := by
  have hp := (step_wf hs hw hh).2.2 c
  let tg : ComponentTag × Tm → Bool := fun p => F.ofC C p.1
  obtain ⟨F₀, hF, hb⟩ : ∃ F₀ : ComponentTag × Tm, (path c x.t).head? = some F₀ ∧
      ((∃ N R, (path c x.t).map tg = tg F₀ :: R ∧ (path c y.t).map tg = N ++ tg F₀ :: R ∧ N.length ≤ 1) ∨
        (∃ N g R, (path c x.t).map tg = tg F₀ :: g :: R ∧ (path c y.t).map tg = N ++ g :: R ∧ N.length ≤ 1)) := by
    rcases hp with ⟨new, F₁, F', rest, hP, hP', ht, hn⟩ | ⟨new, F₁, G, G', rest, hP, hP', ht, hn⟩
    · refine ⟨F₁, by rw [hP]; rfl, .inl ⟨new.map tg, rest.map tg, by rw [hP]; rfl, ?_, by simpa using hn⟩⟩
      rw [hP']; simp [tg, ht]
    · refine ⟨F₁, by rw [hP]; rfl, .inr ⟨new.map tg, tg G, rest.map tg, by rw [hP]; rfl, ?_, by simpa using hn⟩⟩
      rw [hP']; simp [tg, ht]
  have hd := blocks_step hb
  have hact : activeTag c x.t = F₀.1 := by simp [activeTag, hF]
  have ho : Outside F C c x ↔ tg F₀ = false := by
    simp [Outside, OutsideAt, hact, tg, Family.ofC]
  unfold Disc depthC
  refine ⟨fun h => hd.1 (ho.mp h), fun h => hd.2 ?_⟩
  cases htg : tg F₀
  · exact (h (ho.mpr htg)).elim
  · rfl

/-! ## Executions of well-formed terms -/

/-- **A well-formed configuration**: its term well formed, its heap free of
runs. -/
def Conf.WF (x : Conf) : Prop := wf x.t = true ∧ HeapFree x.s.h

/-- **Every actual step keeps a configuration well formed and obeys the
call discipline.** -/
theorem AStep.wf_disc {F : Family} {C : Nat} {c : ComponentTag} {x y : Conf} (hs : AStep x y) (hx : x.WF) :
    y.WF ∧ Disc F C c x y :=
  let h := step_wf hs.step hx.1 hx.2
  ⟨⟨h.1, h.2.1⟩, disc_of_wf hs.step hx.1 hx.2⟩

/-- A term free of runs, a source program's term among them, is well
formed. -/
theorem wf_of_source {t : Tm} (ht : free false t = true) : wf t = true := pf_wf t (free_mono t ht)

/-! ## A safe term's steps are actual steps -/

/-- **The world of a safe term's step** (`AStep.adm`'s source): from a term
safe at budget `n + 1`, the calculus's step (deterministic, `Step_det`) is
the one `Safe` witnesses, so it reaches a world `W'` at budget `n` that
extends `W` truncated (`WorldReach`), is admissible, holds the new heap
(`HeapOk`) and at which the new term is safe. -/
theorem safe_step_world {Ξ T : Fam} {n : Nat} {W : WorldT (n + 1)} {h h' : Heap} {t t' : Tm}
    (hs : Safe Ξ T (n + 1) W h t) (hstep : Step h t h' t') :
    ∃ W' : WorldT n, WorldReach W W' ∧ WorldAdm W' ∧ HeapOk n W' h' ∧ Safe Ξ T n W' h' t' := by
  obtain ⟨-, (⟨hv, -⟩ | hth) | ⟨W', h₂, t₂, hx, hadm, hst, hok, hs'⟩⟩ := hs
  · exact (value_no_step hv hstep).elim
  · exact (hth.no_step hstep).elim
  · obtain ⟨rfl, rfl⟩ := Step_det hst hstep
    exact ⟨W', ⟨Nat.le_succ n, hx⟩, hadm, hok, hs'⟩

/-- **A safe term's step is an actual step**: the configuration after it,
at the world `Safe` gives, with the step's admissible world transition.
`AStep.adm` is the first premise of `Safe`'s step clause. -/
theorem astep_of_safe {Ξ T : Fam} {x : Conf} {n : Nat} (hn : 0 < n) (hx : x.s.n = n + 1)
    (hs : Safe Ξ T x.s.n x.s.W x.s.h x.t) {h' : Heap} {t' : Tm} (hstep : Step x.s.h x.t h' t') :
    ∃ y : Conf, y.s.h = h' ∧ y.t = t' ∧ AStep x y ∧ Safe Ξ T y.s.n y.s.W y.s.h y.t := by
  obtain ⟨⟨m, W, h, pos, adm, ok⟩, t, ht⟩ := x
  simp only at hx hs hstep
  subst hx
  obtain ⟨W', hr, hadm', hok', hs'⟩ := safe_step_world hs hstep
  exact ⟨⟨⟨n, W', h', hn, hadm', hok'⟩, t', Safe.refs hs'⟩, rfl, rfl, ⟨hstep, hr⟩, hs'⟩

/-- **A step of a well-formed execution with its ghost**: the call
discipline of `XStep` holds of the step (`disc_of_wf`). -/
theorem XStep.of_wf {F : Family} {C : Nat} {c : ComponentTag} {tv : TypeView} {Θ : Protocol (F.at C)}
    {chk : Conf → Conf → CheckData (F.at C) tv} {a b : Conf × Ghost (F.at C)} (hs : AStep a.1 b.1) (hw : a.1.WF)
    (hg : b.2 = Ghost.next F C c chk a.1 b.1 a.2) (hh : StepHyp (c := c) Θ chk a.1 b.1 a.2) :
    XStep F C c Θ chk a b :=
  ⟨hs, disc_of_wf hs.step hw.1 hw.2, hg, hh⟩

/-! ## The call structure on re-entry, throw and return

Computed checks of the number of calls of a component active (`blocks` of
the path's tags, the component tagged `some 0`) and of the active frame,
at the terms of a call from outside code, a callback, a re-entry, its
return or throw, and the returns to the member and to the top level: a
top level outside the component (`none`) and a module of the component
(`some 0`). The last check is the counter-model for terms that are not
well formed: a binding whose body holds two nested runs enters both in
one step, two calls at once. -/

/-- The number of calls of the component `some 0` active at a term. -/
def callsAt (c : ComponentTag) (t : Tm) : Nat := blocks ((path c t).map fun p => p.1 == some 0)

/-- Whether the active frame runs the component `some 0`. -/
def activeIn (c : ComponentTag) (t : Tm) : Bool := activeTag c t == some 0

/-- A run not yet entered, of code tagged `comp`. -/
def runAt (comp : ComponentTag) : Tm := .goto [] [] 0 [] .nul comp

/-- A frame of code tagged `comp` running `t`. -/
def frameAt (comp : ComponentTag) (t : Tm) : Tm := .frame [] [] t [] .nul .ret none comp

-- A top level outside the component: entry, callback, re-entry, its
-- return and its throw, the callback's return, the member's exit.
#guard callsAt none .nul == 0 && !activeIn none .nul
#guard callsAt none (runAt (some 0)) == 1 && activeIn none (runAt (some 0))
#guard callsAt none (frameAt (some 0) (runAt none)) == 1 && !activeIn none (frameAt (some 0) (runAt none))
#guard callsAt none (frameAt (some 0) (frameAt none (runAt (some 0)))) == 2
#guard callsAt none (frameAt (some 0) (frameAt none .nul)) == 1
#guard callsAt none (frameAt (some 0) (frameAt none (.throw .nul))) == 1
#guard callsAt none (frameAt (some 0) .nul) == 1 && activeIn none (frameAt (some 0) .nul)
-- A module of the component: its top level is a call active from the start.
#guard callsAt (some 0) .nul == 1 && activeIn (some 0) .nul
#guard callsAt (some 0) (runAt none) == 1 && !activeIn (some 0) (runAt none)
#guard callsAt (some 0) (frameAt none (runAt (some 0))) == 2
#guard callsAt (some 0) (frameAt none (.throw .nul)) == 1
-- Each of these terms is well formed.
#guard wf (frameAt (some 0) (frameAt none (runAt (some 0)))) && wf (frameAt (some 0) (frameAt none (.throw .nul)))
-- Not well formed: two nested runs under a binding, entered by one step.
#guard !wf (.letE .nul (frameAt (some 0) (frameAt none (runAt (some 0)))))
#guard callsAt none (.letE .nul (frameAt (some 0) (frameAt none (runAt (some 0))))) == 0 &&
  callsAt none (subst 0 .nul (frameAt (some 0) (frameAt none (runAt (some 0))))) == 2

/-- The step of the counter-model: a binding of a value. -/
theorem twoCalls_step :
    Step [] (.letE .nul (frameAt (some 0) (frameAt none (runAt (some 0))))) []
      (subst 0 .nul (frameAt (some 0) (frameAt none (runAt (some 0))))) :=
  .letV rfl

end Verification.TolerantFrames.ReadOnly
