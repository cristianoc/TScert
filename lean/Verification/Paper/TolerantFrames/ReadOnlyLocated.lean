import Verification.Paper.TolerantFrames.ReadOnlyRuns

/-! # Read-only handles: located reductions

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "Located
reductions"). The checks of a component read each step at the node of the
code that performs it. A run not yet entered (`Tm.goto`) carries its node's
label; a frame (`Tm.frame`) carries its code, environment, continuation and
handler, and no label. A located configuration carries one label per entry
of its evaluation path (`path`), a ghost the steps of the calculus thread:

- **The run of a path entry** (`runHead`): the top segment, a run not yet
  entered (its code, tag and label) or a frame (its code, tag, continuation
  and handler).
- **A step's change of the runs** (`PathRuns`, `step_runs`): a step of a
  well-formed term on a heap free of runs changes the innermost entry, or
  pops it and changes the one under it, and pushes at most one entry, a run
  not yet entered; the entry it changes keeps its tag and code
  (`HeadStep`): a frame stays a frame of the same code, continuation and
  handler, or becomes a run of the same code at a node (a continuation, a
  handler); a run not yet entered becomes a frame of its node's
  continuation and handler.
- **Labels agreeing with the path** (`LabelsOk`): one per entry, a run's
  own label, and for a frame a node of its code whose continuation and
  handler the frame runs.
- **A located step** (`LStep`): an actual step, the labels after it those of
  the entries pushed, the changed entry's kept unless it is a run at a node,
  the others unchanged (`relabel`). Its erasure is the step
  (`locatedStep_erase`), and every step from a located configuration lifts
  (`step_lift`), to labels agreeing with the path again: a call of a closure
  (a run pushed), a substitution (the entry changed in place), a normal
  return and a throw out of a frame (the entry popped) and the unwinding to
  a handler (a frame becoming a run at the handler's node).
- **The occurrence of a step** (`occ`): the code, tag and label of the
  innermost entry's run, and the entry's term, its position in the node's
  expression. Codes are identified by their content, so two identical
  bodies have the same occurrences, and a check of one is a check of the
  other. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

/-- **Every step changes the runs so** (proved): a step of a well-formed
term on a heap free of runs, at every top tag. -/
theorem step_runs {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') (hw : wf t = true) (hh : HeapFree h) :
    ∀ c, PathRuns (path c t) (path c t') :=
  (step_runs_wf hs hw hh).2.2

/-! ## Labels -/

/-- **The label of an entry agrees with its run**: a run not yet entered's
own; a node of a frame's code at which it runs. -/
def LabelAt (p : ComponentTag × Tm) (l : Nat) : Prop :=
  match runHead p.2 with
  | .top => True
  | .goto _ _ l' => l = l'
  | .frame m _ k x => NodeOf m l k x

/-- **Labels agreeing with the path**: one per entry, each agreeing with its
entry's run. -/
inductive LabelsOk : List (ComponentTag × Tm) → List Nat → Prop where
  | nil : LabelsOk [] []
  | cons {p : ComponentTag × Tm} {l : Nat} {P : List (ComponentTag × Tm)} {ls : List Nat} :
      LabelAt p l → LabelsOk P ls → LabelsOk (p :: P) (l :: ls)

/-- The label an entry gives itself, or `l`. -/
def labelOr (p : ComponentTag × Tm) (l : Nat) : Nat :=
  match runHead p.2 with
  | .goto _ _ l' => l'
  | _ => l

/-- **The labels after a step**: the pushed entries' own, the changed
entry's kept unless it is a run at a node, the others unchanged. -/
def Relabel (P P' : List (ComponentTag × Tm)) (ls ls' : List Nat) : Prop :=
  (∃ new F F' rest lF lrest, P = F :: rest ∧ P' = new ++ F' :: rest ∧ HeadStep F F' ∧ new.length ≤ 1 ∧
    (∀ p ∈ new, IsGoto p) ∧ ls = lF :: lrest ∧ ls' = new.map (labelOr · 0) ++ labelOr F' lF :: lrest) ∨
  (∃ new F G G' rest lF lG lrest, P = F :: G :: rest ∧ P' = new ++ G' :: rest ∧ HeadStep G G' ∧
    new.length ≤ 1 ∧ (∀ p ∈ new, IsGoto p) ∧ ls = lF :: lG :: lrest ∧
    ls' = new.map (labelOr · 0) ++ labelOr G' lG :: lrest)

/-! ## Located configurations and steps -/

/-- **A located configuration**: a configuration, the labels of its path's
entries (top segment tagged `c`). -/
structure Located where
  x : Conf
  ls : List Nat

/-- **A located step** at the top tag `c`: an actual step, the labels after
it the step's relabelling. -/
def LStep (c : ComponentTag) (a b : Located) : Prop :=
  AStep a.x b.x ∧ Relabel (path c a.x.t) (path c b.x.t) a.ls b.ls

/-- **A located step's erasure is the calculus's step** (proved). -/
theorem locatedStep_erase {c : ComponentTag} {a b : Located} (hs : LStep c a b) :
    Step a.x.s.h a.x.t b.x.s.h b.x.t :=
  hs.1.step

theorem labelAt_goto {p : ComponentTag × Tm} (hp : IsGoto p) (l : Nat) : LabelAt p (labelOr p l) := by
  obtain ⟨m, c, l', he⟩ := hp
  simp [LabelAt, labelOr, he]

theorem labelsOk_new {new : List (ComponentTag × Tm)} (hn : ∀ p ∈ new, IsGoto p) :
    LabelsOk new (new.map (labelOr · 0)) := by
  induction new with
  | nil => exact .nil
  | cons p ps ih =>
    exact .cons (labelAt_goto (hn p (.head _)) 0) (ih fun q hq => hn q (.tail _ hq))

/-- **A head step keeps a label agreeing** (proved): a run's own label is
its own; a frame entered from a run at a node runs at that node; a frame
kept keeps its node. -/
theorem labelAt_step {p p' : ComponentTag × Tm} {l : Nat} (hs : HeadStep p p') (hl : LabelAt p l) :
    LabelAt p' (labelOr p' l) := by
  obtain ⟨-, hs⟩ := hs
  unfold LabelAt at hl ⊢
  unfold labelOr
  revert hs hl
  cases runHead p.2 <;> cases runHead p'.2 <;> simp_all

theorem LabelsOk.cons_inv {p : ComponentTag × Tm} {P : List (ComponentTag × Tm)} {ls : List Nat}
    (h : LabelsOk (p :: P) ls) : ∃ l ls', ls = l :: ls' ∧ LabelAt p l ∧ LabelsOk P ls' := by
  cases h with
  | cons hp hP => exact ⟨_, _, rfl, hp, hP⟩

theorem labelsOk_append {P Q : List (ComponentTag × Tm)} {ls ms : List Nat} (h₁ : LabelsOk P ls)
    (h₂ : LabelsOk Q ms) : LabelsOk (P ++ Q) (ls ++ ms) := by
  induction h₁ with
  | nil => exact h₂
  | cons hp _ ih => exact .cons hp ih

/-- **Every step from a located configuration lifts** (proved): a step of a
well-formed term on a heap free of runs, from labels agreeing with the
path, is the erasure of a located step to labels agreeing with the path
again. -/
theorem step_lift {c : ComponentTag} {a : Located} {y : Conf} (hs : AStep a.x y) (hw : a.x.WF)
    (hl : LabelsOk (path c a.x.t) a.ls) :
    ∃ ls', LStep c a ⟨y, ls'⟩ ∧ LabelsOk (path c y.t) ls' := by
  rcases step_runs hs.step hw.1 hw.2 c with ⟨new, F, F', rest, hP, hP', hF, hn, hg⟩ |
    ⟨new, F, G, G', rest, hP, hP', hG, hn, hg⟩
  · rw [hP] at hl
    obtain ⟨lF, lrest, hls, hF₀, hrest⟩ := hl.cons_inv
    refine ⟨new.map (labelOr · 0) ++ labelOr F' lF :: lrest,
      ⟨hs, .inl ⟨new, F, F', rest, lF, lrest, hP, hP', hF, hn, hg, hls, rfl⟩⟩, ?_⟩
    rw [hP']
    exact labelsOk_append (labelsOk_new hg) (.cons (labelAt_step hF hF₀) hrest)
  · rw [hP] at hl
    obtain ⟨lF, l₁, hls, -, hl'⟩ := hl.cons_inv
    obtain ⟨lG, lrest, hls', hG₀, hrest⟩ := hl'.cons_inv
    subst hls'
    refine ⟨new.map (labelOr · 0) ++ labelOr G' lG :: lrest,
      ⟨hs, .inr ⟨new, F, G, G', rest, lF, lG, lrest, hP, hP', hG, hn, hg, hls, rfl⟩⟩, ?_⟩
    rw [hP']
    exact labelsOk_append (labelsOk_new hg) (.cons (labelAt_step hG hG₀) hrest)

/-- **A run's entry is located** (proved): the term that runs a code from a
node, `goto`, at the top tag `c`, with its own label and any label for the
top segment. -/
theorem labelsOk_goto {E : List Tm} {K : List (Continuation × Option Target)} {l : Nat} {L : List Tm} {d : Tm}
    {comp c : ComponentTag} (l₀ : Nat) : LabelsOk (path c (.goto E K l L d comp)) [l, l₀] := by
  simp only [path]
  exact .cons (by simp [LabelAt, runHead]) (.cons (by simp [LabelAt, runHead, hole]) .nil)

/-! ## The occurrence of a step -/

/-- **An occurrence**: a code, its tag and a node label, and the term of the
entry, the position in the node's expression. -/
structure Occ where
  code : Code
  comp : ComponentTag
  label : Nat
  pos : Tm

/-- **The occurrence of a located configuration's next step**: the run of
its innermost entry at its label; none in the top segment. -/
def occ (c : ComponentTag) (a : Located) : Option Occ :=
  match (path c a.x.t).head?, a.ls.head? with
  | some p, some l =>
    match runHead p.2 with
    | .goto m comp _ => some ⟨m, comp, l, p.2⟩
    | .frame m comp _ _ => some ⟨m, comp, l, p.2⟩
    | .top => none
  | _, _ => none

/-- **The locations a step allocates**, numbered within the reduction: the
`i`-th fresh location of the step from `a` to `b`. -/
def allocAt (a b : Located) (i : Nat) : Option Nat :=
  if a.x.s.h.length + i < b.x.s.h.length then some (a.x.s.h.length + i) else none

end Verification.TolerantFrames.ReadOnly
