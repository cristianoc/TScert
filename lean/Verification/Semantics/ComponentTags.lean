import Verification.Semantics.ExceptionalPosts

/-! # A run's component is ghost

A run of graph code (`Tm.goto`, `Tm.frame`) carries the component of the
code it runs (`ComponentTag`). Every reduction rule copies it and none reads
it, and neither do reference validity (`refs`), being a value (`isVal`) or
raising (`Raises`). So two runs that differ only in the outermost run's
component (`SameRun`) step alike: each step of one is a step of the other,
from and to the same heap, to runs that again differ at most there
(`SameRun.step`). The heap is the same on both sides, so every value it
holds, closures and their code's components included, is the same. Safety
and its postcondition forms (`Safe`, `SafePostW`, `SafePostExcW`,
`SafePostExcV`, hence `SafePost` and `SafePostExc`) therefore hold of a run
at one component exactly when they hold of it at every other
(`SafePostExcV.goto_comp_iff` and the others). -/
namespace Verification

/-- **Two runs differing at most in the outermost run's component**: the
same term, or a run of the same code at the same node, environment and (for
a frame) expression, continuation and handler, at any two components. -/
inductive SameRun : Tm → Tm → Prop where
  | refl (t : Tm) : SameRun t t
  | goto {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {l : Nat}
      {L : List Tm} {d : Tm} (c c' : ComponentTag) : SameRun (.goto E K l L d c) (.goto E K l L d c')
  | frame {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {t : Tm}
      {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target}
      (c c' : ComponentTag) : SameRun (.frame E K t L d k x c) (.frame E K t L d k x c')

namespace SameRun

theorem symm {t u : Tm} : SameRun t u → SameRun u t
  | .refl _ => .refl _
  | .goto c c' => .goto c' c
  | .frame c c' => .frame c' c

/-- The references of a run read no component (proved). -/
theorem refs_eq {t u : Tm} (h : SameRun t u) : refs t = refs u := by
  cases h <;> simp [refs]

theorem refsOk {k : Nat} {W : WorldT k} {t u : Tm} (h : SameRun t u) : RefsOk W t ↔ RefsOk W u := by
  unfold RefsOk; rw [h.refs_eq]

/-- A value is the same term on both sides (proved): no run is a value. -/
theorem eq_of_val {t u : Tm} (h : SameRun t u) (hv : isVal t = true) : t = u := by
  cases h with
  | refl => rfl
  | goto => simp [isVal] at hv
  | frame => simp [isVal] at hv

/-- A run raises nothing (proved): what raises is the same term on both sides. -/
theorem raises {t u v : Tm} (h : SameRun t u) (hr : Raises t v) : Raises u v := by
  cases h with
  | refl => exact hr
  | goto => cases hr
  | frame => cases hr

/-- **A step of one run is a step of the other** (proved): from and to the
same heap, to runs again differing at most in the outermost component. -/
theorem step {t u t' : Tm} {hp hp' : Heap} (h : SameRun t u) (s : Step hp t hp' t') :
    ∃ u', Step hp u hp' u' ∧ SameRun t' u' := by
  cases h with
  | refl => exact ⟨t', s, .refl _⟩
  | goto c c' =>
    cases s with
    | gotoEnter he hk => exact ⟨_, .gotoEnter he hk, .frame _ _⟩
  | frame c c' =>
    cases s with
    | frameC s => exact ⟨_, .frameC s, .frame _ _⟩
    | frameRet hv => exact ⟨_, .frameRet hv, .refl _⟩
    | frameBind hv => exact ⟨_, .frameBind hv, .goto _ _⟩
    | frameEffect hv => exact ⟨_, .frameEffect hv, .goto _ _⟩
    | frameYes => exact ⟨_, .frameYes, .goto _ _⟩
    | frameNo => exact ⟨_, .frameNo, .goto _ _⟩
    | frameYesBind => exact ⟨_, .frameYesBind, .goto _ _⟩
    | frameNoBind => exact ⟨_, .frameNoBind, .goto _ _⟩
    | frameTag hv => exact ⟨_, .frameTag hv, .goto _ _⟩
    | frameHandle hr => exact ⟨_, .frameHandle hr, .goto _ _⟩
    | frameRaise hr => exact ⟨_, .frameRaise hr, .refl _⟩

theorem thrown {Ξ : Fam} {k : Nat} {W : WorldT k} {t u : Tm} (h : SameRun t u) :
    Thrown Ξ k W t → Thrown Ξ k W u := fun ⟨v, hr, hs, hx⟩ => ⟨v, h.raises hr, hs, hx⟩

end SameRun

/-- **Safety reads no run's component** (proved). -/
theorem Safe.sameRun {Ξ T : Fam} : ∀ {n : Nat} {W : WorldT n} {h : Heap} {t u : Tm},
    SameRun t u → Safe Ξ T n W h t → Safe Ξ T n W h u := by
  intro n; induction n with
  | zero => intro W h t u hr hs; exact hr.refsOk.mp hs
  | succ n ih =>
    intro W h t u hr hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hr.refsOk.mp hrf, ?_⟩
    rcases hs with (⟨hv, hT⟩ | hth) | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · obtain rfl := hr.eq_of_val hv; exact .inl (.inl ⟨hv, hT⟩)
    · exact .inl (.inr (hr.thrown hth))
    · obtain ⟨u', su, hr'⟩ := hr.step st
      exact .inr ⟨U, h', u', hx, hu, su, hh, ih hr' hs⟩

namespace HeapObservations

/-- **Safety with a postcondition reads no run's component** (proved). -/
theorem SafePostW.sameRun {Ξ T : Fam} {Q : WPost} : ∀ {n : Nat} {W : WorldT n} {h : Heap} {t u : Tm},
    SameRun t u → SafePostW Ξ T Q n W h t → SafePostW Ξ T Q n W h u := by
  intro n; induction n with
  | zero => intro W h t u hr hs; exact hr.refsOk.mp hs
  | succ n ih =>
    intro W h t u hr hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hr.refsOk.mp hrf, ?_⟩
    rcases hs with (⟨hv, hT, hQ⟩ | hth) | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · obtain rfl := hr.eq_of_val hv; exact .inl (.inl ⟨hv, hT, hQ⟩)
    · exact .inl (.inr (hr.thrown hth))
    · obtain ⟨u', su, hr'⟩ := hr.step st
      exact .inr ⟨U, h', u', hx, hu, su, hh, ih hr' hs⟩

/-- **Safety with postconditions on both exits reads no run's component**
(proved). -/
theorem SafePostExcW.sameRun {Ξ T : Fam} {Q : WPost} {R : WExc} :
    ∀ {n : Nat} {W : WorldT n} {h : Heap} {t u : Tm},
    SameRun t u → SafePostExcW Ξ T Q R n W h t → SafePostExcW Ξ T Q R n W h u := by
  intro n; induction n with
  | zero => intro W h t u hr hs; exact hr.refsOk.mp hs
  | succ n ih =>
    intro W h t u hr hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hr.refsOk.mp hrf, ?_⟩
    rcases hs with (⟨hv, hT, hQ⟩ | ⟨hth, hR⟩) | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · obtain rfl := hr.eq_of_val hv; exact .inl (.inl ⟨hv, hT, hQ⟩)
    · exact .inl (.inr ⟨hr.thrown hth, hR⟩)
    · obtain ⟨u', su, hr'⟩ := hr.step st
      exact .inr ⟨U, h', u', hx, hu, su, hh, ih hr' hs⟩

/-- **Safety with postconditions on both exits, the throw's reading the
thrown value, reads no run's component** (proved). -/
theorem SafePostExcV.sameRun {Ξ T : Fam} {Q : WPost} {R : WExcV} :
    ∀ {n : Nat} {W : WorldT n} {h : Heap} {t u : Tm},
    SameRun t u → SafePostExcV Ξ T Q R n W h t → SafePostExcV Ξ T Q R n W h u := by
  intro n; induction n with
  | zero => intro W h t u hr hs; exact hr.refsOk.mp hs
  | succ n ih =>
    intro W h t u hr hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hr.refsOk.mp hrf, ?_⟩
    rcases hs with (⟨hv, hT, hQ⟩ | ⟨v, hra, hsc, hx, hR⟩) | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · obtain rfl := hr.eq_of_val hv; exact .inl (.inl ⟨hv, hT, hQ⟩)
    · exact .inl (.inr ⟨v, hr.raises hra, hsc, hx, hR⟩)
    · obtain ⟨u', su, hr'⟩ := hr.step st
      exact .inr ⟨U, h', u', hx, hu, su, hh, ih hr' hs⟩

end HeapObservations

/-! ### A run at one component is a run at every component -/

section
variable {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {l : Nat}
  {L : List Tm} {d : Tm} (c c' : ComponentTag)

theorem goto_refsOk_comp_iff {k : Nat} {W : WorldT k} :
    RefsOk W (.goto E K l L d c) ↔ RefsOk W (.goto E K l L d c') := (SameRun.goto c c').refsOk

theorem Safe.goto_comp_iff {Ξ T : Fam} {n : Nat} {W : WorldT n} {h : Heap} :
    Safe Ξ T n W h (.goto E K l L d c) ↔ Safe Ξ T n W h (.goto E K l L d c') :=
  ⟨Safe.sameRun (.goto c c'), Safe.sameRun (.goto c' c)⟩

theorem HeapObservations.SafePostW.goto_comp_iff {Ξ T : Fam} {Q : HeapObservations.WPost} {n : Nat}
    {W : WorldT n} {h : Heap} :
    SafePostW Ξ T Q n W h (.goto E K l L d c) ↔ SafePostW Ξ T Q n W h (.goto E K l L d c') :=
  ⟨SafePostW.sameRun (.goto c c'), SafePostW.sameRun (.goto c' c)⟩

theorem HeapObservations.SafePostExcW.goto_comp_iff {Ξ T : Fam} {Q : HeapObservations.WPost}
    {R : HeapObservations.WExc} {n : Nat} {W : WorldT n} {h : Heap} :
    SafePostExcW Ξ T Q R n W h (.goto E K l L d c) ↔ SafePostExcW Ξ T Q R n W h (.goto E K l L d c') :=
  ⟨SafePostExcW.sameRun (.goto c c'), SafePostExcW.sameRun (.goto c' c)⟩

/-- **A run's safety at one component is its safety at every component**
(proved), with postconditions on both exits, the throw's reading the thrown
value. -/
theorem HeapObservations.SafePostExcV.goto_comp_iff {Ξ T : Fam} {Q : HeapObservations.WPost}
    {R : HeapObservations.WExcV} {n : Nat} {W : WorldT n} {h : Heap} :
    SafePostExcV Ξ T Q R n W h (.goto E K l L d c) ↔ SafePostExcV Ξ T Q R n W h (.goto E K l L d c') :=
  ⟨SafePostExcV.sameRun (.goto c c'), SafePostExcV.sameRun (.goto c' c)⟩

end

end Verification
