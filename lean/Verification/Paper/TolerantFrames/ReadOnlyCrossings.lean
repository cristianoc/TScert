import Verification.Paper.TolerantFrames.ReadOnlyBridge

/-! # Read-only handles: the actual crossings of a step

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
actual crossings of a step"). A step of `C`'s code gives values to code
outside `C` in two ways: a value becomes a root of outside code (an
argument of a call of outside code, a result returned to it, a value thrown
to it), or the step leaves a value in a location outside code reaches.
The crossings out of the step are exactly these values, read at the step's
configurations (`actualXs`), each at one type `T`:

- **The new roots** (`newRoots`): the roots of outside code after the step
  that are not roots before it.
- **The values left where outside code reaches** (`leftVals`): the value of
  each location the step changes that is reachable from the roots after
  the step.

Two of the five fields of `PkgProps` then hold of every step by
construction (`gives_actual`, `stores_actual`). The three others are the
checks proper (`EscapeAt`): every actual crossing meets the marks
(`CrossOk`), and the step's stores keep local storage closed
(`localStores`, `localBindings`). With them `PkgProps` holds
(`pkgProps_actual`). A crossing into `C` changes no field of `PkgProps`;
the history records none here, so no location becomes protected by one. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Classical

variable {F : Family} {C : Nat} {tv : TypeView}

/-- **The new roots of outside code**: those after the step that are not
roots before it. -/
noncomputable def newRoots (F : Family) (C : Nat) (t t' : Tm) : List Val :=
  (rootsOf F C none t').filter fun r => decide (r ∉ rootsOf F C none t)

/-- **The values left where outside code reaches**: the value of each
location the step changes that is reachable from the roots after it. -/
noncomputable def leftVals (F : Family) (C : Nat) (h : Heap) (h' : Heap) (t' : Tm) : List Val :=
  (List.range h'.length).filterMap fun w =>
    if ReachesFrom (F.at C).ofC h' (rootsOf F C none t') w ∧ ¬ Same h h' w then h'[w]? else none

/-- **The actual crossings of a step**: out of `C`, at the type `T`, each
new root and each value left where outside code reaches. -/
noncomputable def actualXs (F : Family) (C : Nat) (T : tv.Ty) (h : Heap) (t : Tm) (h' : Heap) (t' : Tm) :
    List (Crossing tv) :=
  (newRoots F C t t' ++ leftVals F C h h' t').map fun v => ⟨.outOf, T, v⟩

/-- **Every new root crosses** (proved, by construction). -/
theorem gives_actual (T : tv.Ty) (h : Heap) (t : Tm) (h' : Heap) (t' : Tm) :
    ∀ r ∈ rootsOf F C none t', r ∈ rootsOf F C none t ∨ ∃ c ∈ actualXs F C T h t h' t', c.val = r := by
  intro r hr
  by_cases ho : r ∈ rootsOf F C none t
  · exact .inl ho
  · refine .inr ⟨⟨.outOf, T, r⟩, ?_, rfl⟩
    simp only [actualXs, List.mem_map]
    exact ⟨r, List.mem_append_left _ (List.mem_filter.mpr ⟨hr, by simpa using ho⟩), rfl⟩

/-- **Every value left where outside code reaches crosses** (proved, by
construction). -/
theorem stores_actual (T : tv.Ty) (h : Heap) (t : Tm) (h' : Heap) (t' : Tm) :
    ∀ w u, ReachesFrom (F.at C).ofC h' (rootsOf F C none t') w → h'[w]? = some u → ¬ Same h h' w →
      ∃ c ∈ actualXs F C T h t h' t', c.val = u := by
  intro w u hr hu hs
  refine ⟨⟨.outOf, T, u⟩, ?_, rfl⟩
  simp only [actualXs, List.mem_map]
  refine ⟨u, List.mem_append_right _ ?_, rfl⟩
  simp only [leftVals, List.mem_filterMap, List.mem_range]
  exact ⟨w, (List.getElem?_eq_some_iff.mp hu).1, by simp [hr, hs, hu]⟩

/-- **The checks at a step of `C`'s code, at its actual crossings**: every
actual crossing meets the marks at the heap after the step, and the step's
stores keep local storage closed. -/
structure EscapeAt (st st' : St (F.at C)) (mid : Ghost (F.at C)) (xs : List (Crossing tv)) : Prop where
  crossOk : ∀ c ∈ xs, CrossOk tv mid st'.s.h c
  localStores : ∀ w u, ¬ Same st.s.h st'.s.h w → st'.s.h[w]? = some u → ∀ a l, next u a = some l →
    mid.origin l = some .local → mid.origin w = some .local
  localBindings : ∀ w u, ¬ Same st.s.h st'.s.h w → st'.s.h[w]? = some u → ∀ x ∈ codeVals (F.at C).ofC u, ∀ l,
    Leaves (F.at C).ofC x l → mid.origin l ≠ some .local

/-- **The checks give `PkgProps` at the actual crossings** (proved): `gives`
and `stores` by construction, the other three from the checks. -/
theorem pkgProps_actual (T : tv.Ty) {x y : Conf} {g g' mid : Ghost (F.at C)}
    (he : EscapeAt (lift F C none x g) (lift F C none y g') mid (actualXs F C T x.s.h x.t y.s.h y.t)) :
    PkgProps tv (lift F C none x g) (lift F C none y g') mid (actualXs F C T x.s.h x.t y.s.h y.t) where
  crossOk := he.crossOk
  gives := gives_actual T x.s.h x.t y.s.h y.t
  stores := stores_actual T x.s.h x.t y.s.h y.t
  localStores := he.localStores
  localBindings := he.localBindings

namespace ClientFrame
variable {τ : Type} (fr : ClientFrame τ)

/-- **A frame whose checks cross at the actual crossings**, each at the
type `T`. -/
def ActualCrossings (T : τ) : Prop :=
  ∀ h t h' t', (fr.chk h t h' t').xs = actualXs (tv := fr.view.view) fr.F fr.C T h t h' t'

/-- **What the checks of `C`'s code establish** at each step of its code
from a reached state: `EscapeAt` at the frame's crossings. -/
def EscapeSound : Prop :=
  ∀ a b, fr.Reached a → fr.KStep a b → kind fr.F fr.C none a.1 b.1 ≠ .outside →
    EscapeAt (lift fr.F fr.C none a.1 a.2)
      (lift fr.F fr.C none b.1 (Ghost.next fr.F fr.C none fr.chkConf a.1 b.1 a.2))
      (midOf fr.chkConf a.1 b.1 a.2) (fr.chkConf a.1 b.1).xs

variable {fr}

/-- **`ChkSound` from the checks** (proved): at the actual crossings, the
checks give `PkgProps` at every step of `C`'s code (`pkgProps_actual`). -/
theorem chkSound_of_escape {T : τ} (hx : fr.ActualCrossings T) (he : fr.EscapeSound) : fr.ChkSound := by
  intro a b ha hk ho
  have h := he a b ha hk ho
  have hxs : (fr.chkConf a.1 b.1).xs = actualXs (tv := fr.view.view) fr.F fr.C T a.1.s.h a.1.t b.1.s.h b.1.t :=
    hx _ _ _ _
  rw [hxs] at h ⊢
  exact pkgProps_actual (tv := fr.view.view) T h

end ClientFrame

end Verification.TolerantFrames.ReadOnly
