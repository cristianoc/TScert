import Verification.Paper.TolerantFrames.ReadOnlyFitsEntry

/-! # Read-only handles: the crossings into `C` at a step

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The history of a program"). A step of
`C`'s code crosses, beside the values it gives to outside code
(`actualXs`), values into `C`: at an entering step the entered run's
arguments, at their declared types. The crossings of such a frame are the
incoming ones followed by the actual ones (`ActualCrossingsIn`), and the
checks at the actual crossings give `ChkSound` there too:

- **`PkgProps` at the crossings with the incoming ones**
  (`pkgProps_actualIn`): `gives` and `stores` read the actual part, by
  construction; the other three are the checks at every crossing.
- **An incoming crossing meets the marks** (`crossOk_incoming`): its value
  is one outside code held before the step, so it meets `O` at the history
  before the step (`SitesAt`), and so at the history after the step's
  allocation, which keeps the site of every old location; by
  `crossOk_of_sites` it reaches no local, internal or exposed location.
- **The sites at a reached state** (`sitesAt_reached`): the fit of every
  reached state (`fitsAt_reached`) gives its heap meeting the heap of
  sites and its roots of outside code meeting `O` (`fits_roots`).
- **`ChkSound` at the crossings with the incoming ones**
  (`chkSound_of_sitesIn`, `chkSound_of_flowIn`): the restatements of
  `chkSound_of_sites` and `chkSound_of_flow`, with the premise that every
  incoming value is a root of outside code at the state before the step
  or holds no location (`IncomingRoots`, `crossOk_noLeaves`).
- **A root is located** (`vals_located`): the roots of a term are
  objects, spines and view spines, so a primitive argument is no root. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

variable {F : Family} {C : Nat} {tv : TypeView}

/-- **`PkgProps` at incoming crossings followed by the actual ones**
(proved): the checks at every crossing give `crossOk`, `localStores` and
`localBindings`; `gives` and `stores` hold of the actual part by
construction. -/
theorem pkgProps_actualIn (T : tv.Ty) (inc : List (Crossing tv)) {x y : Conf} {g g' mid : Ghost (F.at C)}
    (he : EscapeAt (lift F C none x g) (lift F C none y g') mid (inc ++ actualXs F C T x.s.h x.t y.s.h y.t)) :
    PkgProps tv (lift F C none x g) (lift F C none y g') mid (inc ++ actualXs F C T x.s.h x.t y.s.h y.t) where
  crossOk := he.crossOk
  gives r hr := (gives_actual (F := F) (C := C) T x.s.h x.t y.s.h y.t r hr).imp_right
    fun ⟨c, hc, hv⟩ => ⟨c, List.mem_append_right _ hc, hv⟩
  stores w u hr hu hs :=
    let ⟨c, hc, hv⟩ := stores_actual (F := F) (C := C) T x.s.h x.t y.s.h y.t w u hr hu hs
    ⟨c, List.mem_append_right _ hc, hv⟩
  localStores := he.localStores
  localBindings := he.localBindings

namespace ClientFrame
variable {τ : Type} (fr : ClientFrame τ)

/-- **A frame whose checks cross at incoming crossings, then at the actual
ones**, each actual one at the type `T`. -/
def ActualCrossingsIn (T : τ) (inc : Heap → Tm → Heap → Tm → List (Crossing fr.view.view)) : Prop :=
  ∀ h t h' t', (fr.chk h t h' t').xs = inc h t h' t' ++ actualXs (tv := fr.view.view) fr.F fr.C T h t h' t'

/-- **Every incoming value is one outside code held, or holds no
location**: at each step of `C`'s code from a reached state, the value of
each incoming crossing is a root of outside code at the state before the
step, or a value with no location (a primitive argument, an `undefined`
pad). -/
def IncomingRoots (inc : Heap → Tm → Heap → Tm → List (Crossing fr.view.view)) : Prop :=
  ∀ a b, fr.Reached a → fr.KStep a b → kind fr.F fr.C none a.1 b.1 ≠ .outside →
    ∀ c ∈ inc a.1.s.h a.1.t b.1.s.h b.1.t,
      c.val ∈ rootsOf fr.F fr.C none a.1.t ∨ ∀ l, ¬ Leaves (fr.F.at fr.C).ofC c.val l

variable {fr}

/-- The frame's crossings at a step are its incoming ones, then the actual
ones (proved, by `ActualCrossingsIn`). -/
theorem chkConf_xs {T : τ} {inc : Heap → Tm → Heap → Tm → List (Crossing fr.view.view)}
    (hx : fr.ActualCrossingsIn T inc) (x y : Conf) :
    (fr.chkConf x y).xs = inc x.s.h x.t y.s.h y.t ++ actualXs (tv := fr.view.view) fr.F fr.C T x.s.h x.t y.s.h y.t :=
  hx _ _ _ _

/-- **`ChkSound` from the checks, with incoming crossings** (proved): at
the incoming and actual crossings, the checks give `PkgProps` at every step
of `C`'s code (`pkgProps_actualIn`). -/
theorem chkSound_of_escapeIn {T : τ} {inc : Heap → Tm → Heap → Tm → List (Crossing fr.view.view)}
    (hx : fr.ActualCrossingsIn T inc) (he : fr.EscapeSound) : fr.ChkSound := by
  intro a b ha hk ho
  have h := he a b ha hk ho
  rw [chkConf_xs hx] at h ⊢
  exact pkgProps_actualIn (tv := fr.view.view) T _ h

/-- **The sites at a reached state** (proved): where every entry fits the
flow, every reached state does (`fitsAt_reached`), so its heap meets the
heap of sites and its roots of outside code meet `O` (`fits_roots`). -/
theorem sitesAt_reached {Fl : Flow (fr.F.at fr.C)} (hF : Fl.Facts) (hS : fr.FlowSites Fl) (hE : fr.EntryFits Fl)
    {a : Conf × Ghost (fr.F.at fr.C)} (ha : fr.Reached a) : fr.SitesAt Fl.H Fl.O a := by
  have hfa := fitsAt_reached hF hS hE ha
  refine ⟨hfa.2.sites, fun r hr => fits_roots (Family.realm_ofC fr.C) hfa.1 false r ?_⟩
  have hn : fr.F.ofC fr.C none = false := by simp [Family.ofC, Family.Runs]
  have : rootsOf fr.F fr.C none a.1.t = vals (fr.F.at fr.C).ofC fr.F.realm true false a.1.t := by
    simp [rootsOf, hn]; rfl
  rwa [this] at hr

/-- **An incoming crossing meets the marks** (proved, the draft's
`crossOk_incoming`): its value is a root of outside code at the state
before the step, which meets `O` there (`SitesAt`); the step's allocation
keeps the site of every location the value reaches, which the
configuration's references bound; so at a heap after the step meeting the
heap of sites, with `O` closed and lendable, it reaches no local, internal
or exposed location (`crossOk_of_sites`). -/
theorem crossOk_incoming {H : SiteHeap (fr.F.at fr.C)} {O : List (Option (fr.F.at fr.C).Site)}
    (hO : Closed H O) (hlend : Lendable O) {a b : Conf × Ghost (fr.F.at fr.C)} (ha : fr.SitesAt H O a)
    (hH : HeapSites (midOf fr.chkConf a.1 b.1 a.2) H b.1.s.h) {c : Crossing fr.view.view}
    (hc : c.val ∈ rootsOf fr.F fr.C none a.1.t) :
    CrossOk fr.view.view (midOf fr.chkConf a.1 b.1 a.2) b.1.s.h c := by
  refine crossOk_of_sites hH hO hlend ?_
  have hv : SitesOf a.2 O c.val := ha.2 c.val hc
  have hr : RefsOkN a.1.s.W c.val := vals_refsOkN (RefsOk.refsOkN a.1.ok) hc
  exact hv.alloc fun l hl => Leaves.lt (s := a.1.s) hr hl

/-- **A crossing of a value with no location meets the marks** (proved,
`crossOk_of_sites`): it reaches no location. -/
theorem crossOk_noLeaves {H : SiteHeap (fr.F.at fr.C)} {O : List (Option (fr.F.at fr.C).Site)}
    (hO : Closed H O) (hlend : Lendable O) {g : Ghost (fr.F.at fr.C)} {h : Heap} (hH : HeapSites g H h)
    {c : Crossing fr.view.view} (hc : ∀ l, ¬ Leaves (fr.F.at fr.C).ofC c.val l) :
    CrossOk fr.view.view g h c :=
  crossOk_of_sites hH hO hlend fun l hl => (hc l hl).elim

/-- **`ChkSound` from the sites, with incoming crossings** (proved, the
restatement of `chkSound_of_sites`): at the actual crossings as there
(`escapeAt_of_sites`), and at each incoming crossing by
`crossOk_incoming`, where every reached state meets the sites and every
incoming value is a root of outside code before its step. -/
theorem chkSound_of_sitesIn {T : τ} {inc : Heap → Tm → Heap → Tm → List (Crossing fr.view.view)}
    {H : SiteHeap (fr.F.at fr.C)} {O : List (Option (fr.F.at fr.C).Site)}
    (hx : fr.ActualCrossingsIn T inc) (hO : Closed H O) (hlend : Lendable O) (hL : LocalHeld H)
    (hs : fr.SitesSound H O) (hat : ∀ a, fr.Reached a → fr.SitesAt H O a) (hin : fr.IncomingRoots inc) :
    fr.ChkSound := by
  refine chkSound_of_escapeIn hx fun a b ha hk ho => ?_
  obtain ⟨hH, hr⟩ := hs a b ha hk ho
  have he := escapeAt_of_sites (tv := fr.view.view) (x := a.1) (y := b.1) (g := a.2)
    (g' := Ghost.next fr.F fr.C none fr.chkConf a.1 b.1 a.2) T hH hO hlend hL hr
  rw [chkConf_xs hx]
  refine ⟨fun c hc => ?_, he.localStores, he.localBindings⟩
  rcases List.mem_append.mp hc with hi | hac
  · rcases hin a b ha hk ho c hi with hr | hn
    · exact crossOk_incoming hO hlend (hat a ha) hH hr
    · exact crossOk_noLeaves hO hlend hH hn
  · exact he.crossOk c hac

/-- **`ChkSound` from the flow and the shape of the calls, with incoming
crossings** (proved, the restatement of `chkSound_of_flow`): the fit of
every entry (`entryFits`) gives `SitesSound` (`sitesSound_of_fits`) and the
sites at every reached state (`sitesAt_reached`), and those the checks at
the incoming and actual crossings (`chkSound_of_sitesIn`). -/
theorem chkSound_of_flowIn {T : τ} {inc : Heap → Tm → Heap → Tm → List (Crossing fr.view.view)}
    {Fl : Flow (fr.F.at fr.C)} (hF : Fl.Facts) (hS : fr.FlowSites Fl)
    {args : Heap → Tm → List (fr.view.view.Ty × Val)} (hst : fr.StartsEntry args)
    (hsh : ∀ k (W : WorldT k) h t, fr.Call k W h t → EntryShape Fl h t) (hx : fr.ActualCrossingsIn T inc)
    (hlend : Lendable Fl.O) (hL : LocalHeld Fl.H) (hin : fr.IncomingRoots inc) : fr.ChkSound :=
  have hE := entryFits hF hst hsh
  chkSound_of_sitesIn hx (fun s hs s' h' => hF.closed s hs s' h') hlend hL (sitesSound_of_fits hF hS hE)
    (fun _ ha => sitesAt_reached hF hS hE ha) hin

end ClientFrame

/-- A value with a location of its own: an object, a spine or a view
spine. -/
def LocatedVal : Tm → Bool
  | .objAt .. | .arr _ | .viewSpine .. => true
  | _ => false

/-- **A root is located** (proved, by induction on the term): every value a
term holds at its positions (`vals`) is an object, a spine or a view
spine; a number, a string or `undefined` passed as an argument is no
root. -/
theorem vals_located {ofC : ComponentTag → Bool} (t : Tm) :
    ∀ rl o nk, ∀ v ∈ vals ofC rl o nk t, LocatedVal v = true := by
  induction t using Tm.induct with
  | _ =>
    intro rl o nk v hv
    simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap] at hv
    repeat' split at hv
    all_goals first
      | (simp at hv; done)
      | (simp_all [LocatedVal]; done)
      | grind [LocatedVal]

/-- **A primitive argument is no root** (proved, the counter-model to
reading every incoming value as a root): at an entering step whose
argument is a number, the crossing's value is no root of outside code,
whatever the term. -/
theorem num_not_root (F : Family) (C : Nat) (t : Tm) (b : UInt64) : Tm.num b ∉ rootsOf F C none t :=
  fun h => by simpa [LocatedVal] using vals_located t _ _ _ _ h

end Verification.TolerantFrames.ReadOnly
