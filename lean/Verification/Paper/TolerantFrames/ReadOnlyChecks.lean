import Verification.Paper.TolerantFrames.ReadOnlyFrame

/-! # Read-only handles: member certificates from the checks

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
checks the rule requires" and "What the Lean states"): each check as a
predicate over a step of the package's code, the step lemma they give, and
a member's certificate (`ReadOnlyFrame.Member`) built from them.

- A path of a well-formed heap from a valid value ends at an allocated
  location (`follows_lt`).
- A path after a step either is a path before it, or passes a location the
  step changed or allocated, from whose new contents the rest of the path
  runs (`follows_split`).
- **The step lemma** (`pkg_step_ok`): a step of the package's code that
  meets the checks (each value it gives to code that is not its, and each
  value it stores where such code reaches, crosses; each crossing meets the
  marks; each crossing updates `E`), with history transitions that never
  pop below depth `d`, keeps the invariants of states and the marks, and
  grows the history.
- **Incoming values** (`incoming_site`, `incoming_charged`): a location
  reachable from a value code that is not the package's holds is of an
  exposed or released site or outside storage, so a write charged to every
  such part is charged to its own.
- **A member from its checks** (`memberOfChecks`): its call, a sequence of
  checked steps and runs of code that is not the package's one call deeper,
  keeps the invariants; with its certified effect within `Ψ_P` part by part
  (the protocol as a fixed point) it bounds `R_P` by `Ψ_P`; with every step
  keeping the invariants of complete handles (Tolerant invariant) it keeps
  them. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

variable {P : Package}

/-! ## Paths across a step -/

/-- A location holds the same contents in both heaps. -/
def Same (h h' : Heap) (w : Nat) : Prop := ∃ v, h[w]? = some v ∧ h'[w]? = some v

theorem follows_cons {ofC : ComponentTag → Bool} {h : Heap} {v v₀ : Val} {a : Label} {π : List Label} {l : Nat}
    (hs : Succ ofC h v a v₀) (hf : Follows ofC h v₀ π l) : Follows ofC h v (a :: π) l := by
  cases π with
  | nil => exact hf.elim
  | cons b π => exact ⟨v₀, hs, hf⟩

/-- **A path after a step** either is a path before it, or passes a location
the step changed or allocated, the path's prefix reaching it and the rest
running from its new contents. A step into a value's code reads no heap. -/
theorem follows_split {ofC : ComponentTag → Bool} {h h' : Heap} :
    ∀ {v : Val} {π : List Label} {l : Nat}, Follows ofC h' v π l →
      Follows ofC h v π l ∨
        ∃ w u π₁ π₂, Follows ofC h' v π₁ w ∧ h'[w]? = some u ∧ ¬ Same h h' w ∧ Follows ofC h' u π₂ l
  | _, [], _, hf => hf.elim
  | _, [_], _, hf => .inl hf
  | _, a :: b :: π, _, ⟨v₀, hsucc, hf⟩ => by
    rcases follows_split hf with hf₀ | ⟨w, u, π₁, π₂, h₁, hu, hs, h₂⟩
    · rcases hsucc with ⟨l₀, hn, hl₀⟩ | hc
      · by_cases hs : Same h h' l₀
        · obtain ⟨u, hu, hu'⟩ := hs
          rw [hl₀] at hu'
          cases hu'
          exact .inl ⟨_, .inl ⟨l₀, hn, hu⟩, hf₀⟩
        · exact .inr ⟨l₀, v₀, [a], b :: π, hn, hl₀, hs, hf⟩
      · exact .inl ⟨v₀, .inr hc, hf₀⟩
    · exact .inr ⟨w, u, a :: π₁, π₂, follows_cons hsucc h₁, hu, hs, h₂⟩

/-! ## The history keeps the marks -/

theorem HStep.marks {tv : TypeView} {h : Heap} {g g' : Ghost P} (hs : HStep tv h g g') :
    g'.site = g.site ∧ g'.key = g.key := by
  cases hs <;> exact ⟨rfl, rfl⟩

theorem HSteps.marks {tv : TypeView} {d : Nat} {g g' : Ghost P} (hs : HSteps tv d g g') :
    g'.site = g.site ∧ g'.key = g.key := by
  induction hs with
  | refl => exact ⟨rfl, rfl⟩
  | step _ hst _ _ ih => exact ⟨ih.1.trans hst.marks.1, ih.2.trans hst.marks.2⟩

theorem HStep.exposed_mono {tv : TypeView} {h : Heap} {g g' : Ghost P} (hs : HStep tv h g g') {l : Nat}
    (he : g.E l) : g'.E l := by
  cases hs
  case cross => exact .inl he
  all_goals exact he

/-- **A crossing updates `E`** (the draft, Crossings): after a crossing at
the heap `h`, and any later transitions, every exposed location the
crossing reaches read-only at `h` is in `E`. -/
theorem HSteps.cross_covers {tv : TypeView} {d : Nat} {h : Heap} {g g' : Ghost P} (c : Dir) (T : tv.Ty)
    (v : Val) (hs : HSteps tv d (g.cross tv c T h v) g') {l : Nat} (hr : ReachRO tv P.ofC T h v l)
    (he : g.origin l = some .exposed) : g'.E l := by
  have h₀ : (g.cross tv c T h v).E l := .inr ⟨hr, he⟩
  clear hr he
  generalize g.cross tv c T h v = g₀ at hs h₀
  induction hs with
  | refl => exact h₀
  | step _ hst _ _ ih => exact ih (hst.exposed_mono h₀)

/-! ## The checks of a step of the package's code -/

/-- **A crossing**: its direction, the type of its root position and the
value that crosses. -/
structure Crossing (tv : TypeView) where
  dir : Dir
  ty : tv.Ty
  val : Val

/-- **The marks at a crossing** (the draft, Definitions, "Marks", and the
check *Confinement*): no location of a local or an internal site is
reachable from the crossing value, and one of an exposed site only through
a read-only path. -/
def CrossOk (tv : TypeView) (g : Ghost P) (h : Heap) (c : Crossing tv) : Prop :=
  ∀ l, Reaches P.ofC h c.val l → g.origin l ≠ some .local ∧ g.origin l ≠ some .internal ∧
    (g.origin l = some .exposed → ReachRO tv P.ofC c.ty h c.val l)

/-- **A step of the package's code inside a call at depth `d`**, with its
checks. It allocates, fixing every old location's site and key (`mid`);
its history transitions, at the heap after it, never pop below depth `d`;
and its crossings `xs`, at that heap, update `E` (the draft, Crossings) and
meet the marks. Every value the step gives to code that is not the
package's crosses (`gives`: an argument of such a call, a result, a value
thrown), and so does every value it leaves in storage such code reaches,
changed or allocated by the step (`stores`: the draft's "the content of
storage both sides reach"). Storage the step changes or allocates that
references local storage is local (`localStores`, the local mark's "never
stored into storage"). The frames' values stay valid. -/
structure PkgStep (tv : TypeView) (d : Nat) (st st' : St P) : Type where
  adm : Admissible st.s st'.s
  mid : Ghost P
  sites : ∀ l, l < st.s.h.length → mid.site l = st.g.site l ∧ mid.key l = st.g.key l
  midE : mid.E = st.g.E
  midA : mid.A = st.g.A
  midB : mid.B = st.g.B
  hist : HSteps tv d mid st'.g
  xs : List (Crossing tv)
  covers : ∀ c ∈ xs, ∀ l, ReachRO tv P.ofC c.ty st'.s.h c.val l → mid.origin l = some .exposed → st'.g.E l
  crossOk : ∀ c ∈ xs, CrossOk tv mid st'.s.h c
  gives : ∀ r ∈ st'.roots, r ∈ st.roots ∨ ∃ c ∈ xs, c.val = r
  stores : ∀ w u, ReachesFrom P.ofC st'.s.h st'.roots w → st'.s.h[w]? = some u → ¬ Same st.s.h st'.s.h w →
    ∃ c ∈ xs, c.val = u
  valid : RootsValid st'
  localStores : ∀ w u, ¬ Same st.s.h st'.s.h w → st'.s.h[w]? = some u → ∀ a l, next u a = some l →
    mid.origin l = some .local → mid.origin w = some .local
  localBindings : ∀ w u, ¬ Same st.s.h st'.s.h w → st'.s.h[w]? = some u → ∀ x ∈ codeVals P.ofC u, ∀ l,
    Leaves P.ofC x l → mid.origin l ≠ some .local

/-- **The step lemma**: a checked step of the package's code inside a call
at depth `d` keeps the invariants of states and the marks, and grows the
history. (M): a location the frames of code that is not the package's
reach afterwards is reached along a path they had, or from a value that
crossed, which meets the marks. (P2): an exposed location so reached was in
`E`, or a crossing put it there. -/
theorem pkg_step_ok {tv : TypeView} {d : Nat} {st st' : St P} (hp : PkgStep tv d st st') (hok : Ok d st) :
    Ok d st' ∧ Kept st st' ∧ Grows d st.g st'.g := by
  have hm := hp.hist.marks
  have hkept : Kept st st' := ⟨hp.adm, fun l hl => by rw [hm.1, hm.2]; exact hp.sites l hl⟩
  have hmid : Grows d st.g hp.mid :=
    ⟨hok.pos, hok.len, by rw [hp.midA]; exact hok.len, hp.midB,
      fun l h => (Ghost.prot_congr hp.midA hp.midB l).mpr h, fun l h => by rw [hp.midE]; exact h⟩
  obtain ⟨hgr, hu⟩ := hp.hist.grows (Ghost.uniform_congr hp.midA hp.midB hok.uniform) hok.pos hmid.len'
  have hg := hmid.trans hgr
  have horig : ∀ l, st'.g.origin l = hp.mid.origin l := fun l => by simp only [Ghost.origin, hm.1]
  -- A location reached afterwards from a value that crossed meets the marks.
  have hcross : ∀ c ∈ hp.xs, ∀ l, Reaches P.ofC st'.s.h c.val l →
      st'.g.origin l ≠ some .local ∧ st'.g.origin l ≠ some .internal ∧
        (st'.g.origin l = some .exposed → st'.g.E l) := by
    intro c hc l hr
    obtain ⟨h₁, h₂, h₃⟩ := hp.crossOk c hc l hr
    rw [horig l]
    exact ⟨h₁, h₂, fun he => hp.covers c hc l (h₃ he) he⟩
  -- A location reached afterwards along a path the frames had.
  have hold : ∀ r ∈ st.roots, ∀ π l, Follows P.ofC st.s.h r π l →
      st'.g.origin l ≠ some .local ∧ st'.g.origin l ≠ some .internal ∧
        (st'.g.origin l = some .exposed → st'.g.E l) := by
    intro r hr π l hf
    have hl := follows_lt (hok.valid r hr) hf
    have ho : st'.g.origin l = st.g.origin l := hkept.origin hl
    have hreach : ReachesFrom P.ofC st.s.h st.roots l := ⟨r, hr, π, hf⟩
    obtain ⟨h₁, h₂⟩ := hok.marks l hreach
    rw [ho]
    exact ⟨h₁, h₂, fun he => hg.exposed l (hok.confined l hreach he)⟩
  have hall : ∀ l, ReachesFrom P.ofC st'.s.h st'.roots l →
      st'.g.origin l ≠ some .local ∧ st'.g.origin l ≠ some .internal ∧
        (st'.g.origin l = some .exposed → st'.g.E l) := by
    rintro l ⟨r, hr, π, hf⟩
    rcases hp.gives r hr with hr₀ | ⟨c, hc, rfl⟩
    · rcases follows_split (h := st.s.h) hf with hf₀ | ⟨w, u, π₁, π₂, h₁, hu, hs, h₂⟩
      · exact hold r hr₀ π l hf₀
      · obtain ⟨c, hc, hcu⟩ := hp.stores w u ⟨r, hr, π₁, h₁⟩ hu hs
        exact hcross c hc l ⟨π₂, hcu ▸ h₂⟩
    · exact hcross c hc l ⟨π, hf⟩
  have hlc : LocalClosed st' := by
    intro w u hu' a l hn hloc
    rw [horig l] at hloc
    rw [horig w]
    by_cases hs : Same st.s.h st'.s.h w
    · obtain ⟨v, hv₀, hv₁⟩ := hs
      rw [hu'] at hv₁
      cases hv₁
      have hw : w < st.s.h.length := (List.getElem?_eq_some_iff.mp hv₀).1
      have hl' : l < st.s.h.length := next_lt (RefsOk.refsOkN (contents_valid hw hv₀)) hn
      have hmo : ∀ x, x < st.s.h.length → hp.mid.origin x = st.g.origin x := fun x hx => by
        simp only [Ghost.origin, (hp.sites x hx).1]
      rw [hmo l hl'] at hloc
      rw [hmo w hw]
      exact hok.localClosed w _ hv₀ a l hn hloc
    · exact hp.localStores w u hs hu' a l hn hloc
  have hbc : BindingsClosed st' := by
    intro w u hu' x hx l hl hloc
    rw [horig l] at hloc
    by_cases hs : Same st.s.h st'.s.h w
    · obtain ⟨v, hv₀, hv₁⟩ := hs
      rw [hu'] at hv₁
      cases hv₁
      have hw : w < st.s.h.length := (List.getElem?_eq_some_iff.mp hv₀).1
      have hl' : l < st.s.h.length :=
        Leaves.lt (s := st.s) (codeVals_refsOkN (RefsOk.refsOkN (contents_valid hw hv₀)) hx) hl
      have hmo : hp.mid.origin l = st.g.origin l := by simp only [Ghost.origin, (hp.sites l hl').1]
      rw [hmo] at hloc
      exact hok.bindings w _ hv₀ x hx l hl hloc
    · exact hp.localBindings w u hs hu' x hx l hl hloc
  exact ⟨⟨hok.pos, hg.len', hu, fun l h => ⟨(hall l h).1, (hall l h).2.1⟩, fun l h he => (hall l h).2.2 he,
    hp.valid, hlc, hbc⟩, hkept, hg⟩

/-- A step whose history begins with its crossings, at the heap after it,
updates `E` as `PkgStep.covers` states. -/
theorem covers_of_cross {tv : TypeView} {d : Nat} {h : Heap} {g g' : Ghost P} (c : Crossing tv)
    (hs : HSteps tv d (g.cross tv c.dir c.ty h c.val) g') :
    ∀ l, ReachRO tv P.ofC c.ty h c.val l → g.origin l = some .exposed → g'.E l :=
  fun _ hr he => hs.cross_covers c.dir c.ty c.val hr he

/-! ## Incoming values -/

/-- **A value entering the package reaches no local or internal storage**
(the draft, *Incoming values*, "by (M) it is never charged to a local or
internal site"): a location reachable from a value the frames of code that
is not the package's hold is of an exposed or a released site, or outside
storage. -/
theorem incoming_site {st : St P} (hm : MarksOk st) {l : Nat} (hr : ReachesFrom P.ofC st.s.h st.roots l) :
    st.g.origin l = some .exposed ∨ st.g.Lent l := by
  obtain ⟨h₁, h₂⟩ := hm l hr
  unfold Ghost.Lent
  rcases ho : st.g.origin l with _ | m
  · exact .inr (.inr rfl)
  · cases m
    · rw [ho] at h₁; exact absurd rfl h₁
    · rw [ho] at h₂; exact absurd rfl h₂
    · exact .inl rfl
    · exact .inr (.inl rfl)

/-- A part whose site is exposed, released or outside storage. -/
def Part.Incoming (p : Part P) : Prop :=
  p.site = none ∨ ∃ s, p.site = some s ∧ (P.mark s = .exposed ∨ P.mark s = .released)

/-- **A write to an entering value charged to every exposed and released
part and to outside storage** at its kind and key (the draft, *Incoming
values*) is charged to the written location's own part. -/
theorem incoming_charged {st : St P} (hm : MarksOk st) {eff : Protocol P} {δ : Change}
    (hc : ∀ p : Part P, p.Incoming → δ.le (eff p) = true) {l : Nat} (hr : ReachesFrom P.ofC st.s.h st.roots l) :
    δ.le (eff (st.part l)) = true := by
  refine hc _ ?_
  simp only [Part.Incoming, St.part]
  rcases incoming_site hm hr with he | hL
  · simp only [Ghost.origin] at he
    obtain ⟨s, hs, hm'⟩ := Option.map_eq_some_iff.mp he
    exact .inr ⟨s, hs, .inl hm'⟩
  · rcases hL with hL | hL
    · simp only [Ghost.origin] at hL
      obtain ⟨s, hs, hm'⟩ := Option.map_eq_some_iff.mp hL
      exact .inr ⟨s, hs, .inr hm'⟩
    · simp only [Ghost.origin, Option.map_eq_none_iff] at hL
      exact .inl hL

/-! ## A member from its checks -/

/-- **A member's call inside a call at depth `d`**: checked steps of the
package's code (its entry, its body and its normal or exceptional exit
among them), and runs of code that is not the package's it makes while its
call is active, related by `Inner`. -/
inductive MemberRun (tv : TypeView) (Inner : St P → St P → Prop) (d : Nat) : St P → St P → Prop
  | nil (st : St P) : MemberRun tv Inner d st st
  | step {st st' st'' : St P} : PkgStep tv d st st' → MemberRun tv Inner d st' st'' →
      MemberRun tv Inner d st st''
  | inner {st st' st'' : St P} : d + 1 ≤ st.g.A.length → Inner st st' → MemberRun tv Inner d st' st'' →
      MemberRun tv Inner d st st''

theorem Grows.weaken {d : Nat} {g g' : Ghost P} (hg : Grows (d + 1) g g') (hd : 0 < d) : Grows d g g' :=
  ⟨hd, by have := hg.len; omega, by have := hg.len'; omega, hg.record, hg.prot, hg.exposed⟩

theorem Ok.deeper {d : Nat} {st : St P} (hok : Ok d st) (hl : d + 1 ≤ st.g.A.length) : Ok (d + 1) st :=
  ⟨Nat.succ_pos _, hl, hok.uniform, hok.marks, hok.confined, hok.valid, hok.localClosed, hok.bindings⟩

theorem Ok.shallower {d : Nat} {st : St P} (hok : Ok (d + 1) st) (hd : 0 < d) : Ok d st :=
  ⟨hd, by have := hok.len; omega, hok.uniform, hok.marks, hok.confined, hok.valid, hok.localClosed, hok.bindings⟩

/-- **A member's call keeps the invariants, the marks, and grows the
history**, from the step lemma and its runs' bounds one call deeper. -/
theorem MemberRun.ok {tv : TypeView} {Ψ : Protocol P} {Inner : St P → St P → Prop} {d : Nat}
    (hI : ∀ t t', Inner t t' → Ok (d + 1) t → RBound Ψ (d + 1) t t' ∧ Ok (d + 1) t') {st st' : St P}
    (hr : MemberRun tv Inner d st st') (hok : Ok d st) : Ok d st' ∧ Kept st st' ∧ Grows d st.g st'.g := by
  induction hr with
  | nil st => exact ⟨hok, Kept.refl st, Grows.refl hok.pos hok.len⟩
  | step hp _ ih =>
    obtain ⟨ok₁, k₁, g₁⟩ := pkg_step_ok hp hok
    obtain ⟨ok₂, k₂, g₂⟩ := ih ok₁
    exact ⟨ok₂, k₁.trans k₂, g₁.trans g₂⟩
  | inner hl hin _ ih =>
    obtain ⟨⟨k₁, g₁, -⟩, ok₁⟩ := hI _ _ hin (hok.deeper hl)
    obtain ⟨ok₂, k₂, g₂⟩ := ih (ok₁.shallower hok.pos)
    exact ⟨ok₂, k₁.trans k₂, (g₁.weaken hok.pos).trans g₂⟩

/-- **Tolerant invariant at a step** (the draft, the check *Tolerant
invariant*): the invariant `Inv o` of every complete handle `o` after the
step holds, given it of every handle complete before. A handle that the
step completes (by crossing, or by its introduction's `invariant-ensures`)
meets it at once; one still being built is free. -/
def TolerantStep (Inv : Nat → St P → Prop) (Complete : St P → Nat → Prop) (st st' : St P) : Prop :=
  (∀ o, Complete st o → Inv o st) → ∀ o, Complete st' o → Inv o st'

/-- The invariant of a handle type over its complete handles, a member of
`G_P`. -/
def AllComplete (Inv : Nat → St P → Prop) (Complete : St P → Nat → Prop) (st : St P) : Prop :=
  ∀ o, Complete st o → Inv o st

theorem MemberRun.keeps {tv : TypeView} {Ψ : Protocol P} {Inner : St P → St P → Prop} {d : Nat}
    {I : St P → Prop}
    (hI : ∀ t t', Inner t t' → Ok (d + 1) t → RBound Ψ (d + 1) t t' ∧ Ok (d + 1) t')
    (hIk : ∀ t t', Inner t t' → Ok (d + 1) t → I t → I t')
    (hstep : ∀ t t', PkgStep tv d t t' → Ok d t → I t → I t') {st st' : St P}
    (hr : MemberRun tv Inner d st st') (hok : Ok d st) (hi : I st) : I st' := by
  induction hr with
  | nil st => exact hi
  | step hp _ ih => exact ih (pkg_step_ok hp hok).1 (hstep _ _ hp hok hi)
  | inner hl hin _ ih =>
    have ok₁ := (hI _ _ hin (hok.deeper hl)).2
    exact ih (ok₁.shallower hok.pos) (hIk _ _ hin (hok.deeper hl) hi)

/-- **A member's certificate from its checks.** Its call is a checked run
(`MemberRun`). Its certified effect `eff` gives each part a change, and its
certification states that, with its runs of code that is not the package's
bounded on `R_P` by `Ψ_P` one call deeper, the call changes every location
of `R_P` at its entry within `eff` at its part, after `fresh_eff` drops
what it allocated (`certified`, what the pass's check of the member's
body establishes). The protocol is a fixed point over the members: `eff`
is within `Ψ_P` part by part (`within`). Each invariant of `G_P` is kept by
each of its steps (`tolerant`, Tolerant invariant). Then the member meets
`ReadOnlyFrame.Member`. -/
def memberOfChecks (tv : TypeView) (Ψ : Protocol P) (G : (St P → Prop) → Prop) (eff : Protocol P)
    (within : ∀ p, (eff p).le (Ψ p) = true)
    (certified : ∀ (d : Nat) (Inner : St P → St P → Prop),
      (∀ t t', Inner t t' → Ok (d + 1) t → RBound Ψ (d + 1) t t' ∧ Ok (d + 1) t') →
      ∀ st st', MemberRun tv Inner d st st' → Ok d st → ∀ l v, st.g.InR l → st.s.h[l]? = some v →
        ∃ v', st'.s.h[l]? = some v' ∧ (eff (st.part l)).Holds st.s.h.length v v')
    (tolerant : ∀ I, G I → ∀ (d : Nat) t t', PkgStep tv d t t' → Ok d t → I t → I t') :
    Member P Ψ G where
  Call d Inner := MemberRun tv Inner d
  bound d Inner hI st st' hr hok := by
    obtain ⟨ok', hk, hg⟩ := MemberRun.ok hI hr hok
    refine ⟨⟨hk, hg, fun l v hR hv => ?_⟩, ok'⟩
    obtain ⟨v', hv', hc⟩ := certified d Inner hI st st' hr hok l v hR hv
    exact ⟨v', hv', hc.mono (within _)⟩
  keeps I hG d Inner hI hIk st st' hr hok hi :=
    MemberRun.keeps hI hIk (fun t t' hp ho => tolerant I hG d t t' hp ho) hr hok hi

/-! ## The frame's premise, checked -/

/-- A part of a local or an exposed site. -/
def Part.held (p : Part P) : Bool :=
  match p.site.map P.mark with
  | some .local | some .exposed => true
  | _ => false

/-- A part of a released site or outside storage. -/
def Part.lent (p : Part P) : Bool :=
  match p.site.map P.mark with
  | some .released | none => true
  | _ => false

/-- **The check of the frame's premise** (the draft, "At a callback"): for
each region of the support and each part its locations may have (the flow
of possible sites, `parts`), `Ψ_P`'s change at the part is within the
region's, and the part is of a local or an exposed site, or is released or
outside storage of a region a live incoming read-only crossing protects
(`prot`). -/
def insideCheck (Ψ : Protocol P) (S : Footprint) (parts : Region → List (Part P)) (prot : Region → Bool) : Bool :=
  S.all fun e => (parts e.1).all fun p => (Ψ p).le e.2 && (p.held || (prot e.1 && p.lent))

/-- **The check is sound for the frame's premise**, where the flow of
possible sites covers each location's part and a region the check reads as
protected has its released and outside locations recorded in the history. -/
theorem insideCheck_sound {Ψ : Protocol P} {S : Footprint} {parts : Region → List (Part P)}
    {prot : Region → Bool} {ρ : Env} {st : St P} (hc : insideCheck Ψ S parts prot = true)
    (hflow : ∀ e ∈ S, ∀ l, e.1.mem ρ st.s.h l = true → st.part l ∈ parts e.1)
    (hprot : ∀ e ∈ S, prot e.1 = true → ∀ l, e.1.mem ρ st.s.h l = true → st.g.Lent l → st.g.Prot l) :
    Inside Ψ S ρ st := by
  intro e he l hm
  have hp := List.all_eq_true.mp (List.all_eq_true.mp hc e he) _ (hflow e he l hm)
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hp
  obtain ⟨hle, hs⟩ := hp
  refine ⟨?_, hle⟩
  have ho : (st.part l).site.map P.mark = st.g.origin l := rfl
  rcases hs with hh | ⟨hpr, hL⟩
  · simp only [Part.held, ho] at hh
    unfold Ghost.InR
    split at hh <;> simp_all
  · have hLent : st.g.Lent l := by
      simp only [Part.lent, ho] at hL
      unfold Ghost.Lent
      split at hL <;> simp_all
    exact .inr (.inr ⟨hLent, hprot e he hpr l hm hLent⟩)

end Verification.TolerantFrames.ReadOnly
