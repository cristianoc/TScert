import Verification.Paper.TolerantFrames.ReadOnlyCrossings

/-! # Read-only handles: the sites a value may reach

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
sites a value may reach"). The checks of `C`'s code read, for each value
of an execution, the sites of the locations it may reach, `none` the site
of outside storage. The abstraction is a finite set of sites per value and
a heap of sites (`SiteHeap`): for each site, the sites the storage of that
site may reference, outside storage included.

- **A value meets a set of sites** (`SitesOf`): every first location the
  value reaches (`Leaves`: through a field, a spine or a cell, or through
  the code of a closure of outside code or of a bound function) is of a
  site of the set.
- **A heap meets a heap of sites** (`HeapSites`): the value of each
  location meets the sites the heap of sites gives the location's site.
- **A set closed in a heap of sites** (`Closed`): the sites the storage of
  each of its sites may reference are in it.
- **Reach** (`reach_sites`): in a heap meeting a heap of sites, a value
  meeting a closed set reaches only locations of sites of the set.
- **The marks at a crossing** (`crossOk_of_sites`): a crossing whose
  value meets a closed set of released sites and outside storage meets
  the marks (`CrossOk`).
- **Steps** (`HeapSites.set`, `HeapSites.alloc`): a write of a value
  meeting the sites of the written location's site, and an allocation of
  values each meeting the sites of its fresh location's site, keep the
  heap meeting the heap of sites.
- **Local storage** (`localStores_of_sites`, `localBindings_of_sites`):
  where storage of a site that is not local references no local site
  (`LocalHeld`) and no binding reaches one, the stores of a step keep
  local storage closed.
- **The checks at the actual crossings** (`escapeAt_of_sites`): where every
  root of outside code after a step meets a closed set `O` of released
  sites and outside storage, every actual crossing meets the marks: a new
  root by itself, a value left where outside code reaches because its
  location is of a site of `O`, whose contents `O` holds. At a frame
  (`ClientFrame.SitesSound`, `chkSound_of_sites`), `ChkSound` holds where
  the flow of `C`'s code gives these two at each step of its code.
- **Outside code** (`sites_outside`, `ClientFrame.sitesAt_outside`): where
  `O` holds outside storage and every site of `O` may hold every value of
  `O` (`OutsideWritable`), a step of outside code keeps the heap meeting
  the heap of sites and the roots meeting `O` (`SitesAt`): it changes only
  what its roots reach, leaves there only what they reach or what it
  allocates, outside storage, and its roots reach afterwards nothing else.
  The entry history meets both (`ClientFrame.sitesAt_lentStart`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification

variable {P : Package}

/-- **A heap of sites**: for each site, `none` for outside storage, the
sites the storage of that site may reference. -/
structure SiteHeap (P : Package) where
  contents : Option P.Site → List (Option P.Site)
  /-- The sites the values the code of a closure of outside code or of a
  bound function held in that storage binds may reach first. -/
  bindings : Option P.Site → List (Option P.Site)

/-- **A value meets a set of sites**: every first location it reaches is
of a site of the set. -/
def SitesOf (g : Ghost P) (S : List (Option P.Site)) (v : Val) : Prop :=
  ∀ l, Leaves P.ofC v l → g.site l ∈ S

/-- **A heap meets a heap of sites**: the value of each location meets the
sites of the location's site. -/
def HeapSites (g : Ghost P) (H : SiteHeap P) (h : Heap) : Prop :=
  ∀ w u, h[w]? = some u → SitesOf g (H.contents (g.site w)) u ∧
    ∀ x ∈ codeVals P.ofC u, SitesOf g (H.bindings (g.site w)) x

/-- **A set of sites closed in a heap of sites**. -/
def Closed (H : SiteHeap P) (S : List (Option P.Site)) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ H.contents s, s' ∈ S

/-- **A value its code holds meets the sites of the value** (proved). -/
theorem SitesOf.code {g : Ghost P} {S : List (Option P.Site)} {v x : Val} (hv : SitesOf g S v)
    (hx : x ∈ codeVals P.ofC v) : SitesOf g S x :=
  fun l hl => hv l (Leaves.code hx hl)

/-- **A larger set** (proved). -/
theorem SitesOf.mono {g : Ghost P} {S S' : List (Option P.Site)} {v : Val} (hv : SitesOf g S v)
    (hS : ∀ s ∈ S, s ∈ S') : SitesOf g S' v :=
  fun l hl => hS _ (hv l hl)

/-- **Reach** (proved): in a heap meeting a heap of sites, a value meeting
a closed set reaches only locations of its sites. -/
theorem reach_sites {g : Ghost P} {H : SiteHeap P} {h : Heap} {S : List (Option P.Site)} (hH : HeapSites g H h)
    (hS : Closed H S) : ∀ {v : Val}, SitesOf g S v → ∀ l, Reaches P.ofC h v l → g.site l ∈ S := by
  have key : ∀ (π : List Label) (v : Val) (l : Nat), SitesOf g S v → Follows P.ofC h v π l → g.site l ∈ S := by
    intro π
    induction π with
    | nil => intro _ _ _ hf; exact hf.elim
    | cons a π ih =>
      intro v l hv hf
      cases π with
      | nil => exact hv l (Leaves.of_next hf)
      | cons b π =>
        obtain ⟨v₀, hs, hf⟩ := hf
        refine ih v₀ l ?_ hf
        rcases hs with ⟨l₀, hn, hl₀⟩ | ⟨i, -, hi⟩
        · intro l' hl'
          exact hS _ (hv l₀ (Leaves.of_next hn)) _ ((hH l₀ v₀ hl₀).1 l' hl')
        · exact hv.code (List.mem_of_getElem? hi)
  intro v hv l ⟨π, hf⟩
  exact key π v l hv hf

/-- **Sites a crossing may reach** (`CrossOk`'s premise): released sites and
outside storage. -/
def Lendable (S : List (Option P.Site)) : Prop := ∀ s ∈ S, ∀ s', s = some s' → P.mark s' = .released

/-- **The marks at a crossing** (proved): a crossing whose value meets a
closed set of released sites and outside storage reaches no local, internal
or exposed location. -/
theorem crossOk_of_sites {tv : TypeView} {g : Ghost P} {H : SiteHeap P} {h : Heap} {S : List (Option P.Site)}
    {c : Crossing tv} (hH : HeapSites g H h) (hS : Closed H S) (hL : Lendable S) (hv : SitesOf g S c.val) :
    CrossOk tv g h c := by
  intro l hr
  have hs := reach_sites hH hS hv l hr
  unfold Ghost.origin
  cases hsl : g.site l with
  | none => simp
  | some s =>
    rw [hsl] at hs
    simp [hL _ hs s rfl]

/-- **A write keeps the heap meeting the heap of sites** (proved): the
written value meets the sites of the written location's site. -/
theorem HeapSites.set {g : Ghost P} {H : SiteHeap P} {h : Heap} {w : Nat} {u : Val} (hH : HeapSites g H h)
    (hu : SitesOf g (H.contents (g.site w)) u)
    (hb : ∀ x ∈ codeVals P.ofC u, SitesOf g (H.bindings (g.site w)) x) : HeapSites g H (h.set w u) := by
  intro x v hx
  rw [List.getElem?_set] at hx
  split at hx
  · rename_i he; subst he; split at hx
    · cases hx; exact ⟨hu, hb⟩
    · cases hx
  · exact hH x v hx

/-- **A value whose locations exist keeps its sites at an allocation**
(proved): the allocation keeps the site of every old location. -/
theorem SitesOf.alloc {g : Ghost P} {S : List (Option P.Site)} {v : Val} {n : Nat}
    {site : Nat → Option P.Site} {key : Nat → Option PropKey} (hv : SitesOf g S v)
    (hn : ∀ l, Leaves P.ofC v l → l < n) : SitesOf (g.alloc n site key) S v := by
  intro l hl
  rw [(Ghost.alloc_old (hn l hl)).1]
  exact hv l hl

/-- **An allocation keeps the heap meeting the heap of sites** (proved):
the old values reference old locations, and each new value meets the sites
of its fresh location's site. -/
theorem HeapSites.alloc {g : Ghost P} {H : SiteHeap P} {h : Heap} {xs : List Val} {site : Nat → Option P.Site}
    {key : Nat → Option PropKey} (hH : HeapSites g H h)
    (hold : ∀ (w : Nat) (u : Val), h[w]? = some u → ∀ l, Leaves P.ofC u l → l < h.length)
    (hnew : ∀ (i : Nat) (u : Val), xs[i]? = some u →
      SitesOf (g.alloc h.length site key) (H.contents (site (h.length + i))) u ∧
      ∀ x ∈ codeVals P.ofC u, SitesOf (g.alloc h.length site key) (H.bindings (site (h.length + i))) x) :
    HeapSites (g.alloc h.length site key) H (h ++ xs) := by
  intro w u hw
  by_cases hlt : w < h.length
  · rw [List.getElem?_append_left hlt] at hw
    rw [(Ghost.alloc_old hlt).1]
    exact ⟨(hH w u hw).1.alloc (hold w u hw), fun x hx => ((hH w u hw).2 x hx).alloc
      (fun l hl => hold w u hw l (Leaves.code hx hl))⟩
  · rw [List.getElem?_append_right (by omega)] at hw
    have hs : (g.alloc h.length site key).site w = site (h.length + (w - h.length)) := by
      simp [Ghost.alloc, hlt, show h.length + (w - h.length) = w by omega]
    rw [hs]
    exact hnew _ u hw

/-! ## Local storage -/

/-- **No local site** in a set. -/
def NoLocal (S : List (Option P.Site)) : Prop := ∀ s ∈ S, ∀ s', s = some s' → P.mark s' ≠ .local

/-- **Local storage is held only by local storage** in a heap of sites:
storage of a site that is not local references no local site. -/
def LocalHeld (H : SiteHeap P) : Prop :=
  ∀ s, (∀ s', s = some s' → P.mark s' ≠ .local) → NoLocal (H.contents s)

/-- **Closed local storage** (proved, `PkgProps.localStores`): in a heap
meeting a heap of sites where local storage is held only by local storage,
a location referencing a local location is local. -/
theorem localStores_of_sites {g : Ghost P} {H : SiteHeap P} {h h' : Heap} (hH : HeapSites g H h')
    (hL : LocalHeld H) :
    ∀ w u, ¬ Same h h' w → h'[w]? = some u → ∀ a l, next u a = some l → g.origin l = some .local →
      g.origin w = some .local := by
  intro w u _ hu a l hn hl
  have hs := (hH w u hu).1 l (Leaves.of_next hn)
  obtain ⟨sl, hsl, hml⟩ := Option.map_eq_some_iff.mp hl
  rw [hsl] at hs
  refine Classical.byContradiction fun hw => ?_
  have hnl : ∀ s', g.site w = some s' → P.mark s' ≠ .local := by
    intro s' hs' hm
    exact hw (by simp [Ghost.origin, hs', hm])
  exact hL _ hnl _ hs sl rfl hml

/-- **Closed bindings** (proved, `PkgProps.localBindings`): in a heap
meeting a heap of sites whose bindings reach no local site, no value the
code of a stored closure binds reaches a local location first. -/
theorem localBindings_of_sites {g : Ghost P} {H : SiteHeap P} {h h' : Heap} (hH : HeapSites g H h')
    (hB : ∀ s, NoLocal (H.bindings s)) :
    ∀ w u, ¬ Same h h' w → h'[w]? = some u → ∀ x ∈ codeVals P.ofC u, ∀ l, Leaves P.ofC x l →
      g.origin l ≠ some .local := by
  intro w u _ hu x hx l hl hloc
  have hs := (hH w u hu).2 x hx l hl
  obtain ⟨sl, hsl, hml⟩ := Option.map_eq_some_iff.mp hloc
  rw [hsl] at hs
  exact hB _ _ hs sl rfl hml

/-! ## The checks at the actual crossings -/

variable {F : Family} {C : Nat} {tv : TypeView}

/-- **The checks at a step of `C`'s code from the sites** (proved): where
the heap after the step meets a heap of sites in which local storage is
held only by local storage and bindings reach no local site, and every
root of outside code after the step meets a closed set of released sites
and outside storage, every actual crossing meets the marks and the step's
stores keep local storage closed. A value left where outside code reaches
is in storage of a site of that set, whose contents the set holds. -/
theorem escapeAt_of_sites (T : tv.Ty) {x y : Conf} {g g' mid : Ghost (F.at C)} {H : SiteHeap (F.at C)}
    {O : List (Option (F.at C).Site)} (hH : HeapSites mid H y.s.h) (hO : Closed H O) (hlend : Lendable O)
    (hL : LocalHeld H) (hB : ∀ s, NoLocal (H.bindings s))
    (hroots : ∀ r ∈ rootsOf F C none y.t, SitesOf mid O r) :
    EscapeAt (lift F C none x g) (lift F C none y g') mid (actualXs F C T x.s.h x.t y.s.h y.t) where
  crossOk := by
    intro c hc
    simp only [actualXs, List.mem_map] at hc
    obtain ⟨v, hv, rfl⟩ := hc
    refine crossOk_of_sites hH hO hlend ?_
    rcases List.mem_append.mp hv with hn | hl
    · exact hroots v (List.mem_filter.mp hn).1
    · simp only [leftVals, List.mem_filterMap, List.mem_range] at hl
      obtain ⟨w, -, hw⟩ := hl
      split at hw
      · rename_i hr
        obtain ⟨⟨r, hr', hreach⟩, -⟩ := hr
        have hsw := reach_sites hH hO (hroots r hr') w hreach
        exact ((hH w v hw).1).mono (hO _ hsw)
      · cases hw
  localStores := localStores_of_sites hH hL
  localBindings := localBindings_of_sites hH hB

/-! ## A step of outside code -/

/-- **Outside storage may hold every value outside code holds**: the
contents and the bindings of each site of `O` hold `O`. -/
def OutsideWritable (H : SiteHeap P) (O : List (Option P.Site)) : Prop :=
  ∀ s ∈ O, ∀ s' ∈ O, s' ∈ H.contents s ∧ s' ∈ H.bindings s

/-- The heap's values reference allocated locations (proved). -/
theorem heap_leaves_lt {s : IndexedHeap} {ofC : ComponentTag → Bool} {w : Nat} {u : Val} (hu : s.h[w]? = some u) :
    ∀ l, Leaves ofC u l → l < s.h.length :=
  fun _ hl => Leaves.lt (s := s) (RefsOk.refsOkN (contents_valid (List.getElem?_eq_some_iff.mp hu).1 hu)) hl

/-- **A step of outside code keeps the sites** (proved): where the heap
meets a heap of sites, the roots of outside code meet a set `O` closed in
it that holds outside storage, and outside storage may hold every value
of `O`, after a step of outside code, with what it allocates outside
storage, the heap meets the heap of sites and the roots meet `O`. Outside
code changes only locations its roots reach and leaves in them only what
they reach or what it allocates (`outsideStep_reach`,
`outsideStep_writes`), and its roots reach afterwards only what they
reached or what it allocated (`outsideStep_noForge`). -/
theorem sites_outside {x y : Conf} {g : Ghost (F.at C)} {key : Nat → Option PropKey} {H : SiteHeap (F.at C)}
    {O : List (Option (F.at C).Site)} (hs : AStep x y) (hact : Outside F C none x) (hO : Closed H O)
    (hnone : none ∈ O) (hW : OutsideWritable H O) (hH : HeapSites g H x.s.h)
    (hR : ∀ r ∈ rootsOf F C none x.t, SitesOf g O r) :
    HeapSites (g.alloc x.s.h.length (fun _ => none) key) H y.s.h ∧
      ∀ r ∈ rootsOf F C none y.t, SitesOf (g.alloc x.s.h.length (fun _ => none) key) O r := by
  let g' := g.alloc x.s.h.length (fun _ => none) key
  have hr0 : (lift F C none x g).roots = vals (F.ofC C) (!F.ofC C none) x.t := rfl
  have hr1 : (lift F C none y g').roots = vals (F.ofC C) (!F.ofC C none) y.t := rfl
  -- A location the old roots reach, or a fresh one, is of a site of `O`.
  have hsite : ∀ l, ReachesFrom (F.at C).ofC x.s.h (rootsOf F C none x.t) l ∨ x.s.h.length ≤ l →
      g'.site l ∈ O := by
    intro l hl
    by_cases hlt : l < x.s.h.length
    · have he : g'.site l = g.site l := (Ghost.alloc_old hlt).1
      rw [he]
      rcases hl with ⟨r, hr, hreach⟩ | hge
      · exact reach_sites hH hO (hR r hr) l hreach
      · omega
    · have he : g'.site l = none := by simp [g', Ghost.alloc, hlt]
      rw [he]; exact hnone
  have hwr := outsideStep_writes (st := lift F C none x g) (st' := lift F C none y g') hs.step hact hr0
  have hreach := outsideStep_reach (st := lift F C none x g) (st' := lift F C none y g') hs.step hact hr0
  have hnf := outsideStep_noForge (st := lift F C none x g) (st' := lift F C none y g') hs.step hact hr0 hr1
  refine ⟨fun w u hu => ?_, fun r hr l hl => ?_⟩
  · by_cases hsame : ∃ v : Val, x.s.h[w]? = some v ∧ y.s.h[w]? = some v
    · obtain ⟨v, hv, hv'⟩ := hsame
      obtain rfl : v = u := Option.some.inj (hv'.symm.trans hu)
      have hw : w < x.s.h.length := (List.getElem?_eq_some_iff.mp hv).1
      have he : g'.site w = g.site w := (Ghost.alloc_old hw).1
      rw [he]
      exact ⟨(hH w v hv).1.alloc (heap_leaves_lt hv), fun x' hx => ((hH w v hv).2 x' hx).alloc
        (fun l hl => heap_leaves_lt hv l (Leaves.code hx hl))⟩
    · -- A changed or allocated location: reached by the old roots, or fresh.
      have hsw : g'.site w ∈ O := by
        apply hsite
        by_cases hlt : w < x.s.h.length
        · obtain ⟨v, hv⟩ : ∃ v, x.s.h[w]? = some v := ⟨_, List.getElem?_eq_getElem hlt⟩
          refine .inl (hreach w ⟨v, hv, fun h' => hsame ⟨v, hv, h'⟩⟩)
        · exact .inr (by omega)
      refine ⟨fun l hl => (hW _ hsw _ (hsite l (hwr w u hsame hu l hl))).1, fun x' hx l hl =>
        (hW _ hsw _ (hsite l (hwr w u hsame hu l (Leaves.code hx hl)))).2⟩
  · exact hsite l (hnf l ⟨r, hr, hl.reaches⟩)

/-- **The sites read only the ghost's sites** (proved). -/
theorem SitesOf.congr {g g' : Ghost P} {S : List (Option P.Site)} {v : Val} (he : g'.site = g.site)
    (hv : SitesOf g S v) : SitesOf g' S v := by
  intro l hl; rw [he]; exact hv l hl

theorem HeapSites.congr {g g' : Ghost P} {H : SiteHeap P} {h : Heap} (he : g'.site = g.site)
    (hH : HeapSites g H h) : HeapSites g' H h := by
  intro w u hu
  rw [he]
  exact ⟨(hH w u hu).1.congr he, fun x hx => ((hH w u hu).2 x hx).congr he⟩

/-- The sites after a step of outside code are its allocation's (proved). -/
theorem outsideNextAt_site {key : Nat → Option PropKey} {len : Nat} {h' : Heap} {t' : Tm} {g : Ghost (F.at C)} :
    (outsideNextAt F C none key len h' t' g).site = (g.alloc len (fun _ => none) key).site := by
  unfold outsideNextAt; split <;> rfl

namespace ClientFrame
variable {τ : Type} (fr : ClientFrame τ)

/-- **What the flow of `C`'s code establishes**: at each step of its code
from a reached state, the heap after the step meets the heap of sites `H`
at the ghost after its allocation, and every root of outside code after
it meets `O`. -/
def SitesSound (H : SiteHeap (fr.F.at fr.C)) (O : List (Option (fr.F.at fr.C).Site)) : Prop :=
  ∀ a b, fr.Reached a → fr.KStep a b → kind fr.F fr.C none a.1 b.1 ≠ .outside →
    HeapSites (midOf fr.chkConf a.1 b.1 a.2) H b.1.s.h ∧
      ∀ r ∈ rootsOf fr.F fr.C none b.1.t, SitesOf (midOf fr.chkConf a.1 b.1 a.2) O r

/-- **The sites at a state**: its heap meets the heap of sites, and the
roots of outside code meet `O`. -/
def SitesAt (H : SiteHeap (fr.F.at fr.C)) (O : List (Option (fr.F.at fr.C).Site))
    (a : Conf × Ghost (fr.F.at fr.C)) : Prop :=
  HeapSites a.2 H a.1.s.h ∧ ∀ r ∈ rootsOf fr.F fr.C none a.1.t, SitesOf a.2 O r


variable {fr}

/-- **A step of outside code keeps the sites at a state** (proved,
`sites_outside`): the history after it has its allocation's sites. -/
theorem sitesAt_outside {H : SiteHeap (fr.F.at fr.C)} {O : List (Option (fr.F.at fr.C).Site)}
    (hO : Closed H O) (hnone : none ∈ O) (hW : OutsideWritable H O) {a b : Conf × Ghost (fr.F.at fr.C)}
    (hk : fr.KStep a b) (ho : kind fr.F fr.C none a.1 b.1 = .outside) (ha : fr.SitesAt H O a) :
    fr.SitesAt H O b := by
  obtain ⟨hs, hg, -⟩ := hk
  have hact := ((kind_spec (F := fr.F) (C := fr.C) (c := none) a.1 b.1).1 ho).1
  have hsite : b.2.site = (a.2.alloc a.1.s.h.length (fun _ => none) (fr.chkConf a.1 b.1).key).site := by
    rw [hg, fr.next_conf]
    simp only [Ghost.next, Ghost.stepAt, stepKind_conf, ho]
    exact outsideNextAt_site
  obtain ⟨hH, hR⟩ := sites_outside (key := (fr.chkConf a.1 b.1).key) hs hact hO hnone hW ha.1 ha.2
  exact ⟨hH.congr hsite, fun r hr => (hR r hr).congr hsite⟩

/-- **The sites at an entry** (proved): every location of the entry history
is outside storage, which `O` holds and outside storage may hold. -/
theorem sitesAt_lentStart {H : SiteHeap (fr.F.at fr.C)} {O : List (Option (fr.F.at fr.C).Site)}
    (hnone : none ∈ O) (hW : OutsideWritable H O) (x : Conf) :
    fr.SitesAt H O (x, lentStart fr.F fr.C x.t) := by
  have hc := hW none hnone none hnone
  refine ⟨fun w u _ => ⟨fun l _ => hc.1, fun _ _ l _ => hc.2⟩, fun r _ l _ => hnone⟩

/-- **`ChkSound` from the flow** (proved): at the actual crossings, where
`O` is closed in `H` and holds released sites and outside storage only,
local storage is held only by local storage and no binding reaches a local
site, the flow gives the checks (`escapeAt_of_sites`), and the checks
`ChkSound` (`chkSound_of_escape`). -/
theorem chkSound_of_sites {T : τ} {H : SiteHeap (fr.F.at fr.C)} {O : List (Option (fr.F.at fr.C).Site)}
    (hx : fr.ActualCrossings T) (hO : Closed H O) (hlend : Lendable O) (hL : LocalHeld H)
    (hB : ∀ s, NoLocal (H.bindings s)) (hs : fr.SitesSound H O) : fr.ChkSound := by
  refine chkSound_of_escape hx fun a b ha hk ho => ?_
  obtain ⟨hH, hr⟩ := hs a b ha hk ho
  have hxs : (fr.chkConf a.1 b.1).xs = actualXs (tv := fr.view.view) fr.F fr.C T a.1.s.h a.1.t b.1.s.h b.1.t :=
    hx _ _ _ _
  rw [hxs]
  exact escapeAt_of_sites (tv := fr.view.view) T hH hO hlend hL hB hr

end ClientFrame

end Verification.TolerantFrames.ReadOnly
