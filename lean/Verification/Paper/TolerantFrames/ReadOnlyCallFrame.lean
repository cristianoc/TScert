import Verification.Paper.TolerantFrames.ReadOnlyFits
import Verification.Paper.TolerantFrames.ReadOnlyBridge

/-! # Read-only handles: the frame's check at a call, from the sites

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
frame at a call"). At a call of outside code, the pass asks whether a fact
survives the call; the read-only frame answers with `frameCheck` over the
parts each location of the fact's support may have, and `frameCheck_sound`
turns a successful check into `Framed`, the premise of the rule. The parts
are read from the sites:

- **The sites of a region** (`regionSites`): at an environment whose slots
  meet sets of sites (`τ`), the sites of the locations a region names: a
  field of a slot's value, or of the value a path of fields reads from it,
  its spine and the spine's cells, each path step through the contents of
  the heap of sites (`pathSites`). A region of every location of a class,
  of every location, or of a value's field locations by enumeration has
  none here: the check refuses it.
- **They hold** (`regionSites_sound`): in a heap meeting the heap of sites,
  every location of the region is of one of them.
- **The check at a call** (`frameCheckAt`, `framed_of_sites`): the frame's
  check over the parts of those sites, every region of the support given
  sites, gives `Framed` where the query is sound, the roots valid, the
  environment meets the slots' sites, the heap the heap of sites, each
  location's key is among the region's keys, and each lent location of a
  region read as protected has a live history witness
  (`prot_of_witness`).
- **At a frame of `C`'s code** (`frame_sites`, `framed_of_frame`): a frame
  of `C`'s code fitting the flow runs a node of a code of the flow, its
  environment meeting the node's slots; with a heap meeting the flow, the
  check at that node's slots gives `Framed` at the frame's environment.
- **Live protection witnesses** (`Witness.grow`, `entryStart_witness`): a
  location an entry's argument reaches read-only at its parameter's type
  has a witness at the entry history, and at every history the entry's
  grows into inside the call. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

variable {P : Package}

/-- The sites the values held in storage of a set's sites may reach first:
one step through the contents of the heap of sites. -/
def stepSites (H : SiteHeap P) (S : List (Option P.Site)) : List (Option P.Site) := S.flatMap H.contents

/-- The sites of the value a path of fields reads from a value of the
sites `S`. -/
def pathSites (H : SiteHeap P) : List (Option P.Site) → List String → List (Option P.Site)
  | S, [] => S
  | S, _ :: p => pathSites H (stepSites H S) p

/-- **The sites of a region's locations**, at slots of the sites `τ`, or
none where the region is not read from a slot's value through fields. -/
def regionSites (H : SiteHeap P) (τ : Nat → List (Option P.Site)) : Region → Option (List (Option P.Site))
  | .field x _ => some (τ x)
  | .path x p _ => some (pathSites H (τ x) p)
  | .spine x p => some (pathSites H (τ x) p)
  | .cells x => some (stepSites H (τ x))
  | .pathCells x p => some (stepSites H (pathSites H (τ x) p))
  | .inCls r _ => regionSites H τ r
  | .fields _ | .pathFields _ _ | .cls _ | .all => none

theorem stepSites_of {H : SiteHeap P} {S : List (Option P.Site)} {s s' : Option P.Site} (hs : s ∈ S)
    (h' : s' ∈ H.contents s) : s' ∈ stepSites H S :=
  List.mem_flatMap.mpr ⟨s, hs, h'⟩

/-- **A read through a location meets the contents of its site** (proved):
the value a location of a site of `S` holds, in a heap meeting the heap of
sites, meets `stepSites H S`. -/
theorem SitesOf.step {g : Ghost P} {H : SiteHeap P} {h : Heap} {S : List (Option P.Site)} {v u : Val} {a : Label}
    {l : Nat} (hH : HeapSites g H h) (hv : SitesOf g S v) (hn : next v a = some l) (hu : h[l]? = some u) :
    SitesOf g (stepSites H S) u :=
  fun l' hl' => stepSites_of (hv l (Leaves.of_next hn)) ((hH l u hu).1 l' hl')

/-- **A path of fields keeps the sites** (proved): the value a path reads
from a value meeting `S` meets `pathSites H S p`. -/
theorem SitesOf.readPath {g : Ghost P} {H : SiteHeap P} {h : Heap} (hH : HeapSites g H h) :
    ∀ {p : List String} {S : List (Option P.Site)} {v u : Val}, SitesOf g S v →
      HeapKnowledge.readPath h v p = some u → SitesOf g (pathSites H S p) u
  | [], _, _, _, hv, hr => by simp only [HeapKnowledge.readPath] at hr; cases hr; exact hv
  | f :: p, S, v, u, hv, hr => by
    cases v with
    | objAt fs c i =>
      simp only [HeapKnowledge.readPath] at hr
      cases hl : fs.lookup (.str f) with
      | none => simp [hl] at hr
      | some l =>
        cases hu : h[l]? with
        | none => simp [hl, hu] at hr
        | some w =>
          simp only [hl, hu] at hr
          have hn : next (.objAt fs c i) (.key (.str f)) = some l := by simp [next, fieldsOf, hl]
          exact SitesOf.readPath hH (p := p) (S := stepSites H S) (hv.step hH hn hu) hr
    | _ => simp [HeapKnowledge.readPath] at hr

/-- A field location of a value is a first location of it. -/
theorem leaves_field {ofC : ComponentTag → Bool} {v : Val} {k : PropKey} {l : Nat}
    (h : (fieldsOf v).lookup k = some l) : Leaves ofC v l :=
  Leaves.of_next (a := .key k) (by simpa [next] using h)

/-- The spine location a value selects is a first location of it. -/
theorem leaves_elements {ofC : ComponentTag → Bool} {v : Val} {l : Nat}
    (h : HeapKnowledge.elementsOf v = some l) : Leaves ofC v l := by
  cases v with
  | objAt fs c i =>
    simp only [HeapKnowledge.elementsOf] at h
    cases hl : fs.lookup arraySpineKey with
    | some s => rw [hl] at h; cases h; exact leaves_field (k := arraySpineKey) (by simpa [fieldsOf] using hl)
    | none =>
      rw [hl] at h
      cases c <;> simp at h
      cases h
      exact Leaves.of_next (a := .view) (by simp [next, HeapKnowledge.descriptorSpine])
  | _ => simp [HeapKnowledge.elementsOf] at h

/-- **The cells a value's spines list are of the contents of its sites**
(proved): each cell the spine at a first location of the value lists is
held there, of a site the contents of that location's site give. -/
theorem cells_sites {g : Ghost P} {H : SiteHeap P} {h : Heap} {S : List (Option P.Site)} {v : Val} {l : Nat}
    (hH : HeapSites g H h) (hv : SitesOf g S v) (hc : (spineCells h v).contains (some l) = true) :
    g.site l ∈ stepSites H S := by
  have hc' : some l ∈ spineCells h v := List.contains_iff_mem.mp hc
  -- The spine location `s`, a first location of `v`, holds the spine whose
  -- entries list `l`.
  have key : ∀ (o : Option Nat) (a : Label), next v a = o → some l ∈ entriesAt h o → g.site l ∈ stepSites H S := by
    intro o a ho hl
    cases o with
    | none => simp [entriesAt] at hl
    | some s =>
      simp only [entriesAt] at hl
      cases hs : h[s]? with
      | none => simp [hs] at hl
      | some sp =>
        rw [hs] at hl
        cases he : spineEntries sp with
        | none => simp [he] at hl
        | some ls =>
          simp only [he, Option.bind_some, Option.getD_some] at hl
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hl
          have hn : next sp (.cell i) = some l := by simp [next, he, hi]
          exact stepSites_of (hv s (Leaves.of_next ho))
            ((hH s sp hs).1 l (Leaves.of_next hn))
  simp only [spineCells, List.mem_append] at hc'
  rcases hc' with h1 | h2
  · exact key _ (.key arraySpineKey) (by simp [next]) h1
  · exact key _ .view (by simp [next]) h2

/-- **The sites of a region hold** (proved): at an environment whose slots
meet `τ` and a heap meeting the heap of sites, every location of a region
given sites is of one of them. -/
theorem regionSites_sound {g : Ghost P} {H : SiteHeap P} {h : Heap} {τ : Nat → List (Option P.Site)} {ρ : Env}
    (hH : HeapSites g H h) (henv : ∀ i, SitesOf g (τ i) (ρ i)) :
    ∀ {r : Region} {T : List (Option P.Site)} {l : Nat}, regionSites H τ r = some T → r.mem ρ h l = true →
      g.site l ∈ T := by
  intro r
  induction r with
  | field x k =>
    intro T l hr hm
    simp only [regionSites, Option.some.injEq] at hr; subst hr
    simp only [Region.mem, beq_iff_eq] at hm
    exact henv x l (leaves_field hm)
  | path x p k =>
    intro T l hr hm
    simp only [regionSites, Option.some.injEq] at hr; subst hr
    simp only [Region.mem] at hm
    cases hp : HeapKnowledge.readPath h (ρ x) p with
    | none => rw [hp] at hm; cases hm
    | some u =>
      rw [hp, beq_iff_eq] at hm
      exact (SitesOf.readPath hH (henv x) hp) l (leaves_field hm)
  | spine x p =>
    intro T l hr hm
    simp only [regionSites, Option.some.injEq] at hr; subst hr
    simp only [Region.mem] at hm
    cases hp : HeapKnowledge.readPath h (ρ x) p with
    | none => rw [hp] at hm; cases hm
    | some u =>
      rw [hp, beq_iff_eq] at hm
      exact (SitesOf.readPath hH (henv x) hp) l (leaves_elements hm)
  | cells x =>
    intro T l hr hm
    simp only [regionSites, Option.some.injEq] at hr; subst hr
    exact cells_sites hH (henv x) hm
  | pathCells x p =>
    intro T l hr hm
    simp only [regionSites, Option.some.injEq] at hr; subst hr
    simp only [Region.mem] at hm
    cases hp : HeapKnowledge.readPath h (ρ x) p with
    | none => rw [hp] at hm; cases hm
    | some u =>
      rw [hp] at hm
      exact cells_sites hH (SitesOf.readPath hH (henv x) hp) hm
  | inCls r c ih =>
    intro T l hr hm
    simp only [regionSites] at hr
    simp only [Region.mem, Bool.and_eq_true] at hm
    exact ih hr hm.1
  | fields _ => intro _ _ hr; simp [regionSites] at hr
  | pathFields _ _ => intro _ _ hr; simp [regionSites] at hr
  | cls _ => intro _ _ hr; simp [regionSites] at hr
  | all => intro _ _ hr; simp [regionSites] at hr

/-- **The parts at a call**: a region's sites' parts, at its keys. -/
def callParts (H : SiteHeap P) (τ : Nat → List (Option P.Site)) (keys : Region → List (Option PropKey))
    (r : Region) : List (Part P) :=
  partsOf ((regionSites H τ r).getD []) (keys r) r

/-- **The frame's check at a call**: every region of the support given
sites, and the check over their parts. -/
def frameCheckAt (q : SepQuery) (Ψ : Protocol P) (Φ S : Footprint) (H : SiteHeap P)
    (τ : Nat → List (Option P.Site)) (keys : Region → List (Option PropKey)) (prot : Region → Bool) : Bool :=
  S.all (fun e => (regionSites H τ e.1).isSome) && frameCheck q Ψ Φ S (callParts H τ keys) prot

/-- **The frame's check at a call gives the rule's premise** (proved, by
`flow_of_sites`, `regionSites_sound` and `frameCheck_sound`): where the
query is sound, the roots valid, the environment meets the slots' sites,
the heap the heap of sites, each location's key is among its region's,
and each lent location of a region read as protected has a live history
witness. -/
theorem framed_of_sites {q : SepQuery} {Ψ : Protocol P} {Φ S : Footprint} {H : SiteHeap P}
    {τ : Nat → List (Option P.Site)} {keys : Region → List (Option PropKey)} {prot : Region → Bool}
    {tv : TypeView} {d : Nat} {ρ : Env} {st : St P}
    (hc : frameCheckAt q Ψ Φ S H τ keys prot = true) (hq : q.Sound ρ st.s.h) (hρ : RootsOk st.s.W ρ)
    (henv : ∀ i, SitesOf st.g (τ i) (ρ i)) (hH : HeapSites st.g H st.s.h)
    (hkey : ∀ e ∈ S, ∀ l, l < st.s.h.length → e.1.mem ρ st.s.h l = true → st.g.key l ∈ keys e.1)
    (hw : ∀ e ∈ S, prot e.1 = true → ∀ l, l < st.s.h.length → e.1.mem ρ st.s.h l = true → st.g.Lent l →
      Witness tv d st l) :
    Framed Φ Ψ S ρ st := by
  simp only [frameCheckAt, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hsome, hc⟩ := hc
  refine frameCheck_sound hc hq ?_ (prot_of_witness hw)
  intro e he l hl hm
  have hsite : ∀ e' ∈ S, ∀ l, l < st.s.h.length → e'.1.mem ρ st.s.h l = true →
      st.g.site l ∈ (regionSites H τ e'.1).getD [] := by
    intro e' he' l' _ hm'
    obtain ⟨T', hT'⟩ := Option.isSome_iff_exists.mp (hsome e' he')
    rw [hT']
    exact regionSites_sound hH henv hT' hm'
  exact flow_of_sites (sites := fun r => (regionSites H τ r).getD []) hρ hsite hkey e he l hl hm

/-- **A frame of `C`'s code runs at a node whose slots its environment
meets** (proved, the rule `Fits.frameC`). -/
theorem frame_sites {Fl : Flow P} {g : Ghost P} {n : Nat} {Γ : Nat → Option (Sites P)} {a : Alloc P} {o : Bool}
    {S : Sites P} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {t : Tm}
    {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    (hf : Fits Fl (VJ Fl g n) Γ a o S (.frame E K t L d k x comp)) (hc : P.ofC comp = true) :
    ∃ π l, Fl.code (E, K) = some π ∧ NodeOf (E, K) l k x ∧ ∀ i, SitesOf g (π.env l i) (envOf L d i) := by
  cases hf with
  | val hv => simp [isVal] at hv
  | frameC π l _ hcode hn henv => exact ⟨π, l, hcode, hn, fun i => (henv i).sites⟩
  | frameOut hc' => rw [hc] at hc'; cases hc'

/-- **The check at a frame of `C`'s code gives the rule's premise**
(proved): a frame of `C`'s code fitting the flow, at a heap meeting it, runs
a node whose slots' sites give `Framed` at the frame's environment through
the check at a call (`framed_of_sites`). -/
theorem framed_of_frame {Fl : Flow P} {Γ : Nat → Option (Sites P)} {a : Alloc P} {o : Bool}
    {S₀ : Sites P} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {t : Tm}
    {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    {st : St P} (hf : Fits Fl (VJ Fl st.g st.s.h.length) Γ a o S₀ (.frame E K t L d k x comp))
    (hc : P.ofC comp = true) (hH : HeapInv Fl st.g st.s.h) :
    ∃ π l, Fl.code (E, K) = some π ∧ NodeOf (E, K) l k x ∧
      ∀ {q : SepQuery} {Ψ : Protocol P} {Φ S : Footprint} {keys : Region → List (Option PropKey)}
        {prot : Region → Bool} {tv : TypeView} {dp : Nat},
        frameCheckAt q Ψ Φ S Fl.H (π.env l) keys prot = true → q.Sound (envOf L d) st.s.h →
        RootsOk st.s.W (envOf L d) →
        (∀ e ∈ S, ∀ w, w < st.s.h.length → e.1.mem (envOf L d) st.s.h w = true → st.g.key w ∈ keys e.1) →
        (∀ e ∈ S, prot e.1 = true → ∀ w, w < st.s.h.length → e.1.mem (envOf L d) st.s.h w = true →
          st.g.Lent w → Witness tv dp st w) →
        Framed Φ Ψ S (envOf L d) st := by
  obtain ⟨π, l, hcode, hn, henv⟩ := frame_sites hf hc
  exact ⟨π, l, hcode, hn, fun hck hq hρ hkey hw => framed_of_sites hck hq hρ henv hH.sites hkey hw⟩

/-! ## Live protection witnesses -/

/-- **A witness stays live as the history grows** (proved, `Grows.trans`). -/
theorem Witness.grow {tv : TypeView} {d : Nat} {st st' : St P} {l : Nat} (hw : Witness tv d st l)
    (hg : Grows d st.g st'.g) : Witness tv d st' l := by
  obtain ⟨g, T, h, v, hA, hr, hL, hgr⟩ := hw
  exact ⟨g, T, h, v, hA, hr, hL, hgr.trans hg⟩

/-- **An entry's argument is witnessed** (proved): at the entry history, a
location an argument reaches read-only at its parameter's type, inside a
call of `C`, has a live witness at every depth up to the calls active: the
argument's crossing reached it while it was outside storage, and the
crossings after it grow the history. -/
theorem entryStart_witness {F : Family} {C : Nat} {tv : TypeView} {h : Heap} {t : Tm} {args : List (tv.Ty × Val)}
    {d : Nat} (hd : 0 < d) (hdl : d ≤ depthC F C none t) {T : tv.Ty} {v : Val} (ha : (T, v) ∈ args) {l : Nat}
    (hr : ReachRO tv (F.at C).ofC T h v l) {st : St (F.at C)} (hst : st.g = entryStart F C tv h t args) :
    Witness tv d st l := by
  suffices ∀ (xs : List (Crossing tv)) (g : Ghost (F.at C)), d ≤ g.A.length → g.site = (fun _ => none) →
      g.Uniform → ∀ x ∈ xs, x.dir = .into → ReachRO tv (F.at C).ofC x.ty h x.val l →
      ∃ (g₀ : Ghost (F.at C)) (T₀ : tv.Ty) (v₀ : Val), g₀.A ≠ [] ∧ ReachRO tv (F.at C).ofC T₀ h v₀ l ∧
        g₀.Lent l ∧ Grows d (g₀.cross tv .into T₀ h v₀) (Ghost.crosses tv h xs g) by
    obtain ⟨g₀, T₀, v₀, hA, hr₀, hL, hg⟩ := this (args.map fun a => ⟨.into, a.1, a.2⟩) (bareStart F C t)
      (by simpa [bareStart] using hdl) rfl
      (bareStart_uniform F C t) ⟨.into, T, v⟩ (List.mem_map.mpr ⟨(T, v), ha, rfl⟩) rfl hr
    exact ⟨g₀, T₀, h, v₀, hA, hr₀, hL, by rw [hst]; exact hg⟩
  intro xs
  induction xs with
  | nil => intro _ _ _ _ x hx; cases hx
  | cons y ys ih =>
    intro g hl hs hu x hx hdir hrx
    have hl' : d ≤ (g.cross tv y.dir y.ty h y.val).A.length := by simpa [Ghost.cross, Ghost.add] using hl
    have hu' := (HStep.cross (h := h) g y.dir y.ty y.val).uniform hu
    rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨g, x.ty, x.val, ?_, hrx, .inr (by simp [Ghost.origin, hs]), ?_⟩
      · intro hA; rw [hA] at hl; simp at hl; omega
      · rw [← hdir]
        exact ((Ghost.crosses_hsteps (d := d) ys _ hl').grows hu' hd hl').1
    · exact ih _ hl' (by rw [← hs]; rfl) hu' x hx hdir hrx

end Verification.TolerantFrames.ReadOnly
