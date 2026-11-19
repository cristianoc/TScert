import Verification.Paper.TolerantFrames.ReadOnlyFitsReach
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
  check at that node's slots gives `Framed` at the frame's environment;
  at a reached state whose term is a frame of `C`'s code, the call of the
  unit's own frame, every reached state fitting the flow
  (`ClientFrame.framed_at_frame`).
- **At a call of outside code** (`OutCall`, `Fits.outCall`,
  `ClientFrame.framed_at_call`): where the innermost frame is a frame of
  `C`'s code and its next step calls a closure of outside code, the frame
  fits at a node of its continuation and handler that may call outside
  code (`CodeFlow.out`), at a context of its code, so the check is
  required at those nodes and contexts only.
- **Live protection witnesses** (`Witness.grow`, `entryStart_witness`): a
  location an entry's argument reaches read-only at its parameter's type
  has a witness at the entry history, and at every history the entry's
  grows into inside the call; every step of an execution that keeps at
  least `d` calls active grows the history at depth `d` (`XStep.grows`,
  `Ex.grows`), so a witness stays live along it. -/
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

/-- **The class of a region's locations**: a class region's selector, every
category for any other region. -/
def regionSel : Region → Selector
  | .cls c => c
  | .inCls _ c => c
  | _ => Selector.all

/-- A location of a region is of its class (proved). -/
theorem regionSel_mem {ρ : Env} {h : Heap} {l : Nat} {v : Val} :
    ∀ {r : Region}, r.mem ρ h l = true → h[l]? = some v → (regionSel r).selects v = true
  | .cls c, hm, hv => by simpa [regionSel, Region.mem, hv] using hm
  | .inCls r c, hm, hv => by simp only [Region.mem, hv, Bool.and_eq_true] at hm; exact hm.2
  | .field _ _, _, _ | .fields _, _, _ | .cells _, _, _ | .all, _, _ | .path _ _ _, _, _
  | .pathFields _ _, _, _ | .pathCells _ _, _, _ | .spine _ _, _, _ => by
    exact Selector.has_all _

/-- **The separation of classes**: two regions of disjoint classes are
disjoint. -/
def classQuery : SepQuery := ⟨fun r s => (regionSel r).disjoint (regionSel s)⟩

/-- **The separation of classes is sound at every state** (proved): a
location holds one value, of one category. -/
theorem classQuery_sound (ρ : Env) (h : Heap) : classQuery.Sound ρ h := by
  intro r s l hl hd hr hs
  obtain ⟨v, hv⟩ : ∃ v, h[l]? = some v := ⟨h[l], List.getElem?_eq_getElem hl⟩
  have h1 := Selector.selects_disjoint hd (regionSel_mem hr hv)
  rw [regionSel_mem hs hv] at h1
  cases h1

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
theorem frame_sites {Fl : Flow P} {g : Ghost P} {n : Nat} {Γ : Nat → Option (Sites P)} {a : FrameAt P} {o : Bool}
    {S : Sites P} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {t : Tm}
    {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    (hf : Fits Fl (VJ Fl g n) Γ a o S (.frame E K t L d k x comp)) (hc : P.ofC comp = true) :
    ∃ c π l, Fl.code (E, K) c = some π ∧ NodeOf (E, K) l k x ∧ ∀ i, SitesOf g (π.env l i) (envOf L d i) := by
  cases hf with
  | val hv => simp [isVal] at hv
  | frameC c π l _ hcode hn henv => exact ⟨c, π, l, hcode, hn, fun i => (henv i).sites⟩
  | frameOut hc' => rw [hc] at hc'; cases hc'

/-- **The check at a frame of `C`'s code gives the rule's premise**
(proved): a frame of `C`'s code fitting the flow, at a heap meeting it, runs
a node whose slots' sites give `Framed` at the frame's environment through
the check at a call (`framed_of_sites`). -/
theorem framed_of_frame {Fl : Flow P} {Γ : Nat → Option (Sites P)} {a : FrameAt P} {o : Bool}
    {S₀ : Sites P} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {t : Tm}
    {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    {st : St P} (hf : Fits Fl (VJ Fl st.g st.s.h.length) Γ a o S₀ (.frame E K t L d k x comp))
    (hc : P.ofC comp = true) (hH : HeapInv Fl st.g st.s.h) :
    ∃ c π l, Fl.code (E, K) c = some π ∧ NodeOf (E, K) l k x ∧
      ∀ {q : SepQuery} {Ψ : Protocol P} {Φ S : Footprint} {keys : Region → List (Option PropKey)}
        {prot : Region → Bool} {tv : TypeView} {dp : Nat},
        frameCheckAt q Ψ Φ S Fl.H (π.env l) keys prot = true → q.Sound (envOf L d) st.s.h →
        RootsOk st.s.W (envOf L d) →
        (∀ e ∈ S, ∀ w, w < st.s.h.length → e.1.mem (envOf L d) st.s.h w = true → st.g.key w ∈ keys e.1) →
        (∀ e ∈ S, prot e.1 = true → ∀ w, w < st.s.h.length → e.1.mem (envOf L d) st.s.h w = true →
          st.g.Lent w → Witness tv dp st w) →
        Framed Φ Ψ S (envOf L d) st := by
  obtain ⟨c, π, l, hcode, hn, henv⟩ := frame_sites hf hc
  exact ⟨c, π, l, hcode, hn, fun hck hq hρ hkey hw => framed_of_sites hck hq hρ henv hH.sites hkey hw⟩

/-- **The check at the unit's frame of a reached state** (proved): where
the flow's facts hold, the checks give fresh locations the flow's sites and
every entry fits, a reached state whose term is a frame of `C`'s code (the
unit's own frame, outside every other call) fits the flow
(`ClientFrame.fitsAt_reached`), so the check at its node gives `Framed` at
its environment (`framed_of_frame`). -/
theorem ClientFrame.framed_at_frame {τ : Type} {fr : ClientFrame τ} {Fl : Flow (fr.F.at fr.C)} (hF : Fl.Facts)
    (hS : fr.FlowSites Fl) (hE : fr.EntryFits Fl) {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b)
    {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {t : Tm} {L : List Tm} {d : Tm}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    (ht : b.1.t = .frame E K t L d k x comp) (hc : (fr.F.at fr.C).ofC comp = true) :
    ∃ c π l, Fl.code (E, K) c = some π ∧ NodeOf (E, K) l k x ∧
      ∀ {q : SepQuery} {Ψ : Protocol (fr.F.at fr.C)} {Φ S : Footprint} {keys : Region → List (Option PropKey)}
        {prot : Region → Bool} {tv : TypeView} {dp : Nat},
        frameCheckAt q Ψ Φ S Fl.H (π.env l) keys prot = true → q.Sound (envOf L d) b.1.s.h →
        RootsOk b.1.s.W (envOf L d) →
        (∀ e ∈ S, ∀ w, w < b.1.s.h.length → e.1.mem (envOf L d) b.1.s.h w = true → b.2.key w ∈ keys e.1) →
        (∀ e ∈ S, prot e.1 = true → ∀ w, w < b.1.s.h.length → e.1.mem (envOf L d) b.1.s.h w = true →
          b.2.Lent w → Witness tv dp (lift fr.F fr.C none b.1 b.2) w) →
        Framed Φ Ψ S (envOf L d) (lift fr.F fr.C none b.1 b.2) := by
  obtain ⟨hfit, hH⟩ := ClientFrame.fitsAt_reached hF hS hE hb
  rw [ht] at hfit
  exact framed_of_frame (st := lift fr.F fr.C none b.1 b.2) hfit hc hH

/-! ## The innermost frame under an evaluation context -/

mutual
/-- **The innermost frame around the next step's redex**: the last frame
`activeFrame` descends through, following `Step`'s congruence rules, or
none where no frame is on the path. -/
def innermost : Tm → Option Tm
  | .invoke f r args =>
    if isVal f = false then innermost f
    else if isVal r = false then innermost r
    else innermostArgs args
  | .construct f args => if isVal f = false then innermost f else innermostArgs args
  | .letE a _ => if isVal a = false then innermost a else none
  | .makeAt _ _ xs => innermostArgs xs
  | .readAt _ a => if isVal a = false then innermost a else none
  | .indexAt a key =>
    if isVal a = false then innermost a else if isVal key = false then innermost key else none
  | .writeAt _ a b =>
    if isVal a = false then innermost a else if isVal b = false then innermost b else none
  | .test _ a => if isVal a = false then innermost a else none
  | .ite x _ _ => if isVal x = false then innermost x else none
  | .arith _ a b =>
    if isVal a = false then innermost a else if isVal b = false then innermost b else none
  | .arrLit xs => innermostArgs xs
  | .elemAt a i =>
    if isVal a = false then innermost a else if isVal i = false then innermost i else none
  | .setElem a i v =>
    if isVal a = false then innermost a else if isVal i = false then innermost i
    else if isVal v = false then innermost v else none
  | .lenOf a => if isVal a = false then innermost a else none
  | .spread a => if isVal a = false then innermost a else none
  | .throw a => if isVal a = false then innermost a else none
  | .merge _ a b =>
    if isVal a = false then innermost a else if isVal b = false then innermost b else none
  | .makeKey k a =>
    if isVal k = false then innermost k else if isVal a = false then innermost a else none
  | .frame E K t L d k x comp => (innermost t).or (some (.frame E K t L d k x comp))
  | _ => none
termination_by structural t => t

/-- The innermost frame through a list evaluated left to right. -/
def innermostArgs : List Tm → Option Tm
  | [] => none
  | a :: as => if isVal a = false then innermost a else innermostArgs as
termination_by structural xs => xs
end

/-- The code and tag of a frame. -/
def frameOf : Tm → Option (Code × ComponentTag)
  | .frame E K _ _ _ _ _ comp => some ((E, K), comp)
  | _ => none

theorem innermostArgs_mem : ∀ {xs : List Tm} {f : Tm}, innermostArgs xs = some f → ∃ x ∈ xs, innermost x = some f
  | [], _, h => by simp [innermostArgs] at h
  | a :: as, f, h => by
    simp only [innermostArgs] at h
    split at h
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨x, hx, hf⟩ := innermostArgs_mem h
      exact ⟨x, List.mem_cons_of_mem _ hx, hf⟩

/-- A value has no frame on its path. -/
theorem innermost_val {v : Tm} (hv : isVal v = true) : innermost v = none := by
  cases v <;> simp_all [isVal, innermost]

/-- What `activeFrame` reads of the innermost frame. -/
def InnSpec (cur : Option (Code × ComponentTag)) (o : Option Tm) (a : Option (Code × ComponentTag)) : Prop :=
  a = (o.bind frameOf).or cur ∧ ∀ f, o = some f → (frameOf f).isSome

mutual
/-- **The active frame is the innermost frame's** (proved, by structural
induction, the two definitions following the same congruences): the code
and tag `activeFrame` gives are the innermost frame's, `cur` where no frame
is on the path, and the innermost frame is a frame. -/
theorem activeFrame_innermost : ∀ (t : Tm) (cur : Option (Code × ComponentTag)),
    InnSpec cur (innermost t) (activeFrame cur t).1
  | .invoke f r args, cur => by
    have h₁ := activeFrame_innermost f cur
    have h₂ := activeFrame_innermost r cur
    have h₃ := activeArgs_innermost args cur (.invoke f r args)
    simp only [activeFrame, innermost]; split <;> (try split) <;> assumption
  | .construct f args, cur => by
    have h₁ := activeFrame_innermost f cur
    have h₃ := activeArgs_innermost args cur (.construct f args)
    simp only [activeFrame, innermost]; split <;> assumption
  | .letE a b, cur => by
    have h₁ := activeFrame_innermost a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact ⟨by simp, by simp⟩
  | .makeAt cc ns xs, cur => by
    simpa only [activeFrame, innermost] using activeArgs_innermost xs cur (.makeAt cc ns xs)
  | .readAt fd a, cur => by
    have h₁ := activeFrame_innermost a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact ⟨by simp, by simp⟩
  | .indexAt a key, cur => by
    have h₁ := activeFrame_innermost a cur
    have h₂ := activeFrame_innermost key cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact ⟨by simp, by simp⟩
  | .writeAt fd a b, cur => by
    have h₁ := activeFrame_innermost a cur
    have h₂ := activeFrame_innermost b cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact ⟨by simp, by simp⟩
  | .test k a, cur => by
    have h₁ := activeFrame_innermost a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact ⟨by simp, by simp⟩
  | .ite x a b, cur => by
    have h₁ := activeFrame_innermost x cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact ⟨by simp, by simp⟩
  | .arith op a b, cur => by
    have h₁ := activeFrame_innermost a cur
    have h₂ := activeFrame_innermost b cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact ⟨by simp, by simp⟩
  | .arrLit xs, cur => by
    simpa only [activeFrame, innermost] using activeArgs_innermost xs cur (.arrLit xs)
  | .elemAt a i, cur => by
    have h₁ := activeFrame_innermost a cur
    have h₂ := activeFrame_innermost i cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact ⟨by simp, by simp⟩
  | .setElem a i v, cur => by
    have h₁ := activeFrame_innermost a cur
    have h₂ := activeFrame_innermost i cur
    have h₃ := activeFrame_innermost v cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · split
        · exact h₃
        · exact ⟨by simp, by simp⟩
  | .lenOf a, cur => by
    have h₁ := activeFrame_innermost a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact ⟨by simp, by simp⟩
  | .spread a, cur => by
    have h₁ := activeFrame_innermost a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact ⟨by simp, by simp⟩
  | .throw a, cur => by
    have h₁ := activeFrame_innermost a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact ⟨by simp, by simp⟩
  | .merge dd a b, cur => by
    have h₁ := activeFrame_innermost a cur
    have h₂ := activeFrame_innermost b cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact ⟨by simp, by simp⟩
  | .makeKey k a, cur => by
    have h₁ := activeFrame_innermost k cur
    have h₂ := activeFrame_innermost a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact ⟨by simp, by simp⟩
  | .frame E K t L d k x comp, cur => by
    obtain ⟨h₁, h₂⟩ := activeFrame_innermost t (some ((E, K), comp))
    simp only [activeFrame, innermost]
    refine ⟨?_, ?_⟩
    · rw [h₁]
      cases hi : innermost t with
      | none => simp [frameOf]
      | some f =>
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h₂ f hi)
        simp [hy]
    · intro f hf
      cases hi : innermost t with
      | none => rw [hi] at hf; simp at hf; subst hf; simp [frameOf]
      | some f' => rw [hi] at hf; simp at hf; subst hf; exact h₂ _ hi
  | .var _, _ | .nul, _ | .undef, _ | .tru, _ | .fls, _ | .num _, _ | .str _, _ | .bigint _, _ | .sym _, _
  | .objAt .., _ | .arr _, _ | .viewSpine .., _ | .goto .., _ => by
    simp only [activeFrame, innermost]; exact ⟨by simp, by simp⟩
termination_by structural t => t

/-- The active frame through a list is the innermost frame's (proved). -/
theorem activeArgs_innermost : ∀ (xs : List Tm) (cur : Option (Code × ComponentTag)) (t : Tm),
    InnSpec cur (innermostArgs xs) (activeArgs cur t xs).1
  | [], cur, t => by simp only [activeArgs, innermostArgs]; exact ⟨by simp, by simp⟩
  | a :: as, cur, t => by
    have h₁ := activeFrame_innermost a cur
    have h₂ := activeArgs_innermost as cur t
    simp only [activeArgs, innermostArgs]; split <;> assumption
termination_by structural xs => xs
end

/-- What `activeFrame` gives of the innermost frame's term: the innermost
frame is a frame whose running term has no frame on its path, and the term
the next step reduces is the one `activeFrame` gives in that frame. -/
def RedexSpec (o : Option Tm) (p : Option (Code × ComponentTag) × Tm) : Prop :=
  ∀ f, o = some f → ∃ E K t L d k x comp, f = .frame E K t L d k x comp ∧ innermost t = none ∧
    p.2 = (activeFrame (some ((E, K), comp)) t).2

theorem RedexSpec.none {p : Option (Code × ComponentTag) × Tm} :
    RedexSpec none p := fun _ h => nomatch h

mutual
/-- **The active term is the innermost frame's** (proved, by structural
induction, the two definitions following the same congruences): the
innermost frame is a frame with no frame on its running term's path, and
the term `activeFrame` gives is the one it gives in that frame. -/
theorem activeFrame_redex : ∀ (t : Tm) (cur : Option (Code × ComponentTag)),
    RedexSpec (innermost t) (activeFrame cur t)
  | .invoke f r args, cur => by
    have h₁ := activeFrame_redex f cur
    have h₂ := activeFrame_redex r cur
    have h₃ := activeArgs_redex args cur (.invoke f r args)
    simp only [activeFrame, innermost]; split <;> (try split) <;> assumption
  | .construct f args, cur => by
    have h₁ := activeFrame_redex f cur
    have h₃ := activeArgs_redex args cur (.construct f args)
    simp only [activeFrame, innermost]; split <;> assumption
  | .letE a b, cur => by
    have h₁ := activeFrame_redex a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact RedexSpec.none
  | .makeAt cc ns xs, cur => by
    simpa only [activeFrame, innermost] using activeArgs_redex xs cur (.makeAt cc ns xs)
  | .readAt fd a, cur => by
    have h₁ := activeFrame_redex a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact RedexSpec.none
  | .indexAt a key, cur => by
    have h₁ := activeFrame_redex a cur
    have h₂ := activeFrame_redex key cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact RedexSpec.none
  | .writeAt fd a b, cur => by
    have h₁ := activeFrame_redex a cur
    have h₂ := activeFrame_redex b cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact RedexSpec.none
  | .test k a, cur => by
    have h₁ := activeFrame_redex a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact RedexSpec.none
  | .ite x a b, cur => by
    have h₁ := activeFrame_redex x cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact RedexSpec.none
  | .arith op a b, cur => by
    have h₁ := activeFrame_redex a cur
    have h₂ := activeFrame_redex b cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact RedexSpec.none
  | .arrLit xs, cur => by
    simpa only [activeFrame, innermost] using activeArgs_redex xs cur (.arrLit xs)
  | .elemAt a i, cur => by
    have h₁ := activeFrame_redex a cur
    have h₂ := activeFrame_redex i cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact RedexSpec.none
  | .setElem a i v, cur => by
    have h₁ := activeFrame_redex a cur
    have h₂ := activeFrame_redex i cur
    have h₃ := activeFrame_redex v cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · split
        · exact h₃
        · exact RedexSpec.none
  | .lenOf a, cur => by
    have h₁ := activeFrame_redex a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact RedexSpec.none
  | .spread a, cur => by
    have h₁ := activeFrame_redex a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact RedexSpec.none
  | .throw a, cur => by
    have h₁ := activeFrame_redex a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · exact RedexSpec.none
  | .merge dd a b, cur => by
    have h₁ := activeFrame_redex a cur
    have h₂ := activeFrame_redex b cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact RedexSpec.none
  | .makeKey k a, cur => by
    have h₁ := activeFrame_redex k cur
    have h₂ := activeFrame_redex a cur
    simp only [activeFrame, innermost]; split
    · exact h₁
    · split
      · exact h₂
      · exact RedexSpec.none
  | .frame E K t L d k x comp, cur => by
    have h₁ := activeFrame_redex t (some ((E, K), comp))
    simp only [activeFrame, innermost]
    intro f hf
    cases hi : innermost t with
    | none =>
      rw [hi] at hf; simp only [Option.none_or, Option.some.injEq] at hf; subst hf
      exact ⟨E, K, t, L, d, k, x, comp, rfl, hi, rfl⟩
    | some f' => rw [hi] at hf; simp only [Option.some_or, Option.some.injEq] at hf; subst hf; exact h₁ _ hi
  | .var _, _ | .nul, _ | .undef, _ | .tru, _ | .fls, _ | .num _, _ | .str _, _ | .bigint _, _ | .sym _, _
  | .objAt .., _ | .arr _, _ | .viewSpine .., _ | .goto .., _ => by
    simp only [activeFrame, innermost]; exact RedexSpec.none
termination_by structural t => t

/-- The active term through a list is the innermost frame's (proved). -/
theorem activeArgs_redex : ∀ (xs : List Tm) (cur : Option (Code × ComponentTag)) (t : Tm),
    RedexSpec (innermostArgs xs) (activeArgs cur t xs)
  | [], cur, t => by simp only [activeArgs, innermostArgs]; exact RedexSpec.none
  | a :: as, cur, t => by
    have h₁ := activeFrame_redex a cur
    have h₂ := activeArgs_redex as cur t
    simp only [activeArgs, innermostArgs]; split <;> assumption
termination_by structural xs => xs
end

/-- **Every frame on the path fits** (proved, by induction on `Fits`): the
innermost frame of a fitting term fits, at the sites of its position. -/
theorem Fits.innermost {Fl : Flow P} {V : Sites P → Val → Prop} :
    ∀ {Γ a o S t}, Fits Fl V Γ a o S t → ∀ {f : Tm}, innermost t = some f →
      ∃ Γ' a' o' S', Fits Fl V Γ' a' o' S' f := by
  intro Γ a o S t h
  induction h with
  | val hv _ _ => intro f hf; rw [innermost_val hv] at hf; cases hf
  | var _ _ _ => intro f hf; simp [ReadOnly.innermost] at hf
  | invoke _ _ _ _ _ _ _ _ ihf ihr iha =>
    intro f hf
    simp only [ReadOnly.innermost] at hf
    split at hf
    · exact ihf hf
    · split at hf
      · exact ihr hf
      · obtain ⟨x, hx, hf⟩ := innermostArgs_mem hf
        exact iha x hx hf
  | invokeC σ c π Sa Sr _ hfn _ _ _ _ _ _ _ _ _ ihr iha =>
    intro f hf
    simp only [ReadOnly.innermost, hfn.val, Bool.true_eq_false, if_false] at hf
    split at hf
    · exact ihr hf
    · obtain ⟨x, hx, hf⟩ := innermostArgs_mem hf
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      exact iha i x hi hf
  | construct _ _ _ _ _ _ _ ihf iha =>
    intro f hf
    simp only [ReadOnly.innermost] at hf
    split at hf
    · exact ihf hf
    · obtain ⟨x, hx, hf⟩ := innermostArgs_mem hf
      exact iha x hx hf
  | letE _ _ _ ihx _ =>
    intro f hf; simp only [ReadOnly.innermost] at hf; split at hf
    · exact ihx hf
    · cases hf
  | spread _ _ _ ih =>
    intro f hf; simp only [ReadOnly.innermost] at hf; split at hf
    · exact ih hf
    · cases hf
  | makeAbsent _ _ _ _ _ ih | makeView _ _ _ _ _ _ ih | makeBound _ _ _ _ _ _ ih
  | makeGraphC _ _ _ _ _ _ _ _ _ _ _ _ ih | makeGraphOut _ _ _ _ _ _ _ _ _ ih | arrLit _ _ _ _ _ ih =>
    intro f hf
    simp only [ReadOnly.innermost] at hf
    obtain ⟨x, hx, hf⟩ := innermostArgs_mem hf
    exact ih x hx hf
  | readAt _ _ _ _ _ ih | test _ _ ih | lenOf _ _ ih | throw _ _ ih =>
    intro f hf; simp only [ReadOnly.innermost] at hf; split at hf
    · exact ih hf
    · cases hf
  | ite _ _ _ _ ihc _ _ =>
    intro f hf; simp only [ReadOnly.innermost] at hf; split at hf
    · exact ihc hf
    · cases hf
  | indexAt _ _ _ _ _ _ ihx ihk | writeAt _ _ _ _ ihx ihk | arith _ _ _ ihx ihk | elemAt _ _ _ _ ihx ihk
  | merge _ _ _ _ _ _ _ _ ihx ihk | makeKey _ _ _ _ _ ihx ihk =>
    intro f hf; simp only [ReadOnly.innermost] at hf; split at hf
    · exact ihx hf
    · split at hf
      · exact ihk hf
      · cases hf
  | setElem _ _ _ _ _ _ _ ihx ihi ihv =>
    intro f hf; simp only [ReadOnly.innermost] at hf; split at hf
    · exact ihx hf
    · split at hf
      · exact ihi hf
      · split at hf
        · exact ihv hf
        · cases hf
  | gotoC _ _ _ _ _ _ _ _ | gotoOut _ _ _ _ _ => intro f hf; simp [ReadOnly.innermost] at hf
  | frameC c π l hc hcode hn henv hfn hvfn ht hS ho ih =>
    intro f hf
    simp only [ReadOnly.innermost] at hf
    cases hi : ReadOnly.innermost _ with
    | none => rw [hi] at hf; simp at hf; subst hf; exact ⟨_, FrameAt.outside, _, _, .frameC c π l hc hcode hn henv hfn hvfn ht hS ho⟩
    | some f' => rw [hi] at hf; simp at hf; subst hf; exact ih hi
  | frameOut hc hE henv ht hS ho ih =>
    intro f hf
    simp only [ReadOnly.innermost] at hf
    cases hi : ReadOnly.innermost _ with
    | none => rw [hi] at hf; simp at hf; subst hf; exact ⟨_, FrameAt.outside, _, _, .frameOut hc hE henv ht hS ho⟩
    | some f' => rw [hi] at hf; simp at hf; subst hf; exact ih hi

/-- **The check at the innermost frame of a reached state** (proved): at a
reached state, the innermost frame on its term's path, where it is a frame
of `C`'s code (a call of `C` nested in a call of outside code, a callback
that re-entered `C`, or the unit's own frame), fits the flow
(`fitsAt_reached`, `Fits.innermost`), so the check at its node gives
`Framed` at its environment (`framed_of_frame`). Its code and tag are the
active frame's (`activeFrame_innermost`). -/
theorem ClientFrame.framed_at_innermost {τ : Type} {fr : ClientFrame τ} {Fl : Flow (fr.F.at fr.C)} (hF : Fl.Facts)
    (hS : fr.FlowSites Fl) (hE : fr.EntryFits Fl) {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b)
    {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {t : Tm} {L : List Tm} {d : Tm}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    (ht : innermost b.1.t = some (.frame E K t L d k x comp)) (hc : (fr.F.at fr.C).ofC comp = true) :
    (activeFrame none b.1.t).1 = some ((E, K), comp) ∧
    ∃ c π l, Fl.code (E, K) c = some π ∧ NodeOf (E, K) l k x ∧
      ∀ {q : SepQuery} {Ψ : Protocol (fr.F.at fr.C)} {Φ S : Footprint} {keys : Region → List (Option PropKey)}
        {prot : Region → Bool} {tv : TypeView} {dp : Nat},
        frameCheckAt q Ψ Φ S Fl.H (π.env l) keys prot = true → q.Sound (envOf L d) b.1.s.h →
        RootsOk b.1.s.W (envOf L d) →
        (∀ e ∈ S, ∀ w, w < b.1.s.h.length → e.1.mem (envOf L d) b.1.s.h w = true → b.2.key w ∈ keys e.1) →
        (∀ e ∈ S, prot e.1 = true → ∀ w, w < b.1.s.h.length → e.1.mem (envOf L d) b.1.s.h w = true →
          b.2.Lent w → Witness tv dp (lift fr.F fr.C none b.1 b.2) w) →
        Framed Φ Ψ S (envOf L d) (lift fr.F fr.C none b.1 b.2) := by
  obtain ⟨hfit, hH⟩ := ClientFrame.fitsAt_reached hF hS hE hb
  refine ⟨by rw [(activeFrame_innermost b.1.t none).1, ht]; simp [frameOf], ?_⟩
  obtain ⟨Γ', a', o', S', hf'⟩ := hfit.innermost ht
  exact framed_of_frame (st := lift fr.F fr.C none b.1 b.2) hf' hc hH

/-! ## The frame at a call of outside code -/

/-- **A call of outside code**: a call or a `new` of a closure of outside
code. -/
def OutCall (P : Package) : Tm → Prop
  | .invoke f _ _ => OutClosure P f
  | .construct f _ => OutClosure P f
  | _ => False

/-- A value is no call (proved). -/
theorem outCall_val {cur : Option (Code × ComponentTag)} {v : Tm} (hv : isVal v = true) :
    ¬ OutCall P (activeFrame cur v).2 := by
  cases v <;> simp_all [isVal, activeFrame, OutCall]

/-- **A list's active term**: every element a value, or the active term of
its first element that is not one (proved). -/
theorem activeArgs_split {cur : Option (Code × ComponentTag)} {t : Tm} : ∀ (xs : List Tm),
    (activeArgs cur t xs = (cur, t) ∧ innermostArgs xs = none) ∨
      ∃ x ∈ xs, activeArgs cur t xs = activeFrame cur x ∧ innermostArgs xs = innermost x
  | [] => .inl ⟨by simp [activeArgs], by simp [innermostArgs]⟩
  | a :: as => by
    cases ha : isVal a with
    | false => exact .inr ⟨a, List.mem_cons_self .., by simp [activeArgs, ha], by simp [innermostArgs, ha]⟩
    | true =>
      rcases activeArgs_split (cur := cur) (t := t) as with ⟨h₁, h₂⟩ | ⟨x, hx, h₁, h₂⟩
      · exact .inl ⟨by simp [activeArgs, ha, h₁], by simp [innermostArgs, ha, h₂]⟩
      · exact .inr ⟨x, List.mem_cons_of_mem _ hx, by simp [activeArgs, ha, h₁], by simp [innermostArgs, ha, h₂]⟩

/-- The active term of a list of fitting terms calls outside code only
where one of them does, or where every one is a value and the term `t`
does (proved). -/
theorem activeArgs_out {cur : Option (Code × ComponentTag)} {t : Tm} {xs : List Tm} {q : Prop}
    (ih : ∀ x ∈ xs, innermost x = none → ∀ cur, OutCall P (activeFrame cur x).2 → q)
    (htop : OutCall P t → q) (hi : innermostArgs xs = none) (hc : OutCall P (activeArgs cur t xs).2) : q := by
  rcases activeArgs_split (cur := cur) (t := t) xs with ⟨h₁, _⟩ | ⟨x, hx, h₁, h₂⟩
  · rw [h₁] at hc; exact htop hc
  · rw [h₁] at hc; rw [h₂] at hi; exact ih x hx hi cur hc

/-- **A frame calls outside code only where its node may** (proved, by
induction on `Fits`): where no frame is on a fitting term's path and the
term its next step reduces is a call of outside code, the frame may call
outside code: that call's callee meets a set holding outside storage, the
token of the closures of outside code (`FnsIn.notOut`), which a frame's
call holds only where the frame may call outside code (`Fits.invoke`,
`Fits.construct`); a call of a closure of a known signature calls `C`'s
code (`Fits.invokeC`). -/
theorem Fits.outCall {Fl : Flow P} {V : Sites P → Val → Prop} (hV : ∀ S v, V S v → FnsIn Fl S v) :
    ∀ {Γ a o S t}, Fits Fl V Γ a o S t → ReadOnly.innermost t = none → ∀ cur, OutCall P (activeFrame cur t).2 →
      a.out = true := by
  intro Γ a o S t h
  induction h with
  | val hv _ _ => intro _ cur hc; exact absurd hc (outCall_val hv)
  | var _ _ _ => intro _ cur hc; simp [activeFrame, OutCall] at hc
  | @invoke _ a _ _ _ f r args hf _ _ _ _ _ _ hout ihf ihr iha =>
    intro hi cur hc
    simp only [ReadOnly.innermost] at hi
    simp only [activeFrame] at hc
    split at hc
    · rename_i hv; rw [if_pos hv] at hi; exact ihf hi cur hc
    · rename_i hfv
      rw [if_neg hfv] at hi
      split at hc
      · rename_i hv; rw [if_pos hv] at hi; exact ihr hi cur hc
      · rename_i hrv
        rw [if_neg hrv] at hi
        refine activeArgs_out iha (fun htop => hout ?_) hi hc
        have hfv' : isVal f = true := by simpa using hfv
        exact (hV _ _ (hf.value hfv')).notOut htop
  | @invokeC _ _ _ _ f r args σ c π Sa Sr _ hfn _ _ _ _ _ _ _ _ _ ihr iha =>
    intro hi cur hc
    have hfv : isVal f = true := hfn.val
    simp only [ReadOnly.innermost, hfv, Bool.true_eq_false, if_false] at hi
    simp only [activeFrame, hfv, Bool.true_eq_false, if_false] at hc
    by_cases hrv : isVal r = false
    · rw [if_pos hrv] at hi hc; exact ihr hi cur hc
    · rw [if_neg hrv] at hi hc
      refine activeArgs_out (fun x hx => iha (List.getElem?_of_mem hx).choose x
        (List.getElem?_of_mem hx).choose_spec) (fun htop => ?_) hi hc
      obtain ⟨fs, caps, k, comp, oid, rfl, -, hcomp⟩ := hfn
      obtain ⟨_, _, _, _, _, _, _, _, _, _, he, hc'⟩ := htop
      cases he; rw [hcomp] at hc'; cases hc'
  | @construct _ a _ _ _ f args hf _ _ _ _ _ hout ihf iha =>
    intro hi cur hc
    simp only [ReadOnly.innermost] at hi
    simp only [activeFrame] at hc
    split at hc
    · rename_i hv; rw [if_pos hv] at hi; exact ihf hi cur hc
    · rename_i hfv
      rw [if_neg hfv] at hi
      refine activeArgs_out iha (fun htop => hout ?_) hi hc
      have hfv' : isVal f = true := by simpa using hfv
      exact (hV _ _ (hf.value hfv')).notOut htop
  | letE _ _ _ ihx _ | spread _ _ _ ihx | readAt _ _ _ _ _ ihx | test _ _ ihx | ite _ _ _ _ ihx _ _
  | lenOf _ _ ihx | throw _ _ ihx =>
    intro hi cur hc
    simp only [ReadOnly.innermost] at hi
    simp only [activeFrame] at hc
    split at hc
    · rename_i hv; rw [if_pos hv] at hi; exact ihx hi cur hc
    · simp [OutCall] at hc
  | indexAt _ _ _ _ _ _ ihx ihk | writeAt _ _ _ _ ihx ihk | arith _ _ _ ihx ihk | elemAt _ _ _ _ ihx ihk
  | merge _ _ _ _ _ _ _ _ ihx ihk | makeKey _ _ _ _ _ ihx ihk =>
    intro hi cur hc
    simp only [ReadOnly.innermost] at hi
    simp only [activeFrame] at hc
    split at hc
    · rename_i hv; rw [if_pos hv] at hi; exact ihx hi cur hc
    · rename_i hxv
      rw [if_neg hxv] at hi
      split at hc
      · rename_i hv; rw [if_pos hv] at hi; exact ihk hi cur hc
      · simp [OutCall] at hc
  | setElem _ _ _ _ _ _ _ ihx ihi ihv =>
    intro hi cur hc
    simp only [ReadOnly.innermost] at hi
    simp only [activeFrame] at hc
    split at hc
    · rename_i hv; rw [if_pos hv] at hi; exact ihx hi cur hc
    · rename_i hxv
      rw [if_neg hxv] at hi
      split at hc
      · rename_i hv; rw [if_pos hv] at hi; exact ihi hi cur hc
      · rename_i hiv
        rw [if_neg hiv] at hi
        split at hc
        · rename_i hv; rw [if_pos hv] at hi; exact ihv hi cur hc
        · simp [OutCall] at hc
  | makeAbsent _ _ _ _ _ ih | makeView _ _ _ _ _ _ ih | makeBound _ _ _ _ _ _ ih
  | makeGraphC _ _ _ _ _ _ _ _ _ _ _ _ ih | makeGraphOut _ _ _ _ _ _ _ _ _ ih | arrLit _ _ _ _ _ ih =>
    intro hi cur hc
    simp only [ReadOnly.innermost] at hi
    simp only [activeFrame] at hc
    exact activeArgs_out ih (fun htop => by simp [OutCall] at htop) hi hc
  | gotoC _ _ _ _ _ _ _ _ | gotoOut _ _ _ _ _ => intro _ cur hc; simp [activeFrame, OutCall] at hc
  | frameC _ _ _ _ _ _ _ _ _ _ _ _ _ | frameOut _ _ _ _ _ _ _ =>
    intro hi; simp [ReadOnly.innermost] at hi

/-- **The check at a call of outside code** (proved): at a reached state
whose innermost frame on its term's path is a frame of `C`'s code and
whose next step calls outside code, the frame fits the flow at a context
of its code and a node of its continuation and handler that may call
outside code (`Fits.outCall`, `activeFrame_redex`), its environment
meeting the node's slots; so the check at that node's slots gives
`Framed` at its environment (`framed_of_sites`). The check is therefore
required at each such node and context, and at no other. -/
theorem ClientFrame.framed_at_call {τ : Type} {fr : ClientFrame τ} {Fl : Flow (fr.F.at fr.C)} (hF : Fl.Facts)
    (hS : fr.FlowSites Fl) (hE : fr.EntryFits Fl) {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b)
    {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {t : Tm} {L : List Tm} {d : Tm}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    (ht : innermost b.1.t = some (.frame E K t L d k x comp)) (hc : (fr.F.at fr.C).ofC comp = true)
    (hcall : OutCall (fr.F.at fr.C) (activeFrame none b.1.t).2) :
    ∃ c π l, Fl.code (E, K) c = some π ∧ NodeOf (E, K) l k x ∧ π.out l = true ∧
      ∀ {q : SepQuery} {Ψ : Protocol (fr.F.at fr.C)} {Φ S : Footprint} {keys : Region → List (Option PropKey)}
        {prot : Region → Bool} {tv : TypeView} {dp : Nat},
        frameCheckAt q Ψ Φ S Fl.H (π.env l) keys prot = true → q.Sound (envOf L d) b.1.s.h →
        RootsOk b.1.s.W (envOf L d) →
        (∀ e ∈ S, ∀ w, w < b.1.s.h.length → e.1.mem (envOf L d) b.1.s.h w = true → b.2.key w ∈ keys e.1) →
        (∀ e ∈ S, prot e.1 = true → ∀ w, w < b.1.s.h.length → e.1.mem (envOf L d) b.1.s.h w = true →
          b.2.Lent w → Witness tv dp (lift fr.F fr.C none b.1 b.2) w) →
        Framed Φ Ψ S (envOf L d) (lift fr.F fr.C none b.1 b.2) := by
  obtain ⟨hfit, hH⟩ := ClientFrame.fitsAt_reached hF hS hE hb
  obtain ⟨Γ', a', o', S', hf'⟩ := hfit.innermost ht
  obtain ⟨E', K', t', L', d', k', x', comp', he, hi, hred⟩ := activeFrame_redex b.1.t none _ ht
  cases he
  cases hf' with
  | val hv => simp [isVal] at hv
  | frameC c π l _ hcode hn henv _ _ hrun =>
    have hout : (π.at l).out = true := hrun.outCall (fun _ _ hv => hv.fns) hi _ (by rw [← hred]; exact hcall)
    exact ⟨c, π, l, hcode, hn, hout, fun hck hq hρ hkey hw =>
      framed_of_sites hck hq hρ (fun i => (henv i).sites) hH.sites hkey hw⟩
  | frameOut hc' => rw [hc] at hc'; cases hc'

/-! ## The keys of a region's locations

The checks read the protocol per site and kind: they give every location
the key `none` (`ClientFrame.NoKeys`), so a part's key is `none` at every
reached state and a region's keys are `[none]` (`noKeys`). A protocol is
then read at `(σ, κ, none)` for every key of a site, a change bounding
every field of the site's records. -/

/-- **The keys after a step** (proved): the step's allocation's; entries,
crossings and exits change no key. -/
theorem stepAt_key {F : Family} {C : Nat} {c : ComponentTag} {tv : TypeView} {d : CheckData (F.at C) tv}
    {h : Heap} {t : Tm} {h' : Heap} {t' : Tm} {g : Ghost (F.at C)} :
    (Ghost.stepAt F C c d h t h' t' g).key = (g.alloc h.length (fun _ => none) d.key).key := by
  unfold Ghost.stepAt
  split <;> rename_i hk
  · unfold outsideNextAt; split <;> rfl
  · exact (Ghost.crosses_site _ _).2
  · exact (Ghost.crosses_site _ _).2
  · exact (Ghost.crosses_site _ _).2

/-- The keys of every region: `none`. -/
def noKeys : Region → List (Option PropKey) := fun _ => [none]

namespace ClientFrame
variable {τ : Type} (fr : ClientFrame τ)

/-- **The checks give no key**: every location a step allocates has the key
`none`, and so does every location of a history an entry starts from. -/
def NoKeys : Prop :=
  (∀ h t h' t', (fr.chk h t h' t').key = fun _ => none) ∧
    ∀ k W h t g, fr.start k W h t g → g.key = fun _ => none

variable {fr}

/-- **Every reached state's keys are `none`** (proved, `stepAt_key`). -/
theorem reached_key (hk : fr.NoKeys) {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b) :
    b.2.key = fun _ => none := by
  obtain ⟨a, n, _, hst, hex⟩ := hb
  refine hex.carry (r := fun x : Conf × Ghost (fr.F.at fr.C) => x.2.key = fun _ => none) ?_ (hk.2 _ _ _ _ _ hst)
  intro x y _ hxy hx
  obtain ⟨-, hg, -⟩ := hxy
  rw [hg]
  simp only [next, stepAt_key, Ghost.alloc, hk.1, hx]
  funext l; split <;> rfl

/-- **A region's locations have the region's keys** (proved): at a reached
state, every location's key is `none`, the one key `noKeys` gives. -/
theorem reached_hkey (hk : fr.NoKeys) {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b) (S : Footprint)
    (ρ : Env) : ∀ e ∈ S, ∀ w, w < b.1.s.h.length → e.1.mem ρ b.1.s.h w = true → b.2.key w ∈ noKeys e.1 := by
  intro _ _ w _ _
  rw [reached_key hk hb]; simp [noKeys]

/-- **Entries start with no key** (proved): the entry history keeps the
keys of `bareStart`, which are `none`. -/
theorem entryStart_key (F : Family) (C : Nat) (tv : TypeView) (h : Heap) (t : Tm) (args : List (tv.Ty × Val)) :
    (entryStart F C tv h t args).key = fun _ => none :=
  (Ghost.crosses_site _ _).2

end ClientFrame

/-- **The check at the innermost frame, keys read** (proved): at a reached
state of a frame whose checks give no key, `framed_at_innermost` with the
keys `noKeys`. -/
theorem ClientFrame.framed_at_innermost_keys {τ : Type} {fr : ClientFrame τ} {Fl : Flow (fr.F.at fr.C)}
    (hF : Fl.Facts) (hS : fr.FlowSites Fl) (hE : fr.EntryFits Fl) (hK : fr.NoKeys)
    {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b)
    {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {t : Tm} {L : List Tm} {d : Tm}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    (ht : innermost b.1.t = some (.frame E K t L d k x comp)) (hc : (fr.F.at fr.C).ofC comp = true) :
    (activeFrame none b.1.t).1 = some ((E, K), comp) ∧
    ∃ c π l, Fl.code (E, K) c = some π ∧ NodeOf (E, K) l k x ∧
      ∀ {q : SepQuery} {Ψ : Protocol (fr.F.at fr.C)} {Φ S : Footprint} {prot : Region → Bool} {tv : TypeView}
        {dp : Nat},
        frameCheckAt q Ψ Φ S Fl.H (π.env l) noKeys prot = true → q.Sound (envOf L d) b.1.s.h →
        RootsOk b.1.s.W (envOf L d) →
        (∀ e ∈ S, prot e.1 = true → ∀ w, w < b.1.s.h.length → e.1.mem (envOf L d) b.1.s.h w = true →
          b.2.Lent w → Witness tv dp (lift fr.F fr.C none b.1 b.2) w) →
        Framed Φ Ψ S (envOf L d) (lift fr.F fr.C none b.1 b.2) := by
  obtain ⟨ha, c, π, l, hcode, hn, hfr⟩ := ClientFrame.framed_at_innermost hF hS hE hb ht hc
  exact ⟨ha, c, π, l, hcode, hn, fun hck hq hρ hw => hfr hck hq hρ (ClientFrame.reached_hkey hK hb _ _) hw⟩

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

section Growth
variable {F : Family} {C : Nat} {c : ComponentTag} {tv : TypeView} {Θ : Protocol (F.at C)}
  {chk : Conf → Conf → CheckData (F.at C) tv}

/-- **A step keeping `d` calls active grows the history at depth `d`**
(proved): a step of outside code inside a call only allocates
(`outsideNext_of_ne`); a step of `C`'s code is a checked step at depth `d`
(`pkgStep_of`), which grows it (`pkg_step_ok`). -/
theorem XStep.grows {d : Nat} {a b : Conf × Ghost (F.at C)} (hx : XStep F C c Θ chk a b)
    (hl : a.2.A.length = δ F C c a) (hi : Inv (lift F C c a.1 a.2)) (hd : 0 < d) (hda : d ≤ δ F C c a)
    (hdb : d ≤ δ F C c b) : Grows d a.2 b.2 := by
  obtain ⟨hs, hdisc, hg, hh⟩ := hx
  have hlen : d ≤ a.2.A.length := by omega
  by_cases hk : kind F C c a.1 b.1 = .outside
  · have hA : a.2.A ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    have hb : b.2 = a.2.alloc a.1.s.h.length (fun _ => none) (chk a.1 b.1).key := by
      rw [hg]; simp only [Ghost.next, Ghost.stepAt, stepKind_conf, hk]; exact outsideNext_of_ne hA
    rw [hb]
    exact ⟨hd, hlen, by simpa using hlen, rfl, fun _ h => h, fun _ h => h⟩
  · have hpk := pkgStep_of (d := d) hs hk (hyp_props hk hh) hlen (fun hx => by
      have := ((kind_spec (F := F) (C := C) (c := c) a.1 b.1).2.2.1 hx)
      simp only [δ] at hl hdb; omega)
    rw [← hg] at hpk
    exact (pkg_step_ok hpk (hi.ok hd hlen)).2.2

/-- **An execution keeping `d` calls active grows the history at depth
`d`** (proved, by `XStep.grows`, `XStep.len` and `XStep.inv`). -/
theorem Ex.grows {d : Nat} {q : Conf × Ghost (F.at C) → Prop} (hd : 0 < d)
    (hq : ∀ x, q x → d ≤ δ F C c x) :
    ∀ {n : Nat} {a e : Conf × Ghost (F.at C)}, Ex (XStep F C c Θ chk) q n a e →
      a.2.A.length = δ F C c a → Inv (lift F C c a.1 a.2) → d ≤ δ F C c a → d ≤ δ F C c e →
      Grows d a.2 e.2
  | _, a, _, .refl _, hl, _, hda, _ => Grows.refl hd (by omega)
  | _, a, e, .next (b := b) _ hab he, hl, hi, hda, hde => by
    have hdb : d ≤ δ F C c b := by
      cases he with
      | refl => exact hde
      | next hb _ _ => exact hq _ hb
    have h₁ := XStep.grows hab hl hi hd hda hdb
    have hl' : b.2.A.length = δ F C c b + 0 := XStep.len (off := 0) hab (by simpa using hl)
    have h₂ := Ex.grows hd hq he (by simpa using hl') (XStep.inv (off := 0) hab (by simpa using hl) hi) hdb hde
    exact h₁.trans h₂

end Growth

/-- **An entry's argument is witnessed along the call** (proved): from an
entry whose history is the entry's (`entryStart`), along an execution
keeping the call active, every location an argument reaches read-only at
its parameter's type has a live witness at the call's depth `1`
(`entryStart_witness`, `Ex.grows`, `Witness.grow`). -/
theorem witness_along {F : Family} {C : Nat} {tv : TypeView} {Θ : Protocol (F.at C)}
    {chk : Conf → Conf → CheckData (F.at C) tv} {q : Conf × Ghost (F.at C) → Prop}
    (hq : ∀ y, q y → 1 ≤ δ F C none y) {x : Conf} {args : List (tv.Ty × Val)} {n : Nat}
    {e : Conf × Ghost (F.at C)} (hex : Ex (XStep F C none Θ chk) q n (x, entryStart F C tv x.s.h x.t args) e)
    (hdx : 1 ≤ depthC F C none x.t) (hde : 1 ≤ δ F C none e) {T : tv.Ty} {v : Val} (ha : (T, v) ∈ args)
    {l : Nat} (hr : ReachRO tv (F.at C).ofC T x.s.h v l) :
    Witness tv 1 (lift F C none e.1 e.2) l := by
  have hw := entryStart_witness (st := lift F C none x (entryStart F C tv x.s.h x.t args)) (d := 1) Nat.one_pos hdx ha hr rfl
  exact hw.grow (Ex.grows Nat.one_pos hq hex (entryStart_len _) (entryStart_inv x args) hdx hde)

/-! ## A reached state inside the unit's call

A unit's call starts at a `goto` of its code at the top of the term
(`gotoOf`, a call from outside code). Along every execution from it, the
top of the term is a `goto` or a frame of that code, then a value or a
throw of one (`TopC`), the last two taking no step. So every state but the
last of an execution from the entry has the unit's call active
(`ex_depth`), and a reached state with it active is reached by the
execution at depth `1` that `witness_along` reads (`witness_reached`). -/

/-- The blocks of a list end in those of its suffix. -/
theorem blocks_append_ge : ∀ (xs ys : List Bool), blocks ys ≤ blocks (xs ++ ys)
  | [], _ => Nat.le_refl _
  | _ :: xs, ys => by
    simp only [List.cons_append, blocks]
    exact Nat.le_trans (blocks_append_ge xs ys) (Nat.le_add_left _ _)

/-- **A frame of `C`'s code at the top holds a call of `C`** (proved). -/
theorem depthC_frame {F : Family} {C : Nat} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {t : Tm} {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target}
    {comp : ComponentTag} (hc : F.ofC C comp = true) : 1 ≤ depthC F C none (.frame E K t L d k x comp) := by
  obtain ⟨init, s, hp⟩ := path_last t comp
  have hn : F.ofC C none = false := by simp [Family.ofC, Family.Runs]
  have hm : (path none (.frame E K t L d k x comp)).map (fun p => F.ofC C p.1) =
      (init.map fun p => F.ofC C p.1) ++ [true, false] := by
    simp only [path, List.map_append, hp]
    have e : (wrap (fun s => .frame E K s L d k x comp) (init ++ [(comp, s)])).map (fun p => F.ofC C p.1) =
        ((wrap (fun s => .frame E K s L d k x comp) (init ++ [(comp, s)])).map Prod.fst).map (F.ofC C) := by
      simp [List.map_map, Function.comp_def]
    rw [e, wrap_fst]
    simp [hc, hn, Function.comp_def]
  unfold depthC
  rw [hm]
  exact Nat.le_trans (by simp [blocks]) (blocks_append_ge _ [true, false])

/-- **A `goto` of `C`'s code at the top holds a call of `C`** (proved). -/
theorem depthC_goto {F : Family} {C : Nat} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {l : Nat} {L : List Tm} {d : Tm} {comp : ComponentTag} (hc : F.ofC C comp = true) :
    1 ≤ depthC F C none (.goto E K l L d comp) := by
  have hn : F.ofC C none = false := by simp [Family.ofC, Family.Runs]
  simp [depthC, path, blocks, hc, hn]

/-- **The top of the term of a unit's call** at the tag `comp` of `C`'s
code: a `goto` or a frame of it, a value, or a throw of a value. -/
def TopC (F : Family) (C : Nat) (t : Tm) : Prop :=
  (∃ E K l L d comp, t = .goto E K l L d comp ∧ F.ofC C comp = true) ∨
  (∃ E K s L d k x comp, t = .frame E K s L d k x comp ∧ F.ofC C comp = true) ∨
  isVal t = true ∨ (∃ v, t = .throw v ∧ isVal v = true)

/-- **Every step keeps the top of a unit's call** (proved): entering a node
makes a frame of the same code, a frame's steps keep it, leave a `goto` of
the same code, a value or a throw of one. -/
theorem TopC.step {F : Family} {C : Nat} {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') (ht : TopC F C t) :
    TopC F C t' := by
  rcases ht with ⟨E, K, l, L, d, comp, rfl, hc⟩ | ⟨E, K, s, L, d, k, x, comp, rfl, hc⟩ | hv | ⟨v, rfl, hv⟩
  · cases hs with
    | gotoEnter => exact .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl, hc⟩)
  · cases hs with
    | frameC => exact .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl, hc⟩)
    | frameRet hv => exact .inr (.inr (.inl hv))
    | frameRaise hr => exact .inr (.inr (.inr ⟨_, rfl, raises_val hr⟩))
    | _ => exact .inl ⟨_, _, _, _, _, _, rfl, hc⟩
  · exact absurd hv (by rw [notVal_of_step hs]; simp)
  · cases hs with
    | throwC hs' => exact absurd hv (by rw [notVal_of_step hs']; simp)

/-- **A state of a unit's call that steps has the call active** (proved). -/
theorem TopC.depth {F : Family} {C : Nat} {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') (ht : TopC F C t) :
    1 ≤ depthC F C none t := by
  rcases ht with ⟨E, K, l, L, d, comp, rfl, hc⟩ | ⟨E, K, s, L, d, k, x, comp, rfl, hc⟩ | hv | ⟨v, rfl, hv⟩
  · exact depthC_goto hc
  · exact depthC_frame hc
  · exact absurd hv (by rw [notVal_of_step hs]; simp)
  · cases hs with
    | throwC hs' => exact absurd hv (by rw [notVal_of_step hs']; simp)

namespace ClientFrame
variable {τ : Type} {fr : ClientFrame τ}

/-- **An execution of a unit's call keeps the call active** (proved): every
state that steps has it active (`TopC.depth`), the top kept by each step
(`TopC.step`). -/
theorem ex_depth : ∀ {n : Nat} {a e : Conf × Ghost (fr.F.at fr.C)}, Ex fr.KStep (fun _ => True) n a e →
    TopC fr.F fr.C a.1.t → Ex fr.KStep (fun y => 1 ≤ δ fr.F fr.C none y) n a e
  | _, _, _, .refl a, _ => .refl a
  | _, _, _, .next _ hab he, ht =>
    .next (TopC.depth hab.1.step ht) hab (ex_depth he (TopC.step hab.1.step ht))

/-- **An entry's argument is witnessed at a reached state of its call**
(proved, `ex_depth`, `ex_xstep`, `witness_along`): from a call the claim is
about, at the top a `goto` of `C`'s code, and the entry history of its
arguments, at every state the execution reaches with the call still
active, each location an argument reaches read-only at its parameter's
type has a live witness at depth `1`. -/
theorem witness_reached (hc : fr.ChkSound) {args : Heap → Tm → List (fr.view.view.Ty × Val)}
    (hse : fr.StartsEntry args) {x : Conf} {g : Ghost (fr.F.at fr.C)} (hN : fr.Call x.s.h x.t)
    (hg : fr.start x.s.n x.s.W x.s.h x.t g) (htop : TopC fr.F fr.C x.t) (hdx : 1 ≤ depthC fr.F fr.C none x.t)
    {n : Nat} {e : Conf × Ghost (fr.F.at fr.C)} (hex : Ex fr.KStep (fun _ => True) n (x, g) e)
    (hde : 1 ≤ δ fr.F fr.C none e) {T : fr.view.view.Ty} {v : Val} (ha : (T, v) ∈ args x.s.h x.t) {l : Nat}
    (hr : ReachRO fr.view.view (fr.F.at fr.C).ofC T x.s.h v l) :
    Witness fr.view.view 1 (lift fr.F fr.C none e.1 e.2) l := by
  have hgs : g = entryStart fr.F fr.C fr.view.view x.s.h x.t (args x.s.h x.t) := (hse _ _ _ _ _).mp hg
  have hx := ex_xstep hc ⟨(x, g), 0, hN, hg, .refl _⟩ (ex_depth hex htop)
  subst hgs
  exact witness_along (fun _ h => h) hx hdx hde ha hr

end ClientFrame

end Verification.TolerantFrames.ReadOnly
