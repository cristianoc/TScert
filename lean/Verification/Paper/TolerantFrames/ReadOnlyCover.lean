import Verification.Paper.TolerantFrames.ReadOnlyCharges

/-! # Read-only handles: the frame's check at regions with no sites

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The check at a call", the part
universe). A region read from no slot (`fields`, `pathFields`, `cls`,
`all`) has no computed sites (`regionSites` is `none`); the frame's check
reads it at a universe of sites `U` that every location's site lies in.

- **The check at a universe** (`frameCheckAtU`): each region's parts at
  its computed sites, or at `U` where it has none.
- **The check gives the rule's premise** (`framed_of_cover`): as
  `framed_of_sites`, with the premise that every location's site is in
  `U` in place of every region having sites.
- **Every location's site is among the flow's** (`stepSite_mem`,
  `ClientFrame.sites_in`, `ClientFrame.sites_in_flow`): a step's fresh
  locations take the allocation sites of the innermost frame's proposal or
  outside storage, each among the sites a flow names (`flowSites`); so at
  every reached state, from starts whose sites are among them. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

variable {P : Package}

/-! ## The check at a universe of sites -/

/-- **The parts at a call, at a universe**: a region's computed sites'
parts, or `U`'s where it has none. -/
def callPartsU (U : List (Option P.Site)) (H : SiteHeap P) (τ : Nat → List (Option P.Site))
    (keys : Region → List (Option PropKey)) (r : Region) : List (Part P) :=
  partsOf ((regionSites H τ r).getD U) (keys r) r

/-- **The frame's check at a call, at a universe**: the check over every
region's parts at its computed sites, or at `U`. -/
def frameCheckAtU (U : List (Option P.Site)) (q : SepQuery) (Ψ : Protocol P) (Φ S : Footprint) (H : SiteHeap P)
    (τ : Nat → List (Option P.Site)) (keys : Region → List (Option PropKey)) (prot : Region → Bool) : Bool :=
  frameCheck q Ψ Φ S (callPartsU U H τ keys) prot

/-- **The check at a universe gives the rule's premise** (proved, by
`regionSites_sound`, `flow_of_sites` and `frameCheck_sound`): where every
location's site is in `U`, the query is sound, the roots valid, the
environment meets the slots' sites, the heap the heap of sites, each
location's key is among its region's, and each lent location of a region
read as protected has a live history witness. -/
theorem framed_of_cover {U : List (Option P.Site)} {q : SepQuery} {Ψ : Protocol P} {Φ S : Footprint}
    {H : SiteHeap P} {τ : Nat → List (Option P.Site)} {keys : Region → List (Option PropKey)}
    {prot : Region → Bool} {tv : TypeView} {d : Nat} {ρ : Env} {st : St P}
    (hc : frameCheckAtU U q Ψ Φ S H τ keys prot = true) (hcov : ∀ l, l < st.s.h.length → st.g.site l ∈ U)
    (hq : q.Sound ρ st.s.h) (hρ : RootsOk st.s.W ρ)
    (henv : ∀ i, SitesOf st.g (τ i) (ρ i)) (hH : HeapSites st.g H st.s.h)
    (hkey : ∀ e ∈ S, ∀ l, l < st.s.h.length → e.1.mem ρ st.s.h l = true → st.g.key l ∈ keys e.1)
    (hw : ∀ e ∈ S, prot e.1 = true → ∀ l, l < st.s.h.length → e.1.mem ρ st.s.h l = true → st.g.Lent l →
      Witness tv d st l) :
    Framed Φ Ψ S ρ st := by
  refine frameCheck_sound hc hq ?_ (prot_of_witness hw)
  have hsite : ∀ e' ∈ S, ∀ l, l < st.s.h.length → e'.1.mem ρ st.s.h l = true →
      st.g.site l ∈ (regionSites H τ e'.1).getD U := by
    intro e' _ l' hl' hm'
    cases hT : regionSites H τ e'.1 with
    | none => exact hcov l' hl'
    | some T => exact regionSites_sound hH henv hT hm'
  exact flow_of_sites (sites := fun r => (regionSites H τ r).getD U) hρ hsite hkey

/-- **The check at a universe at a frame of `C`'s code** (proved): as
`framed_of_frame`, a frame of `C`'s code fitting the flow, at a heap
meeting it whose every location's site is in `U`, runs a node at which the
check at the universe gives `Framed`. -/
theorem framed_of_frame_cover {Fl : Flow P} {Γ : Nat → Option (Sites P)} {a : FrameAt P} {o : Bool}
    {S₀ : Sites P} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {t : Tm}
    {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    {st : St P} (hf : Fits Fl (VJ Fl st.g st.s.h.length) Γ a o S₀ (.frame E K t L d k x comp))
    (hc : P.ofC comp = true) (hH : HeapInv Fl st.g st.s.h) {U : List (Option P.Site)}
    (hcov : ∀ l, l < st.s.h.length → st.g.site l ∈ U) :
    ∃ c π l, Fl.code (E, K) c = some π ∧ NodeOf (E, K) l k x ∧
      ∀ {q : SepQuery} {Ψ : Protocol P} {Φ S : Footprint} {keys : Region → List (Option PropKey)}
        {prot : Region → Bool} {tv : TypeView} {dp : Nat},
        frameCheckAtU U q Ψ Φ S Fl.H (π.env l) keys prot = true → q.Sound (envOf L d) st.s.h →
        RootsOk st.s.W (envOf L d) →
        (∀ e ∈ S, ∀ w, w < st.s.h.length → e.1.mem (envOf L d) st.s.h w = true → st.g.key w ∈ keys e.1) →
        (∀ e ∈ S, prot e.1 = true → ∀ w, w < st.s.h.length → e.1.mem (envOf L d) st.s.h w = true →
          st.g.Lent w → Witness tv dp st w) →
        Framed Φ Ψ S (envOf L d) st := by
  obtain ⟨c, π, l, hcode, hn, henv⟩ := frame_sites hf hc
  exact ⟨c, π, l, hcode, hn, fun hck hq hρ hkey hw => framed_of_cover hck hcov hq hρ henv hH.sites hkey hw⟩

/-! ## Every location's site is among the flow's -/

section flowSites
variable [DecidableEq P.Site] [Hashable P.Site]

theorem mem_flowSites {F : FFlow P} {s : Option P.Site} :
    s ∈ flowSites F ↔ s ∈ none :: F.O ++ F.heap.flatMap (fun (s, S) => s :: S) ++
      F.codes.flatMap fun (_, cs) => cs.flatMap fun (_, c) =>
        c.tok :: c.alloc.obj :: c.alloc.arr :: c.ret ++ c.allocs.flatMap (fun (_, o, a) => [o, a]) ++
          (c.dflt :: c.nodes.toList).flatMap fun x => x.val ++ x.dflt ++ x.env.toList.flatten := by
  simp only [flowSites, Std.HashSet.mem_toList, Std.HashSet.mem_ofList, List.contains_iff_mem]

/-- **A proposal's allocation sites are the flow's** (proved). -/
theorem allocAt_mem {F : FFlow P} {m : Code} {c : Nat} {fc : FCode P} (h : F.at m c = some fc) (kx : NodeKey) :
    (fc.allocAt kx).obj ∈ flowSites F ∧ (fc.allocAt kx).arr ∈ flowSites F := by
  obtain ⟨l, hm, hc⟩ := FFlow.at_mem h
  have hin : ∀ s, (s = fc.alloc.obj ∨ s = fc.alloc.arr ∨ ∃ e ∈ fc.allocs, s = e.2.1 ∨ s = e.2.2) →
      s ∈ flowSites F := by
    intro s hs
    rw [mem_flowSites]
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨(m, l), hm, List.mem_flatMap.mpr ⟨(c, fc), hc, ?_⟩⟩)
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap]
    rcases hs with rfl | rfl | ⟨e, he, rfl | rfl⟩
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr (.inl (.inr ⟨e, he, by simp⟩))))
    · exact .inr (.inr (.inr (.inl (.inr ⟨e, he, by simp⟩))))
  unfold FCode.allocAt
  split
  · rename_i e o a he
    have hm' := List.mem_of_find?_eq_some he
    exact ⟨hin _ (.inr (.inr ⟨_, hm', .inl rfl⟩)), hin _ (.inr (.inr ⟨_, hm', .inr rfl⟩))⟩
  · exact ⟨hin _ (.inl rfl), hin _ (.inr (.inl rfl))⟩

theorem none_mem_flowSites (F : FFlow P) : none ∈ flowSites F := by
  rw [mem_flowSites]; simp

/-- **A step's fresh locations take the flow's sites** (proved): the
allocation sites of the innermost frame's proposal, or outside storage. -/
theorem stepSite_mem (F : FFlow P) (cur : Option FrameKey) (t : Tm) : stepSite F.flow cur t ∈ flowSites F := by
  have hA : ∀ fr, (allocOf F.flow fr).obj ∈ flowSites F ∧ (allocOf F.flow fr).arr ∈ flowSites F := by
    intro fr
    match fr with
    | none => exact ⟨none_mem_flowSites F, none_mem_flowSites F⟩
    | some ((m, comp), kx) =>
      simp only [allocOf]
      split
      · cases hc : F.at m entryCx with
        | none => simp [FFlow.flow, hc, Alloc.outside, none_mem_flowSites]
        | some fc => simpa [FFlow.flow, hc, FCode.flow] using allocAt_mem hc kx
      · exact ⟨none_mem_flowSites F, none_mem_flowSites F⟩
  unfold stepSite
  split <;> first | exact (hA _).1 | exact (hA _).2

end flowSites

namespace ClientFrame
variable {τ : Type} {fr : ClientFrame τ}

/-- **Every location's site is in a universe** (proved, along the
execution): where every start's sites are in `U`, `U` holds outside
storage and every site the checks give, every location of a reached state
has a site in `U`. -/
theorem sites_in {U : List (Option (fr.F.at fr.C).Site)} (hnone : none ∈ U)
    (hchk : ∀ h t h' t' w, (fr.chk h t h' t').site w ∈ U)
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → ∀ w, a.2.site w ∈ U)
    {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b) : ∀ w, b.2.site w ∈ U := by
  obtain ⟨a, n, hc, hs, hex⟩ := hb
  refine hex.carry (r := fun x : Conf × Ghost (fr.F.at fr.C) => ∀ w, x.2.site w ∈ U) ?_ (hst a hc hs)
  intro x y _ hxy hx w
  obtain ⟨-, hg, -⟩ := hxy
  rw [hg]
  simp only [FrameCore.next, stepAt_site, Ghost.alloc]
  split
  · exact hx w
  · split
    · exact hnone
    · exact hchk _ _ _ _ w

/-- **Every location's site is among the flow's** (`sites_in_flow`,
proved): at a frame whose checks give fresh locations the flow's sites
(`FlowSites`), from starts whose sites are the flow's, every location of a
reached state has a site among those the flow names. -/
theorem sites_in_flow [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    {F : FFlow (fr.F.at fr.C)} (hS : fr.FlowSites F.flow)
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → ∀ w, a.2.site w ∈ flowSites F)
    {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b) : ∀ w, b.2.site w ∈ flowSites F :=
  sites_in (none_mem_flowSites F) (fun h t h' t' w => by rw [hS h t h' t']; exact stepSite_mem F none t) hst hb

end ClientFrame

end Verification.TolerantFrames.ReadOnly
