import Verification.Source.Claims.FramedProtection
import Verification.Source.Claims.FramedPaths

/-! # The locations a framed call keeps

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Milestone 2: the protected
reading", the theorem chain's step 6). Along a framed plan's execution, a
location keeps its contents where the history protects it and no code of
`C` is charged at its kind and key:

- **A step of the term's active frame** (`activeFrame_tag_ne`): a step
  changing the heap reduces its redex at the frame the path's innermost
  tag reads, as an allocating step does (`activeFrame_tag`).
- **A step keeps such a location** (`ClientFrame.kept_step`): a step of
  outside code by the client obligation at the history (`Row`, `Θ_C`
  keeping every part); a step of `C`'s code changes an old location only
  at a kind and key its frame's code charges (`step_kind_charged`,
  `frameKinds_flow`), where the component's protocol is `any`
  (`probeProtocol_charged`); a step changing the calls of `C` active keeps
  the heap (`step_wfS`). -/

namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow HeapObservations

/-- **The frame of a step that changes the heap is the path's innermost**
(proved, by induction on the step, as `activeFrame_tag`): `activeFrame`
and `path` follow the same congruences, and a step changing the heap runs
no `goto`. -/
theorem activeFrame_tag_ne {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') (hlen : h' ≠ h) :
    ∀ cur : Option FrameKey, frameTag (activeFrame cur t).1 = activeTag Realm.empty (frameTag cur) false t := by
  induction hs
  all_goals intro cur
  -- Steps that keep the heap's length allocate nothing.
  all_goals try (exfalso; exact hlen rfl)
  case callL hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case callRecv hfv hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn, hfv]) (by simp [activeTag, path, wrap_head, hn, hfv]) (ih hlen cur)
  case callArg hfv hrv hai hpre hst ih =>
    have hn := notVal_of_step hst
    refine activeFrame_cong_eq _ (by simp only [activeFrame, hfv, hrv, Bool.true_eq_false, ite_false]; exact activeArgs_at hai hpre hn)
      (by simp only [activeTag, path, hfv, hrv, Bool.true_eq_false, ite_false, pathArgs_at _ hai hpre hn, wrap_head]) (ih hlen cur)
  case constructL hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case constructArg hfv hai hpre hst ih =>
    have hn := notVal_of_step hst
    refine activeFrame_cong_eq _ (by simp only [activeFrame, hfv, Bool.true_eq_false, ite_false]; exact activeArgs_at hai hpre hn)
      (by simp only [activeTag, path, hfv, Bool.true_eq_false, ite_false, pathArgs_at _ hai hpre hn, wrap_head]) (ih hlen cur)
  case letC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case spreadC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case makeArg hai hpre hst ih =>
    have hn := notVal_of_step hst
    refine activeFrame_cong_eq _ (by simp only [activeFrame]; exact activeArgs_at hai hpre hn)
      (by simp only [activeTag, path, pathArgs_at _ hai hpre hn, wrap_head]) (ih hlen cur)
  case readC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case indexC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case indexC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case writeC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case writeC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case testC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case iteC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case arithC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case arithC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case arrArg hai hpre hst ih =>
    have hn := notVal_of_step hst
    refine activeFrame_cong_eq _ (by simp only [activeFrame]; exact activeArgs_at hai hpre hn)
      (by simp only [activeTag, path, pathArgs_at _ hai hpre hn, wrap_head]) (ih hlen cur)
  case elemC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case elemC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case setC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case setC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case setC3 hav hiv hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn, hav, hiv]) (by simp [activeTag, path, wrap_head, hn, hav, hiv]) (ih hlen cur)
  case lenC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case throwC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case mergeC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case mergeC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case makeKeyC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case makeKeyC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong_eq _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case frameC ih =>
    rw [activeTag_frame]
    simp only [activeFrame]
    exact ih hlen _
  case makeFields hvs _ =>
    simp only [activeFrame, path, activeArgs_vals hvs, pathArgs_vals _ hvs, activeTag]; rfl
  case arrAlloc hvs _ =>
    simp only [activeFrame, path, activeArgs_vals hvs, pathArgs_vals _ hvs, activeTag]; rfl
  case arrAllocThrow hvs _ =>
    simp only [activeFrame, path, activeArgs_vals hvs, pathArgs_vals _ hvs, activeTag]; rfl
  case setGrow ls b _ _ v hv _ _ =>
    simp only [activeFrame, path, hv, show isVal (.arr ls) = true from rfl, show isVal (.num b) = true from rfl,
      Bool.true_eq_false, ite_false, activeTag, List.head?_cons, Option.map_some, Option.getD_some]
  case lenStrThrow =>
    simp [activeFrame, path, activeTag, isVal]
  case arithThrow hb =>
    obtain ⟨ha, hb'⟩ := binopThrows_values hb
    simp [activeFrame, path, activeTag, ha, hb']
  all_goals simp_all [activeFrame, path, activeTag, isVal]


/-- **A step changing the heap keeps the calls of `C` active** (proved,
`step_wfS`): its path keeps its tags. -/
theorem depth_of_heap_ne {F : Family} {C : Nat} {h h' : Heap} {t t' : Tm} (hs : Step h t h' t')
    (hw : wfS t = true) (hh : HeapFree h) (hne : h' ≠ h) : depthC F C none t' = depthC F C none t := by
  rcases (step_wfS hs hw hh).2 with e | hst
  · exact absurd e hne
  · obtain ⟨F₀, F', rest, hP, hP', ht⟩ := hst F.realm none false
    unfold depthC
    rw [hP, hP']
    simp [ht]

namespace ClientFrame
variable {τ : Type} {fr : ClientFrame τ}

/-- **A step keeps a protected location no code of `C` is charged at**
(proved): a reached step whose term holds no write outside every frame
keeps the contents of an old location the history protects (`RowProtects`)
where the component's protocol keeps its kind and key: a step of outside
code by the client obligation, which keeps every part (`Row`); a step of
`C`'s code changes an old location only at a kind and key its frame's code
charges (`step_kind_charged`, `frameKinds_flow`), where the protocol is
`any` (`probeProtocol_charged`); a step changing the calls of `C` active
keeps the heap (`depth_of_heap_ne`). -/
theorem kept_step [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    [LawfulHashable (Option (fr.F.at fr.C).Site)] {Fl : FFlow (fr.F.at fr.C)} {lay : List Layout}
    (hrn : ∀ t, fr.F.realm.tags t = false)
    (hc : fr.ChkSound) (hFa : Fl.flow.Facts) (hS : fr.FlowSites Fl.flow) (hE : fr.EntryFits Fl.flow)
    (hwk : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → WOk a.1.t ∧ HeapW a.1.s.h)
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → wfS a.1.t = true)
    (hΘ : ∀ p, fr.Θ p = .keep) {y z : Conf × Ghost (fr.F.at fr.C)} (hy : fr.Reached y) (hk : fr.KStep y z)
    (hwy : writesK y.1.t = []) {ℓ : Nat} (hlt : ℓ < y.1.s.h.length) (hprot : RowProtects y.2 ℓ)
    (hΨ : componentProtocol Fl lay ⟨none, kindAt y.1.s.W ℓ, keyAt y.1.s.W ℓ⟩ = .keep) :
    z.1.s.h[ℓ]? = y.1.s.h[ℓ]? := by
  obtain ⟨v, hv⟩ : ∃ v, y.1.s.h[ℓ]? = some v := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hstep := hk.1.step
  by_cases hne : z.1.s.h = y.1.s.h
  · rw [hne]
  have hd := depth_of_heap_ne (F := fr.F) (C := fr.C) hstep (reached_wfS hst hy) (Reached.entry hy).2.1.2 hne
  by_cases ho : OutsideAt fr.F fr.C none y.1.t
  · -- A step of outside code: the client obligation keeps every part.
    have hx := kstep_xstep hc hy hk
    have hrow := hx.2.2.2
    unfold StepHyp at hrow
    rw [ite_eq_left (kind_outside ho hd)] at hrow
    obtain ⟨v', hv', hhold⟩ := (row_iff.mp hrow) ℓ v hprot hv
    simp only [lift, hΘ, Footprints.Change.Holds] at hhold hv'
    rw [hv', hhold, hv]
  · -- A step of `C`'s code: a change is at a charged kind and key.
    rw [hv]
    refine Classical.byContradiction fun hne' => ?_
    have hu : isVal y.1.t = false := by
      cases e : isVal y.1.t
      · rfl
      · exact absurd hstep (value_no_step e)
    have hch := step_kind_charged (K₀ := []) hstep (wok_reached hwk hy).1 (by rw [hwy]; exact List.Subset.refl _)
      y.1.ok hv hne'
    have htag := activeFrame_tag_ne hstep hne none
    have hC : ∀ key, (activeFrame none y.1.t).1 = some key → (fr.F.at fr.C).ofC key.1.2 = true := by
      intro key hkey
      rw [hkey] at htag
      simp only [frameTag] at htag
      rw [outsideAt_noRealm hrn, Classical.not_not] at ho
      simp only [Family.at, Family.ofC, htag, decide_eq_true_eq]
      exact ho
    have hfr := frameKinds_flow (K₀ := []) (Fits.frameIn_hole (V := VJ Fl.flow y.2 y.1.s.h.length) .hole hu
      (fitsAt_reached hFa hS hE hy).1) hC hch
    have hany := probeProtocol_charged (P := fr.F.at fr.C) (K := flowKinds Fl)
      (held := capClose Fl (tokenCaps Fl lay) (captureSites Fl lay ++ Fl.O))
      (p := ⟨none, kindAt y.1.s.W ℓ, keyAt y.1.s.W ℓ⟩) (by simpa using hfr) (by simp)
    simp only [componentProtocol] at hΨ
    rw [hany] at hΨ
    cases hΨ


/-- A term at the top of a unit's call holds no write outside every frame
(proved). -/
theorem TopC.writes {F : Family} {C : Nat} {t : Tm} (ht : TopC F C t) : writesK t = [] := by
  rcases ht with ⟨_, _, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, rfl, _⟩ | hv | ⟨v, rfl, hv⟩
  · rfl
  · rfl
  · exact writesK_val hv
  · simp only [writesK]; exact writesK_val hv

/-- **A set of locations protected at a unit's start and kept by the
component's protocol keeps its contents along the call** (proved, by
induction on the execution, `kept_step` at each step): from a call the
claim is about, at the top a run of `C`'s code, and a start meeting the
invariants of states, each location of `Rel`, allocated at the start,
protected there (`RowProtects`) and at a kind and key the component's
protocol keeps, holds its start's contents at every state of an execution
from the start: the history grows inside the call, which keeps the
protection (`XStep.grows`, `Grows.prot`, `Grows.exposed`), the sites of
old locations are kept (`next_site`), and admissible steps keep their
kinds and keys (`kindAt_kept`, `keyAt_kept`). -/
theorem kept_along [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    [LawfulHashable (Option (fr.F.at fr.C).Site)] {Fl : FFlow (fr.F.at fr.C)} {lay : List Layout}
    (hrn : ∀ t, fr.F.realm.tags t = false)
    (hc : fr.ChkSound) (hi : fr.StartInv) (hFa : Fl.flow.Facts) (hS : fr.FlowSites Fl.flow)
    (hE : fr.EntryFits Fl.flow)
    (hwk : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → WOk a.1.t ∧ HeapW a.1.s.h)
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → wfS a.1.t = true)
    (hΘ : ∀ p, fr.Θ p = .keep) {x : Conf} {g : Ghost (fr.F.at fr.C)}
    (hN : fr.Call x.s.n x.s.W x.s.h x.t) (hg : fr.start x.s.n x.s.W x.s.h x.t g) (htop : TopC fr.F fr.C x.t)
    {Rel : Nat → Prop}
    (hrel : ∀ ℓ, Rel ℓ → ℓ < x.s.h.length ∧ RowProtects g ℓ ∧
      componentProtocol Fl lay ⟨none, kindAt x.s.W ℓ, keyAt x.s.W ℓ⟩ = .keep)
    {n : Nat} {e : Conf × Ghost (fr.F.at fr.C)} (hex : Ex fr.KStep (fun _ => True) n (x, g) e) :
    Ex fr.KStep (fun y => ∀ ℓ, Rel ℓ → y.1.s.h[ℓ]? = x.s.h[ℓ]?) n (x, g) e ∧
      ∀ ℓ, Rel ℓ → e.1.s.h[ℓ]? = x.s.h[ℓ]? := by
  -- The invariant along the execution, relative to the start.
  let I : Conf × Ghost (fr.F.at fr.C) → Prop := fun y => fr.Reached y ∧ TopC fr.F fr.C y.1.t ∧
    Admissible x.s y.1.s ∧ (∀ ℓ, ℓ < x.s.h.length → y.2.site ℓ = g.site ℓ) ∧
    (1 ≤ δ fr.F fr.C none y → Grows 1 g y.2) ∧ ∀ ℓ, Rel ℓ → y.1.s.h[ℓ]? = x.s.h[ℓ]?
  have hI₀ : I (x, g) := by
    refine ⟨⟨(x, g), 0, hN, hg, .refl _⟩, htop, Admissible.refl _, fun _ _ => rfl, fun hd => ?_, fun _ _ => rfl⟩
    obtain ⟨-, hl⟩ := hi x g hN.1 hg
    exact Grows.refl Nat.one_pos (by rw [hl]; exact hd)
  have step : ∀ {y z : Conf × Ghost (fr.F.at fr.C)}, I y → fr.KStep y z → I z := by
    intro y z hy hk
    obtain ⟨hR, ht, hadm, hsite, hgrow, hkeep⟩ := hy
    have hdy : 1 ≤ δ fr.F fr.C none y := TopC.depth hk.1.step ht
    have hR' := Reached.step hR hk
    have hlen := Footprints.step_length_le hk.1.step
    refine ⟨hR', ht.step hk.1.step, WorldReach.trans hadm hk.1.adm, fun ℓ hℓ => ?_, fun hdz => ?_,
      fun ℓ hℓ => ?_⟩
    · have hℓy : ℓ < y.1.s.h.length := Nat.lt_of_lt_of_le hℓ hadm.length_le
      rw [next_site hS hk ℓ (Nat.lt_of_lt_of_le hℓy hlen), Ghost.alloc_old hℓy, hsite ℓ hℓ]
    · obtain ⟨hl, hinv, -⟩ := reached_ok hc hi hR
      exact (hgrow hdy).trans (XStep.grows (kstep_xstep hc hR hk) hl hinv Nat.one_pos hdy hdz)
    · obtain ⟨hlt, hprot, hΨ⟩ := hrel ℓ hℓ
      have hℓy : ℓ < y.1.s.h.length := Nat.lt_of_lt_of_le hlt hadm.length_le
      have hg' := hgrow hdy
      have ho : y.2.origin ℓ = g.origin ℓ := by simp only [Ghost.origin, hsite ℓ hlt]
      have hprot' : RowProtects y.2 ℓ := by
        rcases hprot with ⟨he, hE⟩ | ⟨hL, hP⟩
        · exact .inl ⟨ho.trans he, hg'.exposed ℓ hE⟩
        · exact .inr ⟨by unfold Ghost.Lent; rw [ho]; exact hL, hg'.prot ℓ hP⟩
      have hΨ' : componentProtocol Fl lay ⟨none, kindAt y.1.s.W ℓ, keyAt y.1.s.W ℓ⟩ = .keep := by
        rw [kindAt_kept hadm hlt, keyAt_kept hadm hlt]; exact hΨ
      rw [kept_step hrn hc hFa hS hE hwk hst hΘ hR hk (TopC.writes ht) hℓy hprot' hΨ', hkeep ℓ hℓ]
  suffices ∀ {n : Nat} {y e : Conf × Ghost (fr.F.at fr.C)}, I y → Ex fr.KStep (fun _ => True) n y e →
      Ex fr.KStep (fun y => ∀ ℓ, Rel ℓ → y.1.s.h[ℓ]? = x.s.h[ℓ]?) n y e ∧ ∀ ℓ, Rel ℓ → e.1.s.h[ℓ]? = x.s.h[ℓ]? from
    this hI₀ hex
  intro n y e hy hex
  induction hex with
  | refl a => exact ⟨.refl a, hy.2.2.2.2.2⟩
  | next _ hab _ ih =>
    obtain ⟨hrest, hlast⟩ := ih (step hy hab)
    exact ⟨.next hy.2.2.2.2.2 hab hrest, hlast⟩

end ClientFrame

end Verification.TolerantFrames.ReadOnly
