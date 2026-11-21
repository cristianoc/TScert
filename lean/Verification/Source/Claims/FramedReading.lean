import Verification.Source.Claims.FramedCopies

/-! # The regions a framed node reads from its arguments

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Milestone 2: the protected
reading", the decision's (P) and the theorem chain's step 8). At a framed
node, a region rooted at a slot that holds the reads of a path from an
argument at a read-only position, where the component's protocol keeps
every part the path's and the region's steps read, has every location it
holds at the node reached from that argument at the call's entry heap:

- **A step's part** (`stepKeptB`, `stepKept_part`): the parts a step's
  locations may have, at kinds of its bound and its keys, at the site
  `none`; where the component's protocol keeps them all, it keeps the part
  of each location of the step at a heap meeting its world.
- **The locations an entry reads are kept** (`ClientFrame.region_reached`):
  the set of locations the arguments at read-only positions reach at the
  entry's heap, at kinds and keys the protocol keeps, holds its contents
  along the call (`kept_along`), so the copies hold (`copies_along`), and
  a region of the slot holds at the node only locations reached from the
  argument at the entry's heap (`region_reach`). -/

namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow Footprints

variable {P : Package}

/-- **A step's location has a kept part** (proved, `Region.bound_sound`,
`regionKeys_sound`): at a heap meeting its world, a location of a step
read in a value with valid references has its kind and key among the
step's, so `Ψ` keeps its part at the site `none`. -/
theorem stepKept_part {Ψ : Protocol P} {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) {w : Val}
    (hw : RefsOk W w) {q : Region} {ℓ : Nat} (hl : ℓ < h.length) (hm : q.mem (fun _ => w) h ℓ = true)
    (hq : stepKeptB Ψ q = true) : Ψ ⟨none, kindAt W ℓ, keyAt W ℓ⟩ = .keep := by
  unfold stepKeptB at hq
  split at hq
  · rename_i K hK
    have hρ : RootsOk W (fun _ => w) := fun _ => hw
    obtain ⟨role, hrole, hb⟩ := Region.bound_sound hok hρ q hl hm
    have hkey := regionKeys_sound hok hρ hK hl hm
    have hmem : (⟨none, kindAt W ℓ, keyAt W ℓ⟩ : Part P) ∈ partsOf [none] K q := by
      simp only [partsOf, List.mem_flatMap, List.mem_map, List.mem_singleton]
      exact ⟨none, rfl, _, by rw [kindAt, hrole]; exact roleKinds_mem hb, _, hkey, rfl⟩
    have := List.all_eq_true.mp hq _ hmem
    simpa using this
  · cases hq

/-- The steps of a path are read from slot `0` (proved). -/
theorem pathSteps_slot {π : List PropKey} {q : Region} (hq : q ∈ pathSteps π) : regionSlot q = some 0 := by
  simp only [pathSteps, keySteps, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hq
  obtain ⟨_, _, rfl | rfl⟩ := hq <;> rfl

/-- The steps of a region are read from slot `0` (proved). -/
theorem regionSteps_slot : ∀ {r q : Region}, q ∈ regionSteps r → regionSlot q = some 0
  | .path _ p _, q, hq | .spine _ p, q, hq => by
    simp only [regionSteps, ownSteps, List.mem_map] at hq
    obtain ⟨_, _, rfl⟩ := hq; rfl
  | .cells _, q, hq => by
    simp only [regionSteps, spineSteps, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> rfl
  | .pathCells _ p, q, hq => by
    simp only [regionSteps, ownSteps, spineSteps, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with ⟨_, _, rfl⟩ | rfl | rfl <;> rfl
  | .inCls r _, q, hq => regionSteps_slot (r := r) (by simpa [regionSteps] using hq)
  | .field _ _, _, hq | .fields _, _, hq | .pathFields _ _, _, hq | .cls _, _, hq | .all, _, hq => by
    simp [regionSteps] at hq

/-- **A step's location is reached from the value holding it** (proved,
`region_reach` at one heap). -/
theorem stepLoc_reach {ofC : ComponentTag → Bool} {h : Heap} {w : Val} {q : Region} (hq : regionSlot q = some 0)
    {ℓ : Nat} (hm : q.mem (fun _ => w) h ℓ = true) : Reaches ofC h w ℓ :=
  region_reach (ρ := fun _ => w) (h₀ := h) (h₁ := h) hq (fun _ _ _ _ => rfl) hm

/-- A value reached from a value with valid references has valid references
(proved). -/
theorem ValReach.refs {ofC : ComponentTag → Bool} {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h)
    {v w : Val} (hv : RefsOk W v) (hw : ValReach ofC h v w) : RefsOk W w := by
  rcases hw with rfl | ⟨_, l, _, hl⟩
  · exact hv
  · exact Footprints.HeapOk.contents_refs hok hl


namespace ClientFrame
variable {τ : Type} {fr : ClientFrame τ}

/-- **A region of a copy at a framed node is reached from its argument**
(proved, `kept_along`, `copies_along`, `region_reach`): from a call's
start at a run of the code `Pe`, `Pk` meeting the invariants of states,
whose slots below the arity at the positions `roPos` reach only locations
the start protects, along an execution to a frame of the code, some node
`l''` with the frame's continuation and handler has, for each entry of its
table at such a position whose path's steps the component's protocol
keeps, every location of a region of the entry's slot whose steps it
keeps, at the frame's slots and heap, reached from the argument at the
start's heap. -/
theorem region_reached [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    [LawfulHashable (Option (fr.F.at fr.C).Site)] {Fl : FFlow (fr.F.at fr.C)} {lay : List Layout}
    (hc : fr.ChkSound) (hi : fr.StartInv) (hFa : Fl.flow.Facts) (hS : fr.FlowSites Fl.flow)
    (hE : fr.EntryFits Fl.flow)
    (hwk : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → WOk a.1.t ∧ HeapW a.1.s.h)
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → wfS a.1.t = true)
    (hΘ : ∀ p, fr.Θ p = .keep) {Pe : List Tm} {Pk : List (Continuation × Option Target)} {c₀ : ComponentTag}
    {start arity : Nat} {cp : CopyTable} (hcp : copiesB Pe Pk start arity cp = true) (hlen : Pe.length = Pk.length)
    {roPos : Nat → Bool} {a : Conf × Ghost (fr.F.at fr.C)} (hN : fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t)
    (hg : fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2) (hc₀ : fr.F.ofC fr.C c₀ = true) {L₀ : List Tm} {d₀ : Tm}
    (hat : a.1.t = .goto Pe Pk start L₀ d₀ c₀) (hL₀ : SlotVals L₀ d₀)
    (hprot : ∀ j, j < arity → roPos j = true → ∀ ℓ, Reaches (fr.F.at fr.C).ofC a.1.s.h (envOf L₀ d₀ j) ℓ →
      ℓ < a.1.s.h.length ∧ RowProtects a.2 ℓ)
    {n : Nat} {b₀ : Conf × Ghost (fr.F.at fr.C)} (hex : Ex fr.KStep (fun _ => True) n a b₀) {u : Tm}
    {L : List Tm} {d : Tm} {k : Continuation} {x : Option Target} (hbt : b₀.1.t = .frame Pe Pk u L d k x c₀) :
    ∃ l'', Pk[l'']? = some (k, x) ∧ ∀ e ∈ cp.at l'', e.2.1 < arity → roPos e.2.1 = true →
      stepsKeptB (componentProtocol Fl lay) (pathSteps e.2.2) = true → ∀ r', regionSlot r' = some e.1 →
      stepsKeptB (componentProtocol Fl lay) (regionSteps r') = true → ∀ w, r'.mem (envOf L d) b₀.1.s.h w = true →
      Reaches (fr.F.at fr.C).ofC a.1.s.h (envOf L₀ d₀ e.2.1) w := by
  let h₀ := a.1.s.h
  let ρ₀ := envOf L₀ d₀
  have hρ₀ : RootsOk a.1.s.W ρ₀ := goto_rootsOk (by have := a.1.ok; rw [hat] at this; exact this)
  -- The kept set: what the arguments at read-only positions reach, at kept parts.
  let K : Nat → Prop := fun ℓ => (∃ j, j < arity ∧ roPos j = true ∧ Reaches (fr.F.at fr.C).ofC h₀ (ρ₀ j) ℓ) ∧
    componentProtocol Fl lay ⟨none, kindAt a.1.s.W ℓ, keyAt a.1.s.W ℓ⟩ = .keep
  have htop : TopC fr.F fr.C a.1.t := .inl ⟨_, _, _, _, _, _, hat, hc₀⟩
  obtain ⟨hexK, hlastK⟩ := kept_along hc hi hFa hS hE hwk hst hΘ (x := a.1) (g := a.2) hN hg htop (Rel := K)
    (fun ℓ ⟨⟨j, hj, hpos, hr⟩, hΨ⟩ => ⟨(hprot j hj hpos ℓ hr).1, (hprot j hj hpos ℓ hr).2, hΨ⟩) hex
  -- The reached states hold values in their heaps.
  have hhv : ∀ y, fr.Reached y → ∀ (l : Nat) (v : Tm), y.1.s.h[l]? = some v → isVal v = true :=
    fun y hy l v hv => ((fitsAt_reached hFa hS hE hy).2 l v hv).val
  have hinv₀ : CopyInv Pe Pk c₀ cp h₀ ρ₀ K a.1.t := .inl ⟨start, L₀, d₀, hat, hL₀, copiesB_start hcp⟩
  have hinv := copies_along hcp hlen hhv hexK ⟨a, 0, hN, hg, .refl _⟩ hinv₀
  rcases hinv with ⟨_, _, _, h', _, _⟩ | ⟨u', L', d', k', x', l'', h', _, hkx, hSH, _⟩ | hvt
  · rw [hbt] at h'; cases h'
  · rw [hbt] at h'
    simp only [Tm.frame.injEq] at h'
    obtain ⟨-, -, -, rfl, rfl, rfl, rfl, -⟩ := h'
    refine ⟨l'', hkx, ?_⟩
    rintro ⟨i, j, π⟩ he hj hpos hπ r' hslot hr' w hw
    -- A location reached from the argument, at a kept part, is in the kept set.
    have hK : ∀ v ℓ q, ValReach (fr.F.at fr.C).ofC h₀ (ρ₀ j) v → regionSlot q = some 0 →
        q.mem (fun _ => v) h₀ ℓ = true → stepKeptB (componentProtocol Fl lay) q = true → K ℓ := by
      intro v ℓ q hv hq hm hkq
      have hreach := hv.reaches (stepLoc_reach (ofC := (fr.F.at fr.C).ofC) hq hm)
      have hlt := (hprot j hj hpos ℓ hreach).1
      exact ⟨⟨j, hj, hpos, hreach⟩,
        stepKept_part a.1.s.ok (hv.refs a.1.s.ok (hρ₀ j)) hlt hm hkq⟩
    -- The copy holds.
    have hreads : Reads h₀ (ρ₀ j) π (envOf L d i) := hSH _ he fun ℓ v q hr => by
      obtain ⟨hv, hq, hm⟩ := readsAt_reach (ofC := (fr.F.at fr.C).ofC) hr (.inl rfl)
      exact hK v ℓ q hv (pathSteps_slot hq) hm (List.all_eq_true.mp hπ q hq)
    -- The region's prefix is kept at the node.
    rcases reads_reach (ofC := (fr.F.at fr.C).ofC) hreads (.inl rfl) with hu | hu
    · have hkeep : ∀ ℓ v q, RegionReadsAt h₀ r' (envOf L d i) ℓ v q → b₀.1.s.h[ℓ]? = h₀[ℓ]? := by
        intro ℓ v q hr
        obtain ⟨hv, hq, hm⟩ := regionReadsAt_reach (ofC := (fr.F.at fr.C).ofC) (W := a.1.s.W) hr
          (fun v' hv' => (hu.refs a.1.s.ok (hρ₀ j) |> fun hu' => hv'.refs a.1.s.ok hu'))
        have hvr : ValReach (fr.F.at fr.C).ofC h₀ (ρ₀ j) v := by
          rcases hv with rfl | ⟨π', l', hf, hl'⟩
          · exact hu
          · obtain ⟨π₀, hf₀⟩ := hu.reaches ⟨π', hf⟩
            exact .inr ⟨π₀, l', hf₀, hl'⟩
        exact hlastK ℓ (hK v ℓ q hvr (regionSteps_slot hq) hm (List.all_eq_true.mp hr' q hq))
      exact hu.reaches (region_reach (ρ := envOf L d) hslot hkeep hw)
    · -- An undefined copy holds no location.
      exfalso
      have hkeep : ∀ ℓ v q, RegionReadsAt h₀ r' (envOf L d i) ℓ v q → b₀.1.s.h[ℓ]? = h₀[ℓ]? := by
        intro ℓ v q hr
        obtain ⟨hv, hq, hm⟩ := regionReadsAt_reach (ofC := (fr.F.at fr.C).ofC) (W := a.1.s.W) hr
          (fun v' hv' => by
            rw [hu] at hv'
            rcases hv' with rfl | ⟨π', l', hf, _⟩
            · intro r hr; simp [refs] at hr
            · exact absurd ⟨π', hf⟩ undef_reaches)
        rw [hu] at hv
        rcases hv with rfl | ⟨π', l', hf, _⟩
        · exact absurd (stepLoc_reach (ofC := (fr.F.at fr.C).ofC) (regionSteps_slot hq) hm) undef_reaches
        · exact absurd ⟨π', hf⟩ undef_reaches
      have := region_reach (ofC := (fr.F.at fr.C).ofC) (ρ := envOf L d) hslot hkeep hw
      rw [hu] at this
      exact undef_reaches this
  · rw [hbt] at hvt
    rcases hvt with hv | ⟨_, h', _⟩
    · simp [isVal] at hv
    · cases h'

end ClientFrame

end Verification.TolerantFrames.ReadOnly

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly HeapObservations Verification.Footprints

/-- **The proposal of the copies passes the check** (proved, by its
definition): `copiesOf` returns a table `copiesB` passes, or the empty
table, which passes. -/
theorem copiesOf_sound (Pe : List Tm) (Pk : List (Continuation × Option Target)) (start arity bound : Nat) :
    copiesB Pe Pk start arity (copiesOf Pe Pk start arity bound) = true := by
  unfold copiesOf
  simp only
  split
  · assumption
  · simp only [copiesB, CopyTable.at, List.getD_nil, List.all_nil, Bool.true_and, List.all_eq_true]
    intro l _
    split
    · simp [edgeOkB, CopyTable.at]
    · rfl

end Verification.SourceClaimJson

namespace Verification.TolerantFrames.ReadOnly.ClientFrame
open Verification ControlFlow Footprints Verification.SourceClaimJson
variable {τ : Type} {fr : ClientFrame τ}

/-- **Every lent location of a region read as protected has a live
witness** (proved, `region_reached`, `witness_of_start`): from a call's
start meeting the invariants of states, at a run of the code whose slots
below the arity at read-only positions reach only locations the start
protects, and witnesses where they are released or outside storage, at a
frame of the code entering the node `l`, every released or outside
location of a region `protRegionB` reads as protected at the node is
reached from the argument at the entry's heap, so witnessed at the start
and, the history growing inside the call, at the frame's state. -/
theorem prot_witness [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    [LawfulHashable (Option (fr.F.at fr.C).Site)] {Fl : FFlow (fr.F.at fr.C)} {lay : List Layout}
    (hc : fr.ChkSound) (hi : fr.StartInv) (hFa : Fl.flow.Facts) (hS : fr.FlowSites Fl.flow)
    (hE : fr.EntryFits Fl.flow)
    (hwk : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → WOk a.1.t ∧ HeapW a.1.s.h)
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → wfS a.1.t = true)
    (hΘ : ∀ p, fr.Θ p = .keep) {Pe : List Tm} {Pk : List (Continuation × Option Target)} {c₀ : ComponentTag}
    {start arity : Nat} {cp : CopyTable} (hcp : copiesB Pe Pk start arity cp = true) (hlen : Pe.length = Pk.length)
    {roPos : Nat → Bool} {a : Conf × Ghost (fr.F.at fr.C)} (hN : fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t)
    (hg : fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2) (hc₀ : fr.F.ofC fr.C c₀ = true) {L₀ : List Tm} {d₀ : Tm}
    (hat : a.1.t = .goto Pe Pk start L₀ d₀ c₀) (hL₀ : SlotVals L₀ d₀)
    (hprot : ∀ j, j < arity → roPos j = true → ∀ ℓ, Reaches (fr.F.at fr.C).ofC a.1.s.h (envOf L₀ d₀ j) ℓ →
      ℓ < a.1.s.h.length ∧ RowProtects a.2 ℓ ∧ (a.2.Lent ℓ → Witness fr.view.view 1 (lift fr.F fr.C none a.1 a.2) ℓ))
    {n : Nat} {b₀ : Conf × Ghost (fr.F.at fr.C)} (hex : Ex fr.KStep (fun _ => True) n a b₀) {u : Tm}
    {L : List Tm} {d : Tm} {k : Continuation} {x : Option Target} {l : Nat} (hkl : Pk[l]? = some (k, x))
    (hbt : b₀.1.t = .frame Pe Pk u L d k x c₀) :
    ∀ r', protRegionB (componentProtocol Fl lay) cp arity roPos (Pe, Pk) l r' = true → ∀ w,
      r'.mem (envOf L d) b₀.1.s.h w = true → b₀.2.Lent w →
      Witness fr.view.view 1 (lift fr.F fr.C none b₀.1 b₀.2) w := by
  obtain ⟨l'', hkx, hreach⟩ := region_reached hc hi hFa hS hE hwk hst hΘ hcp hlen hN hg hc₀ hat hL₀
    (fun j hj hpos ℓ hr => ⟨(hprot j hj hpos ℓ hr).1, (hprot j hj hpos ℓ hr).2.1⟩) hex hbt
  intro r' hr' w hw hL
  unfold protRegionB at hr'
  split at hr'
  · cases hr'
  · rename_i xr hslot
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hr'
    obtain ⟨hsteps, hall⟩ := hr'
    have hshare : l'' ∈ sharingNodes (Pe, Pk) l := by
      simp only [sharingNodes, List.mem_filter, List.mem_range, beq_iff_eq]
      exact ⟨(List.getElem?_eq_some_iff.mp hkx).1, by rw [hkx, hkl]⟩
    obtain ⟨⟨i, j, π⟩, he, hcond⟩ := hall l'' hshare
    simp only [beq_iff_eq, decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨rfl, hj⟩, hpos⟩, hπ⟩ := hcond
    have hr := hreach _ he hj hpos hπ r' hslot hsteps w hw
    obtain ⟨hlt, -, hwit⟩ := hprot j hj hpos w hr
    have hsite : b₀.2.site w = a.2.site w := (ex_sites hS hex).2 w hlt
    have hL₀ : a.2.Lent w := by
      unfold Ghost.Lent Ghost.origin at hL ⊢; rw [hsite] at hL; exact hL
    have hdx : 1 ≤ depthC fr.F fr.C none a.1.t := by rw [hat]; exact depthC_goto hc₀
    have hde : 1 ≤ δ fr.F fr.C none b₀ := by simp only [δ]; rw [hbt]; exact depthC_frame hc₀
    exact witness_of_start hc hi hN hg (.inl ⟨_, _, _, _, _, _, hat, hc₀⟩) hdx hex hde (hwit hL₀)

end Verification.TolerantFrames.ReadOnly.ClientFrame

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly HeapObservations Verification.Footprints

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

namespace FramedSpec
variable (spec : FramedSpec ι)

/-- **The witness at a framed plan's frame** (proved, `start_protects`,
`ClientFrame.prot_witness`): at a reached state whose term is a frame of
the request's code entering the node `l`, every released or outside
location of a region `protRegionB` reads as protected there, at the
component's protocol and a checked table of copies, has a live witness at
depth `1`. The call it is reached from starts at an entry of the request
(`EntryAt`), whose slots at read-only positions reach only locations its
start protects and witnesses. -/
theorem prot_witness (r : SourceRequest σ ι) (hr : noRestB spec.lay = true) (hF : spec.flow.Facts)
    (hst : r.start < r.program.length) (hreal : realizedFlowB spec.fflow r = true)
    (hcomp : (spec.F.at spec.C).ofC r.comp = true) (har : spec.arityB r = true)
    (hro : readOnlyB r.inputs spec.readOnly spec.roPositions spec.outType = true) (hinner : spec.inner = false)
    (hm : Lendable spec.flow.O ∧ LocalHeld spec.flow.H) (hinitF : spec.InitialFits r) (hinitE : spec.InitialEntry r)
    (hinit : ∀ x, spec.Initial r x → spec.ProgOk r (x, bareStart (spec.core r).F (spec.core r).C x.t))
    (hrets : spec.RetsIn r) (hc : (spec.frame r).ChkSound) (hi : (spec.frame r).StartInv) (hE : (spec.frame r).EntryFits spec.flow)
    (hwk : ∀ (a : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)),
      (spec.frame r).Call a.1.s.n a.1.s.W a.1.s.h a.1.t → (spec.frame r).start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 →
        WOk a.1.t ∧ HeapW a.1.s.h)
    (hΘ : ∀ p, (spec.frame r).Θ p = .keep) {cp : CopyTable}
    (hcp : copiesB (requestCode r).1 (requestCode r).2 r.start spec.arity cp = true)
    {b₀ : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)} (hb : (spec.frame r).Reached b₀) {u : Tm}
    {L : List Tm} {d : Tm} {k : Continuation} {x : Option Target} {l : Nat}
    (hkl : (requestCode r).2[l]? = some (k, x))
    (hbt : b₀.1.t = .frame (requestCode r).1 (requestCode r).2 u L d k x r.comp) :
    ∀ r', protRegionB (componentProtocol spec.fflow spec.lay) cp spec.arity spec.roPos (requestCode r) l r' = true →
      ∀ w, r'.mem (envOf L d) b₀.1.s.h w = true → b₀.2.Lent w →
        Witness spec.view.view 1 (lift (spec.frame r).F (spec.frame r).C none b₀.1 b₀.2) w := by
  obtain ⟨a, n, hN, hg, hex⟩ := hb
  rcases hg with ⟨a₂, he, hga⟩ | ⟨hne, -⟩
  · obtain ⟨L₀, d₀, hat, hprot⟩ := spec.start_protects r hr hF hst hcomp har hro hinner hm hinitF hinitE hinit he a.1 rfl rfl
    have hL₀ : SlotVals L₀ d₀ :=
      spec.slotVals r hr hF hst hreal hcomp hinit hrets a.1.s.n a.1.s.W a.1.s.h L₀ d₀ (by rw [← hat]; exact hN)
    have hF' : spec.fflow.flow.Facts := hF
    have hS' : (spec.frame r).FlowSites spec.fflow.flow := spec.flowSites r
    have hE' : (spec.frame r).EntryFits spec.fflow.flow := hE
    have hlen : (requestCode r).1.length = (requestCode r).2.length := by simp [requestCode]
    have hg' : (spec.frame r).start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 := by rw [hga]; exact .inl ⟨a₂, he, rfl⟩
    have hat' : a.1.t = .goto (requestCode r).1 (requestCode r).2 r.start L₀ d₀ r.comp := by rw [hat]; rfl
    exact ClientFrame.prot_witness (fr := spec.frame r) (Fl := spec.fflow) (lay := spec.lay) hc hi hF' hS' hE' hwk
      (spec.wfS_start r) hΘ hcp hlen hN hg' hcomp hat' hL₀
      (fun j hj hpos ℓ hreach => by
        obtain ⟨hlt, -, -, hrow, hw⟩ := hprot j hj hpos ℓ hreach
        exact ⟨hlt, by rw [hga]; exact hrow, fun hL => hw (by rw [← hga]; exact hL) _ hga⟩)
      hex hkl hbt
  · exact absurd hN.2 hne

end FramedSpec
end
end Verification.SourceClaimJson
