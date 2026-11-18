import Verification.Source.Claims.PassUnit
import Verification.Paper.TolerantFrames.ReadOnlyBridge

/-! # The framed claim where the client obligation is met

A framed plan's request is accepted under its frame's client obligation
(`FramedRequestSafe`). Where every execution from every history the frame
starts from keeps the obligation (`ClientFrame.Met`: an invariant on which
every step keeps it, as where no code outside the component runs,
`ClientFrame.keepsOn_inside`, or where outside code is certified to keep
`Θ`, `ClientFrame.keepsOn_of`), the framed claim is `RequestSafe` at every
call (`CallSafe`):

- `requestSafe_callSafe`: `RequestSafe` gives `CallSafe`, its clauses read
  at the environments of calls (`envOf L d`);
- `framed_callSafe`: `FramedRequestSafe` under a met obligation gives
  `CallSafe`. The graph's safety and its assertions are read back from the
  term that runs the graph (`GraphCode.safeGraph_of_sim`,
  `GraphCode.sim_step`). -/
namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open Verification.TolerantFrames.ReadOnly (ClientFrame)
open HeapObservations


section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **A request is safe at every call meeting `Ent`**: `RequestSafe`'s
clauses at the entries whose environment is a call's frame, `envOf L d`,
and whose term and heap meet `Ent`. -/
def CallSafe (Ent : Heap → Tm → Prop) (r : SourceRequest σ ι) : Prop :=
  (∀ η, r.Admits η → ∀ n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) → Ent h (gotoOf r.program r.start L d r.comp) →
    SafeGraph (excOf (reassign (RequestJson.graph r.toRequest) η)) r.program
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d))) n W h
      (.at r.start (envOf L d))) ∧
  (r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true →
    ∀ η n W h (L : List Tm) (d : Tm),
      EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
        (envOf L d) n W h → RootsOk W (envOf L d) →
      (∀ v ∈ L, isVal v = true) → isVal d = true → Ent h (gotoOf r.program r.start L d r.comp) →
      HeapObservations.SafePostExc (excOf (reassign (RequestJson.graph r.toRequest) η))
        (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
        (fun h' v => r.footprint.Holds h h' ∧ (r.fresh = true → Footprints.FreshAt h.length v))
        (fun h' => r.onThrow = true → r.footprint.Holds h h') n W h (gotoOf r.program r.start L d r.comp)) ∧
  (r.ensures ≠ [] → ∀ η n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) → Ent h (gotoOf r.program r.start L d r.comp) →
    HeapObservations.SafePost (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun h' v => GraphCode.EnsuresAt r.ensures ⟨envOf L d, h⟩ h' (push v (envOf L d))) n W h
      (gotoOf r.program r.start L d r.comp)) ∧
  (∀ Φ regions, r.regional = some (Φ, regions) → ∀ η n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) → Ent h (gotoOf r.program r.start L d r.comp) →
    HeapObservations.SafePostExc (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun h' _ => Footprints.ArgumentSpineRegionsWithin Φ regions (envOf L d) h h')
      (fun h' => r.stated.any (·.onThrow) = true →
        Footprints.ArgumentSpineRegionsWithin Φ regions (envOf L d) h h')
      n W h (gotoOf r.program r.start L d r.comp)) ∧
  (∀ η, r.Admits η → ∀ n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) → Ent h (gotoOf r.program r.start L d r.comp) →
    ∀ l k, (l, k) ∈ r.assertions → ∀ j h' ρ', j < n →
      ReachesIn r.program j h (.at r.start (envOf L d)) h' (.at l ρ') →
      HeapKnowledge.Holds k ⟨envOf L d, h⟩ ρ' h') ∧
  (∀ ci q, r.codes[ci]? = some q → ∀ η n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) (codeRequest r q).inputs {}
      (codeRequest r q).entryIndices (envOf L d) n W h →
    RootsOk W (envOf L d) → Ent h (gotoOf (codeRequest r q).program (codeRequest r q).start L d none) →
    ∀ l k, (l, k) ∈ (codeHintsAt r ci).requirements → ∀ j h' ρ', j < n →
      ReachesIn (codeRequest r q).program j h (.at (codeRequest r q).start (envOf L d)) h' (.at l ρ') →
      HeapKnowledge.Holds k ⟨envOf L d, h⟩ ρ' h')

/-- **`RequestSafe` is safe at every call** (proved): each clause at the
environments of calls, whatever they meet. -/
theorem requestSafe_callSafe {r : SourceRequest σ ι} (hr : RequestSafe r) (Ent : Heap → Tm → Prop) :
    CallSafe Ent r := by
  obtain ⟨hs, hf, he, hg, ha, hc⟩ := hr
  exact ⟨fun η hη n W h L d hE hR _ => hs η hη n W h (envOf L d) hE hR,
    fun hb η n W h L d hE hR hL hd _ => hf hb η n W h L d hE hR hL hd,
    fun hn η n W h L d hE hR _ => he hn η n W h L d hE hR,
    fun Φ regions hreg η n W h L d hE hR _ => hg Φ regions hreg η n W h L d hE hR,
    fun η hη n W h L d hE hR _ => ha η hη n W h (envOf L d) hE hR,
    fun ci q hq η n W h L d hE hR _ => hc ci q hq η n W h (envOf L d) hE hR⟩
end

/-! ## The framed claim at a met obligation -/

/-- The term `gotoOf` builds runs the graph from its entry. -/
theorem sim_gotoOf (P : Program) (l : Nat) (L : List Tm) (d : Tm) (c : ComponentTag) :
    GraphCode.Sim (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler)) (gotoOf P l L d c)
      (.at l (envOf L d)) := .goto

/-- **A graph path is a path of the term that runs it** (proved, by
`GraphCode.sim_step`). -/
theorem reaches_sim {E : List Tm} {K : List (Continuation × Option Target)} :
    ∀ {j : Nat} {h : Heap} {s : State} {h' : Heap} {s' : State},
      ReachesIn (GraphCode.program E K) j h s h' s' → ∀ {ts : Tm}, GraphCode.Sim E K ts s →
      ∃ ts', HeapObservations.Steps j h ts h' ts' ∧ GraphCode.Sim E K ts' s'
  | _, _, _, _, _, .refl, _, hs => ⟨_, .refl, hs⟩
  | _, _, _, _, _, .step tr hrest, _, hs => by
    obtain ⟨ts₁, st, hs₁⟩ := GraphCode.sim_step hs tr
    obtain ⟨ts', hst, hs'⟩ := reaches_sim hrest hs₁
    exact ⟨ts', .next st hst, hs'⟩

/-- **A framed run is a safe run where the obligation is met** (proved). -/
theorem framed_erase {τ : Type} {fr : ClientFrame τ} (hm : fr.Met) {J : Heap → Tm → Prop} {Ξ T : Fam} {Q : WPost} {R : WExc} {n : Nat}
    {W : WorldT n} {h : Heap} {t : Tm}
    (hs : ∀ g, fr.start n W h t g → SafeUnder fr.Keeps fr.next J Ξ T Q R n W g h t) :
    SafePostExcW Ξ T Q R n W h t ∧
      ∀ {j : Nat} {h' : Heap} {t' : Tm}, j < n → HeapObservations.Steps j h t h' t' → J h' t' := by
  obtain ⟨I, hk, hI⟩ := hm
  obtain ⟨g, hg⟩ := fr.start_total n W h t
  exact ⟨SafeUnder.erase hk (hI _ _ _ _ _ hg) (hs g hg),
    fun hj hst => SafeUnder.reach hk (hI _ _ _ _ _ hg) (hs g hg) hj hst⟩

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι] {fr : ClientFrame (Ty ι)}

/-- **An assertion read at a graph state reached** (proved): the term that
runs the graph reaches a `goto` at the label, at whose frame `J` gives it. -/
theorem asserted_of_reach {P : Program} {assertions : List (Nat × HeapKnowledge.Knowledge)} {ρ : Env}
    {h : Heap} {n : Nat} {start : Nat} {L : List Tm} {d : Tm} {c : ComponentTag}
    (hJ : ∀ {j : Nat} {h' : Heap} {t' : Tm}, j < n → HeapObservations.Steps j h (gotoOf P start L d c) h' t' →
      AssertedAt P assertions ρ h h' t')
    {l : Nat} {k : HeapKnowledge.Knowledge} (hl : (l, k) ∈ assertions) {j : Nat} {h' : Heap} {ρ' : Env}
    (hj : j < n) (hr : ReachesIn P j h (.at start (envOf L d)) h' (.at l ρ')) :
    HeapKnowledge.Holds k ⟨ρ, h⟩ ρ' h' := by
  rw [← SourceExtraction.program_nodes P] at hr
  obtain ⟨ts', hst, hs'⟩ := reaches_sim hr (sim_gotoOf P start L d c)
  cases hs' with
  | goto => exact hJ hj hst l k hl _ _ _ rfl

/-- **The framed claim is safety at every call where the obligation is
met** (proved): under a client frame whose obligation is met from every
history it starts from, a request safe under the frame is safe at every
call. -/
theorem framed_callSafe {r : SourceRequest σ ι} (hr : FramedRequestSafe r fr) (hm : fr.Met) :
    CallSafe fr.Call r := by
  obtain ⟨hs, hf, he, hg, ha, hc⟩ := hr
  refine ⟨fun η hη n W h L d hE hR hN => ?_, fun hb η n W h L d hE hR hL hd hN => ?_,
    fun hn η n W h L d hE hR hN => ?_, fun Φ regions hreg η n W h L d hE hR hN => ?_,
    fun η hη n W h L d hE hR hN => ?_, fun ci q hq η n W h L d hE hR hN => ?_⟩
  · have := (framed_erase hm (hs η hη n W h L d hE hR hN)).1.post.erase
    have := GraphCode.safeGraph_of_sim n W h (sim_gotoOf r.program r.start L d r.comp) this
    rwa [SourceExtraction.program_nodes] at this
  · exact (framed_erase hm (hf hb η n W h L d hE hR hL hd hN)).1
  · exact (framed_erase hm (he hn η n W h L d hE hR hN)).1.post
  · exact (framed_erase hm (hg Φ regions hreg η n W h L d hE hR hN)).1
  · exact fun l k hl j h' ρ' hj hre =>
      asserted_of_reach (framed_erase hm (ha η hη n W h L d hE hR hN)).2 hl hj hre
  · exact fun l k hl j h' ρ' hj hre =>
      asserted_of_reach (framed_erase hm (hc ci q hq η n W h L d none hE hR hN)).2 hl hj hre
end

/-! ## The framed claim's executions are the paper's -/

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι] {fr : ClientFrame (Ty ι)}
open Verification.TolerantFrames.ReadOnly

/-- **A graph path of a framed entry is an execution of the paper**
(proved): from an entry of the framed claim's assertions clause (its
contracts, valid roots, the frame's entry premises and a history it starts
from), a graph path within the budget to a state at a label is either broken
by a step that breaks the client obligation, after which the claim states
nothing, or an execution of steps keeping it (`KStep`) from the entry's
configuration to a reached configuration (`Reached`) that runs the graph at
that label: by `ClientFrame.kstep_xstep`, `ClientFrame.reached_ok` and
`ClientFrame.call_segment`, its steps are `XStep`s, its states are `Ok` at
their depth, and each of its calls of outside code is a run of outside code
(`ClientFrame.call_premises`) where `ChkSound` and `StartInv` hold. -/
theorem framed_reaches {r : SourceRequest σ ι} (ha : FramedAssertionsClause r fr) {η : MixedAssignment ι}
    (hη : r.Admits η) {n : Nat} {W : WorldT n} {h : Heap} {L : List Tm} {d : Tm} (hn : 0 < n)
    (hE : EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h) (hR : RootsOk W (envOf L d)) (hN : fr.Call h (gotoOf r.program r.start L d r.comp))
    {g : Ghost (fr.F.at fr.C)} (hg : fr.start n W h (gotoOf r.program r.start L d r.comp) g)
    {j : Nat} {h' : Heap} {l : Nat} {ρ' : Env} (hj : j + 1 < n)
    (hr : ReachesIn r.program j h (.at r.start (envOf L d)) h' (.at l ρ')) :
    ∃ x : Conf, x.s.h = h ∧ x.t = gotoOf r.program r.start L d r.comp ∧ x.s.n = n ∧
      ((∃ e, fr.Reached e ∧ Ex fr.KStep (fun _ => True) j (x, g) e ∧ e.1.s.h = h' ∧
        GraphCode.Sim (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler)) e.1.t
          (.at l ρ')) ∨
       (∃ b m h₁ t₁, Ex fr.KStep (fun _ => True) m (x, g) b ∧ m < j ∧ Step b.1.s.h b.1.t h₁ t₁ ∧
        ¬ fr.Keeps b.2 b.1.s.n b.1.s.W b.1.s.h b.1.t h₁ t₁)) := by
  have hs := ha η hη n W h L d hE hR hN g hg
  let x : Conf := ⟨⟨n, W, h, hn, hE.2.2.2.1, hE.2.2.2.2⟩, gotoOf r.program r.start L d r.comp,
    ClientFrame.safeUnder_refs hs⟩
  rw [← SourceExtraction.program_nodes r.program] at hr
  obtain ⟨ts', hst, hsim⟩ := reaches_sim hr (sim_gotoOf r.program r.start L d r.comp)
  refine ⟨x, rfl, rfl, rfl, ?_⟩
  rcases ClientFrame.safeUnder_path (x := x) hs hst hj with ⟨e, hex, he, ht⟩ | hb
  · exact .inl ⟨e, ClientFrame.reached_of_path hN hg hex, hex, he, ht ▸ hsim⟩
  · exact .inr hb
end

/-! ## A framed member -/

/-- **A member is safe at every call where its frame's obligation is met**
(proved): a member safe under `MemberSafe` whose certified plan is a graph
plan, or a framed plan whose frame's obligation is met, has a request safe
at every call. -/
theorem callSafe_of_member {f : FilePlans} {j : Nat} (hm : MemberSafe f j) :
    ∃ p c, f.plans[j]? = some (.ok p) ∧ p.certify = .ok c ∧
      match c with
      | .graph _ _ r => ∀ Ent, CallSafe Ent r
      | .framed _ _ r fr => fr.Met → CallSafe fr.Call r := by
  obtain ⟨p, c, hp, hc, hs⟩ := hm
  refine ⟨p, c, hp, hc, ?_⟩
  cases c with
  | graph _ _ r => exact requestSafe_callSafe hs
  | framed _ _ r fr => exact framed_callSafe hs

end Verification.SourceClaimJson.PassUnit
