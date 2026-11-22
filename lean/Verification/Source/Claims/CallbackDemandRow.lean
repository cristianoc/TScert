import Verification.Source.Claims.CallbackDemandOriginRun
import Verification.Source.Claims.PassUnitHeadline

/-! # The walker side of a callback demand

A callback-demand plan's request is safe at every call meeting its
callback returns (`CallbackReturnsMet`, `PassUnitHeadline.callbackDemand_requestSafe`).
This module states those returns at the level of the graph machine and
proves the step from them to the term-level invariant:

- `FramedReturnsReached spec P start n W h ρ`: at every state `.at l ρ'`
  the graph machine of `P` reaches from `.at start ρ` on `h`, at every
  admissible world above `W` typing the heap there, every normal return of
  the node's term within the budget keeps the supports `spec.framed` lists
  for `l` (`Supported`, between the heap the node was entered at and the
  heap it returns at).
- `callbackReturnsMet_of_reached` (proved): `FramedReturnsReached` at the
  entry gives `CallbackReturnsMet spec` of the term that runs the graph
  (`gotoOf`): the invariant follows the run step by step (`GraphCode.sim_step_back`),
  recording at each framed node the heap and world it was entered at and
  the steps its term has taken. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean Verification ProgramTyping RequestJson SourceElaboration ControlFlow
open PositiveGraphs PositiveRules LabelStore HeapObservations CallbackDemands

/-! ## The framed returns at reached framed nodes -/

/-- **The framed returns at every reached framed node**: at every node
`l` the graph machine of `P` reaches in `j` transitions from `.at start ρ`
on `h`, at environment `ρ'` and heap `h₁`, at every world `V` of index
`k` (with `j + k ≤ n`) extending `W` truncated, admissible and typing `h₁`,
every run of the node's term returning a value in fewer than `k` steps, at
`h₂`, keeps every support `spec.framed` lists for `l` from `h₁` to `h₂`. -/
def FramedReturnsReached (spec : CallbackDemands.CallbackDemandSpec) (P : Program) (start : Nat)
    (n : Nat) (W : WorldT n) (h : Heap) (ρ : Env) : Prop :=
  ∀ j h₁ l ρ' (node : Node), ReachesIn P j h (.at start ρ) h₁ (.at l ρ') → P[l]? = some node →
    ∀ k (hk : k ≤ n) (V : WorldT k), j + k ≤ n → WExt (trunc k hk W) V → WorldAdm V → HeapOk k V h₁ →
    ∀ j₁ h₂ v, j₁ < k → Steps j₁ h₁ (instantiate 0 ρ' node.expression) h₂ v → isVal v = true →
    ∀ T ∈ (SinglePass.framedAt spec.framed l).getD [], Footprints.Supported T ρ' h₁ h₂

/-- The invariant `callbackReturnsMet_of_reached` follows: the state is
reached from the entry in `j` steps, its world of index `k` extends the
entry's truncated with `j + k ≤ n`, and a pending framed node `l` entered
at `h₁` is the running frame's, entered by a reached `goto` at the world
`V₁` of index `k₁`, its term run `j₁` steps with `k + j₁ ≤ k₁`. -/
def ReachedFrames (P : Program) (start : Nat) (L : List Tm) (d : Tm) (comp : ComponentTag)
    (n : Nat) (W : WorldT n) (h : Heap) :
    Option (Nat × Heap) → (k : Nat) → WorldT k → Heap → Tm → Prop :=
  fun p k V h' t' => ∃ (hk : k ≤ n) (j : Nat), WExt (trunc k hk W) V ∧ j + k ≤ n ∧
    Steps j h (gotoOf P start L d comp) h' t' ∧
    ∀ l h₁, p = some (l, h₁) →
      ∃ (u : Tm) (L' : List Tm) (d' : Tm) (cont : Continuation) (x : Option Target) (comp' : ComponentTag)
        (e : Tm) (j₀ k₁ : Nat) (hk₁ : k₁ ≤ n) (V₁ : WorldT k₁) (j₁ : Nat),
        t' = .frame (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler)) u L' d' cont x comp' ∧
        (P.map (·.expression))[l]? = some e ∧
        Steps j₀ h (gotoOf P start L d comp) h₁
          (.goto (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler)) l L' d' comp') ∧
        j₀ + k₁ ≤ n ∧ WExt (trunc k₁ hk₁ W) V₁ ∧ WorldAdm V₁ ∧ HeapOk k₁ V₁ h₁ ∧
        Steps j₁ h₁ (instantiate 0 (envOf L' d') e) h' u ∧ k + j₁ ≤ k₁

/-- A value is no frame. -/
theorem isFrame_of_isVal {v : Tm} (hv : isVal v = true) : isFrame v = false := by
  cases v <;> simp_all [isFrame, isVal]

/-- **The framed returns at reached nodes are the callback returns of the
run** (proved): `FramedReturnsReached` at the entry `(n, W, h, envOf L d)`
gives `CallbackReturnsMet spec` of the term that runs `P` from it, at
every component, the invariant `ReachedFrames`. -/
theorem callbackReturnsMet_of_reached {spec : CallbackDemands.CallbackDemandSpec} {P : Program} {start : Nat}
    {L : List Tm} {d : Tm} {comp : ComponentTag} {n : Nat} {W : WorldT n} {h : Heap}
    (hret : FramedReturnsReached spec P start n W h (envOf L d)) :
    CallbackReturnsMet spec n W h (gotoOf P start L d comp) := by
  refine ⟨ReachedFrames P start L d comp n W h,
    ⟨Nat.le_refl n, 0, by rw [trunc_id]; exact WExt_refl W, by omega, .refl, fun _ _ hp => by cases hp⟩, ?_⟩
  intro p k W' h' t' U h'' t'' hI st hx _ hh
  obtain ⟨hk, j, hW, hjk, hst, hpend⟩ := hI
  have hW' : WExt (trunc k (by omega) W) U := by
    have := WExt_trans (WExt_trunc (Nat.le_succ k) hW) hx
    simpa only [trunc_trunc] using this
  have hst' := steps_snoc hst st
  obtain ⟨s', -, hsim⟩ := sim_reaches hst (sim_gotoOf P start L d comp)
  cases hsim with
  | goto =>
    rename_i l L' d' comp'
    cases st with
    | gotoEnter he hK =>
      rename_i e cont x
      refine ⟨by rcases p with _ | ⟨_, _⟩ <;> trivial, fun _ => ⟨by omega, j + 1, hW', by omega, hst', ?_⟩⟩
      intro l₂ h₂ hp
      simp only [framedPend, isFrame, Bool.true_and] at hp
      split at hp
      · cases hp
        exact ⟨_, L', d', cont, x, comp', e, j, k, by omega, U, 0, rfl, he, hst, by omega, hW',
          ‹_›, hh, .refl, by omega⟩
      · cases hp
  | frame =>
    rename_i u L' d' cont x comp'
    -- At a pending framed node, a returned value keeps the node's supports.
    have hR : ∀ l h₀, p = some (l, h₀) → isVal u = true →
        ∀ T ∈ (SinglePass.framedAt spec.framed l).getD [], Footprints.Supported T (envOf L' d') h₀ h' := by
      intro l h₀ hp hv
      obtain ⟨uw, Lw, dw, contw, xw, compw, e, j₀, k₁, hk₁, V₁, j₁, heq, he, hst₀, hj₀, hW₁, hU₁, hh₁,
        hinner, hkj⟩ := hpend l h₀ hp
      simp only [Tm.frame.injEq, true_and] at heq
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
      obtain ⟨s₀, hreach, hsim₀⟩ := sim_reaches hst₀ (sim_gotoOf P start L d comp)
      cases hsim₀ with
      | done hv' => simp [isVal] at hv'
      | goto => ?_
      rw [SourceElaboration.program_nodes] at hreach
      rw [List.getElem?_map] at he
      obtain ⟨node, hnode, rfl⟩ := Option.map_eq_some_iff.mp he
      exact hret j₀ h₀ l _ node hreach hnode k₁ hk₁ V₁ hj₀ hW₁ hU₁ hh₁ j₁ h' u (by omega) hinner hv
    -- A step leaving the frame meets the returns and leaves nothing pending.
    have hRet : ∀ t'', isFrame t'' = false →
        RetAt (fun l ρ h₁ h₂ => ∀ T ∈ (SinglePass.framedAt spec.framed l).getD [], Footprints.Supported T ρ h₁ h₂)
          (fun _ _ _ _ => True) p h'
          (.frame (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler)) u L' d' cont x comp') t'' := by
      intro t'' _
      rcases p with _ | ⟨l, h₀⟩
      · trivial
      · simp only [RetAt]
        by_cases hv : isVal u = true
        · exact .inr (.inl ⟨hv, hR l h₀ rfl hv⟩)
        · exact .inr (.inr ⟨by simpa using hv, trivial⟩)
    have hInv : ∀ t'', isFrame t'' = false → Steps (j + 1) h (gotoOf P start L d comp) h' t'' →
        ReachedFrames P start L d comp n W h
          (framedPend (fun l => (SinglePass.framedAt spec.framed l).isSome) p h'
            (.frame (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler)) u L' d' cont x comp') t'')
          k U h' t'' := by
      intro t'' hnf hs
      refine ⟨by omega, j + 1, hW', by omega, hs, fun l₂ h₂ hp => ?_⟩
      simp [framedPend, hnf] at hp
    cases st with
    | frameC st₁ =>
      refine ⟨?_, fun _ => ⟨by omega, j + 1, hW', by omega, hst', fun l₂ h₂ hp => ?_⟩⟩
      · rcases p with _ | ⟨_, _⟩
        · trivial
        · exact .inl rfl
      · simp only [framedPend, isFrame, ite_true] at hp
        obtain ⟨uw, Lw, dw, contw, xw, compw, e, j₀, k₁, hk₁, V₁, j₁, heq, he, hst₀, hj₀, hW₁, hU₁, hh₁,
          hinner, hkj⟩ := hpend l₂ h₂ hp
        simp only [Tm.frame.injEq, true_and] at heq
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
        exact ⟨_, _, _, _, _, _, e, j₀, k₁, hk₁, V₁, j₁ + 1, rfl, he, hst₀, hj₀, hW₁, hU₁, hh₁,
          steps_snoc hinner st₁, by omega⟩
    | frameRet hv => exact ⟨hRet _ (isFrame_of_isVal hv), fun _ => hInv _ (isFrame_of_isVal hv) hst'⟩
    | frameBind => exact ⟨hRet _ rfl, fun _ => hInv _ rfl hst'⟩
    | frameEffect => exact ⟨hRet _ rfl, fun _ => hInv _ rfl hst'⟩
    | frameYes => exact ⟨hRet _ rfl, fun _ => hInv _ rfl hst'⟩
    | frameNo => exact ⟨hRet _ rfl, fun _ => hInv _ rfl hst'⟩
    | frameYesBind => exact ⟨hRet _ rfl, fun _ => hInv _ rfl hst'⟩
    | frameNoBind => exact ⟨hRet _ rfl, fun _ => hInv _ rfl hst'⟩
    | frameTag => exact ⟨hRet _ rfl, fun _ => hInv _ rfl hst'⟩
    | frameHandle => exact ⟨hRet _ rfl, fun _ => hInv _ rfl hst'⟩
    | frameRaise => exact ⟨hRet _ rfl, fun _ => hInv _ rfl hst'⟩
  | done hv => exact absurd st (value_no_step hv)
  | raised hv hs => exact absurd st (raises_no_step (.throwV hv hs))

/-! ## A framed node's supports from the demand -/

/-- **A support entry projects within a demand**: `projectEntry` maps it to
a confined allocation, or to an entry `(r', δ')` some entry of `dem` names
with a change at most `δ'`, as `checkProducer` checks of every entry of a
framed node's supports. -/
def ProjectedIn (env : List SlotOrigin) (confined : List Nat) (dem : Footprints.Footprint)
    (e : Footprints.Region × Footprints.Change) : Prop :=
  projectEntry env confined e = .confined ∨
    ∃ r' δ', projectEntry env confined e = .demand (r', δ') ∧ ∃ d ∈ dem, d.1 = r' ∧ d.2.le δ' = true

/-- **What the producer check gives at a framed node** (proved): the origin
table is valid, and at each node `l` that `spec.framed` lists with supports
`Ss`, the node calls a slot holding a parameter `paramPos - 1` and every
entry of every support projects within that parameter's demand. -/
theorem checkProducer_framed {σ ι : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι}
    {spec : CallbackDemands.CallbackDemandSpec} (h : SourceClaimJson.CallbackDemandSpec.checkProducer r spec = true) :
    originsValid r.codes r.program r.start (requestInitOrigins r) (requestOrigins r) = true ∧
    ∀ l Ss, SinglePass.framedAt spec.framed l = some Ss →
      ∃ (node : Node) (env : List SlotOrigin) (paramPos fnSlot : Nat) (recv : Tm) (args : List Tm),
        r.program[l]? = some node ∧ (requestOrigins r)[l]?.join = some env ∧
        node.expression = .invoke (.var fnSlot) recv args ∧ originAt env fnSlot = .param (paramPos - 1) ∧
        ∀ S ∈ Ss, ∀ e ∈ S, ProjectedIn env spec.confined
          (((spec.demands.find? (·.param == paramPos)).map (·.support)).getD []) e := by
  simp only [SourceClaimJson.CallbackDemandSpec.checkProducer, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨horig, -⟩, hcalls⟩, -⟩ := h
  refine ⟨horig, fun l Ss hl => ?_⟩
  simp only [SinglePass.framedAt, Option.map_eq_some_iff] at hl
  obtain ⟨⟨l', Ss'⟩, hfind, rfl⟩ := hl
  have hl' : l' = l := by simpa using List.find?_some hfind
  subst hl'
  have hc := hcalls _ (List.mem_of_find?_eq_some hfind)
  simp only at hc
  split at hc
  · rename_i paramPos node env _ hP henv
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨hcall, hsup⟩ := hc
    split at hcall
    · rename_i fnSlot recv args hexpr
      simp only [Bool.and_eq_true, beq_iff_eq] at hcall
      refine ⟨node, env, paramPos, fnSlot, recv, args, hP, henv, hexpr, hcall.1, fun S hS e he => ?_⟩
      have hp := hsup S hS e he
      unfold ProjectedIn
      split at hp
      · rename_i hpe; exact .inl hpe
      · rename_i r' δ' hpe
        simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
        obtain ⟨d, hd, hd1, hle⟩ := hp
        exact .inr ⟨r', δ', hpe, d, hd, hd1, hle⟩
      · cases hp
    · cases hcall
  · cases hc

/-- **A framed node's supports are kept where the demand's are** (proved):
at a node whose slots meet their origins `env` in `h₁` (`EnvOriginHolds`,
relative to the entry's call environment `ρ₀`), with every path origin an
own-field read (`hown`) and the parameter paths reading the same at `h₁`
as at the entry heap `h₀` (`hagree`, `hcells`), every support `S` whose
entries project within the demand `dem` (`ProjectedIn`) is kept from `h₁`
to `h₂` (`Supported`) wherever `dem` is kept relative to the entry
(`SupportedAt`) and every location at or above `bOwn` (the allocations of
the run) is unchanged: a demanded entry's locations are the demand's
(`projectEntry_demand_mem`), a confined one's lie at or above `bOwn`
(`projectEntry_confined_ge`). -/
theorem supported_of_projected {ι : Type} {codes : List (RequestJson.CodeRequest ι)}
    {ρ₀ ρ : Env} {sibVal : String → Tm} {bOwn bCaller : Nat} {h₀ h₁ h₂ : Heap}
    {env : List SlotOrigin} {confined : List Nat} {dem S : Footprints.Footprint}
    (henv : EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h₁ env ρ)
    (hown : ∀ x p fs, originAt env x = .path p fs → HeapKnowledge.readPath h₁ (ρ₀ (p + 1)) fs = some (ρ x))
    (hagree : ∀ p fs, HeapKnowledge.readPath h₁ (ρ₀ (p + 1)) fs = HeapKnowledge.readPath h₀ (ρ₀ (p + 1)) fs)
    (hcells : ∀ p fs l,
      (((HeapKnowledge.readPath h₁ (ρ₀ (p + 1)) fs).map (Footprints.spineCells h₁)).getD []).contains (some l) = true →
      (((HeapKnowledge.readPath h₀ (ρ₀ (p + 1)) fs).map (Footprints.spineCells h₀)).getD []).contains (some l) = true)
    (hS : ∀ e ∈ S, ProjectedIn env confined dem e)
    (hdem : SupportedAt dem ρ₀ h₀ h₁ h₂)
    (hconf : ∀ l v, bOwn ≤ l → h₁[l]? = some v → h₂[l]? = some v) :
    Footprints.Supported S ρ h₁ h₂ := by
  intro e he l v hm hv
  obtain ⟨r, δ⟩ := e
  rcases hS (r, δ) he with hc | ⟨r', δ', hp, d, hd, hd1, hle⟩
  · exact ⟨v, hconf l v (projectEntry_confined_ge henv hc l hm) hv, Footprints.Change.Holds.refl _ _ _⟩
  · obtain ⟨rfl, hmem⟩ := projectEntry_demand_mem henv hown hagree hcells hp
    obtain ⟨v', hv', hch⟩ := hdem d hd l v (by rw [hd1]; exact hmem l hm) hv
    exact ⟨v', hv', hch.mono hle⟩

/-! ## The demanded row of a callback-demand member -/

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **A callback-demand request is module code at its demanded signature**
(proved): where a unit request is a code's (`UnitIsCode`) collecting no
rest and meeting the row conditions, its safety at every call meeting its
callback returns (`CallbackDemandRequestSafe`), with the framed returns at
its reached framed nodes from every entry whose callback arguments meet the
demands (`hret`), makes the code meet its signature as a demanded module
row (`DemandedRowSpec`, no demanded capture) at the request's entry
separation, at every assignment: at each such entry the returns give
`CallbackReturnsMet` (`callbackReturnsMet_of_reached`), and the request's
clauses there give the row's run (`rowRun_at`). -/
theorem demandedRowSpec_of_callbackDemand {r : SourceRequest σ ι} {spec : CallbackDemands.CallbackDemandSpec}
    {c : CodeEntry ι}
    (hsafe : CallbackDemandRequestSafe r spec) (hu : UnitIsCode r c) (hcond : rowConditions c = true)
    (hspine : c.spine = none)
    (hret : ∀ η n W h (L : List Tm),
      EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
        (envOf L .nul) n W h → RootsOk W (envOf L .nul) →
      ∀ rv args, FrameValues c.arity (none : Option (Ty ι)) L rv args →
      DemandsMet (reassign (RequestJson.graph r.toRequest) η) c.row spec.demands rv args h n W →
      FramedReturnsReached spec r.program r.start n W h (envOf L .nul)) :
    ∀ η, DemandedRowSpec (reassign (RequestJson.graph r.toRequest) η) c.arity c.exprs c.conts c.start
      c.captures (fun _ => []) c.row r.entrySeparation spec.demands := by
  intro η
  have hadm : r.Admits η := by simp [SourceRequest.Admits, hu.unqualified]
  have hprog : r.program = GraphCode.program c.exprs c.conts := by
    rw [hu.exprs, hu.conts, program_nodes]
  have hgoto : ∀ L d, gotoOf r.program r.start L d r.comp = .goto c.exprs c.conts c.start L d r.comp := by
    intro L d; simp only [gotoOf, hu.exprs, hu.conts, hu.start]
  have hcond' := hcond
  simp only [rowConditions, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hcond'
  obtain ⟨⟨⟨harity, hrow⟩, _⟩, _⟩ := hcond'
  refine ⟨harity, hrow, ?_⟩
  intro n W heap L comp he hw hh hgo hvalues hpre hsep rv args hframe hdem
  have hnil : frameDem c.arity (fun _ => []) = fun _ => [] := by
    funext i; unfold frameDem; split <;> rfl
  rw [hnil, demandedEnvOk_nil_iff] at he
  have he' : EnvOk (reassign (RequestJson.graph r.toRequest) η) (codeFrame c.arity c.row c.captures c.spine)
      (envOf L .nul) n W := by
    rw [hspine]; exact he
  have hpre' : PreAt c.row.effect c.spine L heap := by rw [hspine]; exact hpre
  have hentry : EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation
      r.entryIndices (envOf L .nul) n W heap := by
    rw [hu.inputs, hu.indices]
    exact ⟨he', hsep, GraphCode.codeEntryIndices_holds hpre', hw, hh⟩
  have hroots : RootsOk W (envOf L .nul) := (GraphCode.goto_refs hgo).2
  have hmet : CallbackReturnsMet spec n W heap (gotoOf r.program r.start L .nul r.comp) :=
    callbackReturnsMet_of_reached (hret η n W heap L hentry hroots rv args hframe hdem)
  refine rowRun_at hcond hspine ?_ ?_ ?_ hw hh hgo hvalues hframe
  · intro _ hρ
    have := hsafe.1 η hadm n W heap L .nul hentry hρ hmet
    rw [hprog, hu.goal, hu.start] at this
    exact this
  · intro Φ Ψ fresh hb _
    rw [← hu.goal]
    exact requestBound_at hu.bound hgoto
      (fun hbd => hsafe.2.1 hbd η n W heap L .nul hentry hroots hvalues rfl hmet) Φ Ψ fresh hb
  · intro hne _
    have := hsafe.2.2.1 (by rw [hu.ensures]; exact hne) η n W heap L .nul hentry hroots hmet
    rw [hgoto, hu.goal, hu.ensures] at this
    exact (HeapObservations.SafePostW.goto_comp_iff r.comp none).mp this

end

/-- **An accepted callback-demand member is module code at its demanded
signature** (proved, under `RunSound` and `RunKeepsSummaries`, zero client
trust `Θ_C`): the accepted plan's request is safe at every call meeting its
callback returns (`callbackDemand_requestSafe`), so where it is a code's
(`UnitIsCode`) collecting no rest and meeting the row conditions, and the
framed returns hold at its reached framed nodes from every entry whose
callback arguments meet the demands (`hret`), the code meets its signature
as a demanded module row (`DemandedRowSpec`) at every assignment. -/
theorem callbackDemand_rowSpec {f : FilePlans} {r : Req f} {spec : CallbackDemands.CallbackDemandSpec} {c}
    (hrun : RunSound (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (hkeep : RunKeepsSummaries (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (htypes : r.types = f.F.store) (hacc : CallbackDemandsAccepted f r spec)
    (hu : UnitIsCode r c) (hcond : rowConditions c = true) (hspine : c.spine = none)
    (hret : ∀ η n W h (L : List Tm),
      EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
        (envOf L .nul) n W h → RootsOk W (envOf L .nul) →
      ∀ rv args, FrameValues c.arity (none : Option (Ty (EquationStore.CheckedLabel f.F.equations f.F.primitive)))
        L rv args →
      DemandsMet (reassign (RequestJson.graph r.toRequest) η) c.row spec.demands rv args h n W →
      FramedReturnsReached spec r.program r.start n W h (envOf L .nul)) :
    ∀ η, DemandedRowSpec (reassign (RequestJson.graph r.toRequest) η) c.arity c.exprs c.conts c.start
      c.captures (fun _ => []) c.row r.entrySeparation spec.demands :=
  demandedRowSpec_of_callbackDemand (callbackDemand_requestSafe hrun hkeep htypes hacc) hu hcond hspine hret

end Verification.SourceClaimJson.PassUnit
