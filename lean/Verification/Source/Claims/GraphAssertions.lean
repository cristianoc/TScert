import Verification.Source.Claims.PassUnit

/-! # Assertions along the run of a graph

The term that runs a graph (`gotoOf`) and the graph machine take the same
paths (`GraphCode.sim_step`, `GraphCode.sim_step_back`), so an assertion
stated at a label holds at every reached graph state there exactly where it
holds at every state of the term's run at a `goto` of that label
(`asserted_of_reach`, `assertedAt_of_graph`). -/
namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore
open HeapObservations

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

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **An assertion read at a graph state reached** (proved): the term that
runs the graph reaches a `goto` at the label, at whose frame `J` gives it. -/
theorem asserted_of_reach {P : Program} {assertions : List (Nat × HeapKnowledge.Knowledge)} {ρ : Env}
    {h : Heap} {n : Nat} {start : Nat} {L : List Tm} {d : Tm} {c : ComponentTag}
    (hJ : ∀ {j : Nat} {h' : Heap} {t' : Tm}, j < n → HeapObservations.Steps j h (gotoOf P start L d c) h' t' →
      AssertedAt P assertions ρ h h' t')
    {l : Nat} {k : HeapKnowledge.Knowledge} (hl : (l, k) ∈ assertions) {j : Nat} {h' : Heap} {ρ' : Env}
    (hj : j < n) (hr : ReachesIn P j h (.at start (envOf L d)) h' (.at l ρ')) :
    HeapKnowledge.Holds k ⟨ρ, h⟩ ρ' h' := by
  rw [← SourceElaboration.program_nodes P] at hr
  obtain ⟨ts', hst, hs'⟩ := reaches_sim hr (sim_gotoOf P start L d c)
  cases hs' with
  | goto => exact hJ hj hst l k hl _ _ _ rfl

/-- **A path of the term that runs a graph is a graph path** (proved, by
`GraphCode.sim_step_back`). -/
theorem sim_reaches {E : List Tm} {K : List (Continuation × Option Target)} :
    ∀ {j : Nat} {h : Heap} {ts : Tm} {h' : Heap} {ts' : Tm},
      HeapObservations.Steps j h ts h' ts' → ∀ {s : State}, GraphCode.Sim E K ts s →
      ∃ s', ReachesIn (GraphCode.program E K) j h s h' s' ∧ GraphCode.Sim E K ts' s'
  | _, _, _, _, _, .refl, _, hs => ⟨_, .refl, hs⟩
  | _, _, _, _, _, .next st hrest, _, hs => by
    obtain ⟨s₁, tr, hs₁⟩ := GraphCode.sim_step_back hs st
    obtain ⟨s', hr, hs'⟩ := sim_reaches hrest hs₁
    exact ⟨s', .step tr hr, hs'⟩

/-- **An assertion at every state reached, from the graph's** (proved; the
draft, `assertedAt_of_graph`, the converse of `asserted_of_reach`): where
each stated assertion holds at every graph state reached at its label
within the budget, it holds at every state the term that runs the graph
reaches at a `goto` at its label. -/
theorem assertedAt_of_graph {P : Program} {assertions : List (Nat × HeapKnowledge.Knowledge)} {ρ : Env}
    {h : Heap} {n : Nat} {start : Nat} {L : List Tm} {d : Tm} {c : ComponentTag}
    (hg : ∀ l k, (l, k) ∈ assertions → ∀ j h' ρ', j < n →
      ReachesIn P j h (.at start (envOf L d)) h' (.at l ρ') → HeapKnowledge.Holds k ⟨ρ, h⟩ ρ' h') :
    ∀ {j : Nat} {h' : Heap} {t' : Tm}, j < n → HeapObservations.Steps j h (gotoOf P start L d c) h' t' →
      AssertedAt P assertions ρ h h' t' := by
  intro j h' t' hj hst l k hl L' d' c' ht
  subst ht
  obtain ⟨s', hr, hs'⟩ := sim_reaches hst (sim_gotoOf P start L d c)
  cases hs' with
  | goto =>
    rw [SourceElaboration.program_nodes P] at hr
    exact hg l k hl j h' _ hj hr
  | done hv => simp [gotoOf, isVal] at hv

end

end Verification.SourceClaimJson.PassUnit
