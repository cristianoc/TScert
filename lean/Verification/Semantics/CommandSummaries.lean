import Verification.Semantics.ExitSummaries

/-! # Command summaries

The effect of a command (the note *Tolerant frames*, §3, "The effect of a
command", the judgment $c:\Phi\mid\Phi^{e}$, and §6, the rules Entry and
Frame): for each exit, normal and exceptional, a frame read at the
command's entry and two-state postconditions relating its entry to that
exit (`CommandSummary`, an `Exits ExitSpec`). A command is given by its
runs (`Runs`): `R c s` states that the command, run from `s.before` with
the valuation `s.beforeEnv`, completes by `c` in `s.after` with the
valuation `s.afterEnv`, within the invocation of entry mark `s.mark`. The
reduction those runs come from is deterministic and unchanged here; a
summary is sound for a command from an entry condition `P` when every run
from a state meeting `P` meets the summary at its exit
(`CommandSummary.Sound`).

A postcondition that holds at one two-state is carried to another by what
it reads: a formula reading one phase alone (`Formula.reads`) holds alike at
two-states agreeing on that phase (`holds_reads`), and one reading a
command's exit alone holds, entry and exit exchanged, at the entry of the
command that follows (`holds_carry`). Consequences are the derivation
checker's (`Consequence`, `checkConsequences_sound`), and an exit
specification is weakened by checked frame inclusion and checked
consequence (`ExitSpec.weakenCheck_sound`). -/
namespace Verification.CallEffects
open Verification Footprints HeapKnowledge TolerantFrames Parity

/-! ## Summaries and their meaning -/

/-- **The summary of a command** (the note, §3, the judgment
$c:\Phi\mid\Phi^{e}$, with the postconditions of §6): for each exit a frame,
read at the command's entry, and postconditions relating the entry to the
exit. -/
abbrev CommandSummary := Exits ExitSpec

/-- **The runs of a command**: `R c s` when the command, run from the entry
state and valuation of `s`, completes by `c` in its exit state and
valuation, within the invocation of mark `s.mark`. -/
abbrev Runs := Completion → TwoState → Prop

/-- **The meaning of a summary at an exit**: that exit's specification holds
of the two-state from the command's entry to the exit. -/
def CommandSummary.Holds (arena : AssertionArena) (S : CommandSummary) (c : Completion) (s : TwoState) : Prop :=
  (S.get c).Holds arena s

/-- The entry of a two-state meets an entry condition. -/
def _root_.Verification.Parity.TwoState.Entry (P : Assertion) (s : TwoState) : Prop := P s.beforeEnv s.mark s.before

/-- **A summary is sound for a command from an entry condition**: every run
from a state meeting `P` meets the summary at the exit it completes by. -/
def CommandSummary.Sound (arena : AssertionArena) (P : Assertion) (R : Runs) (S : CommandSummary) : Prop :=
  ∀ c s, s.Entry P → R c s → S.Holds arena c s

/-! ## An exit specification as formulas -/

/-- The formulas an exit specification states: the transition within its
frame (the note's `tr_Φ`, §6, Entry) and its postconditions. -/
def ExitSpec.facts (q : ExitSpec) : List Formula := .transition q.frame :: q.ensures

/-- **An exit specification holds where its formulas do.** -/
theorem ExitSpec.holds_iff_facts {arena : AssertionArena} {q : ExitSpec} {s : TwoState} :
    q.Holds arena s ↔ ∀ F ∈ q.facts, Parity.Holds arena s F := by
  simp only [ExitSpec.Holds, ExitSpec.facts, List.forall_mem_cons, Parity.Holds]

/-! ## Checked consequence -/

/-- **Consequence**: at every two-state where the premises hold, the goals
hold. -/
def Consequence (arena : AssertionArena) (Γ goals : List Formula) : Prop :=
  ∀ s, (∀ F ∈ Γ, Parity.Holds arena s F) → ∀ G ∈ goals, Parity.Holds arena s G

/-- **The derivation checker on a list of goals**: each goal with its raw
derivation from the premises (`checkDerivation`). -/
def checkConsequences (arena : AssertionArena) (Γ : List Formula) : List Formula → List RawDerivation → Bool
  | [], [] => true
  | G :: gs, r :: rs =>
    (match checkDerivation arena Γ G r with
      | .ok _ => true
      | .error _ => false) && checkConsequences arena Γ gs rs
  | _, _ => false

/-- **Checked consequences are consequences** (`checkDerivation_sound`). -/
theorem checkConsequences_sound {arena : AssertionArena} (hv : arena.Valid) {Γ : List Formula} :
    ∀ {goals : List Formula} {raws : List RawDerivation}, checkConsequences arena Γ goals raws = true →
      Consequence arena Γ goals
  | [], [], _ => fun _ _ _ hG => by cases hG
  | G :: gs, r :: rs, h => by
    simp only [checkConsequences, Bool.and_eq_true] at h
    obtain ⟨hd, hr⟩ := h
    intro s hΓ G' hG'
    rcases List.mem_cons.mp hG' with rfl | hG'
    · split at hd
      · rename_i d hc
        exact checkDerivation_sound hv hc s hΓ
      · cases hd
    · exact checkConsequences_sound hv hr s hΓ G' hG'
  | [], _ :: _, h => by simp [checkConsequences] at h
  | _ :: _, [], h => by simp [checkConsequences] at h

theorem Consequence.nil (arena : AssertionArena) (Γ : List Formula) : Consequence arena Γ [] :=
  fun _ _ _ hG => by cases hG

/-- Each premise is a consequence. -/
theorem Consequence.refl (arena : AssertionArena) (Γ : List Formula) : Consequence arena Γ Γ :=
  fun _ hΓ G hG => hΓ G hG

/-- More premises keep a consequence. -/
theorem Consequence.mono {arena : AssertionArena} {Γ Γ' goals : List Formula} (hsub : ∀ F ∈ Γ, F ∈ Γ')
    (h : Consequence arena Γ goals) : Consequence arena Γ' goals :=
  fun s hΓ => h s fun F hF => hΓ F (hsub F hF)

/-- Consequences of consequences. -/
theorem Consequence.trans {arena : AssertionArena} {Γ Δ goals : List Formula} (h₁ : Consequence arena Γ Δ)
    (h₂ : Consequence arena Δ goals) : Consequence arena Γ goals :=
  fun s hΓ => h₂ s (h₁ s hΓ)

/-! ## Formulas reading one phase -/

/-- The phase a two-state variable reads. -/
def stepPhase : StepVar → Phase
  | .before _ => .before
  | .after _ => .after

/-- **A formula reading one phase alone**: an assertion at that phase, a
linear fact or definedness over that phase's terms, and their connectives. -/
def _root_.Verification.Parity.Formula.reads (p : Phase) : Formula → Bool
  | .at q _ => q == p
  | .linear F => F.vars.all fun v => stepPhase v == p
  | .defined v => stepPhase v == p
  | .and F G => F.reads p && G.reads p
  | .truth | .falsity => true
  | _ => false

private theorem stepValue_congr {p : Phase} {s s' : TwoState} (he : s.env p = s'.env p)
    (hst : s.state p = s'.state p) {v : StepVar} (hv : stepPhase v = p) : stepValue s v = stepValue s' v := by
  cases v <;> cases p <;> simp only [stepPhase, reduceCtorEq] at hv
  · simp only [TwoState.env] at he; simp only [TwoState.state] at hst
    simp only [stepValue, he, hst]
  · simp only [TwoState.env] at he; simp only [TwoState.state] at hst
    simp only [stepValue, he, hst]

/-- **A formula reading one phase holds alike at two-states agreeing on
that phase and the mark.** -/
theorem holds_reads {arena : AssertionArena} {p : Phase} {s s' : TwoState} (he : s.env p = s'.env p)
    (hst : s.state p = s'.state p) (hm : s.mark = s'.mark) :
    ∀ {F : Formula}, F.reads p = true → (Parity.Holds arena s F ↔ Parity.Holds arena s' F)
  | .at q a, h => by
    simp only [Formula.reads, beq_iff_eq] at h
    subst h
    simp only [Parity.Holds, he, hst, hm]
  | .linear F, h => by
    simp only [Formula.reads, List.all_eq_true, beq_iff_eq] at h
    have hv : ∀ v ∈ F.vars, stepValue s v = stepValue s' v := fun v hv => stepValue_congr he hst (h v hv)
    simp only [Parity.Holds, FactAt]
    constructor
    · rintro ⟨hd, hF⟩
      refine ⟨fun v hm' => by rw [← hv v hm']; exact hd v hm', ?_⟩
      exact (Linear.Fact.holds_congr fun v hm' => by rw [hv v hm']).mp hF
    · rintro ⟨hd, hF⟩
      refine ⟨fun v hm' => by rw [hv v hm']; exact hd v hm', ?_⟩
      exact (Linear.Fact.holds_congr fun v hm' => by rw [hv v hm']).mpr hF
  | .defined v, h => by
    simp only [Formula.reads, beq_iff_eq] at h
    simp only [Parity.Holds, stepValue_congr he hst h]
  | .and F G, h => by
    simp only [Formula.reads, Bool.and_eq_true] at h
    simp only [Parity.Holds, holds_reads he hst hm h.1, holds_reads he hst hm h.2]
  | .truth, _ => Iff.rfl
  | .falsity, _ => Iff.rfl
  | .transition _, h | .operation _, h | .transport _, h => by simp [Formula.reads] at h

/-- A formula reading one phase reads the two states symmetrically. -/
theorem _root_.Verification.Parity.Formula.reads_swappable {p : Phase} {F : Formula} (h : F.reads p = true) :
    F.swappable = true := by
  induction F with
  | «at» _ _ | linear _ | defined _ | truth | falsity => rfl
  | and F G ihF ihG =>
    simp only [Formula.reads, Bool.and_eq_true] at h
    simp only [Formula.swappable, ihF h.1, ihG h.2, Bool.and_self]
  | transition _ | operation _ | transport _ => simp [Formula.reads] at h

/-- **A formula reading a command's exit holds, entry and exit exchanged, at
the entry of the command that follows**: the first two-state's exit is the
second's entry. -/
theorem holds_carry {arena : AssertionArena} {s₁ s₂ : TwoState} (he : s₁.afterEnv = s₂.beforeEnv)
    (hst : s₁.after = s₂.before) (hm : s₁.mark = s₂.mark) {F : Formula} (hF : F.reads .after = true)
    (h : Parity.Holds arena s₁ F) : Parity.Holds arena s₂ F.swap := by
  let t : TwoState := ⟨s₂.afterEnv, s₂.beforeEnv, s₂.mark, s₂.after, s₂.before⟩
  have hsw : t.swap = s₂ := rfl
  rw [← hsw, holds_swap (Formula.reads_swappable hF)]
  exact (holds_reads (p := .after) (s := s₁) (s' := t) he hst hm hF).mp h

/-! ## Weakening an exit specification -/

/-- **An exit specification within another from an entry condition**: at
every two-state whose entry meets `P`, the first's holding gives the
second's. -/
def ExitSpec.Weakens (arena : AssertionArena) (P : Assertion) (q q' : ExitSpec) : Prop :=
  ∀ s, s.Entry P → q.Holds arena s → q'.Holds arena s

/-- **The weakening check**: the frame is within the weaker frame by checked
inclusion, and each weaker postcondition is a checked consequence of the
stronger specification's formulas. -/
def ExitSpec.weakenCheck (arena : AssertionArena) (cl : ClassEvidence) (raws : List RawDerivation)
    (q q' : ExitSpec) : Bool :=
  Footprint.le cl q.frame q'.frame && checkConsequences arena q.facts q'.ensures raws

/-- **The weakening rule**: frame inclusion, from an entry where its class
evidence holds, and consequence give the weaker specification. -/
theorem ExitSpec.weakens_of {arena : AssertionArena} {P : Assertion} {cl : ClassEvidence} {q q' : ExitSpec}
    (hcl : ∀ η m st, P η m st → ClassOk cl η st.h) (hle : Footprint.le cl q.frame q'.frame = true)
    (hq : Consequence arena q.facts q'.ensures) : q.Weakens arena P q' := by
  intro s hP h
  have hf := ExitSpec.holds_iff_facts.mp h
  exact ⟨action_le hle (hcl _ _ _ hP) h.1, hq s hf⟩

/-- **The weakening check is sound.** -/
theorem ExitSpec.weakenCheck_sound {arena : AssertionArena} (hv : arena.Valid) {P : Assertion}
    {cl : ClassEvidence} {raws : List RawDerivation} {q q' : ExitSpec}
    (hcl : ∀ η m st, P η m st → ClassOk cl η st.h) (h : q.weakenCheck arena cl raws q' = true) :
    q.Weakens arena P q' := by
  simp only [ExitSpec.weakenCheck, Bool.and_eq_true] at h
  exact ExitSpec.weakens_of hcl h.1 (checkConsequences_sound hv h.2)

/-- **A summary weakened at each exit stays sound.** -/
theorem CommandSummary.Sound.weaken {arena : AssertionArena} {P : Assertion} {R : Runs} {S S' : CommandSummary}
    (hS : S.Sound arena P R) (hw : ∀ c, (S.get c).Weakens arena P (S'.get c)) : S'.Sound arena P R :=
  fun c s hP hr => hw c s hP (hS c s hP hr)

/-- A stronger entry condition keeps a summary sound. -/
theorem CommandSummary.Sound.entry {arena : AssertionArena} {P P' : Assertion} {R : Runs} {S : CommandSummary}
    (hS : S.Sound arena P R) (hP : ∀ η m st, P' η m st → P η m st) : S.Sound arena P' R :=
  fun c s hP' hr => hS c s (hP _ _ _ hP') hr

/-! ## Footprint inclusion -/

theorem _root_.Verification.Footprints.Change.le_refl (c : Change) : c.le c = true := by
  cases c <;> rfl

theorem _root_.Verification.Footprints.Region.sub_refl (cl : ClassEvidence) (r : Region) : Region.sub cl r r = true := by
  cases r <;> simp [Region.sub, Region.subBase]

theorem _root_.Verification.Footprints.Footprint.le_of_subset {cl : ClassEvidence} {Φ Ψ : Footprint} (h : ∀ e ∈ Φ, e ∈ Ψ) :
    Footprint.le cl Φ Ψ = true :=
  List.all_eq_true.mpr fun e he => List.any_eq_true.mpr
    ⟨e, h e he, by simp [Change.le_refl, Region.sub_refl]⟩

theorem _root_.Verification.Footprints.Footprint.le_refl (cl : ClassEvidence) (Φ : Footprint) : Footprint.le cl Φ Φ = true :=
  Footprint.le_of_subset fun _ h => h

theorem _root_.Verification.Footprints.Footprint.le_append_left (cl : ClassEvidence) (Φ Ψ : Footprint) : Footprint.le cl Φ (Φ ++ Ψ) = true :=
  Footprint.le_of_subset fun _ h => List.mem_append_left _ h

theorem _root_.Verification.Footprints.Footprint.le_append_right (cl : ClassEvidence) (Φ Ψ : Footprint) : Footprint.le cl Ψ (Φ ++ Ψ) = true :=
  Footprint.le_of_subset fun _ h => List.mem_append_right _ h

end Verification.CallEffects
