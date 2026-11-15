import Verification.Semantics.CommandComposition

/-! # The summary of a loop

The note *Tolerant frames*, §6, the rule Loop,

    {I ∧ □_Φ R} c {I}    c : Φ    Φ rigid
    ──────────────────────────────────────── (Loop)
    {I ∧ □_Φ R} loop c {I ∧ □_Φ R}

over summaries. A loop runs zero or more normal iterations of its body
(`Iterates`), each from the state and valuation the last leaves, and then
departs (`Runs.loop`): a departure is a run of the body that leaves the
loop, by its normal exit (a false guard, a `break`) or by a throw.

**The loop's prefix summary** `L` (`LoopEvidence`) bounds, from the loop's
entry, every iteration head: it holds of no iteration, and it is closed
under another traversal, `L` followed by the iteration's summary `q` within
`L` (`ThenEvidence.Into`): with `q`'s frame `Φ` that is `Φ ∪ rebase(Φ) ⊑ Φ`.
Then `L` holds at every head (`LoopEvidence.prefix_sound`), and the loop's
summary is `L` followed by the departures' (`LoopEvidence.loop_sound`).

**The frame `□_Φ R`** is read at the loop's entry valuation, which the
note's side condition (neither `R` nor `Φ` mentions a loop-carried
variable) makes the valuation of every iteration. Where `Φ` is rigid as a
whole on a domain (`RigidOnDomain`, the evidence of `RigidityEvidence`),
`□_Φ R` at the entry gives `□_Φ R` and `R` at every state the entry reaches
by an action of `Φ` (`box_of_rigid`): at every head and every exit whose
frame is within `Φ` (`LoopEvidence.frame_at_exit`), and at every interior
point reached by a prefix whose composed frame is within `Φ`
(`reliance_at_prefix`); the iteration's exit bound alone gives no bound
inside it. -/
namespace Verification.CallEffects
open Verification Footprints HeapKnowledge TolerantFrames Parity

/-- **Zero or more normal iterations**, each from the state and valuation
the previous one leaves. -/
inductive Iterates (iter : TwoState → Prop) : TwoState → Prop
  | zero (η : Env) (m : Nat) (s : IndexedHeap) : Iterates iter ⟨η, η, m, s, s⟩
  | step {ρ₀ η ρ₂ : Env} {m : Nat} {t₀ t₁ t₂ : IndexedHeap} :
      Iterates iter ⟨ρ₀, η, m, t₀, t₁⟩ → iter ⟨η, ρ₂, m, t₁, t₂⟩ → Iterates iter ⟨ρ₀, ρ₂, m, t₀, t₂⟩

/-- **The runs of a loop**: iterations by `iter`, then a departure by `D`
completing by `c`. -/
def Runs.loop (iter : TwoState → Prop) (D : Runs) : Runs := fun c s =>
  ∃ η t, Iterates iter ⟨s.beforeEnv, η, s.mark, s.before, t⟩ ∧ D c ⟨η, s.afterEnv, s.mark, t, s.after⟩

/-- **The evidence of a loop's prefix summary** `L`, the iteration's
summary `q` and the head condition `I`, from the entry condition `P`: `L`'s
postconditions hold of no iteration; `I` holds at every head `L` bounds;
and `L` followed by `q` is within `L`. -/
structure LoopEvidence (arena : AssertionArena) (P I : Assertion) (L q : ExitSpec) (ev : ThenEvidence) : Prop where
  base : ∀ η m st, P η m st → ∀ F ∈ L.ensures, Parity.Holds arena ⟨η, η, m, st, st⟩ F
  head : ∀ s, s.Entry P → L.Holds arena s → I s.afterEnv s.mark s.after
  valid : ev.Valid arena P L q
  closed : ev.Into arena L q L

/-- **The prefix summary holds at every iteration head** (the note, §6,
Loop: induction on normal iterations). -/
theorem LoopEvidence.prefix_sound {arena : AssertionArena} {P I : Assertion} {L q : ExitSpec} {ev : ThenEvidence}
    {iter : TwoState → Prop} (hl : LoopEvidence arena P I L q ev)
    (hq : ∀ s, s.Entry I → iter s → q.Holds arena s) :
    ∀ s, s.Entry P → Iterates iter s → L.Holds arena s := by
  intro s hP hi
  induction hi with
  | zero η m st => exact ⟨EffectAction.refl _ _ _, hl.base η m st hP⟩
  | @step ρ₀ η ρ₂ m t₀ t₁ t₂ _ hit ih =>
    have hL := ih hP
    have hI := hl.head ⟨ρ₀, η, m, t₀, t₁⟩ hP hL
    exact ev.sound hl.valid hl.closed hP hL (hq ⟨η, ρ₂, m, t₁, t₂⟩ hI hit)

/-- **The summary of a loop**: the prefix summary followed by the
departures' summary, at each exit. -/
theorem LoopEvidence.loop_sound {arena : AssertionArena} {P I : Assertion} {L q : ExitSpec} {ev : ThenEvidence}
    {iter : TwoState → Prop} {D : Runs} {B C : CommandSummary} {evd : Completion → ThenEvidence}
    (hl : LoopEvidence arena P I L q ev) (hq : ∀ s, s.Entry I → iter s → q.Holds arena s)
    (hB : B.Sound arena I D) (hd : ∀ c, (evd c).Valid arena P L (B.get c))
    (hdi : ∀ c, (evd c).Into arena L (B.get c) (C.get c)) : C.Sound arena P (Runs.loop iter D) := by
  rintro c ⟨ρ₀, ρ₂, m, t₀, t₂⟩ hP ⟨η, t₁, hi, hr⟩
  have hL := hl.prefix_sound hq ⟨ρ₀, η, m, t₀, t₁⟩ hP hi
  have hI := hl.head ⟨ρ₀, η, m, t₀, t₁⟩ hP hL
  exact (evd c).sound (hd c) (hdi c) hP hL (hB c ⟨η, ρ₂, m, t₁, t₂⟩ hI hr)

/-! ## The frame across iterations -/

/-- **A box of a rigid effect survives an action of it** (the note, §3,
"rigid", and §5, law (e)): on the domain `D`, `□_Φ R` at `s₀` and an action
of `Φ` from `s₀` to `s` give `□_Φ R` and `R` at `s`. -/
theorem box_of_rigid {arena : AssertionArena} {D : AssertionRef} {Φ : Footprint} {R : Assertion} {ρ : Env}
    {m : Nat} {s₀ s : IndexedHeap} (hr : RigidOnDomain arena D Φ) (hD : Sat arena ρ m s₀ D)
    (hb : Box Φ R ρ m s₀) (ha : EffectAction Φ ρ s₀ s) : Box Φ R ρ m s ∧ R ρ m s :=
  ⟨fun s' ha' => hb s' (hr ρ m s₀ s s' hD ha ha').2, hb s ha⟩

/-- **The frame at every iteration head**: `□_Φ R` at the loop's entry, with
`Φ` the prefix summary's frame rigid on a domain the entry meets, holds,
with `R`, at every head, read at the entry's valuation. -/
theorem LoopEvidence.frame_at_head {arena : AssertionArena} {P I : Assertion} {L q : ExitSpec} {ev : ThenEvidence}
    {iter : TwoState → Prop} {D : AssertionRef} {R : Assertion} (hl : LoopEvidence arena P I L q ev)
    (hq : ∀ s, s.Entry I → iter s → q.Holds arena s) (hr : RigidOnDomain arena D L.frame)
    (hPD : ∀ η m st, P η m st → Sat arena η m st D ∧ Box L.frame R η m st) :
    ∀ s, s.Entry P → Iterates iter s → Box L.frame R s.beforeEnv s.mark s.after ∧ R s.beforeEnv s.mark s.after := by
  intro s hP hi
  obtain ⟨hD, hb⟩ := hPD _ _ _ hP
  exact box_of_rigid hr hD hb (hl.prefix_sound hq s hP hi).1

/-- **The Loop rule's conclusion `□_Φ R` at the loop's exits** (the note,
§6, Loop): a sound loop summary whose exit frames are within the rigid `Φ`
from the entry gives `□_Φ R` and `R` at every exit, read at the entry's
valuation. -/
theorem frame_at_exit {arena : AssertionArena} {P : Assertion} {Rn : Runs} {C : CommandSummary} {Φ : Footprint}
    {D : AssertionRef} {R : Assertion} {cl : ClassEvidence} (hC : C.Sound arena P Rn)
    (hr : RigidOnDomain arena D Φ) (hPD : ∀ η m st, P η m st → Sat arena η m st D ∧ Box Φ R η m st)
    (hcl : ∀ η m st, P η m st → ClassOk cl η st.h) (hle : ∀ c, Footprint.le cl (C.get c).frame Φ = true) :
    ∀ c s, s.Entry P → Rn c s → Box Φ R s.beforeEnv s.mark s.after ∧ R s.beforeEnv s.mark s.after := by
  intro c s hP hrn
  obtain ⟨hD, hb⟩ := hPD _ _ _ hP
  exact box_of_rigid hr hD hb (action_le (hle c) (hcl _ _ _ hP) (hC c s hP hrn).1)

/-- **Reliance inside an iteration** (the note, §6, Loop: "the body may use
`R` at a point where the transition from the iteration's entry to that
point is bounded by `Φ`"): an exit specification from the loop's entry to a
point, whose frame is within `Φ`, gives `R` there from `□_Φ R` at the
entry. -/
theorem reliance_at_prefix {arena : AssertionArena} {q : ExitSpec} {Φ : Footprint} {R : Assertion}
    {cl : ClassEvidence} {ρ η : Env} {m : Nat} {s₀ t : IndexedHeap} (hb : Box Φ R ρ m s₀)
    (hq : q.Holds arena ⟨ρ, η, m, s₀, t⟩) (hle : Footprint.le cl q.frame Φ = true) (hcl : ClassOk cl ρ s₀.h) :
    R ρ m t :=
  hb t (action_le hle hcl hq.1)

end Verification.CallEffects
