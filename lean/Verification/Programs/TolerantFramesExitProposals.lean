import Verification.Source.Lowering.ExitProposals
import Verification.Semantics.CommandComposition
import Verification.Semantics.CommandLoops

/-! # Proposed exit summaries: soundness for runs

The rules composing the front's class-level summaries
(`Source/Lowering/ExitProposals.lean`) are the class instances of the note's
rules over command summaries (`Semantics/CommandSummaries.lean`,
`Semantics/CommandComposition.lean`, `Semantics/CommandLoops.lean`):

- one exit followed by another, at the class level, is Seq-Eff
  (`ClassSummary.then_into`, `ThenEvidence.Into`);
- entailment between summaries is weakening at each exit
  (`ClassSummary.within_weakens`, `ExitSpec.Weakens`);
- **each rule is sound for runs**: a summary is sound for a command's runs
  (`ClassSummary.Sound`) where every run completes by an exit it reaches,
  within that exit's bound; sequence (`seq_sound`), choice
  (`choice_sound`), the walk's step (`extend_sound`), a handler
  (`handle_sound`), a finalizer (`finally_sound`), an async body
  (`settle_sound`), a loop with rigid class entries (`loop_sound`) keep it,
  and a sound summary is a sound command summary (`sound_spec`).

The walk's invariant, which no theorem states: after walking part of a body
from a summary sound for the runs reaching it, the walk's summary is sound
for the union of the runs of the prefixes walked (each operation by
`extend_sound`; a handler entered from both exits of its body, an
over-approximation `handle_sound` covers; a loop body walked once or more
and closed by `close`, `within_close`). -/
namespace Verification.SourceExtraction
open Verification Footprints CallEffects Parity

namespace ClassSummary

/-- **One exit followed by another, at the class level, is Seq-Eff**
(`ThenEvidence.Into`): for any rebasing and class evidence, a first exit of
frame `a.fp` followed by a later exit of frame `b.fp` is within the exit of
frame `(a.join b).fp` (no postcondition). -/
theorem then_into (arena : AssertionArena) (ev : ThenEvidence) (a b : Closed) :
    ev.Into arena ⟨a.fp, []⟩ ⟨b.fp, []⟩ ⟨(a.join b).fp, []⟩ :=
  ⟨by simpa [rebaseAll_fp] using (fp_join_covers a b).le ev.cl, Consequence.nil _ _⟩

/-- **Entailment is weakening at each exit** (proved; `ExitSpec.Weakens`): at
each exit the first summary reaches, the second reaches it too, and the
first's exit specification weakens to the second's from any entry. -/
theorem within_weakens {A B : ClassSummary} (h : A.within B = true) (arena : AssertionArena) (P : TolerantFrames.Assertion)
    (c : Completion) {k : Closed} (hk : A.get c = some k) :
    ∃ k', B.get c = some k' ∧ ExitSpec.Weakens arena P ⟨k.fp, []⟩ ⟨k'.fp, []⟩ := by
  have he : exitWithin (A.get c) (B.get c) = true := by
    simp only [within, Bool.and_eq_true] at h
    cases c
    · exact h.1
    · exact h.2
  rw [hk] at he
  cases hb : B.get c with
  | none => rw [hb] at he; cases he
  | some k' =>
    rw [hb] at he
    refine ⟨k', rfl, fun s _ hs => ⟨⟨hs.1.1, Closed.post_mono he hs.1.2⟩, fun _ hF => nomatch hF⟩⟩
/-! ## Soundness of a summary for runs

A summary is sound for a command's runs where every run from an entry
meeting `P` completes by an exit the summary reaches, within that exit's
bound (`Sound`). Each composition rule above is sound for the runs of the
composite command (`Runs.seq`, `Runs.choice`, `Runs.handle`, `Runs.loop`,
and a finalizer's and an async body's runs), and a sound summary gives the
command's summary of `Semantics/CommandSummaries.lean` (`sound_spec`). -/

/-- An exit's bound holds of a two-state: an action of its class entries; an
unreached exit holds of none. -/
def ExitHolds : Option Closed → TwoState → Prop
  | some c, s => EffectAction c.fp s.beforeEnv s.before s.after
  | none, _ => False

/-- **A class summary is sound for runs `R` from the entry condition `P`.** -/
def Sound (P : TolerantFrames.Assertion) (R : CallEffects.Runs) (S : ClassSummary) : Prop :=
  ∀ c s, s.Entry P → R c s → ExitHolds (S.get c) s

/-- A closed footprint's postcondition reads no slot. -/
theorem post_fp_env {c : Closed} {ρ ρ' : Env} {h h' : Heap} (hp : Post c.fp ρ h h') : Post c.fp ρ' h h' :=
  Closed.post_iff.mpr (Closed.post_iff.mp hp)

/-- **Class actions compose** (Seq-Eff on class entries): an action of `a`,
then one of `b` from the state it leaves, is an action of `a.join b`. -/
theorem exitHolds_then {a b : Option Closed} {ρ₀ η ρ₂ : Env} {m : Nat} {t₀ t₁ t₂ : TolerantFrames.IndexedHeap}
    (h₁ : ExitHolds a ⟨ρ₀, η, m, t₀, t₁⟩) (h₂ : ExitHolds b ⟨η, ρ₂, m, t₁, t₂⟩) :
    ExitHolds (andThen a b) ⟨ρ₀, ρ₂, m, t₀, t₂⟩ := by
  cases a with
  | none => exact h₁.elim
  | some a =>
  cases b with
  | none => exact h₂.elim
  | some b =>
  refine ⟨TolerantFrames.Admissible.trans h₁.1 h₂.1, ?_⟩
  have e₁ : (a.join b).Holds t₀.h t₁.h := Closed.Holds.mono (le_join a b).1 (post_fp_env h₁.2)
  have e₂ : (a.join b).Holds t₁.h t₂.h := Closed.Holds.mono (le_join a b).2 (post_fp_env h₂.2)
  exact post_fp_env (Closed.Holds.trans_on e₁ (e₂.on _))

theorem exitHolds_mono {a b : Option Closed} {s : TwoState} (hw : exitWithin a b = true) (h : ExitHolds a s) :
    ExitHolds b s := by
  cases a with
  | none => exact h.elim
  | some a =>
    cases b with
    | none => cases hw
    | some b => exact ⟨h.1, Closed.post_mono hw h.2⟩

theorem exitHolds_alt_left {a : Option Closed} (b : Option Closed) {s : TwoState} (h : ExitHolds a s) :
    ExitHolds (alt a b) s := exitHolds_mono (exitWithin_alt_left a b) h

theorem exitHolds_alt_right (a : Option Closed) {b : Option Closed} {s : TwoState} (h : ExitHolds b s) :
    ExitHolds (alt a b) s := exitHolds_mono (exitWithin_alt_right a b) h

/-- **A sound summary weakens to one it is within.** -/
theorem Sound.weaken {P : TolerantFrames.Assertion} {R : CallEffects.Runs} {S S' : ClassSummary}
    (h : Sound P R S) (hw : S.within S' = true) : Sound P R S' := by
  intro c s hP hr
  have he : exitWithin (S.get c) (S'.get c) = true := by
    simp only [within, Bool.and_eq_true] at hw
    cases c
    · exact hw.1
    · exact hw.2
  exact exitHolds_mono he (h c s hP hr)

/-- **Fewer runs keep a summary sound.** -/
theorem Sound.runs {P : TolerantFrames.Assertion} {R R' : CallEffects.Runs} {S : ClassSummary}
    (h : Sound P R S) (hr : ∀ c s, R' c s → R c s) : Sound P R' S :=
  fun c s hP h' => h c s hP (hr c s h')

private theorem then_holds {P P₂ : TolerantFrames.Assertion} {R₁ R₂ : CallEffects.Runs} {A B : ClassSummary}
    {k₁ k₂ : Completion} (hA : Sound P R₁ A) (hB : Sound P₂ R₂ B)
    (hmid : ∀ s, s.Entry P → ExitHolds (A.get k₁) s → P₂ s.afterEnv s.mark s.after) :
    ∀ s, s.Entry P → R₁.then k₁ R₂ k₂ s → ExitHolds (andThen (A.get k₁) (B.get k₂)) s := by
  rintro ⟨ρ₀, ρ₂, m, t₀, t₂⟩ hP ⟨η, t₁, r₁, r₂⟩
  have a₁ := hA k₁ ⟨ρ₀, η, m, t₀, t₁⟩ hP r₁
  exact exitHolds_then a₁ (hB k₂ ⟨η, ρ₂, m, t₁, t₂⟩ (hmid ⟨ρ₀, η, m, t₀, t₁⟩ hP a₁) r₂)

/-- **Sequence is sound** (`CommandSummary.seq_sound` at the class level). -/
theorem seq_sound {P P₂ : TolerantFrames.Assertion} {R₁ R₂ : CallEffects.Runs} {A B : ClassSummary}
    (hA : Sound P R₁ A) (hB : Sound P₂ R₂ B)
    (hmid : ∀ s, s.Entry P → ExitHolds A.normal s → P₂ s.afterEnv s.mark s.after) :
    Sound P (R₁.seq R₂) (seq A B) := by
  intro c s hP hr
  cases c with
  | normal => exact then_holds (k₁ := .normal) (k₂ := .normal) hA hB hmid s hP hr
  | exceptional =>
    rcases hr with hr | hr
    · exact exitHolds_alt_left _ (hA .exceptional s hP hr)
    · exact exitHolds_alt_right _ (then_holds (k₁ := .normal) (k₂ := .exceptional) hA hB hmid s hP hr)

/-- **Choice is sound** (`CommandSummary.choice_sound`). -/
theorem choice_sound {P : TolerantFrames.Assertion} {R₁ R₂ : CallEffects.Runs} {A B : ClassSummary}
    (hA : Sound P R₁ A) (hB : Sound P R₂ B) : Sound P (R₁.choice R₂) (choice A B) := by
  intro c s hP hr
  rcases hr with hr | hr
  · cases c
    · exact exitHolds_alt_left _ (hA .normal s hP hr)
    · exact exitHolds_alt_left _ (hA .exceptional s hP hr)
  · cases c
    · exact exitHolds_alt_right _ (hB .normal s hP hr)
    · exact exitHolds_alt_right _ (hB .exceptional s hP hr)

/-- **The walk's step is sound**: the runs walked so far, or those followed
by the operation's, within `extend`. -/
theorem extend_sound {P P₂ : TolerantFrames.Assertion} {R Rop : CallEffects.Runs} {S op : ClassSummary}
    (hS : Sound P R S) (hop : Sound P₂ Rop op)
    (hmid : ∀ s, s.Entry P → ExitHolds S.normal s → P₂ s.afterEnv s.mark s.after) :
    Sound P (R.choice (R.seq Rop)) (extend S op) :=
  choice_sound hS (seq_sound hS hop hmid)

/-- **Handler is sound** (`CommandSummary.handle_sound`). -/
theorem handle_sound {P P₂ : TolerantFrames.Assertion} {R₁ R₂ : CallEffects.Runs} {A D : ClassSummary}
    (hA : Sound P R₁ A) (hD : Sound P₂ R₂ D)
    (hmid : ∀ s, s.Entry P → ExitHolds A.exceptional s → P₂ s.afterEnv s.mark s.after) :
    Sound P (R₁.handle R₂) (handle A D) := by
  intro c s hP hr
  cases c with
  | normal =>
    rcases hr with hr | hr
    · exact exitHolds_alt_left _ (hA .normal s hP hr)
    · exact exitHolds_alt_right _ (then_holds (k₁ := .exceptional) (k₂ := .normal) hA hD hmid s hP hr)
  | exceptional => exact then_holds (k₁ := .exceptional) (k₂ := .exceptional) hA hD hmid s hP hr

/-- **The runs of `try c finally f`**: `f` after either exit of `c`; the
statement returns where both do, and throws where `f` throws or `c` threw
and `f` returned (the throw is raised again). -/
def _root_.Verification.CallEffects.Runs.finally (R F : CallEffects.Runs) : CallEffects.Runs
  | .normal, s => R.then .normal F .normal s
  | .exceptional, s => R.then .exceptional F .normal s ∨ R.then .normal F .exceptional s ∨
      R.then .exceptional F .exceptional s

/-- **A finalizer's summary.** -/
def finally_ (A F : ClassSummary) : ClassSummary :=
  ⟨andThen A.normal F.normal,
    alt (andThen A.exceptional F.normal) (alt (andThen A.normal F.exceptional) (andThen A.exceptional F.exceptional))⟩

/-- **A finalizer's summary is sound**, `f` entered after either exit. -/
theorem finally_sound {P P₂ : TolerantFrames.Assertion} {R F : CallEffects.Runs} {A B : ClassSummary}
    (hA : Sound P R A) (hF : Sound P₂ F B)
    (hmid : ∀ c s, s.Entry P → ExitHolds (A.get c) s → P₂ s.afterEnv s.mark s.after) :
    Sound P (R.finally F) (finally_ A B) := by
  intro c s hP hr
  cases c with
  | normal => exact then_holds (k₁ := .normal) (k₂ := .normal) hA hF (hmid .normal) s hP hr
  | exceptional =>
    rcases hr with hr | hr | hr
    · exact exitHolds_alt_left _ (then_holds (k₁ := .exceptional) (k₂ := .normal) hA hF (hmid .exceptional) s hP hr)
    · exact exitHolds_alt_right _ (exitHolds_alt_left _
        (then_holds (k₁ := .normal) (k₂ := .exceptional) hA hF (hmid .normal) s hP hr))
    · exact exitHolds_alt_right _ (exitHolds_alt_right _
        (then_holds (k₁ := .exceptional) (k₂ := .exceptional) hA hF (hmid .exceptional) s hP hr))

/-- **The runs of an async body's call**: the body's return, or its throw,
which rejects the promise the call returned, both a normal return; the call
never throws. -/
def _root_.Verification.CallEffects.Runs.settle (R : CallEffects.Runs) : CallEffects.Runs
  | .normal, s => R .normal s ∨ R .exceptional s
  | .exceptional, _ => False

theorem settle_sound {P : TolerantFrames.Assertion} {R : CallEffects.Runs} {S : ClassSummary}
    (h : Sound P R S) : Sound P R.settle S.settle := by
  intro c s hP hr
  cases c with
  | normal =>
    rcases hr with hr | hr
    · exact exitHolds_alt_left _ (h .normal s hP hr)
    · exact exitHolds_alt_right _ (h .exceptional s hP hr)
  | exceptional => exact hr.elim

/-- **Iterations are within the prefix summary** (the note, §6, Loop, with
rigid class entries; induction on iterations). -/
theorem iterates_holds {R : CallEffects.Runs} {B : ClassSummary}
    (hB : Sound (fun _ _ _ => True) R B) :
    ∀ s, CallEffects.Iterates (R .normal) s → ExitHolds (iterated B) s := by
  intro s hi
  induction hi with
  | zero η m st =>
    exact exitHolds_alt_left _ (show ExitHolds (some Closed.empty) _ from EffectAction.refl _ _ _)
  | @step ρ₀ η ρ₂ m t₀ t₁ t₂ _ hit ih =>
    exact exitHolds_mono (iterated_step B) (exitHolds_then ih (hB .normal ⟨η, ρ₂, m, t₁, t₂⟩ trivial hit))

/-- **A loop's summary is sound**: its iterations within the prefix
summary, then a departure within the departures' summary `D`. -/
theorem loop_sound {R Rd : CallEffects.Runs} {B D : ClassSummary}
    (hB : Sound (fun _ _ _ => True) R B) (hD : Sound (fun _ _ _ => True) Rd D) :
    Sound (fun _ _ _ => True) (CallEffects.Runs.loop (R .normal) Rd) (seq ⟨iterated B, none⟩ D) := by
  rintro c ⟨ρ₀, ρ₂, m, t₀, t₂⟩ _ ⟨η, t₁, hi, hr⟩
  have h₁ := iterates_holds hB ⟨ρ₀, η, m, t₀, t₁⟩ hi
  have h₂ := hD c ⟨η, ρ₂, m, t₁, t₂⟩ trivial hr
  cases c with
  | normal => exact exitHolds_then h₁ h₂
  | exceptional => exact exitHolds_alt_right (none : Option Closed) (exitHolds_then h₁ h₂)

/-! ## The command summary it gives -/

/-- The exit specification of a reached bound: its class entries, no
postcondition; an unreached exit's is vacuous. -/
def spec (S : ClassSummary) : CommandSummary :=
  ⟨⟨(S.normal.getD .empty).fp, []⟩, ⟨(S.exceptional.getD .empty).fp, []⟩⟩

/-- The summary's schema at a call of any arity is its command summary. -/
theorem schema_atArity (S : ClassSummary) (n : Nat) : S.schema.atArity n = S.spec := rfl

/-- **A sound class summary is a sound command summary** (proved;
`CommandSummary.Sound` of `Semantics/CommandSummaries.lean`). -/
theorem sound_spec {P : TolerantFrames.Assertion} {R : CallEffects.Runs} {S : ClassSummary}
    (h : Sound P R S) (arena : AssertionArena) : CommandSummary.Sound arena P R S.spec := by
  intro c s hP hr
  have he := h c s hP hr
  cases c with
  | normal =>
    cases hn : S.normal with
    | none => rw [show S.get .normal = S.normal from rfl, hn] at he; exact he.elim
    | some k =>
      rw [show S.get .normal = S.normal from rfl, hn] at he
      refine ⟨?_, fun _ hF => nomatch hF⟩
      simp only [spec, Exits.get, hn, Option.getD]
      exact he
  | exceptional =>
    cases hx : S.exceptional with
    | none => rw [show S.get .exceptional = S.exceptional from rfl, hx] at he; exact he.elim
    | some k =>
      rw [show S.get .exceptional = S.exceptional from rfl, hx] at he
      refine ⟨?_, fun _ hF => nomatch hF⟩
      simp only [spec, Exits.get, hx, Option.getD]
      exact he

end ClassSummary

end Verification.SourceExtraction