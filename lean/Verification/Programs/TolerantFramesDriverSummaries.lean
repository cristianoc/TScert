import Verification.Programs.TolerantFramesDriverWalk

/-! # Tolerant frames: the read summaries along the driver's walk

A drive whose every visit leaves the read-summary table it starts from as
a prefix of the one it returns (`VisitKeeps`), and of the one it stops
with (`VisitStopsKeep`), leaves its start's table a prefix of the table it
returns (`Drives.keeps`) or stops with (`drive_stop_keeps`). A table
restored at a visit's boundary, the earlier table followed by what the
later one adds after it, has the earlier as its prefix (`keep_prefix`).
The setup leaves the answers it is given unchanged (`setup_answers`), so
where every visit keeps its table (`VisitsKeepSummaries`) a call's walk
keeps the call's table (`walk_keeps`) and the pass keeps the summaries it
was given (`runKeepsSummaries`, the unit level's `RunKeepsSummaries`). -/
namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs

section Summaries
variable {ι : Type} [DecidableEq ι] [Hashable ι] {G : NormalGraph ι}

/-- The read-summary table of `a` is a prefix of `b`'s. -/
def SumsPrefix (a b : Answered G) : Prop := a.summaries.toList <+: b.summaries.toList

theorem SumsPrefix.refl (a : Answered G) : SumsPrefix a a := List.prefix_refl _

theorem SumsPrefix.trans {a b c : Answered G} (h₁ : SumsPrefix a b) (h₂ : SumsPrefix b c) : SumsPrefix a c :=
  List.IsPrefix.trans h₁ h₂

/-- A prefix's summaries are summaries of the longer table. -/
theorem SumsPrefix.mem {a b : Answered G} (h : SumsPrefix a b) : ∀ s ∈ a.summaries.toList, s ∈ b.summaries.toList :=
  fun _ hs => h.subset hs

/-- **A table restored at a visit's boundary** (the earlier table, then
what the later one adds after its length) has the earlier as its prefix. -/
theorem keep_prefix (a b : Answered G) :
    SumsPrefix a { b with summaries := a.summaries ++ b.summaries.extract a.summaries.size b.summaries.size } := by
  unfold SumsPrefix
  simp only [Array.toList_append]
  exact List.prefix_append _ _

/-- Every visit that returns leaves the table it starts from a prefix of
its result's. -/
def VisitKeeps (visit : SinglePass.WalkState ι G → Nat → Except (SinglePass.WalkStop ι G) (SinglePass.WalkState ι G)) :
    Prop :=
  ∀ σ l σ', visit σ l = .ok σ' → SumsPrefix σ.answers σ'.answers

/-- Every visit that stops leaves the table it starts from a prefix of the
one it stops with. -/
def VisitStopsKeep
    (visit : SinglePass.WalkState ι G → Nat → Except (SinglePass.WalkStop ι G) (SinglePass.WalkState ι G)) : Prop :=
  ∀ σ l stop, visit σ l = .error stop → SumsPrefix σ.answers stop.answers

/-- **A drive keeps its start's table as a prefix** (`Drives`). -/
theorem Drives.keeps {visit : SinglePass.WalkState ι G → Nat → Except (SinglePass.WalkStop ι G) (SinglePass.WalkState ι G)}
    (hv : VisitKeeps visit) {σ σ' : SinglePass.WalkState ι G} (h : Drives visit σ σ') : SumsPrefix σ.answers σ'.answers := by
  induction h with
  | done _ => exact SumsPrefix.refl _
  | step _ hvis _ ih => have h1 := hv _ _ _ hvis; exact SumsPrefix.trans h1 ih

/-- **A drive that stops keeps its start's table as a prefix** of the one
it stops with. -/
theorem drive_stop_keeps
    {visit : SinglePass.WalkState ι G → Nat → Except (SinglePass.WalkStop ι G) (SinglePass.WalkState ι G)}
    (hv : VisitKeeps visit) (hs : VisitStopsKeep visit) :
    ∀ (fuel : Nat) (σ : SinglePass.WalkState ι G) stop, SinglePass.drive visit fuel σ = .error stop →
      SumsPrefix σ.answers stop.answers
  | 0, σ, stop, h => by
    cases hq : σ.queue with
    | nil => simp [SinglePass.drive, hq] at h
    | cons l rest =>
      simp only [SinglePass.drive, hq, Except.error.injEq] at h
      subst h
      exact SumsPrefix.refl _
  | fuel + 1, σ, stop, h => by
    cases hq : σ.queue with
    | nil => simp [SinglePass.drive, hq] at h
    | cons l rest =>
      simp only [SinglePass.drive, hq] at h
      cases hvis : visit { σ with queue := rest } l with
      | error e =>
        rw [hvis] at h
        cases h
        have h1 := hs _ _ _ hvis
        exact h1
      | ok σ₁ =>
        rw [hvis] at h
        have h1 := hv _ _ _ hvis
        exact SumsPrefix.trans h1 (drive_stop_keeps hv hs fuel σ₁ stop h)

end Summaries

end Verification.TolerantFrames

namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore

section Setup
variable {ι : Type} [Labels ι]

/-- The answers a setup's result carries: those it stops with, or those of
the state the first visit starts from. -/
def SetupAnswers {G : NormalGraph ι} {I : InstanceImageCheck G} (a : Answered G) :
    Except (SinglePass.WalkStop ι G) (SinglePass.WalkEnv ι G I × SinglePass.WalkState ι G) → Prop
  | .error stop => stop.answers = a
  | .ok (_, σ0) => σ0.answers = a

/-- **The setup leaves the answers it is given unchanged**, where it stops
and in the state the first visit starts from. -/
theorem setup_answers {G : NormalGraph ι} {I : InstanceImageCheck G} (c : Target.RunCall G I) :
    SetupAnswers c.answers (SinglePass.setup G I c.pool c.fuel c.P c.claims c.start c.inputs c.goal c.assertions
      c.cuts c.candidates c.entryIndices c.suggestions c.known c.codes c.aliases c.passChecker c.answers
      c.reference c.debugNode c.bound c.givenImplies c.givenArgs c.ensures c.givenInputs c.entrySeparation
      c.observe c.tracing c.observeEntry c.regional) := by
  generalize h : SinglePass.setup G I _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = r
  unfold SinglePass.setup at h
  repeat' (first | (extract_lets at h) | split at h | (dsimp (config := { zetaDelta := true }) only at h))
  all_goals (try simp only [Id.run_bind, Id.run_pure] at h)
  all_goals (subst h; rfl)

variable (ι) in
/-- **(Named hypothesis) Every visit keeps the read-summary table it starts
from** as a prefix of the one it returns or stops with, at every setup's
`env` (`VisitKeeps`, `VisitStopsKeep` of `SinglePass.visit`). -/
def VisitsKeepSummaries : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (env : SinglePass.WalkEnv ι G I),
    VisitKeeps (SinglePass.visit G I env) ∧ VisitStopsKeep (SinglePass.visit G I env)

/-- **A call's walk keeps the summaries it is given**: the table of the
answers it returns or stops with has the call's table as a prefix
(`setup_answers`, `Drives.keeps`, `drive_stop_keeps`). -/
theorem walk_keeps (hv : VisitsKeepSummaries ι) {G : NormalGraph ι} {I : InstanceImageCheck G}
    (c : Target.RunCall G I) :
    (∀ stop, RunCall.walk c = .error stop → SumsPrefix c.answers stop.answers) ∧
    (∀ σ reach, RunCall.walk c = .ok (σ, reach) → SumsPrefix c.answers σ.answers) := by
  have hs := setup_answers c
  unfold RunCall.walk SinglePass.runWalk
  generalize SinglePass.setup G I _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = r at hs ⊢
  cases r with
  | error stop =>
    simp only [SetupAnswers] at hs
    refine ⟨fun stop' h => ?_, fun σ reach h => ?_⟩
    · cases h; rw [hs]; exact SumsPrefix.refl _
    · cases h
  | ok p =>
    obtain ⟨env, σ0⟩ := p
    simp only [SetupAnswers] at hs
    have hk := hv G I env
    cases hd : SinglePass.drive (SinglePass.visit G I env) (env.n + 1) σ0 with
    | error stop =>
      refine ⟨fun stop' h => ?_, fun σ reach h => ?_⟩
      · simp only [bind, Except.bind, hd] at h
        cases h
        exact hs ▸ drive_stop_keeps hk.1 hk.2 _ _ _ hd
      · simp only [bind, Except.bind, hd] at h
        cases h
    | ok σ =>
      refine ⟨fun stop' h => ?_, fun σ' reach h => ?_⟩
      · simp only [bind, Except.bind, hd] at h
        cases h
      · simp only [bind, Except.bind, hd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hs ▸ Drives.keeps hk.1 (drives_of_drive _ _ _ hd)

/-- **(`runKeepsSummaries`) The pass keeps the read summaries it was
given** (`Target.RunKeepsSummaries`), where every visit keeps them
(`walk_keeps`; `run` returns the answers of the stop or of the walk's
state). -/
theorem runKeepsSummaries (hv : VisitsKeepSummaries ι) : Target.RunKeepsSummaries ι := by
  intro G I c s hs
  have hk := walk_keeps hv c
  unfold Target.RunCall.result SinglePass.run
  cases hw : RunCall.walk c with
  | error stop =>
    unfold RunCall.walk at hw
    rw [hw]
    exact (hk.1 stop (by unfold RunCall.walk; exact hw)).mem s hs
  | ok p =>
    obtain ⟨σ, reach⟩ := p
    unfold RunCall.walk at hw
    rw [hw]
    exact (hk.2 σ reach (by unfold RunCall.walk; exact hw)).mem s hs

end Setup
end Verification.TolerantFrames
