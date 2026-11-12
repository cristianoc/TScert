import Verification.Programs.TolerantFramesComposeYields

/-! # The producer's guarded subtype answers -/
namespace Verification.TolerantFrames
open Verification CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates PositiveRules LabelStore
variable {ι : Type} [Labels ι]

/-- A cached acceptance has its proved inclusion; a new acceptance has the search's inclusion. -/
theorem subtypeUsing_sound {G : NormalGraph ι} {I : InstanceImageCheck G} {A B : List ι} {a : Answered G}
    (h : (subtypeUsing G I A B a).1.value.isSome = true) :
    ∀ η, FamLe (mixedMeaning G η A) (mixedMeaning G η B) := by
  unfold subtypeUsing at h
  split at h
  · split at h
    · simp at h
    · rename_i r _ hg
      have hp : a.proved.contains (A, B) = true := by
        cases he : a.proved.contains (A, B) <;> simp_all
      exact a.proved_sound A B hp
  · exact subtypeSearch_sound h

/-- Every accepted subtype answer supplies ordinary value inclusion. -/
theorem subtypeAnswersAll : SubtypeAnswersAll ι := by
  intro G I A B a h n W v hv
  exact subtypeUsing_sound h G.env n W (.inl v) hv

end Verification.TolerantFrames
