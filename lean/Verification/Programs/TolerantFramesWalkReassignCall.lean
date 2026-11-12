import Verification.Programs.TolerantFramesWalkReassignNodes

/-! # Tolerant frames: the direct call at a reassignment

`directCall` reads a call's derivation off its callee's signatures in two
nested `for` loops over the phases and the signatures and a third over the
operands, threading the answers through `subtypeUsing`. At `reassign G η`
with the image check `images.reassign η` and the answers reassigned it
returns the same derivation, its answers reassigned (`directCall_reassign`):
each loop commutes with the map of its state (`forIn_map_state`, the `for`
form of `foldl_map_state`), and each answered request is invariant
(`subtypeUsing_reassign`, `Parametricity.checkTree_reassign`). -/
namespace Verification.TolerantFrames
open Verification PositiveGraphs PositiveRules PositiveCertificates ProgramTyping ProgramCertificates SinglePass CertificateProducer

/-- A loop step with its state mapped by `g`. -/
def stepMap {β γ : Type} (g : β → γ) : ForInStep β → ForInStep γ
  | .done b => .done (g b)
  | .yield b => .yield (g b)

/-- **A `for` loop commuting with a map of its state**: where the body at a
mapped state is the mapped step of the body, the loop from a mapped state
ends at the mapped state. -/
theorem forIn_map_state {α β γ : Type} (g : β → γ) (f : α → β → Id (ForInStep β)) (f' : α → γ → Id (ForInStep γ))
    (h : ∀ a b, f' a (g b) = stepMap g (f a b)) (l : List α) (b : β) :
    forIn (m := Id) l (g b) f' = g (forIn (m := Id) l b f) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, h]
    cases f a b with
    | done b' => rfl
    | yield b' => exact ih b'

section
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (η : MixedAssignment ι)
  (images : InstanceImageCheck G)

/-- The state of `directCall`'s loops over the phases and the signatures:
the returned derivation with its answers, and the answers. -/
def callStateMap (s : Option (Option (ProgramCertificates.Evidence ι × Bool) × Answered G) × Answered G) :
    Option (Option (ProgramCertificates.Evidence ι × Bool) × Answered (reassign G η)) × Answered (reassign G η) :=
  (s.1.map fun r => (r.1, Answered.reassign r.2 η), Answered.reassign s.2 η)

/-- The state of `directCall`'s loop over the operands: the answers, the
operands' derivations and whether each was found. -/
def operandStateMap (s : Answered G × Array (ProgramCertificates.Evidence ι) × Bool) :
    Answered (reassign G η) × Array (ProgramCertificates.Evidence ι) × Bool :=
  (Answered.reassign s.1 η, s.2)

/-- **The direct call at a reassigned graph**: the same derivation, the
answers reassigned. -/
theorem directCall_reassign (Γ : List (Ty ι)) (t : Tm) (A : Ty ι) (adm : CallEffects.Effect → Tm → Bool) (undefTy : Option (Ty ι))
    (a : Answered G) :
    directCall (reassign G η) (images.reassign η) Γ t A adm undefTy (Answered.reassign a η) =
      ((directCall G images Γ t A adm undefTy a).1, Answered.reassign (directCall G images Γ t A adm undefTy a).2 η) := by
  unfold directCall
  simp only [Parametricity.expand_reassign]
  split
  · rename_i f recv args
    split
    · rename_i F hF
      split
      · rfl
      · split
        all_goals first
        | rfl
        | split
          · simp only [pure_bind]
            generalize hX : forIn (m := Id) [true, false] (none, a) _ = X
            generalize hY : forIn (m := Id) [true, false] (none, Answered.reassign a η) _ = Y
            have hXY : Y = callStateMap G η X := by
              rw [← hX, ← hY]
              refine forIn_map_state (callStateMap G η) _ _ ?_ _ (none, a)
              intro phase ⟨r, b⟩
              generalize hX2 : forIn (m := Id) (List.filter _ _ ++ List.filter _ _) (none, b) _ = X2
              generalize hY2 : forIn (m := Id) (List.filter _ _ ++ List.filter _ _)
                (none, (callStateMap G η (r, b)).snd) _ = Y2
              have hXY2 : Y2 = callStateMap G η X2 := by
                rw [← hX2, ← hY2]
                refine forIn_map_state (callStateMap G η) _ _ ?_ _ (none, b)
                intro p ⟨r', b'⟩
                dsimp only
                split
                · rfl
                split
                · rfl
                split
                · rfl
                generalize hX3 : forIn (m := Id) ((recv, p.receiver) :: args.zip p.arguments) (b', #[], true) _ = X3
                generalize hY3 : forIn (m := Id) ((recv, p.receiver) :: args.zip p.arguments)
                  ((callStateMap G η (r', b')).snd, #[], true) _ = Y3
                have hXY3 : Y3 = operandStateMap G η X3 := by
                  rw [← hX3, ← hY3]
                  refine forIn_map_state (operandStateMap G η) _ _ ?_ _ (b', #[], true)
                  intro ⟨tm, D⟩ ⟨a3, parts, ok⟩
                  dsimp only [operandStateMap]
                  cases tm
                  case var i =>
                    dsimp only
                    split
                    · split
                      · rfl
                      · rw [subtypeUsing_reassign]
                        dsimp only
                        split <;> rfl
                    · rfl
                  case undef =>
                    dsimp only
                    rw [Parametricity.checkTree_reassign]
                    split
                    · rfl
                    · rw [subtypeUsing_reassign]
                      dsimp only
                      split <;> rfl
                  all_goals rfl
                subst hXY3
                rcases X3 with ⟨a3, parts, ok⟩
                have e : ∀ {β γ : Type} (s : β) (k : β → Id γ), (bind (m := Id) s k) = k s := fun _ _ => rfl
                simp only [e, operandStateMap]
                split
                · rfl
                · by_cases hs : same p.result A = true
                  · simp only [hs, if_true]
                    split <;> rfl
                  · simp only [hs, Bool.false_eq_true, if_false, subtypeUsing_reassign]
                    split <;> rfl
              subst hXY2
              rcases X2 with ⟨_ | ⟨r2, b2⟩, a2⟩ <;> rfl
            subst hXY
            rcases X with ⟨_ | ⟨r, b⟩, a'⟩ <;> rfl
          · rfl
    · rfl
  · rfl
end
end Verification.TolerantFrames
