import Verification.Paper.TolerantFrames.PostconditionProgramRenaming

/-! # Full postconditions ignore out-of-scope body locals

Use the existing syntactic program-map agreement and complete renaming theorem.
The entry is fixed. Function postconditions have input scope Γ and current
scope Γ plus a result, hence entry-scope inclusion is explicit. Logical names
are unchanged, including beneath both kinds of quantifier.
-/
namespace Verification.Paper.TolerantFrames.TwoState
open Verification

theorem Post.current_env_agree {entryPrograms programs : Nat → Prop} {indices values : Nat}
    {Q : Post} (scope : Q.Scoped entryPrograms programs indices values)
    (included : ∀ x, entryPrograms x → programs x)
    (c : Context) (ρ' : Env) (η : LogicalEnv)
    (agree : ∀ x, programs x → c.current.env x = ρ' x) :
    Q.Holds c η ↔ Q.Holds {c with current := {c.current with env := ρ'}} η := by
  classical
  let leftMap : Nat → Nat := fun x => 2 * x
  let rightMap : Nat → Nat := fun x => if programs x then 2 * x else 2 * x + 1
  let packed : Context :=
    ⟨⟨(fun x => c.entry.env (x / 2)), c.entry.heap⟩,
      ⟨(fun x => if x % 2 = 0 then c.current.env (x / 2) else ρ' (x / 2)), c.current.heap⟩,
      c.mark⟩
  have mapAgree : ∀ x, programs x → leftMap x = rightMap x := by
    intro x hx
    simp only [leftMap, rightMap, if_pos hx]
  have renamed := Post.rename_program_agree (fun x hx => mapAgree x (included x hx)) mapAgree id id scope
  have leftContext : packed.rename (programMap leftMap id id) = c := by
    dsimp [packed, Context.rename, State.rename, programMap, leftMap]
    congr 1
    · congr 1
      funext x
      congr 1
      omega
    · congr 1
      funext x
      have hm : (2 * x) % 2 = 0 := by omega
      have hd : 2 * x / 2 = x := by omega
      simp only [hm, if_true, hd]
  have rightContext : packed.rename (programMap rightMap id id) =
      {c with current := {c.current with env := ρ'}} := by
    dsimp [packed, Context.rename, State.rename, programMap]
    congr 1
    · congr 1
      funext x
      congr 1
      dsimp only [rightMap]
      split <;> omega
    · congr 1
      funext x
      by_cases hx : programs x
      · have hm : (2 * x) % 2 = 0 := by omega
        have hd : 2 * x / 2 = x := by omega
        simpa only [rightMap, if_pos hx, hm, if_true, hd] using agree x hx
      · have hm : (2 * x + 1) % 2 ≠ 0 := by omega
        have hd : (2 * x + 1) / 2 = x := by omega
        simp only [rightMap, if_neg hx, hm, if_false, hd]
  have leftMeaning := Post.holds_rename (programMap leftMap id id) packed η Q
  have rightMeaning := Post.holds_rename (programMap rightMap id id) packed η Q
  rw [leftContext] at leftMeaning
  rw [rightContext] at rightMeaning
  change (Q.rename (programMap leftMap id id)).Holds packed η ↔ Q.Holds c η at leftMeaning
  change (Q.rename (programMap rightMap id id)).Holds packed η ↔
    Q.Holds {c with current := {c.current with env := ρ'}} η at rightMeaning
  exact leftMeaning.symm.trans ((Iff.of_eq (congrArg (fun R => R.Holds packed η) renamed)).trans rightMeaning)

end Verification.Paper.TolerantFrames.TwoState
