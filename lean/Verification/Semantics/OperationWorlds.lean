-- OperationResults.lean defines an operation's result family as the closure of its outcomes; without it operation results have no least admissible bound.
import Verification.Semantics.OperationResults

namespace Verification.OperationWorlds
open OperationResults

/-- A fixed choice of world annotations for a modeled execution. It is supplied
by the program/host model, independently of the result bound being checked. -/
structure Policy where
  allows : Config → Config → Prop
  unique : ∀ {c d e}, allows c d → allows c e → d = e

def SafeWith (Ξ : Fam) (p : Policy) (B : Fam) : (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, _, _, _ => True
  | n+1, W, h, t =>
      ((isVal t = true ∧ B (n+1) W t) ∨ Thrown Ξ (n+1) W t) ∨
      ∃ U : WorldT n, ∃ h' t',
        WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧
        Step h t h' t' ∧ HeapOk n U h' ∧
        p.allows ⟨n+1,W,h,t⟩ ⟨n,U,h',t'⟩ ∧ SafeWith Ξ p B n U h' t'

theorem erase {p B} : ∀ n (W : WorldT n) h t,
    SafeWith Ξ p B n W h t → Safe Ξ B n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with (hv | ht) | ⟨U,h',t',he,hu,st,hh,_,rest⟩
    · exact .inl (.inl hv)
    · exact .inl (.inr ht)
    · exact .inr ⟨U,h',t',he,hu,st,hh,ih U h' t' rest⟩


end Verification.OperationWorlds
