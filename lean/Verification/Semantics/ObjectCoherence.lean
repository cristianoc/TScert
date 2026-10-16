import Verification.Semantics.CallArguments

/-!
# Source terms

Program syntax cannot manufacture an already allocated identity, even in
an unreachable branch or the body of an empty overload.
-/
namespace Verification.ObjectCoherence

mutual
def sourceTerm : Tm → Bool
  | .objAt .. => false
  | .makeAt (.bound t r pre) _ args =>
      sourceTerm t && sourceTerm r && sourceArgs pre && sourceArgs args
  | .makeAt .absent _ args => sourceArgs args
  | .invoke f r args => sourceTerm f && sourceTerm r && sourceArgs args
  | .construct f args => sourceTerm f && sourceArgs args
  | .letE a b | .writeAt _ a b | .arith _ a b | .elemAt a b | .merge _ a b
  | .indexAt a b | .makeKey a b => sourceTerm a && sourceTerm b
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => sourceTerm a
  | .setElem a b c => sourceTerm a && sourceTerm b && sourceTerm c
  | .arrLit args => sourceArgs args
  | .arr .. => false
  | .ite c a b => sourceTerm c && sourceTerm a && sourceTerm b
  | .makeAt (.graph _ E _ _ caps _ _) _ args => sourceArgs E && sourceArgs caps && sourceArgs args
  | .goto .. | .frame .. => false
  | _ => true

def sourceArgs : List Tm → Bool
  | [] => true
  | a :: args => sourceTerm a && sourceArgs args
end


end Verification.ObjectCoherence
