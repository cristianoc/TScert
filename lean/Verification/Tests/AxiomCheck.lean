import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Verification.Source.SourceClaimJson

/-!
The acceptance theorem rests on Lean's standard axioms alone. The build fails
when `SourceClaimJson.checkJson_safe` depends on any other axiom: `sorryAx`
or one the project declares. Every accepted function's safety is a
consequence of that theorem, so this one check covers what acceptance uses.
-/

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let used ← liftCoreM <| collectAxioms ``Verification.SourceClaimJson.checkJson_safe
  for axiom_ in used do
    unless standard.contains axiom_ do
      throwError "checkJson_safe depends on the axiom {axiom_}"
