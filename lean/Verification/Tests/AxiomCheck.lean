import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Compiler.CSimpAttr
import Verification.Source.Claims.Json
import Verification.Source.RequestCli

/-!
Acceptance rests on Lean's standard axioms alone. The build fails when either
depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`
(`sorryAx`, or one the project declares):

- `SourceClaimJson.checkUnitJson_safe`, the acceptance theorem, of which every
  accepted function's and module run's safety is a consequence;
- each `@[csimp]` lemma of the project's modules the verifier imports
  (`Verification.Source.RequestCli`, what `Main` imports): the compiled
  verifier runs a lemma's right-hand side in place of the definition the
  proofs reason about, so its equation is part of what acceptance uses.
-/

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.SourceClaimJson.checkUnitJson_safe
  let env ← getEnv
  let project (decl : Name) : Bool := match env.getModuleIdxFor? decl with
    | some i => (`Verification).isPrefixOf env.header.moduleNames[i.toNat]!
    | none => false
  let lemmas := (Compiler.CSimp.ext.getState env).thmNames.toList.filter project
  if lemmas.isEmpty then throwError "no @[csimp] lemma of the project found"
  for decl in lemmas do check decl
