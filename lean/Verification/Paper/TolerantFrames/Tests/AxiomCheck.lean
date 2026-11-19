import Verification.Paper.TolerantFrames.Bridges.ExitProposals
import Verification.Paper.TolerantFrames.Bridges.Grow
import Verification.Paper.TolerantFrames.Bridges.ModelTyped
import Verification.Paper.TolerantFrames.Bridges.ParityArithmeticBridges
import Verification.Paper.TolerantFrames.Bridges.Transfer
import Verification.Paper.TolerantFrames.CommandBodies
import Verification.Paper.TolerantFrames.CommandComposition
import Verification.Paper.TolerantFrames.CommandLoops
import Verification.Paper.TolerantFrames.CommandSummaries
import Verification.Paper.TolerantFrames.Examples
import Verification.Paper.TolerantFrames.Instances
import Verification.Paper.TolerantFrames.KindsModelRules
import Verification.Paper.TolerantFrames.ModelLoop
import Verification.Paper.TolerantFrames.ModelRules
import Verification.Paper.TolerantFrames.NamedCounterexample
import Verification.Paper.TolerantFrames.ParityAssertions
import Verification.Paper.TolerantFrames.ParityDerivations
import Verification.Paper.TolerantFrames.ParityEvidence
import Verification.Paper.TolerantFrames.ReadOnlyBinding
import Verification.Paper.TolerantFrames.ReadOnlyBridge
import Verification.Paper.TolerantFrames.ReadOnlyCallFrame
import Verification.Paper.TolerantFrames.ReadOnlyCert
import Verification.Paper.TolerantFrames.ReadOnlyCharges
import Verification.Paper.TolerantFrames.ReadOnlyCover
import Verification.Paper.TolerantFrames.ReadOnlyChecks
import Verification.Paper.TolerantFrames.ReadOnlyClaim
import Verification.Paper.TolerantFrames.ReadOnlyComponents
import Verification.Paper.TolerantFrames.ReadOnlyCrossings
import Verification.Paper.TolerantFrames.ReadOnlyExec
import Verification.Paper.TolerantFrames.ReadOnlyFlow
import Verification.Paper.TolerantFrames.ReadOnlyFlowSolve
import Verification.Paper.TolerantFrames.ReadOnlyIncoming
import Verification.Paper.TolerantFrames.ReadOnlyFits
import Verification.Paper.TolerantFrames.ReadOnlyFitsCheck
import Verification.Paper.TolerantFrames.ReadOnlyFitsDecide
import Verification.Paper.TolerantFrames.ReadOnlyFitsEntry
import Verification.Paper.TolerantFrames.ReadOnlyFitsReach
import Verification.Paper.TolerantFrames.ReadOnlyFitsStep
import Verification.Paper.TolerantFrames.ReadOnlyFitsSubst
import Verification.Paper.TolerantFrames.ReadOnlyFrame
import Verification.Paper.TolerantFrames.ReadOnlyLocated
import Verification.Paper.TolerantFrames.ReadOnlyLayouts
import Verification.Paper.TolerantFrames.ReadOnlyLocalReach
import Verification.Paper.TolerantFrames.ReadOnlyOutside
import Verification.Paper.TolerantFrames.ReadOnlyProvenance
import Verification.Paper.TolerantFrames.ReadOnlyPublic
import Verification.Paper.TolerantFrames.ReadOnlyIsolate
import Verification.Paper.TolerantFrames.ReadOnlyRealize
import Verification.Paper.TolerantFrames.ReadOnlyRegion
import Verification.Paper.TolerantFrames.ReadOnlyRuns
import Verification.Paper.TolerantFrames.ReadOnlySegment
import Verification.Paper.TolerantFrames.ReadOnlySites
import Verification.Paper.TolerantFrames.ReadOnlySteps
import Verification.Paper.TolerantFrames.ReadOnlyStepWrites
import Verification.Paper.TolerantFrames.ReadOnlyWriteKinds
import Verification.Paper.TolerantFrames.ReadOnlyWire
import Verification.Paper.TolerantFrames.Tests.ParityDerivationTests
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
The formalisation of the paper "Tolerant frames" rests on Lean's standard
axioms alone. The build fails when a safe declaration of any module under
`Verification.Paper` depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound` (`sorryAx`, or one the project
declares). This module imports every such module, which
`tests/axiom-check-imports.mts` checks. These declarations are the
definitions and rules of the paper stated in Lean, its worked examples, the
counter-model where a statement of the paper needs a premise, and the
bridges from the implementation's rules to the paper's; the paper cites
them, and acceptance reads none of them.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let library := `Verification.Paper
  let imported := env.header.moduleNames
  -- Every safe declaration of the paper's formalisation rests on the standard
  -- axioms.
  let mut checked := 0
  for (decl, info) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? decl | continue
    let module := imported[i.toNat]!
    unless library.isPrefixOf module && !info.isUnsafe do continue
    checked := checked + 1
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  if checked == 0 then throwError "no declaration of the paper's formalisation found"
