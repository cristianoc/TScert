import Verification.Paper.TolerantFrames.BoundedCommands
import Verification.Paper.TolerantFrames.BoundedFrameRules
import Verification.Paper.TolerantFrames.BoundedEffects
import Verification.Paper.TolerantFrames.PostconditionValuationScope
import Verification.Paper.TolerantFrames.MarkIndependence
import Verification.Paper.TolerantFrames.RecursiveFunctions
import Verification.Paper.TolerantFrames.RecursiveCallRules
import Verification.Paper.TolerantFrames.CallableEntrySpecification
import Verification.Paper.TolerantFrames.CallableReferences
import Verification.Paper.TolerantFrames.PostconditionEnvironmentScope
import Verification.Paper.TolerantFrames.CallableEntryCorrectness
import Verification.Paper.TolerantFrames.CallableEntryCode
import Verification.Paper.TolerantFrames.CallableEntryLayout
import Verification.Paper.TolerantFrames.LengthBridges
import Verification.Paper.TolerantFrames.PaperTermForms
import Verification.Paper.TolerantFrames.LengthReading
import Verification.Paper.TolerantFrames.CompilerCorrectness
import Verification.Paper.TolerantFrames.CompilerNodeSimulation
import Verification.Paper.TolerantFrames.CompilerSinks
import Verification.Paper.TolerantFrames.CompilerControlSimulation
import Verification.Paper.TolerantFrames.CompilerPrimitiveSimulation
import Verification.Paper.TolerantFrames.CompilerSimulation
import Verification.Paper.TolerantFrames.CompilerOrigins
import Verification.Paper.TolerantFrames.CompilerRoutes
import Verification.Paper.TolerantFrames.CompilerSegments
import Verification.Paper.TolerantFrames.CommandCompiler
import Verification.Paper.TolerantFrames.CommandMachine
import Verification.Paper.TolerantFrames.GraphSegments
import Verification.Paper.TolerantFrames.GraphInversion
import Verification.Paper.TolerantFrames.CompilerScope
import Verification.Paper.TolerantFrames.CompilerLayout
import Verification.Paper.TolerantFrames.BitwiseArithmetic
import Verification.Paper.TolerantFrames.PureOperations
import Verification.Paper.TolerantFrames.BitwiseRules
import Verification.Paper.TolerantFrames.OperationCode
import Verification.Paper.TolerantFrames.OwnFieldCode
import Verification.Paper.TolerantFrames.BudgetTruncation
import Verification.Paper.TolerantFrames.CallAdmission
import Verification.Paper.TolerantFrames.CallRules
import Verification.Paper.TolerantFrames.PrimitiveRenaming
import Verification.Paper.TolerantFrames.FormulaScopes
import Verification.Paper.TolerantFrames.PostconditionProgramRenaming
import Verification.Paper.TolerantFrames.PostconditionRenamingScopes
import Verification.Paper.TolerantFrames.PostconditionRenamingAdmission
import Verification.Paper.TolerantFrames.PostconditionScopeWeakening
import Verification.Paper.TolerantFrames.WorldIndependence
import Verification.Paper.TolerantFrames.HeapValidity
import Verification.Paper.TolerantFrames.PathTermSupports
import Verification.Paper.TolerantFrames.ElementSupports
import Verification.Paper.TolerantFrames.AtomSupports
import Verification.Paper.TolerantFrames.EverySupports
import Verification.Paper.TolerantFrames.PolaritySupports
import Verification.Paper.TolerantFrames.BelowMark
import Verification.Paper.TolerantFrames.PathSupports
import Verification.Paper.TolerantFrames.FreshnessCounterexample
import Verification.Paper.TolerantFrames.LiteralEquality
import Verification.Paper.TolerantFrames.PostconditionSyntax
import Verification.Paper.TolerantFrames.PostconditionScope
import Verification.Paper.TolerantFrames.PostconditionAdmission
import Verification.Paper.TolerantFrames.PostconditionRenaming
import Verification.Paper.TolerantFrames.PostconditionExamples
import Verification.Paper.TolerantFrames.IndexInstantiation
import Verification.Paper.TolerantFrames.Arithmetic
import Verification.Paper.TolerantFrames.Obstructions
import Verification.Paper.TolerantFrames.AllSupport
import Verification.Paper.TolerantFrames.Existentials
import Verification.Paper.TolerantFrames.Renaming
import Verification.Paper.TolerantFrames.RenamingAdmission
import Verification.Paper.TolerantFrames.PathReplacement
import Verification.Paper.TolerantFrames.ModalReplacement
import Verification.Paper.TolerantFrames.QuantifiedRules
import Verification.Paper.TolerantFrames.AliasExample
import Verification.Paper.TolerantFrames.Admission
import Verification.Paper.TolerantFrames.Derivations
import Verification.Paper.TolerantFrames.Transfer
import Verification.Paper.TolerantFrames.Scopes
import Verification.Paper.TolerantFrames.Loops
import Verification.Paper.TolerantFrames.CommandRules
import Verification.Paper.TolerantFrames.Commands
import Verification.Paper.TolerantFrames.Consequences
import Verification.Paper.TolerantFrames.Assertions
import Verification.Paper.TolerantFrames.SemanticRules
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
