import Verification.Source.Claims.FramedBinding
import Verification.Source.Claims.FlowProbe

/-! Controls for the binding checks of a framed plan's flow
(`TolerantFrames.ReadOnly.codesCoverB`, `allocSomeB`, `entryFnB`,
`agreeB`, the draft "Accepting a unit through the read-only frame", "The
binding checks"). Each check passes a flow bound to the code it is given
and refuses a forged one:

- **A flow omitting a code** (`codesCoverB`): a frame of an omitted code
  reads its allocation sites as outside storage (`allocOf`), so its
  allocations would not be `C`'s storage.
- **An allocation site `none`** (`allocSomeB`, the review's
  `AstraR3.lean` flow, which `FFlow.check`, `marksB` and `entryB` pass):
  at a node key or by default.
- **A signature at an entry slot that is not a sibling's** (`entryFnB`).
- **A realized code whose proposal differs from its request's at a body
  label** (`agreeB`, which `realizedFlowB` reads): its value set, or its
  allocation site at a body node's continuation and handler. -/
namespace Verification.SourceClaimJson.FramedBindingControls
open Verification TolerantFrames.ReadOnly ControlFlow

/-- The component `0`, outside code seeing outside storage only. -/
private abbrev Pk : TolerantFrames.ReadOnly.Package := markedPackage (· == some 0) [none]

/-- A code of one node returning `undefined`. -/
private def m₀ : Code := ([.undef], [(.ret, none)])
/-- The same code behind a prologue node. -/
private def m₁ : Code := ([.undef, .undef], [(.ret, none), (.ret, none)])

private def node (val : Sites Pk) (fn : Array (Option Nat) := #[]) : FNode Pk :=
  { env := #[], dflt := [], val := val, fn := fn, vfn := none }

private def code (val : Sites Pk) (obj : Option Nat := some 3) (allocs : List (NodeKey × Option Nat × Option Nat) := [])
    (fn : Array (Option Nat) := #[]) : FCode Pk :=
  { nodes := #[node val fn], dflt := node [], alloc := ⟨obj, some 4⟩, sigs := #[⟨m₀, 0, 0, false, 0⟩], ret := [],
    tok := some 5, allocs := allocs }

private def flowOf (codes : List (Code × List (Nat × FCode Pk))) : FFlow Pk := { O := [none], heap := [], codes := codes }

/-! ## The codes -/

#guard codesCoverB (flowOf [(m₀, [(entryCx, code [])])]) [m₀]
-- a flow omitting the realized code
#guard !codesCoverB (flowOf [(m₀, [(entryCx, code [])])]) [m₀, m₁]
-- a code with a proposal at another context only
#guard !codesCoverB (flowOf [(m₀, [(1, code [])])]) [m₀]

/-! ## The allocation sites -/

#guard allocSomeB (flowOf [(m₀, [(entryCx, code [])])])
-- an object site `none` by default
#guard !allocSomeB (flowOf [(m₀, [(entryCx, code [] (obj := none))])])
-- an array site `none` at a node key
#guard !allocSomeB (flowOf [(m₀, [(entryCx, code [] (allocs := [((.ret, none), some 6, none)]))])])
-- at a context other than the entry's
#guard !allocSomeB (flowOf [(m₀, [(entryCx, code []), (1, code [] (obj := none))])])

/-! ## The entry's signatures -/

-- slot 1 names a signature: allowed where it is a sibling's slot
#guard entryFnB (flowOf [(m₀, [(entryCx, code [] (fn := #[none, some 0]))])]) m₀ 0 [1]
#guard !entryFnB (flowOf [(m₀, [(entryCx, code [] (fn := #[none, some 0]))])]) m₀ 0 [2]

/-! ## A realized code's proposals at body labels -/

#guard agreeB (flowOf [(m₁, [(entryCx, code [some 1])]), (m₀, [(entryCx, code [some 1])])]) m₁ m₀ m₀.2 1
-- a different value set at the body's label
#guard !agreeB (flowOf [(m₁, [(entryCx, code [some 1])]), (m₀, [(entryCx, code [some 2])])]) m₁ m₀ m₀.2 1
-- a different allocation site at the body node's continuation and handler
#guard !agreeB (flowOf [(m₁, [(entryCx, code [some 1] (allocs := [((.ret, none), some 7, some 4)]))]),
  (m₀, [(entryCx, code [some 1])])]) m₁ m₀ m₀.2 1
-- the request's code without a proposal at a context of the realized code
#guard !agreeB (flowOf [(m₁, [(entryCx, code [some 1]), (1, code [some 1])]), (m₀, [(entryCx, code [some 1])])])
  m₁ m₀ m₀.2 1

end Verification.SourceClaimJson.FramedBindingControls
