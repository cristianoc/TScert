import Verification.Source.Claims.FramedBinding
import Verification.Source.Claims.FlowProbe

/-! Controls for the binding checks of a framed plan's flow
(`TolerantFrames.ReadOnly.codesCoverB`, `allocSomeB`, `entryFnB`,
`agreeB`, `compB`, the draft "Accepting a unit through the read-only frame", "The
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
  allocation site at a body node's continuation and handler.
- **Two sites for one body allocation** (`allocCanonB`, the fourth
  review's finding on P22's `const c = { i: 0 }`): a realized code
  allocating at a site other than its body's canonical one, which a
  numbering per code gives.
- **A wire $`\Theta_C`$ other than the source's** (`clientsB`): one changing
  a kind no row states, one keeping a kind a row extends, and a row stating
  a path key (the restriction "@clients by kind").
- **A wire $`\Psi_C`$ below its definition** (`protocolAtLeastB`): one
  keeping a part the component's charges change.
- **A forged request tag** (`compB`): a request tagged with another
  component, or with outside code's tag, whose frames would not run `C`'s
  code. -/
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

/-! ## One site per body allocation -/

/-- The realized code `m₁`'s body is `m₀`. -/
private def body (m : Code) : Code := if m = m₁ then m₀ else m

-- `m₀`'s one node key `(ret, none)` is the first occurrence: sites 10 and 11
#guard canonSite 10 [m₀] m₀ (.ret, none) false == 10 && canonSite 10 [m₀] m₀ (.ret, none) true == 11
-- both codes at the canonical sites of the body's occurrence
#guard allocCanonB (P := Pk) id 10 [m₀] body
  (flowOf [(m₁, [(entryCx, code [] (obj := some 10) (allocs := [((.ret, none), some 10, some 11)]))]),
    (m₀, [(entryCx, code [] (obj := some 10) (allocs := [((.ret, none), some 10, some 11)]))])])
-- the realized code at a site of its own, as a numbering per code gives it
#guard !allocCanonB (P := Pk) id 10 [m₀] body
  (flowOf [(m₁, [(entryCx, code [] (obj := some 12) (allocs := [((.ret, none), some 12, some 13)]))]),
    (m₀, [(entryCx, code [] (obj := some 10) (allocs := [((.ret, none), some 10, some 11)]))])])

/-! ## The client obligation -/

/-- A row extending the array spines of `this`'s class, and one stating a
path key. -/
private def spineRow : ComponentWire.Clients :=
  ⟨"m", "T", (0, 0), true, [(.cls ⟨false, true, false⟩, .extend)]⟩
private def pathRow : ComponentWire.Clients :=
  ⟨"m", "T", (0, 0), true, [(.path 0 [] (.str "items"), .extend)]⟩

/-- The obligation of the spine row, by kind. -/
private def spineTheta : Protocol Pk := fun p => if p.kind = some .spine then .extend else .keep

#guard clientsB (P := Pk) [none, some 0] spineTheta [spineRow]
-- a wire obligation changing a kind no row states
#guard !clientsB (P := Pk) [none, some 0] (fun _ => .any) [spineRow]
-- a wire obligation keeping the spines the row extends
#guard !clientsB (P := Pk) [none, some 0] (fun _ => .keep) [spineRow]
-- a row stating a path key
#guard !clientsB (P := Pk) [none, some 0] (rowsTheta [pathRow]) [pathRow]
-- no row states one: read-only
#guard clientsB (P := Pk) [none, some 0] (fun _ => .keep) [{ spineRow with stated := false }]

/-! ## The protocol -/

-- the wire's protocol at least the charges' at every part of the flow's sites
#guard protocolAtLeastB (P := Pk) [none, some 0] (probeProtocol [some .field] []) (fun _ => .any)
-- a wire protocol keeping the field parts the charges change
#guard !protocolAtLeastB (P := Pk) [none, some 0] (probeProtocol [some .field] []) (fun _ => .keep)

/-! ## The component -/

/-- A request of one node returning `undefined`, its frames tagged with the
component `0`. -/
private def req₀ : SourceExtraction.SourceRequest EquationStore.State EquationGraphs.Tree :=
  { types := { doc := #[] }, program := [], claims := [], result := [], start := 0, inputs := [], obligations := [],
    async := false, stated := none, comp := some 0 }

-- a request tagged with its component
#guard compB 0 req₀
-- a forged request tag: another component's, or outside code's
#guard !compB 0 { req₀ with comp := some 1 }
#guard !compB 0 { req₀ with comp := none }

end Verification.SourceClaimJson.FramedBindingControls
