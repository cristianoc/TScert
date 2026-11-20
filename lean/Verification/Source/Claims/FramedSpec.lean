import Verification.Source.SourceRequests
import Verification.Source.Equations.Store
import Verification.Paper.TolerantFrames.ReadOnlyPublic
import Verification.Paper.TolerantFrames.ReadOnlyFits
import Verification.Paper.TolerantFrames.ReadOnlyFitsDecide
import Verification.Source.Claims.FramedFlow
import Verification.Source.Claims.FramedComponentChecks
import Verification.Source.ComponentWire

/-! # A framed plan's proposals and the frame they define

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The frame of a request"). A framed
plan carries, beside its request, a `FramedSpec`: the component `C`, the
read-only types, the type outgoing values cross at, the realm's heap, the
initialization's code, the function's arity and what the pass's check
reads, its component's flow among them; the family of components with its
sites numbered, the client obligation `Θ` and the finite flow of sites are
defined from them (`FramedSpec.fam`, `FramedSpec.Θ`, `FramedSpec.fflow`).
From them and the request, `FramedSpec.frame` defines the client frame the
plan is accepted under:

- **The realized code** (`realizedCode`): the request's node lists behind
  the receiver's prologue (`PassUnit.dropReceiver`), at which a call of the
  function's closure starts.
- **The checks' data** (`FramedSpec.chk`): the sites the flow gives a
  step's fresh locations (`stepSite`), no keys, and the crossings of a
  step: at an entering step of the realized code its arguments crossing in
  at their declared types, and every value reaching outside code crossing
  out (`actualXs`).
- **An initial configuration** (`FramedSpec.Initial`): the realm's heap and
  the initialization run in front of a client term of lowered outside
  source with the exports bound.
- **The realization** (`RealizedAt`): from an entering step of the realized
  code, the prologue's steps to the first state whose innermost run is the
  realized code at the request's start.
- **The frame** (`FramedSpec.frame`): its entries are the realizations of
  the public calls of the realized code (`EntryAt`), at the program's world,
  heap and slots, its term the request's run at those slots; its start at
  such an entry the program's history truncated to the one set of the
  entered call, and the history before any entry otherwise (total,
  `FramedSpec.start_total`). -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly

namespace PassUnit
/-- The term that runs a program graph from `start`, frame `L`, receiver `d`,
its frames tagged `comp`, the component whose code it is. -/
def gotoOf (P : Program) (start : Nat) (L : List Tm) (d : Tm) (comp : ComponentTag) : Tm :=
  .goto (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler)) start L d comp
end PassUnit
open PassUnit (gotoOf)

/-- **A framed plan's proposals** (the draft, "The plan"): the component
`C`; the types a crossing reads read-only; the type outgoing values cross
at; the realm's heap; the initialization's code and the order in which it
allocates the module functions' closures; the number of the function's
parameters; and what the pass's check reads (the draft, "What
the pass checks"): the component's tags and the marks of its flow's sites,
the flow the solver proposes for the component's codes at those marks
(`checked`), each code's layout, the natives' codes, the component family
the declaration document describes (`family`, its `@clients` rows, its
codes' declared shapes and its bodies' events), the checked file's name and
functions, the component's module functions' codes, names, arities and the names
their slots read, its entries, the wire's client obligation by kind
(`theta`) and protocol by site and kind (`psi`), the component's protocol
as defined (`psiDef`), the refusal of the checks that read the component
alone with the evaluation it is (`componentRefusal`), and each framed call
node
of the main graph with the supports its frame keeps. The family of
components, the client obligation and the finite flow the frame reads are
defined from them (`FramedSpec.fam`, `FramedSpec.Θ`, `FramedSpec.fflow`). -/
structure FramedSpec (ι : Type) where
  C : Nat
  readOnly : List (Ty ι)
  outType : Ty ι
  realm : Heap
  initE : List Tm
  initK : List (Continuation × Option Target)
  /-- The module functions in the order the initialization allocates their
  closures, by name. -/
  initOrder : List String
  arity : Nat
  ofC : ComponentTag → Bool
  marks : List (Option Nat)
  checked : FFlow (markedPackage ofC marks)
  lay : List (Nat × Bool × Nat × Nat)
  host : Nat → Bool
  family : ComponentWire.Components
  file : String
  fns : List (String × Span × Bool)
  codes : List Code
  names : List (String × Nat × List String)
  entries : List String
  theta : List (Option Verification.Kind × Footprints.Change)
  psi : List (Option Nat × Option Verification.Kind × Footprints.Change)
  /-- The component's protocol as defined (`componentProtocol`) at every
  part of its flow's sites, each change but `keep`, computed once per
  component. -/
  psiDef : List (Option Nat × Option Verification.Kind × Footprints.Change)
  /-- The refusal of the binding checks that read the component alone,
  with the evaluation of `componentBindingRefusal` at the plan's fields it
  is: computed once per component and shared by its plans; `none` where
  they pass. -/
  componentRefusal : { w : Option String // w = componentBindingRefusal checked lay codes names entries
    realm initOrder initE initK family file fns C }
  framed : List (Nat × List Footprints.Footprint)

namespace FramedSpec
variable {ι : Type} (spec : FramedSpec ι)

/-- Each site's mark, as the flow's `O` gives it. -/
abbrev mark : Nat → Mark := (markedPackage spec.ofC spec.marks).mark

/-- **The binding checks that read the component alone pass** where the
plan's refusal of them is none (proved, by the refusal's evaluation). -/
theorem componentRefusal_none (h : spec.componentRefusal.val = none) :
    componentBindingRefusal spec.checked spec.lay spec.codes spec.names spec.entries spec.realm
      spec.initOrder spec.initE spec.initK spec.family spec.file spec.fns spec.C = none :=
  spec.componentRefusal.property ▸ h

/-- **The family of a framed plan**: the one component `C`, each site of its
code marked as the flow marks it (`oneComponent`). -/
def fam : NumberedFamily := oneComponent spec.C spec.mark

/-- **The client obligation of a framed plan**: the wire's change per kind
(`protocolOfKinds`), which `clientsB` checks against the `@clients` rows. -/
noncomputable def Θ : Protocol (spec.fam.family.at spec.C) := protocolOfKinds spec.theta

/-- **The finite flow of a framed plan** (which the binding checks decide):
the checked flow, its sites renamed into the family's (`FFlow.mapSites`). -/
noncomputable def fflow : FFlow (spec.fam.family.at spec.C) :=
  spec.checked.mapSites (oneComponent.site spec.C spec.mark) (·.1)
end FramedSpec

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **The realized code of a request** of a function declared without
`this` (`PassUnit.dropReceiver`): its node lists behind one prologue node,
which evaluates `undefined` and continues at the request's start with the
frame past the receiver. -/
def realizedCode (r : SourceRequest σ ι) : Code :=
  (r.program.map (·.expression) ++ [.undef],
    r.program.map (fun n => (n.continuation, n.handler)) ++
      [(.effect ⟨r.start, some ((List.range (r.inputs.length + 1)).map (· + 1))⟩, none)])

namespace FramedSpec
variable (spec : FramedSpec ι)

/-- **The flow of a framed plan**: the flow its finite flow stands for. -/
noncomputable def flow : Flow (spec.fam.family.at spec.C) := spec.fflow.flow

/-- **The type view of a framed plan**: a type is read-only where the plan
names it so, and a type's children are itself, so a read-only type is
read-only throughout. -/
def view : ViewOver (Ty ι) := ⟨fun t _ => t, fun t => t ∈ spec.readOnly, fun _ _ h => h⟩

/-- The family of the plan. -/
abbrev F : Family := spec.fam.family

open Classical in
/-- **The crossings in at an entering step of the realized code**: from a
term whose active frame runs outside code to one with one more call of `C`
active whose innermost run is the realized code, each argument of the call
the step reduces (the first `arity` of them) crosses in at its declared
type. -/
noncomputable def entryXs (r : SourceRequest σ ι) (t t' : Tm) : List (Crossing spec.view.view) :=
  if spec.F.ofC spec.C (frameTag (activeFrame none t).1) = false ∧ entered none t' = some (realizedCode r) ∧
      depthC spec.F spec.C none t' = depthC spec.F spec.C none t + 1 then
    match (activeFrame none t).2 with
    | .invoke _ _ args | .construct _ args =>
      ((args.take spec.arity).zip (r.inputs.take spec.arity)).map fun (v, T) => ⟨.into, T, v⟩
    | _ => []
  else []

/-- **What the checks give at a step** (the draft, "The binding checks" and
"The history of a program"): the flow's site of its fresh locations, no
keys, its arguments crossing in at an entering step, and every value
reaching outside code crossing out at `outType`. -/
noncomputable def chk (r : SourceRequest σ ι) (h : Heap) (t : Tm) (h' : Heap) (t' : Tm) :
    CheckData (spec.F.at spec.C) spec.view.view :=
  ⟨fun _ => stepSite spec.flow none t, fun _ => none,
    spec.entryXs r t t' ++ actualXs spec.F spec.C spec.outType h t h' t'⟩

/-- **The frame's core** for a request. -/
noncomputable def core (r : SourceRequest σ ι) : FrameCore (Ty ι) :=
  ⟨spec.fam, spec.C, spec.view, spec.Θ, spec.chk r⟩

/-- **An initial configuration**: the realm's heap, and the initialization
run in front of a client term of lowered outside source whose one free
variable is the exports. -/
def Initial (x₀ : Conf) : Prop :=
  ∃ client, x₀.s.h = spec.realm ∧ x₀.t = .letE (.goto spec.initE spec.initK 0 [] .undef (some spec.C)) client ∧
    LoweredSrc (spec.F.ofC spec.C) client ∧ Scoped 1 client

/-- **The realization of an entering step** (the draft, "Realization",
`RealizedAt`): `a₁`'s innermost run is the realized code at its prologue's
label, the closure's entry, and `a₂` is the first state after it, along
steps keeping the obligation, whose innermost run is the realized code at
the request's start, with slots `L`, default `d` and the request's tag. -/
def RealizedAt (r : SourceRequest σ ι) (a₁ a₂ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)) (L : List Tm)
    (d : Tm) : Prop :=
  (∃ L₁ d₁ c₁, innermostGoto a₁.1.t = some (realizedCode r, r.program.length, L₁, d₁, c₁)) ∧
    (∃ j, Ex (spec.core r).KStep
      (fun a => ¬ ∃ L' d' c', innermostGoto a.1.t = some (realizedCode r, r.start, L', d', c')) j a₁ a₂) ∧
    innermostGoto a₂.1.t = some (realizedCode r, r.start, L, d, r.comp)

/-- **An entry of the request at a program's state `a₂`**: `a₂` realizes a
public call of the realized code, at the world `W`, the heap `h` and the
request's run `t` at the slots it reached. -/
def EntryAt (r : SourceRequest σ ι) (k : Nat) (W : WorldT k) (h : Heap) (t : Tm)
    (a₂ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)) : Prop :=
  ∃ x₀ n x a₁ L d, (spec.core r).PublicCall spec.Initial (realizedCode r) x₀ n x a₁ ∧
    spec.RealizedAt r a₁ a₂ L d ∧ a₂.1.s.n = k ∧ HEq a₂.1.s.W W ∧ h = a₂.1.s.h ∧
    t = gotoOf r.program r.start L d r.comp

/-- **The history a framed call starts from**: the program's at the entry,
its sets truncated to the one of the entered call (the protected set), the
crossing in recorded at the entering step. -/
def truncate {P : Package} (g : Ghost P) : Ghost P := { g with A := [fun l => g.Prot l] }

/-- **The frame of a framed plan** (the draft, `FramedSpec.frame`). -/
noncomputable def frame (r : SourceRequest σ ι) : ClientFrame (Ty ι) where
  toFrameCore := spec.core r
  codes m := ∃ cx f, spec.flow.code m cx = some f
  enters k W h t := ∃ a₂, spec.EntryAt r k W h t a₂
  start k W h t g := (∃ a₂, spec.EntryAt r k W h t a₂ ∧ g = truncate a₂.2) ∨
    ((¬ ∃ a₂, spec.EntryAt r k W h t a₂) ∧ g = bareStart (spec.core r).F (spec.core r).C t)
  start_total k W h t := by
    by_cases he : ∃ a₂, spec.EntryAt r k W h t a₂
    · obtain ⟨a₂, ha⟩ := he
      exact ⟨_, .inl ⟨a₂, ha, rfl⟩⟩
    · exact ⟨_, .inr ⟨he, rfl⟩⟩

/-- The frame's sites are the plan's family's at its component: equality
of them is decided. -/
instance (r : SourceRequest σ ι) : DecidableEq ((spec.frame r).F.at (spec.frame r).C).Site :=
  show DecidableEq (spec.fam.family.at spec.C).Site from inferInstance

/-- The frame's sites are hashed by their numbers. -/
instance (r : SourceRequest σ ι) : Hashable ((spec.frame r).F.at (spec.frame r).C).Site :=
  show Hashable (spec.fam.family.at spec.C).Site from inferInstance

omit [Labels ι] in
/-- **An initial configuration's client is lowered outside source**
(proved, by definition). -/
theorem initial_lowered {x₀ : Conf} (hx : spec.Initial x₀) :
    ∀ client, x₀.t = .letE (.goto spec.initE spec.initK 0 [] .undef (some spec.C)) client →
      LoweredSrc (spec.F.ofC spec.C) client := by
  obtain ⟨c, -, ht, hc, -⟩ := hx
  intro client hcl
  rw [ht] at hcl
  cases hcl
  exact hc

/-- **The frame's entries are the realized public calls** (proved, by
definition). -/
theorem frame_enters (r : SourceRequest σ ι) {k : Nat} {W : WorldT k} {h : Heap} {t : Tm} :
    (spec.frame r).enters k W h t ↔ ∃ a₂, spec.EntryAt r k W h t a₂ := Iff.rfl

end FramedSpec
end

open EquationGraphs EquationStore in
/-- A framed plan's proposals over the frozen equations: its types
relabeled. -/
def FramedSpec.over (F : Frozen) (spec : FramedSpec Tree) :
    Except String (FramedSpec (CheckedLabel F.equations F.primitive)) := do
  return { spec with readOnly := ← relabel spec.readOnly, outType := ← relabel spec.outType }

end Verification.SourceClaimJson
