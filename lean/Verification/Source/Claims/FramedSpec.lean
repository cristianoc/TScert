import Verification.Source.SourceRequests
import Verification.Source.Equations.Store
import Verification.Paper.TolerantFrames.ReadOnlyPublic
import Verification.Paper.TolerantFrames.ReadOnlyFits
import Verification.Paper.TolerantFrames.ReadOnlyFitsDecide
import Verification.Source.Claims.FramedFlow
import Verification.Source.Claims.FramedComponentChecks
import Verification.Source.ComponentWire
import Verification.Paper.TolerantFrames.ReadOnlyPending

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
- **An initial configuration** (`FramedSpec.Initial`, the draft's "The
  initialization as a premise"): a configuration at the history before any
  entry that fits the flow, is an entry, meets the invariants every step
  keeps (`States`), and whose module functions' closures are unfoldings of
  the plan's layout at least as deep as its budget, their outside captures
  meeting their types at its world and every world above it (`SlotsMet`).
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
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow LabelStore PositiveGraphs PositiveRules
open Verification.TolerantFrames.ReadOnly

namespace PassUnit
/-- The term that runs a program graph from `start`, frame `L`, receiver `d`,
its frames tagged `comp`, the component whose code it is. -/
def gotoOf (P : Program) (start : Nat) (L : List Tm) (d : Tm) (comp : ComponentTag) : Tm :=
  .goto (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler)) start L d comp
end PassUnit
open PassUnit (gotoOf)

/-- **A module function of the plan's layout**: its name, its realized
code, and per capture slot, in its request's order, the module function of
the component the slot names (`some`) or none for an outside slot, with the
type its request reads the slot at. -/
structure FramedLayoutEntry (ι : Type) where
  name : String
  code : Code
  slots : List (Option String × Ty ι)

/-- **A framed plan's proposals** (the draft, "The plan"): the component
`C`; the types a crossing reads read-only; the type outgoing values cross
at; the layout of the component's module functions; the number of the
function's parameters; and what the pass's check reads (the draft, "What
the pass checks"): the component's tags and the marks of its flow's sites,
the flow the solver proposes for the component's codes at those marks
(`checked`), each code's layout, the natives' codes, the component family
the declaration document describes (`family`, its `@clients` rows, its
codes' declared shapes), the component's module functions' codes, names, arities and the names
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
  /-- **The layout** (`FramedSpec.SlotsMet`): the component's module
  functions, each with its code and its slots' links and types. -/
  layout : List (FramedLayoutEntry ι)
  arity : Nat
  /-- **The read-only positions** (`roPositionsB`): position `j` is
  read-only where every function of `C` whose code is the request's
  realized code declares parameter `j` read-only throughout. -/
  roPositions : List Bool
  ofC : ComponentTag → Bool
  marks : List (Option Nat)
  checked : FFlow (markedPackage ofC marks)
  lay : List (Nat × Bool × Nat × Nat)
  host : Nat → Bool
  family : ComponentWire.Components
  codes : List Code
  names : List (String × Nat × List String)
  entries : List String
  theta : List (Option Verification.Kind × Footprints.Change)
  psi : List (Option Nat × Option Verification.Kind × Option PropKey × Footprints.Change)
  /-- The component's protocol as defined (`componentProtocol`) at every
  part of its flow's sites, each change but `keep`, computed once per
  component. -/
  psiDef : List (Option Nat × Option Verification.Kind × Option PropKey × Footprints.Change)
  /-- The refusal of the binding checks that read the component alone,
  with the evaluation of `componentBindingRefusal` at the plan's fields it
  is: computed once per component and shared by its plans; `none` where
  they pass. -/
  componentRefusal : { w : Option String // w = componentBindingRefusal checked lay codes C }
  framed : List (Nat × List Footprints.Footprint)
  /-- **Whether the request is checked at the contexts of its known calls**
  (the Read-only frames note, (B1)): its function is no entry and its
  token lies outside `O`, so the claim is about every call of its code that
  a program makes, each at a context of its code, and no region is read as
  protected. -/
  inner : Bool := false

namespace FramedSpec
variable {ι : Type} (spec : FramedSpec ι)

/-- Each site's mark, as the flow's `O` gives it. -/
abbrev mark : Nat → Mark := (markedPackage spec.ofC spec.marks).mark

/-- **The binding checks that read the component alone pass** where the
plan's refusal of them is none (proved, by the refusal's evaluation). -/
theorem componentRefusal_none (h : spec.componentRefusal.val = none) :
    componentBindingRefusal spec.checked spec.lay spec.codes spec.C = none :=
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

mutual
/-- **The closures a term holds**: every closure (`CallCode.graph`) of the
term, of its values' code and captures and of its runs, at any depth. By
cases on every constructor of `Tm` and `CallCode`. -/
def closuresOf : Tm → List Tm
  | .var _ | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ | .arr _ | .viewSpine .. => []
  | .invoke f r args => closuresOf f ++ closuresOf r ++ closuresOfs args
  | .construct f args => closuresOf f ++ closuresOfs args
  | .letE a b => closuresOf a ++ closuresOf b
  | .objAt _ .absent _ => []
  | .objAt _ (.view ..) _ => []
  | .objAt _ (.bound t r pre) _ => closuresOf t ++ closuresOf r ++ closuresOfs pre
  | .objAt fs (.graph n E K s caps k r c) i =>
    .objAt fs (.graph n E K s caps k r c) i :: (closuresOfs E ++ closuresOfs caps)
  | .makeAt .absent _ xs => closuresOfs xs
  | .makeAt (.view ..) _ xs => closuresOfs xs
  | .makeAt (.bound t r pre) _ xs => closuresOf t ++ closuresOf r ++ closuresOfs pre ++ closuresOfs xs
  | .makeAt (.graph _ E _ _ caps _ _ _) _ xs => closuresOfs E ++ closuresOfs caps ++ closuresOfs xs
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => closuresOf a
  | .indexAt a b | .writeAt _ a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
    closuresOf a ++ closuresOf b
  | .ite a b c | .setElem a b c => closuresOf a ++ closuresOf b ++ closuresOf c
  | .arrLit xs => closuresOfs xs
  | .goto E _ _ L d _ => closuresOfs E ++ closuresOfs L ++ closuresOf d
  | .frame E _ t L d _ _ _ => closuresOfs E ++ closuresOf t ++ closuresOfs L ++ closuresOf d
termination_by structural t => t
/-- The closures a list of terms holds. -/
def closuresOfs : List Tm → List Tm
  | [] => []
  | x :: xs => closuresOf x ++ closuresOfs xs
termination_by structural xs => xs
end

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

/-- Whether parameter `j` is a read-only position (`roPositions`). -/
def roPos (j : Nat) : Bool := spec.roPositions.getD j false

/-- **The type an entering step records argument `j` at**: its declared
type at a read-only position, and the writable type outgoing values cross
at otherwise. -/
def entryTy (r : SourceRequest σ ι) (j : Nat) : Ty ι :=
  if spec.roPos j then r.inputs.getD j spec.outType else spec.outType

open Classical in
/-- **The crossings in at an entering step of the realized code**: from a
term whose active frame runs outside code to one with one more call of `C`
active whose innermost run is the realized code, each argument `j` of the
call the step reduces (the first `arity` of them) crosses in at its entry
type (`entryTy`): its declared type where every function sharing the code
declares it read-only, the writable type otherwise. -/
noncomputable def entryXs (r : SourceRequest σ ι) (t t' : Tm) : List (Crossing spec.view.view) :=
  if spec.F.ofC spec.C (frameTag (activeFrame none t).1) = false ∧ entered none t' = some (realizedCode r) ∧
      depthC spec.F spec.C none t' = depthC spec.F spec.C none t + 1 then
    match (activeFrame none t).2 with
    | .invoke _ _ args | .construct _ args =>
      (args.take spec.arity).mapIdx fun j v => ⟨.into, spec.entryTy r j, v⟩
    | _ => []
  else []

/-- **What the checks give at a step** (the draft, "The binding checks" and
"The history of a program"): the flow's site of its fresh locations, its
arguments crossing in at an entering step, and every value
reaching outside code crossing out at `outType`. -/
noncomputable def chk (r : SourceRequest σ ι) (h : Heap) (t : Tm) (h' : Heap) (t' : Tm) :
    CheckData (spec.F.at spec.C) spec.view.view :=
  ⟨fun _ => stepSite spec.flow none t, spec.entryXs r t t' ++ actualXs spec.F spec.C spec.outType h t h' t'⟩

/-- **The frame's core** for a request. -/
noncomputable def core (r : SourceRequest σ ι) : FrameCore (Ty ι) :=
  ⟨spec.fam, spec.C, spec.view, spec.Θ, spec.chk r⟩

/-- **The frame's core and codes, entering nothing**: what an initial
configuration's fit and entry read, the frame's calls aside. -/
noncomputable def frame₀ (r : SourceRequest σ ι) : ClientFrame (Ty ι) where
  toFrameCore := spec.core r
  codes m := ∃ cx f, spec.flow.code m cx = some f
  enters _ _ _ _ := False
  start _ _ _ t g := g = bareStart (spec.core r).F (spec.core r).C t
  start_total _ _ _ _ := ⟨_, rfl⟩

/-- **The invariants every step keeps** (`ProgOk`'s, `WOk`'s): a reached
term, layout provenance at the plan's layouts, no run of `C` waiting as a
binding's body, and the residual invariant of the term and the heap. -/
def States (x₀ : Conf) : Prop :=
  wfS x₀.t = true ∧ (layP (layQ spec.fflow spec.lay) x₀.t = true ∧ HeapLay (layQ spec.fflow spec.lay) x₀.s.h) ∧
    NoPend (spec.F.at spec.C) x₀.t ∧ WOk x₀.t ∧ HeapW x₀.s.h

/-- **The closure `v` is an unfolding of the layout's module function `g`
at depth `i`** (the draft's `approx code i u`, `approxEnv`): at depth `0`
`null`; at depth `i + 1` a closure of `g`'s code whose capture slots are
`g`'s, each linked slot holding the named function unfolded at depth `i`
and each outside slot a value meeting the slot's type at every budget up
to `i`, at every world above `W₀` (`Above`). -/
def UnfoldsAt (G : NormalGraph ι) (lay : List (FramedLayoutEntry ι)) {N : Nat} (W₀ : WorldT N) :
    Nat → String → Tm → Prop
  | 0, _, v => v = .nul
  | i + 1, g, v => ∃ e ∈ lay, e.name = g ∧ ∃ fs ar s caps k rest comp oid,
      v = .objAt fs (.graph ar e.code.1 e.code.2 s caps k rest comp) oid ∧ caps.length = e.slots.length ∧
      ∀ (j : Nat) (y : Option String) (A : Ty ι) (c : Tm), e.slots[j]? = some (y, A) → caps[j]? = some c →
        match y with
        | some g' => UnfoldsAt G lay W₀ i g' c
        | none => ∀ b ≤ i, ∀ V : WorldT b, (∃ hb : b ≤ N, WExt (trunc b hb W₀) V) → meaning G A b V c

/-- **The module functions' closures meet the layout** (the draft's
`SlotsMet`): every closure of `C`'s code that `x₀`'s term or heap holds
whose code is a module function's of the layout is an unfolding of it at
a depth at least `x₀`'s budget, its outside captures meeting their types,
in the request's graph, at `x₀`'s world and every world above it. -/
def SlotsMet (r : SourceRequest σ ι) (x₀ : Conf) : Prop :=
  ∀ v ∈ closuresOf x₀.t ++ x₀.s.h.flatMap closuresOf, ∀ e ∈ spec.layout,
    ∀ fs ar s caps k rest comp oid, v = .objAt fs (.graph ar e.code.1 e.code.2 s caps k rest comp) oid →
      spec.F.ofC spec.C comp = true →
      ∃ i, x₀.s.n ≤ i ∧ UnfoldsAt (StoreView.graph r.types) spec.layout x₀.s.W (i + 1) e.name v

/-- **An initial configuration** (the draft, "The initialization as a
premise"): at the history before any entry, it fits the flow, is an entry,
meets the invariants every step keeps, and its module functions' closures
meet the layout. -/
def Initial (r : SourceRequest σ ι) (x₀ : Conf) : Prop :=
  (spec.frame₀ r).FitsAt spec.flow (x₀, bareStart (spec.core r).F (spec.core r).C x₀.t) ∧
    (spec.frame₀ r).Entry x₀.s.h x₀.t ∧ spec.States x₀ ∧ spec.SlotsMet r x₀

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

/-- **A call of the realized code the claim is about**: from an initial
configuration, an execution of steps keeping the obligation at the history
before any entry to `x`, and a step keeping it from `x` to `a₁`; an
entering step from outside code (`FrameCore.Entering`) unless the request
is checked at the contexts of its known calls (`inner`), whose calls are
every call a program makes. -/
def Called (r : SourceRequest σ ι) (x₀ : Conf) (n : Nat)
    (x a₁ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)) : Prop :=
  spec.Initial r x₀ ∧ Ex (spec.core r).KStep (fun _ => True) n (x₀, bareStart (spec.core r).F (spec.core r).C x₀.t) x ∧
    (spec.core r).KStep x a₁ ∧ (spec.inner = false → (spec.core r).Entering (realizedCode r) x a₁)

/-- **A call the claim is about is one execution** (proved). -/
theorem Called.ex {r : SourceRequest σ ι} {x₀ : Conf} {n : Nat}
    {x a₁ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)} (h : spec.Called r x₀ n x a₁) :
    Ex (spec.core r).KStep (fun _ => True) (n + 1) (x₀, bareStart (spec.core r).F (spec.core r).C x₀.t) a₁ :=
  h.2.1.snoc trivial h.2.2.1

/-- **A call of a request checked at its entry is a public call** (proved). -/
theorem Called.public {r : SourceRequest σ ι} {x₀ : Conf} {n : Nat}
    {x a₁ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)} (h : spec.Called r x₀ n x a₁)
    (hi : spec.inner = false) : (spec.core r).PublicCall (spec.Initial r) (realizedCode r) x₀ n x a₁ :=
  ⟨h.1, h.2.1, h.2.2.2 hi⟩

/-- **An entry of the request at a program's state `a₂`**: `a₂` realizes a
call of the realized code the claim is about (`Called`), at the world `W`,
the heap `h` and the request's run `t` at the slots it reached. -/
def EntryAt (r : SourceRequest σ ι) (k : Nat) (W : WorldT k) (h : Heap) (t : Tm)
    (a₂ : Conf × Ghost ((spec.core r).F.at (spec.core r).C)) : Prop :=
  ∃ x₀ n x a₁ L d, spec.Called r x₀ n x a₁ ∧
    spec.RealizedAt r a₁ a₂ L d ∧ a₂.1.s.n = k ∧ HEq a₂.1.s.W W ∧ h = a₂.1.s.h ∧
    t = gotoOf r.program r.start L d r.comp

/-- **The history a framed call starts from**: the program's at the entry,
its sets truncated to the one of the entered call (the protected set), the
crossing in recorded at the entering step. -/
def truncate {P : Package} (g : Ghost P) : Ghost P := { g with A := [fun l => g.Prot l] }

omit [Labels ι] in
/-- **The truncation keeps the protected set** (proved). -/
theorem truncate_prot {P : Package} (g : Ghost P) (l : Nat) : (truncate g).Prot l ↔ g.Prot l := by
  simp only [Ghost.Prot, truncate, List.mem_singleton, exists_eq_left]
  exact ⟨fun h => h.elim id .inr, .inl⟩

omit [Labels ι] in
/-- **The truncation grows a history inside a call** (proved,
`truncate_prot`): with a call active, the one set is the protected set,
and `B` and `E` are kept. -/
theorem truncate_grows {P : Package} {g : Ghost P} (hA : 1 ≤ g.A.length) : Grows 1 g (truncate g) :=
  ⟨Nat.one_pos, hA, by simp [truncate], rfl, fun l h => (truncate_prot g l).mpr h, fun _ h => h⟩

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

/-- **An initial configuration fits the flow** (named premise of the
claim): its term fits `O` at a position of outside code, and its heap
meets the flow, at the history before any entry. -/
def InitialFits (r : SourceRequest σ ι) : Prop :=
  ∀ x, spec.Initial r x → (spec.frame r).FitsAt spec.flow (x, bareStart (spec.core r).F (spec.core r).C x.t)

/-- **An initial configuration is an entry** (named premise of the claim):
code provenance, the call discipline, outside code lowered source and
closed values. -/
def InitialEntry (r : SourceRequest σ ι) : Prop := ∀ x, spec.Initial r x → (spec.frame r).Entry x.s.h x.t

/-- **Every initial configuration fits the flow** (proved, by the
definition of `Initial`). -/
theorem initialFits (r : SourceRequest σ ι) : spec.InitialFits r := fun _ hx => hx.1

/-- **Every initial configuration is an entry** (proved, by the definition
of `Initial`). -/
theorem initialEntry (r : SourceRequest σ ι) : spec.InitialEntry r := fun _ hx => hx.2.1

/-- The frame's sites are the plan's family's at its component: equality
of them is decided. -/
instance (r : SourceRequest σ ι) : DecidableEq ((spec.frame r).F.at (spec.frame r).C).Site :=
  show DecidableEq (spec.fam.family.at spec.C).Site from inferInstance

/-- The frame's sites are hashed by their numbers. -/
instance (r : SourceRequest σ ι) : Hashable ((spec.frame r).F.at (spec.frame r).C).Site :=
  show Hashable (spec.fam.family.at spec.C).Site from inferInstance

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
  let layout ← spec.layout.mapM fun e => do
    return { e with slots := ← e.slots.mapM fun (y, A) => do return (y, ← relabel A) }
  return { spec with readOnly := ← relabel spec.readOnly, outType := ← relabel spec.outType, layout }

end Verification.SourceClaimJson
