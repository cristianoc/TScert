# Parity interfaces

## The existing mechanism this extends

This design fixes the interfaces between legs 2–5 of the parity plan. The intended rules are those of [the tolerant-frames note](tolerant-frames-note/note.tex), §§3–7, with linear arithmetic, constant right shifts, constant masks, and the string observations used by the existing pretext checks.

The implementation mechanisms being extended are:

| Concern | Existing Lean definitions | Owning document |
|---|---|---|
| States and admissibility | `WorldT`, `roles`, `WExt`, `HeapOk`; `TolerantFrames.IndexedHeap`, `Admissible` | [Location kinds](location-kinds.md), [the note](tolerant-frames-note/note.tex), §§2–3 |
| Regions, effects and rebasing | `Footprints.Region`, `Change.Holds`, `Post`, `Supported`, `Closed`, `RebaseEvidence`, `RebaseOk`, `Post.compose_at` | [Footprints](../FOOTPRINTS.md) |
| Call specifications | `CallEffects.Effect`, `PromiseWith`, `NativeContract`, `ConstructPromise` | [Source contracts](../SOURCE-CONTRACTS.md), [inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification) |
| Assertions and consequences | `HeapKnowledge.Term`, `IndexFact`, `Knowledge`, `StepRelation`; `Linear.Step`, `Linear.check`; `TolerantFrames.Assertion`, `Box` | [Arithmetic](../ARITHMETIC.md), [Footprints](../FOOTPRINTS.md), the note §§4–7 |
| Actual checking visits | `SinglePass.VisitRecord`, `StepGrades`, `visitStep`, `recordsAdmit`; `SinglePassClose.run_rebound_of_records` | [One-pass checking](../SOURCE-ELABORATION.md#checking-a-unit-in-one-pass) |
| Typed-array operations | `Tm`, `Step`; `CallEffects.ElementKind`, `ExactWrite`; `Kinds.ViewWrite`, `ViewWriteOf` | [Element writes](../FOOTPRINTS.md#element-writes), the note §6 |

The five interfaces below extend these mechanisms. They introduce one interpretation of regions, one assertion semantics, and one checked consequence judgment. Primitive operational rules supply effects and exact posts to that judgment.

The declaration blocks are **interface signatures and proof obligations**, not checked Lean source. Bodies and proofs are intentionally omitted. `NEW`, `CHANGED`, and `UNCHANGED` describe each declaration’s relationship to the inspected implementation. Constructor schemas use explicitly described notation where spelling every arena lookup would obscure the rule; the implementation uses the indexed references specified below.

Definitions generic in graph labels, stores, or their type-class instances carry `@[nospecialize]`. Each module places its structures and inductives before proofs. No interface introduces an axiom, `sorry`, version field, mode selector, or alternative acceptance route.

## Scope and fixed decisions

The arithmetic scope is:

- Integer linear consequences, with definedness and the JavaScript numeric premises required by each operational step.
- Signed right shift by a constant in `[0, 31]`, on operands proved in `[0, 2^31 − 1]`.
- Bitwise-and with a constant in `[0, 2^31 − 1]`, on operands in that same range.
- UTF-16 string length, string element reads, concatenation length on normal completion, and the existing string-length-plus-one boundary case.

Multiplication by a constant is linear. Products of two variables, left shift, and bitwise-or are outside this interface.

Closure specifications over captured values are separate work. Exact typed-array updates are internal operational posts; the public contract language has no typed-update assertion.

The primitive formats are the four already represented by `ElementKind` and `tools/library-types.mts`: `uint8`, `uint16`, `int32`, and `float64`. Additional formats require their own representation and conversion extension. This is an explicit fragment boundary.

## I1. Entry-relative regions and exit specifications

### The existing mechanism this extends

This interface extends `Footprints.Region.mem`, `Allowed`, `Post`, `Supported`, `Closed.fp`, and `TolerantFrames.Action`, together with the region and frame portions of `CallEffects.Effect`.

[Footprints](../FOOTPRINTS.md) owns their operational meaning. The note counterpart is §3’s regions, effect action, inclusion and rigidity, and §6’s independent normal and exceptional effects.

### State and role interpretation

Keep `TolerantFrames.IndexedHeap`. Its world and heap remain the semantic state used by the modality. Environment typing remains a premise supplied by the graph interpretation through `EnvOk`; it is not duplicated inside the heap record.

The correspondence theorem packages:

- `IndexedHeap.ok` as W1–W3 and heap-contract satisfaction;
- `EnvOk` and valid roots as the environment part of W3–W4;
- environment agreement on the assertion’s free variables;
- `Admissible` as truncation followed by world extension.

Modal statements quantify over the existing indexed states. They hold at fixed environments; fresh operational bindings are connected by substitution and scope evidence. No statement identifies environment extension with equality of the pass’s de Bruijn slot numbers.

Region interpretation is heap-only. A location's contents decide its category: an array store, a view store (the tagged contents of I3), or a value location. The connecting theorem gives the note's role-based meaning: under `HeapOk n W h`, every allocated location's contents category equals its role's category, and under `Admissible` an old location keeps its contents category. Roles remain in the world, admissibility, contracts, valid-reference proofs and assertion-level separation evidence; no region predicate takes a role map.

```lean
namespace Verification

/-- NEW: disjoint categories; every allocated role has exactly one. -/
inductive Category where
  | value
  | array
  | view
  deriving DecidableEq, Repr

/-- NEW: category of a role. -/
def Role.category : Role → Category

end Verification

namespace Verification.Footprints

/-- NEW: a selector is a finite subset of the three categories. -/
structure Selector where
  value : Bool
  array : Bool
  view : Bool
  deriving DecidableEq, Repr

/-- NEW: membership, inclusion and disjointness of selectors. -/
def Selector.has : Selector → Category → Bool
def Selector.sub : Selector → Selector → Bool
def Selector.disjoint : Selector → Selector → Bool

/-- NEW: the named selectors used by annotations and normalization. -/
def Selector.values : Selector
def Selector.arrays : Selector
def Selector.views : Selector
def Selector.stores : Selector
def Selector.all : Selector

/-- NEW: whether a class region selects a location holding `v`, by the
contents category of `v`. -/
def Selector.selects : Selector → Val → Bool

/-- NEW: the connecting theorem. -/
theorem HeapOk.category {n : Nat} {W : WorldT n} {h : Heap}
    (hok : HeapOk n W h) {l : Nat} {r : Role} {v : Val}
    (hr : roleAt W l = some r) (hv : h[l]? = some v) :
    contentsCategory v = r.category

end Verification.Footprints
```

`Role.field`, `.cell`, `.elem`, and `.identity` belong to `value`; `.store .array` belongs to `array`; every `.store (.view …)` belongs to `view`.

`stores` selects `array ∪ view`. `values`, `arrays`, and `views` are pairwise disjoint. `stores` and `views` overlap. Inclusion and disjointness inspect the three category bits; unequal selector names prove nothing.

### Regions

Keep the existing region constructors, replacing `Cls` by `Selector`. Add an explicit selected-store constructor so typed stores need no fake field:

```lean
namespace Verification.Footprints

/-- CHANGED: `cls` and `inCls` take selectors; `store` selects
an ordinary or typed store independently of its representation. -/
inductive Region where
  | field (x : Nat) (k : PropKey)
  | own (x : Nat)
  | elems (x : Nat)
  | cls (c : Selector)
  | all
  | path (x : Nat) (p : List String) (k : PropKey)
  | pathOwn (x : Nat) (p : List String)
  | pathElems (x : Nat) (p : List String)
  | store (x : Nat) (p : List String)
  | cell (binding : String)
  | inCls (r : Region) (c : Selector)
  deriving DecidableEq, Repr

/-- UNCHANGED signature: heap-only. A class region reads the contents
category of the entry heap's location (`Selector.selects`). -/
def Region.mem :
  Env → Heap → Region → Nat → Bool

/-- UNCHANGED: an effect is a finite list of region/change entries. -/
abbrev Footprint := List (Region × Change)

/-- NEW: the note's store-plus-cells region, represented without
a second region interpreter. -/
def storeAndCells (x : Nat) (p : List String)
    (δ : Change) : Footprint
```

`storeAndCells x p δ` expands to `[(.store x p, δ), (.pathElems x p, δ)]`. The note’s `x[*]` always includes the store.

Mapping of existing constructors:

| Existing form | Interpretation |
|---|---|
| `field`, `path` | The selected own location; failed paths select nothing. |
| `own`, `pathOwn` | The object’s own locations under the existing object interpretation. |
| `elems`, `pathElems` | Cells listed by the selected store; they exclude the store location. |
| `cls .value` | `cls Selector.values`. |
| `cls .store` | `cls Selector.stores`. |
| `all` | Every allocated entry location. |
| `inCls r c` | Intersection with the role selector. |
| `cell binding` | Its existing conservative value-category meaning. Exact module-cell selection is separate work. |
| `path x p arrayStoreKey` used as a store selector | `store x p`. Ordinary field access to an actual field retains `path`. |

Both ordinary and typed store selectors use one `storeOf` observation. A non-store endpoint selects no store. Array-separation assertions separately require array endpoints; empty regions do not establish that assertion.

### Effect action and evidence

```lean
namespace Verification.Footprints

/-- UNCHANGED: read at the effect's entry heap. -/
def Allowed (Φ : Footprint)
    (ρ : Env) (h : Heap) (l : Nat) (v v' : Val) : Prop

/-- UNCHANGED: allocation plus bounds on every old location. -/
def Post (Φ : Footprint)
    (ρ : Env) (h h' : Heap) : Prop

/-- UNCHANGED: every support entry constrains each old location it selects. -/
def Supported (S : Footprint)
    (ρ : Env) (h h' : Heap) : Prop

/-- CHANGED from two closed grades: pointwise grades on disjoint categories. -/
structure Closed where
  value : Change
  array : Change
  view : Change
  deriving DecidableEq, Repr

/-- CHANGED: compilation into the common footprint interpretation. -/
def Closed.fp : Closed → Footprint

end Verification.Footprints

namespace Verification.TolerantFrames

/-- UNCHANGED: admissibility and the heap-only action. -/
def Action (Φ : Footprints.Footprint) (ρ : Env)
    (s s' : IndexedHeap) : Prop :=
  Admissible s s' ∧
  Footprints.Post Φ ρ s.h s'.h

/-- UNCHANGED meaning: transitivity of the whole action. -/
def Rigid (Φ : Footprints.Footprint) (ρ : Env) : Prop

end Verification.TolerantFrames
```

`Allowed` retains the existing meaning: unchanged contents, or a covering entry whose change permits the replacement. `Post` requires heap growth and such an allowed replacement for every old location. `Supported` requires every applicable support bound, rather than choosing one.

The basic theorem signatures are:

```lean
namespace Verification.Footprints

/-- NEW: an old location keeps its contents category along an
admissible transition (from `HeapOk.category` and role transport). -/
theorem category_admissible {s s' : TolerantFrames.IndexedHeap}
    (ha : TolerantFrames.Admissible s s') {l : Nat} {v v' : Val}
    (hv : s.h[l]? = some v) (hv' : s'.h[l]? = some v') :
    contentsCategory v' = contentsCategory v

/-- NEW: selector inclusion implies region inclusion. -/
theorem class_subset_sound {a b : Selector}
    (hab : a.sub b = true) {ρ h l}
    (ha : Region.mem ρ h (.cls a) l = true) :
    Region.mem ρ h (.cls b) l = true

/-- NEW: selector disjointness excludes common membership. -/
theorem class_disjoint_sound {a b : Selector}
    (hab : a.disjoint b = true) {ρ h l}
    (ha : Region.mem ρ h (.cls a) l = true) :
    Region.mem ρ h (.cls b) l = false

/-- UNCHANGED: the existing foundation lemmas, heap-only. -/
theorem Post.refl (Φ : Footprint)
    (ρ : Env) (h : Heap) : Post Φ ρ h h

theorem Post.empty_iff {ρ h h'} :
    Post [] ρ h h' ↔ h.IsPrefix h'

end Verification.Footprints
```

General inclusion and disjointness use finite certificates, interpreted under entry knowledge. Their constructors are reflexivity, selector inclusion/disjointness, intersection, field/own inclusion, store/cell category facts, path equality, failed-path emptiness, and proved store/cell separation. These are instances of semantic membership inclusion or exclusion.

```lean
namespace Verification.Footprints

/-- NEW: evidence is interpreted under the supplied entry context.
The concrete proof syntax is shared with I4. -/
def RegionIncluded (K : TolerantFrames.Assertion)
    (r t : Region) : Prop :=
  ∀ ρ m s, K ρ m s → ∀ l,
    r.mem ρ s.h l = true →
    t.mem ρ s.h l = true

def RegionsDisjoint (K : TolerantFrames.Assertion)
    (r t : Region) : Prop :=
  ∀ ρ m s, K ρ m s → ∀ l,
    r.mem ρ s.h l = true →
    t.mem ρ s.h l = false

/-- NEW: semantic inclusion of actions under an entry context. -/
def EffectIncluded (K : TolerantFrames.Assertion)
    (Φ Ψ : Footprint) : Prop :=
  ∀ ρ m s s', K ρ m s →
    TolerantFrames.Action Φ ρ s s' →
    TolerantFrames.Action Ψ ρ s s'

end Verification.Footprints
```

Rigidity evidence checks the **whole effect**. Class entries require only contents-category stability on admissible states (`category_admissible`). Raw `Post` on arbitrary heaps permits category changes under `any`, so class transport is proved on admissible states, or under a heap-category-stability premise, never unconditionally on raw heaps. A selected-store entry requires that its path selects the same store under every action of the whole effect. A store-and-cells entry does not acquire rigidity merely from a rigid object path.

The checked evidence and its theorem are specified in I5. `Closed` meet and order operate pointwise on the three categories. `Closed.fp` has one equivalence theorem to `Post`; its implementation is a computational normalization, not a second effect semantics.

### Stated effects and the wire

The annotation language states a finite list of entries, each containing a general `Region` and a `Change`. Roots use the existing call convention: receiver `0`, argument `i` at `i + 1`. Paths have arbitrary finite depth.

The signature has a precondition and two exit specifications:

```lean
namespace Verification.CallEffects

/-- NEW: the two completion kinds of a callable specification. -/
inductive Completion where
  | normal
  | exceptional
  deriving DecidableEq, Repr

/-- NEW: explicit data, also used for serialization. -/
structure Exits (α : Type) where
  normal : α
  exceptional : α

/-- NEW: a completion's shared-state guarantee. `ensures` uses
the existing post vocabulary, with result/thrown value at position 0. -/
structure ExitSpec where
  frame : Footprints.Footprint
  ensures : List HeapKnowledge.IndexFact

/-- CHANGED: the frame-bearing portion of Effect. Existing result
promises remain separately typed result predicates. -/
structure SharedEffect where
  pre : List HeapKnowledge.IndexFact
  exits : Exits ExitSpec

end Verification.CallEffects
```

`SharedEffect` is the frame/post field of `Effect`, not a second public effect type. The wire stores these fields directly in `Effect`; it has no wrapper discriminator.

The migration removes `closed`, `regions`, `receiverStore`, `receiverOwn`, `receiverGrows`, `elementWrite`, and `onThrow` as independent frame specifications:

- Closed grades compile to category entries.
- Receiver-store and receiver-own bounds become ordinary region entries.
- Argument-store regions become `.store` entries at the stated change.
- `receiverGrows` contributes its proved frame and its ordinary append post.
- Primitive exact writes come from I3, never a signature flag.
- A former `onThrow = true` supplies the former frame to the exceptional exit.
- A former `onThrow = false` supplies top and no exceptional post.
- Fresh-result and other result predicates keep their existing meanings. They are conjoined with the common normal post.

The JSON representation requires both exit objects, each with `frame` and `ensures`. Entry records contain exactly `region` and `change`. All producers, decoders, comparisons, substitutions and fixtures change together. Source annotation sugar may omit an exceptional clause; elaboration fills it with top and `true`. The decoder accepts one current shape.

Both exits' frames are read at the call's entry heap. Meet, weakening and promise combination use that same entry interpretation on both sides; frames add no entry-world argument to `excPostW`. Heap-only helpers may interpret result predicates; they do not repeat a frame specification.

### Migration and open work

Leg 2 owns this migration. It replaces `Cls.has`, inequality-based class separation and the duplicate frame interpretations. The three-category split of the interpreter and of `Closed`, and the all-views region as an effect entry, follow I3's tagged representation.

The precise selection of named module cells remains open. Their existing conservative value selector is sound and does not block these interfaces. Search for the smallest regional effect also remains open: checked inclusion, not minimality, is the requirement.

## I2. A certificate of the actual visit

### The existing mechanism this extends

Leg 1’s `SinglePass.VisitRecord` contains `label`, `grades`, and `outFresh`. Its `StepGrades` retains alternative normal and exceptional closed bounds. `visitStep` and the record-rebound proofs tie those values to a successful visit.

This interface extends that record into evidence of the checked local command. [One-pass checking](../SOURCE-ELABORATION.md#checking-a-unit-in-one-pass) owns the pass integration. Its note counterparts are Entry and the exit-edge tuple in §7.

### Identity and payload

A label does not identify a visit: a label may be visited with different input knowledge, selected call signatures or summaries. A certificate is indexed by the actual checker input and result.

The input identity includes:

- The retained graph and type interpretation.
- Label and node.
- Entry claim and knowledge references.
- The summaries used by the successful step.
- Selected typing/call evidence.
- Frame dependencies and their anchors.

Identity is structural or by references whose interpretation has a proved equality. A hash alone is insufficient.

```lean
namespace Verification.Programs.SinglePass

/-- NEW: the finite input captured by one execution of the step checker.
Its fields are the existing checker inputs, retained by reference. -/
structure VisitInput (ι : Type) where
  label : Nat
  node : Node
  claim : PointClaim ι
  knowledge : Parity.KnowledgeRef
  summaries : Parity.SummaryRef
  dependencies : Array Parity.DependencyRef

/-- NEW: an actual exit of this node, including branch and handler exits.
`ordinal` is the position in the node's lowered exit list. -/
structure VisitExit where
  ordinal : Nat
  completion : CallEffects.Completion
  deriving DecidableEq, Repr

/-- NEW: one justified alternative, rather than an unchecked meet of bounds. -/
structure LocalAlternative where
  frame : Footprints.Footprint
  evidence : Parity.EffectProofRef

/-- NEW: an exit's result from this visit. -/
structure ExitRecord where
  exit : VisitExit
  alternatives : Array LocalAlternative
  post : Parity.PostRef
  condition : Parity.AssertionRef
  targetSubst : Parity.Substitution
  rebase : Parity.RebaseProofRef
  supports : Array Parity.SupportUseRef

/-- CHANGED from label/closed-grades/freshness alone.
This is always the successful visit's retained record. -/
structure VisitRecord (ι : Type) where
  input : VisitInput ι
  typing : ProgramCertificates.Evidence ι
  exits : Array ExitRecord
  prefixes : Array Parity.PrefixRecord
  outFresh : Bool

end Verification.Programs.SinglePass
```

The `Parity.*Ref` names are typed indices into the retained certificate store. Their referents are the finite evidence types in I4–I5 and the existing summary objects. They are not callbacks returning `Prop`.

An exit with no possible execution carries a checked contradiction. An exit with a possible execution has a justified bound, at worst top. An empty list is not interpreted as permission to discard an exit.

`prefixes` records justified bounds at internal observation or callback boundaries that the local operation exposes. Exit bounds alone cannot justify an assertion at an interior observation.

### Soundness and independence

The semantic certificate has the following signature schema. `VisitRuns` is the restriction of existing `ControlFlow.Transitions` to the recorded node and exit, with its initial and final environments. `InputHolds` interprets the recorded typing, knowledge and dependencies. Neither introduces a new execution relation.

```lean
namespace Verification.Parity

/-- NEW: semantic interpretation of a retained local certificate. -/
def LocalSound {ι : Type}
    (r : Programs.SinglePass.VisitRecord ι) : Prop :=
  ∀ execution, VisitRuns r execution →
    InputHolds r execution.before →
    execution.steps < execution.before.heap.n →
    ∃ after : TolerantFrames.IndexedHeap,
      after.h = execution.afterHeap ∧
      after.n + execution.steps = execution.before.heap.n ∧
      TolerantFrames.Admissible execution.before.heap after ∧
      ExitHolds r execution.exit execution.before
        execution.afterEnv after ∧
      PrefixesHold r execution

/-- NEW: the record is the output of this successful invocation,
and proves every actual completion and recorded prefix. -/
theorem checkedVisit_sound
    {ι : Type} {G : NormalGraph ι}
    {input : Programs.SinglePass.VisitInput ι}
    {r : Programs.SinglePass.VisitRecord ι}
    (hc : checkedVisit G input = .ok r) :
    r.input = input ∧ LocalSound r

end Verification.Parity
```

`ExitHolds` expands to:

1. The result/thrown-value typing established by the selected operational rule.
2. `Action Φ` for **each** recorded alternative `Φ` of that exit.
3. The recorded exact or contractual two-state post.
4. The branch condition.
5. The target-environment substitution relation.
6. Valid rebasing and support evidence used by that exit.

“Exact post” means the post supplied by the selected rule. A primitive write has the exact post in I3; an arbitrary call has only its checked specification. The record does not claim a strongest postcondition for every command.

`checkedVisit` has no enclosing effect-bound parameter. It may consume typed claims and established frame hypotheses. Those hypotheses and their dependencies are explicit in the input. A later bound check selects a proved local alternative and checks its rebasing/inclusion; it cannot change the local transfer.

The producer is the successful `checkedStep`/`visitStep` path. It computes local evidence once, then uses that value for both admission and recording. Consumers are:

- Edge transfer, through I4.
- Regional, loop and function effect composition, through I5.
- Final written-effect admission.
- Later retained-plan finalization.

`outFresh` remains a projection justified by the post evidence. `StepGrades` becomes a closed projection of the common local alternatives, with a projection theorem, then disappears from consumers that need regional precision.

### Migration and open work

Leg 5 owns `VisitInput`, the expanded record, the producer integration and the record soundness theorem. Leg 2 supplies effect evidence; leg 3 supplies primitive posts; leg 4 supplies assertion and transfer evidence.

The `grading` branch is removed when this record becomes the common checking result. Every successful visit returns its record. The old record is not retained alongside the new one.

Leg 5 deletes `regionalBoth`-style reconstruction from final summaries and bound-driven local transfer. Leg 7 connects the retained plan and records to final acceptance; record soundness alone does not prove a completed or accepted function.

Storage layout, hash-consing and compression remain open performance choices. They do not change referent identity, dependency validity or the certificate theorem.

## I3. Operational typed arrays

### The existing mechanism this extends

This interface extends `Tm`, `Step`, `StoreForm`, `Cat`, `RefsOk` and `HeapOk`. It replaces the production roles of `ElementWrite`, `ExactWrite`, `ViewWrite`, `ViewWriteOf`, and `Effect.viewPost`.

[Element writes](../FOOTPRINTS.md#element-writes) owns the primitive boundary. The note counterpart is W2–W4 and View-Length, View-Read and View-Write.

### Representation

Use tagged primitive stores. Operational execution identifies a view by its value and store tags, without inspecting a proof world or a callable signature.

```lean
namespace Verification

/-- NEW: the admitted numeric storage formats.
This replaces CallEffects.ElementKind at the semantic foundation. -/
inductive ViewFormat where
  | uint8
  | uint16
  | int32
  | float64
  deriving DecidableEq, Repr

/-- NEW Tm constructors, added to the existing mutual declaration:
a source-level view object, and an internal dense store value. -/
-- Tm.viewAt (fields : List (PropKey × Nat))
--   (identity store : Nat) (format : ViewFormat) (length : Nat)
-- Tm.viewStore (format : ViewFormat) (cells : List Nat)

/-- NEW operational expressions; operands evaluate left to right. -/
-- Tm.viewLength (receiver : Tm)
-- Tm.viewRead (receiver index : Tm)
-- Tm.viewWrite (receiver index value : Tm)

/-- CHANGED: view roles include the immutable format and length. -/
inductive StoreForm where
  | array
  | view (format : ViewFormat) (length : Nat)
  deriving DecidableEq, Repr

/-- NEW: total conversion of a JavaScript Number's representation. -/
def ViewFormat.convert : ViewFormat → UInt64 → UInt64

/-- NEW: the numeric representations a format stores. -/
def ViewFormat.Stored : ViewFormat → UInt64 → Prop

/-- NEW: numeric-property index, after ToPropertyKey.
Numeric negative zero denotes index zero. -/
def viewIndex (length : Nat) (bits : UInt64) : Option Nat

end Verification
```

`viewAt` has ordinary own fields and an identity in addition to its immutable primitive descriptor. Its view store is not an ordinary writable field. `fieldsOf`, object identity, property reads, source-value classification and reference traversal handle both ordinary objects and views.

A view store contains a `List Nat`, so holes are unrepresentable. Its role requires the stored format and list length to match the descriptor. Every listed cell has element role and holds a number admitted by the format.

The primitive store contract admits every dense, length-preserving replacement using cells of that format. Writable aliases cannot strengthen it to a particular value range narrower than the format. Such refinements are assertions subject to effect checking.

This contract condition is enforced for every view store in an admitted world, including imported and allocated views. It is necessary because a write may affect a view other than its receiver.

```lean
namespace Verification

/-- NEW: the canonical contract for a view store.
It admits exactly the represented fixed-length format stores, with
valid element references at each inspected world. -/
def viewStoreCtr (k : Nat) (format : ViewFormat) (length : Nat) : Ctr k

/-- NEW: every view-store role has the primitive replacement contract.
Equality is extensional at all levels the entry can inspect. -/
def ViewWorld {k : Nat} (W : WorldT k) : Prop

/-- CHANGED: view stores satisfy their tag, length and dense shape. -/
def Cat : Role → Val → Prop

end Verification
```

`ViewWorld` joins the admitted-world invariant and is preserved by truncation and extension. It is not a postcondition assumed of an operational result. Primitive preservation constructs the result world and proves this invariant.

### Total conversion

Conversion is defined from the IEEE-754 binary64 fields, using integer arithmetic on the sign, exponent and significand:

| Format | Conversion |
|---|---|
| `uint8` | Nonfinite numbers and either zero become `+0`; finite numbers are truncated toward zero, reduced modulo `2^8`, and encoded exactly as binary64. |
| `uint16` | The same operation modulo `2^16`. |
| `int32` | Truncate, reduce modulo `2^32`, interpret residues at least `2^31` as negative, and encode exactly. |
| `float64` | Preserve the binary64 representation. |

For `float64`, stored-value equality is numeric observational equality: equal numeric values, with both NaNs treated alike and signed zeros distinguished where the operation observes their sign. Primitive postconditions do not require a JavaScript implementation to preserve a NaN payload.

`Stored` is the conversion range for integer formats and all binary64 values for `float64`. Conversion is total on `UInt64`; it does not require `ElementKind.Takes`. The old safe-integer conversion lemmas become corollaries.

The valid numeric index is an integer in `[0, length)`. Numeric `-0` maps to zero. Nonfinite values, negative values other than `-0`, fractional values and out-of-range integers are invalid. String keys, including the string `"-0"`, remain property operations with their own lowering.

### Operational rules

The three operations use the existing small-step evaluator.

1. **Length.** After evaluating the receiver to a valid `viewAt`, return its fixed length as a number. The heap is unchanged.
2. **Read.** Evaluate receiver and numeric index. A valid index reads the number in the corresponding cell. An invalid index returns `undefined`. The heap is unchanged.
3. **Write.** Evaluate receiver, numeric index and numeric value. An invalid index returns the original assigned value and leaves the heap unchanged. A valid index replaces the receiver’s selected cell reference with a fresh cell holding the converted value, then returns the original assigned value.

A valid write may also replace observations of other views. The abstract machine makes this conservative overlap behavior explicit:

- Scan old locations tagged `viewStore`.
- For the receiver store, retain every other cell reference and replace precisely the selected one.
- For every other view store, choose a vector of format-admitted numbers of its existing length and allocate fresh cells for that vector.
- Replace those view-store contents with their resulting dense vectors.
- Preserve every old non-view location, including every old element cell.

A finite `ViewChoices` value supplies these vectors; an operational predicate checks their lengths and numeric formats against the runtime tags. It mentions neither worlds nor `HeapOk`. The transition relation ranges over all valid choices.

This is an abstraction of overlapping storage. It permits unrelated views to change, while preserving the exact receiver update. Same-store aliases observe the receiver update. An unchanged observation of another view is represented by choosing its old values.

```lean
namespace Verification

/-- NEW: finite operational choices for other old view stores. -/
abbrev ViewChoices := List (Nat × List UInt64)

/-- NEW: checked solely against runtime store tags and numeric formats. -/
def ViewChoices.Valid (h : Heap) (receiverStore : Nat)
    (choices : ViewChoices) : Prop

/-- NEW: constructs fresh cells and replaces view-store vectors.
It never consults a world or a desired postcondition. -/
def writeViews (h : Heap) (receiverStore index : Nat)
    (value : UInt64) (choices : ViewChoices) : Heap

end Verification
```

The extra choices make view writes nondeterministic in the abstract machine. Existing proofs that use determinism, including the route through `TolerantFramesRuns.graph_run`, must use universal safety over operational successors. Leg 3 owns this proof migration. No second evaluator supplies a deterministic “checking meaning.”

`Change.Holds .grow` is extended through a common store observation covering `.arr` and `.viewStore`. Its mathematical conditions remain dense-prefix preservation, nondecreasing length, the array-length bound where applicable, and old-or-fresh listed cells. For views, the unchanged role additionally fixes length and format.

### The eight primitive theorems

The following signatures use these NEW predicates:

- `ViewReceiver W h b`: the receiver descriptor, role, canonical contract and contents agree.
- `ViewLengthRun`, `ViewReadRun`, `ViewWriteRun`: abbreviations for the corresponding existing `Steps` executions after operand evaluation.
- `ViewWriteExact h h' b i v`: the valid-index receiver update described above.
- `SameNumber`: the numeric observational equality just specified.

All quantify over every admitted format and every numeric bit pattern.

```lean
namespace Verification.PrimitiveViews

/-- NEW: length execution is safe and preserves the world and heap. -/
theorem viewLength_safe
    (hs : ViewReceiver s.W s.h b) :
    ∃ result, ViewLengthRun s.h b s.h result

/-- NEW: the result is exactly the fixed length; no heap change. -/
theorem viewLength_post
    (hs : ViewReceiver s.W s.h b)
    (hr : ViewLengthRun s.h b h' result) :
    h' = s.h ∧ result = .num (bitsOfNat (viewLengthOf b))

/-- NEW: every numeric index has a read result; execution preserves
the heap and returns a source value. -/
theorem viewRead_safe
    (hs : ViewReceiver s.W s.h b) (index : UInt64) :
    ∃ result, ViewReadRun s.h b index s.h result ∧
      isSourceVal result = true

/-- NEW: valid indices read their stored number; invalid ones
return undefined, in either case without mutation. -/
theorem viewRead_post
    (hs : ViewReceiver s.W s.h b)
    (hr : ViewReadRun s.h b index h' result) :
    h' = s.h ∧ ViewReadResult s.h b index result

/-- NEW: progress and preservation for every operational choice.
The preservation conclusion constructs an extended/truncated world;
it does not assume exit HeapOk. -/
theorem viewWrite_safe
    (hs : ViewReceiver s.W s.h b) (hw : ViewWorld s.W)
    (index value : UInt64) :
    ViewWriteProgress s.h b index value ∧
    ∀ h' result, ViewWriteRun s.h b index value h' result →
      ∃ s' : TolerantFrames.IndexedHeap,
        s'.h = h' ∧ TolerantFrames.Admissible s s' ∧
        ViewWorld s'.W ∧ result = .num value

/-- NEW: every write execution has the common all-views grow bound. -/
theorem viewWrite_frame
    (hs : ViewReceiver s.W s.h b) (hw : ViewWorld s.W)
    (hr : ViewWriteRun s.h b index value h' result) :
    Footprints.Post
      [(.cls Footprints.Selector.views, .grow)]
      ρ s.h h'

/-- NEW: a valid write stores the converted number and preserves
every other receiver index, including its cell reference. -/
theorem viewWrite_exact
    (hs : ViewReceiver s.W s.h b)
    (hi : viewIndex (viewLengthOf b) index = some i)
    (hr : ViewWriteRun s.h b index value h' result) :
    result = .num value ∧ ViewWriteExact s.h h' b i value

/-- NEW: invalid numeric indices cause no write, and assignment
returns its original numeric operand. -/
theorem viewWrite_invalid
    (hs : ViewReceiver s.W s.h b)
    (hi : viewIndex (viewLengthOf b) index = none)
    (hr : ViewWriteRun s.h b index value h' result) :
    h' = s.h ∧ result = .num value

end Verification.PrimitiveViews
```

Here `s` is an `IndexedHeap`; implicit variables in these theorem signatures have the types displayed by their uses. The primitive typing theorem additionally carries the evaluator’s ordinary step-budget accounting when embedded in general `Safe` proofs.

### Metadata and host boundary

Delete `viewLengthKey`, `viewElementsKey`, `LengthMeta`, and the view-specific part of `ViewMetaOk` after their producers and observations use the primitive descriptor. Length is an immutable descriptor component. The operational store tag identifies its format.

`hostKey` remains for unrelated host objects. It has no role in validating primitive view access. `Buffer` and imported typed arrays enter through an explicit primitive-view representation boundary; arbitrary user records cannot acquire primitive status by matching a field or signature shape.

Fixed-length, non-detached, non-resizable storage remains an explicit source and external-contract boundary. Shared-memory interference requires a separate concurrency model. Source lowering and native library contracts must establish this boundary independently of the Lean primitive theorem.

### Migration and open work

Leg 3 owns the representation, evaluator, reference and typing migration, the eight theorems and primitive lowering. It deletes the exact-write effect flag and special world post when all consumers use the primitive record.

Leg 2 supplies the view category. Leg 4 derives same-view quantified consequences from `ViewWriteExact`. Library `fill`, `copyWithin` and `set` use ordinary reviewed exit specifications; they do not inherit the primitive’s exact post.

Byte-level buffer offsets and non-overlap proofs remain open. Conservative changes to other views make them unnecessary for the selected scope. A concrete JavaScript-to-abstract-view simulation remains an unproved source/host boundary and must be reviewed as such.

## I4. Assertions, checked consequences and shared frames

### The existing mechanism this extends

This interface extends `HeapKnowledge.Term`, `IndexFact`, `Knowledge`, `StepRelations`, `Linear.check`, and the semantic `TolerantFrames.Assertion` and `Box`.

[Arithmetic](../ARITHMETIC.md) owns arithmetic observations; [Footprints](../FOOTPRINTS.md) owns support and preservation. The note counterparts are its assertion grammar, modal laws, atom axioms, Entry and checked transfer.

### Assertion representation

Use one hash-consed, acyclic arena. Every reference names an earlier node. Boxes refer to their body; knowledge contains references rather than copied frame facts.

```lean
namespace Verification.Parity

/-- NEW: typed indices into a retained arena. -/
structure AssertionRef where
  index : Nat
  deriving DecidableEq, Repr

structure PostRef where
  index : Nat
  deriving DecidableEq, Repr

/-- NEW: an ordinary path; the root is a de Bruijn slot. -/
structure Path where
  root : Nat
  fields : List String
  deriving DecidableEq, Repr

/-- NEW: a witness expression denotes a source value. -/
inductive Witness where
  | path (p : Path)
  | literal (v : Val)

/-- NEW: the selected first-order atoms.
ScalarBody is a finite conjunction of the existing scalar linear
clauses, with bound index and element variables explicitly scoped. -/
inductive Atom where
  | linear (fact : Linear.Fact HeapKnowledge.Term)
  | equal (path : Path) (value : Witness)
  | dense (path : Path) (bound : HeapKnowledge.Term)
  | contents (path : Path) (kind : CallEffects.ElemPred)
  | every (path : Path) (bound : HeapKnowledge.Term) (body : ScalarBody)
  | element (path : Path) (index : HeapKnowledge.Term) (value : Witness)
  | defined (term : HeapKnowledge.Term)
  | safeInt (path : Path)
  | pastSafe (path : Path)

/-- NEW: sharing is the representation of the note's ordinary syntax. -/
inductive AssertionNode where
  | truth
  | falsity
  | atom (a : Atom)
  | and (left right : AssertionRef)
  | guarded (guard body : AssertionRef)
  | existsValue (body : AssertionRef)
  | separated (left right : Path)
  | apart (left right : Path)
  | fresh (path : Path)
  | box (effect : Footprints.Footprint) (body : AssertionRef)

/-- NEW: finite immutable nodes; validity checks references and scopes. -/
structure AssertionArena where
  nodes : Array AssertionNode

/-- NEW: references precede their users; binders have correct scopes;
guards have separately checked invariant evidence. -/
def AssertionArena.Valid : AssertionArena → Prop

/-- NEW: semantic interpretation, reusing IndexedHeap and Action. -/
def Sat (arena : AssertionArena) (η : Env) (mark : Nat)
    (s : TolerantFrames.IndexedHeap) (a : AssertionRef) : Prop

end Verification.Parity
```

`ScalarBody` uses the existing `LinearClause Bound` vocabulary restricted by its declared scalar grammar: literals, logical scalar parameters, the bound index and the element’s scalar value or string length. It excludes heap projections through elements. This restriction is syntax, checked once when the body is constructed.

`existsValue` binds logical slot `0`; outer slots shift by one. `Sat` uses `push witness η`. A witness remains fixed under a box. Runtime bindings and eigenvariables therefore share de Bruijn operations but have distinct scope evidence; a program edge cannot assign a logical witness.

Interpretation is compositional:

- Linear atoms require every term to be defined, then use `Linear.Fact.Holds`.
- Density requires an ordinary array and a natural prefix bound.
- `every` requires the bounded cells to be present and their scalar bodies to hold.
- Element equality observes a present typed-array element and a defined witness.
- `separated` requires two ordinary arrays with different stores.
- `apart` additionally requires disjoint element-cell sets.
- `fresh` requires a selected store at or above the invocation mark.
- `box Φ A` quantifies over every `Action Φ` at the same environment and mark.
- `guarded g A` means `g ∨ A`; well-formed use includes checked invariance of `g`.

Single-state assertions contain current observations only. `Term.old` belongs to two-state posts and is indexed by the enclosing command boundary. The arena validator prevents an old observation from silently referring to a function entry when the judgment means node entry.

Existing facts embed into these nodes. Search indices and normalized arithmetic rows may cache projections, with interpretation theorems. They do not carry independent truth.

### Two-state formulas

```lean
namespace Verification.Parity

/-- NEW: the state selected by a two-state formula. -/
inductive Phase where
  | before
  | after
  deriving DecidableEq, Repr

/-- NEW: internal exact operational posts.
Each constructor is introduced only by its operation's checked rule. -/
inductive OperationPost where
  | fieldUpdate (receiver : Path) (key : PropKey) (value : Witness)
  | arrayWrite (array : Path) (index : HeapKnowledge.Term) (value : Witness)
  | arrayAppend (array : Path) (values : List Witness)
  | viewWrite (view : Path) (index : HeapKnowledge.Term) (value : Witness)
  | resultBinding (value : Witness)
  | thrownBinding (value : Witness)

/-- NEW: formulas used by the common consequence checker. -/
inductive Formula where
  | at (phase : Phase) (assertion : AssertionRef)
  | transition (effect : Footprints.Footprint)
  | operation (post : OperationPost)
  | linear (fact : Linear.Fact HeapKnowledge.StepVar)
  | and (left right : Formula)
  | truth
  | falsity

/-- NEW: one node entry and one exit, with a common invocation mark. -/
structure TwoState where
  beforeEnv : Env
  afterEnv : Env
  mark : Nat
  before : TolerantFrames.IndexedHeap
  after : TolerantFrames.IndexedHeap

/-- NEW: `before` interprets Old; transition uses entry roles/environment. -/
def Holds (arena : AssertionArena) (s : TwoState) : Formula → Prop

end Verification.Parity
```

`OperationPost.viewWrite` is internal certificate data. It has no annotation or wire constructor in `Effect.ensures`.

Exact posts include success conditions. In particular, ordinary in-bounds writes preserve length, writing at the old length increments it within the array limit, and append length equations describe normal completion. A post for a throwing execution contains only what its exceptional proof establishes.

### Checked derivations

Use an indexed derivation datatype, with finite raw certificates checked into it:

```lean
namespace Verification.Parity

/-- NEW: a checked derivation of one two-state formula.
Constructors are the rule schemas specified below. -/
inductive Derivation (arena : AssertionArena) :
    List Formula → Formula → Type

/-- NEW: untrusted finite proof data, containing rule tags, references,
substitutions and existing Linear.Step certificates. -/
inductive RawDerivation

/-- NEW: checks scopes, all premises and all arithmetic certificates. -/
def checkDerivation (arena : AssertionArena)
    (premises : List Formula) (goal : Formula)
    (raw : RawDerivation) :
    Except String (Derivation arena premises goal)

/-- NEW: the common consequence theorem. -/
theorem Derivation.sound
    {arena : AssertionArena} (ha : arena.Valid)
    {Γ : List Formula} {goal : Formula}
    (d : Derivation arena Γ goal) :
    ∀ s, (∀ p ∈ Γ, Holds arena s p) → Holds arena s goal

end Verification.Parity
```

The following table fixes the constructors and their indices. It is part of the declaration of `Derivation`, not a list of optional search strategies.

Notation:

- `D Γ F` means `Derivation arena Γ F`.
- `old A` and `now A` mean `.at .before A` and `.at .after A`.
- `box Φ A`, conjunctions, guards and existentials name arena nodes whose shapes are checked.
- `Γ ⊢ p` denotes a recursively supplied derivation.
- A side certificate is a finite checked datatype from I1 or I5; it is never an arbitrary user-supplied semantic implication.

| Constructor | Premises and conclusion |
|---|---|
| `assumption` | `F ∈ Γ → D Γ F`. |
| `truth` | `D Γ true`. |
| `falseElim` | `D Γ false → D Γ F`. |
| `andIntro` | `D Γ F → D Γ G → D Γ (F ∧ G)`. |
| `andLeft`, `andRight` | Project a checked conjunction. |
| `cut` | `D Γ F → D (F :: Γ) G → D Γ G`. |
| `guardLeft`, `guardRight`, `guardCases` | Ordinary disjunction introduction/elimination, with the node’s invariant-guard certificate. |
| `existsIntro` | A defined witness and `D Γ (A[witness/0])` give `D Γ (∃ A)`. |
| `existsElim` | Open an existential with a fresh logical slot; the slot is absent from the conclusion and other undischarged assumptions. |
| `equalitySubst` | A proved value/path equality and capture-avoiding substitution evidence transport an assertion. |
| `oldLift` | A one-state derivation becomes a derivation with every premise and conclusion interpreted before the command. |
| `boxElim` | `D Γ (at p (box Φ A)) → D Γ (at p A)`. |
| `boxAndIntro`, `boxAndLeft`, `boxAndRight` | Both directions of modal conjunction, for either phase. |
| `boxMono` | A context-free one-state derivation `A ⊢ B` gives `box Φ A ⊢ box Φ B`. Ambient mutable assumptions cannot be imported into this premise. |
| `boxAnti` | Checked `Φ ⊑ Ψ` gives `box Ψ A ⊢ box Φ A`. Context-dependent inclusion carries its context proof. |
| `boxGuard` | `g ∨ box Φ A ⊢ box Φ (g ∨ A)`, with invariant evidence for `g`. |
| `boxIdem` | `box Φ A ⊢ box Φ (box Φ A)`, with whole-effect rigidity evidence. |
| `tolerantFrame` | Support, respect and the I5 modal-context certificate give `K ∧ A ⊢ box Φ A`. |
| `grow` | The note’s lower-bound axiom, with a fixed logical scalar bound and defined ordinary-array length. |
| `dense` | Dynamic density enters the grow modality; its bound is a fixed scalar during the action. |
| `sep` | Store separation frames any selected atom whose heap observations are confined to the displayed length. Observation evidence checks that property. |
| `every` | `apart(x,z)` frames the scalar bounded quantification under `x[*]:any`; bound and scalar parameters are fixed. |
| `init` | Any selected atom whose heap observations are the displayed path length enters `values:init`. Definedness of the path is a premise. |
| `rigidPath` | Open the rigid-path value witness, apply the fresh-variable atom derivation, then substitute back using I5. |
| `view` | An atom observing only the displayed fixed view length enters top; the receiver is fixed. |
| `entry` | Retain arbitrary old input knowledge, and expose the selected local certificate’s transition and post for this exit. |
| `frame` | `old(box Φ A) ∧ tr Φ` gives `now A`, with the environment/scope transport. |
| `framePlus` | The preceding premises plus rigidity give `now(box Φ A)`. |
| `call` | Instantiate either completion’s checked call specification, including result/thrown binding and freshness-mark evidence. |
| `alloc` | An actual ordinary-array allocation gives emptiness, selected-store freshness and apartness from every array in the preallocation scope. |
| `seqEffect` | Compose actions through certified rebasing and inclusion. |
| `freshEffect` | Erase only a selected store proved outside the earlier entry domain. |
| `reliance` | A box and a certified respecting prefix yield its body at that prefix. Repeated use additionally requires the recorded composition/rigidity evidence. |
| `transfer` | A derivation of the substituted target assertion plus I5 substitution evidence establishes target knowledge. |
| `linear` | Existing `Linear.check` over explicitly defined before/after observations. |
| `integerOperation` | Exact addition, subtraction or constant multiplication, with safe-integer operands and exact-result range evidence. |
| `shiftRight` | The constant-shift rule below. |
| `mask` | The constant-mask rule below. |
| `stringLength` | A defined string has its UTF-16 length, in `[0, maxStringLength]`. |
| `stringRead` | A valid string index reads the corresponding code unit; the result has UTF-16 length one. Invalid-index conclusions follow the operation’s result rule. |
| `stringConcat` | A normal concatenation result has the sum of operand UTF-16 lengths. |
| `lengthSuccessor` | The existing exact-or-`pastSafe` consequence at the string-length-plus-one boundary. |
| `ordinaryWritePost`, `appendPost` | Eliminate the checked operational post into arithmetic and element consequences. |
| `viewLengthPost`, `viewReadPost`, `viewWritePost`, `viewInvalidPost` | Eliminate I3’s primitive posts. |
| `exactUpdate` | Preserve observations outside a proved update domain; establish updated observations inside it. |
| `everyIntro`, `everyElim` | Introduce/eliminate scalar bounded quantification using a fresh index and explicit presence/bound premises. |

Loop and graph composition are derivations over graph commands rather than single two-state formulas. They use the same references and local certificates:

```lean
namespace Verification.Parity

/-- NEW: checked graph-command proof data.
The constructors are leaf, sequence, handler, frame, framePlus,
loop and consequence. Each refers to actual local certificates. -/
inductive CommandDerivation

/-- NEW: every finite execution of the checked command establishes
its exit knowledge, and every certified prefix establishes its frame uses. -/
theorem CommandDerivation.sound
    (d : CommandDerivation) :
    CommandSafe d

end Verification.Parity
```

The `loop` constructor checks:

- Establishment from every external entry.
- A body checked under `I ∧ box Φ R`.
- Recurrence establishing that same assertion after the back-edge substitution.
- A rigid summary and valid anchor transport.
- Separate departure and exceptional derivations.
- Prefix bounds for every interior use of the shared frame.

This allows the body to use its frame for safety. It does not require checking the body from `I` alone.

### Arithmetic indices and range conditions

For `shiftRight`, let the left operand denote the integer `x`, the constant shift be `d`, and the result denote `y`. Required premises and conclusions are:

```math
0 \le x \le 2^{31}-1,\qquad 0\le d<32,
\qquad
0\le y,\qquad
2^d y\le x\le 2^d y+(2^d-1).
```

`d` is a literal checked integer; the certificate connects the actual `Arith.shr` result to these inequalities. It does not infer them from a matching expression spelling.

For `mask`, with constant `m`:

```math
0\le x\le 2^{31}-1,\qquad 0\le m<2^{31},
\qquad
0\le y\le m,\qquad y\le x.
```

The result is the actual `Arith.bitAnd` result. These are precisely the relations needed from `bitAtoms` and `smallOperand`.

The general integer-operation constructor handles multiplication only when one operand is a proved constant. It checks exact binary64 representability of the result. An integer linear derivation alone never proves that a rounded JavaScript operation equals its mathematical result.

`lengthSuccessor` retains the behavior behind `stringLengthPlusOne` and `pastSafeAtoms`: a nonnegative safe-integer sum bounded by `2^53` yields either its ordinary safe-integer equations or the explicit `pastSafe` result `2^53`. It does not declare `2^53` a safe integer. The alternatives are represented by invariant scalar guards and checked separately when consumed.

### Shared-frame references

```lean
namespace Verification.Parity

/-- NEW: a shared frame is one box node with its command anchor. -/
structure FrameRef where
  assertion : AssertionRef
  anchor : Nat

/-- NEW: a use transports the anchor's names and cites the prefix
certificate that makes the frame available here. -/
structure FrameUse where
  frame : FrameRef
  subst : Substitution
  prefix : PrefixProofRef
  dependencies : Array DependencyRef

/-- NEW: resolving a reference establishes the same assertion as its
arena interpretation, with the recorded substitution. -/
theorem frameUse_sound
    (h : FrameUse.Valid arena use) :
    FrameUse.Holds arena use

end Verification.Parity
```

A frame reference owns no new semantic modality. It points to a `box` node. Expansion is a mathematical interpretation used in proofs, not a second executable assertion tree.

A dependency change invalidates the certificate that uses it. Removing a frame fact after a visit has used it cannot preserve that visit’s certificate without rechecking or a proved interpretation-preserving replacement.

### Migration and open work

Leg 4 owns the assertion arena, checked derivations, arithmetic rules and their soundness. It migrates `IndexFact`, `Knowledge`, `StepRelation` and `Composer` consumers to projections or instances of this semantics.

The selected preservation roles of `keptBy`, `keptIndicesWith`, `guardKept`, `stableIndices`, `regionFirst`, `regionSep`, `storeHeld`, append-specific filtering and typed-write filtering are deleted when their precision is represented by these derivations.

Leg 5 owns command composition and edge use. Leg 6 owns full shared-loop-frame integration.

Search order, proof compression and invariant proposal heuristics remain open. Derivation checking and soundness are fixed independently of those choices. Projected quantified predicates remain outside the selected assertion grammar and cannot silently use scalar-`every` rules.

## I5. Rebasing, substitution and support contexts

### The existing mechanism this extends

This interface extends `Footprints.RebaseEvidence`, `RebaseOk`, `transport`, `Post.compose_at`, `Survival.ReadContext`, `Supports C P S`, and `TolerantFrames.RigidOn`.

[Footprints](../FOOTPRINTS.md), especially its argument-path regions and support sections, owns these mechanisms. The note counterparts are rebasing, Fresh-Eff, rigid-path substitution, support/respect, and capture-avoiding Call and Transfer.

### General rebasing

Rebasing is old-location coverage. It is indexed by both environments and states:

```lean
namespace Verification.Footprints

/-- NEW: every old location permitted by the later effect is permitted
at an equal or greater change by the earlier-entry effect. -/
def Rebased (Φ Ψ : Footprint)
    (ρ₀ ρ : Env)
    (s₀ s : TolerantFrames.IndexedHeap) : Prop :=
  ∀ r δ, (r, δ) ∈ Φ → ∀ l,
    l < s₀.h.length →
    r.mem ρ s.h l = true →
    ∃ t γ, (t, γ) ∈ Ψ ∧
      t.mem ρ₀ s₀.h l = true ∧
      δ.le γ = true

/-- CHANGED: finite facts for arbitrary paths replace root/one-field flags. -/
structure RebaseEvidence where
  links : List (Nat × Nat × List String)
  agreements : List (Nat × List String)
  freshStores : List (Nat × List String)
  classes : List (Region × Selector)

/-- CHANGED: interprets all evidence against the two entry contexts. -/
def RebaseOk (ev : RebaseEvidence) (ρ₀ ρ : Env)
    (s₀ s : TolerantFrames.IndexedHeap) : Prop

/-- CHANGED: returns class-precise coverage and its finite proof. -/
def rebaseAll (ev : RebaseEvidence)
    (Φ : Footprint) : Footprint

/-- CHANGED: soundness has no path-depth restriction. -/
theorem rebase_sound
    (ha : TolerantFrames.Admissible s₀ s)
    (he : RebaseOk ev ρ₀ ρ s₀ s) :
    Rebased Φ (rebaseAll ev Φ) ρ₀ ρ s₀ s

end Verification.Footprints
```

`RebaseOk` requires:

- Each link identifies the later root with the value of the recorded earlier path.
- Each agreement identifies the relevant path’s result at both states, including failure where equality is required.
- Each fresh-store fact puts every selected store outside the earlier heap domain.
- Each class fact proves membership inclusion for every selected location.

The executable evidence constructors are:

| Constructor | Obligation |
|---|---|
| `class` | Old-location role transport. |
| `path` | Root link plus arbitrary-depth path agreement. |
| `rigidPath` | A rigid-path witness and admissibility establish the agreement. |
| `freshStore` | The selected store’s location is at least the earlier entry length. |
| `widen` | Proved category inclusion. |
| `intersection` | Preserve the intersecting selector while rebasing its region. |
| `append` | Combine entrywise coverage. |

Default widening is determined by the region’s semantic category:

- Selected ordinary store: arrays.
- Selected typed store: views.
- Selected store without a form proof: stores.
- Element cells: values.
- Ordinary source fields and module cells: values.
- Own-location sets: the proved union of their categories.
- An unrestricted internal region: all categories.

A store-and-cells footprint rebases its entries separately. Fresh-store erasure deletes only its store entry. Its old cells remain covered. An all-views entry always rebases to all-views, even when the receiver is fresh.

Sequential composition has the signature:

```lean
namespace Verification.Footprints

/-- CHANGED from Post.compose_at: role-aware, arbitrary environments,
with common semantic rebasing evidence. -/
theorem Post.compose_at
    (h₁ : TolerantFrames.Action Φ ρ₀ s₀ s)
    (h₂ : TolerantFrames.Action Ψ ρ s s')
    (hr : Rebased Ψ Ψ₀ ρ₀ ρ s₀ s) :
    TolerantFrames.Action (Φ ++ Ψ₀) ρ₀ s₀ s'

end Verification.Footprints
```

A subsequent inclusion proof may weaken the concatenated footprint to the chosen command summary.

### Rigidity and path evidence

A rigid path means the note’s existential fixed-value box. Singleton-field chains are one evidence producer.

```lean
namespace Verification.Parity

/-- NEW: the semantic meaning of arbitrary-path rigidity. -/
def PathRigid (p : Path) (ρ : Env) (m : Nat)
    (s : TolerantFrames.IndexedHeap) : Prop :=
  ∃ v, ∀ s', TolerantFrames.Admissible s s' →
    HeapKnowledge.readPath s'.h (ρ p.root) p.fields = some v

/-- NEW: checked path proofs include variables, singleton-contract
field extension, equality transport, and an opened modal witness. -/
inductive PathRigidEvidence

/-- NEW: conditional rigidity of a whole effect on a stable domain. -/
structure RigidityEvidence where
  domain : AssertionRef
  effect : Footprints.Footprint
  proof : RigidityProof

/-- NEW: the evidence includes domain preservation and transitivity. -/
theorem rigidity_sound
    (he : RigidityEvidence.Valid arena ev) :
    ∀ ρ m s₀ s₁ s₂,
      Sat arena ρ m s₀ ev.domain →
      TolerantFrames.Action ev.effect ρ s₀ s₁ →
      TolerantFrames.Action ev.effect ρ s₁ s₂ →
      Sat arena ρ m s₁ ev.domain ∧
      TolerantFrames.Action ev.effect ρ s₀ s₂

end Verification.Parity
```

`RigidityProof` has class, selected-store, union and weakening-by-proved-equivalence constructors. The union constructor checks stability of every selected region under the **union effect**, not merely under its own entry. It has no general store-and-cells rigidity constructor.

### Substitution and marks

```lean
namespace Verification.Parity

/-- NEW: finite, capture-avoiding substitution of free slots by paths.
Logical binders lift this map; bound slots remain bound. -/
structure Substitution where
  images : Array Path

/-- NEW: a separate witness records the interpretation of names. -/
def Substitution.Holds (θ : Substitution)
    (target source : Env) (h : Heap) : Prop :=
  ∀ i p, θ.images[i]? = some p →
    HeapKnowledge.readPath h (source p.root) p.fields = some (target i)

/-- NEW: current and command-entry substitutions are explicit. -/
structure TwoSubstitution where
  before : Substitution
  after : Substitution

/-- NEW: caller/callee marks are related explicitly. -/
structure MarkEvidence where
  caller : Nat
  callee : Nat
  ordered : caller ≤ callee

/-- NEW: syntactic substitution and its semantic equivalence. -/
def substAssertion :
  AssertionArena → Substitution → AssertionRef →
  Except String (AssertionArena × AssertionRef)

theorem substAssertion_sound
    (hc : substAssertion arena θ A = .ok (arena', A'))
    (hθ : θ.Holds target source s.h) :
    Sat arena' source m s A' ↔ Sat arena target m s A

end Verification.Parity
```

The equivalence also requires arena-extension and scope validity, carried by the checked substitution result. It applies to all constructors, including effects inside boxes and bound logical witnesses.

Freshness transport is directional:

```lean
namespace Verification.Parity

/-- NEW: a store fresh for a later callee mark is fresh for the caller.
The reverse implication is unavailable without stronger evidence. -/
theorem fresh_mark_mono
    (hm : caller ≤ callee)
    (hf : Footprints.FreshAt callee v) :
    Footprints.FreshAt caller v

end Verification.Parity
```

For mark-sensitive posts, the checker transports each freshness occurrence with this rule or an exact selected-location proof. It does not rename marks by textual substitution. Positive freshness is sufficient for the selected grammar; any future negative freshness construct needs its own variance rule.

Substitution of paths into regions uses their actual entry observations. If a substituted path is mutable, the checker must supply the corresponding agreement or rigidity evidence before using a box at a different anchor.

### Support contexts throughout a modality

Retain contextual support as a semantic generalization, but distinguish actual-step evidence from modal evidence.

```lean
namespace Verification.Parity

/-- NEW: a contextual support may depend on both endpoint states. -/
abbrev SupportContext :=
  Env → Nat → TolerantFrames.IndexedHeap →
    TolerantFrames.IndexedHeap → Prop

/-- CHANGED from heap-only Supports: the assertion uses the common Sat. -/
def Supports (arena : AssertionArena) (C : SupportContext)
    (S : Footprints.Footprint) (A : AssertionRef) : Prop :=
  ∀ ρ m s s',
    TolerantFrames.Admissible s s' →
    C ρ m s s' →
    Sat arena ρ m s A →
    Footprints.Supported S ρ s.h s'.h →
    Sat arena ρ m s' A

/-- NEW: context evidence valid over the entire modal domain.
It covers a start reached from the anchor and every subsequent
effect-bounded transition from that start. -/
def ContextThroughout (arena : AssertionArena)
    (K : AssertionRef) (Φ : Footprints.Footprint)
    (C : SupportContext) : Prop :=
  ∀ ρ m anchor s s',
    Sat arena ρ m anchor K →
    TolerantFrames.Action Φ ρ anchor s →
    TolerantFrames.Action Φ ρ s s' →
    C ρ m s s'

/-- NEW: finite evidence for the preceding universal statement. -/
inductive ContextEvidence

/-- NEW: checked contextual support plus respect introduces a box. -/
theorem tolerant_frame
    (hs : Supports arena C S A)
    (hc : ContextThroughout arena K Φ C)
    (hr : Respects arena K Φ S) :
    ∀ ρ m s,
      Sat arena ρ m s K →
      Sat arena ρ m s A →
      ∀ s', TolerantFrames.Action Φ ρ s s' →
        Sat arena ρ m s' A

end Verification.Parity
```

`ContextEvidence` has constructors for:

- `true`.
- Facts supplied by every well-formed state.
- Singleton-contract stability.
- Proved invariant assertions.
- Path rigidity under the whole effect.
- Conjunction and weakening through checked derivations.

For a repeated frame use, the certificate also carries the stable-domain evidence needed to re-establish respect at the new anchor. Initial separation knowledge alone is not silently reused after it may have changed.

The existing `ReadContext.Holds` becomes one supported context instance. A proof of `ReadContext.Holds` for one observed write can justify an actual-step consequence through Entry. It cannot construct `ContextThroughout` without the universal evidence above.

Both alternative supports for `apart` are available: grow/keep and keep/grow over the complete store-plus-cells regions. Grow/grow is rejected as a general support.

### Migration and open work

Leg 2 owns role-aware rebasing and its basic coverage lemmas. Leg 4 owns assertion substitution, contextual support and checked evidence. Leg 5 integrates these into actual visits and graph composition.

`freshField`, depth-one `nodeAgree`, blanket `.all` fallback, and actual-step contexts used as modal evidence are replaced in their owning legs.

Search for arbitrary rigidity witnesses is incomplete by design. The interface accepts any derivation in the fixed evidence language; recognition of more instances does not change the semantic definition.

## Ownership and landing order

Paths in this table are relative to `lean/Verification/` unless stated otherwise.

| Owner | Exclusive files and responsibility |
|---|---|
| **Leg 2: shared foundation** | `Semantics/Worlds.lean` for role/category integration; `Footprints.lean`, `ClosedFootprints.lean`, `FootprintRebase.lean`, `FootprintStability.lean`, `CallEffects.lean`, `ExceptionalPosts.lean`; `Source/EffectJson.lean`. Owns general signature regions, both exits and common action semantics. |
| **Leg 3: primitive views** | `Semantics/Calculus.lean`, evaluator/substitution dependencies, `ElementWrites.lean`, primitive typing modules; primitive sections of `Programs/HeapExpressionRules.lean`, `ExpressionClaims.lean`; affected `Source/Fragment*` and lowering. Owns the later `Worlds.lean`/`Heaps.lean` view-invariant patch after leg 2’s role declarations. |
| **Leg 4: assertions and arithmetic** | New `Semantics/ParityAssertions.lean`, `ParityDerivations.lean`, `ParityEvidence.lean`; `IndexFacts.lean`, `HeapKnowledge.lean`, `StepRelations.lean`, `Survival*.lean`; `Programs/IndexWrites.lean`, `PromiseCalls.lean`; support and atom-rule portions of tolerant-frame modules. |
| **Leg 5: actual local and graph certificates** | New `Programs/LocalCertificates.lean`; `ExpressionEffects.lean`, `ArgumentRegionCertificates.lean`, `ArgumentRegionGraph.lean`, regional consumers, `SinglePass.lean`, `SinglePassClose.lean`; command/transfer portions of tolerant-frame modules and minimal `Source/Claims/PassProposals.lean` integration. |

Shared files have sequential ownership:

- Leg 2 lands `CallEffects`; leg 4 then migrates call consequence consumers.
- Leg 3 lands primitive heap-rule declarations; leg 4 then replaces their preservation filtering.
- Leg 4 lands assertion/evidence declarations; leg 5 then changes pass records.
- Leg 1’s visit-record work is the base for leg 5, not a parallel owner of `SinglePass`.

Each semantic owner also owns its producer transaction. The integration owner serializes edits to `tools/declaration-types.mts`, `type-term.mts`, `type-graph.mts`, `compiler-api.mts`, `named-record.mts`, `intrinsics.mts`, `library-types.mts`, fragment producers, and their fixtures.

The declaration order is:

1. **Pure vocabulary and algebra:** `ViewFormat`, categories/selectors, selector laws, path/substitution data, exit products and typed reference identifiers. These can land without changing accepted behavior.
2. **Common region semantics:** heap-only `Region.mem` over contents categories with the connecting theorem to roles, action, inclusion/disjointness and closed normalization; the three-category split after I3's tags. Migrate existing consumers in the same buildable series. There is one authoritative interpretation.
3. **Assertion arena and semantic evidence:** nodes, scope validity, `Sat`, substitution, rebasing and support meanings, with basic interpretation lemmas. They can be unused by acceptance while proved.
4. **Primitive representation:** runtime tags, total conversion, store invariants and operational rules, with preservation. Metadata is removed as its consumers migrate.
5. **Checked derivations and local records:** finite proof datatypes precede their soundness proofs. Primitive and call rules produce records; edges consume the common consequence checker.
6. **Behavioral integration:** general signature wire, actual visit composition, removal of the replaced preservation and reconstruction paths.

A declaration may precede its acceptance integration. An unproved semantic placeholder may not. No temporary duplicate format is accepted for compatibility.

## Note corrections exposed by these interfaces

The following changes are within the agreed scope.

1. **State notation.** Region interpretation reads the entry heap's contents categories, which equal the entry world's role categories on well-formed states. Admissibility at differing budgets uses truncation followed by extension. Environment agreement is on named values, with explicit substitution for graph slots.

2. **View representation.** W2 already requires density; the implementation must satisfy it. The note should identify the fixed format and length descriptor and format-admitted cells. It should remove any claim that view length necessarily occupies a separate value location.

3. **View conversion and assignment.** State the four admitted formats, total numeric conversion, numeric `-0`, invalid-index behavior, and the assignment result. Exact equality for floating-point observations must not assert NaN-payload preservation.

4. **View contracts.** The world condition for mutable view stores must admit all format-valid replacement contents. Arbitrary stronger element refinements are assertions, not permanent writable-store contracts.

5. **Overlap abstraction.** State that another view’s observations may change conservatively while the receiver’s other indices remain exact. Store separation of two views does not establish byte separation.

6. **Contextual support.** A context valid for one actual transition proves only that transition’s consequence. Modal introduction and repeated use require context evidence over the quantified domain.

7. **Loop and prefix rules.** The body may be checked under `I ∧ box Φ R`. Every interior use needs a prefix certificate; a restoring exit post is insufficient. Recurrences include anchor transport.

8. **Both exits.** Call substitution, Entry, composition and handler transfer use independent normal and exceptional effects and posts. Caught throws compose the throwing prefix with the handler.

9. **Arithmetic semantics.** Specify defined observations, exact-number premises, the shift/mask ranges, UTF-16 length and reads, normal concatenation length, and the explicit `2^53` boundary alternative.

10. **Ordinary exact posts.** State the successful in-bounds write, write-at-length and append posts used by the common consequence rules.

11. **Reliance.** Preservation at callback observation points and density of a native operation’s constructed result are separate obligations.

12. **Scope annotations.** The “five of eleven” count disagrees with the twelve-row pattern table. Theorem-scope annotations should name proved statements and executable routes only when those obligations are discharged.

No correction adds closure-capture specifications, nonlinear products, left shifts, bitwise-or, byte-range separation, or arbitrary public exact-update contracts.

## Completion obligations

The declarations above are design obligations. Their proofs and executable integrations establish parity; passing examples alone does not.

The implementation must retain the exact `Mode8Accepted` premise and the conclusion covering every member of `PassUnitSafe`, through exhaustive `FunctionPlan.certify`. Every accepted plan variant needs the common certificate interpretation. A retained record, an inferred effect or a checked arithmetic consequence is not itself an accepted unit.

This design was prepared by read-only inspection. No files were edited, and no builds or suites were run.