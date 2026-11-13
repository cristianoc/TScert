# Draft: fixed location kinds

The design of location kinds for the model of the
[Tolerant frames note](../REFERENCES.md#the-tolerant-frames-note) (§§2–3):
every location of a heap has a kind, fixed for its life, and a fact
supported by locations of one kind survives an effect confined to another
by kinds alone. With kinds in every well-formed state, three statements of
the note hold with no premise beyond the state: a typed array's length is
immutable (View), every store lists allocated element cells, and an
allocated array is apart from every older one (Alloc).

Claims are labelled **proved**, with the Lean name, in the kinded
development: [Kinds](../../lean/Verification/Semantics/Kinds.lean),
[KindsAllocation](../../lean/Verification/Semantics/KindsAllocation.lean),
[KindsWrites](../../lean/Verification/Semantics/KindsWrites.lean),
[KindsNatives](../../lean/Verification/Semantics/KindsNatives.lean),
[KindsStates](../../lean/Verification/Semantics/KindsStates.lean),
[KindsCapabilities](../../lean/Verification/Semantics/KindsCapabilities.lean),
[KindsContracts](../../lean/Verification/Semantics/KindsContracts.lean) and
[KindsModelRules](../../lean/Verification/Programs/KindsModelRules.lean),
each theorem checked by the
[axiom check](../../lean/Verification/Tests/AxiomCheck.lean) in its block
for the kinds of the Tolerant-frames model. That development is inactive:
the active proofs use the world of `Worlds.lean`, and
[the activation](#activation) replaces it by the kinded one. Claims about
the activation are labelled **planned**.

## The existing mechanism this extends

[Changes and footprints](../FOOTPRINTS.md#changes-and-footprints) own
regions, changes, support and respect; the world of
[Worlds](../../lean/Verification/Semantics/Worlds.lean) owns each location's
contract, fixed at allocation and kept by extension, and `HeapOk`
([Heaps](../../lean/Verification/Semantics/Heaps.lean)) relates a heap to
it; semantic typing gives each allocation its world entries; safety
([Safety](../../lean/Verification/Semantics/Safety.lean),
[ExceptionalPosts](../../lean/Verification/Semantics/ExceptionalPosts.lean))
states what a call guarantees on its normal and exceptional exits. A kind
is one more fixed part of a world entry, beside the contract; structural
satisfaction is one more conjunct of `HeapOk`; a storage capability is the
typing's grant of a location, carrying its role; and a native's contract is
a safety statement whose postconditions may read the exit world. No second
effect system is introduced: the frame mechanism reads kinds from the world
as it reads contracts.

## 1. Roles and worlds

A role refines a kind:

```math
\mathrm{Role} ::= F \mid C \mid E \mid S_{\mathrm{array}} \mid S_{\mathrm{view}(N)} \mid I
```

F holds an object's ordinary property, C a binding's storage, E an element,
S a store, I an object's identity (a location holding `null` that every
object allocation adds). An ordinary array's store and a typed array's view
store of fixed length $`N`$ are two forms of S, distinguished by role.

A world entry is a pair of a role and a contract. The kinded world
`Kinds.WorldT n` is the stratified construction of `WorldT`, each entry's
contract inspecting kinded worlds below `n`, so a contract can read roles.
Extension appends entries and keeps every old pair; truncation keeps every
role and restricts the contracts. The world records a location's role
permanently, at the allocation that justifies it: the typing derivation of
that allocation chooses the role (§4), and no later type can relabel the
location.

The calculus's terms and steps are those of `Semantics/Calculus.lean`:
roles live in worlds, which are proof-level. The typing's storage
capabilities and the lowering's metadata carry roles (§4), so typing and
lowering metadata change at the activation; calculus terms and steps do
not.

## 2. Reference validity and view metadata

$`\mathrm{RefsOk}(W,t)`$ holds when every location a term refers to has the
role its position demands: an object's identity is in I; its slot under
`[]` is in $`S_{\mathrm{array}}`$; under `[[viewElements]]` it is in
$`S_{\mathrm{view}(N)}`$ for some $`N`$; under every other key it is in F
or C; every cell a store lists is in E; and every object's field map has
valid view metadata. `RefsOk` covers every subterm, the captures, bound
targets, receivers and prefixes of call descriptors, and a graph's node
expressions, and it reads the world only.

**View metadata validity** of a field map $`fs`$, wherever the metadata
occurs (`ViewMetaOk`):

- every location $`fs`$ gives `[[viewLength]]` is a **length metadata
  location** of some $`N`$: a location of role F whose contract admits the
  value $`N`$ alone (`LengthMeta`);
- every location $`fs`$ gives `[[viewElements]]` has role
  $`S_{\mathrm{view}(N)}`$, and $`fs`$'s `[[viewLength]]` location is a
  length metadata location of that same $`N`$.

The first clause covers a host object that holds its length alone, which
the length observation `viewLengthOf`
([IndexFacts](../../lean/Verification/Semantics/IndexFacts.lean)) reads as
a typed array. It is the validity of the representation that observation
reads.

## 3. Well-formed states

The structural part of satisfaction is unindexed, so it holds at every
budget, zero included:

```math
\begin{aligned}
\mathrm{Shape}(W,F|C|E,u) &\iff u\text{ is a source value}\land\mathrm{RefsOk}(W,u)\\
\mathrm{Shape}(W,S_{\mathrm{array}},u) &\iff u\text{ is a store}\land\mathrm{RefsOk}(W,u)\\
\mathrm{Shape}(W,S_{\mathrm{view}(N)},u) &\iff u\text{ is a store of length }N\land\mathrm{RefsOk}(W,u)\\
\mathrm{Shape}(W,I,u) &\iff u=\mathtt{null}\\
\mathrm{HeapOk}(n,W,h) &\iff h\text{ meets }W\text{'s contracts below }n\land
  \forall l.\ W(l)=(r,c)\Rightarrow\mathrm{Shape}(W,r,h(l))
\end{aligned}
```

A **state** is a positive budget $`n`$, a world $`W`$ at $`n`$ whose
contracts survive allocation, and a heap $`h`$ with
$`\mathrm{HeapOk}(n,W,h)`$. A transition $`s \rightsquigarrow s'`$ is
admissible when $`n' \le n`$ and $`W'`$ extends $`W`$ truncated to $`n'`$.

The environment is inside the well-formed state. A **state over** $`\rho`$
is a state whose world validates every root of $`\rho`$:

```math
\mathrm{RootsOk}(W,\rho) \iff \forall x.\ \mathrm{RefsOk}(W,\rho(x))
```

Assertions and modalities range over states over their environment. An
admissible transition keeps every role, every valid reference and every
length metadata location with its length, so it takes a state over
$`\rho`$ to a state over $`\rho`$ (**proved**, `Admissible.roleAt`,
`Admissible.refsOk`, `Admissible.lengthMeta`, `RootsOk.admissible`,
`State.next`); extending $`\rho`$ by a value valid in the world keeps every
existing binding (`RootsOk.set`). At activation the typed entry obtains
$`\mathrm{RootsOk}`$ from `EnvOk`
([TypingBasics](../../lean/Verification/Programs/TypingBasics.lean)),
strengthened by reference validity (**planned**).

The running term is valid too: safety requires $`\mathrm{RefsOk}(W,t)`$ of
the running term at every budget (§5).

## 4. Storage capabilities

Roles belong to allocation provenance. An object literal `{ value: v }`
and a binding cell holding `v` are the same calculus allocation; an
array's store slot is one more of its kind. What tells their locations'
roles apart is the typing derivation that justified the allocation, through
the capability it grants.

A **storage capability** is a key and a family of permitted pairs of a
role and a contents type. Its meaning at a field map $`fs`$ is that the key
denotes a location with one of those roles and a contract agreeing with the
paired type:

```math
\mathrm{cap}=(k,P)\qquad
\mathrm{cap}\models_W fs \iff \exists l.\ fs(k)=l\land W(l)=(r,c)\land(r,T)\in P\land c\simeq T
```

where $`c \simeq T`$ is agreement at every budget below the world's. The
constructions:

- an ordinary property of type $`A`$: $`(f,\{(F,A)\})`$;
- a binding's storage of type $`A`$: $`(\mathtt{value},\{(C,A)\})`$;
- an ordinary array's store: $`([\,],\{(S_{\mathrm{array}},A)\})`$;
- a typed array's element store, over every length:
  $`(\mathtt{[[viewElements]]},\{(S_{\mathrm{view}(N)},A_N)\mid N\})`$.

**Proved** (`KindsCapabilities`): an allocation choosing role $`r_i`$ and
type $`A_i`$ for its $`i`$-th key establishes every capability over that
key permitting $`(r_i,A_i)`$ (`Capability.holds_alloc`), with the object
literal, the binding cell and the array store as instances
(`field_holds_literal`, `binding_holds_cell`, `arrayStore_holds_array`); a
holding capability exposes its target's role (`Capability.Holds.role`);
two capabilities over one key of one object share a role
(`Capability.Holds.common`), so a binding capability and a field capability
never both hold of one object (`binding_not_field`) and no inclusion takes
one to the other (`binding_not_le_field`); extension and truncation keep a
capability's meaning; a write of contents with the target role's shape and
the paired type keeps `HeapOk` (`Capability.At.write`).

**Storage typing** (**proved** where named). A type states each storage
position's role as a tag, $`\mathrm{StorageRole} ::= \mathtt{field} \mid
\mathtt{cell} \mid \mathtt{arrayStore} \mid \mathtt{viewStore}`$
([StorageRoles](../../lean/Verification/Semantics/StorageRoles.lean)), whose
meaning is the capability $`\mathrm{ofRole}(s,k,A)`$ permitting each role
the tag names with $`A`$ (`Capability.ofRole`). Distinct tags name disjoint
roles (`StorageRole.permits_unique`), so two positions over one key of one
object state one tag (`ofRole_exclusive`) and an inclusion keeps the tag
(`ofRole_le`); an allocation choosing role $`r`$ establishes every position
whose tag names $`r`$ (`ofRole_holds_alloc`). The positions carrying a tag
are the write-granting ones: every invariant field of a record operand
(`Clause.refs`, `dict`, `callable`, `ctors`), every optional field, every
writable index; a view and a store's element position carry none.
`Fields`, `recT`, `recT_alloc` and `recT_at`
([Types](../../lean/Verification/Types/Types.lean)) range over positions;
mapping and substitution keep every role (`storage_map`,
`storageOf_famsOf`); normalization concatenates operands; covering requires
equal roles (`CoversFields`), so no covering takes a binding's storage to an
ordinary property (`binding_not_covers_field`). The allocation rule
(`HasTyWith.alloc`) takes each key's role from the claimed type:
lowering states `field` for an object literal, `cell` for a binding's cell
and its uninitialized marker (`CellClaims.reference` takes the role), and
`arrayStore` for an array's store slot; `AllocationWorlds.next` takes the
allocation's entries. Active worlds record no role, so these typings carry
the role without checking it; the activation checks it against the kinded
world, and adds to the allocation rule that each role fits its key (§2) and
its initializer (§9).

## 5. The native-contract condition

A **world-indexed postcondition** receives the exit world as well as the
budget, the heap and the result; an exceptional one the exit world, the
budget and the heap. A postcondition of the heap and result alone lifts by
ignoring the world (`WPost.lift`, `WExc.lift`).

**Safety with world-indexed postconditions** (`SafeW`) is the safety
predicate of `ExceptionalPosts` over kinded worlds with one structural
component: the running term's references are valid in the world at every
budget, zero included. At a positive budget the term is a value of the
result type meeting the postcondition at the current world and heap, or
throws a value of the exception family meeting the exceptional
postcondition there, or steps to a heap meeting an admissible extension of
the truncated world, where safety continues.

The one condition on every native and every call contract
(`NativeContract`): from every well-formed entry configuration below the
budget (a heap meeting an admissible extension $`U`$ of the truncated
world; callee, receiver and actuals valid in $`U`$ and of their input
types; the precondition) the invocation is `SafeW` at its result type, its
normal postcondition and its exceptional one. Every execution prefix of
such a call then ends in a well-formed configuration under one extension
of $`U`$, its budget possibly zero (**proved**, `SafeW.run`,
`NativeContract.run`), and a thrown value is of the exception family with
valid references (`Thrown.refs`). Typing, structural validity and the
postconditions read one successor world.

The condition applies at callback boundaries recursively: a callback's
allocations take whatever roles its own typing chooses, and a native's
element allocation after the callback extends the callback's world with E
entries. An effect without `onThrow` bounds no exceptional heap; the
structural component of safety still holds there.

A footprint states where a call may change the heap, not what it may
write there or allocate. The relations below bound locations only and
give no well-formed exit by themselves: `ElementWrite.changes`
(`elementWrite_not_respects`: it lets a field holding a string come to hold
a store), `array_native_post`, `receiverOwn`, `receiverStore`,
`fresh`, `freshObject` and an unrestricted `excPost`. `native_shaped`
proves an array native's element-storage phase preserves kinds under its
stated premises; a whole native, callbacks included, meets
`NativeContract`.

## 6. The view-element write

The primitive contract of a typed array's element write (`%ByteSet%`,
`fill`, `copyWithin`, `set`) is a relation from the entry world $`W`$ and
heap $`h`$ to the exit world $`W'`$ and heap $`h'`$ (`ViewWrite`):

- $`W'`$ extends $`W`$ truncated to the exit budget, and
  $`\mathrm{HeapOk}(n',W',h')`$: the domain grows with the world, every
  location, fresh ones included, has its role's shape and meets its
  contract;
- every old location whose role is no view store keeps its contents;
- every cell an old view store newly lists is fresh against $`h`$;
- the exact form adds `ExactWrite` of the designated view, index and value.

It constrains every view store, whichever view the call names: an
overlapping view may change, exactness constraining the designated one. An
updated view store lists fresh cells, so old element cells keep their
contents. The relation is a world-indexed postcondition
(`ViewWrite.post`). **Proved**: an ordinary array's store is kept
(`ViewWrite.keeps_array`); an old $`S_{\mathrm{view}(N)}`$ location holds a
store of length $`N`$ listing element cells of $`h'`$
(`ViewWrite.view_store`); from a well-formed entry heap, the coarse change
of `ElementWrite` follows (`ViewWrite.changes`, `ViewWriteOf.holds`). Two
views over the same bytes both change under one exact write while an
ordinary array's store is kept, between two well-formed heaps
(`viewWrite_overlap`). The numerical correspondence between overlapping
views' elements and their shared bytes is part of the host contract's
audit; kinds do not state it.

## 7. Allocated cells

Every cell a store of a well-formed heap lists has role E and is a
location of the heap, at every budget, zero included (**proved**,
`HeapOk.store_cells`, from `HeapOk.kinds`). This structural consequence is
what every consumer of allocated cells needs: `RootCells` holds at every
state and after every action (`rootCells`, `rootCells_box`), every store of
every state lists allocated cells (`storeCells`, `storeCells_invariant`),
and the dangling store `[[5], null, null]` meets no kinded world at any
budget (`dangling_excluded`).

`CellsCtr` quantifies over other worlds and every store a contract admits
there, which structural validity of the current heap does not give; at
activation it is removed with `StoreCells`, their establishment machinery
and `rootCells_not_invariant`, and each consumer uses the structural
consequence (**planned**).

## 8. What is proved

- **Kinds are fixed.** Kinds are disjoint (`kinds_disjoint`), kept by
  extension (`WExt_kindAt`) and by truncation to any level (`kindAt_trunc`);
  `Shape` is monotone in extension (`Shape_mono`) and survives truncation
  (`Shape_trunc`, `HeapOk_trunc`).
- **Kinds partition a well-formed heap** (`HeapOk.kinds`): each location has
  exactly one kind; a location is in S exactly when it holds a store; every
  store lists only element cells, all locations of the heap.
- **The audit's counter-heap is excluded** (`counterheap_excluded`): no
  world satisfies `[[1], 0, null]` with the array `{[]: 0}` and the object
  `{f: 1}` both valid, since location 1 would be in F or C and in E.
- **(View)**: the length a value with valid references reads through
  `viewLengthOf`, as defined, is kept by every admissible transition, with
  no stability premise (`viewLengthOf_kept`); the length of a root is
  invariant (`viewLength_invariant`); a linear fact whose current terms are
  roots' integers and view lengths holds after every action of the top
  footprint (`view_box`); no admissible transition changes a valid typed
  array's length from 1 to 2 (`view_change_excluded`).
- **Allocated cells**: §7.
- **Alloc**: an array allocated past a well-formed heap is apart from every
  store of that heap the later heap keeps, with no premise on the old
  store's cells (`alloc_apart`); the allocated empty array is fresh, of
  length 0 and apart from every array of the entry heap (`alloc_post`), and
  the extended heap is well-formed with the array valid
  (`alloc_wellformed`).
- **Allocation** (`HeapOk_appendWs`; `makeFields_shaped` for any object,
  with `objectLiteral_shaped`, `bindingCell_shaped`, `closure_shaped`,
  `arrayObject_shaped`, `typedArray_shaped`, `hostLength_shaped`;
  `arrAlloc_shaped` for a store literal's elements; `thrownError_shaped`
  for a fresh error).
- **Writes** (`write_sound`; `writeField_shaped`, `writeOrdinary_shaped`,
  `bindingWrite_shaped`, `storeWrite_shaped`, `lengthStore_refs`;
  `setPresent_shaped`, `setGrow_shaped`).
- **Steps that change no heap keep references valid** (`step_refs`):
  congruences, substitution, a graph's entry, a node's instantiation, every
  continuation's environment map, handlers and raises, reads, spreads,
  copies, tests and arithmetic.
- **Copies** (`mergeParts_cat`): no copied key is `[]`, and every copied
  value under a key other than `[[viewElements]]` is a source value.
- **Array natives** (`Arr.natives_within`, `Arr.Within.refs`,
  `native_shaped`): `Set`, `Delete`, a length change, `push`, `pop`,
  `shift`, `unshift`, `reverse` and `sort`'s writeback keep a store's cells
  among the original and fresh ones, and their element-storage phase
  preserves kinds when the fresh locations are element cells holding
  source values and the old locations changed are element cells holding
  source values.
- **States, capabilities, native contracts and the view write**: §§3–6.

## 9. The typing premises

Each step below preserves kinded satisfaction only under the premise
listed; the raw step admits more. The activation discharges them from the
typing rules, through the capabilities of §4.

- **Object allocation** (`Step.makeFields`): the rule's role for each key
  fits it (a store slot's under `[]`, a view's under `[[viewElements]]`, F
  or C under any other key); each initializer has its role's category (a
  source value in F or C, a store in S); the field map has valid view
  metadata, which holds where it names neither metadata key. A source
  allocation names neither key (reserved spellings); a binding allocation
  chooses C, an object literal F.
- **Store literal** (`Step.arrAlloc`): each initializer is a source value.
- **Field write** (`Step.writeField`): the payload has the category of its
  target's role: a source value in F or C, a store under `[]` (a grown
  store's writeback, a length write).
- **Present element write** (`Step.setPresent`) and **hole or past-end
  write** (`Step.setGrow`): the payload is a source value.
- **Natives**: `NativeContract` (§5).
- **Copies** (`Step.mergeV`): an ordinary accumulator owns no
  `[[viewElements]]` slot, or the copy's allocating rule gives that key a
  view role with its length metadata.
- **Every step**: the running term's references are valid (`SafeW`'s
  structural component), and the environment's (`RootsOk`).

The steps that change no heap, the throwing steps and the fresh errors
preserve kinds for every well-formed state.

## Activation

The order of the remaining work (**planned**). Each commit builds its
whole dependency closure.

1. **Storage typing.** Carry roles through allocation specifications,
   semantic capabilities, syntax mappings and certification (§4); callers
   move to explicit object, binding and store capabilities. Calculus steps
   are unchanged.
2. **Native specifications.** Introduce world-indexed postconditions in
   `SafePost`
   ([HeapObservations](../../lean/Verification/Semantics/HeapObservations.lean)),
   `SafePostExc`, `PromiseWith` and `ConstructPromise`
   ([CallEffects](../../lean/Verification/Semantics/CallEffects.lean)),
   `SafeWith` and `SafeGraph`, heap-only postconditions lifted; replace
   `ElementWrite.changes` as the defining contract by `ViewWrite`, keeping
   the coarse change as its consequence and reproving `prefix_left`,
   `.stores`, effect weakening, meeting and invocation transport; prove
   call preservation on normal and exceptional exits and discharge each
   native's obligation. The audit follows every contract producer and
   invocation path: primitives, ordinary mutators, callback operations,
   constructors and result allocation, `receiverOwn`, argument regions,
   imported and external arrows, exceptional exits; and the builtin initial
   worlds (I identities, F properties, store slots).
3. **Activation, atomically.** Replace `Worlds.lean` and `Heaps.lean` by
   the kinded world (`ofEntries_entries` in place of `ofList_toList`, which
   cannot reconstruct roles); strengthen safety and state validity as in
   §§3 and 5; migrate every allocation and write; prove typed-step
   preservation, exhaustive over `Step`, and its run consequences. The
   modal theorems take the statements of `KindsStates` and
   `KindsModelRules`: `view_box` without `ViewStable`, `alloc_post` and
   `alloc_apart` from a well-formed entry heap. `view_not_invariant` and
   `rootCells_not_invariant` are deleted: their heaps meet no kinded
   world. `apart_not_kept_fresh` is kept, rebuilt over distinct I
   locations: freshness does not keep separation.
4. **Removal.** Delete the parallel worlds, `CellsCtr`, `StoreCells` and
   their establishment, and the element-value evidence that the state
   gives; the elementary separation lemma takes the name of separation
   from explicit bounds. The note's correspondence statements follow:
   roles in world entries, structural validity in every state, binding
   handles and store slots apart from ordinary properties.

The headline acceptance theorems keep their statements:
`passUnitVerdict_sound` and `PassUnit.mode8Accepted_sound`
([PassUnitRun](../../lean/Verification/Source/Claims/PassUnitRun.lean))
and `run_sound_single_pass`
([TolerantFramesSinglePassSound](../../lean/Verification/Programs/TolerantFramesSinglePassSound.lean));
their semantic dependencies become stronger.
