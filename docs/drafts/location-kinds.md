# Draft: fixed location kinds

The design of location kinds for the model of the
[Tolerant frames note](../REFERENCES.md#the-tolerant-frames-note) (§§2–3):
every location of a heap has a kind, fixed for its life, and a fact
supported by locations of one kind survives an effect confined to another
by kinds alone. With kinds in every well-formed state, three statements of
the note hold with no premise beyond the state: a typed array's length is
immutable (View), every store lists allocated element cells, and an
allocated array is apart from every older one (Alloc).

The kinded worlds are the active model
([kinded states](../SINGLE-PASS-PROOF.md#kinded-states)): worlds, heap
satisfaction and reference validity in
[Worlds](../../lean/Verification/Semantics/Worlds.lean) and
[Heaps](../../lean/Verification/Semantics/Heaps.lean), states in
[TolerantFramesCells](../../lean/Verification/Semantics/TolerantFramesCells.lean).
Claims are labelled **proved**, with the Lean name, in those modules and in
[Kinds](../../lean/Verification/Semantics/Kinds.lean),
[KindsAllocation](../../lean/Verification/Semantics/KindsAllocation.lean),
[KindsWrites](../../lean/Verification/Semantics/KindsWrites.lean),
[KindsNatives](../../lean/Verification/Semantics/KindsNatives.lean),
[KindsCapabilities](../../lean/Verification/Semantics/KindsCapabilities.lean),
[KindsContracts](../../lean/Verification/Semantics/KindsContracts.lean),
[KindsCalls](../../lean/Verification/Semantics/KindsCalls.lean),
[KindsEffects](../../lean/Verification/Semantics/KindsEffects.lean),
[ElementWrites](../../lean/Verification/Semantics/ElementWrites.lean)
(below the call effects, so that their postconditions can state the view
write) and
[KindsModelRules](../../lean/Verification/Programs/KindsModelRules.lean),
each theorem checked by the
[axiom check](../../lean/Verification/Tests/AxiomCheck.lean) in its block
for the kinds of the Tolerant-frames model. Claims not yet established are
labelled **planned**.

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
object allocation adds, whose contract admits `null` alone: `idCtr`, the
contract `objectEntries` gives every identity, and the representative host
world's). An ordinary array's store and a typed array's view
store of fixed length $`N`$ are two forms of S, distinguished by role.

A world entry is a pair of a role and a contract. The kinded world
`WorldT n` is the stratified construction of `WorldT`, each entry's
contract inspecting kinded worlds below `n`, so a contract can read roles.
Extension appends entries and keeps every old pair; truncation keeps every
role and restricts the contracts. The world records a location's role
permanently, at the allocation that justifies it: the typing derivation of
that allocation chooses the role (§4), and no later type can relabel the
location.

The calculus's terms and steps are those of `Semantics/Calculus.lean`:
roles live in worlds, which are proof-level. The typing's storage
capabilities and the lowering's metadata carry roles (§4); calculus terms
and steps carry none.

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
  length metadata location of that same $`N`$;
- a map naming `[[viewElements]]` names `[[host]]`: a typed array is a host
  object.

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
`Admissible.refsOk`, `Admissible.lengthMeta`, `RootsOk.admissible`). A graph
state's environment is valid (`ControlFlow.StateRefs`), and a typed term is
safe from an entry where its instantiation's references are valid
(`HasTyUsing.sound`).

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
allocation's entries, each the tag's concrete role at its value; the
allocation rules require each role to fit its key (§2) and its initializer's
category (§9), and the world records the role (`RoleIn`).

**Concrete roles** (**proved**, `KindsCapabilities`). The role an
allocation records for a position is its tag's role chosen by the contents
allocated there (`StorageRole.concrete`): `field`, `cell` and `arrayStore`
their role, `viewStore` the view store of the length of the store it is
allocated holding; none where the contents are not of the tag's category
(`StorageRole.Holds`). The recorded role is one the tag names
(`StorageRole.concrete_permits`), the contents have its category, a view
store's of its length (`StorageRole.concrete_cat`,
`StorageRole.concrete_view`), and contents of their tags' categories
determine every recorded role (`concreteRoles_of_holds`). A tag fits its
key (`StorageRole.fitsKey`: `arrayStore` under `[]`, `viewStore` under
`[[viewElements]]`, `field` or `cell` under any other key) exactly so that
every role it names is the slot's role (`StorageRole.slotRole_of_fitsKey`).
An allocation whose `[[viewLength]]` locations are fields admitting one
length alone and whose `[[viewElements]]` locations are view stores of that
length (`MetaFit`) gives a field map with valid view metadata
(`viewMetaOk_alloc`). Together: an allocation at concrete roles, each tag
fitting its key and its metadata fitting, keeps kinds
(`concrete_shaped`). `AllocationWorlds.next`'s entries record, beside each
contract, its tag's concrete role at the allocated value
(`AllocationWorlds.roles`).

**Overlapping capabilities agree.** One location is granted by every
storage position over its key. An allocation at a dictionary
(`HasTyWith.allocDict`) requires each named field's role, and each writable
optional field's, to be that of every writable index whose class may admit
its key; the certificate check decides the same conjuncts. A readonly
optional field is a view of whatever location holds the key and states no
role: covering requires a role of a writable optional target only
(`CoversOptional`), and the storage a clause grants lists writable optional
fields only (`Clause.storage`). A key-adding write's proposal
(`Synthesis.growth`) takes the role every applicable declaration states (the
optional field of each arm, each writable index admitting the key), `field`
where none does, and proposes nothing where they differ.

**Inclusion up to agreement** (**proved**). Covering proves contents types
equivalent, not equal; one position grants no more than another below a
budget exactly when key and tag are the same and the contents agree below
it (`Capability.ofRole_leBelow_iff`), which keeps a capability's meaning
(`Capability.Holds.weakenBelow`); `ofRole_le` is the instance at equal
types.

**The premises the role choices rest on** (**proved** where the typing
rules check them: key fit `StorageRole.fitsKey` and the absence of metadata
keys at every typed allocation, the payload premise at every allocation and
write):

- a stable key, absent from the claim's positions, gets `field`
  (`allocRole`): its key is an ordinary key, which the rule reads from
  typing today (no reserved key: `hostKey` and, with stable keys, `[]` are
  excluded), and its contents are a source value, which the part's
  payload premise gives (`Payload`, `Payload.stored`);
- a fresh array's and a primitive wrapper's prototype slot gets `field`:
  the prototype reference is an ordinary property, a source value;
- a key-adding write's new location gets the agreed role above, or `field`
  for an own property the write makes on an ordinary object: the write's
  typing must establish that the object is ordinary (it owns no store slot
  and no metadata key) and that the written value is a source value;
- every initializer's category (`StorageRole.Holds`) follows from the
  payload premise of its part's rule (`Payload`: a field's, a cell's or an
  element's contents' type in `V`, a store slot's in `S`;
  `Payload.stored`, `Payload.element`).

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
normal postcondition and its exceptional one, each given the entry budget,
world $`U`$ and heap and reading the exit world (`CPost`, `CExc`). Every execution prefix of
such a call then ends in a well-formed configuration under one extension
of $`U`$, its budget possibly zero (**proved**, `SafeW.run`,
`NativeContract.run`), and a thrown value is of the exception family with
valid references (`Thrown.refs`). Typing, structural validity and the
postconditions read one successor world.

**Call preservation** (**proved**, [KindsCalls](../../lean/Verification/Semantics/KindsCalls.lean)):
a run of a `SafeW` term ending in a value or a throw with budget left ends
under one extension of the truncated entry world where the heap is
well-formed, the term valid, and the result type with the normal
postcondition, or the exception family, the thrown value's valid references
and the exceptional postcondition, hold (`SafeW.exit`); a term safe in an
evaluation context's hole is safe in the context when the context continues
from each normal exit at the world that exit reached (`SafeW.bind`), and a
context stepping a throw to a handler enters the handler at the throwing
configuration's world and heap, well-formed whatever the exceptional
postcondition states (`SafeW.handle`); a callee meeting `NativeContract`
makes its invocation `SafeW` (`NativeContract.safe`); the condition is
closed downward (`NativeContract.down`) and a forwarding descriptor meets it
when its target does, the target's postconditions read from the
descriptor's entry world truncated by the forwarding step
(`NativeContract.bound`); world-indexed postconditions implying heap-only
ones give `SafeW` at the heap-only ones lifted (`SafeW.erase`).

**Signatures over kinded worlds** (**proved**,
[KindsEffects](../../lean/Verification/Semantics/KindsEffects.lean)). A
signature's normal postcondition, given the call's entry world $`W`$ and
heap $`h`$, is its heap postcondition and, where it states an element
write, the view write from $`(W,h)`$ to the exit world and heap
(`Effect.postK`); its exceptional one is its heap postcondition on a throw
(`Effect.excPostK`). A promise over kinded worlds (`PromiseK`) is
`NativeContract` at these; a construct signature (`ConstructK`) is the
condition of `new` (`NativeConstruct`), whose construction is safe
(`NativeConstruct.safe`). Two promises of one value whose signatures mean
the same result (`Effect.sameResult`) give the promise of their meet
(`PromiseK.combine`): the first run's world and its view write are kept,
the second run takes the same steps and its heap postconditions hold at
the same exits (`SafeW.cross`), and the two view writes are one, since the
signatures state the same element write (`Effect.postK_meet`). A promise
weakens to a signature it covers, its element write included
(`PromiseK.weaken`, `Effect.coversK_sound`); allocation between the call's
entry and its body composes with the postcondition, the view write
included (`Effect.postK_prefix`, `ViewWrite.prefix_left`); a fact of the
world that extension and truncation keep holds at every exit
(`SafeW.world`).

**One world per exit** (**proved**, `gate_write`, `gate_handled`). A
callback allocates `{ f: x }`; then a value meeting two such promises is
called with a view write among its effects. Every normal exit of
`let o = { f: x } in g(r, args)` is at one world where the object's field
capability holds, the heap meets the world in both parts (`SafeW.exit`),
and both signatures' postconditions hold, the view write from the call's
entry world; every throw into a node's handler enters it at one world with
the heap well-formed, the thrown value valid, the capability, and the
meet's exceptional postcondition.

**Early evidence** (**proved**): the callback `throw { f: v }` is `SafeW`
with no exceptional postcondition from every well-formed configuration
(`allocThrow_safe`), and run in a graph node with a handler it reaches the
handler's entry at a heap well-formed under one extension of the entry
world (`callback_throw_handled`); a callback's well-formed exit followed by
a native's write-back of fresh element cells and an ordinary array's store
is well-formed under one world extending the callback's
(`callback_writeback`).

The active safety predicates take world-indexed postconditions:
`SafePostW` and `SafePostExcW`
([HeapObservations](../../lean/Verification/Semantics/HeapObservations.lean),
[ExceptionalPosts](../../lean/Verification/Semantics/ExceptionalPosts.lean))
read the exit world, `SafePost` and `SafePostExc` are their instances at
lifted heap-only postconditions, and `PromiseWith` and `ConstructPromise`
([CallEffects](../../lean/Verification/Semantics/CallEffects.lean)) state
the call safe at the effect's postconditions lifted (`Effect.postW`,
`Effect.excPostW`). `SafeWith` and `SafeGraph` state no heap postcondition;
their result families read the exit world.

The condition applies at callback boundaries recursively: a callback's
allocations take whatever roles its own typing chooses, and a native's
element allocation after the callback extends the callback's world with E
entries. An effect without `onThrow` bounds no exceptional heap; the
structural component of safety still holds there.

A footprint states where a call may change the heap, not what it may
write there or allocate. The relations below bound locations only and
give no well-formed exit by themselves: `ElementWrite.changes`
(`elementWrite_not_respects`: it lets a field holding a string come to hold
a store), `array_native_post`, a change confined to one location and
arbitrary there, as `receiverOwn`, `receiverStore` and an argument store
region allow at the locations they name (`confined_not_respects`), an
allocation whatever the fresh locations hold, as `fresh` and `freshObject`
allow (`allocation_not_respects`), and an unrestricted `excPost`
(`unrestricted_not_respects`). `native_shaped`
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
- the exact form adds `ExactWrite` of the designated view's element type,
  view, index and value: the value is a safe integer within the type's
  range (`ElementKind.Takes`), and the cell at the index holds the type's
  conversion of it (`ElementKind.convert`, the host's ToUint8, ToUint16 or
  ToInt32 there, the value itself for `Float64Array`:
  `ElementKind.convert_takes`). An exact effect's precondition states the
  range (`ElementKind.preFacts`, required by the effect decoder), and a call
  meeting it writes such a value (`ElementKind.takes_of_requires`).

In an effect's heap postcondition, the element write's defining
contract is the same relation read against a role assignment of the entry
heap (`CallEffects.ViewWriteA`, `ElementWrite.Holds`): a stated hypothesis
`RolesFit` constrains the assignment by the entry heap's categories, and the
relation states the domain's growth, the kept contents of every location
whose role is no view store, each view store's length with its cells
locations of the exit heap, and the freshness of newly listed cells. Three
conjuncts read the kinded world and wait for it: the listed cells are E,
every location has its role's shape, and the exit heap meets the exit world.
`ViewWriteA` is the weaker relation: its role
assignment is any one fitting the entry heap's categories, so an ordinary
array's store may be classed a view store for it, and it states neither
reference validity nor the contracts. The kinded relation gives it at the
entry world's roles, one way (`ViewWriteOf.holds`); the kinded signature
states `Effect.viewPost`, whose assignment is the entry world's roles and
whose exit world is the one safety chose
([call contracts](#call-contracts-over-kinded-worlds)). The coarse change
follows from the active one
(`ViewWriteA.changes`); a location holding a string never comes to hold a
store (`ElementWrite.Holds.not_string_to_store`). The relation from a heap
holds from each of its prefixes (`ViewWriteA.prefix_left`).

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
state and after every action (`rootCells_holds`, `rootCells_box`), and the
dangling store `[[5], null, null]` meets no kinded world at any budget
(`dangling_excluded`).

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
- **Copies** (`mergeParts_cat`): no copied key is `[]` or
  `[[viewElements]]`, and every copied value is a source value: a copy's
  accumulator is no host object, an object owning `[[viewElements]]` is one
  (view metadata validity), and its source copies no internal key.
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
listed; the raw step admits more. The typing rules discharge them, through
the capabilities of §4.

- **Object allocation** (`Step.makeFields`): the rule's role for each key
  fits it (a store slot's under `[]`, a view's under `[[viewElements]]`, F
  or C under any other key); each initializer has its role's category (a
  source value in F or C, a store in S), which the rule's payload premise
  gives (`Payload`, PROGRAM-TYPING's
  [sorts and categories](../PROGRAM-TYPING.md#sorts-and-categories)); the field map has valid view
  metadata, which holds where it names neither metadata key. A source
  allocation names neither key (reserved spellings); a binding allocation
  chooses C, an object literal F.
- **Store literal** (`Step.arrAlloc`): each initializer is a source value
  (`arrLit`'s and `arrParts`' payload premise, `Payload.element`).
- **Field write** (`Step.writeField`): the payload has the category of its
  target's role: a source value in F or C, a store under `[]` (a grown
  store's writeback, a length write).
- **Present element write** (`Step.setPresent`) and **hole or past-end
  write** (`Step.setGrow`): the payload is a source value (`setElem`'s and
  `setElem-bounded`'s payload premise).
- **Natives**: `NativeContract` (§5).
- **Copies** (`Step.mergeV`): the copied fields are allocated as fields;
  every copied key fits that role and every copied value has its category
  (`mergeParts_cat`), so no premise remains beyond the step's own.
- **Every step**: the running term's references are valid (`SafeW`'s
  structural component), and the environment's (`RootsOk`).

The steps that change no heap, the throwing steps and the fresh errors
preserve kinds for every well-formed state.

## 10. Audit of call contracts

Each path by which a call runs code, and each component of a stated effect,
against the native-contract condition (§5). A host contract is a trust
statement the owner reviews.

**Invocation paths** (`CallArguments.Invoke`, `ConstructsTo`, the initial
environment's values, `EnvOk`
([TypingBasics](../../lean/Verification/Programs/TypingBasics.lean))):

- **Graph code**, called or constructed (`Invoke.graph`; its signatures by
  `callsT_of_graph`, `restsT_of_graph`, `restsT_of_graphRest`,
  `ctorsT_of_graph`), result allocation by its own steps included: the
  body's steps are the calculus's, and the condition is typed-step
  preservation along its run (**proved**: `HasTyUsing.sound`,
  `ControlFlow.state_progress`, `GraphCode.goto_safe`).
- **Forwarding descriptors** (`Invoke.bound`): **proved** from the target's
  condition (`NativeContract.bound`).
- **Host values of the initial environment**, natives and imported or
  external arrows alike: **assumed**. The trust statement: every value the
  initial environment binds meets, at kinded worlds, `NativeContract` at its
  declared signature's input and result types, with `post` its effect's
  normal postcondition and `excPost` its exceptional one: every execution
  prefix of its invocation, the callbacks it runs included, is well-formed
  under one extension of the entry world, and every exit meets the
  postconditions at that world.

**Effect components** (`CallEffects.Effect`), each read alone:

- the closed footprint (`closed`, `top` for an undeclared external arrow):
  **fails** alone (`confined_not_respects` for any footprint letting a
  location change arbitrarily); repaired by the host assumption above;
- `receiverStore`, `receiverOwn`, argument store regions (`regions`):
  **fail** alone, each allowing arbitrary contents at the locations it
  names (`confined_not_respects`, the inclusion read from
  `Effect.withinClosed` and `Effect.frame`, unformalized); repaired by the
  host assumption;
- `fresh`, `freshObject`: **fail** alone (`allocation_not_respects`);
  repaired by the host assumption;
- `receiverGrows` (`ReceiverGrows`, `ReceiverAppends`): the element-storage
  phase preserves kinds when its fresh locations are element cells holding
  source values (**proved**, `native_shaped`); the whole call, callbacks
  included, by the host assumption;
- `elementWrite`: the defining contract is the view write (§6); its
  inhabitant from a representative initial host world (`host_viewWrite`)
  and over overlapping views (`viewWrite_overlap`) are **proved**; the
  conjuncts reading kinded worlds are part of the host assumption;
- `onThrow = false`: the exceptional postcondition is unrestricted and
  **fails** alone (`unrestricted_not_respects`); the structural part comes
  from safety, which suffices for a handler (`callback_throw_handled`);
  `onThrow = true` bounds the exceptional heap by the footprint, which fails
  alone as the closed footprint does;
- `requires`, `pre`, `elements`, `ensures`, `promise`: preconditions on the
  entry and promises on values; they change no location.

**Callbacks**: a native running a callback composes the callback's safety
with its own phases at one world (`SafeW.bind`, `SafeW.handle`,
`callback_writeback`); the callback's allocations take the roles its own
typing chose.

## Call contracts over kinded worlds

The active meaning of a function type states its effect's heap
postconditions (`PromiseWith`, `ConstructPromise`), and a typed array's
element write by the weaker relation over a role assignment fitting the entry
heap (`ViewWriteA`, §6). The signatures over kinded worlds (`PromiseK`,
`ConstructK`, `Effect.postK` with the view write at the entry world's roles)
and their composition are proved (§5); their replacing the active meaning is
**planned**.

**Non-vacuity** (**proved**, `families_state`, `families_refs`): at every
budget one heap meets an admissible kinded world with every structural family
of value valid at once: an object's identity, a property and a prototype
property, a binding cell, an ordinary array's store and element, a typed
array's view metadata and view store of its length, a closure's capture and
code field, and a forwarding descriptor's target, receiver and prefix.
