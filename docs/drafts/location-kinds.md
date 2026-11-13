# Draft: fixed location kinds

The design of location kinds for the model of the note *Tolerant frames*
(§§2–3): every location of a heap has a kind, fixed for its life, and a fact
supported by locations of one kind survives an effect confined to another
by kinds alone. Claims are labelled **proved** (with the Lean name, in
[Kinds](../../lean/Verification/Semantics/Kinds.lean),
[KindsAllocation](../../lean/Verification/Semantics/KindsAllocation.lean),
[KindsWrites](../../lean/Verification/Semantics/KindsWrites.lean) and
[KindsNatives](../../lean/Verification/Semantics/KindsNatives.lean), each
checked by the [axiom check](../../lean/Verification/Tests/AxiomCheck.lean)
in its block for the kinds of the Tolerant-frames model) or **planned**. The
existing proofs use the world of `Worlds.lean`; [the activation](#activation)
replaces it by the kinded one.

## The existing mechanism this extends

[Changes and footprints](../FOOTPRINTS.md#changes-and-footprints) own
regions, changes, support and respect; the world of
[Worlds](../../lean/Verification/Semantics/Worlds.lean) owns each location's
contract, fixed at allocation and kept by extension, and `HeapOk`
([Heaps](../../lean/Verification/Semantics/Heaps.lean)) relates a heap to
it. A kind is one more fixed part of a world entry, beside the contract, and
kinded satisfaction is one more conjunct of `HeapOk`. The frame mechanism
then reads kinds from the world as it reads contracts.

## 1. Design decisions

1. **The calculus and the lowering are unchanged.** Kinds organise the model
   and the proof rules only: no term form, value form or step is added, and
   no lowering changes. A role is assigned to a location when the world is
   extended at an allocation, by the typing rule that justifies that
   allocation. The calculus step is the same whatever roles the rule
   chooses.
2. **A world entry is a role beside a contract.** The kinded world
   `Kinds.WorldT n` is the stratified construction of `WorldT`, each entry a
   pair of a role and a contract inspecting kinded worlds below `n`.
   Truncation keeps the roles and weakens the contracts; extension appends
   entries; `appendW` takes a role with its contract. Its interface keeps
   every name of the existing one (`Ctr`, `toList` for the contracts,
   `lookup`, `trunc`, `WExt`, `appendW`, `appendWs`, `CtrAdm`, `WorldAdm`,
   `HeapOk`) and adds `entries`, `roles`, `roleAt` and `kindAt`. This form
   was chosen because the activation then replaces the definitions of
   `Worlds.lean` and `Heaps.lean` by these, the type and lemma names
   unchanged, and edits only the places that build an entry (each
   allocation, which now states a role) and those that destructure
   `HeapOk`; a pair of a role list with the existing world would instead
   change the type of every world in every statement. Contracts see roles,
   so a type's contract can require them (step 5 of the plan).
3. **Five kinds and two store forms.**

   ```math
   \mathrm{Role} ::= F \mid C \mid E \mid S_{\mathrm{array}} \mid S_{\mathrm{view}(N)} \mid I
   ```

   F holds an object's ordinary property, C a binding cell's, E an
   element, S a store, I an object's identity (a location holding `null`
   that every object allocation adds; the note's four kinds cannot classify
   it). An ordinary array's store and a typed array's view store of fixed
   length $`N`$ are two forms of S, distinguished by role, since a fixed
   length alone does not distinguish them.
4. **A binding cell is recognised by the role of its property's location.**
   In the calculus a binding cell is the allocation of an object with one
   field `value` and its identity; an object literal `{ value: v }` is the
   same allocation. The rule allocating a binding gives the field's
   location the role C; the rule for an object literal gives F. So the
   object-shape condition is: each ordinary property maps to a location of
   role F or C. A region `o.*` denotes whatever roles those locations have,
   and the sets of all cells and of all fields are disjoint, as the note
   requires (**proved**, `kinds_disjoint`).
5. **Reference validity.** $`\mathrm{RefsOk}(W,t)`$ holds when every location
   a term refers to has the role its position demands: an object's identity
   is in I; its slot under `[]` is in $`S_{\mathrm{array}}`$; under
   `[[viewElements]]` it is in $`S_{\mathrm{view}(N)}`$ for some $`N`$, and
   the object's `[[viewLength]]` field is in F with a contract admitting
   $`N`$ alone; under every other key it is in F or C; every cell a store
   lists is in E. It covers every subterm, the captures, bound targets,
   receivers and prefixes of call descriptors, and a graph's node
   expressions, and it reads the world only.
6. **Shapes and kinded satisfaction.** The structural part is unindexed, so
   it holds at every budget, zero included:

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

## 2. What is proved

- **Kinds are fixed.** Kinds are disjoint (`kinds_disjoint`), kept by
  extension (`WExt_kindAt`) and by truncation to any level (`kindAt_trunc`);
  `Shape` is monotone in extension (`Shape_mono`) and survives truncation
  (`Shape_trunc`, `HeapOk_trunc`).
- **Kinds partition a well-formed heap** (`HeapOk.kinds`): each location has
  exactly one kind; a location is in S exactly when it holds a store; every
  store lists only element cells, all locations of the heap.
- **The audit's counter-heap is excluded** (`counterheap_excluded`): no
  world satisfies `[[1], 0, null]` with the array `{[]: 0}` and the object
  `{f: 1}` both valid, since location 1 would be in F or C and in E. **The
  dangling store of `rootCells_not_invariant` is excluded**
  (`dangling_excluded`): no kinded world is satisfied by
  `[[5], null, null]`.
- **Allocation** (`HeapOk_appendWs` for both parts;
  `makeFields_shaped` for any object, with `objectLiteral_shaped`,
  `bindingCell_shaped`, `closure_shaped`, `arrayObject_shaped`,
  `typedArray_shaped`; `arrAlloc_shaped` for a store literal's elements;
  `thrownError_shaped` for a fresh error).
- **Writes** (`write_sound` for both parts; `writeField_shaped`,
  `writeOrdinary_shaped`, `bindingWrite_shaped`, `storeWrite_shaped`,
  `lengthStore_refs`; `setPresent_shaped`, `setGrow_shaped`).
- **Steps that change no heap keep references valid** (`step_refs`):
  congruences, substitution, a graph's entry, a node's instantiation, every
  continuation's environment map, handlers and raises, reads, spreads,
  copies, tests and arithmetic.
- **Copies** (`mergeParts_cat`): no copied key is `[]`, and every copied
  value under a key other than `[[viewElements]]` is a source value.
- **Array natives** (`Arr.natives_within`, `Arr.Within.refs`,
  `native_shaped`): `Set`, `Delete`, a length change, `push`, `pop`,
  `shift`, `unshift`, `reverse` and `sort`'s writeback keep a store's cells
  among the original and fresh ones, and the native preserves kinds when
  its fresh locations are element cells holding source values and the old
  locations it changes are element cells holding source values.
- **Host contracts** stated as heap relations have the obligation
  `RespectsKinds` (and `ResultRespectsKinds` with a result). The
  typed-array element write's contract as stated does not meet it
  (`elementWrite_not_respects`): it lets a field holding a string come to
  hold a store.

## 3. The typing premises

Each step below preserves kinded satisfaction only under the premise
listed; the raw step admits more. These are what the activation discharges
from the typing rules.

- **Object allocation** (`Step.makeFields`): the rule's role for each key
  fits it (a store slot's under `[]`, a view's under `[[viewElements]]`, F
  or C under any other key); each initializer has its role's category (a
  source value in F or C, a store in S); and the field map meets the
  view-length condition, which holds where no key is `[[viewElements]]`. A
  source allocation names no `[[viewElements]]` key (a reserved spelling);
  a binding allocation chooses C, an object literal F.
- **Store literal** (`Step.arrAlloc`): each initializer is a source value.
- **Field write** (`Step.writeField`): the payload has the category of its
  target's role: a source value in F or C (an ordinary key, a binding
  update), a store under `[]` (a grown store's writeback, a length write).
- **Present element write** (`Step.setPresent`) and **hole or past-end
  write** (`Step.setGrow`): the payload is a source value.
- **Array natives**: the audited heap side of each native's row
  (`array_native_post`), with the contents it writes and allocates source
  values.
- **Copies** (`Step.mergeV`): an ordinary accumulator owns no
  `[[viewElements]]` slot, or the copy's allocating rule gives that key a
  view role with its length field's singleton contract.
- **Every step**: the term's references are valid in the world
  (`RefsOk`), which the activation adds to the state's well-formedness
  together with the environment's values.

No other step needs a premise: the steps that change no heap, the throwing
steps and the fresh errors preserve kinds for every well-formed state.

## 4. Contracts that need a kinds audit

The obligation is `RespectsKinds`, or `ResultRespectsKinds` for a contract
with a result.

- The typed-array element writes `%ByteSet%`, `fill`, `copyWithin` and
  `set` ([`ElementWrite.changes`](../../lean/Verification/Semantics/CallEffects.lean)):
  the change must keep each changed location's shape, and a view store's
  new entries must be element cells.
- Host constructors, typed arrays' among them: the allocation must be that
  of `typedArray_shaped` (a view store of the array's length, its length
  field's contract admitting that length alone).
- Result-producing natives and calls with `fresh`, `freshObject`,
  `receiverGrows` or argument store regions in their effect
  ([call effects](../../lean/Verification/Semantics/CallEffects.lean)),
  `splice` and `map`'s results among them.
- The builtin initial worlds: prototypes and builtin objects need I
  identities, F properties and the store slots that apply.

## 5. Gaps found

- **An object value alone does not say whether a property location is F or
  C.** A field write's target is in F only when the object is no binding
  cell, which `RefsOk` cannot tell. So "a field write's effect is confined
  to F" is not a consequence of a well-formed state alone: the frame rule
  for a field write must obtain the target's role from the object's type.
  This needs a record type's contract to require the role F of each of its
  property locations, and a binding cell's type the role C (plan step 5).
- **The typed-array element write's contract** as stated does not respect
  kinds (`elementWrite_not_respects`); its audit is a prerequisite of
  framing a typed-array write by kinds.

## Activation

The plan for the commit that activates kinded worlds. It follows the
addition of the function's entry state to fact satisfaction, which changes
the same statements.

1. Replace `WorldT`, `Ctr`, `toList`, `lookup`, `trunc`, `WExt`, `appendW`,
   `appendWs`, `CtrAdm`, `WorldAdm` and `HeapOk` of
   [Worlds](../../lean/Verification/Semantics/Worlds.lean) and
   [Heaps](../../lean/Verification/Semantics/Heaps.lean) by the kinded ones;
   `write_sound`, `heap_alloc` and `heap_allocs` by `write_sound` and
   `HeapOk_appendWs`.
2. Give each allocation its roles: `AllocationWorlds.next` (its fields by
   key, its identity I), the binding and module-binding allocations (C),
   store literals (E), arrays' store slots ($`S_{\mathrm{array}}`$), the
   fresh errors (I); discharge each premise of §3 from its typing rule.
3. Add $`\mathrm{RefsOk}(W,t)`$ for the active term and the environment's
   values to `EnvOk` and the safety predicates' state well-formedness, and
   prove it preserved along every step by induction on the step:
   `step_refs` for the steps that change no heap, the lemmas of §2 for the
   rest, `RefsOk_mono` for the unchanged context.
4. Establish kinded satisfaction of the initial worlds: the builtin
   objects' and the host families'.
5. Require roles in the contracts that look up locations: `listT`'s cells
   in E, `recT`'s properties in F, a binding cell's in C; `StoreCells`,
   `CellsCtr` and `RootCells` then follow from `HeapOk.kinds`, and
   `ElemsValueOk` and the `elemsValue` evidence become consequences.
6. Audit the contracts of §4 against `RespectsKinds`.
