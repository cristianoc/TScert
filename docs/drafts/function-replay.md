# Function-granular replay

## The existing mechanism this extends

Consider three exported functions in one module.

```ts
export function f0(x: number): number { return x + 1; }
export function f1(x: number): number { return f0(x) + 1; }
export function f2(x: number): number { return f1(x) + 1; }
```

The [file worker](../STAGE-STORE.md#worker-stages) publishes one preparation
and one verdict per selected group of mutually dependent units. Without
direct-dependency slicing, each caller's input carries the bodies of every
callee it reaches transitively, so editing the literal in `f0` invalidates
all three keys.

With direct dependencies, `f0` supplies its annotated slot and a named
proposal to `f1`. The declaration of `f0` supplies the signature.
The check of its definition establishes the proposed effect. The body of
`f1` reads this slot and supplies its own result to `f2`. Changing the
literal to 2 changes the proposal key and the check key of `f0`. Its
proposal has the same value, so both callers find their original keys.
Changing the effect of `f0` changes the input of `f1`. Propagation
continues across each edge whose consumed value changes.

For an intermediate cutoff, let `middle` push to a module array before
calling `left`, and let `right` call `middle`. Adding a push to `left`
changes the result consumed by `middle`. Its own published footprint
already includes the push. The edit checks `left` and `middle`, and replays
`right` and initialization.

```text
invokeWorker(W):
  look up the preparation and selected physical verdicts under W
  on a miss, validate the Fragment and prepare its units and dependency graph
  visit the requested groups and unresolved dependencies in callee-first order
  for each group:
    project its members, read slots, initializer and environmental inputs
    hash its relative program and the named results it consumes
    if a finished check exists, use its verdict and proposals
    if only a proposal is needed, compute or replay its result
    if a check is needed, check its plan with its saved or freshly computed proposal
    materialize the line in the current file and publish the physical verdict
singlePass resolves the current verdicts of all dependencies and providers
```

### What this duplicates

The front owns source bindings, edges and groups. The projection reads these
tables. The proposal fold owns stand-ins and the rule for returned callables.
Its exported values cross group boundaries. The existing member checker owns
the verdict. The [stage store](../STAGE-STORE.md#worker-stages) owns key
comparison, process claims and publication. The driver resolves refusals by
one reverse traversal of the current dependency graph. When several paths
to a refusal are shortest, the verdict's dependency order selects the path.

## Group-local lowering

`SliceIndex.layout` keeps the selected bodies, their same-name overloads,
and signatures of the external groups supplying their slots. An external
recursive group retains its ordered membership and leader. For example, a
caller of the second member of a mutually recursive pair reads that
member's signature and depends on the check named by the first member.
`planSliceWithResult` checks the selected membership and direct dependency
identities against the file preparation before running the checker.

A body that reads a module binding carries the initializer. For example,
in `let n = 1; n = 2; const saved = n`, the statement assigning 2 binds
no name, yet it precedes the read that initializes `saved`.
`Front.withInitTypes` walks those statements in execution order. Its
result supplies the binding types and can extend the equation store.
The initializer's external function slots use their published answers.
Group import discovery examines the executable slice and resolves its
free import names against the physical module's declaration document.
The input includes ownership (when the slice carries the initializer),
initialization order where applicable, declaration roots and reachable
definitions, symbol identities, qualified import answers, row tables and
unbound reads or their planning error. Written application obligations are
checked once on the whole file during preparation and omitted from slices.
Local equation lowering rebuilds the store from this input. The declaration
cache matches complete declaration JSON.

For a factory that returns a closure, a stand-in can carry the returned
callable's footprint as well as the call's own normal and exceptional
effects and its return alias. Initialization that calls the factory can
bind the returned closure. The first proposal fold reads the known lower
answers. A reachable initializer-mentioned proposal with a non-top returned
footprint selects a second fold. Each group propagates that condition to
its direct dependents. The fold elaborates local members at its first
prior and uses the published answers for external slots in both rounds.
A call back from such a callee to its caller would put both in the same
strongly connected component. The local fold retains the member bodies
and their first prior in that case.
Typing the selected initializer uses the stand-ins its statements mention.
Recursive settlement and this second fold are internal work of one
proposal operation. A named empty answer suppresses inference for that
slot. The worker-order control exercises a factory, its caller, the
caller's caller and an initializer calling the factory.

## Exact inputs and replay

The program uses source-relative member, dependency and occurrence
identities. A declaration's annotation coordinates belong to its
declaration identity. The worker restores the current physical contract
sites and dependency IDs when rendering a verdict. Fuel, search controls,
interface demand, forced proposals and the counting flag enter the key.
The [wire protocol](../REQUEST-PROTOCOL.md) defines the two operations.

The first compact JSON line describes the program. Each subsequent line
is an ordered named proposal consumed by it. The driver hashes each line
and keys the operation on its name, implementation identity, program
digest and result digests. Consequently the input identity of a callee
can change while the digest read by its caller stays equal.

A check publishes its exported answers with its verdict. A standalone
proposal publishes those answers and its settlement result or planning
error. A subsequent check at that input supplies the saved settlement to
the planner, checks the members and compares the exported proposals.
The operations share a claim and repeat lookup after acquiring it.
The worker caches answers by group for the life of a request stream.
An unchanged physical file can replay all selected lines without starting
a worker. An edited physical file incurs preparation, lookups and output
proportional to the selection even when only one group needs checking.

## Soundness obligation

For the example, replaying the line for `f1` retains its dependency on
`f0`. A refusal at the current `f0` prevents verification of `f1`
and `f2`, even if their local checks replay. `ordinarySlots` interprets
the stand-in at the written declaration. The defining member's
`checkRequestResult` checks its contract, including the bound on its
calls and the contract required of its returns by `resultWithFootprint`.
An imported slot rests on its providers' checks.

`Mode8Accepted.slice` requires successful explicit import planning and
an accepting `passGroupMode8` on those prepared requests.
`PassUnit.sliceVerdict_sound` proves `PassUnitSafe` for that group.
Under the store's integrity assumptions a hit identifies this same
operation at the same input and implementation. SHA-256 integrity,
the worker protocol, projection from the TypeScript fragment and transport
back to source sites have the [existing correspondence obligations](../DESIGN.md#what-verified-means).
The theorem's scope is the prepared group. Equivalence of its bindings
and their meaning to those of the physical file is a source-correspondence
obligation. The shadow modes compare plans, proposals and physical lines
on concrete inputs.

## Cost and diagnostic scope

On the numeric chain, preparation indexes name targets and computes the
strongly connected components with Tarjan's algorithm. Every group has
one body and at most one external slot. The scheduler visits each edge
and group a bounded number of times, and each group has a bounded-size
planning and checking problem. Thus group work is linear in the number
of functions for this family, counting bounded-size names and numbers.
In general the work also depends on the size of bodies, recursive groups,
declaration environments, initializer inputs, and the checker's cost on
each input.

A change inside one function can also change a module input. Add
`const values: number[] = [x]` to the numeric leaf in the three-function
example. Its published proposal stays equal. The parser supplies the
module's first `ArrayProto` declaration. `EquationLowering.lowerSource`
reads its presence when constructing every slice's built-ins and excluded
keys. All three groups execute. Replaying across that change would require
establishing that the changed equation environment gives the same meaning
to the caller's requests.

Opaque refusals carry physical equation-head names. In Pretext's
`prepare.ts` at `a6d353cf`, the refusal of `measureAnalysis` at
`[38096,38112)` quotes a literal array at `[16039,16056)` in a frozen
head. Relative serialization gives that head different coordinates.
`PreparedFile.physicalVerdict` checks the refusing group on the prepared file
front with published stand-ins fixed in both rounds, so no proposal is settled
again and all initialization statements stay intact. It supplies diagnostic
text only when both checks refuse. The stored relative result supplies its
proposals to callers and avoids repeating settlement during relocation. A
result whose acceptance or dependencies cannot be materialized requires a
current physical check. Physical diagnostics therefore fall outside the
one-check and bounded-input cost of an accepting chain.
