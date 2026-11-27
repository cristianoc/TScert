# Function-granular replay

## The existing mechanism this extends

The [stage store](../STAGE-STORE.md#worker-stages) publishes a preparation and
one verdict per selected group of mutually dependent units. Let W be the
worker identity, including the executable, controls, Fragment and interfaces.
The runner and worker compute the following.

```text
invokeWorker(W):
  lookup (W, null), then (W, unitId) for each selected group
  on a miss: prepareUnitsFile validates the file and lowers its front
  for each missing group i:
    known(i) obtains groupProposals below i, callees first
    plan i with those answers and the selection's interface demand
    passGroupMode8 checks the members and gives dependencies or a refusal
singlePass follows current verdicts and providers to decide verification
```

Consider this file with four groups, including initialization.

```ts
const limit = 1;
function touch(xs: number[]) { xs.length; }
function use(xs: number[]) { touch(xs); return limit; }
function square(n: number) { return n * n; }
```

Changing the multiplication to addition changes W. The current lookup misses
for all four groups. Under the proposed rule the worker prepares the edited
file, obtains the proposal for `touch`, and constructs the input for each
requested group. With equal binding, store and proposal inputs, `init`,
`touch` and `use` replay. Only `square` has a changed program. If instead
`touch` changes, its new proposal value flows into the input of `use`.
An equal value can preserve that hit even when the current verdict of
`touch` refuses. The dependency traversal then refuses verification of
`use`.

### What this duplicates

Lean's front supplies SCC membership, ownership, bindings and import reads.
Member elaboration and the frozen equation store determine the group program
and its types. The proposal fold supplies effects, throw bounds, aliases and
returned footprints. The group check supplies local verdicts. The store
compares inputs and publishes results. The runner resolves current providers
and dependencies. Recording observed reads would also require a query
language, candidate validation and a proof that each validated trace
reproduces execution.

## Exact inputs and replay

For an edited file, establish imported interfaces and run current fragment,
declaration and symbol validation before requesting a group. In dependency
order compute the canonical input G from the selected members and overloads,
their ordered programs, claims and defaults, nested code, effective demand
and force, binding types or errors, ownership answers, qualified imports,
row agreement, unbound reads, equation inputs and search settings. Include
ordered named proposal answers for the groups below. A present empty answer
suppresses inference. An absent name permits it. Recursive rounds and the
initialization-dependent returned-callable round belong to planning.

The current planner's returned-callable round deserves a separate test.
When initialization mentions a factory with a proposed result footprint,
the second fold in `plansOnFront` starts with the first round's proposals
as its prior and an empty list of known answers. In the example, replacing
`touch` with a factory called by both initialization and `use` can make the
planner walk the factory again while planning `use`. A first-round answer
alone does not determine that second computation. The closed input must
include its exact inputs or its answer at that prior, with current-file
correspondence established for both rounds.

Lookup uses the implementation, operation and canonical bytes of G. On a
miss execute check(G), returning its named proposals, member references,
local verdict, dependencies, contracts and diagnostic sites. An unselected
dependency can supply the proposal alone. A hit supplies the same proposal
values to callers. Materialize every reference at its current occurrence and
run current dependency closure in selection order. Keep identical-W replay,
atomic finished entries and attempt-specific timeout observations. Charge
projection and proposal-only execution to the requested part. A chain of n
groups can contribute n(n−1)/2 lower-group answers in total. Measure bytes
and CPU spent constructing those inputs alongside the checks saved.

Use full stable symbol identities, including fresh and private declaration
sites, until a checked correspondence preserves sharing and comparisons.
Sites in other declarations require their own occurrence map. Preserve
ordered search, freeze failures, builtins, prototypes, images and lookup
absence. The search limit is 120. Inserting an unrelated declaration can
supply a previously absent meet key in the intern index. Keeping the entire
index is conservative. The riskiest assumption is that a sufficiently small
projection of this index and of initialization bindings costs less than the
walk it saves. Compare an unrelated insertion with one that supplies a
missing meet and record the first differing field and projection CPU.

## Soundness obligation

Equal complete inputs to a deterministic closed operation give equal results.
To authorize fine replay, prove in Lean that materializing the operation's
result on *this* prepared file gives its current planner result and selected
group check, for successful and failed plans and their proposal values.
On acceptance this gives the successful `fragmentPlansFromInterfaces` result, current selection and
`passGroupMode8 = .ok deps` premises of `Mode8Accepted.main`.
`mode8Accepted_sound` then gives `PassUnitSafe` for the current group.
Module establishment retains its own constructor. The theorem and scope are
described in [what verified means](../DESIGN.md#what-verified-means).
Replay requires a finished result published by this operation and implementation
at the exact input. Payload integrity, SHA-256 collision resistance, executable
identity and the runner's association of a response with its request belong
to the stage store's trust boundary. Projection, serialization and site transport
require checking before cross-file-version replay can use this argument.

## Commit sequence and gates

1. Give the generated Pretext project a stable directory keyed by its exact
   config. Compare identical verdicts and stage counts on two unchanged runs.
   On 2026-11-27 the unchanged analysis.ts rerun took 1.3 s with zero stages
   executed, against 3.6 s with six executed.
2. Factor group planning, proposal production and checking under W. Use
   explicit demand and ordered lower answers, fresh or exactly memoized
   inference, retained plans and shared initialization typing at equal inputs.
   Compare complete proposals and verdict lines in fresh, reversed and resumed
   workers, with failed planning, present empty answers, returned callables
   and forced inference. Count cold initialization and proposal walks.
   `GroupContext.groupOperation` supplies the verdict and its proposals from
   one plan. A worker retains the qualified front and its initialization
   typings, including typings over changed stand-ins. Each retained changed
   typing carries a Lean equality to the fresh computation. Both proposal rounds of every group request share settlement
   at the same qualified front, member index and complete ordered stand-ins.
   The final group plan carries its provider identities into the verdict.
3. Compute G and relative results in shadow mode. Prove current-file
   correspondence and compare forced executions across a moved refusal,
   an ownership escape in an uncalled body, fresh/private symbols, a changed
   meet lookup and an SCC split. Compare a body edit, a leading comment,
   an independent insertion, a changed callee effect and a changed captured
   binding. Diff the four Pretext transitions by input field, preserving
   annotations in the comment-only comparison. Count projection work separately.
4. Enable fine lookup and atomic publication. Compare mixed hits, restart and
   concurrent publication with forced execution on the edited snapshot.
   Require zero group checks and proposal walks on the ordinary-comment
   fixture and one group check on the independent-body edit. Report
   preparation, proposal, verdict and projection costs separately.

## Cold worker measurement

On 2026-11-27 the standalone worker-order Fragment had five groups. Its
factory returns a closure, initialization and `use` call the factory,
`outer` calls `use`, and `leaf` has no caller. Each column compares one
fresh worker at `1b92d984e` with one using the factored operation, requesting
all five groups. The complete verdict lines agree in each pair.

| Work table count | Ordinary | Forced results |
| --- | ---: | ---: |
| Initialization typings | 13 → 6 | 14 → 7 |
| Proposal member plans | 9 → 4 | 11 → 7 |
| Main graph walks during proposal settling | 4 → 4 | 5 → 7 |
| Nested code graph walks during proposal settling | 2 → 2 | 2 → 3 |
| Group checks | 5 → 5 | 5 → 5 |

The invocation uses `TSCERT_PROFILE=1`, 4096 subtype rounds, depth 12,
full selection and the worker request `{"units":null}`. The forced column
adds `--force-proposals results`. Graph walk counts are the work table's
`run:` records under proposal settling. In the forced returned-callable round for `outer`, its first proposal
enters the stand-ins for `factory` and `use`. Earlier requests for those
members supplied the ordinary effect for `outer`. At these different
inputs the exact table executes the main and nested graphs of `factory`
and the main graph of `use`. The old digest reused their answers.

This takes up C4's immutable group inputs, C10's sharing of planning and
initialization, and C11's per-group keys and separation of proposal content
from current establishment. The broader callable-interface and preparation
work has its own [commit sequence](on-demand-processing.md#commit-order).
