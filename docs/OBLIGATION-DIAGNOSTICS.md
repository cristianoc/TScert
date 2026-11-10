# Obligation diagnostics

This is explanatory metadata about an unsuccessful verification attempt, not
proof evidence and not a judgement that a source claim is false. It plays no
part in certificate checking.

## Transport and identity

On a structured failure, the verifier emits its human-readable error,
then one line on stderr:

```text
obligation-diagnostic: {"phase":"proof-search","outcome":{"kind":"not-established"},...}
```

The human sentence of a failed graph search names the obligation: `source
expression obligation at [s,e): evidence search failed: no derivation of its
<role> claim` for a node, `source incoming edge obligation at [s,e): … the
edge from node N does not establish the claims at this point` for an edge.
`verify-source.mts` then adds one line, `obligation: <summary>`, the
source-term account of the record below (which claim was available and what
was required, or, for a term that is not a slot, its form and the claims of
the slots it reads), so a refusal read in a log or a coverage row says why
without opening the record.

### A failed search refused by name

Where the cause of a failed search is known, `verify-source.mts` puts it first, as a
line `reject: <reason>` before the verifier's own, which follow unchanged.
The outcome stays the unverified search Lean decided on the ordinary
proposal; the line only names why it found no derivation. Two sources give
it, in this order:

- The producer's explanation: `producer --explain` runs the ordinary
  inference of the unit holding the failed obligation and prints, instead
  of claims, the forms it met whose failure has a stated reason, each at
  its source span
  (`Proposal_diagnostics.explain`). The innermost one whose span meets the
  failed obligation's names it. The forms and their reasons:
  - a `for...of` loop or a spread over an iterable an arm of which is no
    array: a host kind's iteration is stated (`%Iterate:K%`), and a loop over
    a union of host kinds steps their union's iteration; a spread over such a
    union, or a loop over a value of no host kind, has no intrinsic; an
    iterable the program defines, or a union with one, runs the iterator
    protocol;
  - an open record or `unknown` that `Array.isArray` or `instanceof Array`
    found an array, used as one: the object owns an array's store, which is
    no proof that it is an array of `Array.prototype`;
  - an array used as a record naming `length`, and a mutable tuple's
    `length` at its arity;
  - where a signature binding more parameters is expected: a function value
    known only by its type, whose type states no rest, a module function
    with a rest parameter, or a generic one;
  - a named function where a signature indifferent to the receiver it
    requires is expected: its type is its annotated signature;
  - an instance of a declaration with generic methods at an instance of
    another declaring them otherwise: quantified signatures are related
    binding the same rows;
  - a record at an index signature (TypeScript's implicit index signature);
  - a mutable array or a writable field at a wider one (invariance);
  - a `typeof` test, `??` or strict equality on a value of a type parameter
    or `unknown`;
  - a cell read at its contract: contents are stated only for primitives,
    and forgotten across a step that may write them;
  - a write adding a dictionary's key, a spread of a dictionary, and a read
    of a key `in` found in a dictionary;
  - an optional key found `undefined`, read at `undefined`;
  - a non-null assertion on a read at a `for...in` key.
- With `verify-source.mts --typescript-errors` (it loads the project
  again), for code TypeScript refuses, the TypeScript error nearest the
  failed obligation: `reject: TypeScript refuses this code too (line L, col
  C: <message>); the pipeline follows TypeScript's types`. A refusal of the
  parser's gate or of the producer, which names no obligation, is named the
  same way by the file's first TypeScript error.

Neither is a premise of anything: the explanation run's claims are
discarded, and a failure no source names keeps the verifier's lines alone.

`tools/diagnostic.mts` reads the record without parsing the
human sentence. A record it cannot decode field by field, and a duplicate
record, are not interpreted: the reader requires the fields below and refuses
what it does not recognize, so a record it accepts is one of exactly this
shape. Every `not-established` result has a `location`. A generic value's
instance outside its bound carries the `direct-obligation` record described below;
source-conversion refusals use their typed source location. A verifier failure
that supplies neither is an internal protocol error.
Absence of a structured record never changes a failure into success.

IDs (`node:L`, `edge:L:I`, `expression:I`) are local to one function and
attempt. A saved diagnostic is untrusted display data; it cannot establish
verification status.

### Where a proposal drops facts

`producer --explain` also prints, for the unit it runs, each place where
the proposal states fewer facts than before it, and each place that makes
the unit's inferred footprint `store: any`. Every explanation has a `kind`:

- `form`: a form whose failure has a stated reason, as above.
- `facts`: a statement or expression past which the proposal states none
  of the listed facts, and what dropped them: the change the statement was
  given (which classes of locations it may alter, and whether stores are
  kept, grown or changed), or the innermost expression for which the fact
  analysis computes no change, a call with its callee's footprint. In this
  run the dropped facts are carried on, so every later place that drops
  them is listed too.
- `footprint`: an expression for which no footprint is inferred, or a call
  whose callee's footprint has `store: any`.

A unit's check asked for them (`UnitSelection.losses`) attaches the `facts`
and `footprint` explanations to the unit's result, and
`dev/check-functions.mts` prints them under each refused unit, or under
every selected unit with `--explain`. They describe the proposal: Lean
decides each proposed fact, and a place listed here is where a fact a later
obligation needs stops being proposed.

### Candidates left out

A fact the producer supplies at a statement entry is a candidate, which the
evidence search keeps where every edge into the entry establishes it
([source observation checkpoints](PROGRAM-TYPING.md#source-observation-checkpoints)).
A refused graph's record lists in `candidatesLeftOut` every candidate the
search left out of it: `{ "label", "sourceMap", "edgeFrom", "edgeSourceMap",
"fact" }`, the entry's node and source map, the node whose edge into the entry
does not establish the fact and its source map (the entry's own, at the
graph's entry, whose assumed knowledge does not), and the fact, an index atom
over the entry's slots. `dev/check-functions.mts` prints each under the
refused unit, with the edge. They are stated by the search about Lean's
rules, where the explanations above describe the producer's proposal.

## Common fields

| Field | Meaning |
|---|---|
| `kind` | `node-typing`, `edge-coverage`, `expression-claim`, `direct-obligation`, `source-refusal`, or `production-failure`. |
| `phase` | `proof-search`, `certificate-check`, or `request-validation`. |
| `outcome` | `{ "kind": "not-established" }` or `{ "kind": "exhausted", "resource": { "kind": "subtype-frontier", "limit": N, "rounds": N, "visited": N } }`. |
| `fuel` | Search depth used for this attempt, not a semantic bound or a diagnosis of exhaustion. |
| `types` | Finite table of rows, the store's projection onto the labels the record mentions (below); type lists in the record index this table. |
| `names` | `[[row, spelling], …]`: a source-like spelling of each row that stands for an application, such as `Promise<number \| R>`, in row order, each row once. Absent when no row is named. |
| `requiredResult` | Whole-function result type on graph diagnostics; absent on standalone expression obligations. |
| `candidatesLeftOut` | On a graph search's diagnostics, each fact the producer supplied at a statement entry that the search left out ([below](#candidates-left-out)); absent on records no graph search makes. |
| `id` | Local obligation identity, where available. |

An exhausted subtype comparison is inconclusive. Generic module-call bound
checks report this outcome in `request-validation`, at the call's span.
Annotation application bounds use that phase and `binding-annotation`, with
the two compared types under the compacted equations. A source-written
application uses its span; a bound originating in an imported declaration is
located at the requesting unit. `limit` is the requested
frontier-round budget, `rounds` is the number of rounds consumed, and `visited`
is the number of comparison dependencies visited. The runner reports
`exhausted`, and the presentation's `searchOutcome` states these counts.
Source signature comparisons use this same record with `entry-claim`,
`return-contract` or `binding-annotation`. Equality requires two sequential
inclusions; a failure carries the direction being checked. Explicit instance
arguments use `scheme-elimination`. Both source spans in the record are derived
from the located comparison by `SourceExtraction.subtypeFailure`.

Coverage measurements count exhausted attempts separately. Proposal search
retains this outcome through failed alternatives; an established alternative
supplies the requested derivation.

### The label projection

A record does not embed the label store; it embeds what the store's projection
shows of the labels the record mentions (`StoreView.project`, `Projection` in
[Source/LabelStore.lean](../lean/Verification/Source/LabelStore.lean), the label and store interfaces of the source path).
A projection is a finite table of rows over its own
positions, the position each mentioned label is shown at, and the `names`
entries. The record's type lists are those positions, so a reader renders
every record the same way, whatever store built it:

```math
\mathrm{project}(S, M, d) = (\mathit{rows}, \mathit{position} : M \to \mathbb{N}, \mathit{names})
```

for a store $`S`$, the labels $`M`$ the record mentions and the depth bound
$`d`$ (`Projection.depth`, 3). The rows hold $`M`$ and what their rows name, to
$`d`$ row references below $`M`$. An application past the bound is an opaque
named reference: a `names` entry whose row has no clauses. A reader shows a
named row by its name and never expands it.

- **The finite table.** Its labels are row positions already, so the
  projection is the identity: every row, in order, positions unchanged, and no
  `names`. A sub-table would renumber rows.
- **Equation labels** ([RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md),
  [equations and tree labels](REQUEST-PROTOCOL.md#equations-and-tree-labels)).
  A label is a tree over infinitely many applications, so the projection
  chooses positions for $`M`$ and for the rows below them up to $`d`$, and
  names each application.

A `source-refusal` mentions no label. A closure `expression-claim` record's
table shows each row's clauses alone: a parameter, scheme or meet row as no
clauses.

The exact calculus term and type graph use the encodings in
[REQUEST-PROTOCOL](REQUEST-PROTOCOL.md). Sequents have `context`, `term`, and `type`.
Context entries are de Bruijn slots, most recent first, and may include anonymous
saved results. They are not necessarily a source statement environment.

## Direct obligations

A call of a generic module value names its instance before any graph request
exists, and each type argument must lie within its binder's bound. A failure is
a `direct-obligation` record, with mandatory `sourceMap` and a closed,
structured `judgment`. There is no prose field. The judgment is
`{"kind": "subtyping", "subject": span, "actual": labels, "expected": labels}`:
the source span and the two compared types under the record's type equations.
Generic call bounds use the role `scheme-elimination`; exhausted expression
or edge comparisons use the source obligation's role. They must not be disguised as graph sequents. Lean
diagnostics render ground types only through `SourceTypes.render`; numeric
labels remain references inside the graph document and never become type names
in user-facing judgments.

[DirectObligation.lean](../lean/Verification/Programs/DirectObligation.lean) represents this closed judgment form, with no prose field.

The decoder checks the record rather than trusting it: the labels lie in the
record's graph, and the source map has exactly the judgment's span and no
context. An unknown judgment variant is rejected. Displayed text, including the
turnstile, is derived by one printer from the structured sides; no producer or
call site can store arbitrary prose as a judgment. Unsupported source remains a
separate `source-refusal`, with a mandatory source map and reason, and cannot be
rendered as a failed semantic obligation or with a turnstile.

## Node and expression obligations

A `node-typing` record has:

- `source`: `{label, sourceMap, node, claim}`. `node` includes the expression and
  continuation; `claim` includes its entry context and required expression type.
- `sequent`: the exact judgement attempted at that node.

An `expression-claim` record has `sourceMap` and `sequent` directly. The kind
identifies the obligation collection, not a claim of semantic blame.

`sourceMap` is this node's entry in the graph's **source map**: how to describe
the node, and each of its context bindings, in the words of the source it was
lowered from. It is nullable. When present, it contains:

- `pos`: source span, in the parser's UTF-16 offsets.
- `role`: assigned where extraction creates the obligation.
- `environmentStart`: optional source statement-entry offset, only where known.
- `context`: one descriptor per context binding, in context order.

A descriptor has `name`, the source binding this one is addressable by, and
`span`, the source expression whose value it holds; at least one is present.
Lowering is the only pass that knows both the source and the graph, so it is the
only pass that can record this, and it fails rather than emit a context it
cannot describe. **A reader therefore never has to show a position.** Render a
`name` as itself and a `span` as the source text it covers.

Source maps are explanatory in the strict sense: the structure has no decoder,
never reaches a request or a certificate, and cannot affect acceptance. A wrong
descriptor mislabels a message and nothing else. The rule that keeps this clean:
anything travelling back toward a reader carries source descriptors, anything
staying inside the calculus carries positions. `sequent.context`,
`transfer.available` and `target.mapping` are the calculus's own words and stay
positional; a reader joins them to the descriptors by index.

A role names the source purpose of an obligation, as the pass that creates
it assigns it. Direct obligations and source refusals take theirs from one
closed list, `SourceRole` in
[DirectObligation.lean](../lean/Verification/Programs/DirectObligation.lean):
`entry-claim`, `expression-claim`, `return-contract`, `binding-annotation`,
`generic-validation`, `scheme-introduction`, `scheme-elimination`,
`storage-write`, `call-argument` and `initialization-order`. A graph node's
role is a string lowering writes where it creates the node:
`expression-claim`, `node-typing` (no more specific purpose),
`return-contract`, `binding-annotation`, `tag-dispatch`, `closure-entry`,
`heap-observation`, and the roles of the lowered source forms
(`storage-contract`, `method-receiver`, `pattern-rest`, `for-of-step`, …).
A reader explains the roles it knows and shows any other as a generic
obligation, never a guessed explanation.

At a top-level return, expression typing and result-contract checking are
separate nodes that can have the same span. For example, a saved `boolean` result
cannot establish a declared `true` result even when the source expression's claim
is itself valid. The `return-contract` sequent shows the saved result in slot 0
and the required function result as its conclusion. `environmentStart` links to
the original return entry; it does not mean its environment equals the entire
node context (which includes the saved result).

## Edge obligations

An `edge-coverage` record includes `source` and `destination` node records,
`edgeIndex` (0 for the first edge, 1 for the second), and `transfer`:

- `available`: the context before applying the destination map, including any
  result pushed by bind or Boolean dispatch.
- `target`: exact destination label and slot mapping.
- `booleanObservation`: true/false for a result-binding Boolean branch; otherwise
  null. The observed slot is 0. This is the premise of that edge, **not** a claim
  that execution has actually taken the edge.

- `tagObservation`: `{test, answer, slot: 0}` for tag dispatch; otherwise null.
  Like Boolean observations, this describes the selected edge's premise, not an
  assertion that runtime took it. It uses the tag encoding of the request protocol.

The destination requirement is `destination.claim.context`. Both branch edges
can have the same destination label and different maps; `edgeIndex` identifies
which obligation failed. Refinement must be interpreted together with the
observation, not as ordinary subtyping of `available` alone.

Current-content assertions in the supported cell profile reach checked
obligations. Graph failures use `edge-coverage`, with destination `sourceMap` role
`heap-observation`; `requiredKnowledge` at the destination identifies the actual
cell facts. Ordinary closure/compositional proofs use `expression-claim` with the
same role for uniform invariant justification. These are proof failures,
not exporter refusals. [Program typing](PROGRAM-TYPING.md#source-observation-checkpoints)
owns their interpretation.

## Scope of a record

No recursive proof-search trace, minimal failing premise, or complete dependency
graph is promised. Extraction, type-decoding and missing-claim failures use typed
source locations. An independent certificate rejection is an internal error,
because the producer just emitted evidence that its consumer rejects. A source map entry
does not identify every contributing source claim or prove any premise separately.
There are no retained mutable-heap observations. A form with obligations of its
own, as generics and overloads have, gets its own obligation roles rather than
an `in / claim / out` triple or a role inferred by a reader.

## Tool failures

A **tool failure** is the entry point's `error` outcome
([the pipeline entry point](DESIGN.md#the-pipeline-entry-point)), and
certifies nothing. It is any of:

- a subprocess killed by a signal, past its time limit, or exiting without
  its complete refusal record. A refusal record is the verifier's exit
  status 1 or the producer's 2, with a first line `reject: …` or
  `unsupported: …` and a last line `end of refusal`; each tool exits 3 with
  a first line `error: …` on an operational failure, a file it cannot read
  or write among them;
- the producer's `--explain` failing or printing no explanations;
- a failure of a file-system operation of the front end, each made in one
  module (`tools/files.mts`), other than a path naming nothing where that
  absence has a meaning;
- a failed request to the compiler's API, which names the query, the front
  end's call site and the compiler's reason.

Every request to the compiler goes through one guard
(`tools/compiler-channel.mts`), which makes whatever it throws a
`CompilerFailure`: a reply the compiler sent as an error, a transport or
native I/O failure, before or after the request was written, or the front
end exhausting the call stack, which may interrupt a query mid-reply. Every
front-end catch passes a tool failure on, so it never becomes a refusal, an
absence or an unknown answer; one caught within a located read keeps that
location. After a panic the compiler replied, its channel stays readable;
after any other tool failure the compiler is abandoned without a further
request, its process killed, and the next parse opens another. A failure
closing the compiler is a tool failure that names what was in flight. The
compiler API's panics include [the empty-tuple
panic](COMPILER-API.md#the-package-at-run-time).

## Presentation

`presentObligation` (`tools/diagnostic-view.mts`) turns a decoded record into
two strings: `summary`, a source-named sentence where the record supports
one, and `searchOutcome`, whether the search was not established or
exhausted, with the depth or the budget. A summary names the obligation
from the record's structured fields, never from the human sentence:

- a node or expression obligation on a slot: the slot's available claim and
  the required type, the slot named through the source map, for example
  `cell.value` available at `boolean` where a `return-contract` requires
  `true`;
- a node or expression obligation on a compound term: its form and the
  claims of the slots it reads directly;
- an edge: the first destination slot whose mapped incoming claim differs
  from the requirement, or the required heap facts;
- a direct obligation: the two compared types;
- a source refusal: its reason; a production failure: none.

Types are printed in the claim language ([CLAIM-LANGUAGE](CLAIM-LANGUAGE.md)),
lifted from the record's table to depth 3, a row the record's `names` lists
shown by its name. The presentation describes the failed requirement, not a
counterexample: search failure means not established, not refuted.
