# Verification regressions

`make test` builds, then runs the fast checks and the controls
([`test-all.sh`](../test-all.sh), [`pipeline/test.mts`](../pipeline/test.mts));
`make suite` builds, then runs the pipeline cases
([`pipeline/run-cases.mts`](../pipeline/run-cases.mts)).

The pipeline cases are listed in [`pipeline/cases.mts`](../pipeline/cases.mts),
each a source file under [`pipeline/examples/`](../pipeline/examples/) with its
expected outcome, run by `pipeline/run-cases.mts` (`make suite`, and
`make cases P=…` for those whose names contain `P`); the controls no case can
make are `pipeline/test.mts`'s. Two families in
`pipeline/examples/` hold one source per feature, every function checked:

- `stateful-source/`: storage contracts, refinements, loops, generics and the
  operations of the fragment, one phenomenon per file.
- [`callables/`](../pipeline/examples/callables/README.md): call signatures,
  callable objects, arity, receivers and argument lists.

Cases naming a project read their imports from it:
`pipeline/imports-project/` supplies value imports, and
`pipeline/library-project/` is a typed library of reactive collections
(`collections.ts`) with Node's pinned types, read by the `collections-*` cases;
`pipeline/compiler-api-project/` resolves the compiler API, the package
`typescript` the front end pins, for the `*compiler-api*` cases;
`pipeline/augmented-project/` augments `ObjectConstructor` from a module of
its own, and `pipeline/fake-lib-project/` reads `pipeline/fake-lib/`, a file
named like a standard library file, for the `*augmented*` and `*fake-lib*`
cases; `pipeline/lib-collision-project/` holds one at
`typescript/lib/lib.augment.d.ts`, the path a standard library identity is
printed with, for the `*lib-collision*` case;
the `pipeline/merged-*-project/` directories each merge a member into one
standard library interface (`Array`, `ReadonlyArray`, `Object`, `Function`,
`Iterator`, `ArrayIterator`, `String`, `Iterable`, and `ReadonlyArray`'s
`at` restated, renamed, narrowed and reached along two bases), for the cases
whose file names contain the directory's `merged-*` part;
`pipeline/parse-int-overload-project/` adds an overload to the standard
library's `parseInt`, for the `*parse-int-overload*` case;
`pipeline/host-global-project/` declares globals in a declaration file of
its own, for the `*host-global*` cases; `pipeline/fake-process-project/`
declares a `process` spelled as Node's, for the `*fake-process*` case;
`pipeline/host-fixture-project/` reads `pipeline/host-fixture/`, a package
whose manifest names the host package and whose `Node` reaches no node list:
as a case it is no host (`host-fixture-lookalike`), and `pipeline/test.mts`
activates it under the compiler API's description naming its installation
(`pipeline/host-fixture-project/node_modules/typescript`, a fixture link) and
digest for the `*host-fixture*` controls of reading rule 1.
Lean tests build alongside the implementation in `lean/Verification/Tests/`.

This directory holds the suites that check the repository around the pipeline:

| Tests | Coverage |
| --- | --- |
| [`docs.mts`](docs.mts) | Documents: links, anchors and math GitHub renders. |
| [`json-field-names.mts`](json-field-names.mts) | TypeScript, Lean and OCaml use the same JSON field names. |
| [`node-runs.mts`](node-runs.mts) | The examples and native-contract counterexamples run under Node with the outcomes the cases state. |
| [`trusted-inputs.mts`](trusted-inputs.mts) | The front end's trusted inputs: pinned declarations, resolved files, imports, the array overlay. |
| [`tool-failures.mts`](tool-failures.mts) / [`force-tool-failure.mts`](force-tool-failure.mts) | A failure of the compiler's API forced at each kind of site that catches what a query throws (a read refused into a value or a located error, a lookup made an absence, a computed type refused when generic, an imported module left out, `unchecked.mts`'s uninspected nodes) is reported as a tool failure, also when it strikes after a request was sent, a native read failure included; no request follows on a damaged channel, and the next parse opens a fresh compiler; a failure releasing the compiler is a tool failure naming the refusal in flight; an abandoned compiler's process ends; `unchecked.mts` reports every panic, retried or not; a step killed by a signal is a tool failure. |
| [`compiler-api.mts`](compiler-api.mts) | The compiler-API contract against the installed package: the host package is the audited installation with the reviewed declarations (C0); the host enums' declared values are their runtime values (C1); `jsDoc` allocates on each read, a stable member does not (C4). |
| [`rule-inventory.mts`](rule-inventory.mts) / `rule-inventory.snap` | The rules REQUEST-PROTOCOL documents are the rules Lean declares. |
| [`unchecked-project/`](unchecked-project/) | The counterexamples [`tools/unchecked.mts`](../tools/unchecked.mts) must report, each line marked `// expected: KIND`: flows of an external `any` (`library/` declares them) through results, properties read and written, index signatures, aliases, generic arguments, heritage, defaults beside constraints, conditional types, callback and rest parameters and an unreviewed input; the compiler's brands; `JSON.stringify(undefined)`; suppression directives, a syntax error; values still typed `any`; functions at a unit's boundary; and, unmarked, the `Object.assign` mutations outside the check. |
| `unchecked-project/gaps.mts` | Unmarked: the documented gaps, programs the check accepts by its stated limit (the relations `any` satisfied in an outside declaration are not re-established) though the written program or the written types refuse them. |
| [`unchecked-broken/`](unchecked-broken/) | A project the command must refuse: its external declaration names a type that does not exist. |

## Adding a case

A new feature comes with a positive witness and an independent negative
control. Promotion of a boundary case depends on implemented semantics and
checking, not merely on the parser accepting the syntax.

A negative control must be independent: it must fail the check being added and
pass every shortcut that would also accept the positives. A bad program that
any lowering refuses proves nothing about the new rule. For a universal check,
this means a program that satisfies every observed instance and fails only the
universal obligation — `pipeline/examples/invalid-scheme-capture.ts`
instantiates its binder at `boolean` at every call, so per-call specialization
accepts it and only scheme introduction refuses it. A control must reach that
obligation and fail there; a refusal before any obligation exists is a boundary
fixture, not a control, and is filed as one.

Each example function has a doc comment explaining the behavior or proof
obligation it illustrates. For unsupported examples, the comment distinguishes
the adapter's limitation from a soundness result; loop examples say when
termination is not established.

## Path-witness and stable-link evidence controls

`node pipeline/test.mts` derives the 4a and 4b forgeries from each run's
claims and evidence. Function names, parsed statements, source spans and named
receiver paths select the changes. There are no stored evidence patches or
fixture regeneration commands.

[`pipeline/evidence-mutations.mts`](../pipeline/evidence-mutations.mts) builds
an isolated mutation executable in the run directory from the current Lake
build's generated C and link response file. Run `(cd lean && lake build)` first.
The helper uses the pinned toolchain's compiler; it reads the Lake cache and
writes only to the run directory. `pipeline/test.mts` builds it once per run,
beside its controls (`node pipeline/evidence-mutations.mts --build`), and
gives it to its control processes; its invocations replay from the stage
store by its executable's digest and the mutation selection
([controls](../docs/STAGE-STORE.md#controls)). The production verifier and
Lean sources contain no mutation switches.

The mutations bypass mapped/observed edge coverage, read-link entailment or
heap-cell entailment, retain all links through `withStable`, or retain links
through `handlerFacts`. Symbol lookup requires one matching definition and
checks the handler's inlined call site. A compiler output change that breaks
these anchors fails the test. The coverage search constructs empty subtype
choices for the destination context; the other mutations use ordinary search.
Each generated document must be accepted under its selected mutation and
refused with each selected component removed. The stable and handler controls
also require refusal under each other's mutation. The production verifier
checks every forgery against its exact refusal location, including the handler
edge at `[405,424)`.
