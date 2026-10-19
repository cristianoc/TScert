# Verification regressions

`make test` runs the fast checks, which need no build
([`test-all.sh`](../test-all.sh)); `make suite` builds, then runs the pipeline
cases and controls ([`pipeline/test.mts`](../pipeline/test.mts)).

The pipeline cases are listed in [`pipeline/cases.mts`](../pipeline/cases.mts),
each a source file under [`pipeline/examples/`](../pipeline/examples/) with its
expected outcome, run by `pipeline/run-cases.mts` (`make cases P=…`) and, with
the controls no case can make, by `pipeline/test.mts`. Two families in
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
installs it as the host through the test-only stand-in for the
`*host-fixture*` controls of reading rule 1.
Lean tests build alongside the implementation in `lean/Verification/Tests/`.

This directory holds the suites that check the repository around the pipeline:

| Tests | Coverage |
| --- | --- |
| [`docs.mts`](docs.mts) | Documents: links, anchors and math GitHub renders. |
| [`json-field-names.mts`](json-field-names.mts) | TypeScript, Lean and OCaml use the same JSON field names. |
| [`node-runs.mts`](node-runs.mts) | The examples and native-contract counterexamples run under Node with the outcomes the cases state. |
| [`trusted-inputs.mts`](trusted-inputs.mts) | The front end's trusted inputs: pinned declarations, resolved files, imports, the array overlay. |
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
