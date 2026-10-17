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
`typescript` the front end pins, for the `*compiler-api*` cases.
Lean tests build alongside the implementation in `lean/Verification/Tests/`.

This directory holds the suites that check the repository around the pipeline:

| Tests | Coverage |
| --- | --- |
| [`docs.mts`](docs.mts) | Documents: links, anchors and math GitHub renders. |
| [`json-field-names.mts`](json-field-names.mts) | TypeScript, Lean and OCaml use the same JSON field names. |
| [`node-runs.mts`](node-runs.mts) | The examples and native-contract counterexamples run under Node with the outcomes the cases state. |
| [`trusted-inputs.mts`](trusted-inputs.mts) | The front end's trusted inputs: pinned declarations, resolved files, imports, the array overlay. |
| [`compiler-api.mts`](compiler-api.mts) | The compiler-API contract against the installed package: the host enums' declared values are their runtime values (C1). |
| [`rule-inventory.mts`](rule-inventory.mts) / `rule-inventory.snap` | The rules REQUEST-PROTOCOL documents are the rules Lean declares. |

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
