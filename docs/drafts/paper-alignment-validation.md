# Paper alignment validation

## Saved baseline at 2819388e

The evidence in this section applies to the initial implementation and validation
through commit `2819388e290f907d206c5c0bf26a925ef0fa7cb0`. Its module counts,
correspondence counts and test runs do not validate subsequent source changes.

Evidence from the cloud checkout on 2026-11-17. This records validation of the
reviewed implementation, not completion of the full formalisation. The owning
status is [WORK.md](../../WORK.md#status); the complete item comparison is
[B against the paper](b-against-the-paper.md).

### Reproduction and provenance

The repository was cloned in the cloud workspace on `single-pass`. A fetch
verified both the checkout and `origin/single-pass` at
`ba681dfdab8ab41c7d73f3c573f449ab90fedab7`, exactly the launch record. The
implementation is in three dependency-ordered commits:

- `f4809394e7bdd5affedfb35e2e6a102ecd966dda`: semantic premises and rules.
- `2bc3023d59d8e2ca041391a85a34c357ca9f6782`: general assertions and consequences.
- `f4e44a949c7bb76fce64ca2a9665c1622102985e`: commands, scopes, loops,
  logical subcalculus, regional transfer and the actual alias-loop encoding.

The review branch targets `single-pass` in
[draft PR #250](https://github.com/cristianoc/TScert/pull/250). It is not merged.
All required paper, audit and design inputs are in the starting commit’s
ancestry. The paper’s mathematics is unchanged. The owner’s computer was not
used or modified.

Lean is the repository-pinned `leanprover/lean4:v4.33.1`. Node is the
repository-pinned `26.13.0`. The compiler, Node binary and missing `bc` were
installed in cloud scratch; `make setup` installed the locked repository
Node dependencies. To reproduce, use those versions and the repository’s
usual build/test commands, with `bc` available.

### Proof and boundary checks

Focused builds of each new dependency layer passed with warnings treated as
errors. A clean full `lake build` passed (603 jobs); incremental full builds
also included the Paper axiom check. After the last review correction to the
independence domain, this command passed without warnings (396 jobs):

```sh
cd lean
lake build Verification.Tests.AxiomCheck Verification.Paper.TolerantFrames.Tests.AxiomCheck
```

Both axiom checks accept only `propext`, `Classical.choice` and `Quot.sound`.
No project axiom, `sorry`, unsafe cast or broader trust was introduced.

`node tests/axiom-check-imports.mts` confirmed direct import coverage of all
363 other A/shared modules and all 30 other Paper modules. A separate scan of
every Lean module outside `Verification.Paper` found no import of a module
inside it. All changed Lean files are under `Verification.Paper`; no shared
assertion schema, heap/world/region semantics, acceptance decision, lowering,
wire format, trust declaration or headline acceptance theorem changes.

### Static and regression checks

The following passed:

- `(cd tools && npx tsc -p tsconfig.json)`.
- `node tests/json-field-names.mts`: all 17 comparisons agree.
- `node tools/unchecked.mts`: no errors; all 12 assertions have reasons.
- `node tests/docs.mts`: no documentation problems.
- All 23 fast-check suites, including all 175 controls, under pinned Node and
  `bc`. The controls completed on four lanes; no expected outcomes changed.
- `node pipeline/run-cases.mts`: **3419 of 3419 cases as expected**;
  4322 functions verified, 1782 negative controls and 147 named gaps.
- The commit-record hook accepted each implementation record, and
  `node dev/commit-records.mts` rendered the implementation range.

The initial run under the environment’s Node 24.22.1 failed the pinned-runtime
and Node-behaviour checks, and the report-list check failed because `bc` was
missing. Installing the exact prerequisites corrected those failures; no code
or expected test result was changed to accommodate the environment.

The subsequent `make test` run passed all 23 fast suites but reached its
overall 600-second limit before the pipeline-case summary (1368 of 3419
progress reported). It is **not** reported as an exit-zero `make test` run.
The complete standalone case run then passed under a bounded budget based on
the observed cloud throughput. The final axiom builds and standalone cases
cover the final proof statements; the only source change after the fast
suite was the Paper-only independence-domain correction, with no A importers.
GitHub CI results are separate from these local results and are not assumed.

### Independent statement review

An independent `gpt-6-astra` subagent performed read-only reviews against the
paper’s actual premises and conclusions. It did not run compilation or the
regression suite. It identified, and checked corrections for:

- freezing the function entry, rather than a local command entry, for Return;
- retaining shared abrupt obligations in Conj so only the second normal and
  exceptional posts require independence;
- valid input/output contexts and valid returned/thrown values;
- deriving caught-variable validity from the typed exit guarantee;
- own-field reading instead of prototype fallback on an absent field;
- scalar-only command literals, source-valued existential witnesses, element
  suffix restrictions and Boolean operations;
- restricting semantic support, invariance, rigidity, independence and modal
  side conditions to valid paper contexts;
- distinguishing the actual alias-loop command and arithmetic/scoping proofs
  from a closed primitive/graph execution proof;
- separating semantic rules from finite certificates, the incomplete general
  derivation subcalculus and automatic search.

Its final finding was no unsafe added theorem and no remaining material
overclaim in the reviewed correspondence statements. It accepted the
**40 equal / 27 narrower / 9 absent / 13 assumed** table as a statement of
those individual proof scopes, explicitly **not** a claim of full alignment.

### Limits of the evidence

Compilation and axiom checks establish proof checking and axiom dependencies,
not correspondence. The independent source review supplies the separate
statement comparison. Regression success preserves the observed acceptance
behaviour; the unchanged A/shared source and enforced import boundary explain
why the added theory is removable.

Full substitution and postcondition syntax, structural/all supports, the
remaining Call/Fun and effect-composition rules, exact primitive/body/native
bridges, explicit host-contract declarations, complete Definition 23 and
closed paper example proofs are not established by this validation. Those
obligations are recorded individually in the correspondence table and in the
owning status. Host contracts remain assumptions; no actual native library is
claimed verified. No demonstrated false paper statement requires an owner
decision, and the apparent extra premise in Conj was resolved as an encoding
issue.
