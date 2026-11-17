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

## Assertion transport continuation at c71d1ec5

Evidence from the cloud checkout on 2026-11-17, starting from
`2819388e290f907d206c5c0bf26a925ef0fa7cb0` and covering the source and
correspondence in `c71d1ec509464c63016bdab7f7864a3d65359aa7`. A fetch confirmed
`origin/single-pass` remains `ba681dfdab8ab41c7d73f3c573f449ab90fedab7`.
This continuation adds total assertion renaming and admission transport,
grammar-admissible selected path replacement through binders and modalities,
and full syntactic Inst, Prefix and Empty. It also restricts consequence and
modal premises to valid paper contexts. The paper and A/shared code are
unchanged.

Focused builds passed for every added module and its derivation/transfer
integration. Both axiom checks passed together (401 jobs). The build replayed
eight informational `Lean.Meta.whnfEasyCases` PANIC backtraces from the
unchanged A module `Verification.Programs.TolerantFramesStepLink:294`.
The same eight backtraces occur in the saved initial full-build and axiom logs;
the command exited zero and no new module emitted a warning or error.
These cached informational traces are not described as warning-free output.
The axiom dependency results themselves passed with the existing permitted
axioms.

The complete supervised `make test` invocation exited zero under pinned Lean
4.33.1, Node 26.13.0 and `bc`, within an 1800-second budget. It passed:

- the full Lean build (610 jobs);
- all 23 fast suites, including type checking, JSON field names, unchecked
  boundaries, documentation, import coverage and all 175 controls;
- **3419 of 3419 pipeline cases as expected**, 4322 functions verified,
  1782 negative controls and 147 named gaps.

The controls ran on four lanes, with 3 operations executed and 492 replayed
from the repository's content-addressed store. No expected result changed.
Direct axiom-check coverage includes 363 other A/shared modules and 35 other
Paper modules. A separate import scan found no importer of Paper outside
Paper. `git diff --check` and the commit-record hook passed. The final
documentation check reported 76 documents, 892 code citations and no problems.
The raw cloud logs are `/workspace/scratch/continuation-test.log` and
`/workspace/scratch/continuation-axioms.log`; those scratch paths are evidence
locations in this execution environment, not required repository inputs.

Independent read-only Astra review compared all five added modules, their
integration and the revised audit with the paper. It checked capture under
binders, aliased renaming images, definedness of zero-coefficient terms,
all element readings and fields, whole modal action transport, independent
declared admission, and derivation of collection entries for Empty. It found
no soundness or correspondence defect. It confirmed the Inst and Empty
upgrades and the **42 equal / 25 narrower / 9 absent / 13 assumed** accounting.
The reviewer did not run the checks recorded above.

General existential logic, full mixed old/current substitution and
postcondition syntax, structural supports, Call/Fun, primitive/host bridges,
complete derivation admission and closed paper examples remain outside the
proved scope. The correspondence table states those limits individually.
This validation does not establish full alignment or automatic proof-search
completeness.

## Support, witnesses and arithmetic at 1d11d168

Evidence from the cloud checkout on 2026-11-17, for source commit
`1d11d168133c9b85f1dc19c3b2a68df79d94dee4`, following continuation validation
`4174ff63445258c2d82ae443613d3139113c25e8`. Focused builds passed for
AllSupport, Existentials, Arithmetic and Obstructions, then their finite
derivation and transfer integration. Both A and Paper axiom checks passed
together (405 jobs). The same eight cached informational Lean PANIC traces
from unchanged A code described above were replayed; they introduced no new
module warning or error and did not change the exit-zero axiom result.

A complete supervised `make test` invocation exited zero under the pinned
Lean and Node versions with `bc`, within its 1800-second budget:

- full Lean build: 614 jobs;
- all 23 fast suites, including all 175 controls;
- **3419 of 3419 pipeline cases as expected**, 4322 functions verified,
  1782 negative controls and 147 named gaps.

The controls ran on four lanes, with 3 operations executed and 492 replayed.
Axiom-check direct import coverage includes 363 other A/shared modules and
39 other Paper modules. The separate source scan found zero imports of Paper
from outside Paper; every changed Lean file is under Paper. No shared
semantics, acceptance decision or expected test result changed. Documentation
checking passed with 76 documents, 892 code citations and zero problems;
`git diff --check` and the commit-record hook passed.
Raw cloud logs are `/workspace/scratch/support-test.log`,
`/workspace/scratch/support-axioms.log` and
`/workspace/scratch/support-docs.log`.

Independent read-only Astra review checked the full modality-free all-support
statement, the one-way preservation proof, current-only witness opening,
old monotonicity, all framing, recursive term occurrence and exact arithmetic
definedness, fixed literal interpretations, and the defined length ranges.
It found no soundness defect and confirmed the unchanged 89-row accounting:
**42 equal / 25 narrower / 9 absent / 13 assumed**. It did not rerun compilation
or the regression suite.

The review also identified the negative-zero obstruction and checked its
kernel proof: in a valid environment containing only `-0`, integer term
equality with zero holds while raw value equality with `+0` fails. The
unrestricted reverse bridge is not admitted. This is an interpretation
obstruction requiring an owner decision, not a false integer-arithmetic
claim. The paper is unchanged. Earlier statements about no demonstrated
obstruction apply only to their explicitly named saved source scope.

All support and the new logic/arithmetic constructors close parts of
Definitions 14 and 23. They do not establish the structural support table,
full mixed old/current syntax and substitution, all primitive/host bridges,
Call/Fun, complete derivation admission or closed paper example proofs.
Those limitations remain explicit in the audit and the owning WORK row.

## First-order postconditions at 9a410bd4

Evidence from the cloud checkout on 2026-11-17 for source commit
`9a410bd4c065980e3adeae9c791fca8ecc5b6a9a`, following validation commit
`bb126d9414adf27f70e6c0eb4d1d12c26cdf33fe`. All six new modules passed focused
builds: syntax, scope, admission, renaming, exact postcondition formulas and
frozen index instantiation. Both axiom checks passed together (411 jobs).
The same eight cached informational Lean PANIC traces from unchanged A code
were replayed, with no new module warning or error; the command exited zero.

A complete supervised `make test` exited zero under pinned Lean 4.33.1 and
Node 26.13.0 with `bc`, within its 1800-second budget:

- full Lean build: 620 jobs;
- all 23 fast suites and all 175 controls;
- **3419 of 3419 pipeline cases as expected**, 4322 functions verified,
  1782 negative controls and 147 named gaps.

The controls ran on four lanes, with 3 operations executed and 492 replayed.
Axiom-check direct import coverage includes 363 other A/shared modules and
45 other Paper modules. A source scan found no imports of Paper outside Paper;
all Lean changes remain inside Paper. Documentation checking passed with
76 documents, 892 code citations and zero problems; diff and commit-record
checks passed. No shared semantics, trust assumption or expected outcome
changed. Logs are `/workspace/scratch/postcondition-test.log`,
`/workspace/scratch/postcondition-axioms.log` and
`/workspace/scratch/postcondition-docs.log` in the cloud environment.

Independent read-only Astra review checked the raw/admitted distinction,
separate entry/current name scopes, logical valuation agreement, odd-only
value-binder lifting, total semantic renaming and whole regional-action
transport. It checked Q_<, Q_≠i, Push and converted View-Write interpretation
proofs, including the role proof of source-valued old element reads. It also
checked frozen instance evaluation and the conditional phase obstruction.
It found no blocking soundness defect or correspondence overclaim and
recounted **42 equal / 25 narrower / 9 absent / 13 assumed**, 89 main rows.
It did not rerun builds or regression tests.

These proofs establish first-order syntax, static admission, interpretation,
logical valuation independence and semantic renaming. They do not establish
admission preservation under declaration pullback, full mixed-state/path/term
substitution, mixed-state arithmetic or actual native command execution.
The frozen-index theorem is auxiliary and is not a new Definition 23 rule.
Its textual-substitution obstruction assumes term evaluations zero at entry
and one currently; it does not construct an admissible execution or prove
that particular textual formula admitted. The owner was asked to clarify the
index-at-term sentence. The earlier raw-value negative-zero obstruction also
remains unresolved. The paper's mathematics is unchanged.

## Corrected literals and path supports at 3ad56a37

Evidence from the cloud checkout on 2026-11-17 for source commit
`3ad56a37ae4b1c30931fe16cc6e9d859e39b602f`, following validation commit
`f1aaea528085f277e3787671e1d81b2b89dcf827`. The owner supplied the exact
Definition 23 signed-zero correction during this continuation. The paper and
PDF contain that authorized correction; other paper mathematics is unchanged.
The original countermodel remains valid evidence against the former clause,
not an obstacle to the corrected rule.

Focused builds passed for LiteralEquality, PathSupports and the concrete
FreshnessCounterexample, then corrected literal derivations and transfer.
Both axiom checks passed together (414 jobs). The same eight cached
informational PANIC traces from unchanged A code were replayed, with no new
module warning/error; the command exited zero.

A complete supervised `make test` exited zero under pinned Lean 4.33.1 and
Node 26.13.0 with `bc`, within its 1800-second budget:

- full Lean build: 623 jobs;
- all 23 fast suites and 175 controls;
- **3419 of 3419 pipeline cases as expected**, 4322 functions verified,
  1782 negative controls and 147 named gaps.

Controls used four lanes, with 3 operations executed and 492 replayed. Direct
axiom import coverage includes 363 other A/shared and 48 other Paper modules.
The source scan found zero outside-to-Paper imports, and no changed Lean
module is outside Paper. Documentation passed with 76 documents, 892 code
citations and zero problems; diff and commit-record checks passed. Logs are
`/workspace/scratch/literal-path-test.log`,
`/workspace/scratch/literal-path-axioms.log` and
`/workspace/scratch/literal-path-docs.log`.

The paper HTML build initially failed because its Pandoc option was unsupported;
both calls use the standard `--mathjax` option. It then passed with zero
unconverted commands. The PDF build initially lacked TeX prerequisites. They
were installed in isolated cloud scratch, without changing the paper's style:
newtx 1.756 (TeX Live revision 78101), mathpartir 1.3.2 (77682), stmaryrd (77682),
kastrup (15878), txfonts (77682), tex-gyre 2.501 (68624). With those prerequisites,
`python3 color.py` and `latexmk -pdf note-color.tex` completed; after package
installation `-g` forced reevaluation of cached failures. The 26-page tracked
PDF was rebuilt and the corrected rule on page 22 visually inspected. Logs
are `/workspace/scratch/paper-literal-render.log` and
`/workspace/scratch/paper-literal-pdf.log`; generated intermediate files were
removed from the repository. The rendered HTML was retained in cloud scratch.

Independent read-only Astra review confirmed all three literal rules exactly
match the owner's decision, preserve raw equality and use no broader trust.
It checked omission reinsertion and shared traversal reuse, the four exact
successful-read support rows, and the concrete freshness countermodel. The
latter has actual valid-context indexed heaps, an admissible transition and
admitted regions/support under the indicated nullable path classifications;
it is not a full source EnvTyping derivation or command execution proof.
The reviewer found no blocking defect or correspondence overclaim, and
confirmed unchanged **42 equal / 25 narrower / 9 absent / 13 assumed** accounting.
It did not rerun builds or rendering checks.

The paper's failed-prefix freshness support is mathematically obstructed;
its repair and the interpretation of index-at-term instantiation await owner
decisions. Other structural supports, full substitution/admission transport,
primitive/host bridges, Call/Fun and closed examples remain explicit obligations.
No full-alignment claim follows from this validation.


## Owner-requested rebase on 2026-11-17

The original fetched start remains `ba681dfdab8ab41c7d73f3c573f449ab90fedab7`.
On the owner's instruction the implementation was rebased onto the newly fetched
`single-pass` tip `56aaacc51899986d365a3853c94ac58420c1d1b8`. Its twelve commits
were replayed; the rebased pre-continuation tip is
`3224a2efc07734c76d31031e535e27a92f12078c`.

The audit conflicts retain the new correspondence analysis and the owner's
latest array terminology. The paper conflict retains upstream note.tex and PDF
exactly: upstream commit `37c331eb` already contains the authorized signed-zero
correction. The task adds no further mathematical edit. The draft PR is titled
“Codex: align the Lean implementation with Tolerant frames” and still targets
single-pass. The exact old remote tip was used as the force-with-lease value;
no concurrent remote update was overwritten.

The source-commit mapping makes the earlier evidence traceable; that evidence
was measured before rebase and does not certify upstream A changes:

| Earlier source | Rebased source | Scope |
|---|---|---|
| f4809394 | 72938dbb | Semantic premises |
| 2bc3023d | 9aa4aef2 | General assertions |
| f4e44a94 | c6b24bcd | Commands and transfer |
| c71d1ec5 | daf6b169 | Assertion transport |
| 1d11d168 | 05540a4c | All support, witnesses and arithmetic |
| 9a410bd4 | cf5d397d | Two-state postconditions |
| 3ad56a37 | 8ca78a78 | Literal and path supports; paper correction already upstream |

The PR's code-impact comparison is now against the rebased tip, rather than
against the original start. There are no task-authored Lean changes outside
Verification.Paper. Changes to A present between the original start and this
base belong to the owner's upstream branch. The new full regression run checks
the resulting rebased repository; old acceptance results are not reused as
proof that those upstream changes passed.

## Heap-based quantifiers and structural supports at 0ff68167

This evidence applies to source commit
`0ff68167b90d7c9e177ce4b5a5539dfab0cf481f`, after the owner-requested rebase
onto `56aaacc51899986d365a3853c94ac58420c1d1b8`. The original fetched start is
still `ba681dfdab8ab41c7d73f3c573f449ab90fedab7`. Scratch work on the next Call
proof was outside the repository and is not part of this validation claim.

### Proof and regression results

Focused builds passed for heap validity, the refactored support/consequence and
binder rules, Empty, rigidity, below-mark bounds, all first-order postcondition
scope/renaming/interpretation modules, and complete modality-free/HeapOnly
world independence. The universal/existential reflexivity law is a theorem in
the actual AST; no test replaces a logical proof.

Both A and Paper axiom audits passed together, exit zero, 422 build jobs. The
same eight informational PANIC backtraces from upstream A's
Programs/TolerantFramesStepLink.lean:294 are replayed; they were also present in
the original baseline logs. The audit rejects nonstandard axioms and found none
in Paper. No new-module warning or error was emitted.

The full `make test` completed under timeout 1800 with exit zero:

- 631 Lean build jobs;
- 23 fast suites passed, none failed;
- 175 controls on four lanes, 460 operations executed and 35 replayed;
- 3431/3431 pipeline cases as expected;
- 4323 functions verified, 1790 negative controls and 150 named gaps.

The case inventory differs from the previous pre-rebase 3419-case report because
this run includes the owner's new single-pass commits. This is a complete run
on the rebased source, not reuse of the older acceptance results. GitHub CI is
separate and is not assumed to pass.

Direct import coverage passed: all 363 other A/shared modules and all 56 other
Paper modules are imported by their respective axiom checks. A separate source
scan found zero imports of Paper from outside Paper. The diff of task-owned
Lean code against the rebased base has zero files outside Verification.Paper.
The upstream note.tex and PDF are identical to that base. Final documentation
check passed: 77 documents, 892 citations, zero problems; diff whitespace checks
passed.

Cloud logs: `/workspace/scratch/rebased-quantifier-support-test.log`,
`quantifier-support-axioms.log`, `universal-heap-domain.log`,
`world-independence-build.log`, `quantifier-support-docs-final.log`.
Tool versions and the general reproduction commands remain as above.

### Independent correspondence and soundness review

The read-only Astra reviewer checked the stable heap-domain design before
integration, then checked the implementation, phase-aware universal-domain
revision, affected support proofs and documentation against the paper. It found
no unsafe theorem. It specifically checked the unchanged world-valid command
contexts and result guarantees, no inference of fine roles from null contents,
actual heap W3 use, invocation-entry bounds, phase-local witness validity and
equal-heap independence through quantifiers and old terms.

The review caught the former universal/existential domain mismatch; the source
now uses one current heap domain and the corresponding focused old domain.
It also required explicit admissibility in old-element/Push/View interpretation
bridges and corrected stale descriptions that equated logical HeapContext with
program well-formedness. Those corrections are incorporated. The complete
89-row recount remains 42 equal, 25 narrower, 9 absent, 13 assumed. Remaining
substitution/admission, support assembly, Call/Fun/body realization, primitive
and host bridges, derivation coverage and closed examples are not claimed done.
The owner decisions on failed-path freshness support and index-at-term
instantiation remain pending. The next Call/Fun operational design was reviewed
without being claimed as an implemented rule.
