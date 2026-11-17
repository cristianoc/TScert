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

## Actual scoped Call at 9a14cf79

Evidence applies to source `9a14cf79b12544bfdf7213d65c63938570d99ca2`, extending
`985650598f34ce169a178fc5ff4a6621eb2dadfb` on rebased single-pass
`56aaacc51899986d365a3853c94ac58420c1d1b8`. The original fetched start remains
`ba681dfdab8ab41c7d73f3c573f449ab90fedab7`.

All eight new scope/renaming/admission/Call modules passed focused builds under
warnings as errors. Both complete axiom audits passed together, exit zero,
430 jobs, with only the same eight cached informational upstream A backtraces.
The full `make test` completed with exit zero:

- 639 Lean build jobs;
- 23 passing fast suites, none failed;
- 175 controls; 3 operations executed and 492 replayed on four lanes;
- 3431/3431 cases as expected;
- 4323 functions verified, 1790 negative controls and 150 named gaps.

Direct import coverage passed for all 363 other A/shared modules and 64 other
Paper modules. Separate scans again found no outside-to-Paper imports and no
task-authored A/shared Lean changes against the rebased base. Paper mathematics
and upstream PDF remain untouched. Documentation passed at 77 documents,
892 code citations and zero problems; whitespace checks passed. The semantic
commit records render against the exact new base.

Independent read-only Astra review checked actual primitive/formal-call execution
correspondence, all-name output validity, chosen world/budget preservation,
finite mapping extension, aliases, complete AST program-map agreement and
phase-specific scope/declaration transport. It identified two admission gaps in
an intermediate version: image freshness alone did not exclude unrelated caller
bindings, and semantic dependence alone did not imply lexical precondition
scope. The final theorem requires whole-caller freshness and returns actual
Command.WellScoped; FormulaScopes supplies lexical scope for every mention,
including tautologies, and proves dependence/renaming. The assembled theorem
also handles both outer effect scopes and extension independence. Final source
review found no unsafe theorem or remaining blocker to the stated finite
variable-actual Call transport. Documentation corrections distinguish
precondition meaning equality from postcondition AST equality.

The formal call Triple is already uniform at command marks; the theorem retains
that mark and chosen world. Declaration pullbacks are explicit assumptions,
not inferred EnvTyping facts. The Call row stays narrower: actual rest/spread
preparation and freshness-mark rebasing remain, while Fun still needs its
operational body realization. All 89 counts remain 42 equal, 25 narrower,
9 absent and 13 assumed. Full alignment is not claimed.

Logs: `/workspace/scratch/call-scope-test.log`, `call-scope-axioms.log`,
`call-scope-docs.log`, and the focused `*-build.log` files for these modules.


## Raw execution, lexical scope and budgets at 72d0295c

Evidence applies to source `72d0295c9b775746a35cb1ac7501e46c08fc210d`, extending
`9d708349a34bf9d7788c2203cb4a8be4005ea9f1` on rebased single-pass
`56aaacc51899986d365a3853c94ac58420c1d1b8`. The original fetched start remains
`ba681dfdab8ab41c7d73f3c573f449ab90fedab7`.

Focused raw-execution/scope integration and budget proofs pass with warnings as
errors. Both complete axiom audits pass, exit zero, 431 jobs, with only the
same eight cached informational upstream A backtraces. Full make test exits
zero: 640 Lean jobs, 23 passing fast suites, 175 controls (3 operations executed,
492 replayed), 3431/3431 expected cases, 4323 verified functions, 1790 negative
controls and 150 named gaps. Documentation passes at 78 documents, 892 code
citations and zero problems. Direct import coverage passes for 363 other
A/shared and 65 other Paper modules. There are no outside-to-Paper imports or
task-authored shared Lean changes; paper mathematics and PDF are unchanged.

Independent read-only Astra review checked raw isVal versus the strong source
exit guarantees, output validity recovery, lexical joins/catch scope and input
preservation, and both one-state/two-state syntactic budget proofs. It found no
soundness blocker and confirmed the explicit admissibility and budget bounds.
The alias example's scope proof is not a closed execution proof. Budget
transport is not claimed for arbitrary semantic assertions. The operational
function design uses the body triple at the original budget, then restricts
its chosen exit; no full Fun theorem or graph lowering is claimed. The
own-key backend extension remains a reviewed design, with the existing
request-tag vocabulary identified as a required conservation boundary.
All 89 audit counts remain 42 equal, 25 narrower, 9 absent and 13 assumed;
the full alignment is incomplete.

Logs: `/workspace/scratch/raw-scope-budget-test.log`,
`raw-scope-budget-axioms.log`, `raw-scope-budget-build2.log`,
`budget-truncation-build.log` and `raw-scope-budget-docs.log`.


## Second owner-requested rebase, onto the newer paper

A fresh fetch found three additional owner commits on single-pass. The
implementation was rebased without conflicts from `56aaacc51899986d365a3853c94ac58420c1d1b8`
onto exact fetched tip `f2e33e7f35769d00dd6aa1763d86d3c6ef41983f`.
The original fetched start remains `ba681dfdab8ab41c7d73f3c573f449ab90fedab7`.
All owner note.tex/PDF and pipeline changes are retained exactly. This rebase
adds no task-owned paper mathematics or A acceptance changes. Rewritten source
and record commits map as follows:

- `72938dbb5d2acca1e128945da1b531e1a914c6e2` → `26d0fbd2c264bf97b34a9203cb98fb9ef3bf130f`: State semantic support and respect at the paper's generality.
- `9aa4aef2723f4fbc7c94381ee2b5d25af59cdfa3` → `0e0d4113e18dcda0b219d8cb8548240478a832a6`: Interpret general paper assertions and quantified consequences.
- `c6b24bcd3f32de7347327ce6baf40f7c5e9f4f42` → `c5dfad3867728aec83c0537e1c46a769687c9a6c`: Prove general command rules and regional checked transfer.
- `8d90138ec1f95c910d0bed677d18427c4009a55d` → `1c5a117d9e84336b1cec0259d5333315999bc85b`: Record final Paper proof, regression and correspondence validation.
- `daf6b1692d91b4ee332a6b3a2d8c33e471f3d20e` → `9065f4535d24cd15f5042e9764b0519de5014351`: Prove capture-avoiding assertion transport and full quantified rules.
- `d7259435dbdbe455415a557dfd87ed6f88eb2c4e` → `4f99c4ab08f26552989361987f1e7205f671ecac`: Record full validation of the assertion transport continuation.
- `05540a4c061a3527f85344866afe4f7b5b102e8c` → `7a6c41b524e4b08a1e0c6f51b76178a2044c9a74`: Prove general all support, witness rules and integer consequence.
- `af3da32a15a90146ee1b346defb718b8cc8ff011` → `b029933092b487ac695c79762502fdd7191edbb3`: Record validation and the numeric equality obstruction.
- `cf5d397deded2809842d157f58641f2981158a81` → `6b2df2341132bd4ab8e54509b3c837d9442fbafb`: Formalise first-order two-state postconditions and their transport.
- `e10a35cfafa90dabf52614fc58530797f711e6d2` → `a6a692473432e8b2412b22483d3e6652eaf6d4b7`: Record validation of first-order postcondition proofs.
- `8ca78a780f5f7474c229f8043b58475b065c8c84` → `b907a21a5fff67b20e1f8a7905dfd7073026073a`: Correct the zero bridge and prove conditional path supports.
- `3224a2efc07734c76d31031e535e27a92f12078c` → `2a1c50d28dfddfd0bca2a8cc8d2b608522b0fdd1`: Record validation of the corrected literal and path support proofs.
- `0ff68167b90d7c9e177ce4b5a5539dfab0cf481f` → `c735b67546c32b6333acc75444a469aefe6ca40a`: Make logical witnesses heap-based and prove structural supports.
- `985650598f34ce169a178fc5ff4a6621eb2dadfb` → `47af13f28534ff27e11ffa0b41fa30d2542b718d`: Record rebased quantifier and support validation.
- `9a14cf79b12544bfdf7213d65c63938570d99ca2` → `a082e3d8b0765b69fe607b46fa10a4e2ee0a2859`: Prove scoped Call instantiation on actual executions.
- `9d708349a34bf9d7788c2203cb4a8be4005ea9f1` → `e88e2d9e2d7d8980a5afa2c6d8b94c2fa6a52f08`: Record exact scoped Call validation and review.
- `72d0295c9b775746a35cb1ac7501e46c08fc210d` → `b703b5de9b7a1c3f67d96ff4972ca43fcf7fca33`: Observe raw completions and prove scoped budget transport.
- `7c627ecd1ccabc81f4206f66b29c150032f6cb3f` → `7fcd1a5c1266b2add64e3956fddf56af416e4c8c`: Record raw execution and budget proof validation.

The newer paper gives signed Shr with integer shift-count normalization,
Mask at arbitrary safe operands, and new Shl/Or rules. The original 89 rows
are all retained, with Shr/Mask reclassified narrower; the new two absent
rows give 91 total: 40 equal, 27 narrower, 11 absent and 13 assumed. The
independent Astra source review confirms these classifications. In particular,
a proof assuming a safe shift count would not by itself cover the paper's
broader integer-constant wording. Stale original-audit paper line anchors
are removed; rule/definition labels identify the current statements.
The own-key source continuation is validated separately below; older full
runs are not claimed as validation of this rebase or of its shared changes.

## Conservative own-key and fixed-operation code at 69d3e9ac

Evidence applies to exact source `69d3e9acc3646d31e8304897e50d4ff4b5960434`,
extending rebased `7fcd1a5c1266b2add64e3956fddf56af416e4c8c` on latest fetched
single-pass `f2e33e7f35769d00dd6aa1763d86d3c6ef41983f`. Original fetched start
remains `ba681dfdab8ab41c7d73f3c573f449ab90fedab7`.

Focused shared foundations, fixed-operation prefix/inversion and forged nested
JSON controls pass with warnings as errors. Both complete axiom audits exit
zero, 433 jobs, with the same eight upstream informational backtraces. Full
make test completes with exit zero: 642 Lean jobs, all 23 fast suites, 175
controls (460 operations executed, 35 replayed), 3431/3431 expected cases,
4323 verified functions, 1790 negative controls and 150 named gaps. This run
executes the affected A controls and cases on the new binary, not merely the
old cached acceptance outcomes. Final documentation passes at 78 documents,
892 code citations and zero problems; whitespace checks pass. Direct import
coverage checks 363 other A/shared and 67 other Paper modules; a separate
scan finds zero outside-to-Paper imports. The current 91-row recount is
40 equal, 27 narrower, 11 absent and 13 assumed, including all original 89.

The precise shared changes are Calculus's pure internal tag/tagHolds case,
ValueSets's appended key and object-dependent normalization, TypingBasics's
conservative shape response for the new tag, RequestJson's frozen legacy Tag
codec, and ExecutionModelTests's forged decoder controls. No A producer emits
the new tag. All old tag meanings/keys and legacy JSON encodings remain; the
accepted request-tag vocabulary is closed before all dependent codecs. Exact
diagnostic bytes are not claimed unchanged. A's headline acceptance theorem
and trust assumptions are unchanged. Source proofs of simulation/inversion
remain on B's side. The task's paper source/PDF diff against the latest base
is empty; owner paper changes in the rebase are retained exactly.

Independent read-only Astra review checked pure own-key versus prototype
semantics, arbitrary machine values and field maps, nonobject stuckness,
normalization and conservative source typing, exact legacy constructor/payload
names, nested decoder coverage, all symbolic operation cases, internal let
binding and terminal deterministic cancellation. It found no soundness blocker.
It required explicit host.close ρ and preserved host-capture compiler
obligations; those qualifications are in source and correspondence documents.
The reviewer also read the latest paper's arithmetic changes and confirmed
both reclassifications and new absent rows. It identified the source-only
Raises condition: full raw B forward throw simulation would be false, while
completed graph-to-B inversion remains the required compiler direction.

Full command lowering, body/call anchors, rest allocation, Fun, new arithmetic
bridges and other previously listed gaps remain open. The two pending owner
mathematical decisions are unchanged. No axiom audit is used as evidence of
rule correspondence, and no native-library implementation is claimed verified.

Logs: `/workspace/scratch/own-key-test.log`, `own-key-axioms.log`,
`own-key-build1.log`, `own-key-build3.log` (for the nested decoder controls),
`own-key-build5.log`, `operation-code-build2.log`, `own-key-docs-final.log`.

## General Mask and Or commands at 38b31705

Evidence applies to exact source `38b317059e56dd0dc9f155dcceca7f8f8d7c2e48`,
extending `7dcd069f6f306430400b1e1c76a998fcef633ad6` on fetched single-pass
`f2e33e7f35769d00dd6aa1763d86d3c6ef41983f`. The original fetched start remains
`ba681dfdab8ab41c7d73f3c573f449ab90fedab7`.

All three new modules pass focused builds with warnings as errors. Both complete
axiom audits pass, exit zero, 436 jobs, with only the same eight cached upstream
informational backtraces. Full make test completes with exit zero:

- 645 Lean build jobs;
- 23 passing fast suites and 175 controls (3 operations executed, 492 replayed);
- 3431/3431 cases as expected;
- 4323 verified functions, 1790 negative controls and 150 named gaps.

Direct import coverage checks 363 other A/shared and 70 other Paper modules.
There are no outside-to-Paper imports. This continuation changes only Paper
Lean code; the preceding precise shared-impact account remains unchanged.
Documentation passes at 79 documents, 892 code citations and zero problems;
whitespace checks pass. The 91-row recount is 42 equal, 26 narrower, 10 absent
and 13 assumed. All original 89 rows are retained; Mask's general rule and the
new Or rule now have complete displayed semantic command statements/proofs.

Independent read-only Astra reviewed the numerical/pure-execution design before
integration, then the actual arithV bridges, chosen worlds, integer readings,
current-state formulas and admitted Triple/Effects bundles. It found no
soundness or correspondence blocker and confirmed those two equal rows.
Safe-integer operands are the paper's ambient domain; Mask permits negative
and large first operands. Freshness follows from existing command binding
scope and preserves current operand readings; aliases between inputs remain
allowed. The generic computed predicate reads entry state. No arbitrary
semantic predicate or raw signed-zero equality is transported.

Complete assertion admission and the old finite certificate coverage remain
separate. Shr's signed/count generality and Shl remain open, including the
paper's integer-constant count domain beyond SafeInt. No full Fun or complete
alignment is claimed. The independent next graph-layout design/prototype is
not counted as implemented code in this source.

Logs: `/workspace/scratch/bitwise-test.log`, `bitwise-axioms.log`,
`bitwise-rules-build4.log`, and `bitwise-docs-final.log`.

## Operational graph/control foundations at 1fc40c5e

Evidence applies to exact source `1fc40c5e41873c227d977bab594034a8033614bf`,
extending `1e0016aff64de23e3b977badf25f02602728b3ba` on single-pass
`f2e33e7f35769d00dd6aa1763d86d3c6ef41983f`. A fresh fetch before validation
confirmed that exact base was still the remote tip. The original fetched start
remains `ba681dfdab8ab41c7d73f3c573f449ab90fedab7`.

All five modules pass focused builds with warnings as errors. Both complete
axiom audits pass, exit zero, 441 jobs, with only the same eight cached upstream
informational backtraces. Full make test exits zero: 650 Lean build jobs,
23 passing fast suites, 175 controls (3 operations executed, 492 replayed),
3431/3431 expected cases, 4323 verified functions, 1790 negative controls and
150 named gaps. Direct import coverage checks 363 other A/shared and 75 other
Paper modules. A separate scan finds zero outside-to-Paper imports. This batch
changes no A/shared Lean or paper mathematics; the preceding shared-impact
account remains exact. Final documentation passes at 79 documents, 892 code
citations and zero problems; whitespace checks pass.

Independent read-only Astra reviewed the layout/control design before
implementation and all source afterward. It found no soundness blocker.
It specifically checked finite bounds include bind/catch IDs; slot-map defaults
remain machine values; host/payload slots are not silently required to meet
program-root validity; restoring source/world validity has the correct finite
slot and persistence premises; graph inversion retains every real step/count;
evaluation segments expose genuine values/raises; and finite control traces
produce existing structured execution with exact primitive weight. Handlers
use the thrown-time environment and pop before their own execution. Operational
control carries no worlds, marks or entry anchors.

The 91-row table remains 42 equal, 26 narrower, 10 absent and 13 assumed.
These proofs are operational prerequisites: generated finite graphs, their
metadata/offset/routing proofs, whole-command inversion and Fun are not yet
implemented by this source. In particular, zero-weight administrative control
alone supplies no termination argument. The reviewed next CPS prototype exists
only in scratch and is not counted as formalized compiler correctness.

Logs: `/workspace/scratch/graph-foundations-test.log`,
`graph-foundations-axioms.log`, `graph-layout-inversion-build1.log` (layout),
`graph-inversion-build3.log`, `command-machine-build3.log`,
`graph-segments-build1.log` and `graph-foundations-docs-final.log`.


## Third owner-requested rebase, onto 5777ed2e

The owner requested another rebase after new single-pass changes. Fetching
recorded exact remote tip `5777ed2e08992863611715aa38f21b97f10145d5`, adding
`d970a4e3` (bounded universal notation) and `5777ed2e` (unified length) above
`f2e33e7f35769d00dd6aa1763d86d3c6ef41983f`. The 24 implementation/record
commits rebased without conflicts; all seven pending compiler source files
were stashed and restored intact. The original exact fetched start remains
`ba681dfdab8ab41c7d73f3c573f449ab90fedab7`. No owner paper/PDF changes were
reverted or edited. Rewritten commit mapping:

- `26d0fbd2c264bf97b34a9203cb98fb9ef3bf130f` → `ac2533b8332450e57c35db48bb8e46ea28f43a08`: State semantic support and respect at the paper's generality.
- `0e0d4113e18dcda0b219d8cb8548240478a832a6` → `cb5565c22a5f2fe56b7f4a6af57413e34e1acf56`: Interpret general paper assertions and quantified consequences.
- `c5dfad3867728aec83c0537e1c46a769687c9a6c` → `13b4cecfc6ed92ead97159c4af0f55d13f74b709`: Prove general command rules and regional checked transfer.
- `1c5a117d9e84336b1cec0259d5333315999bc85b` → `093f111edc465a31d8e4a88257d527bdb81a841b`: Record final Paper proof, regression and correspondence validation.
- `9065f4535d24cd15f5042e9764b0519de5014351` → `00c4b4b35a653a6bef7b3da9b73ccd4cfb8e3b95`: Prove capture-avoiding assertion transport and full quantified rules.
- `4f99c4ab08f26552989361987f1e7205f671ecac` → `e3d0aaaacab1853eb8b88b288a1b3ddf57675553`: Record full validation of the assertion transport continuation.
- `7a6c41b524e4b08a1e0c6f51b76178a2044c9a74` → `71cc41283ab6390efab93989f6ef361a7d0272c3`: Prove general all support, witness rules and integer consequence.
- `b029933092b487ac695c79762502fdd7191edbb3` → `8c8048b29ea470e58242d6076ac61e163151826e`: Record validation and the numeric equality obstruction.
- `6b2df2341132bd4ab8e54509b3c837d9442fbafb` → `41c5cb107df7389959b76503a1ce258a00aa0de1`: Formalise first-order two-state postconditions and their transport.
- `a6a692473432e8b2412b22483d3e6652eaf6d4b7` → `6aee3ee7c6d05884ebe80beb11fd9c71a554372c`: Record validation of first-order postcondition proofs.
- `b907a21a5fff67b20e1f8a7905dfd7073026073a` → `78ee65e9d7c40295d50f7e1ea0619fc9a1596578`: Correct the zero bridge and prove conditional path supports.
- `2a1c50d28dfddfd0bca2a8cc8d2b608522b0fdd1` → `2d48f60aed43b4204de41993e0d3b93213d64e6f`: Record validation of the corrected literal and path support proofs.
- `c735b67546c32b6333acc75444a469aefe6ca40a` → `942b50883ac0d0c73f79afe3ed096f88bbc50b34`: Make logical witnesses heap-based and prove structural supports.
- `47af13f28534ff27e11ffa0b41fa30d2542b718d` → `bd26c84229721a9f60001361b792fc1496da38d5`: Record rebased quantifier and support validation.
- `a082e3d8b0765b69fe607b46fa10a4e2ee0a2859` → `f2147af42f02ae90362b369f2a5a9449cb3aa0a6`: Prove scoped Call instantiation on actual executions.
- `e88e2d9e2d7d8980a5afa2c6d8b94c2fa6a52f08` → `e66d3bf7b0e9ec780c3a06a7bf91d2fe8b0e6374`: Record exact scoped Call validation and review.
- `b703b5de9b7a1c3f67d96ff4972ca43fcf7fca33` → `12d952d4f24421d513fbf95c219842ed723cd7c9`: Observe raw completions and prove scoped budget transport.
- `7fcd1a5c1266b2add64e3956fddf56af416e4c8c` → `73cc9f4fc553cf31f60e3c7e8ce92b61f833ba08`: Record raw execution and budget proof validation.
- `69d3e9acc3646d31e8304897e50d4ff4b5960434` → `876d9f67a38d969cf52d07b5a90974a97e538853`: Compile fixed primitive terms with a conservative own-key test.
- `7dcd069f6f306430400b1e1c76a998fcef633ad6` → `2f329a34c0306a72c5743a176f7a9e1121cbad86`: Record latest-rebase primitive code and shared regression evidence.
- `38b317059e56dd0dc9f155dcceca7f8f8d7c2e48` → `c55a28d13f6c6e6926fcbdbf8a5bda8a2e68d050`: Prove general Mask and Or on actual arithmetic commands.
- `1e0016aff64de23e3b977badf25f02602728b3ba` → `cdb61b7406b08fc438dee65422d46229ec76927c`: Record complete Mask and Or command validation.
- `1fc40c5e41873c227d977bab594034a8033614bf` → `fd3857298cc866d871ab255c94cb4f13553657a3`: Prove finite graph frames and structured command trace inversion.
- `2583b0ea628ea3c53fc762ec998256c5fc3b6ede` → `0f3d1ba9aaad4a5a2aaa5b49b2ddb21ca6e139d6`: Record exact graph and control foundation validation.

The committed Lean tree is byte-for-byte identical to pre-rebase
`2583b0ea628ea3c53fc762ec998256c5fc3b6ede` (git diff --quiet for lean passed).
The documentation check passes: 79 documents, 892 code citations, zero problems;
whitespace checks pass. Earlier full regressions stay attached to their exact
sources/bases above, not claimed reruns of this newer paper. Pending generated
compiler/local simulation files remain uncommitted and need their own full
validation after completion. No merge is performed.

Independent Astra reread the actual paper diff and identified substantive
unified-length obligations: mixed array/view/string paths, empty-suffix element
lengths, support by declared sort and the explicit collection restriction of
Empty. Receiver independence from the quantifier bound was already represented.
Inst/Prefix/Empty and their excluded summary are conservatively narrower until
that grammar/transport is supplied. Explicitly sorted arithmetic/string/view
rules retain their mathematical content, with notation translation pending;
general semantic arbitrary-assertion theorems are unchanged. The full recount
is 91 rows: 39 equal, 29 narrower, 10 absent and 13 assumed. This reclassification
records new scope, not a closed gap.

Two precise owner questions are pending: the mixed number[]|string support
contains a declared-ill-formed spine region, and an element-free bounded body
has no identified implicit receiver. The correspondence obligations state the
smallest static/interpretation obstructions. Neither the paper nor B's region
admission or quantifier meaning is silently changed. Independent command-graph
work continues. Full alignment remains incomplete.

## Generated-command compiler at 1883afc1

Evidence applies to exact source `1883afc1d92222312f60a80abb2d6534aee48d42`,
extending `158878e222cf32f357142d03fcc91463f0c04380` on current single-pass base
`5777ed2e08992863611715aa38f21b97f10145d5`. The original fetched start remains
`ba681dfdab8ab41c7d73f3c573f449ab90fedab7`.

All ten generated-compiler modules pass focused builds with warnings as errors.
Both complete axiom audits pass, exit zero, 451 jobs, with only the same eight
cached upstream informational backtraces. Full make test exits zero on the
newer paper/base:

- 660 Lean build jobs;
- all 23 fast suites and 175 controls (3 operations executed, 492 replayed);
- 3431/3431 cases as expected;
- 4323 verified functions, 1790 negative controls and 150 named gaps.

Direct import coverage checks 363 other A/shared and 85 other Paper modules.
An independent source scan finds zero outside-to-Paper imports. All new source
is in Paper; preceding task-authored shared changes remain exactly as already
recorded. Paper mathematics/PDF are untouched by this implementation. Final
docs pass at 79 documents, 892 code citations and zero problems; whitespace
checks pass. The latest-paper recount remains 91 rows: 39 equal, 29 narrower,
10 absent and 13 assumed.

Independent read-only Astra reviewed the design and complete source chain:
concrete finite offsets and front normalization, structural Origin/Routes
generation, real mapped environments, actual primitive/control/throw evaluation,
full sink expressions, terminal environment retention, and shared-count whole
inversion. It found no blocker. The theorem derives all compiler/routing evidence
internally for every finite raw command. Actual shared value/raise Steps yield
existing structured Executes with the same heap/exit, recovered final environment
and primitive p≤N. Enter/leave overhead strictly decreases the suffix count,
including around zero-weight B loops. This is not a supplied body summary.

The result is completed-run inversion under explicit machine-value representability
of the three host values. It does not prove forward simulation, progress,
callable argument/capture entry, physical-budget postcondition transfer, Fun,
rest allocation or full typing/admission. Standalone break remains distinct
although its graph sink returns undefined; function premises must exclude it.
A separate source inspection confirmed that ordinary lookup does not represent
literal-array push or scalar string native execution. Explicit resolved native
callees and availability/safety contracts are the next representation repair;
a vacuous partial Triple is not claimed to supply that missing execution.
Unified length and the four pending owner mathematical/interpretation decisions
remain as recorded. Full alignment is incomplete.

Logs: `/workspace/scratch/compiler-test.log`, `compiler-axioms.log`,
`compiler-correctness-build3.log`, `compiler-node-build2.log`,
`compiler-origins-build2.log`, `compiler-routes-build3.log`,
`compiler-control-build4.log` (first control cases), `compiler-sinks-build2.log`
(control completion), and `compiler-docs-final.log`.


## Fourth owner-requested rebase, onto 65d5bf91

A fetch in the cloud checkout recorded exact latest single-pass
`65d5bf9136f4afab47bb76db447f74d400a136f3`, containing 21 upstream commits
above the preceding base `5777ed2e08992863611715aa38f21b97f10145d5`. The
pre-rebase task and remote tip was `dc8b08a3cf68f6a026829d31ad65c3483d2f63ba`.
All 27 task commits replayed; only the two correspondence documents needed
conflict resolution. Their arithmetic/string/view rows were then reconciled
against the new shared rule datum and the actual paper, preserving the task's
postcondition interpretation evidence. The task does not modify the owner's
paper source or PDF relative to this base.

The exact replay mapping is:

- `ac2533b8332450e57c35db48bb8e46ea28f43a08` → `0d2e17bc3a722ff2a63821c449b730f752a1f949`: State semantic support and respect at the paper's generality.
- `cb5565c22a5f2fe56b7f4a6af57413e34e1acf56` → `89d9796a9c99ab5c99cbdff7e6b720fda5d4a6dc`: Interpret general paper assertions and quantified consequences.
- `13b4cecfc6ed92ead97159c4af0f55d13f74b709` → `77c125d547fe6066f5a6233d02f4ae2689f44c82`: Prove general command rules and regional checked transfer.
- `093f111edc465a31d8e4a88257d527bdb81a841b` → `05799b5bb3c6cdf4aafdc38e5519dfbc6bdfcc41`: Record final Paper proof, regression and correspondence validation.
- `00c4b4b35a653a6bef7b3da9b73ccd4cfb8e3b95` → `38cb22290e0563291bfa61f197ef088915030e84`: Prove capture-avoiding assertion transport and full quantified rules.
- `e3d0aaaacab1853eb8b88b288a1b3ddf57675553` → `1ab330fa2b5896aea859208582650cc02fe236a5`: Record full validation of the assertion transport continuation.
- `71cc41283ab6390efab93989f6ef361a7d0272c3` → `aa7c549875a307011d4338b6f8ba760fbf78eed2`: Prove general all support, witness rules and integer consequence.
- `8c8048b29ea470e58242d6076ac61e163151826e` → `eaaccdd44736c8f582e6920058437f7b006b119c`: Record validation and the numeric equality obstruction.
- `41c5cb107df7389959b76503a1ce258a00aa0de1` → `16d27f724e457dccb28b0af1b6d6ff61604c1b4c`: Formalise first-order two-state postconditions and their transport.
- `6aee3ee7c6d05884ebe80beb11fd9c71a554372c` → `02223e86b0c08d9b94a9a0f28ef99173bd61bf69`: Record validation of first-order postcondition proofs.
- `78ee65e9d7c40295d50f7e1ea0619fc9a1596578` → `49b179315ddb08c027747d4ae9ee61dadaa7cfa0`: Correct the zero bridge and prove conditional path supports.
- `2d48f60aed43b4204de41993e0d3b93213d64e6f` → `3437b00e419a0e6d75942fbff6476b8a699b8099`: Record validation of the corrected literal and path support proofs.
- `942b50883ac0d0c73f79afe3ed096f88bbc50b34` → `7d8c219ebca0617e7fd73630d2f61e944f9d3659`: Make logical witnesses heap-based and prove structural supports.
- `bd26c84229721a9f60001361b792fc1496da38d5` → `033ab1dc5a9fd5f66a61b611fb4f8fb8c3c9a53e`: Record rebased quantifier and support validation.
- `f2147af42f02ae90362b369f2a5a9449cb3aa0a6` → `4b84650fe2983bf5d476088cb071be1fd9068972`: Prove scoped Call instantiation on actual executions.
- `e66d3bf7b0e9ec780c3a06a7bf91d2fe8b0e6374` → `27dc6c237d0562b8d292ee555d7c062d85f90213`: Record exact scoped Call validation and review.
- `12d952d4f24421d513fbf95c219842ed723cd7c9` → `ee8155094fbc52ec5b74e01820622a7dba64ec95`: Observe raw completions and prove scoped budget transport.
- `73cc9f4fc553cf31f60e3c7e8ce92b61f833ba08` → `4b47f52e71931b376413ecb9430a856718427c49`: Record raw execution and budget proof validation.
- `876d9f67a38d969cf52d07b5a90974a97e538853` → `6a7fb62b97fbadb7ea1c0d6490540d8bfc047af5`: Compile fixed primitive terms with a conservative own-key test.
- `2f329a34c0306a72c5743a176f7a9e1121cbad86` → `19de341fd8243b1977f3bd7d88da8a05ef0db8f8`: Record latest-rebase primitive code and shared regression evidence.
- `c55a28d13f6c6e6926fcbdbf8a5bda8a2e68d050` → `e47694384c75018275212226745f16213ccf585f`: Prove general Mask and Or on actual arithmetic commands.
- `cdb61b7406b08fc438dee65422d46229ec76927c` → `f97322756a29f30bc65a0b08102620ac948d39c7`: Record complete Mask and Or command validation.
- `fd3857298cc866d871ab255c94cb4f13553657a3` → `ab77913300421c6bb26569e00da42d6f103384d4`: Prove finite graph frames and structured command trace inversion.
- `0f3d1ba9aaad4a5a2aaa5b49b2ddb21ca6e139d6` → `6cb9414b2f40a99463c09f40751a29c07cdcabdb`: Record exact graph and control foundation validation.
- `158878e222cf32f357142d03fcc91463f0c04380` → `6dc6de14dd1984730fd5b1739e2fbec4bdcd506a`: Rebase onto the latest unified-length paper and reconcile its scope.
- `1883afc1d92222312f60a80abb2d6534aee48d42` → `8bf2b0171bd74251813cfba8a9b61396e43450e0`: Generate finite command graphs and invert their actual shared runs.
- `dc8b08a3cf68f6a026829d31ad65c3483d2f63ba` → `6185a24a14a94a7bf9761b2574d8b091b6e4f451`: Record generated compiler validation and exact remaining boundaries.

The upstream shared arithmetic reorganisation removes `toInt32_safe_nonneg`
and `bitAnd_safe`. The task's `BitwiseArithmetic` now imports `ArithmeticRules`,
uses `toInt32_small` at the same bounded conversion premises, and proves the
small nonnegative-input mask corollary with `intAnd_le_left`. Its theorem
statements are unchanged. Focused `BitwiseRules` passes (103 jobs); documentation
passes (81 documents, 894 code citations, zero problems). The first axiom build
failed on the removed references and is not passing evidence. A cache setup
file collision during that failed build also required a sequential rebuild.

Astra's independent read-only review found no blocker in the repaired proofs
and checked the latest rule correspondences. Signed Shr and Shl are equal:
the paper now explicitly requires SafeInt shift constants, with counts modulo
32. Both Mask rows allow arbitrary numeric first operands and a variable
safe-integer mask; its second row bounds by the nonnegative mask, without a
small-mask bound. The shared Concat theorem has the paper's empty logical
precondition for string operands; the older finite certificate's additional
nonnegative-length premises do not narrow that shared theorem. The exact
91-row recount is 41 equal, 28 narrower, 9 absent, 13 assumed. Unified-length
syntax transport remains separate.

The complete sequential `make test` on this compatibility repair and exact
base 65d5bf91 exits zero: 664 Lean jobs, including both complete axiom audits;
24 fast suites, zero failures; all 175 controls (460 operations executed,
35 replayed); 3438/3438 expected cases, 4332 verified functions, 1792 negative
controls and 149 named gaps. No test expectation was changed by this task.
The direct-import check covers 365 other A/shared modules and 85 other Paper
modules. A separate outside-to-Paper scan finds zero imports. Documentation
passes at 81 documents and 894 citations, with zero problems; whitespace
checks pass. These results apply to this combination on 65d5bf91, not later
owner changes. The run log is `fourth-rebase-test.log` in cloud scratch. Its
successful exit was observed; older runs are separate evidence.


## Fifth owner-requested rebase, onto fbc7078c

The remote advanced during the fourth rebase's full regression. Fetching
recorded latest single-pass `fbc7078c22426e2ccc42938cce8e4a33bf903f4f`,
11 commits above 65d5bf91: the SafeInt type clause and source interpretation,
explicit generated library-contract data, and clarified safe-number wording.
The fourth compatibility source/validation commit is
`c17ff993b64773469acb66d4bea3633c122c81a1`. All 28 task commits replayed onto
this base; the resulting source is `933ef9ef5573f6a369886fca0f64f615dc8244c8`.
Only the audit document conflicted. No task Paper source changes in this
rebase, and the task's paper source/PDF diff relative to the owner base is
empty. The only task-authored shared files remain the five own-key-test,
normalization/shape/codec and decoder-control files documented above. Owner
SafeInt changes belong to the base, not to the task's shared extension.

Exact replay mapping:

- `0d2e17bc3a722ff2a63821c449b730f752a1f949` → `ee30180d015f6041f643d96388c5658361389ddf`: State semantic support and respect at the paper's generality.
- `89d9796a9c99ab5c99cbdff7e6b720fda5d4a6dc` → `33c326e09081dbf44eb996d38920d0ea1f7f58ac`: Interpret general paper assertions and quantified consequences.
- `77c125d547fe6066f5a6233d02f4ae2689f44c82` → `d2d1555eae70316485f5cbcee588150b16b36e2c`: Prove general command rules and regional checked transfer.
- `05799b5bb3c6cdf4aafdc38e5519dfbc6bdfcc41` → `df5e79b8cf688551a987867d88648e2bd215dad3`: Record final Paper proof, regression and correspondence validation.
- `38cb22290e0563291bfa61f197ef088915030e84` → `02b2fb6f48f6d3f3498d1fab1234dd2673cfe278`: Prove capture-avoiding assertion transport and full quantified rules.
- `1ab330fa2b5896aea859208582650cc02fe236a5` → `a3dded8f3416b544fd781a9ad584af4383d27176`: Record full validation of the assertion transport continuation.
- `aa7c549875a307011d4338b6f8ba760fbf78eed2` → `f37eae805e2820497c4f2e66784f3ff09d2e6e49`: Prove general all support, witness rules and integer consequence.
- `eaaccdd44736c8f582e6920058437f7b006b119c` → `e0e14ff210fb63bd739067ae4bbdf758aea03128`: Record validation and the numeric equality obstruction.
- `16d27f724e457dccb28b0af1b6d6ff61604c1b4c` → `f0c87ed4151c9a726c2dc7d755dda9c137df2246`: Formalise first-order two-state postconditions and their transport.
- `02223e86b0c08d9b94a9a0f28ef99173bd61bf69` → `5ff4e2fbe9b8c617abd0f2f4bb79b6d229cca633`: Record validation of first-order postcondition proofs.
- `49b179315ddb08c027747d4ae9ee61dadaa7cfa0` → `300f6f1808b5570ecc5969c4217ee73bd0416fad`: Correct the zero bridge and prove conditional path supports.
- `3437b00e419a0e6d75942fbff6476b8a699b8099` → `ec1d83f1cd05c1f84c74043d6f5615bb58801667`: Record validation of the corrected literal and path support proofs.
- `7d8c219ebca0617e7fd73630d2f61e944f9d3659` → `a4ca0ae52caead06a256cf8531ec0d7241633e9b`: Make logical witnesses heap-based and prove structural supports.
- `033ab1dc5a9fd5f66a61b611fb4f8fb8c3c9a53e` → `f8b2ab91347799c91c1582d8a09b3166a33546f9`: Record rebased quantifier and support validation.
- `4b84650fe2983bf5d476088cb071be1fd9068972` → `7ccbc4069b31544f1ffeb4964a77407bd9cf0d99`: Prove scoped Call instantiation on actual executions.
- `27dc6c237d0562b8d292ee555d7c062d85f90213` → `1f5ee75fc1ab30956a6296d1344e67480958ef7e`: Record exact scoped Call validation and review.
- `ee8155094fbc52ec5b74e01820622a7dba64ec95` → `8a142c3f5c9321da5765dda14479997bf259f216`: Observe raw completions and prove scoped budget transport.
- `4b47f52e71931b376413ecb9430a856718427c49` → `ad678f1f3d9949d9525d766483ff4d1ddbc000cc`: Record raw execution and budget proof validation.
- `6a7fb62b97fbadb7ea1c0d6490540d8bfc047af5` → `0d0222052872b4c923788926f5c3c4a66969dbcf`: Compile fixed primitive terms with a conservative own-key test.
- `19de341fd8243b1977f3bd7d88da8a05ef0db8f8` → `f02d1841baec530c7f14a8fa4586eca42478c998`: Record latest-rebase primitive code and shared regression evidence.
- `e47694384c75018275212226745f16213ccf585f` → `26be9281be420ec81cf16368a7c16d495adc90bf`: Prove general Mask and Or on actual arithmetic commands.
- `f97322756a29f30bc65a0b08102620ac948d39c7` → `6689de8003a2d7db3c03c4ba1074d425f17e4e61`: Record complete Mask and Or command validation.
- `ab77913300421c6bb26569e00da42d6f103384d4` → `ea9b580832d842defc04726f76f77a510a1643a4`: Prove finite graph frames and structured command trace inversion.
- `6cb9414b2f40a99463c09f40751a29c07cdcabdb` → `ba994593b7e1d043df180c975667a60a9fdee12a`: Record exact graph and control foundation validation.
- `6dc6de14dd1984730fd5b1739e2fbec4bdcd506a` → `e8928b1aea06fefd665b1dd04596a8da3c268f54`: Rebase onto the latest unified-length paper and reconcile its scope.
- `8bf2b0171bd74251813cfba8a9b61396e43450e0` → `0f7d898dd1d02384ccf9fe00eda33ce9c7382bcf`: Generate finite command graphs and invert their actual shared runs.
- `6185a24a14a94a7bf9761b2574d8b091b6e4f451` → `6da05c4f4601b32d297ae37c2355003530fafa4f`: Record generated compiler validation and exact remaining boundaries.
- `c17ff993b64773469acb66d4bea3633c122c81a1` → `933ef9ef5573f6a369886fca0f64f615dc8244c8`: Rebase over the shared arithmetic datum and preserve bitwise corollaries.

Astra independently compared the new library data and paper formulas. All
13 host rows remain assumed: the data names contracts and records conclusions,
implication atoms, normal effects and allocation; `ArithRule.Sound` does not
prove those metadata fields or execute `.call`/`.construct`. Native callable
elaboration, receiver-compatible availability/safety and command-triple
instantiation remain distinct. The exceptional construction-at-2^53 row is
separate. The code-point threshold is the same integer predicate, and the
clarified interpretation of -0 does not override distinct raw-value equality.
No assertion/quantifier rule changed, so the exact counts remain 41 equal,
28 narrower, 9 absent, 13 assumed among 91 rows.

Validation measured on 2026-11-17 for source 933ef9ef: the full Lean build
passes all 664 jobs, including both complete A/Paper axiom audits. All 24 fast
suites and 176 controls pass (462 operations executed, 35 replayed). The
pipeline run covers 3448 cases; only an incomplete progress measurement had
been observed when this record was committed, so this is not an exit-zero
full-regression result. Documentation passes at 82 documents and 895 code
citations, zero problems. Direct imports cover 365 other A/shared and 85 other
Paper modules; the outside-to-Paper boundary count is zero. The complete
pipeline outcome is recorded separately when observed. The fourth-base full
run remains scoped to 65d5bf91.


### Completed case phase on the fifth base

The overall `make test` command on source 933ef9ef ended at its 1800-second
limit, exit 124, after reporting 3105/3448 cases; it is not an exit-zero full
`make test`. Its complete Lean build, both axiom audits, all 24 fast suites
and 176 controls had passed as recorded above. No expectation was changed.

The case phase alone was then rerun on the identical Lean/pipeline source
(the intervening 37593c01 commit changes documentation only), with completed
stages reused by content and a 900-second budget. Its observed exit is zero:
3448/3448 cases as expected, 4344 verified functions, 1799 negative controls,
149 named gaps. This completes the required case coverage without repeating
the successful fast suites. The exact commands and full outputs are retained
in cloud scratch as `fifth-rebase-test.log` and `fifth-rebase-cases.log`.
The whole required validation is covered by those two runs; a single exit-zero
`make test` on this source is not claimed.

## Canonical unified lengths at 1bbaf0a7

Evidence applies to exact source `1bbaf0a7433a3aaf9f3c9032d8304ada0b778915`,
on fetched single-pass base `fbc7078c22426e2ccc42938cce8e4a33bf903f4f`.
The original fetched start remains `ba681dfdab8ab41c7d73f3c573f449ab90fedab7`.
The source commit changes 26 files: 21 Paper Lean modules and five documents.
It adds LengthReading, PaperTermForms and LengthBridges; no module outside
Paper changes. The paper source/PDF diff relative to the owner base is empty.

Focused repository builds and both complete axiom audits pass, 456 jobs.
Every affected Paper module was also rebuilt in isolated outputs during source
review (67 affected modules, including the complete Paper audit). The final
repository run is the authoritative validation of the committed combination.

Full `make test`, with the pinned Lean/Node and a 1200-second budget, exits zero:

- 667 Lean jobs;
- all 24 fast suites, zero failures;
- all 176 controls, 3 operations executed and 494 replayed;
- 3448/3448 cases as expected;
- 4344 functions verified, 1799 negative controls, 149 named gaps.

Direct axiom-check imports cover 365 other A/shared modules and 88 other
Paper modules. A separate scan finds zero imports into Paper from outside it.
Docs pass: 83 documents, 895 code citations, zero problems. Whitespace and
semantic commit-record checks pass. No test expectation changed. No source
change followed those checks; final correspondence/status edits reran docs.

Independent Astra source review found no soundness blocker in the canonical
runtime dispatch, empty suffixes, both term phases, recursive definedness,
all-keep support, world independence, scopes/admission, selected replacement,
actual instantiation or qualified Option-result bridges. A follow-up review
checked `Derivation.canonicalLengthRange` and its direct soundness branch.
Canonical forms reuse the existing three readers and do not alter A's enum or
heap/world semantics. PaperTerms is a term-form predicate, not complete
admission. A qualified bridge assumes actual reads/category evidence and
preserves possible final undefinedness; it proves no declaration-to-category
judgment. Legacy sorted growth/exactness remains restricted to those forms.

Inst/Prefix's unified-length syntax gap is closed, but the audit retains
narrower for the unresolved element-free receiver interpretation. Empty also
needs the declared-collection-to-runtime-receiver bridge. The exact count
therefore remains 91 rows: 41 equal, 28 narrower, 9 absent, 13 assumed. Full
Definition 23 integration, mixed-state arithmetic/substitution and the exact
support table are not inferred from these new structural proofs.

## Actual fixed-arity callable entry at 4760a0f3

Evidence applies to exact source `4760a0f37340ef8ef08ffb0f475b3fa82c7e8c45`
on fetched single-pass `fbc7078c22426e2ccc42938cce8e4a33bf903f4f`. This batch
changes three new Paper modules, two existing Paper modules and four documents.
No shared/A module, expectation or paper mathematics changes. The original
start remains `ba681dfdab8ab41c7d73f3c573f449ab90fedab7`.

Focused builds of the finite layout, ambient inversion, adapter and completed
invocation proofs pass with warnings as errors. Both complete repository axiom
audits pass, 459 jobs. Complete `make test` exits zero within its 1200-second
budget:

- 670 Lean jobs;
- all 24 fast suites, zero failures;
- all 176 controls, 3 operations executed and 494 replayed;
- 3448/3448 cases as expected;
- 4344 functions verified, 1799 negative controls, 149 named gaps.

Direct imports cover 365 other A/shared modules and 91 other Paper modules.
No outside module imports Paper. Documentation passes at 83 documents and
895 code citations, zero problems; whitespace and semantic commit-record
checks pass. The axiom log replays the same eight informational upstream
TolerantFramesStepLink:294 backtraces recorded at the baseline; both audits
exit zero and no new-module warning/error occurs.

The cloud exec transport briefly disconnected after the full run. Runtime
status and a retry confirmed the same running workspace; the existing test
session subsequently returned exit zero and its complete results were read.
No test restart or source recovery was needed.

Astra independently designed and source-reviewed the fixed-arity foundation,
including finite source selectors, shared parameter padding, capture/self
indices, exact slot maps/default, generated-code lookup agreement, actual
three-step prefix and strict count decrease. It found no blocker. The
source selector list can retain unused logical inputs beyond frameBound;
restore preserves them. Both completed values and throws yield identical heap,
decoded named environment and structured body exit at N=3+q and p≤q<N.
Escaping break is retained as a distinct exit.

Raw inversion requires machine values. Entry ValidContext is separately proved
from actual valid receiver/arguments/self and selected program captures. Self
reference validity may include capture references; it is not a consequence of
machine representability. No callable type/contract membership or native
availability/safety is derived. Function allocation/typing, recursive proof
discharge, specifications and old/budget/mark transport, rest, spread and full
Fun remain separate. All 91 correspondence rows are retained with unchanged
counts: 41 equal, 28 narrower, 9 absent, 13 assumed.
