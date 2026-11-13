# Processing functions on demand

## The existing mechanism this extends

The [single pass](../SINGLE-PASS.md) owns checking a unit; [the front](../SINGLE-PASS-FRONT.md) owns its proposals; [the unit theorem](../SINGLE-PASS-THEOREM.md) owns acceptance, realization and linking; [the stage store](../STAGE-STORE.md) owns replay, input identification and publication. This design extends those mechanisms to a request for a set of functions.

The processing boundary is one function, including all its offered signatures, or one module initialization. Processing produces an interface and checks the body against it. Every consumer reads that interface through the same operation, within a file and across files.

**Evidence.** Code citations below describe the inspected worktree. `Claims/` abbreviates `lean/Verification/Source/Claims/`; `Lowering/` abbreviates `lean/Verification/Source/Lowering/`. The census counts and CPU totals are supplied measurements, not reproduced here. Statements about the proposed algorithm are design requirements; outstanding mathematical statements are labelled proof obligations.

## 1. The computation today

| Step | Actual computation and grain |
| --- | --- |
| Case | `runCase` calls `checkApart`; `pooled` admits one case per core. The worker pool belongs to `verify-source.mts` and retains TypeScript declaration sessions between checks. `pipeline/run-cases.mts:20`, `pipeline/run-cases.mts:33`, `pipeline/verify-source.mts:543`, `pipeline/verify-source.mts:651`. |
| Census | `runFile` calls `checkApart`, omits a located failing declaration and retries the file. Outer rounds enlarge the requested dependency closure and revisit files whose selection changes. `dev/census.mts:531`, `dev/census.mts:543`, `dev/census.mts:553`, `dev/census.mts:649`. |
| Selection | `units.select` reaches `checkUnowned`, but that function passes only `units.omitted` to parsing and calls `singlePass` with every parsed function. `singlePass` requests every name. Thus the census/pretext selection does not select the Lean work on this path. `pipeline/verify-source.mts:255`, `pipeline/verify-source.mts:265`, `pipeline/verify-source.mts:314`, `pipeline/verify-source.mts:338`; `dev/check-functions.mts:39`. |
| Parse | The runner snapshots the source, invokes the observed parse stage and checks the fragment’s source digest. Parsing has file grain, project resolution and recorded filesystem observations. `pipeline/verify-source.mts:193`, `pipeline/verify-source.mts:255`; `docs/STAGE-STORE.md:224`. |
| Interface discovery | `prepareInterfaces` invokes `--module-interface-plan`. `interfacePlan` discovers module dependencies and computes their SCC order. A reached module contributes all its function names and their import closure. `pipeline/module-interfaces.mts:62`; `Claims/ModuleInterfaces.lean:78`; `Claims/FragmentFront.lean:775`, `Claims/FragmentFront.lean:794`. |
| Interface computation | One `--module-interface` process receives a component’s complete module documents and predecessor results. `interfaceFile` decodes them and calls `establishModules`; its fold plans and checks each module once in component order. `pipeline/module-interfaces.mts:91`; `lean/Verification/Source/RequestCli.lean:248`; `Claims/FragmentFront.lean:1039`, `Claims/FragmentFront.lean:1104`. |
| Requested-file computation | `--verify-interface-stage 8` decodes interfaces, calls `fragmentPlansFromInterfaces`, prepares head facts and checks each selected group with `passGroupMode8`. `lean/Verification/Source/RequestCli.lean:307`, `lean/Verification/Source/RequestCli.lean:337`, `lean/Verification/Source/RequestCli.lean:359`. |
| Closure | The runner starts with accepted verdicts and propagates refusal through their dependencies. Missing module verdicts prevent closure; the current loop does not apply the same missing-verdict test to local identities. `pipeline/verify-source.mts:417`. |

A process stage is one explicit invocation with immutable input files and a replayable result. Its manifest contains stage name, adapter identity, executable and libraries, runner, runtime, arguments, environment, refusal protocol, input-role digests and output roles; its key is the digest of that manifest. Limits have separate timeout-observation semantics. `pipeline/stage-execution.mts:688`; `pipeline/stages.mts:188`, `pipeline/stages.mts:225`.

The `pass` key therefore includes the complete fragment and interfaces file, selection and file identity. A component key includes complete module documents and dependency results **and their stage keys**. An interface projection retains source digest, declarations, initialization and function bodies, and decoding demands equality with the importing fragment’s module document. Body changes consequently propagate even when callable contracts agree. `pipeline/stage-execution.mts:648`; `pipeline/module-interfaces.mts:99`; `Claims/ModuleInterfaces.lean:8`, `Claims/ModuleInterfaces.lean:38`.

### Units, types and reads

The front’s units are function declarations followed by initialization. Overloads have separate units sharing implementation code. Groups are SCCs of syntactic name mentions; a mention of an initialization-owned binding adds an edge to initialization. Selection chooses group leaders. `Claims/Extraction.lean:93`, `Claims/Extraction.lean:128`, `Claims/Extraction.lean:169`, `Claims/Extraction.lean:184`, `Claims/Extraction.lean:208`; `Claims/Json.lean:99`.

`fileFront` invokes `equationFront`, which lowers the file’s declarations and annotations through `EquationLowering.source`. `fragmentPlansCore` then computes declaration footprints, initialization types, selected plans and a frozen store. Extraction threads its growing equation store through the selected units. `Claims/Extraction.lean:263`; `Claims/Preparation.lean:230`; `Claims/FragmentFront.lean:682`; `Claims/Json.lean:106`.

A same-file call reads a module slot assembled by `ordinarySlots`: annotations, proposed footprint, throw bound, returned-callable footprint, stated freshness and regions. `withStandIns` installs proposals in both claims and slots. The proposal walk itself traverses other function bodies before their checks. `Claims/Extraction.lean:238`; `Claims/FragmentFront.lean:544`, `Claims/FragmentFront.lean:609`.

Extraction additionally receives the shared declaration store, generic descriptions, initialization-derived constants/cells, class information and ownership information computed over the file’s bodies. Head inference reads a local function’s `ensures` directly from `fr.units`. These accesses exceed a D1 interface lookup. `Claims/Extraction.lean:128`, `Claims/Extraction.lean:387`, `Claims/Extraction.lean:426`, `Claims/Extraction.lean:604`; `Claims/FragmentFront.lean:275`.

An imported callable uses the importer’s declaration type, reconstructed with the established footprint triple by `importedArrow`; captured types are compared with serialized interface rows by `refuseRows`. Eligibility also inspects the origin’s declaration and code for binding stability. `Claims/Extraction.lean:17`, `Claims/Extraction.lean:38`; `Claims/Imports.lean:208`; `Claims/FragmentFront.lean:829`.

The emitted `depends` is a projection of syntactic group edges and named qualified imports. It contains neither the declaration reads nor equation-row observations required for D3/D4. `Claims/Json.lean:131`.

### Repeated processing in one request

These are the identified repetition sites. A walk at different proposed facts or a different overload is distinct checking work; the table distinguishes it from duplicated orchestration.

| Site | Repetition |
| --- | --- |
| Requested and imported roles | A function checked in its own file can also be checked by an interface component. Their commands and inputs differ, so their results have different keys. `pipeline/stage-execution.mts:654`; `Claims/FragmentFront.lean:1066`. |
| Whole-file timeout | `checkAll` first runs the whole file, then runs one process per function name and initialization. Completed unit lines from the interrupted attempt are not individual store entries. `pipeline/module-interfaces.mts:144`. |
| Per-unit fallback preparation | Every fallback process repeats declaration lowering, initialization typing, reachable declaration-effect walks, extraction and freezing. A selected name still selects its entire SCC; selecting several names of one SCC repeats that group. `Claims/FragmentFront.lean:682`; `Claims/Json.lean:99`. |
| Ordinary-contract attempt | Controls and the performance gate use `verifyWithInterfaces`, which may check once with ordinary imports and again with established interfaces. The normal `verifyByUnits` path prepares interfaces first. `pipeline/module-interfaces.mts:135`, `pipeline/module-interfaces.mts:175`; `dev/perf-gate.mts:114`; `tests/single-pass-controls.mts:72`. |
| Census omission rounds | Each changed omission list reparses and rechecks the remaining file. `dev/census.mts:543`, `dev/census.mts:553`. |
| Census dependency rounds | Enlarging a file’s selected set invokes it again; current selection plumbing checks the whole parsed file. Exact stages may replay. `dev/census.mts:649`; `pipeline/verify-source.mts:314`. |
| Declaration proposal and body extraction | `declarationWalks` walks eligible bodies; `retypeFromFragment` walks them for extraction. Generic-call instantiation adds `instancesFromWalk` before retyping. `Claims/FragmentFront.lean:247`, `Claims/FragmentFront.lean:419`, `Claims/FragmentFront.lean:544`; `Claims/Extraction.lean:552`, `Claims/Extraction.lean:600`. |
| Initialization and returned callables | Initialization is typed before declaration effects and again afterwards; a returned-callable proposal used by initialization triggers another declaration-effect round. Initialization extraction also retypes its body. `Claims/FragmentFront.lean:710`, `Claims/FragmentFront.lean:719`, `Claims/FragmentFront.lean:724`; `Claims/Extraction.lean:600`. |
| Recursive effect proposals | A self-recursive declaration receives up to three proposal walks. This contradicts D5’s first-version policy. `Claims/FragmentFront.lean:587`. |
| Multiple signature/body checks | Each overload checks the implementation at its signature. Nested code bodies are checked within their containing member. These obligations remain, with shared preparation where possible. `Claims/Extraction.lean:93`; `Claims/Json.lean:349`. |
| Diagnostic/refinement runs | Head-candidate removal retries a member; regional fallback, comparison, repetition and observation can run additional checks. These are internal processing costs, counted separately. `Claims/FragmentFront.lean:1678`; `Claims/Json.lean:379`, `Claims/Json.lean:514`, `Claims/Json.lean:538`. |

Exact-key contenders already coordinate through store claims; multiple requests for the same existing stage do not imply multiple executions. `pipeline/stages.mts:198`, `pipeline/stages.mts:236`.

## 2. The interface

An interface is the complete callable contract a consumer reads, together with the contract’s type graph and binding identity. Its establishment is separate from its content.

The following inventory describes current reads. “Carried” distinguishes explicit entry fields from information reconstructed through declarations or contained in rows.

| Field or component | Origin and establishment | Cross-file representation today |
| --- | --- | --- |
| Binding identity | Module, declaration name and source span; binding stability is an extraction obligation. `Claims/Imports.lean:208`. | `module`, `name`, `namePos`, `unit`; complete origin document retained. `Claims/ModuleInterfaces.lean:18`. |
| Receiver, parameter types, result type | Written for declarations; inferred/contextual parts for literals. Body safety is `RequestSafe`; realization additionally requires matching frames/goals and `rowSpec_of_requestSafe`. `Lowering/Types.lean:803`; `Claims/PassUnitRealize.lean:392`. | Importer declarations reconstruct them; `interface` and `rows` carry their semantic graph. `Claims/Extraction.lean:38`; `Claims/InterfaceRows.lean:69`. |
| Fixed/rest signatures; extra-argument offers; overload conjunction | Derived from written parameters and code’s calling convention. Every offered row needs a realizing body check. `Lowering/Types.lean:803`; `Claims/Extraction.lean:106`; `Claims/FragmentFront.lean:930`. | Rows can represent signatures, but eligibility excludes rest and the importer accepts one plain signature plus an optional guard signature. `Claims/Imports.lean:225`; `Claims/Extraction.lean:17`. |
| Generic binders, kinds, bounds, resolution, signatures and widening policy | Declarations supply schemes; use sites compute instances. `Claims/TypeComparison.lean:41`; `Claims/Extraction.lean:564`. | Generic functions are ineligible for established reads; `layoutOwn` excludes schemes. `Claims/Imports.lean:225`; `Claims/FragmentFront.lean:948`. |
| `closed` footprint: value/store grades | Written or proposed by declaration/literal walks; the body’s footprint clause establishes it. `Claims/FragmentFront.lean:145`, `Claims/FragmentFront.lean:544`; `Claims/PassUnitRealize.lean:392`. | Explicit `footprint`, also present in arrow rows. `Claims/ModuleInterfaces.lean:26`. |
| `onThrow` | Written or inferred; the footprint guarantee covers exceptional return only when set. `Claims/Json.lean:364`; `Claims/PassUnitRealize.lean:407`. | Explicit `onThrow` and arrow effect. `Claims/ModuleInterfaces.lean:26`. |
| `fresh` | Written for ordinary declaration slots; literals may propose freshness. Own check includes freshness. `Claims/Extraction.lean:253`; `Claims/Json.lean:364`; `docs/SINGLE-PASS-FRONT.md:142`. | No explicit established field; `importedArrow` constructs its arrow with default freshness. Row agreement can consequently refuse a stronger origin signature. `Claims/Extraction.lean:38`; `Lowering/Types.lean:803`. |
| Returned callable’s footprint | Inferred, installed inside the result contract; checked by the function’s returns. `Claims/FragmentFront.lean:515`, `Claims/FragmentFront.lean:580`; `Claims/Extraction.lean:242`. | Explicit `resultFootprint`, reconstructed into the result and carried in rows. `Claims/ModuleInterfaces.lean:27`; `Claims/Extraction.lean:44`. |
| `pre` (`@requires`), `ensures` | Written. Calls establish preconditions; own returns establish postconditions. Realization requires the corresponding entry facts and postcondition positions. `Lowering/Types.lean:823`; `Claims/PassUnitRealize.lean:392`. | Reconstructed from declarations, checked for equality by eligibility, carried in rows. `Claims/Imports.lean:246`; `Claims/Extraction.lean:46`. |
| `promise`: guard/assertion kind, argument and promised type | Written promise, own body checked under its promise goal; interface has plain and promised rows. `Lowering/Types.lean:821`; `Claims/FragmentFront.lean:930`. | `importedSignatures` understands a guard pair, but eligibility excludes guards/promises. `Claims/Extraction.lean:17`; `Claims/Imports.lean:225`, `Claims/Imports.lean:244`. |
| `regions` | Written for declaration slots; request safety has a regional clause. Current row realization excludes relevant forms through its conditions. `Claims/Extraction.lean:249`; `Claims/FragmentFront.lean:980`; `docs/SINGLE-PASS-THEOREM.md:736`. | No explicit entry field; current reconstruction does not pass regions to `moduleArrow`. `Claims/Extraction.lean:46`. |
| Remaining effect fields: `receiverStore`, `receiverOwn`, `freshObject`, `requires`, `elements`, `receiverGrows`, `elementWrite` | Complete effect vocabulary used by callable types, including library contracts. Ordinary declaration arrows supply their specified defaults; several fields are excluded by current realization conditions. `lean/Verification/Semantics/CallEffects.lean:153`; `Lowering/Types.lean:823`; `Claims/FragmentFront.lean:980`. | Graph rows can carry these fields; the footprint triple cannot replace them. External contracts retain their existing trust boundary. `Claims/InterfaceRows.lean:69`; `Claims/PassUnitCross.lean:200`. |
| Captured values and module cells | Constants use initializer claims/annotations; cells use storage contracts. Their semantic availability is H5b, separate from callable-body safety. `Claims/TypeComparison.lean:12`; `Claims/Extraction.lean:330`; `Claims/PassUnitFile.lean:106`. | No established entry for a callable held in initialization: publication enumerates `functions`. `Claims/ModuleInterfaces.lean:22`. |
| Reachable type rows and built-ins | Type operands include their complete recursive contracts. Built-ins determine the exception family as well as prototype/unknown types. Store-map checks establish agreement. `Claims/InterfaceRows.lean:33`, `Claims/InterfaceRows.lean:42`; `Claims/PassUnitSignatures.lean:103`. | Module-wide `rows: {types, builtins}`; built-ins contain `proto`, `unknown`, `keys`. `Claims/InterfaceRows.lean:62`, `Claims/InterfaceRows.lean:89`. |

The new entry carries the whole callable type rather than a footprint triple plus importer reconstruction. Every signature retains every effect field. Scheme metadata needed by elaboration accompanies its semantic type and is included in its content identity.

A callable held in a constant has two obligations: its function unit establishes its callable contract; initialization establishes that the binding holds that value. An overload has one function identity, all its offered rows and all required row checks. Guard, scheme, rest and regional interfaces require the corresponding realization support; adding a serialization field alone does not establish them.

### A type graph per entry

Each entry owns a finite row table rooted at its complete callable type. The table includes the reachable rows, meet parts, scheme binders and bound binders, and built-in roots. This uses `rowRegion` and `encodeRowTable` at one entry’s roots. `Claims/InterfaceRows.lean:33`, `Claims/InterfaceRows.lean:42`, `Claims/InterfaceRows.lean:69`.

Publication decodes the exact bytes to be stored and checks the producer’s interface against that decoded graph. Consumption checks that graph against the consumer’s actual slot type. The same two checks apply within one file.

**Proved basis:** `signatureAgrees_of_checks` requires a realized source entry, empty graph environments, membership-preserving canonicalizers, and two successful `matchStores` results. It derives semantic agreement by composing store-map meaning equalities. `signatureAgrees_of_checks_back` permits the consumer check in the reverse direction. Canonical numbering alone supplies none of these premises. `Claims/PassUnitSignatures.lean:64`, `Claims/PassUnitSignatures.lean:82`.

Use entry-local deterministic numbering and deterministic operand ordering for content comparison. Preserve parameter/binder identity and every contract field. On reprocessing, first check the new producer interface against the previous serialized entry; an accepted publication check permits retaining that entry’s content identity with new provenance. This supports early cut-off despite different internal labels.

A failed equivalence check conservatively produces a new entry identity. The design promises cut-off for unchanged interface content; equivalence of arbitrary semantically equal recursive types is not assumed. Stable serialization and representative reuse need explicit edit tests.

## 3. Request, processing and store

A request supplies roots, project resolution, semantic options and any altered control inputs. Roots expand to stable function identities and initialization identities. Repeated roots share one request-owned task.

A function identity is its logical module and lexical binding identity. Overload rows belong to that identity. Source spans are diagnostic mappings; moving an unrelated declaration does not change identity or semantic input. Anonymous functions use lexical ownership and binding/structural identity, with ambiguity resolved conservatively.

Every result-affecting lookup goes through a recording interface:

- callable entry by binding identity;
- declaration or library contract by declaration identity;
- module binding/cell contract by binding identity;
- lexical resolution, including absent-name observations;
- file-derived semantic facts such as class metadata and ownership, by named projection.

A read records its query and the digest of the complete answer. It includes reads made while proposing effects, instantiating generics, lowering, searching and checking. A lookup of a type includes its required row closure. Negative answers are dependencies.

The file preparation result is an immutable index of syntax, bindings, declarations and independently addressable type components. It is keyed by the complete file preparation inputs and computed once per file snapshot. A unit depends on the projections it reads, not the index’s aggregate digest.

Declaration projections use logical declaration identities and entry-local rows, rather than file-global row numbers or absolute offsets. Recursive declaration components have a component content identity. An edit in such a component legitimately invalidates its readers.

Whole-file facts remain explicit projections. For example, a change affecting a module cell’s ownership can invalidate its readers even when their callable dependencies agree. The current all-body ownership computation supplies evidence that this dependency exists; it cannot disappear merely by making smaller keys. `Claims/Extraction.lean:387`.

Preparation errors attach to the affected projections or units. The current whole-file source gates and declaration lowering cannot remain a single fatal prerequisite for every unrelated unit. `Claims/Preparation.lean:230`.

### Key and result

The unit pre-key contains:

- stable unit identity and its own source/annotations/defaults, with locations normalized to the unit;
- verifier, lowering/adapter and runtime identities;
- all result-affecting options, including search budgets and forced proposals;
- explicit altered inputs for controls;
- the fixed execution context required for deterministic interpretation.

The final key is the digest of the pre-key and the recorded read answers. It contains dependency **interface content**, not dependency processing keys, bodies or verdicts. Publication provenance is stored separately.

A pre-key index holds candidate results. Replay validates every recorded query against the current request’s snapshot and entries, then validates the exact final manifest and payload. A missing or changed answer triggers processing. This extends the store’s existing observed-input mechanism. `docs/STAGE-STORE.md:224`.

A result contains the conditional check verdict, located refusal if any, interface entry or its located construction failure, recorded reads, producer/publication checks, and semantic input manifest. Attempt records contain CPU, elapsed time, peak memory and internal walk counts; timings do not affect interface identity.

A changed callee with an equal interface leaves the caller’s conditional result reusable. Its new verdict still participates in closure: changing an accepted body into a refused body removes verification from dependent results without rerunning their bodies.

### Demand and scheduling

When processing asks for another function’s interface, the scheduler resolves that function first. A ready interface can be consumed while its verdict is unresolved; the consumer’s check remains conditional. Final verification requires its own acceptance and successful closure of all source-unit dependencies.

The front resolves callable dependencies through these actual lookups before freezing the proposed interface. The checker consumes that frozen interface environment. Any additional lookup is recorded and resolved through the same mechanism; an implementation allowing late interface changes must invalidate affected suspended work.

Independent ready work runs across files, at most one executing unit per file and one executing worker per core. One task owns each unit/pre-key during a request. Waiting for a dependency occupies no execution slot or store lock.

On a demand cycle, unwritten interface components use their conservative values: unrestricted changes, unbounded throws, no freshness or returned-callable strengthening. Written contracts remain obligations. There is no recursive interface iteration.

The scheduler records these conservative cycle views separately from eventual entries. Their keys depend on the written contract and conservative-view policy; their establishment edges point to the corresponding body checks. This avoids recursively hashing verdict dependencies.

Cycle closure is the greatest dependency-closed subset of accepted units. A cycle verifies when every member passes, every outside dependency verifies and every consumed view is established. Extending linking across independently stored graphs on a cycle is a proof obligation; today’s cross-module theorem requires `ReadsEarlier`. `Claims/PassUnitCross.lean:184`.

### Workers and initialization

A file worker retains only immutable preparation and pure memoized functions of that preparation between unit results. Each unit has a fresh working equation store and search state.

Demand requires resumable processing. A suspended unit exports an explicit continuation containing its partial computation and reads to the request scheduler; the worker can then process another unit, including one in the same file. Resumption continues that computation. Continuations are request-local data, not reusable verdicts or hidden worker state.

This continuation protocol is necessary to combine D2, D4 and D7 without restarting a caller at each newly discovered dependency. A bounded pool also needs to unload idle file preparation and reload its immutable stored result when more files are live than cores.

Messages are declared data sums: load preparation, process/resume unit, need interface, supply interface, interface ready, complete result and resource failure. They carry request/attempt identities, manifests and content digests. Both decoders require the exact current shape and reject unknown fields; there is no version tag.

The scheduler charges execution time across a unit’s resumptions, excluding dependency wait. A limit kills its active worker, records only that unit’s resource observation and starts another worker for the remaining work. Completed results survive. Shared preparation failure is a file-preparation failure, not a fabricated unit timeout.

Initialization is one unit establishing exported values and cell contracts. Function reads name the relevant binding contracts and depend on initialization’s establishment. Function bodies held in constants have their own processing tasks; initialization checks allocation, capture and binding.

Separating nested function bodies from enclosing code-table checks requires a checked link from each closure construction to its function result, preserving capture types, defaults, offered rows and code identity. Until that link exists, nested checking remains part of the enclosing unit and D3 is only partially implemented for literals. Current extraction and checking construct and check nested code within the member. `Claims/Extraction.lean:449`, `Claims/Extraction.lean:489`; `Claims/Json.lean:349`.

## 4. Soundness and trust

**Proved today:** `passGroupMode8_safe` gives member safety from accepted group checking over one store. `mode8Accepted_sound` covers the exact two existing CLI acceptance paths. Neither directly states the proposed worker result’s acceptance condition. `Claims/PassUnitInferred.lean:317`; `Claims/PassUnitRun.lean:140`.

The new headline states: acceptance of a unit result implies exhaustive certification and `RequestSafe` for every body/signature obligation owned by that function. Its inputs are the precise recorded interface environment. This needs a restated acceptance predicate and a proof connecting the worker computation to the existing member theorem; the graph soundness theorem remains its basis.

Publication additionally establishes that the function value meets its exported interface under the contracts it reads. The reusable ingredients are `rowSpec_of_requestSafe`, realization, linking and the two store-map checks. The new theorem must cover the changed unit representation, independent stores, all offered rows and cycle views. `Claims/PassUnitRealize.lean:392`; `Claims/PassUnitFile.lean:118`; `Claims/PassUnitSignatures.lean:64`.

`layoutOwn` is an executable check of layout conditions, not a theorem equating that Boolean computation with all H5 premises. `ModuleLayout` also requires slot/value correspondence and separation. Initialization’s `init_asserted` establishes knowledge assertions at reached finish states; it does not discharge the full module-cell `KindMet` premise. These remain explicit boundaries unless separately proved. `Claims/FragmentFront.lean:930`; `Claims/PassUnitFile.lean:91`; `Claims/PassUnitInit.lean:23`.

Replay and result binding retain the stage store’s trust: a stored result is the identified execution’s exact result. Dynamic read completeness and projection independence are new implementation obligations within that trust boundary. Calling them “the same store” does not discharge them. `docs/STAGE-STORE.md:726`.

Closure verifies that every dependency exists, the consumed entry matches its establishment, and every source dependency closes. Declaration-only and host contracts are explicit trusted leaves. A source function with no established entry is a blocked source dependency, rather than an implicit trusted leaf.

The unsafe publication points are concrete: a proposal labelled established before its own check; a caller closed before its dependencies; a stale entry paired with a new verdict; an unrecorded declaration/ownership read; an omitted overload; an inferred cycle effect used as established; or rows accepted without their producer realization. Each needs a boundary control.

## 5. Replacement and coverage

The final runner removes component planning/publication stages, duplicated requested/imported file roles, whole-file pass fallback and census omission/retry orchestration. Cases, census, pretext, `make check` and controls submit root sets and compare results.

Parsing, TypeScript diagnostics, the content store, resource supervision, per-unit graph checking, row decoding and store-map checks remain. Store controls exercise storage directly. Internal head refinement remains part of processing, with separate counters.

The supplied census has 428/755 verified functions versus 596/755 on the old route, with 70 losses behind module-interface stages exceeding 300 seconds. Unit publication and resource isolation address that blocking mechanism. They do not imply 70 acceptances: individual checks, interface realization or downstream obligations may still fail.

Loop-fact losses require work in inference/checking. Imported guards, callable constants and overloads require the interface and realization work above. Scheduling alone does not provide their entries.

## 6. Cost and measures

Let the changed work be units whose own input changes or whose recorded interface answers change. Request CPU consists of changed file preparation, validation of reachable cached reads, processing those units, serialization/store-map checks and closure. A warm unchanged request performs validation and closure with zero body processing.

A body edit with an unchanged interface processes that function alone; changed file preparation and validation still occur. An interface edit processes its readers and propagates only where their interfaces change. Initialization edits invalidate readers of changed binding contracts.

The supplied stage CPU is 8,266 seconds for passes and 3,563 seconds for module interfaces: 11,829 seconds total, approximately 69.9% and 30.1%. The 30.1% is not an established saving: interface stages include necessary body checks, and pass stages include repeated preparation. The structural repetition table identifies opportunities, not their measured duration.

**Conjectured:** cold CPU decreases through shared preparation and elimination of repeated roles/fallbacks; wall time decreases where component timeouts dominate. No numeric wall-time prediction follows from the supplied totals. Scheduling is also bounded by the dependency critical path and sequential work within each file.

Gate on executed/replayed units, distinct processed identities, preparation executions, bytes/rows read, map-check CPU, proposal/check walks, resource failures and CPU/wall time. Separate replay validation from processing.

Required edit experiments: unchanged request executes zero units; unchanged-interface body edit executes one; unrelated same-file edit leaves other keys stable; declaration/interface change invalidates exactly its recorded readers; a diamond processes its shared dependency once; a killed unit preserves completed siblings; a cycle uses conservative views without iteration.

## 7. Useful implementation steps

| Step | Build and remove | Evidence of completion |
| --- | --- | --- |
| 1. Exact selection and accounting | Pass selected roots through; identify each preparation/walk/check by function. Keep existing execution routes. | Selected function plus one dependent, once; repetition totals explain existing stage CPU. |
| 2. One interface representation | Entry-local rows, complete callable contracts, same-file entry reads and producer/consumer checks. Remove direct footprint/`ensures` reads for migrated forms. Extend guards, constants, overloads and other callable forms with their realization obligations. | Moving a dependency across a file boundary preserves its contract and verdict for each supported form; forged rows/effects/omitted overloads refuse. D6 is complete only when every retained same-file form passes this gate. |
| 3. Unit results and recorded reads | Stable identities, named declaration projections, candidate replay and separate establishment closure. Remove whole-file result keys for migrated checks. | The edit experiments above pass; source failures do not become trusted leaves; the new acceptance theorem covers result emission. |
| 4. File workers | Immutable shared preparation, resumable demand, unit resource supervision and immediate publication. Remove whole-file timeout fallback and sequentially accumulated unit stores. | One preparation per loaded snapshot; one unit execution per input; killed-worker recovery preserves siblings; cold CPU and peak memory measured. |
| 5. One request mechanism | Route cases, census, pretext and controls through the scheduler. Remove component stages, duplicate file roles and census omission rounds. | Identical root sets have identical results/read manifests across clients; targeted timeout losses inspected individually; full suites pass. |

Every step keeps `make test` green. Boundary changes receive pipeline cases and forged-input controls; proof-covered facts need no duplicate tests. Full census comparison follows the project’s main-branch census policy.

## 8. Decisions

The owner's decisions on the questions this design raised:

1. **Acceptance target.** The redesign is judged by the same verdicts, every item processed once, much faster, and each change in a count explained. Reaching the old route's census count (596/755) is no criterion.
2. **Module initialization (H5b).** H5b stays a stated hypothesis; its typed-finish/world-extension proof is a separate obligation.
3. **Entries for functions held in module constants** are part of this redesign, in step 2 (one interface representation). Their design is [module constant entries](module-constant-entries.md).
4. **Recursion** is left out of the first version: on a demand cycle, the unwritten interface part is read at its conservative value (section 3, "Demand and scheduling"), unless a measurement shows the cost of that reading calls for more.
