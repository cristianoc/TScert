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
| Selection | `units.select` names the request's roots. `singlePass` passes the file's names among them as the pass's `<names>` (empty where they are every name) and as the per-unit fallback's names; the interface plan discovers the modules the roots' code reaches. The verifier checks the groups of the roots and of every unit their code reaches by name (`RequestCli.selectionClosure`). Parsing still has file grain: the whole file is parsed and lowered. `pipeline/verify-source.mts` (`singlePass`); `pipeline/module-interfaces.mts` (`verifyByUnits`); `lean/Verification/Source/RequestCli.lean` (`selectionClosure`, `verifyUnitsFile`). |
| Parse | The runner snapshots the source, invokes the observed parse stage and checks the fragment’s source digest. Parsing has file grain, project resolution and recorded filesystem observations. `pipeline/verify-source.mts:193`, `pipeline/verify-source.mts:255`; `docs/STAGE-STORE.md:224`. |
| Interface discovery | `prepareInterfaces` invokes `--module-interface-plan`. `interfacePlan` discovers module dependencies and computes their SCC order. A reached module contributes all its function names and their import closure. `pipeline/module-interfaces.mts:62`; `Claims/ModuleInterfaces.lean:78`; `Claims/FragmentFront.lean:775`, `Claims/FragmentFront.lean:794`. |
| Interface computation | One `--module-interface` process receives a component’s complete module documents and predecessor results. `interfaceFile` decodes them and calls `establishModules`; its fold plans and checks each module once in component order. `pipeline/module-interfaces.mts:91`; `lean/Verification/Source/RequestCli.lean:248`; `Claims/FragmentFront.lean:1039`, `Claims/FragmentFront.lean:1104`. |
| Requested-file computation | `--verify-interface-stage 8` decodes interfaces, calls `fragmentPlansFromInterfaces`, prepares head facts and checks each selected group with `passGroupMode8`. `lean/Verification/Source/RequestCli.lean:307`, `lean/Verification/Source/RequestCli.lean:337`, `lean/Verification/Source/RequestCli.lean:359`. |
| Closure | The runner starts with accepted verdicts and propagates refusal through their dependencies. A dependency with no verdict, of the file or of a module, prevents closure. `pipeline/verify-source.mts` (`singlePass`). |

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

These are the repetition sites, checked against the code (the citations of this table name the inspected worktree; the accounting below measures each). A walk at different proposed facts or a different overload is distinct checking work; the table distinguishes it from duplicated orchestration.

| Site | Repetition |
| --- | --- |
| Requested and imported roles | A module read by an importer is prepared again by its interface component: lowered, its initialization typed and every function's proposal walked (`fragmentPlansCore` over all its names, with closure). The component checks the groups `establishChecked` selects: the functions whose claims propose more than the ordinary effect, and the groups they reach; a function checked in its own file is checked again there. Their commands and inputs differ, so their results have different keys. At the parse level, an imported module is lowered by TypeScript in a stage of its own (`module`), apart from its own file's parse; that in-process stage takes no execution claim, so concurrent workers can execute one module key more than once. `pipeline/stage-execution.mts:654`; `Claims/FragmentFront.lean:850`, `Claims/FragmentFront.lean:1066`; `pipeline/parse-stage.mts:53`. |
| Whole-file timeout | `checkAll` first runs the whole file (the selection), then runs one process per name, one after the other. Completed unit lines from the interrupted attempt are not individual store entries. `pipeline/module-interfaces.mts:144`. |
| Per-unit fallback preparation | Every fallback process repeats declaration lowering, initialization typing, the declaration-effect walks of the name's reach, and freezing, and extracts and checks the name's closure. A name selects its entire SCC; the several names of one SCC each check that group. `Claims/FragmentFront.lean:682`; `Claims/Json.lean:99`. |
| Ordinary-contract attempt | Controls and the performance gate use `verifyWithInterfaces`, which may check once with ordinary imports and again with established interfaces. The normal `verifyByUnits` path prepares interfaces first, so cases, the census and the pretext tier have no such attempt. `pipeline/module-interfaces.mts:135`, `pipeline/module-interfaces.mts:175`; `dev/perf-gate.mts:114`; `tests/single-pass-controls.mts:72`. |
| Census omission rounds | Each changed omission list reparses and rechecks the remaining file. `dev/census.mts:543`, `dev/census.mts:553`. |
| Census dependency rounds | Enlarging a file’s selected set invokes it again. With the whole file checked for every selection, the second invocation replayed every stage; with exact selection, a larger selection is another pass key, and the units of the earlier selection are checked again. `dev/census.mts:649`; `pipeline/verify-source.mts` (`singlePass`). |
| Declaration proposal and body extraction | `PassProposals.proposals` runs each body's member with its footprint open; `retypeFromFragment` walks them for extraction. Generic-call instantiation adds `instancesFromWalk` before retyping. `Claims/FragmentFront.lean:247`, `Claims/FragmentFront.lean:419`, `Claims/FragmentFront.lean:544`; `Claims/Extraction.lean:552`, `Claims/Extraction.lean:600`. |
| Initialization and returned callables | Initialization is typed before declaration effects and again afterwards; a returned-callable proposal used by initialization triggers another declaration-effect round. Initialization extraction also retypes its body. `Claims/FragmentFront.lean:710`, `Claims/FragmentFront.lean:719`, `Claims/FragmentFront.lean:724`; `Claims/Extraction.lean:600`. |
| Recursive effect proposals | A self-recursive declaration receives up to three proposal walks, inside its own walk: the function is its own dependency, one unit of work (D5 keeps this). `Claims/FragmentFront.lean:587`. |
| Multiple signature/body checks | Each overload checks the implementation at its signature. Nested code bodies are checked within their containing member. These obligations remain, with shared preparation where possible. `Claims/Extraction.lean:93`; `Claims/Json.lean:349`. |
| Diagnostic/refinement runs | Head-candidate removal retries a member; regional fallback, comparison, repetition and observation can run additional checks. These are internal processing costs, counted separately. `Claims/FragmentFront.lean:1678`; `Claims/Json.lean:379`, `Claims/Json.lean:514`, `Claims/Json.lean:538`. |
| Settled run computed twice | `settleInferred` evaluates a member's last run twice: once as the scrutinee of `refusal (run f g)` and again as the result it returns, in both branches that end the runs. The compiled code applies the `run` closure twice to the same arguments; nothing shares the first result. Every member's final pass run is executed twice. `Claims/FragmentFront.lean` (`settleInferred`). |

Exact-key contenders of a process stage coordinate through store claims; multiple requests for the same existing process stage do not imply multiple executions. In-process stages (`parse`, `module`) take no claim. `pipeline/stages.mts` (`invokeProcess`, `invokeInProcess`).

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

On a demand cycle of two or more functions, a member's unwritten interface components use their conservative values: unrestricted changes, unbounded throws, no freshness or returned-callable strengthening. Written contracts remain obligations. There is no joint iteration over a cycle's members; the cycle verifies when every member's own check passes. A function that reads its own interface keeps the front's self-recursive proposal (its runs joined from keep/keep until they establish no more, `PassProposals.proposals`), which stays inside its one unit of work. A cycle is one of the front's name-mention relation (`Front.edgesOf`) until recorded reads replace it.

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

### Accounting

The instrument for "every item processed once" is the [work table](../SINGLE-PASS.md#work) of a profiled request (`TSCERT_PROFILE=<directory>`) and its report, `node dev/work-report.mts report <directory>`, a function of the directory alone. Profiling sets `TSCERT_PROFILE=1` in each verifier stage's environment and adds the output `work.jsonl`, so a profiled stage's key differs from the unprofiled one; an unprofiled request's keys and verdicts are those of a request with no accounting.

An item is a function, `<sha256 prefix of its source>#<unit>`, or a file, `<sha256 prefix>`, so one function has one item in every process of a request, in its own file's pass and in an importer's interface component alike. A unit is named by its lexical identity in the file (`Front.lexicalId`): its name, `init` for the initialization, and `<name>~<k>` for the `k`-th signature of an overloaded function, each signature its own obligation; the identity does not move when code elsewhere in the file does. A class of work is one of: a file's lowering (claims and declarations), its freezing (store and plans over it), its head facts, an importer's plans, the initialization typing, a function's extraction, a body walk (proposal, retype, instance), a check (group, member runs, main graph runs, diagnosing walks), an importer's or a publication's store-map check. The ideal is each class done once on each item per request.

Only executed attempts count; a replay is the result of an execution. An attempt's CPU time (the stage runner's user and system time) outside its recorded work (reading, decoding, encoding) is shared among its work in proportion to the recorded time. Work done more than once is attributed as follows.

- Across attempts, the occurrence in the item's own file's pass (else the first) is the processing. Another occurrence is site 1 when the two stages differ (a pass and an interface component, or two components); between two passes, site 5 when their fragments differ (another omission list), site 3 when their selections differ after a whole-file timeout, site 6 when their selections differ otherwise, site 4 when only their interface files differ.
- A whole-file pass over its limit is site 2, its CPU time whole.
- Within an attempt: the first body walk is the processing, a second proposal walk of the returned-callable round site 8, a recursive function's later walks site 9, the retype and instance walks site 7 (site 8 for the initialization's), each typing of the initialization after the first site 8. Inside one walk (`Synthesis.walkUnit`), each further traversal of the body is counted on the function as its own work and is site 13: a round at an evolving binding's grown contract, and the walk again with the rows a use offers (and its rounds).
- Within an attempt's check of a function: the first member run is the processing; each diagnosing walk and the rerun it leads to, and each main graph run beyond the member runs (a regional check beside a run), site 11; one more member run than the reruns is site 12, the settled run computed twice (`settleInferred`), at the mean member run's time.
- An overloaded function's signatures are distinct obligations, each its own item; a second check of the same signature is a repetition at the site its attempts give.

### Baseline

Measured 2026-11-13 on branch `on-demand` at the commit that adds exact selection, on a 12-core machine shared with other agents, each corpus on a fresh stage store, profiled (`TSCERT_PROFILE`), with `node dev/work-report.mts report`. Stage CPU is the user and system time of every executed stage attempt; a share is of that total. Profiling costs little: pretext's unprofiled stages took 61.9 s of CPU against 60.1 s profiled, by the two stores' measurements. The verdict lines of pretext and of the cases with projects are identical to those of the commit before this accounting (`dev/work-report.mts pretext` and `cases`, paths normalized).

| | pretext, 12 files of `src/` (ba09794f) | 722 pipeline cases with projects | census slice of tools/, shallow |
| --- | --- | --- | --- |
| load (1-minute average) at start, end | 4.7, 6.5 | 15.7, 24.8 | 13.0, 7.1 |
| wall time | 19 s | 98 s (86 s unprofiled) | 2,364 s |
| stage CPU | 70.2 s | 574.9 s | 7,389.9 s |
| work done more than once | 45.0 s, 64.1% | 61.5 s, 10.7% | 3,584.4 s, 48.5% |
| stages working on one function, max / mean | 2 / 1.74 | 1 / 1.00 | 85 / 2.54 |
| body traversals (walks and member runs) of one function, max / mean | 20 / 6.44 | 7 / 2.64 | 262 / 9.34 |
| functions and initializations worked on | 307 | 1,707 | 259 |

The census slice is declaration-graph.mts, fragment-parse.mts, fragment-statements.mts, fragment-expressions.mts (the four largest by lines) and namespace-members.mts, shadow-contracts.mts, every stage limited to 300 s: 122 of 213 units verified, 74 refused at a timeout. Its stages over their limit: 4 whole-file passes (1,178.1 s, site 2), 6 unit passes (1,754.4 s) and 4 interface components (1,100.0 s); the last two are work no repetition explains. Its parse and module stages took 212.1 s.

Work done more than once, by site (s, share of the corpus's stage CPU):

| Site | pretext | cases | census slice |
| --- | --- | --- | --- |
| 1 requested and imported roles: interface components | 13.0 (18.5%) | 0 | 7.3 (0.1%) |
| 1 requested and imported roles: module lowering beside the file's parse | 16.8 (24.0%) | 4.5 (0.8%) | 0 |
| 2 whole-file timeout | 0 | 0 | 1,178.1 (15.9%) |
| 3 per-unit fallback preparation | 0 | 0 | 1,417.1 (19.2%) |
| 4, 5, 6 ordinary attempt, omission and dependency rounds | 0 | 0 | 0 |
| 7 proposal walk and extraction walks | 1.8 (2.5%) | 12.1 (2.1%) | 158.5 (2.1%) |
| 8 initialization and returned callables | 0.3 (0.4%) | 1.4 (0.2%) | 24.6 (0.3%) |
| 9 recursive proposals | 0.0 | 0.5 (0.1%) | 0.9 (0.0%) |
| 11 diagnostic and refinement runs | 9.1 (13.0%) | 2.2 (0.4%) | 210.6 (2.9%) |
| 12 settled run computed twice | 4.0 (5.7%); 0 with the run shared, 2026-11-13 | 40.7 (7.1%); 0 with the run shared, 2026-11-13 | 587.4 (7.9%) |

With the settled run shared (`settleInferred` makes each run once, reads its refusal and returns it), measured 2026-11-13 on fresh stores, load at start 5.0 to 9.6, against the parent commit measured the same way: pretext's stage CPU 68.7 s → 60.4 s (pass stages 25.4 s → 21.2 s), the cases' 572.8 s → 545.7 s (pass stages 76.0 s → 57.8 s), the verdict lines identical. The performance gate's units, against the parent commit's verifier: every counter equal, CPU 9,549 ms → 8,736 ms in all.

Site 10 (overloads) is counted only where a function name has several checked units: none in these corpora. The census slice's omission rounds (two of fragment-parse.mts, one of declaration-graph.mts) answer refusals at the parse, before any pass, so they repeat parses alone, within the slice's 52.3 s of parse CPU; a shallow census has no dependency rounds. The functions with the most repeated work in the slice are initializations reached by every per-unit stage: fragment-parse.mts's (379.1 of 388.5 s, in 16 stages) and fragment-statements.mts's (178.6 of 184.2 s, in 62 stages).

### Edit experiments, today

- **pretext**, `isCollapsibleSpaceCode` of analysis.ts edited (two operands of `||` swapped: its type, effect and verdict unchanged), the request run again on its store: 41.0 s of stage CPU against 76.7 s cold (53%). Every file is parsed again (13 parses, 24 module lowerings: 29.2 s), since each parse observes the files its imports read; 3 passes execute (analysis.ts and the two files whose interfaces input changed, 59 units) and analysis.ts's interface component (8.2 s and 2.9 s). The verdicts are those of the unedited run.
- **tools/**, `collect` of fragment-statements.mts edited (one letter of an error message's text: its type, effect and verdict unchanged), the census slice run again on its store: 2,557.3 s of stage CPU against 7,389.9 s cold (35%), 1,502 s of wall time against 2,364 s. 95 functions are processed again: all 62 units of fragment-statements.mts and all 33 of fragment-expressions.mts, which imports it and whose pass reads the changed module document; 97 pass stages execute, among them the whole-file pass of each file over its limit again (598.4 s) and the per-unit fallback after it. 1,773.3 s of the 2,557.3 s (69.3%) is work done more than once. The verdicts are those of the unedited run.

The steps after this one must bring both experiments to one function processed (unchanged interface), its file's preparation and validation (section 6).

### Expected gains

"Every item processed once" removes the work done more than once. Bounds, from the baseline:

| | today | every item once | |
| --- | --- | --- | --- |
| census slice, stage CPU | 7,389.9 s | ≤ 3,805.5 s | −48.5% |
| pretext, stage CPU | 70.2 s | ≤ 25.2 s | −64.1% |
| cases with projects, stage CPU | 574.9 s | ≤ 513.4 s | −10.7% |
| census slice edit, stage CPU | 2,557.3 s | one function, its file's preparation | |

By step (each the sites it removes, measured; a conjecture where marked):

- **The settled run computed twice (site 12)**, one shared result in `settleInferred`, independent of the steps: −587.4 s on the census slice (7.9%), −4.0 s on pretext (5.7%), −40.7 s on the cases (7.1%). It is the largest gain on the cases and needs no design.
- **Step 3 and step 4 (unit results, file workers)** remove sites 2 and 3: −2,595.2 s on the census slice (35.1%); and site 7's walks where one walk serves proposal and extraction, −158.5 s (2.1%). Their wall time is bounded by the units over their limit, not by repetition: the slice's 6 unit passes and 4 interface components over 300 s take 2,854.4 s of CPU, a stopped unit costing its limit; one worker per file runs fragment-parse.mts's 4 over-limit stages in sequence. **Conjectured:** the slice's wall time falls from 2,364 s to the longest file's own work plus its stopped units, about 1,200 s for fragment-parse.mts at a 300 s limit; a unit over its limit today includes repeated preparation, so some may finish once preparation is shared, which no measurement here shows.
- **Steps 2 and 5 (one interface representation, one request mechanism)** remove site 1: −29.8 s on pretext (42.5%: 13.0 s of interface components, 16.8 s of module lowering beside the files' own parses), −7.3 s on the census slice and −4.5 s on the cases. Pretext is where a request holds both a module and its importers; a full census is too.
- **Noise**: sites 8 and 9 (≤ 0.4% in each corpus), and sites 4, 5, 6 (0 in these corpora: the census slice's omission rounds repeat parses only, and exact selection removes the replays of dependency rounds while a growing selection becomes a new pass key).
- **Not repetition by the design's measure**: site 11, the diagnostic and refinement runs (13.0% of pretext, 2.9% of the slice), is work of inference within one unit and stays until inference proposes fewer facts that fail; site 9's self-recursive walks stay by D5. The cases' CPU is 56% parsing (322.2 s), one parse per case, which none of the steps changes.

## 7. Useful implementation steps

| Step | Build and remove | Evidence of completion |
| --- | --- | --- |
| 1. Exact selection and accounting | Pass selected roots through; identify each preparation/walk/check by function. Keep existing execution routes. | Selected function plus one dependent, once; repetition totals explain existing stage CPU. |
| 2. One interface representation | Entry-local rows, complete callable contracts, same-file entry reads and producer/consumer checks. Remove direct footprint/`ensures` reads for migrated forms. Extend guards, constants, overloads and other callable forms with their realization obligations. | Moving a dependency across a file boundary preserves its contract and verdict for each supported form; forged rows/effects/omitted overloads refuse. D6 is complete only when every retained same-file form passes this gate. |
| 3. Unit results and recorded reads | Stable identities, named declaration projections, candidate replay and separate establishment closure. Remove whole-file result keys for migrated checks. | The edit experiments above pass; source failures do not become trusted leaves; the new acceptance theorem covers result emission. |
| 4. File workers | Immutable shared preparation, resumable demand, unit resource supervision and immediate publication. Remove whole-file timeout fallback and sequentially accumulated unit stores. | One preparation per loaded snapshot; one unit execution per input; killed-worker recovery preserves siblings; cold CPU and peak memory measured. |
| 5. One request mechanism | Route cases, census, pretext and controls through the scheduler. Remove component stages, duplicate file roles and census omission rounds. | Identical root sets have identical results/read manifests across clients; targeted timeout losses inspected individually; full suites pass. |

### Plan for step 2

#### The existing mechanism this extends

The interface is everything another unit may read about a function. Processing a function computes that interface and checks its body against it. The same publication and read operations serve calls within a file and across files. Module initialization is one additional unit whose interface states the contracts of the bindings it establishes.

This extends the [front](../SINGLE-PASS-FRONT.md), the [single pass](../SINGLE-PASS.md), [realization and linking](../SINGLE-PASS-THEOREM.md), and [recorded-input replay](../STAGE-STORE.md). A function’s interface and the evidence establishing it have separate identities.

References below use `C/` for `lean/Verification/Source/Claims/`, `L/` for `lean/Verification/Source/Lowering/`, and `P/` for `lean/Verification/Programs/`. Code observations concern the inspected worktree at `f741ed41`. Proposed definitions, algorithms and theorem statements are obligations of this plan. Performance figures are the measurements in this document’s baseline.

The form inventory is an audit of the language’s constructors and their combinations. It does not define which functions receive entries. Every admitted callable receives an interface or a located construction failure; such a failure blocks a reader.

#### The theorem statements

**One unit, conditional on its reads.** For every function or initialization unit, acceptance of its processing result establishes:

1. Exhaustive certification of every body/signature obligation belonging to that unit.
2. Safety of those obligations under the precise interface environment recorded by the result.
3. Realization of its complete published contract under that environment.
4. Agreement between that contract, the serialized entry, and every consumer representation used in its processing.

The assumptions name the content actually consumed, including conservative recursion views, binding contracts, and file projections. They also state capture/value correspondence, invocation kind, frame separation, and the applicable external-contract and initialization hypotheses.

The conclusion quantifies over every advertised signature, every admitted type-parameter assignment, and every environment satisfying the capture contract. A missing signature or plan constructor prevents acceptance.

The existing basis is `mode8Accepted_sound`, whose conclusion covers every member of the accepted group (`C/PassUnitRun.lean:140`), `requestSafe_of_member` (`C/PassUnitFile.lean:24`), and row realization (`C/PassUnitRealize.lean:435`). The new result needs its own acceptance predicate: the current predicate has constructors for the main-file and fresh-module computations, and no constructor for a cached worker result (`C/PassUnitRun.lean:99`).

**Closure of conditional results.** Let a finite set of results satisfy their conditional theorems. Suppose every consumed source interface has a corresponding producer in that set, every consumed view agrees with the producer’s established contract, and every external leaf satisfies its stated hypothesis. Then every member is safe and every published interface is established.

For cycles, this requires a simultaneous induction on the semantic step index. Its local realization lemma must expose the smaller-budget assumptions used when invoking a captured function. The proposition “each member is safe if the others are safe” alone is insufficient to prove the closure theorem.

Mutually recursive members consume the conservative values of unwritten interface components. Written components remain obligations. Each producer establishes the conservative view used by its cyclic readers as well as its published interface. Self-recursive proposal iteration remains inside the function’s own processing task. The measured no-loss result for this policy concerns the name-mention cycles described in this document’s decisions; preservation under the actual read relation is a separate measurement.

**Relation to the existing linking theorems.**

| Existing statement | Required relation |
| --- | --- |
| `mode8Accepted_sound`, `C/PassUnitRun.lean:140` | Retain exhaustive member certification. Add the worker acceptance case and prove that every accepted worker obligation satisfies the corresponding member safety statement. The final `verified` emission additionally requires closure. |
| `ModuleLayout`, `C/PassUnitFile.lean:91` | Generalize its code/interface/capture correspondence to entries over independent stores, every invocation kind and every admitted callable. The domain is the requested closed set. The present independently selected `D` is not an entry-eligibility policy. |
| `layout_realizes`, `C/PassUnitFile.lean:118` | Factor out the local realization implication used by the conditional theorem. Its premises include complete signature realization and capture separation. |
| `passFile_safe`, `C/PassUnitFile.lean:172` | Recover its safety, interface meaning and capture-environment conclusions when all entries use one file store and the existing layout hypotheses hold. |
| `entries_realized` and `crossModule_safe`, `C/PassUnitCross.lean:132,184` | Recover the existing results when dependencies satisfy `ReadsEarlier`. Prove the new cycle result separately; `ReadsEarlier` does not justify an independently stored recursive component. |
| `signatureAgrees_of_checks`, `C/PassUnitSignatures.lean:64` | Transport the conditional producer contract through the serialized table into the consumer store. Discharge producer realization at closure. Equality transport alone establishes no producer body. |
| `init_asserted`, `C/PassUnitInit.lean:23` | Retain its conclusion about assertions at reached finish states. It does not supply the full typed initialization postcondition. |

**H5b remains explicit.** The top-level interface states each binding’s value or cell contract, its identity, and its initialization availability. Its interpretation assumes that the values and cells supplied by module initialization meet those contracts at the budgets and worlds required by consumers, with the required allocation separation and world extension. Callable bindings additionally identify the function value whose body result supplies the callable contract.

This is the module-cell part of `KindMet` and the outside-slot meaning premise, not a consequence of printing an accepted initialization verdict (`C/PassUnitCross.lean:200`; `C/PassUnitFile.lean:110`; `C/PassUnitInit.lean:23`). Checking closure construction, capture layout, defaults and binding identity remains part of this work. Proving the full initialization/world-extension hypothesis is outside it.

**Trusted orchestration.** Replay assumes that a stored payload is the exact result of the execution identified by its manifest. The scheduler marks a result verified exactly when its conditional check succeeds and all establishment dependencies close. It checks content/provenance correspondence, including for an unchanged entry whose producer has a new body result.

This retains the stage store’s execution-and-input binding trust boundary. Complete read recording, projection independence, candidate validation and closure implementation are additional obligations inside that boundary. Current process execution already coordinates identical keys through claims (`pipeline/stages.mts:186,250`); current closure propagates missing or refused dependencies (`pipeline/verify-source.mts:423`). Neither mechanism proves that a new read manifest is complete.

#### One interface type

The wire carries one declared type. The following is a Lean definition sketch; the supporting types require definitions and exact decoders.

```lean
structure EntryGraph where
  rows     : Array (GraphRow Nat)
  builtins : Option (ArrayBuiltins Nat)

structure CallableContract where
  type        : Ty Nat
  invocation  : InvocationContract
  captures    : CaptureContract Nat
  elaboration : ElaborationContract Nat

structure BindingContract where
  binding      : BindingId
  type         : Ty Nat
  storage      : BindingStorage
  availability : InitializationRequirement
  callable     : Option UnitId

inductive UnitContract where
  | callable       (contract : CallableContract)
  | initialization (bindings : Array BindingContract)

structure Interface where
  identity : UnitId
  graph    : EntryGraph
  contract : UnitContract
```

`type` roots the **complete type**: fixed and variadic signatures, overload conjunctions, schemes, callable records, construct signatures, receiver and argument types, result types, and every reachable contract. Returned callables occur in that result type. Their contracts require no separate footprint reconstruction.

Every signature retains the complete `CallEffects.Effect`:

- `closed`, `promise`, `fresh`, `receiverStore`, `onThrow`, `receiverOwn`, `freshObject`;
- `requires`, `elements`, `pre`, `ensures`;
- `receiverGrows`, `elementWrite`, `regions`.

These are the fields of the inspected definition (`lean/Verification/Semantics/CallEffects.lean:153`). Throw behavior includes the graph’s exception family and the effect’s exceptional preservation guarantee; `onThrow` alone is not a thrown-value type.

The normal and exceptional two-state postconditions are the meanings of the signature’s effect. `Effect.post` relates the entry heap, exit heap and returned value; `Effect.excPost` relates the entry and exceptional exit heaps (`lean/Verification/Semantics/CallEffects.lean:424,437`). Transport preserves those meanings in full.

There is a source-language limit to distinguish from that semantic postcondition: written `@ensures` currently elaborates post-state index facts, and `old(...)` is explicitly excluded (`tools/fragment-statements.mts:2273`; `docs/SOURCE-FRAGMENT.md:236`). This plan retains an explicit restriction against source postconditions requiring entry-heap snapshots. The source gate and forged-fragment boundary must refuse them at their location. Supporting arbitrary two-state written clauses requires a snapshot-bearing clause language, call instantiation and return proofs; adding an interface field cannot establish them. Existing two-state effect guarantees remain complete in every entry.

`elaboration` contains all information a reader uses beyond semantic type meaning: binder kinds and bounds, resolution groups, widening policy, contextual offers and any ordering relevant to signature selection. It is declared data, not an executable closure into the producer’s store. The present generic description contains `instantiate` and `bounds` functions closing over lowering data (`L/Synthesis.lean:54`; `C/TypeComparison.lean:41`).

`captures` describes the environment required to construct a closure, with stable binding identities, value/cell distinctions and contracts. An enclosing unit checks the actual captured environment against it. Capture types that depend on an enclosing type parameter remain quantified. Their instantiation consumes the same interface operation as other scheme instantiation.

The initialization entry contains every established binding contract. A reader records the named binding answer, with an establishment edge to initialization. A callable constant has both a callable body obligation and a binding-value obligation.

**Entry-local graphs.** Each table contains the closure of its contract roots, capture and elaboration roots, scheme binders and bounds, meet operands, and required built-in roots. The current reach operation already includes row reads, meet parts and scheme binders/bounds (`C/InterfaceRows.lean:33`); its numbering follows first traversal (`C/InterfaceRows.lean:42`).

Canonical numbering must depend on the rooted entry graph alone. Normalize unordered operands according to their semantics; preserve argument positions, binders, resolution positions and semantically significant ordering. Canonically label recursive components using structural refinement and a deterministic tie resolution independent of original labels. Deduplicate identical rows consistently. Hash the exact canonical contract and metadata.

Publication decodes the exact bytes to be stored and checks producer-to-table agreement. Consumption imports the entry and checks table-to-consumer agreement. The reverse consumer map remains available. The premises of `signatureAgrees_of_checks` and `_back` remain: realized source contract, empty graph environments, membership-preserving canonicalizers and successful checked maps (`C/PassUnitSignatures.lean:64,82`).

When reprocessing a producer, a successful comparison against the previous entry permits retaining its representative, provided identity and all elaboration/capture/binding metadata also agree. The new body result supplies fresh provenance. A refused producer with unchanged interface content prevents closure of its readers.

The required stability controls are:

- An unchanged-interface body edit preserves entry content identity.
- Inserting an unrelated declaration preserves existing identities and entries.
- Reordering independent declarations preserves them.
- Permuting dependency-demand order produces identical entries and read manifests.
- Different internal sharing or numbering either passes checked representative reuse or produces a conservative miss; it never produces unchecked equality.

Store-map soundness does not establish matching completeness or the cost of canonical labeling. Both require measurement.

#### Read matrix

A read includes a failed lookup, an inference lookup and a lookup used only to choose a proposal. Internal reads of a unit’s own immutable working graph need no separate dependency once that graph’s external inputs are accounted for.

The projections below have separate **production keys** and **answer identities**. A production key includes the source facts needed to compute the projection. A unit records the query and canonical answer content. Thus a body edit may recompute ownership analysis without invalidating a reader whose ownership answer is unchanged.

| Current site | What it reads | Destination under D-read | Commit |
| --- | --- | --- | --- |
| `C/Extraction.lean:258` | Other declarations’ parameters, result, stated effect, claims, returned-callable footprint, freshness and regions | Complete callable entry. Construct the slot from that entry. | C5–C8, C10 |
| `C/FragmentFront.lean:544,558,575` | Reachable callees’ bodies, proposal order and the accumulating `found` effects | Demand their interfaces. Walk only the current function’s body; retain its self-iteration locally. Delete the neighbouring-body traversal. | C2, C10 |
| `C/FragmentFront.lean:611`; `C/Extraction.lean:414` | Stand-ins installed into claims and module slots | Own proposal belongs to the producer result; foreign proposals are interface answers with establishment obligations. Forced proposals remain explicit control inputs. | C2, C5, C10 |
| `C/FragmentFront.lean:275` | A same-file function’s `ensures` through `fr.units.find?` | Selected signature’s complete postcondition through the entry reader. | C5 |
| `C/FragmentFront.lean:277` | A module value’s postcondition through separately translated type data | The same entry or initialization binding-contract read. Signature selection uses the complete callable type. | C5, C8 |
| `C/Extraction.lean:189,204,218,247`; `C/Json.lean:131` | Every name mentioned, transitive name reach and SCC membership | `Resolve(scope, name)` projection followed by actual interface/projection reads. Delete name-mention dependencies from acceptance and replay manifests. Syntax reach may serve discovery only, without implying establishment. | C10, C11 |
| `C/Imports.lean:331,372,387`; `C/ModuleInterfaces.lean:78` | Other functions’ free names to discover modules and component order | Actual read demands and their establishment graph. Delete recursive body-based module discovery and component planning. | C1, C10, C13 |
| `tools/fragment-parse.mts:2719,2723` | Callable shape and declaration form used to decide which source modules exist for interface processing | `Origin(binding)` projection: source unit, declared external contract or located failure, for every binding. Key by resolution inputs and normalized binding/export identity. | C1 |
| `C/Imports.lean:212,225,239,260` | Origin AST and importer signature to decide eligibility | Resolve the binding, obtain its complete contract, and check correspondence. Delete form eligibility and silent omission of failed reads (`C/Imports.lean:302`). | C1, C5–C9 |
| `C/Imports.lean:230` | Every module body for assignment to an imported binding | `BindingStability(binding)`. Production key covers initialization, all assignment summaries and omitted-code evidence; answer states stability or its located violation. | C1, C4 |
| `C/Imports.lean:88,92,96,102,120` | Declaration definitions, symbol identities, implicit dependencies and written applications | `Declaration(id)`, `Symbol(id)`, `Application(site)` and `Intrinsic(id)` projections, keyed by normalized declaration components and required recursive dependencies. Absence is an answer. | C4, C9 |
| `C/Preparation.lean:230,255` | Whole-file source gates, annotation/declaration lowering and duplicate-root checks | Immutable preparation plus named `SourceAdmissibility(unit)` and declaration projections. Global consistency failures remain explicit file facts; located failures attach to their owning unit or projection. | C4, C12 |
| `C/Preparation.lean:273`; `C/TypeComparison.lean:41`; `C/Extraction.lean:521,590` | Generic binders, bounds, resolution and instance construction | Callable entry’s scheme and elaboration data; declaration projections for referenced named types. Instantiate inside the consumer’s fresh store. | C7 |
| `C/FragmentFront.lean:419` | Generic descriptions during the extra instance walk | The same scheme entry reads in the unit’s shared proposal computation. Delete the separate instance traversal. | C7, C10 |
| `C/Extraction.lean:350,359`; `C/FragmentFront.lean:445` | Initializer types, annotations and mutable-cell storage contracts | Named binding contracts of the initialization interface, including inferred facts retained with annotations. | C8 |
| `C/TypeComparison.lean:12` | Initializer claim plus annotation, with a special keeping-effect retention rule | Complete binding contract established by initialization, using the general contract relation. Delete importer-side effect retention by signature shape. | C3, C8 |
| `C/Extraction.lean:350,365,628` | Generic-class names, class self bindings and source class identities | `Class(id)` projection for declaration facts; initialization binding contracts for runtime class values; callable entries for constructor and method bodies. Production key covers class declaration structure and referenced contracts. | C4, C8 |
| `C/Extraction.lean:294` | Identity of the standard `Error` constructor to attach allocation freshness | Reviewed constructor contract reached through `Intrinsic(id)`, with the allocation property stated in that contract. Delete name-based inference of the property. | C3, C9 |
| `C/Extraction.lean:407`; `lean/Verification/Source/SourceFacts.lean:540` | Initialization, all bodies and omitted mentions to infer module-cell ownership | `ModuleOwnership(binding)`. Production key covers initialization and every contributing escape summary, including omitted code. Answer carries the property used by extraction. | C4 |
| `C/Extraction.lean:391` | Initialization ordering over declarations and top-level code | Initialization’s own check plus `BindingAvailability(binding)` answers for readers. Key by binding/order facts and initialization contract. | C4, C8 |
| `C/Json.lean:106`; `C/FragmentFront.lean:737,744` | The equation store grown by preceding units | Remove the channel. Each unit has a fresh working store seeded from immutable declaration components and imported entry graphs. Freeze its own result. | C4, C10 |
| `L/Synthesis.lean:6288,6295` | Eager translation of every supplied module value | Lazy recorded entry/binding lookup on demand. Failed translation remains a recorded failure; unrelated values are not eagerly evaluated. | C10 |
| `L/Synthesis.lean:523,572,1186,1216,1601,1629` | Prototype types, member contracts, ordinary/generic/method/construct signatures | Entry graph reads or named declaration/intrinsic projections. All referenced operands retain their complete row closure. | C5–C9 |
| `L/Synthesis.lean:2223,2237,2331,6340` | Uses that offer additional signatures to literals and constructors | Explicit contextual-offer data in the callable interface computation. Collect obligations before finalizing the entry; delete the second enclosing-body traversal. | C8, C10 |
| `C/Extraction.lean:473,489`; `L/ClosureSetup.lean:130,183,257`; `L/Closures.lean:150` | Nested callable bodies, contextual signatures, captures, defaults and code identity | Separate callable tasks. Enclosing code reads the child’s interface and checks construction/capture correspondence. Defaults belong to the child’s source and check. | C8 |
| `C/InterfaceRows.lean:140,153`; `C/FragmentFront.lean:948` | Capture names/types and other readers’ slot types to infer a function’s interface | Producer-owned interface and explicit capture schema. Delete `ifaceOf`’s scan of other units’ plans. | C3, C5, C8 |
| `C/HeadInference.lean:469,666,1312,1335` | Typed-array spellings to infer length kind and constructor postconditions | Type/prototype and constructor contracts, reached through entries or intrinsic projections. State the length relation as a contract property. | C3, C5 |
| `C/HeadInference.lean:842,860,1306`; `C/FragmentFront.lean:287` | Callee postconditions and parameter/declaration type kinds while proposing heads | Entry/postcondition and declaration/type-graph reads through the recorder. Proposal output remains checked by the pass. | C5 |
| `C/RegionInference.lean:24,78,94` | Call-context types, selected effects, region paths and graph claims | Imported entry graphs and the unit’s own graph/claims. Record their originating interface reads. Preserve complete regional effects. | C6 |
| `P/SinglePass.lean:764,1779`; `P/ExpressionEffects.lean:327,394` | Callee signatures, preconditions, selected effects and their postconditions | Consumer slots imported from entries, or locally established values. The pass reads the frozen graph assembled from recorded inputs. | C5–C9 |
| `C/InterfaceRows.lean:33,71,115,128` | Reachable rows, built-ins and producer/consumer stores | Entry-local graph and checked maps. Built-in roots and exception-family agreement are part of the content. | C5 |
| `C/ModuleInterfaces.lean:8,38,48` | Complete origin document and source digest when checking staleness | Separate producer provenance plus interface/projection content validation. Delete body-bearing module documents from consumer manifests. | C11, C13 |
| `C/FragmentFront.lean:1069,1115` | Other units’ accepted results, layouts and publication decisions | Establishment graph over conditional results. Delete proposal-based selection and `laidOut` publication filtering. | C3, C11 |
| `C/FragmentFront.lean:1178,1228,1239` | Transitive unbound-name searches through module bodies | Recorded `Resolve`/`Origin` answers, including absent and refused bindings. A reader’s closure reports the originating failure. | C4, C10 |
| `pipeline/module-interfaces.mts:139,148,168` | Whole-file results and interface preparation failure, followed by ordinary-contract fallback | One requested-unit result and explicit blocked dependencies. Delete whole-file fallback and fallback to ordinary imports. | C12, C13 |
| `pipeline/verify-source.mts:423` | Accepted dependency names | Exact consumed-entry identities and current establishment evidence. Closure validates provenance as well as graph membership. | C11 |
| `pipeline/stages.mts:458,474` | Nested parse/module execution and replay context | One preparation request keyed by source snapshot, project observations and adapter identity, shared across file roles. | C12, C13 |

The matrix is an input-boundary inventory. C10 makes these boundaries executable: unit processing receives its own source, an immutable local graph and the recording reader, rather than a `Front` exposing other bodies and mutable file state. Searches, proposal failures and negative lookups use that reader too.

#### Callable form inventory

The rows below compose. A generic asynchronous method, for example, receives the obligations of its invocation kind, scheme, capture environment and asynchronous result contract. There is one publication operation and one reader.

| Admitted form and current source | Interface and own realization obligation | Consumption |
| --- | --- | --- |
| Module function declaration, including named default export: `tools/fragment-statements.mts:2061` | Complete offered type, invocation kind and capture schema. Use `rowSpec_of_requestSafe`; establish frame, goal, pre/postconditions, footprint, freshness and exceptional behavior. `layoutOwn` is an executable check, not itself that theorem (`C/FragmentFront.lean:948`). | Import its complete type into a slot and check agreement. Export aliases resolve to the same binding. |
| Explicit receiver and receiverless declaration: `tools/fragment-statements.mts:2087`; `L/Types.lean:803` | Preserve receiver contract and strict/sloppy invocation behavior. Receiver-bearing code uses `UnitIsCode`; receiverless code needs the existing `ReceiverDropSound` premise or its proof, with postcondition positions preserved (`C/PassUnitRealize.lean:306,505,570`). | The call supplies/checks its receiver against the entry’s signature. |
| Optional/defaulted/pattern parameters: `tools/fragment-statements.mts:2127`; `tools/fragment-expressions.mts:2281,2349` | Offered arguments include optionality. The child’s code includes the binding prologue, defaults, their evaluation order and scope. Realization connects that prologue to the public calling convention (`L/Closures.lean:20,42`). | Consume the same signature; omitted arguments and defaults follow the checked calling convention. |
| Array, tuple and packed-binder rest parameters: `L/ClosureSetup.lean:155,183`; `L/Types.lean:803` | Fixed/variadic offers and packed frame. Extend row realization to a rest store: the current theorem assumes `c.store = none` (`C/PassUnitRealize.lean:436`). Prove allocation and argument-pack correspondence; packs contain values without holes. | Instantiate the entry’s fixed or variadic row; preserve pack/binder restrictions. |
| Overloaded declarations: `tools/fragment-statements.mts:2037` | One function identity, every offered row and every required implementation check. Compare publication against the complete producer contract, so omitting an offer fails. Shared code identity is checked (`C/Extraction.lean:93`). | Read the conjunction and retain elaboration ordering where relevant. |
| Generic and resolution-qualified functions: `C/Extraction.lean:521`; `C/Preparation.lean:273` | Scheme, binder kinds/bounds, resolution, packed binders and widening policy. Prove realization at every admitted instance from the parameterized body check. Existing parametricity is an ingredient, not the publication theorem (`P/Parametricity.lean:12`; `C/Extraction.lean:524`). | Instantiate from entry data in the consumer store; record the entry and any declaration projections used. |
| Guards and assertion functions, including closures: `L/Types.lean:821`; `L/Closures.lean:165` | Preserve promised type, promise argument and guard/assertion kind, together with the plain signature. Realize the promised row and derive the plain row through `rowSpec_plain_of_promise` (`C/PassUnitRealize.lean:167`). | Ordinary calls and promise-consuming calls select rows from the same entry. |
| Arrow functions, expression/block bodies, anonymous and admitted named function expressions: `tools/fragment-expressions.mts:2182` | One task per literal identity, with inferred/contextual result, complete effect, lexical receiver and capture contract. New local-result-to-closure-realization theorem replaces checking its code inside every enclosing member. | Closure construction checks captures and produces a value at the entry type; subsequent reads use that type. |
| Nested function declarations and recursive local closures: `tools/fragment-statements.mts:729`; `L/Closures.lean:157,206` | Same literal interface, with hoisting/availability and self-entry obligations. Preserve current source restrictions; self iteration belongs to the child task. | Resolve the lexical binding and consume the child entry. Parent/child establishment edges preserve construction requirements. |
| Functions held in module/local constants, mutable cells, fields, returned values or conditional expressions: `C/Extraction.lean:350`; `L/Synthesis.lean:2223`; `tools/fragment-expressions.mts:260,881` | The callable has its own interface regardless of the expression holding it. The producing unit establishes the binding/field/result contract and value correspondence. A choice between values preserves the complete resulting type. | Read the binding/value contract; follow its callable contract without inspecting the initializer body. |
| Object-literal methods: `tools/fragment-expressions.mts:881,2182` | Closure contract with receiver, captures and every offered signature. Realization includes method-value construction and host receiver correspondence. | Member lookup obtains the complete method type; invocation uses the common call rule. |
| Instance, static and generic class methods; callable class-field initializers: `tools/fragment-classes.mts:529,574,635` | Separate callable tasks. Class projection supplies declaration facts; initialization/construction establishes member values. Generic methods require scheme realization and receiver/capture correspondence. | Read the class/instance contract and the method’s complete callable entry. |
| Explicit, implicit and derived constructors; admitted local classes: `tools/fragment-classes.mts:223,336,451,814`; `L/ClosureSetup.lean:212` | Construct signature, result instance contract, allocation/field initialization and capture requirements. New constructor realization connects the checked constructor code to its construct offers. Existing call-row realization is insufficient by itself. | Construction consumes the complete constructor type and its effect; instance/member contracts follow its checked result. |
| Async declarations, arrows, expressions and methods: `tools/fragment-statements.mts:2077`; `tools/fragment-expressions.mts:2191`; `L/Closures.lean:155,192` | Preserve promise result and the existing asynchronous lowering contract. Prove entry realization through that lowering. Preserve the restriction against a non-top inferred async footprint (`docs/SOURCE-FRAGMENT.md:131`). | Consume the promise-valued callable type. Rejection and normal-return effects retain their distinct meanings. |
| Callable records, intersections and method-bearing values: `P/SinglePass.lean:772`; `docs/SOURCE-FRAGMENT.md:287` | Publish the whole admitted type graph, including fields and callable clauses. Realization establishes all parts supplied by source construction. | Member and call rules consume the same graph; no footprint-only projection. |
| Imported source callables, aliases and re-exports: `tools/fragment-parse.mts:2723`; `C/Imports.lean:212` | Resolve to the source producer and its complete entry, regardless of declaration form. Source bodies remain establishment dependencies. | Exactly the same read as a same-file binding. |
| Ambient, declared and reviewed library callables, including native methods/constructors: `tools/fragment-parse.mts:1677`; `C/PassUnitCross.lean:200` | Complete contract with an explicit declared/host assumption as establishment evidence. Preserve every effect field and existing audit boundary. | The common entry reader distinguishes the evidence origin, not the contract representation. |
| Intrinsic callable adapters, including binding a receiver or constructing a callable value | The containing operation establishes the resulting complete callable contract through its existing typing rule; captured callable dependencies are entries. Source-generated executable bodies receive unit identities. | Callers read the resulting contract. They do not reconstruct the original callable’s effect. |
| Module top-level code: `C/Extraction.lean:378` | One initialization interface containing all binding contracts, availability and callable identities. Own check establishes its modeled execution and assertions; H5b supplies the stated typed binding interpretation. | Named binding-contract reads, with an initialization establishment edge. |

The existing exclusions remain language restrictions, with their source diagnostics: generators and suspended `yield` (`docs/SOURCE-FRAGMENT.md:205`; `tools/fragment-expressions.mts:2197`), accessors (`docs/SOURCE-FRAGMENT.md:188`), unsupported constructor behavior (`docs/SOURCE-FRAGMENT.md:247`), and the documented overload combinations (`docs/SOURCE-FRAGMENT.md:229`; `tools/fragment-statements.mts:2037`). They do not justify excluding admitted receivers, rest parameters, schemes or closures from entries.

A new restriction requires a behavior-level statement in `SOURCE-FRAGMENT.md`, enforcement at the source boundary and a located refusal through forged input too. It cannot be introduced as a way to preserve a partial interface implementation.

#### Head and region inference

The minimal change belongs **inside this plan, before per-function replay**. `HeadInference` obtains callee postconditions and type kinds through recorded interface/projection reads. `RegionInference` consumes the same imported graph and complete regional effects. Their candidates remain untrusted inputs checked by the pass.

`HeadInference` maintains a separate source-name context and interprets statements (`C/HeadInference.lean:474,1306`). `RegionInference` constructs claimed evidence and iterates graph facts (`C/RegionInference.lean:24,64,94`). They are not both source-statement interpreters, but both duplicate transfer work beside the pass.

Their replacement belongs **after the on-demand cutover**, as the next inference change. This ordering exposes the measured file-role and fallback gains without making them depend on an unmeasured inference-precision change. It does not declare the duplicate transfer mechanisms satisfactory.

The replacement follows the earlier head-inference design: use the pass’s entry, step, merge and edge operations; discover a finite candidate vocabulary; project entry facts to head slots; remove candidates that back edges fail to establish; and rerun only affected regions before the final proved pass. Regional facts, implications and input identities require the same treatment. The proposal must preserve every gate verdict before deleting the old interpreter.

The general property replacing typed-array spelling recognition belongs in C3. Keeping the spelling list until the larger inference replacement would violate the cleanup rule.

There is another repetition obligation: `Synthesis.walkUnit` repeats source walks for evolving bindings and for additional offers discovered at uses (`L/Synthesis.lean:6320,6340`). C10 instruments those traversals and replaces whole-body retries with shared constraint/proposal computation. They are not silently counted as one traversal because one outer `walkUnit` call encloses them.

#### Commit order

Every commit builds and keeps the suite green. Verdict comparison uses stable unit identities and records both conditional acceptance and closed verification. A changed verdict is named, its cause explained and its source preserved; changing an expected classification does not satisfy the unchanged-verdict gate.

Cleanups replace each semantic selection list in its own commit before later changes build on it. If a cleanup requires a more general proof to preserve verdicts, that proof belongs in the cleanup before it lands. Merely renaming a filter to an obligation is insufficient.

For every commit, retain `dev/work-report.mts` output by repetition site and run both edit experiments as soon as that commit affects their path. Before function replay exists, record their remaining work rather than claiming the one-function target.

| Commit | Build and delete | Proof and validation obligation | Measure |
| --- | --- | --- | --- |
| **C0 — Accounting and fixed comparison inputs** | Stable unit identities, signature-obligation identities and counters inside nested synthesis retries. Retain the shared settled result already present at `C/FragmentFront.lean:1700`. | Demonstrate that accounting preserves verdicts; distinguish task execution, proposal traversal, signature checking, replay validation and resource attempts. | Establish site 12 at zero on the slice too. Preserve the original baseline and record the immediate-parent baseline. Run both edit experiments. |
| **C1 — General origin and binding resolution** | Replace `importedModules`’ callable-form filters, `eligibleRead` and silent failed-read omission with origin resolution, stability and complete contract-correspondence obligations. | Every value binding resolves to source, a stated external contract or a located failure. Preserve aliases, overload identity and negative lookups. | Count resolved origins and stability computations; report effects on sites 1 and 4 and both edits. |
| **C2 — General interface proposal obligation** | Replace the exclusions in `declarationWalks` and `importerReads` with one obligation for every callable: written components plus inferred components checked by its own body. Delete form-based decisions about whether dependencies matter. | Conservative proposal components have their semantic meanings; written contracts remain whole. Async restrictions remain source restrictions. No weakening fallback for a failed source interface. | Count proposals by function and component; preserve self-walk counts separately. |
| **C3 — General realization and contract properties** | Replace `laidOut` as a publication subset with a realization obligation over every advertised contract. Replace shape-specific keeping-effect retention, typed-array constructor names and allocation-freshness recognition with the corresponding contract properties. | State and check realization for the complete type, invocation and frame. Required row/region/rest/scheme lemmas land before their former exclusions disappear. Preserve the explicit host assumptions. | Count every function requiring realization and every located failure; compare all existing verdicts. No acceptance gain from omitted obligations. |
| **C4 — Immutable preparation and named projections** | Construct declaration, resolution, class, ownership, stability, availability and admissibility projections. Give units private equation/search state. Delete dependence on a predecessor unit’s grown store. | Equal projection answers yield equal processing inputs. Preserve recursive declaration components, negative answers and ownership evidence from omitted code. | One computation of each preparation/projection per snapshot; order-permutation tests. Track preparation CPU and both edits. |
| **C5 — Complete entries and ordinary same-file reads** | Add the single interface type, entry-local rows, canonical encoding and both store-map checks. Route declaration, receiver, guard, freshness, pre/postcondition and head-proposal reads through entries. Delete corresponding slot and `ensures` reconstruction. | Conditional realization for ordinary rows and promise/plain pairs; exact producer contract comparison; metadata agreement; both receiver paths. | Cross-file relocation preserves complete contracts and verdicts. Body-edit, declaration-insertion/reordering and demand-order controls. Measure serialization/map CPU. |
| **C6 — Regional and variadic reads** | Route regions and rest signatures through the same entries, with no erased effect fields or reconstructed argument contract. | Regional realization on ordinary and receiverless paths; packed-frame realization, separation and allocation/calling-convention correspondence. | Same-file/cross-file positive and negative cases; forged regions and packs; count each offered-row obligation once. |
| **C7 — Scheme reads** | Serialize generic elaboration data; instantiate from entries in private stores. Delete generic access through producer closures and separate generic-instance body walks. | Universal scheme-instance realization, including bounds, resolution, packed binders and store-map transport. Binder-free examples do not discharge this obligation. | Permute instantiation and demand order; compare verdicts and site 7. No extra producer processing for another consumer instance. |
| **C8 — Closures, classes and initialization** | Separate every nested callable task; publish capture schemas and top-level binding contracts. Route constants, methods, constructors, async callables and returned/field-held callables through the common operation. Delete nested-body checking inside enclosing members and repeated initialization typing. | Closure-construction link; defaults and captures; complete offers; constructor and async realization; initialization binding-value correspondence under H5b. | Nested-body edit preserves the parent result when the child interface is unchanged. Count every callable independently. Reduce site 8; test unchanged binding contracts and changed availability. |
| **C9 — External contracts and complete boundary coverage** | Route declared/host callables and intrinsic contracts through the same entry reader. Delete `importedArrow`, the established footprint triple and `ordinaryImport` fallback. | Preserve existing trust assumptions and every effect field. All inventory combinations use the general entry operation. | Complete source/library boundary cases; forged metadata, omitted overloads, wrong receiver, wrong promise and changed built-ins. Both edits retain verdicts. |
| **C10 — One demand computation and recorded reads** | Replace neighbouring-body walks with suspend/resume demands. Share proposal, instance and extraction results; remove whole-body retries identified in C0. Delete name-mention acceptance edges and eager module-value translation. | Every external observation appears in the manifest. Resolve cycles without consuming a stronger provisional interface and later restarting the unit. Check every mutual-cycle view against its producer. | Sites 7 and 8 reach zero; no restarted caller after a newly discovered dependency. Diamonds and repeated roots process their shared dependency once. Audit actual cycles against the measured recursion policy. |
| **C11 — Conditional results, closure and per-function keys** | Publish individual results immediately; validate candidate read manifests; separate content from establishment provenance. Remove whole-file result keys for unit work. | Prove the conditional theorem, store transport and step-indexed closure theorem; connect the exact emission predicate to `mode8Accepted_sound`. | Both supplied body edits process exactly one function. Unchanged request processes zero. Failed producer with unchanged entry blocks cached readers without rerunning them. |
| **C12 — One worker per loaded file** | Retain immutable preparation; execute/resume units with private state. Add per-unit resource accounting and recovery. Delete whole-file timeout attempts and repeated fallback preparation. | Worker eviction, resumption and restart preserve manifests and completed results. Waiting consumes neither execution budget nor an execution slot. | Sites 2 and 3 reach zero. This targets the slice’s measured 2,595.2 s, 35.1%, of repeated work. Measure cold CPU, peak memory, preparation reloads and killed-worker recovery. |
| **C13 — One request mechanism** | Route cases, census, pretext, controls and `make check` through root requests. Unify requested/imported preparation. Delete interface components, duplicate file roles and census omission/dependency retries. | Identical roots/options produce identical conditional results, manifests and closure across clients. Preserve located failures without reparsing successively omitted files. | Site 1 reaches zero: pretext’s measured 29.8 s, 42.5%, is the principal target. Sites 0, 4, 5 and 6 also reach zero. Repeat cold, warm and edit measurements. |

The form commits develop the obligations of one general interface definition. They do not authorize a production mode that chooses entries for some forms and weaker contracts for others. The cutover requires all callable forms reached by the request to use the complete operation; a missing realization is an explicit failure.

C12 and C13 follow the sound per-function result boundary immediately. Their gains do not wait for replacement of head inference. The settled-run saving is already represented by the shared `r` in `settleInferred`, and must not be claimed again as new work (`C/FragmentFront.lean:1700`; this document’s baseline at line 259).

#### Keys, demand and publication

A unit’s pre-key contains its stable lexical identity, normalized own source, annotations/defaults, verifier and adapter identities, and every option affecting processing. Nested callable bodies are replaced in the enclosing unit’s source representation by their identities and construction syntax; their contracts are reads.

The final key adds the canonical answers of every recorded interface and projection query. It contains no other function’s body, processing key or verdict. Source spans remain diagnostic mappings.

Replay validates every query, including absence, against the current snapshot. A matching entry with stale producer provenance cannot establish closure. Source failures remain source dependencies; they cannot become declared leaves.

Demand suspends the current computation while the requested interface is computed. Resumption continues its saved work. Mutual-cycle detection supplies conservative views of unwritten components; those views have explicit content and establishment identities. No provisional stronger view may escape into a result that later requires restarting under a weaker one.

The scheduler owns one task for each unit/pre-key in the request. Preparation has one shared identity regardless of requested/imported role. Worker unloading may reload stored immutable preparation; it must not recompute it or reprocess completed functions.

#### Completion

Completion requires all of the following:

- Every admitted callable and initialization unit has the interface and realization obligation in the inventory. No source reader succeeds through an eligibility omission or weakened fallback.
- Every matrix row has its stated destination. Unit processing has no direct access to another unit’s body or mutable preparation state.
- The conditional theorem covers the exact accepted worker result. The closure theorem establishes every verified member, including mutually recursive members over independent stores.
- `dev/work-report.mts` reports zero repeated orchestration, preparation, proposal/extraction and result-processing work at sites 0–8 and 12. Site 9 records only the stated self-recursive walks. Site 11 records the diagnosing/refinement work retained until head inference is replaced.
- Distinct signature obligations are counted separately and each executes once. A second check of the same function at another required overload is not hidden, and a duplicate check of the same obligation is not excused as an overload.
- Internal synthesis retries are visible in the accounting. Any remaining repetition there prevents the zero-repetition claim.
- An unchanged request processes zero functions. Both supplied edits—`isCollapsibleSpaceCode` in pretext and `collect` in `fragment-statements.mts`—process exactly the changed function, with unchanged entry content and verdicts. Preparation and read validation are reported separately.
- Declaration insertion/reordering and demand-order permutations preserve unrelated entry identities and keys. A changed ownership, stability, declaration or binding-contract answer invalidates exactly its recorded readers.
- Unsafe and forged-input controls retain their refusals. Every verdict difference has a named cause; reclassification does not count as preservation.

The cold comparison uses the same corpus, revisions, limits, profiling settings and stage-store conditions as the recorded baseline:

| Corpus | Recorded stage CPU | Recorded repeated work | Required comparison |
| --- | ---: | ---: | --- |
| Pretext, 12 files | 70.2 s | 45.0 s | Report total CPU, removed work by site and new interface/validation overhead. |
| Six-file census slice | 7,389.9 s | 3,584.4 s | Report total CPU, timeouts by unit, removed fallback work and final verdicts. |
| 722 cases with projects | 574.9 s | 61.5 s | Report total CPU and preserve the parsing denominator. |

These figures are recorded at `docs/drafts/on-demand-processing.md:232,246`. Subtracting repeated work gives a performance hypothesis, not a measured result. The claims “much faster” and “every item once” require both the accounting gate and repeated paired CPU measurements. Report ratios and dispersion against the original baseline and the immediate parent. A lower total caused by checking fewer obligations fails the gate.

The full census follows the main-branch policy. The supplied slice and targeted function/dependent experiments provide the branch comparisons.

#### Questions requiring evidence before their dependent commits

1. **Complete realization coverage.** The inspected row theorem excludes rest collection, and `rowConditions` excludes several effect properties (`C/PassUnitRealize.lean:294,436`). Before C3–C9, map every actual source-produced contract to a realization proof, including qualified schemes, constructors and async code. The cost of those generalizations is not established by reading.

2. **Capture and contextual-offer independence.** Closure setup uses the enclosing scope and contextual offers (`L/ClosureSetup.lean:130,257`; `L/Synthesis.lean:2223,6340`). Before C8, demonstrate that a capture-parameterized interface preserves the existing inferred contracts and verdicts without checking the same body again for each construction or later offer. This is a feasibility gate, not an assumed property.

3. **Demand cycles.** The supplied recursion measurement uses `Front.edgesOf`. Before C10, measure cycles of the actual read relation, including initialization, capture contracts and contextual offers. Demonstrate order-independent conservative views without caller restarts. Any precision loss is named before cutover.

4. **Hidden synthesis work.** The outer `walkUnit` accounting does not by itself distinguish the internal traversals at `L/Synthesis.lean:6323,6336,6344`. C0 measures them before C10 claims to remove repeated walks.

5. **Canonicalization cost and cutoff completeness.** Before C5/C11, measure recursive graph labeling, sharing differences and matching-fuel failures. Require all four stability experiments. No inspected theorem proves those experiments will pass.

6. **Preparation locality.** Whole-file gates and declaration lowering occur in `equationFront` (`C/Preparation.lean:230`). Before C4/C12, identify which failures can be attached to a unit/projection and which are genuinely global consistency failures. Measure the projection recomputation required by the two supplied edits.

7. **Intrinsic adapters and generated code.** Before C9, complete an exhaustive audit of generated callable adapters and every parser/lowering constructor, including callable values produced without a source function declaration. The inventory gives their destination; the precise set of generated bodies requiring independent task identities needs that audit.

8. **Performance.** No builds, checks or timing experiments accompany this read-only plan. The baseline supplies opportunities, not evidence of the proposed implementation’s speed or verdict preservation.

## 8. Decisions

The owner's decisions on the questions this design raised:

1. **Acceptance target.** The redesign is judged by the same verdicts, every item processed once, much faster, and each change in a count explained. Reaching the old route's census count (596/755) is no criterion.
2. **Module initialization (H5b).** H5b stays a stated hypothesis; its typed-finish/world-extension proof is a separate obligation.
3. **Entries for functions held in module constants** are part of this redesign, in step 2 (one interface representation). Their design is [module constant entries](module-constant-entries.md).
4. **Recursion (D5).** No joint iteration over mutual cycles: a member of a cycle of two or more functions reads the others' unwritten interface parts at the worst case, and the cycle verifies when every member's own check passes. A self-recursive function keeps today's proposal, inside its own unit of work (section 3, "Demand and scheduling"). Basis (measured 2026-11-13 over the pipeline cases, a 22-file slice of tools/ and pretext, on `Front.edgesOf`'s cycles): reading every cyclic function's unwritten part at the ordinary effect loses 3, 2 and 2 verdicts, each from a self-recursive function whose walks find a footprint below the ordinary effect that a caller needs; reading only mutual cycles so loses none in any of the three corpora. No cycle crosses modules; in tools/, 49 of 88 cyclic functions state their effect.

## 9. Form-based decisions today

Every place in the front's import, extraction, proposal, publication, row, inference and realization code where a function's form, a class's name, a property's spelling or a value's shape decides whether it is read, proposed for, published, or how it is treated. Read from the code at `795ba048` (the leg's base on `b7c8a559`); `C/` is `lean/Verification/Source/Claims/`. Each row gives the condition and both sides. Where the plan of step 2 or section 2 of this document says otherwise, the code is what this table states and the row says so.

### Resolution of an imported binding (C1)

Every value import of a program source file lists its module (`importedModules`), whatever value it holds. Every import of a listed module resolves by its declaration identity to its origin (`resolveRead`): the module's function binding the name within the declaration's span where that binding is stable, else the module's initialization (no callable entry; read at the declared contract); an unlisted module's import is read at its declaration. Stability is established once per module for each function binding (`DecodedModule.stable`). The entry's contract and the importer's reading correspond by the store-map checks (`refuseRows`), a refused check refusing each reader at `signature rows differ`. The form-based decisions that remain on this path:

| Site | Condition | Holds | Fails |
| --- | --- | --- | --- |
| `C/Imports.lean` (`documentReads`) | a local name two imports bind | — | both read at their declarations |
| `C/Extraction.lean:49,311` (`bodyModule`) | the declaration's module path ends in a source extension and not in a declaration extension | an import with no entry is read at `ordinaryImport` (ordinary effect, precondition kept) | read at its declared type |
| `C/Extraction.lean:17` (`importedSignatures`) | the declared type expands to one fixed signature, or a plain one and a promise one of the same actuals | `importedArrow` reconstructs a slot | `importedArrow` fails; with `lenient`, the import is read at its declared contract |
| `C/Extraction.lean:68` (`ordinaryImport`) | every signature assumes nothing (`assumesNothing`); else a variadic signature or an empty clause states something | read as written; else at the ordinary effect | refused: "read only at its module's entry" |
| `C/FragmentFront.lean:641` (`withNeverImports`) | the value's name starts with `%`, is `arrayPrototypeName`, is the file's own or qualified | skipped | an import of one fixed signature with an empty result and no promise is read at keep/keep |
| `C/FragmentFront.lean:1195` (`unboundReads`) | a name starts with `%` or `?`, or is `this` | not a module binding (an intrinsic) | followed |

### Proposal (C2)

Every function's unwritten components are what its own checked steps establish (`PassProposals.proposals`, [proposals by the pass](proposals-by-the-pass.md)): the join of its steps' local effects, generic and rest functions included; a written effect's footprint and throw bound are kept whole, its steps proposing the returned function's footprint, and the importer's reads follow the bodies of the functions so run (`importerReads`). The decisions that remain:

| Site | Condition | Holds | Fails |
| --- | --- | --- | --- |
| `C/PassProposals.lean` (`proposals`), `C/Imports.lean` (`importerReads`) | a function is async | no run: `top`, by the language (`SOURCE-FRAGMENT.md`, "A footprint other than `top` claimed for an async function") | run |
| same | a function is a stand-in | no run: the control's footprint | run |
| `C/PassProposals.lean` (`proposals`) | the function mentions its own name | its runs joined from keep/keep until they establish no more | one run |
| `C/PassProposals.lean` (`proposals`) | `resultWithFootprint` accepts the result annotation | a returned function's footprint proposed | `top` |
| `C/FragmentFront.lean:74` (`writtenSchemes`) | a generic closure is a guard, async, or of a resolution-qualified binder; or a nested scheme annotation without a written result; or a rest that is no array | claimed at no scheme | claimed at its written scheme |
| `C/FragmentFront.lean:615,741` | a unit has no type parameters and is no initialization | it gets an ordinary slot (`ordinarySlots`) and an interface slot | a generic function is read through `generics` instead |
| `C/Extraction.lean:269` (`ordinarySlots`) | the written effect states regions | slot at the written footprint and regions | slot at the claim's footprint, the written `fresh` |
| `C/FragmentFront.lean:669,734,861` (`proposes`, `establishChecked`) | a module function's claim is more than the ordinary effect, or it states a postcondition or guard (`statesMore`) | its group is checked in the interface component | not checked there |

### Publication and realization (C3)

| Site | Condition | Holds | Fails |
| --- | --- | --- | --- |
| `C/FragmentFront.lean:893` (`establishEntry`) | the claim is the ordinary effect and the function states no postcondition or guard | no entry: "the ordinary effect" | entry candidate |
| `C/FragmentFront.lean:962` (`layoutOwn`) | the unit is the initialization | outside | — |
| `C/FragmentFront.lean:963` | the function has type parameters | outside: "a scheme" | — |
| `C/FragmentFront.lean:965` | its request is qualified | outside | — |
| `C/FragmentFront.lean:970–977` | a captured file function read at other than one type; its own interface read at several types or none | outside | — |
| `C/FragmentFront.lean:980` | its interface expands to one clause of signatures | continue | outside |
| `C/FragmentFront.lean:982` | the code's invocation kind (`convertsReceiver`: sloppy, else call) offers each row's receiver | continue | outside |
| `C/FragmentFront.lean:1009` (= `PassUnit.rowConditions`, `C/PassUnitRealize.lean:295`) | arity within the arguments, `belowRow`, no `freshObject`, no `requires`, no `elements`, no `receiverGrows`, no `elementWrite` | continue | outside: "the code's conditions" |
| `C/FragmentFront.lean:1014` | receiverless and a postcondition names the receiver, in either state (`IndexFact.pastReceiver`) | outside | — |
| `C/FragmentFront.lean:1033` | the member's inputs equal `codeFrame arity p captures none` (no rest store, `C/PassUnitRealize.lean:437` assumes `c.store = none`) | continue | outside: a rest function is never laid out |
| `C/FragmentFront.lean:1046,1116` (`laidOut`) | the function is in the greatest set closed under captured callees | published | "not laid out" |
| `C/ModuleInterfaces.lean:22` (`encodeInterfaces`) | the document's `functions` | one entry per function | a callable held in a constant or class has none |
| `C/TypeComparison.lean:17–33` (`moduleValueType`) | an annotated constant: some signature of the initializer's type has the keep/keep effect (throws aside) and the same receiver, result and arguments as an annotated signature | that signature takes the initializer's effect | the annotation's effect |
| `C/Extraction.lean:295–304` (`freshConstructors`) | a global binding named `Error` declared as `Error` in `typescript/lib/lib.es5.d.ts` | its constructions allocate an unpublished identity | ordinary construction |
| `C/Extraction.lean:350,376`; `C/FragmentFront.lean:473`; `C/InterfaceRows.lean:146` (`genericClassNames`) | a constant whose initializer is a class with type parameters | no module constant, no self binding; read through `generics` | a module constant |
| `C/HeadInference.lean:469` (`typedArrays`), used at 668, 1320, 1337 | a constructor or referenced type named one of nine typed-array names | `length` is a view length; a construction's argument is its length | no fact |
| `C/HeadInference.lean:1321,1338` | a referenced type named `Array` or `ReadonlyArray`; a construction of `Array` | array length | no fact |
| `C/HeadInference.lean:321,486,810` | a method named `push`, `pop`, `shift`, `unshift`, `splice` (and `fill`, `copyWithin` at 486; `push` alone at 810) | the receiver's facts are killed (or, at 810, a push fact proposed) | kept |
| `C/HeadInference.lean:150,158` | a name starting with `%`, or `this` | no source-name fact | a fact |

`RegionInference.lean` and `InterfaceRows.lean` decide nothing by form beyond the rows above: region names are read from each callee's effect, and the reach of a row table follows its rows.

**Count.** 47 decisions at `795ba048`, one per row before C1 replaced 12 of them (the four of `importedModules`, eight of `eligibleRead` and `documentReads`): `fragment-parse.mts` 4, `Imports.lean` 10, `Extraction.lean` 6, `FragmentFront.lean` 21, `TypeComparison.lean` 1, `ModuleInterfaces.lean` 1, `HeadInference.lean` 4; `PassUnitRealize.lean`'s `rowConditions` is the row of `layoutOwn` that calls it; `RegionInference.lean` and `InterfaceRows.lean` 0.

**Where the plan differs.** The plan's typed-array lines (`C/HeadInference.lean:469,666,1312,1335`) are 469, 668, 1320, 1337, and the same functions also decide by the spellings `Array`/`ReadonlyArray` and by method names, which the plan does not list. Eligibility admits guards (above). The plan does not list the ordinary-effect entry omission (`establishEntry`), `withNeverImports`, `bodyModule`, `genericClassNames` or `writtenSchemes`' exclusions.
