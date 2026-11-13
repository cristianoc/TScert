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
| Declaration proposal and body extraction | `declarationWalks` walks eligible bodies; `retypeFromFragment` walks them for extraction. Generic-call instantiation adds `instancesFromWalk` before retyping. `Claims/FragmentFront.lean:247`, `Claims/FragmentFront.lean:419`, `Claims/FragmentFront.lean:544`; `Claims/Extraction.lean:552`, `Claims/Extraction.lean:600`. |
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

On a demand cycle of two or more functions, a member's unwritten interface components use their conservative values: unrestricted changes, unbounded throws, no freshness or returned-callable strengthening. Written contracts remain obligations. There is no joint iteration over a cycle's members; the cycle verifies when every member's own check passes. A function that reads its own interface keeps the front's self-recursive proposal (at most three walks of its own body, `declarationWalks`), which stays inside its one unit of work. A cycle is one of the front's name-mention relation (`Front.edgesOf`) until recorded reads replace it.

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

An item is a function, `<sha256 prefix of its source>#<unit>`, or a file, `<sha256 prefix>`, so one function has one item in every process of a request, in its own file's pass and in an importer's interface component alike. A class of work is one of: a file's lowering (claims and declarations), its freezing (store and plans over it), its head facts, an importer's plans, the initialization typing, a function's extraction, a body walk (proposal, retype, instance), a check (group, member runs, main graph runs, diagnosing walks), an importer's or a publication's store-map check. The ideal is each class done once on each item per request.

Only executed attempts count; a replay is the result of an execution. An attempt's CPU time (the stage runner's user and system time) outside its recorded work (reading, decoding, encoding) is shared among its work in proportion to the recorded time. Work done more than once is attributed as follows.

- Across attempts, the occurrence in the item's own file's pass (else the first) is the processing. Another occurrence is site 1 when the two stages differ (a pass and an interface component, or two components); between two passes, site 5 when their fragments differ (another omission list), site 3 when their selections differ after a whole-file timeout, site 6 when their selections differ otherwise, site 4 when only their interface files differ.
- A whole-file pass over its limit is site 2, its CPU time whole.
- Within an attempt: the first body walk is the processing, a second proposal walk of the returned-callable round site 8, a recursive function's later walks site 9, the retype and instance walks site 7 (site 8 for the initialization's), each typing of the initialization after the first site 8.
- Within an attempt's check of a function: the first member run is the processing; each diagnosing walk and the rerun it leads to, and each main graph run beyond the member runs (a regional check beside a run), site 11; one more member run than the reruns is site 12, the settled run computed twice (`settleInferred`), at the mean member run's time.
- Units of one function name beyond the first (overloads) are site 10.

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

### Step 2, as commits

Each commit is reviewed by Astra before the next starts; each states its proof obligation, its pipeline cases (a form moved across a file boundary keeps its contract and verdict) and its forged-input controls. Guards are done (`rowSpec_plain_of_promise`, guard entries); the rest, in order:

1. **Entry-local row tables.** Publication encodes each entry's own table rooted at its complete callable type (`rowRegion`, `encodeRowTable` at one entry's roots) with deterministic numbering, replacing the module-wide `rows`; decoding checks each entry's table on its own. Obligation: `signatureAgrees_of_checks` and `signatureAgrees_of_checks_back` per entry, their premises unchanged (a realized source entry, empty graph environments, membership-preserving canonicalizers, two `matchStores` results). Control: an entry's table forged (a row dropped, a field changed) is refused at decoding or at the store-map check.
2. **The complete callable contract on the wire.** The entry carries the whole callable type, every signature with every effect field, and the importer's slot is checked against it (the consumer's store-map check), replacing `importedArrow`'s reconstruction from the importer's declaration and the footprint triple. `fresh` is carried with it: realization already compares a member's `fresh` with the row's (`layoutOwn`'s frame check), so no new lemma; `crossModule_safe`'s established slots (`ChosenSlots`, `EstablishedSlots`) quote the entry's type. Obligation: `entries_realized` and `crossModule_safe` at the new `Established` (entry type and table in place of the triple). Effect: an origin signature stronger than the importer's declaration (freshness) is accepted.
3. **Same-file entry reads.** A call within a file reads the callee's entry through the same consumer check, replacing `ordinarySlots`' footprint and `ensures` reads (`Front.withStandIns`, head inference's reads of `fr.units`) for the migrated forms; a callee not laid out is read at its declared contract, as across files. Obligation: `passFile_safe`'s layout with `layout.iface` the entry's type (`layoutOwn` one interface type per read); no new hypothesis. A unit verified today through a stand-in read of a callee `laidOut` leaves out becomes a measured loss, each a row in WORK.md.
4. **Regions.** The entry keeps `regions` (`keepingType` and `moduleArrow` stop erasing them); realization of a regional row. Obligation: a lemma deriving `RowSpec` for a row with regions from `RequestSafe`'s regional clause (docs/SINGLE-PASS-THEOREM.md, the regional clause), and `layoutOwn` comparing the member's regions with the row's. Control: forged regions refused.
5. **Rest parameters.** Eligibility admits a rest signature (`Claims/Imports.lean` eligibility), its row the code's packed calling convention. Obligation: `RowSpec` for a rest row from the member's request over the packed frame (`codeFrame` with the argument pack, which holds values and has no holes).
6. **Overloads.** One identity, every offered row, each realized by its own unit's check; publication requires every overload unit accepted. Obligation: `layoutOwn`'s rows loop over all `offerRows`, each with a realizing member (present); a new control publishing an entry with an overload's row omitted, refused.
7. **Constants holding functions** ([module constant entries](module-constant-entries.md)): the constant's literal laid out as a module function; the entry is the function unit's contract and the initialization's establishment of the binding. Obligation: the layout lemma for the literal's code; H5b stays the stated hypothesis (`KindMet` at `moduleCell`).
8. **Generics.** A scheme entry: binders, kinds, bounds and resolution in the entry's table (scheme rows), `layoutOwn`'s scheme exclusion lifted. Obligation, the largest: a theorem that a generic body checked once at its scheme's binders realizes `RowSpec` at every instance the consumer's store-map check admits. May split into binder-free instances first.
9. **Removal.** `importedArrow` for established reads, the `(footprint, onThrow, resultFootprint)` triple of `Established`, `qualified` stand-ins for migrated forms. Gate: every retained same-file form has its cross-file case with the same verdict (D6).

Every step keeps `make test` green. Boundary changes receive pipeline cases and forged-input controls; proof-covered facts need no duplicate tests. Full census comparison follows the project’s main-branch census policy.

## 8. Decisions

The owner's decisions on the questions this design raised:

1. **Acceptance target.** The redesign is judged by the same verdicts, every item processed once, much faster, and each change in a count explained. Reaching the old route's census count (596/755) is no criterion.
2. **Module initialization (H5b).** H5b stays a stated hypothesis; its typed-finish/world-extension proof is a separate obligation.
3. **Entries for functions held in module constants** are part of this redesign, in step 2 (one interface representation). Their design is [module constant entries](module-constant-entries.md).
4. **Recursion (D5).** No joint iteration over mutual cycles: a member of a cycle of two or more functions reads the others' unwritten interface parts at the worst case, and the cycle verifies when every member's own check passes. A self-recursive function keeps today's proposal, inside its own unit of work (section 3, "Demand and scheduling"). Basis (measured 2026-11-13 over the pipeline cases, a 22-file slice of tools/ and pretext, on `Front.edgesOf`'s cycles): reading every cyclic function's unwritten part at the ordinary effect loses 3, 2 and 2 verdicts, each from a self-recursive function whose walks find a footprint below the ordinary effect that a caller needs; reading only mutual cycles so loses none in any of the three corpora. No cycle crosses modules; in tools/, 49 of 88 cyclic functions state their effect.

## 9. Form-based decisions today

Every place in the front's import, extraction, proposal, publication, row, inference and realization code where a function's form, a class's name, a property's spelling or a value's shape decides whether it is read, proposed for, published, or how it is treated. Read from the code at `f741ed41`; `C/` is `lean/Verification/Source/Claims/`. Each row gives the condition and both sides. Where the plan of step 2 or section 2 of this document says otherwise, the code is what this table states and the row says so.

### Resolution of an imported binding (C1)

| Site | Condition | Holds | Fails |
| --- | --- | --- | --- |
| `tools/fragment-parse.mts:2738` (`importedModules`) | the imported value is no construct signature, has no type parameters and its type is one signature or an intersection of signatures (`callable`) | its module is a candidate for the fragment's `modules` | its module is not listed through this import |
| `tools/fragment-parse.mts:2740` | the declaration's module path starts with `typescript/lib/` or `tscert/` | not listed | — |
| `tools/fragment-parse.mts:2743` | with a project root: the path ends in `.ts`/`.mts`/`.cts`, not `.d.*ts`, no `node_modules` segment | listed | not listed |
| `tools/fragment-parse.mts:2752` | without a project root: the alias target's last declaration is a `FunctionDeclaration` with a body, in no declaration file and outside `node_modules` | listed | not listed (a `const f = () => …` export is not) |
| `C/Imports.lean:227` (`eligibleRead`) | the origin unit has no type parameters, no `rest` parameter and no parameter named `this` | continue | the read fails: "not eligible" |
| `C/Imports.lean:235` | no statement of the origin module's initialization or of any of its function bodies assigns the binding's name (`assignsStmt`), scanned for every read | continue | the read fails: "writes its binding" |
| `C/Imports.lean:238` | the imported value is no construct signature and has no type parameters | continue | the read fails: "not eligible" |
| `C/Imports.lean:242–259` | the origin unit states a guard: the declared type is an intersection of exactly a plain and a promise signature of the same actuals, receiver and effect | the plain signature and the promised type are compared | the read fails. The guard pair is admitted: section 2's "eligibility excludes guards/promises" is contradicted by the code, which refuses only a promise on the plain signature (line 264) |
| `C/Imports.lean:260` | the (plain) declared type is one `function` term with no `rest` and no `receiver` | continue | the read fails: "not eligible" |
| `C/Imports.lean:264` | the plain signature's effect states no promise | continue | the read fails |
| `C/Imports.lean:270,275,278,281` | the importer's precondition, postcondition, arity and `sameReading` agree with the origin unit's | the read resolves to the unit | the read fails |
| `C/Imports.lean:320` (`documentReads`) | `eligibleRead` returns an error | — | the import is silently omitted: no read, no located failure; the importer reads it at `ordinaryImport` |
| `C/Imports.lean:322` | a local name two imports bind | — | both omitted |
| `C/Imports.lean:377` (`importerReads`) | an importer function is generic, async, of a written effect, of a `rest` parameter, or a stand-in | its body's mentions are not followed when collecting reads | they are |
| `C/Extraction.lean:49,311` (`bodyModule`) | the declaration's module path ends in a source extension and not in a declaration extension | an import with no entry is read at `ordinaryImport` (ordinary effect, precondition kept) | read at its declared type |
| `C/Extraction.lean:17` (`importedSignatures`) | the declared type expands to one fixed signature, or a plain one and a promise one of the same actuals | `importedArrow` reconstructs a slot | `importedArrow` fails; with `lenient`, the import is read at its declared contract |
| `C/Extraction.lean:68` (`ordinaryImport`) | every signature assumes nothing (`assumesNothing`); else a variadic signature or an empty clause states something | read as written; else at the ordinary effect | refused: "read only at its module's entry" |
| `C/FragmentFront.lean:641` (`withNeverImports`) | the value's name starts with `%`, is `arrayPrototypeName`, is the file's own or qualified | skipped | an import of one fixed signature with an empty result and no promise is read at keep/keep |
| `C/FragmentFront.lean:1199` (`unboundReads`) | a name starts with `%` or `?`, or is `this` | not a module binding (an intrinsic) | followed |

### Proposal (C2)

| Site | Condition | Holds | Fails |
| --- | --- | --- | --- |
| `C/FragmentFront.lean:565` (`declarationWalks`) | a function is generic, async, of a written effect (`stated`), of a `rest` parameter, or a stand-in | no walk: it keeps the claim `fragmentClaims` gives (the ordinary effect unless written) | its body is walked and a footprint proposed |
| `C/FragmentFront.lean:589` | the function mentions its own name | up to three walks at the assumed footprint | one walk |
| `C/FragmentFront.lean:583` | `resultWithFootprint` accepts the result annotation | a returned function's footprint proposed | `top` |
| `C/FragmentFront.lean:74` (`writtenSchemes`) | a generic closure is a guard, async, or of a resolution-qualified binder; or a nested scheme annotation without a written result; or a rest that is no array | claimed at no scheme | claimed at its written scheme |
| `C/FragmentFront.lean:615,741` | a unit has no type parameters and is no initialization | it gets an ordinary slot (`ordinarySlots`) and an interface slot | a generic function is read through `generics` instead |
| `C/Extraction.lean:269` (`ordinarySlots`) | the written effect states regions | slot at the written footprint and regions | slot at the claim's footprint, the written `fresh` |
| `C/FragmentFront.lean:490` (`keepingType`) | the type expands to one clause; for the result footprint, the result is one clause of fixed signatures all at `top`, no `onThrow`, no promise | each signature's effect replaced (regions erased) and the result's footprint set | "a module function of no one signature"; result left as it is |
| `C/FragmentFront.lean:515` (`returnedFootprint`) | every return holds one clause of signatures | join of their footprints | `top` |
| `C/FragmentFront.lean:669,734,861` (`proposes`, `establishChecked`) | a module function's claim is more than the ordinary effect, or it states a postcondition or guard (`statesMore`) | its group is checked in the interface component | not checked there |

### Publication and realization (C3)

| Site | Condition | Holds | Fails |
| --- | --- | --- | --- |
| `C/FragmentFront.lean:893` (`establishEntry`) | the claim is the ordinary effect and the function states no postcondition or guard | no entry: "the ordinary effect" | entry candidate |
| `C/FragmentFront.lean:967` (`layoutOwn`) | the unit is the initialization | outside | — |
| `C/FragmentFront.lean:968` | the function has type parameters | outside: "a scheme" | — |
| `C/FragmentFront.lean:970` | its request is qualified | outside | — |
| `C/FragmentFront.lean:975–982` | a captured file function read at other than one type; its own interface read at several types or none | outside | — |
| `C/FragmentFront.lean:985` | its interface expands to one clause of signatures | continue | outside |
| `C/FragmentFront.lean:987` | the code's invocation kind (`convertsReceiver`: sloppy, else call) offers each row's receiver | continue | outside |
| `C/FragmentFront.lean:1014` (= `PassUnit.rowConditions`, `C/PassUnitRealize.lean:294`) | arity within the arguments, `belowRow`, no `freshObject`, no `requires`, no `elements`, no `receiverGrows`, no `elementWrite` | continue | outside: "the code's conditions" |
| `C/FragmentFront.lean:1019` | receiverless and a postcondition names slot 1 | outside | — |
| `C/FragmentFront.lean:1037` | the member's inputs equal `codeFrame arity p captures none` (no rest store, `C/PassUnitRealize.lean:436` assumes `c.store = none`) | continue | outside: a rest function is never laid out |
| `C/FragmentFront.lean:1050,1120` (`laidOut`) | the function is in the greatest set closed under captured callees | published | "not laid out" |
| `C/ModuleInterfaces.lean:22` (`encodeInterfaces`) | the document's `functions` | one entry per function | a callable held in a constant or class has none |
| `C/TypeComparison.lean:17–33` (`moduleValueType`) | an annotated constant: some signature of the initializer's type has the keep/keep effect (throws aside) and the same receiver, result and arguments as an annotated signature | that signature takes the initializer's effect | the annotation's effect |
| `C/Extraction.lean:295–304` (`freshConstructors`) | a global binding named `Error` declared as `Error` in `typescript/lib/lib.es5.d.ts` | its constructions allocate an unpublished identity | ordinary construction |
| `C/Extraction.lean:350,376`; `C/FragmentFront.lean:473`; `C/InterfaceRows.lean:146` (`genericClassNames`) | a constant whose initializer is a class with type parameters | no module constant, no self binding; read through `generics` | a module constant |
| `C/HeadInference.lean:469` (`typedArrays`), used at 668, 1320, 1337 | a constructor or referenced type named one of nine typed-array names | `length` is a view length; a construction's argument is its length | no fact |
| `C/HeadInference.lean:1321,1338` | a referenced type named `Array` or `ReadonlyArray`; a construction of `Array` | array length | no fact |
| `C/HeadInference.lean:321,486,810` | a method named `push`, `pop`, `shift`, `unshift`, `splice` (and `fill`, `copyWithin` at 486; `push` alone at 810) | the receiver's facts are killed (or, at 810, a push fact proposed) | kept |
| `C/HeadInference.lean:150,158` | a name starting with `%`, or `this` | no source-name fact | a fact |

`RegionInference.lean` and `InterfaceRows.lean` decide nothing by form beyond the rows above: region names are read from each callee's effect, and the reach of a row table follows its rows.

**Count.** 47 decisions, one per row: `fragment-parse.mts` 4, `Imports.lean` 10, `Extraction.lean` 6, `FragmentFront.lean` 21, `TypeComparison.lean` 1, `ModuleInterfaces.lean` 1, `HeadInference.lean` 4; `PassUnitRealize.lean`'s `rowConditions` is the row of `layoutOwn` that calls it; `RegionInference.lean` and `InterfaceRows.lean` 0.

**Where the plan differs.** The plan's typed-array lines (`C/HeadInference.lean:469,666,1312,1335`) are 469, 668, 1320, 1337, and the same functions also decide by the spellings `Array`/`ReadonlyArray` and by method names, which the plan does not list. Eligibility admits guards (above). The plan does not list the ordinary-effect entry omission (`establishEntry`), `withNeverImports`, `bodyModule`, `genericClassNames` or `writtenSchemes`' exclusions.
