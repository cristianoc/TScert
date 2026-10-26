# Census blocker cases

The input is the 121-program index in `../rewrite-loop/repros/index.json`, from the diagnostic rewrite loop over census commit `963ffa4`. The source worktree baseline is `3895490`. The cases commit is `4f7cfaf` on `blocker-cases`.

On 2026-10-25, all 121 original programs reproduce their recorded refusal families through this worktree's pipeline, with their original strict project settings and imports redirected to this worktree. No original program fails to reproduce. The reductions below have separately measured expectations in `pipeline/cases.mts`.

There are 45 kept cases: 42 gaps and 3 negatives. They represent 67 repros. Existing cases cover the remaining 54. Each input appears in exactly one disposition; shared census functions can appear in several causes because the rewrite loop uncovers successive refusals.

## Classification and evidence

The seven reports in `../blockers/` establish the mapped-type, API-default/conditional-member, named-view, Node-contract, module-constant, mixed-overload and field-assignment mechanisms. [Source restrictions](docs/SOURCE-FRAGMENT.md), [source contracts](docs/SOURCE-CONTRACTS.md) and [compiler API contracts](docs/COMPILER-API.md) distinguish missing machinery from excluded behaviour.

For the other groups, the evidence is the original source, its diagnostic (including the available and required type graphs), and a smaller program retaining the refusal. A cause names the missing source operation, contract or failed judgment demonstrated by that reduction; it does not assert an unproved implementation repair. In particular, the recursive host-shape and branch-join cases establish search gaps, not a claim that the calculus lacks a rule.

The sparse-map group is not grouped merely by its search message: its diagnostic graphs contain a sparse result where the written result requires readable elements. The callbacks call functions with no preservation contract. The array-widening group instead has readable stores with different invariant element contracts. The `every` group loses a promised element refinement, while the literal-result group widens a literal during generic result inference. These are separate causes.

Earlier unsupported contracts remain gaps: `blocker-entries-mixed-overloads` stops before the operand's possible compiler-object reflection is checked. The API value-import case uses the class only as a type; the existing retained-callback constructor negatives do not cover that safe form. The Node contract cases carry no claim that native declarations are audited specifications.

The three new negatives exercise distinct obligations:

- `blocker-in-field-narrowing`: a value satisfying the `asserts` arm may also own `guards` at an unrelated type; testing its presence cannot promise a number-valued child. Under Node, the kept function given `{ asserts: { value: 0 }, guards: "extra property" }` returns `undefined` despite its `number` result annotation.
- `blocker-guard-readonly-storage`: testing a readonly dictionary's contents does not give a writable field its invariant contract.
- `blocker-contextual-any`: a callback parameter context of `any` states no contract, a documented source restriction.

The ordinary and subclass Error options cases retain both lowering paths. The loop-completion cases retain a function with no exit and a closure whose loop exits by a tuple return; a repair of one path can miss the other. The compiler parent-loop and residual-join cases retain a back edge and a branch join respectively. The dictionary-member guard and recursive nullable-field cases exercise different forms of field refinement.

`pipeline/blocker-project/tsconfig.json` supplies the original strict, ES2022/bundler-resolution regime, the effect declarations and the front end's installed Node declarations. Package resolution uses the suite's existing examples installation link. A few reductions retain imports of the project's recursive type declarations: replacing them with a small nonrecursive type removes the recorded failure. Only cases, examples and this case project belong to `4f7cfaf`.

## Kept cases

| File | Kind | Cause | Census functions | Repros replaced |
| --- | --- | --- | --- | --- |
| [blocker-local-class.ts](pipeline/examples/blocker-local-class.ts) | gap | A class declared inside a function needs local class lowering. | `array-prototype.mts#arrayPrototype`<br>`array-prototype.mts#mergeRefusal`<br>`array-prototype.mts#primitivePrototype`<br>`array-prototype.mts#prototype` | `gate-statement-outside-the-fragment-classdeclaration-002.ts` |
| [blocker-annotated-pattern.ts](pipeline/examples/blocker-annotated-pattern.ts) | gap | A binding pattern needs its written annotation checked. | `claim-text.mts#lift`<br>`claim-text.mts#liftClause`<br>`claim-text.mts#liftLabels`<br>`claim-text.mts#liftSignatures`<br>`claim-text.mts#liftType`<br>`claim-text.mts#treeAtom`<br>`intrinsics.mts#iterationIntrinsic`<br>`regexp.mts#dispatchIntrinsic` | `annotated-pattern-007.ts` |
| [blocker-compiler-api-value-default.ts](pipeline/examples/blocker-compiler-api-value-default.ts) | gap | A value import used only as a type eagerly reads the imported class type-parameter default. | `compiler-channel.mts#abandon`<br>`compiler-channel.mts#abandonCompiler`<br>`compiler-channel.mts#compilerLedger`<br>`compiler-channel.mts#openCompiler`<br>`compiler-channel.mts#openFrontEndCompiler`<br>`compiler-channel.mts#privateClient`<br>`compiler-channel.mts#releaseCompiler` | `api-value-default-009.ts` |
| [blocker-weakmap.ts](pipeline/examples/blocker-weakmap.ts) | gap | A global from an unreviewed declaration origin needs a reviewed contract (WeakMap, Buffer and TextDecoder). | `compiler-channel.mts#query`<br>`files.mts#answerOf`<br>`files.mts#compilerFileSystem`<br>`files.mts#compilerText`<br>`files.mts#direntsOf`<br>`files.mts#direntsRead`<br>`files.mts#entriesOf`<br>`files.mts#entriesRead`<br>`files.mts#listDirectory`<br>`files.mts#nodeResolve`<br>`files.mts#observationsHold`<br>`files.mts#observePackageLinks`<br>`files.mts#observeResolution`<br>`files.mts#observeScope`<br>`files.mts#observed`<br>`files.mts#observedNoting`<br>`files.mts#remembered`<br>`files.mts#resolveObserved`<br>`files.mts#treeDigest`<br>`files.mts#validateLedger`<br>`wire-strings.mts#wireText` | `gate-the-global-weakmap-is-declared-in-typescript-lib-lib-es2015--010.ts`<br>`buffer-contract-063.ts`<br>`gate-the-global-textdecoder-is-declared-in-node-modules-types-nod-066.ts` |
| [blocker-nullable-field.ts](pipeline/examples/blocker-nullable-field.ts) | gap | A user guard on a dictionary member needs to refine the member reread, including an object-valued result. | `claim-text.mts#atomText`<br>`claim-text.mts#bareAtomText`<br>`claim-text.mts#printType`<br>`claim-text.mts#restElement`<br>`claim-text.mts#setLiterals`<br>`claim-text.mts#typeText`<br>`claim.mts#atom`<br>`claim.mts#decodeClaimType`<br>`diagnostic.mts#readDiagnostic` | `unsupported-a-field-read-at-its-contract-a-read-of-map-through-a--005.ts`<br>`unsupported-a-field-read-at-its-contract-a-read-of-bits-through-a-006.ts`<br>`unsupported-a-field-read-at-its-contract-a-read-of-length-through-008.ts`<br>`unsupported-a-field-read-at-its-contract-a-read-of-foreach-throug-052.ts` |
| [blocker-module-assignment.ts](pipeline/examples/blocker-module-assignment.ts) | gap | Assignments to module bindings need modeled module storage. | `compiler-processes.mts#compilerStarted`<br>`files.mts#fresh`<br>`files.mts#importLedger`<br>`files.mts#inconsistent`<br>`files.mts#inheritLedger`<br>`files.mts#kept`<br>`files.mts#nodeUnobservable`<br>`files.mts#note`<br>`files.mts#noteIn`<br>`files.mts#unobservable` | `reject-assignment-to-generations-which-is-not-a-mutable-local-021.ts`<br>`reject-assignment-to-staleprocess-which-is-not-a-mutable-local-060.ts`<br>`reject-assignment-to-retiringprocess-which-is-not-a-mutable-local-062.ts`<br>`reject-source-refusal-064.ts`<br>`reject-source-refusal-067.ts` |
| [blocker-error-options.ts](pipeline/examples/blocker-error-options.ts) | gap | Error construction needs a contract for the cause options argument. | `fragment-parse.mts#failingAsTool` | `gate-new-error-is-read-with-at-most-1-argument-s-082.ts` |
| [blocker-node-path-sep.ts](pipeline/examples/blocker-node-path-sep.ts) | gap | An imported property of an export-assigned Node module needs a reviewed constant contract. | `declaration-graph.mts#declarationOrigin`<br>`declaration-graph.mts#globalFunction`<br>`declaration-graph.mts#moduleIds`<br>`declaration-graph.mts#originOf`<br>`declaration-graph.mts#selectGlobal`<br>`family-activation.mts#activateGuards`<br>`family-activation.mts#activatedModules`<br>`family-activation.mts#activeGuards`<br>`family-activation.mts#checkInventory`<br>`family-activation.mts#checkedGuards`<br>`family-activation.mts#checkedInstallation`<br>`family-activation.mts#checkedInventory`<br>`family-activation.mts#declarationInventory`<br>`family-activation.mts#declarationsDigest`<br>`family-activation.mts#familyOfFile`<br>`family-activation.mts#guardOfExport`<br>`family-activation.mts#hostEnumObject`<br>`family-activation.mts#importedExport`<br>`family-activation.mts#importedGuard`<br>`family-activation.mts#installationPath`<br>`family-activation.mts#installations`<br>`family-activation.mts#isHostFile`<br>`family-activation.mts#loadedGuards`<br>`family-activation.mts#selectionGuard`<br>`family-activation.mts#tagEnumMatches`<br>`family-activation.mts#tagEnumObject`<br>`files.mts#compilerFileSystem` | `module-constant-sep-030.ts` |
| [blocker-api-indexed-method.ts](pipeline/examples/blocker-api-indexed-method.ts) | gap | The Parameters utility type needs the declared method signature recovered from an indexed class member. | `declaration-session.mts#update` | `gate-the-written-application-parameters-api-updatesnapshot-in-var-041.ts` |
| [blocker-node-hash-contract.ts](pipeline/examples/blocker-node-hash-contract.ts) | gap | Hash and stream declarations need reviewed contracts instead of synthesised members with no written origin. | `family-activation.mts#checkInventory`<br>`family-activation.mts#checkedInstallation`<br>`family-activation.mts#checkedInventory`<br>`family-activation.mts#declarationsDigest`<br>`family-activation.mts#digestOf`<br>`family-activation.mts#familyOfFile`<br>`family-activation.mts#installationPath`<br>`family-activation.mts#isHostFile`<br>`files.mts#fileDigest`<br>`files.mts#readAnswer`<br>`files.mts#readBytes`<br>`guard-closure.mts#guardClosure`<br>`host-families.mts#familyTable`<br>`unchecked.mts#isResult` | `crypto-synthesised-member-053.ts`<br>`gate-stream-in-node-modules-types-node-stream-d-ts-writable-a-mem-119.ts` |
| [blocker-node-buffer-contract.ts](pipeline/examples/blocker-node-buffer-contract.ts) | gap | Node filesystem and Buffer declarations need reviewed contracts that cover their conditional buffer types. | `family-activation.mts#declarationInventory`<br>`files.mts#attemptAnswer`<br>`files.mts#findPackage`<br>`files.mts#installed`<br>`files.mts#kindOf`<br>`files.mts#manifestField`<br>`files.mts#privateLauncher`<br>`files.mts#realOf`<br>`files.mts#realPath` | `buffer-contract-054.ts` |
| [blocker-import-meta.ts](pipeline/examples/blocker-import-meta.ts) | gap | Module metadata needs a source expression and its contract. | `family-activation.mts#installationRoot`<br>`family-activation.mts#installations` | `gate-expression-outside-the-fragment-metaproperty-055.ts` |
| [blocker-node-create-require.ts](pipeline/examples/blocker-node-create-require.ts) | gap | The imported createRequire signature needs the type reader to read its result type, NodeJS.Require. | `files.mts#loadModule` | `gate-a-qualified-type-reference-in-createrequire-070.ts` |
| [blocker-field-literal-context.ts](pipeline/examples/blocker-field-literal-context.ts) | gap | A property assignment needs to build its fresh array at the field storage contract. | `fragment-statements.mts#abrupt`<br>`fragment-statements.mts#block`<br>`fragment-statements.mts#controlStmt`<br>`fragment-statements.mts#declarations`<br>`fragment-statements.mts#forInStmt`<br>`fragment-statements.mts#forStmt`<br>`fragment-statements.mts#hoistTarget`<br>`fragment-statements.mts#hoisting`<br>`fragment-statements.mts#letPattern`<br>`fragment-statements.mts#markEarly`<br>`fragment-statements.mts#neverAssigned`<br>`fragment-statements.mts#patternStmt`<br>`fragment-statements.mts#protocolForOf`<br>`fragment-statements.mts#protocolPattern`<br>`fragment-statements.mts#readCannotThrow`<br>`fragment-statements.mts#readScope`<br>`fragment-statements.mts#statements`<br>`fragment-statements.mts#stmt`<br>`fragment-statements.mts#switchStmt`<br>`fragment-statements.mts#tryStmt`<br>`fragment-statements.mts#unassigned` | `search-expression-096.ts` |
| [blocker-entries-mixed-overloads.ts](pipeline/examples/blocker-entries-mixed-overloads.ts) | gap | Object.entries needs generic and plain reviewed overloads represented together; its gate refusal precedes checking whether the operand can be a compiler object. | `type-term.mts#classInstance`<br>`type-term.mts#constructorForms`<br>`type-term.mts#expandMapped`<br>`type-term.mts#indexKinds`<br>`type-term.mts#intersection`<br>`type-term.mts#mapped`<br>`type-term.mts#members`<br>`type-term.mts#promiseOf`<br>`type-term.mts#quantified`<br>`type-term.mts#readTypeTerm`<br>`type-term.mts#sameData`<br>`type-term.mts#sameIndex`<br>`type-term.mts#signature`<br>`type-term.mts#signatures`<br>`type-term.mts#statedResult`<br>`type-term.mts#statementOf`<br>`type-term.mts#substitute`<br>`type-term.mts#tuple`<br>`type-term.mts#typeTerm`<br>`type-term.mts#validateAnnotation`<br>`type-term.mts#visitType` | `object-entries-mixed-overloads-113.ts` |
| [blocker-node-default-import.ts](pipeline/examples/blocker-node-default-import.ts) | gap | An export-assigned Node module default import needs its merged declarations resolved. | `shadow-contracts.mts#shadowText` | `gate-typescript-found-2-declarations-for-path-104.ts` |
| [blocker-contextual-default-argument.ts](pipeline/examples/blocker-contextual-default-argument.ts) | gap | A contextual reference to a generic alias needs its omitted default argument completed. | `diagnostic-view.mts#presentObligation` | `gate-the-contextual-type-labels-does-not-state-every-declaration--047.ts` |
| [blocker-compiler-api-conditional-member.ts](pipeline/examples/blocker-compiler-api-conditional-member.ts) | gap | An API instance at the type argument false needs its conditional member type evaluated at that argument. | `declaration-graph.mts#clientErrors`<br>`declaration-graph.mts#withOwnProject`<br>`declaration-graph.mts#withProject`<br>`declaration-session.mts#asideForTests`<br>`declaration-session.mts#close`<br>`declaration-session.mts#discard`<br>`declaration-session.mts#inDeclarationAttempt`<br>`declaration-session.mts#incompatibility`<br>`declaration-session.mts#noteAutomaticCollection`<br>`declaration-session.mts#releaseDeclarationSession`<br>`declaration-session.mts#retainDeclarationSessions`<br>`declaration-session.mts#settleDeclarationSession`<br>`fragment-parse.mts#close`<br>`fragment-parse.mts#openFile`<br>`fragment-parse.mts#openText`<br>`fragment-parse.mts#projectFor`<br>`fragment-parse.mts#release` | `api-conditional-member-028.ts` |
| [blocker-compiler-api-type-node.ts](pipeline/examples/blocker-compiler-api-type-node.ts) | gap | A TypeNode found by the host guard needs its recursive host shape admitted at the declared TypeNode contract. | `declaration-graph.mts#computedAt`<br>`declaration-graph.mts#typeNodeAt` | `search-expression-034.ts`<br>`search-expression-035.ts`<br>`search-expression-036.ts` |
| [blocker-in-field-narrowing.ts](pipeline/examples/blocker-in-field-narrowing.ts) | negative | A presence test on a union of records permitting extra properties cannot establish the tested property type: the other arm may own that key at another type. | `fragment-guards.mts#guardOf`<br>`fragment-parse.mts#importedModules` | `unsupported-missing-field-guards-079.ts`<br>`unsupported-missing-field-istypeonly-085.ts` |
| [blocker-aliased-guard.ts](pipeline/examples/blocker-aliased-guard.ts) | gap | A Boolean binding holding a host guard result needs to carry its narrowing to the conditional branch. | `fragment-statements.mts#assignedSteps` | `unsupported-missing-field-left-086.ts` |
| [blocker-compiler-api-field-guard.ts](pipeline/examples/blocker-compiler-api-field-guard.ts) | gap | A loop needs to preserve a host child field narrowing for the read after the loop. | `fragment-support.mts#forInEntryReads` | `unsupported-missing-field-statements-093.ts` |
| [blocker-compiler-api-token-subtype.ts](pipeline/examples/blocker-compiler-api-token-subtype.ts) | gap | A binary operator token needs to meet the Node contract at a call. | `fragment-expressions.mts#chainComparison` | `search-expression-083.ts` |
| [blocker-compiler-api-generic-member.ts](pipeline/examples/blocker-compiler-api-generic-member.ts) | gap | A generic host node refined by a predicate needs its Node bound available for a method read. | `type-probe.mts#nodeAt` | `search-expression-109.ts` |
| [blocker-every-promise.ts](pipeline/examples/blocker-every-promise.ts) | gap | The every guard overload needs to carry its element promise to later callbacks. | `shadow-contracts.mts#prelude`<br>`shadow-contracts.mts#print`<br>`shadow-contracts.mts#printSignature`<br>`shadow-contracts.mts#statedSignatures` | `reject-source-direct-obligation-101.ts`<br>`reject-source-direct-obligation-102.ts` |
| [blocker-compiler-api-find-promise.ts](pipeline/examples/blocker-compiler-api-find-promise.ts) | gap | The find guard overload needs to expose the promised host node type. | `computed-types.mts#unionMembers`<br>`fragment-classes.mts#selfConstruction`<br>`fragment-classes.mts#staticPrivate`<br>`fragment-expressions.mts#hasInstanceAlong`<br>`fragment-expressions.mts#hasInstanceClass` | `unsupported-missing-field-node-023.ts`<br>`unsupported-missing-field-members-073.ts`<br>`search-expression-074.ts`<br>`search-expression-078.ts` |
| [blocker-nullable-field-argument.ts](pipeline/examples/blocker-nullable-field-argument.ts) | gap | A recursive traversal needs the tested nullable field read to meet its recursive value contract. | `declaration-graph.mts#externalStatements`<br>`declaration-graph.mts#promisedBinders`<br>`declaration-graph.mts#promisedMethods`<br>`declaration-graph.mts#promisedNames`<br>`fragment-support.mts#completes` | `search-expression-032.ts`<br>`search-expression-037.ts`<br>`search-expression-091.ts` |
| [blocker-infinite-loop-completion.ts](pipeline/examples/blocker-infinite-loop-completion.ts) | gap | A loop with no exit needs no implicit return obligation. | `namespace-members.mts#written` | `search-expression-099.ts` |
| [blocker-callback-literal-context.ts](pipeline/examples/blocker-callback-literal-context.ts) | gap | A map callback returning a record needs the expected discriminated result type on its literal. | `type-term.mts#emptyObject` | `search-expression-111.ts` |
| [blocker-regexp-capture-callback.ts](pipeline/examples/blocker-regexp-capture-callback.ts) | gap | A replacement callback needs the regex capture arguments admitted by its callable contract. | `regexp-shape.mts#decodeName`<br>`regexp-shape.mts#groupsOf`<br>`regexp-shape.mts#regexpShape` | `search-expression-098.ts` |
| [blocker-fresh-sort-effect.ts](pipeline/examples/blocker-fresh-sort-effect.ts) | gap | Sorting the fresh result of filter needs its store mutation recognised as confined to fresh storage. | `intrinsics.mts#enumIntrinsic`<br>`intrinsics.mts#enumMembersTerm` | `reject-source-effect-refusal-095.ts` |
| [blocker-closure-loop-result.ts](pipeline/examples/blocker-closure-loop-result.ts) | gap | A closure whose loop exits only by returning a tuple needs its inferred result to exclude implicit undefined. | `fragment-statements.mts#sites` | `search-expression-087.ts` |
| [blocker-callback-array-index.ts](pipeline/examples/blocker-callback-array-index.ts) | gap | A callback index and an iterator index need their array-index fact available at an indexed read. | `computed-types.mts#parameterMembers`<br>`declaration-graph.mts#mergedParameters` | `reject-source-refusal-022.ts`<br>`reject-source-refusal-038.ts` |
| [blocker-compiler-api-parent-loop.ts](pipeline/examples/blocker-compiler-api-parent-loop.ts) | gap | A loop updating a node to its parent needs the recursive host contract preserved across its back edge. | `fragment-classes.mts#staticInitOf`<br>`fragment-support.mts#jumpTarget` | `search-incoming-edge-or-heap-075.ts`<br>`search-expression-090.ts` |
| [blocker-compiler-api-residual-join.ts](pipeline/examples/blocker-compiler-api-residual-join.ts) | gap | Host tag refinements need compatible recursive claims when guard branches rejoin. | `fragment-expressions.mts#letWrites`<br>`fragment-expressions.mts#localValues`<br>`fragment-support.mts#writtenElement` | `search-incoming-edge-or-heap-077.ts`<br>`search-incoming-edge-or-heap-092.ts` |
| [blocker-recursive-union-join.ts](pipeline/examples/blocker-recursive-union-join.ts) | gap | Grouped switch cases need compatible claims for a recursive discriminated union at their shared return. | `type-term.mts#restRefusal` | `search-incoming-edge-or-heap-110.ts` |
| [blocker-compiler-api-optional-path-join.ts](pipeline/examples/blocker-compiler-api-optional-path-join.ts) | gap | A host optional-member test needs compatible path claims at the following closure binding. | `declaration-graph.mts#overlaidInterface` | `search-incoming-edge-or-heap-044.ts` |
| [blocker-guard-readonly-storage.ts](pipeline/examples/blocker-guard-readonly-storage.ts) | negative | Testing readonly dictionary contents does not establish writable field contracts (SOURCE-MODEL, writable string index signatures). | `type-graph.mts#isCallEffect`<br>`type-graph.mts#isClosedFootprint` | `search-expression-106.ts` |
| [blocker-compiler-api-node-list-metadata.ts](pipeline/examples/blocker-compiler-api-node-list-metadata.ts) | gap | A compiler node list needs its own metadata members represented beside its readonly array view. | `shadow-contracts.mts#rewriteSignature` | `unsupported-a-read-of-pos-on-a-union-of-an-array-and-a-record-tha-103.ts` |
| [blocker-array-finally-view.ts](pipeline/examples/blocker-array-finally-view.ts) | gap | A declared array read in a generic finally block needs its array method view retained. | `files.mts#withLedger` | `unsupported-a-read-of-splice-on-a-union-of-an-array-and-a-record--065.ts` |
| [blocker-compiler-api-map-spread.ts](pipeline/examples/blocker-compiler-api-map-spread.ts) | gap | A map of compiler nodes using their text method needs a dense result for a later spread. | `unchecked.mts#unstated` | `search-expression-116.ts` |
| [blocker-map-literal-result.ts](pipeline/examples/blocker-map-literal-result.ts) | gap | Generic map result inference needs to retain a literal in a callback result union before a later every call. | `fragment-expressions.mts#binary`<br>`fragment-expressions.mts#chainLink`<br>`fragment-expressions.mts#expr`<br>`fragment-expressions.mts#knownLocal`<br>`fragment-expressions.mts#lambda`<br>`fragment-expressions.mts#localArrow`<br>`fragment-expressions.mts#memberOf`<br>`fragment-expressions.mts#objectFields`<br>`fragment-expressions.mts#optionalChain`<br>`fragment-expressions.mts#template`<br>`fragment-expressions.mts#update` | `search-closure-expression-076.ts` |
| [blocker-compiler-api-contextual-host-shape.ts](pipeline/examples/blocker-compiler-api-contextual-host-shape.ts) | gap | A filter callback over object-literal members needs its contextual host shape covered by the offered signature. | `written-applications.mts#pairOf` | `reject-source-direct-obligation-121.ts` |
| [blocker-contextual-any.ts](pipeline/examples/blocker-contextual-any.ts) | negative | A callback context typed any states no contract (SOURCE-FRAGMENT, Functions, calls and methods). | `type-term.mts#classInstance`<br>`type-term.mts#constructorForms`<br>`type-term.mts#expandMapped`<br>`type-term.mts#indexKinds`<br>`type-term.mts#intersection`<br>`type-term.mts#mapped`<br>`type-term.mts#members`<br>`type-term.mts#promiseOf`<br>`type-term.mts#quantified`<br>`type-term.mts#readTypeTerm`<br>`type-term.mts#sameData`<br>`type-term.mts#sameIndex`<br>`type-term.mts#signature`<br>`type-term.mts#signatures`<br>`type-term.mts#statedResult`<br>`type-term.mts#statementOf`<br>`type-term.mts#substitute`<br>`type-term.mts#tuple`<br>`type-term.mts#typeTerm`<br>`type-term.mts#validateAnnotation`<br>`type-term.mts#visitType` | `gate-typescript-types-this-unannotated-closure-parameter-from-its-114.ts` |
| [blocker-error-super-options.ts](pipeline/examples/blocker-error-super-options.ts) | gap | Error subclass construction needs the cause options contract on its super call. | `declaration-graph.mts#importBindings`<br>`declaration-graph.mts#useProject`<br>`written-applications.mts#writtenApplications` | `gate-super-message-options-of-error-is-outside-the-fragment-its-o-025.ts` |

## Duplicates represented by kept cases

The first identifier in each kept row is the representative. The following additional repros have the same demonstrated cause; their function sets are included in that row's source header.

| Repros | Kept case | Shared cause |
| --- | --- | --- |
| `buffer-contract-063.ts`<br>`gate-the-global-textdecoder-is-declared-in-node-modules-types-nod-066.ts` | [blocker-weakmap.ts](pipeline/examples/blocker-weakmap.ts) | A global from an unreviewed declaration origin needs a reviewed contract (WeakMap, Buffer and TextDecoder). |
| `unsupported-a-field-read-at-its-contract-a-read-of-bits-through-a-006.ts`<br>`unsupported-a-field-read-at-its-contract-a-read-of-length-through-008.ts`<br>`unsupported-a-field-read-at-its-contract-a-read-of-foreach-throug-052.ts` | [blocker-nullable-field.ts](pipeline/examples/blocker-nullable-field.ts) | A user guard on a dictionary member needs to refine the member reread, including an object-valued result. |
| `reject-assignment-to-staleprocess-which-is-not-a-mutable-local-060.ts`<br>`reject-assignment-to-retiringprocess-which-is-not-a-mutable-local-062.ts`<br>`reject-source-refusal-064.ts`<br>`reject-source-refusal-067.ts` | [blocker-module-assignment.ts](pipeline/examples/blocker-module-assignment.ts) | Assignments to module bindings need modeled module storage. |
| `gate-stream-in-node-modules-types-node-stream-d-ts-writable-a-mem-119.ts` | [blocker-node-hash-contract.ts](pipeline/examples/blocker-node-hash-contract.ts) | Hash and stream declarations need reviewed contracts instead of synthesised members with no written origin. |
| `search-expression-035.ts`<br>`search-expression-036.ts` | [blocker-compiler-api-type-node.ts](pipeline/examples/blocker-compiler-api-type-node.ts) | A TypeNode found by the host guard needs its recursive host shape admitted at the declared TypeNode contract. |
| `unsupported-missing-field-istypeonly-085.ts` | [blocker-in-field-narrowing.ts](pipeline/examples/blocker-in-field-narrowing.ts) | A presence test on a union of records permitting extra properties cannot establish the tested property type: the other arm may own that key at another type. |
| `reject-source-direct-obligation-102.ts` | [blocker-every-promise.ts](pipeline/examples/blocker-every-promise.ts) | The every guard overload needs to carry its element promise to later callbacks. |
| `unsupported-missing-field-members-073.ts`<br>`search-expression-074.ts`<br>`search-expression-078.ts` | [blocker-compiler-api-find-promise.ts](pipeline/examples/blocker-compiler-api-find-promise.ts) | The find guard overload needs to expose the promised host node type. |
| `search-expression-037.ts`<br>`search-expression-091.ts` | [blocker-nullable-field-argument.ts](pipeline/examples/blocker-nullable-field-argument.ts) | A recursive traversal needs the tested nullable field read to meet its recursive value contract. |
| `reject-source-refusal-038.ts` | [blocker-callback-array-index.ts](pipeline/examples/blocker-callback-array-index.ts) | A callback index and an iterator index need their array-index fact available at an indexed read. |
| `search-expression-090.ts` | [blocker-compiler-api-parent-loop.ts](pipeline/examples/blocker-compiler-api-parent-loop.ts) | A loop updating a node to its parent needs the recursive host contract preserved across its back edge. |
| `search-incoming-edge-or-heap-092.ts` | [blocker-compiler-api-residual-join.ts](pipeline/examples/blocker-compiler-api-residual-join.ts) | Host tag refinements need compatible recursive claims when guard branches rejoin. |

## Existing coverage

These rows add no case. Existing classifications are left unchanged, including pre-existing negatives. A source-level refusal that prevents reaching a later obligation is described by the earlier cause here.

| Repros | Existing case | Cause |
| --- | --- | --- |
| `readonly-mapped-key-001.ts`<br>`readonly-mapped-key-027.ts`<br>`gate-a-mapped-type-s-value-names-its-key-in-typescript-lib-lib-es-040.ts`<br>`readonly-mapped-key-051.ts`<br>`readonly-mapped-key-057.ts`<br>`gate-a-mapped-type-s-value-names-its-key-in-typescript-lib-lib-es-069.ts`<br>`gate-a-mapped-type-s-value-names-its-key-in-typescript-lib-lib-es-100.ts` | [written-partial-argument-refused.ts](pipeline/examples/written-partial-argument-refused.ts) | The mapped value refers to its key; Readonly, Pick and Partial reach the same refusal in the mapped-type reader. |
| `compiler-api-named-view-020.ts`<br>`compiler-api-named-view-024.ts`<br>`compiler-api-named-view-033.ts`<br>`compiler-api-named-view-042.ts`<br>`compiler-api-named-view-045.ts`<br>`compiler-api-named-view-046.ts`<br>`compiler-api-named-view-117.ts` | [invalid-compiler-api-view-member.ts](pipeline/examples/invalid-compiler-api-view-member.ts) | A host member is absent from its reviewed named view (COMPILER-API L6); changing the name does not add a new boundary. |
| `unreviewed-global-011.ts`<br>`unreviewed-global-012.ts`<br>`unreviewed-global-043.ts`<br>`unreviewed-global-056.ts` | [library-math-random.ts](pipeline/examples/library-math-random.ts) | A library-global member read only through a reviewed overlay entry; the case's, `Math.random`, has one. |
| `search-expression-004.ts`<br>`search-expression-013.ts`<br>`search-expression-014.ts`<br>`search-expression-015.ts`<br>`search-expression-016.ts`<br>`search-expression-017.ts`<br>`search-expression-018.ts`<br>`search-expression-019.ts` | [invalid-native-map-mutation.ts](pipeline/examples/invalid-native-map-mutation.ts) | The diagnostic type graphs distinguish sparse map results from readable result contracts. The callback invokes an unrestricted supplied or declared function; it may mutate the input array. Object allocation versus return does not change this missing preservation obligation. |
| `unsupported-field-read-on-non-object-026.ts` | [in-primitive-refused.ts](pipeline/examples/in-primitive-refused.ts) | A typeof-object test on unknown supplies no object-family contract for the subsequent property-presence/read operations. |
| `unsupported-missing-field-gettypes-031.ts` | [invalid-compiler-api-sync-guard.ts](pipeline/examples/invalid-compiler-api-sync-guard.ts) | The exact imported isUnionType/getTypes form already has a case; the sync guard has no audited promise (COMPILER-API T7). |
| `reject-unsupported-source-expression-039.ts` | [in-inherited-refused.ts](pipeline/examples/in-inherited-refused.ts) | A built-in inherited name needs prototype membership represented; this repro uses Function.prototype/name rather than Object.prototype. |
| `reject-source-refusal-048.ts`<br>`reject-source-refusal-071.ts` | [number-call-and-members.ts](pipeline/examples/number-call-and-members.ts) | Number is used both as a function and through members; no combined callable-with-methods clause. |
| `search-expression-049.ts` | [invalid-assertion-promise.ts](pipeline/examples/invalid-assertion-promise.ts) | The minimizer leaves an empty assertion function; its argument is not established to be the promised tuple. |
| `reject-source-refusal-050.ts` | [invalid-dictionary-inherited-key.ts](pipeline/examples/invalid-dictionary-inherited-key.ts) | A dynamic string key may name an inherited Object.prototype member absent from the modeled dictionary. |
| `gate-instanceof-whose-right-operand-is-not-a-class-declared-at-th-059.ts` | [instanceof-foreign-constructor-refused.ts](pipeline/examples/instanceof-foreign-constructor-refused.ts) | An imported constructor supplies no local prototype guarantee; the documented restriction already has a case. |
| `reject-source-refusal-061.ts` | [invalid-key-adding-parameter-write.ts](pipeline/examples/invalid-key-adding-parameter-write.ts) | Adding an optional key through an alias may change an object another reference holds. |
| `unsupported-missing-field-parameters-072.ts`<br>`search-expression-120.ts` | [filter-guard-value-refused.ts](pipeline/examples/filter-guard-value-refused.ts) | A guard passed as a value to filter does not supply its narrowing to the result; the existing gap covers both later reads and result contracts. |
| `gate-a-statement-within-on-an-overloaded-declaration-is-outside-t-081.ts` | [invalid-stated-overload-value-import.ts](pipeline/examples/invalid-stated-overload-value-import.ts) | A Within statement on an overload has no certification unit, the documented stated-effect restriction. |
| `reject-source-effect-refusal-084.ts` | [invalid-method-effect-unstated-dependency.ts](pipeline/examples/invalid-method-effect-unstated-dependency.ts) | The minimizer inserts an unrestricted ambient call into a function promising store preservation; the promised effect is not established. |
| `gate-the-contextual-record-name-string-pos-span-type-typeterm-res-088.ts` | [closure-contextual-anonymous-instance-refused.ts](pipeline/examples/closure-contextual-anonymous-instance-refused.ts) | An instantiated anonymous record has an optional member whose written contract cannot be recovered from the compiler API. |
| `gate-a-closure-capturing-a-for-loop-s-let-binding-is-outside-the--089.ts` | [for-let-capture-refused.ts](pipeline/examples/for-let-capture-refused.ts) | A closure captures a for-loop let; per-iteration binding copies have no lowering. |
| `search-expression-094.ts`<br>`search-expression-115.ts` | [named-invariance.ts](pipeline/examples/named-invariance.ts) | A mutable array of one TypeTerm arm is stored as a mutable array of the whole union; widening would permit writes invalidating the narrower alias. |
| `reject-source-direct-obligation-097.ts` | [invalid-field-call-effect.ts](pipeline/examples/invalid-field-call-effect.ts) | An unrestricted callback called from find may shrink the array; find can then pass undefined to a parameter annotated at the element alone. |
| `gate-the-namespace-import-nodemodule-is-used-only-through-member--105.ts` | [invalid-namespace-import-value-value-import.ts](pipeline/examples/invalid-namespace-import-value-value-import.ts) | A namespace object is passed whole, outside the supported named-member import form. |
| `gate-exclude-at-its-arguments-is-objectclause-whose-part-refs-fir-107.ts` | [computed-conditional-selection-refused.ts](pipeline/examples/computed-conditional-selection-refused.ts) | The computed result is not a selection of whole written union arms; a defaulted generic instance changes those arms. |
| `search-closure-expression-108.ts` | [invalid-angle-bracket-assertion.ts](pipeline/examples/invalid-angle-bracket-assertion.ts) | The minimizer leaves a bare cast from a JSON union to a writable number array; no preceding checks establish it. |
| `search-expression-118.ts` | [invalid-compiler-api-view-overload.ts](pipeline/examples/invalid-compiler-api-view-overload.ts) | The Checker view lists the single-node getTypeAtLocation overload, not its array overload. |
| `reject-source-direct-obligation-003.ts` | [named-implicit-index.ts](pipeline/examples/named-implicit-index.ts) | Object.values of the finite mapped primitiveOverlay has no declared index contract for its other enumerable keys. Its plain reviewed result contains unknown; the later flatMap callback demands arrays. The existing implicit-index refusal covers that missing structural guarantee. |
| `search-expression-068.ts` | [object-values-caught-refused.ts](pipeline/examples/object-values-caught-refused.ts) | Object.values of unknown narrowed only by typeof object cannot exclude restricted host values (COMPILER-API R8). |
| `search-expression-080.ts` | [invalid-set-iterator-construction.ts](pipeline/examples/invalid-set-iterator-construction.ts) | The reviewed Set constructor accepts arrays and strings; a non-array iterable runs its iterator, the documented exclusion already exercised by a Map iterator. |
| `gate-the-global-reflect-is-not-an-annotated-variable-058.ts` | [invalid-node-dirent-test-replaced.ts](pipeline/examples/invalid-node-dirent-test-replaced.ts) | Reflect is outside the reviewed globals because its property operations can invoke unstated getters; the existing case exercises the same gate refusal. |
| `unsupported-missing-field-modulespecifier-029.ts`<br>`unsupported-missing-field-typeparameters-112.ts` | [invalid-compiler-api-js-typedef.ts](pipeline/examples/invalid-compiler-api-js-typedef.ts) | The host guards include JavaScript declaration kinds whose corrected shape lacks TypeScript-only members (COMPILER-API R3); the existing typedef case exercises this broadening. |

## Reproduction limits

No original refusal is unreproduced. Several overly small attempts verify: a plain nullable field test, a local defaulted alias, a single guarded compiler child read, and a direct binary-token argument. The kept reductions retain respectively the user guard or recursive traversal, the imported contextual alias, the intervening loop, and the surrounding expression context needed for the failure. The token-argument case retains the larger expression context: smaller direct calls verify; its failed subtype judgment is reproduced without claiming an isolated implementation defect. A successful smaller program is not evidence that the original blocker is covered.

The loop's generated placeholders can weaken a program: the empty assertion function in repro 049, bare cast in 108, and unrestricted call in 084 fail obligations their reduced bodies do not establish. They are assigned to existing negative coverage. The module-assignment case uses an actual mutable module binding, preserving the motivating census operation rather than the minimizer's `declare const` stand-ins.

## Validation

- Original repros: 121 refusal families reproduced on 2026-10-25.
- `make cases P=blocker-`: 45 of 45 as expected; 42 named gaps and 3 negatives.
- `node tests/json-field-names.mts`: 8 comparisons agree across TypeScript, Lean and OCaml.
- `node tests/docs.mts`: 41 documents, 447 citations in code, 0 problems.

The case runner requires generated fixture links local to the worktree. Six inherited installation links through main are replaced by the runner's relative links or local fixture directories; their targets in main are untouched, and these ignored installation files are outside the commit.

No trusted implementation, verifier, producer or gate is part of `4f7cfaf`. No push or merge is part of this task.

## Negatives in tools/

Audit date: 2026-10-25. All three examples remain negatives. The source
repairs preserve the values produced by the front end's constructors and
readers; none establishes that an entire census function verifies.
[Source rewrites](docs/SOURCE-REWRITES.md) owns the general rewrite rules.
Line numbers below are before (`4f7cfaf`) → after this change.

### blocker-in-field-narrowing

**Answer.** `guardOf` really selects a child type by the presence of
`guards` on an open record union. Its producer constructs exclusive
alternatives, but the declared `CallPromise` contract does not state that
exclusivity. The restriction is right: the small example returns
`undefined` for `{ asserts: { value: 0 }, guards: "extra property" }` despite
its `number` annotation. This is a contract weakness in the source; the
counterexample does not show that the front end's own constructors produce
such an object.

`importedModules` is different: it checks `clause.isTypeOnly === true`, so
it does not infer a child's type from presence alone. The case's
counterexample does **not** transfer to that function. Its old read is
nevertheless outside the declared compiler host view: `ImportClause`
exposes `phaseModifier`, not `isTypeOnly`. The compiler's shared runtime
node implements `isTypeOnly` as its low phase bit and `phaseModifier` as a
phase enum; ordinary and type imports give identical answers under the
replacement. The negative remains valid, while its mapping to
`importedModules` needs this separate host-contract explanation.

**Change.** An internal alternative states that its selection field has
no defined value on the other arm (`field?: never`); selection tests
`field !== undefined`. This states the disjointness the existing
constructors provide, without adding runtime keys. `CallPromise` retains a
JSON dictionary contract as well: an optional field cannot admit a
non-JSON value. Import-clause readers use the declared phase enum.

| File, lines before → after | Before | After |
| --- | --- | --- |
| `tools/declaration-types.mts:17 → 18–19` | Open `guards` / `asserts` alternatives | Opposite selection fields optional at `never`, readonly children, JSON object contract |
| `tools/fragment-guards.mts:28 → 28` | `"guards" in promise` | `promise.guards !== undefined` |
| `tools/type-graph.mts:63–64 → 63–64` | Presence selects each promise in `samePromise` | Defined-value tests at the exclusive contract |
| `tools/compiler-channel.mts:206,257–259,273,286,297,317–318 → same` | Open installation / identity / failure alternatives selected with `in` | Declared absent selection fields and defined-value tests in `identify`, `current`, `compilerChoice`, `launcher`, `openFrontEndCompiler` |
| `tools/fragment-parse.mts:1044,1144,1171 → same` | `LoweredModule` success has no constraint on `refused`; readers select by `in` | Success declares `refused?: never`; `lowerModuleText` and `parseModules` test its value |
| `tools/written-applications.mts:117,138,142 → same` | `nodes` / `inferred` selected by presence | The `nodes` arm declares `inferred?: never`; defined-value tests retain `null` as a real inferred result |
| `tools/fragment-support.mts:224 → 224`; `tools/fragment-expressions.mts:233,237,773–774 → 233,237,773–777` | Open field / spread alternatives | Exclusive `spread` / `name` fields, defined-value selection, explicit literal type for the computed-field marker |
| `tools/family-activation.mts:447,456 → same`; `tools/declaration-graph.mts:2117 → 2115` | A resolved program can carry an unconstrained `description` | Program result declares `description?: never`; import and re-export readers test its value |
| `tools/declaration-graph.mts:2805,3969 → 2803,3967` | Global definition / constructor selected with `in` | Definition result declares `construct?: never`; defined-value selection |
| `tools/fragment-parse.mts:2110 → 2110`; `tools/namespace-members.mts:97 → 97`; `tools/declaration-graph.mts:383–385,1080 → 383,1078` | `"isTypeOnly" in clause && clause.isTypeOnly === true` | `clause.phaseModifier === ts.SyntaxKind.TypeKeyword` in all four import-clause readers |

**Scope audit.** A grep of `in` tests across every `tools/*.mts` identifies
all the internal open-union selectors above. Remaining presence tests
inspect JSON dictionaries and then validate their contents, check a value
with equality or a predicate, or inspect generic compiler-node children.
They do not select an internal record alternative by assuming that another
arm lacks an unmentioned field. The JSON decoder's `"guards" in promise`
is retained: it reads `JsonRead` and checks the nested object and numeric
parameter before returning a Boolean.

### blocker-guard-readonly-storage

**Answer.** Both `isClosedFootprint` and `isCallEffect` really promise
writable fields from readonly JSON observations. The restriction is right:
checking the current value does not establish the invariant contract of a
writable location. For example, an alias whose writable field is restricted
to `"keep"` can pass the small guard; the returned writable
`"keep" | "any"` view would permit writing `"any"`, invalidating that alias.
The production consumers read these fields, so the repair changes their
permission contract without changing their computations or the guard tests.

**Change.** `tools/declaration-types.mts:14,17,25 → 15,18–19,27–28`
declares the footprint fields, effect fields, promise field, and parameter
field readonly. The guards' result types therefore promise readonly views
all the way down. `pipeline/test.mts:3565,3570` constructs replacement
effects with object spread instead of assigning their `promise` or
`footprint` fields; the forged documents contain the same values.

**Scope audit.** Grepping the predicates over `JsonRead` / `JsonValue`
finds these two writable structural promises. The other object/list guards
already return `JsonObject` or readonly lists; the primitive guards return
primitive types. No production assignment to the effect or footprint
fields needs a replacement.

### blocker-contextual-any

**Answer.** `sameData` really inherits `[string, any]` from the standard
`Object.entries(object)` overload in its unannotated filter callback.
The other 20 named census functions include `sameData` in their local
dependency closure; they do not each contain a separate callback of this
form. The restriction is right: an `any` context states no contract, even
though this particular body only compares the value and passes it to a
reader accepting `unknown`. An explicit `unknown` contract states exactly
what those operations need.

**Change.** `tools/type-term.mts:1108 → 1108` annotates the filter entry
`([k, v]: [string, unknown])`. The repository-wide `Object.entries` grep
also finds the same implicit callback contract in the local `canonical`
reader of `mergeRefusal`: `tools/array-prototype.mts:723–724 → 723–724`
annotates both its filter and its subsequent map entry `[string, unknown]`.
Callback bodies and evaluation order are unchanged.

**Scope audit.** The other `Object.entries` callbacks in `tools/` have
explicit `[string, unknown]` parameters or read through an explicitly typed
entries variable. The remaining uses are a JSON dictionary read or a
`for...of` iteration, not an unannotated callback parameter receiving the
object overload's `any` context.

### Census slices

The commands use `TSCERT_STEP_LIMIT=300 node dev/census.mts --dir tools
--files <files> --functions <functions> --out <scratch> --record <record>`.
The baseline is `4f7cfaf`; the after record uses the final edited sources.
The main selection contains all 25 census functions named for the three
negatives and the additional affected functions and dependents. Supplemental
baseline selections cover `namespaceMembers`, `importBindings`, `locate`,
`decodeGraph`, `parseModules`, and `collectDeclarations`. The last two use
an archive of `4f7cfaf` inside this worktree, with the same built verifier
and producer. Comparisons use `node dev/census.mts report
<before>,<supplemental-before>,<archive-before> <after>`.

`samePromise` and `compilerChoice` are module arrow bindings: the census
slicer enumerates function declarations, so they have no standalone slice.
Their containing modules are covered by type checking, the case suite,
and controls. The slice results below concern whole dependency closures;
an earlier refusal can hide the pattern this audit repairs.

Measured on 2026-10-25: **0 of 48 verified → 0 of 48 verified**; no gained
or lost verified slice, and **0 → 0 timeouts**. Verified statement coverage
is 0 of 5,298 → 0 of 5,301 statements in this selected inventory.
These are selected slices, not a census of all `tools/`.

| File / functions | Before | After | First refusal before → after |
| --- | --- | --- | --- |
| `array-prototype.mts` — `arrayPrototype`, `primitivePrototype`, `mergeRefusal`, `prototype` | unsupported/source | unsupported/source | gate: a mapped type's value names its key in typescript/lib/lib.es5.d.ts#Readonly for Readonly (same) |
| `compiler-channel.mts` — `identify`, `current`, `launcher`, `locate` | unsupported/source | unsupported/source | gate: process.platform is not in the reviewed overlay of library globals: readonly platform: Platform; (same) |
| `compiler-channel.mts` — `openFrontEndCompiler` | unsupported/source | unsupported/source | gate: a type parameter default of an imported value is outside the fragment: API (same) |
| `declaration-graph.mts` — `selectGlobal` | unsupported/source | unsupported/source | gate: sep is not an annotated constant, function or class (same) |
| `family-activation.mts` — `importedGuard`, `importedExport` | unsupported/source | unsupported/source | gate: sep is not an annotated constant, function or class (same) |
| `fragment-expressions.mts` — `expr`, `objectFields` | unverified/search | unverified/search | reject: closure expression claim: evidence search failed (same) |
| `fragment-guards.mts` — `guardOf` | unsupported/proposal | unverified/search | unsupported: missing field guards → reject: source expression obligation: evidence search failed: no derivation of its node-typing claim |
| `fragment-parse.mts` — `lowerModule`, `lowerModuleText`, `lowerFile`, `parseModules` | unsupported/source | unsupported/source | gate: a statement (Within) on an overloaded declaration is outside the fragment: resolutionSlots (same) |
| `fragment-parse.mts` — `importedModules` | unsupported/proposal | unsupported/proposal | unsupported: missing field isTypeOnly → unsupported: field read on non-object |
| `type-graph.mts` — `isClosedFootprint`, `isCallEffect` | unverified/search | unverified/search | reject: source expression obligation: evidence search failed: the promised argument is not within the promise at this return (same) |
| `type-term.mts` — `visitType`, `validateAnnotation`, `typeTerm`, `readTypeTerm`, `constructorForms`, `mapped`, `expandMapped`, `substitute`, `tuple`, `intersection`, `signature`, `quantified`, `signatures`, `statedResult`, `statementOf`, `promiseOf`, `members`, `sameIndex`, `sameData`, `indexKinds`, `classInstance` | unsupported/source | unsupported/source | gate: Object.entries selects a generic statement beside other overloads (same) |
| `written-applications.mts` — `writtenApplications` | unsupported/source | unsupported/source | gate: super(message, options) of Error is outside the fragment: its options are not stated (same) |
| `declaration-graph.mts` — `importBindings` | unsupported/source | unsupported/source | gate: super(message, options) of Error is outside the fragment: its options are not stated (same) |
| `namespace-members.mts` — `namespaceMembers` | unsupported/proposal | unsupported/proposal | unsupported: field read on non-object (same) |
| `type-graph.mts` — `decodeGraph` | unsupported/source | unsupported/source | gate: Exclude does not select whole written union arms (ObjectClause) (same) |
| `declaration-graph.mts` — `collectDeclarations` | unsupported/source | unsupported/source | gate: Symbol.checkFlags is outside the named view Symbol of the compiler-API contract (compiler-api.mts, reading rule 4) (same) |

The readonly guards still fail to establish their promised argument in search.
The contextual-any functions stop earlier at the mixed-overload
`Object.entries` gap. `guardOf` reaches a node-typing obligation in search;
`importedModules` reaches a different field-read refusal. None of these
measurements justifies marking a motivating function verified.

### Validation of the source repairs

On 2026-10-25:

- `(cd tools && npx tsc -p tsconfig.json)`: pass.
- `node tools/unchecked.mts`: zero errors, zero `any` or `any flow`;
  all 31 assertions have reasons.
- `node tests/json-field-names.mts`: all 8 comparisons agree.
- `node tests/docs.mts`: 41 documents, 447 code citations, zero problems.
- `make suite`: 2,188 of 2,188 cases as expected; 2,832 functions verified,
  1,160 negative controls, 212 named gaps.
- `make test`: 19 suites passed, zero failed; all 153 controls passed.
- The three negatives retain their expected refusals. The 48 selected
  census slices have no verified outcome or timeout before or after.

The source-repair commit is titled
`State the contracts used by the front end's negative patterns`.
Its commit record passes the glossary-only readability check. The owner
reviews before merge; this task includes no push or merge.
