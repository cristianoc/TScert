# Verification work

This is the work ledger for the independent verifier: open work, the reason
each item is open and when it closes. [DESIGN](docs/DESIGN.md) states the
architecture and decisions; [the source boundary](docs/SOURCE-FRAGMENT.md) owns
supported-fragment restrictions.

## Next steps

### Status

Progress is recorded here and nowhere else. A commit that moves an item
updates its row. The prose under [open work](#open-work) describes each item's
design, not its progress.

| Item | State | Closed when |
| --- | --- | --- |
| [A connection to ECMA-262](#a-connection-to-ecma-262) | open | the host's stated types are lemmas of a mechanized specification |
| [Constructor rests](#constructor-rests) | open | a constructor with a rest parameter is constructed and its variadic construct signature introduced |
| [Class offers across units](#class-offers-across-units) | open | a module class passed by a module function to a variadic construct signature verifies |
| [Generic methods left](#generic-methods-left) | open | `class-generic-method-bounded-refused` verifies, and members binding different numbers of binders relate |
| [Contract completeness](#restoring-completeness) | open | effect inference covers the rest wrappers, call forms and nested heap operations it is conservative for |
| [Slices of the value universe](#universe-slices) | open: a design, under review (2026-10-19) | `typeof v === "object" && v !== null` narrows `unknown`, and the guards over `unknown` promise what their tests establish |
| [A guard's promise on a field](#guard-promise-field) | open | `str(o.name); o.name.length` verifies: an assertion or a guard on a field narrows the field's current content |
| [A guard's answer held in a constant](#guard-answer-constant) | open | `const ok = isRecord(v); if (ok) return v;` verifies |
| [Generic equality in a condition](#generic-equality-condition) | open: an investigation, cause unknown | `if (left !== right) return 1;` with `left, right: T` verifies, as `return left !== right` does, and the Boolean-return lowering applies to every function's return |
| [A negated first read of an element](#negated-first-read) | open: an investigation, cause unknown | `const d = list[0]; if (!d.initializer) return -1;` over a program record verifies |
| [A literal guard over `JsonValue \| undefined`](#literal-guard-json-read) | open: an investigation, cause unknown | `guard-literal-json-read-refused` verifies |
| [Guard overloads beyond `filter`'s](#guard-overloads) | open | `shadow-contracts.mts`'s `print`, which reads its array at `string[]` after `every` answers `true` at a guard, and `filter-guard-value-refused` verify |
| [`filter`'s guard overload](docs/SOURCE-CONTRACTS.md#prototype-contracts) | closed: `filter` is stated at TypeScript's guard overload (`native-guard-filter`) and a guard closure is claimed at the longer promise signature it is passed at (`offer-promise`); `filter-guard-callback` and `compiler-api-filter-guard` verify, `invalid-filter-guard-promise` is refused (run under Node), forged promise rows refused in search and in checking (2026-10-21, [slice measurement](#census-filter-guard)) | `fragment-statements.mts#protocolPattern` and `fragment-statements.mts#patternStmt` move past "closure signature claim is outside the source annotation" |
| [Footprints](#footprints) | open: the seven programs decided (2026-10-17) | every application form has a checked bound |
| [Keys known only at run time](#keys-known-only-at-run-time) | open | the writes listed there are typed |
| [Module composition](#module-composition) | open: certified imports checked, their units' composition reviewed (2026-10-18) | a Lean theorem composes units certified against each other's signatures |
| [Decoders' dictionary reads](#decoders-dictionary-reads) | open: the decoders take parsed JSON (2026-10-18); in `calculus` 12 of 15 functions verify, and `decodeTerm`, `decodeCode` and `termsOf` verify in 10.0 s of evidence search with candidate selection and the answered requests threaded through the document's search, 25.2 s without any reuse (user time, median of 3, 2026-10-19) | the decoders of `calculus`/`control-flow` verify in their modules within the limit |
| [Function declarations in bodies](docs/SOURCE-MODEL.md#lexical-bindings-before-initialization) | open | `function-declaration-in-body-refused` verifies: a function declared in a body is created at its block's entry, and a call of it before the block's bindings are initialized reaches their checked accesses |
| [Optional-field truthiness over unions](#optional-field-truthiness) | closed: checked read witnesses (2026-10-20) | `optional-field-truthiness-union-refused` verifies |
| [Exceptional footprints](#exceptional-footprints) | open: handler facts across a throw | a call's footprint on a throw carries an effect through a handler, with `checkJson_safe` concluding it |
| [Iteration left open](#iteration-left-open) | open | the iteration forms listed there are lowered |
| [Enum-member case labels](#enum-member-case-labels) | open | `switch-enum-case-narrowing` verifies |
| [Family identity controls](docs/HOST-FAMILIES.md#identity-through-program-code) | closed: each control verifies or is refused as stated, the negatives with a counterexample run under Node, and forged claims of `{ node }`, of a callback's result, of a re-exported guard's `false` edge and of a guard's wrapper at a node type refused in search and in checking (2026-10-20) | — |
| [A generic method's instance at a union of arms](#generic-instance-union-arms) | open: an investigation, cause unknown | `compiler-api-node-callback-inline` verifies |
| [Compiler enum binding identity](docs/HOST-FAMILIES.md#activation) | closed: all seven allowed enums require the audited runtime object through Node resolution, including program re-exports; 14 positive bindings verify and 14 mismatched bindings are refused with Node counterexamples (2026-10-20) | — |
| [Instance candidate growth](lean/Verification/Tests/InstanceGrowthControls.lean) | closed: a shared 64-patch budget covers fixed and variadic targets before combinations are constructed; controls with 24 ambiguous targets produce at most 66 candidates (2026-10-20) | — |
| [A family's installation](docs/HOST-FAMILIES.md#activation) | closed: each description names its package, installation and digest; the front end activates every active description's installation by that data, the compiler API's among them, refusing another digest, version or an installation Node does not find; the string-tagged stand-in activated by its description alone beside the compiler API's (2026-10-20) | — |
| [Paths at an entry beyond one member](docs/HOST-FAMILIES.md#entries) | closed: an entry's witness of a path reads from its prefix's, one checked link per segment; `compiler-api-entry-path` verifies, the forged chains are refused, each accepted with its check disabled (2026-10-20) | — |
| [Reads at an index computed from the length](docs/PROGRAM-TYPING.md#reads-at-an-index-from-the-length) | closed: a node list read at a `number` key is `%ElementAt%`'s, at its element type or `undefined`; `array-last-element` and `compiler-api-node-list-index` verify, the eleven bypasses listed there are refused, each run under Node (2026-10-22) | `fragment-statements.mts#protocolPattern` and `fragment-statements.mts#patternStmt` move past "a numeric array key needs a proved array-index singleton" |
| [A family guard's test in a guard's Boolean return](docs/SOURCE-ELABORATION.md#derived-source-forms) | closed: a family guard's call is a Boolean by its form; `compiler-api-guard-and-return` verifies, `invalid-compiler-api-guard-and-promise` and `invalid-compiler-api-guard-or-promise` are refused, each run under Node (2026-10-22) | `readCannotThrow`'s `(d): d is ts.FunctionDeclaration => ts.isFunctionDeclaration(d) && d.name?.text === id.text` verifies |
| [The search past 60 s on `fragment-statements.mts`](#fragment-statements-search) | closed: `protocolPattern`'s and `patternStmt`'s searches take 13 s each in their census and alone, where they took 88 s; both then stop at `statements`' `list.findIndex((s) => gate.abrupt(s))` (2026-10-22, [slice measurement](#census-index-from-length)) | `fragment-statements.mts#protocolPattern` and `fragment-statements.mts#patternStmt` finish their search within the census's 60 s limit |
| [The search past 100 s on `fragment-statements.mts`](#fragment-statements-search-rows) | closed: `protocolPattern`'s search on 526bf6e's artifacts takes 27 s of CPU alone, where it took 103 s, with the same refusal (2026-10-22, load averages 3 to 36) | `fragment-statements.mts#protocolPattern` and `fragment-statements.mts#patternStmt` finish their search within 30 s alone |
| [A completed read narrows its receiver](docs/PROGRAM-TYPING.md#a-completed-read-narrows-its-receiver) | closed: past a read `x.k` of an immutable binding or an owned local, the statements after it hold `x` without `null` and `undefined` until `x` is written; `read-narrows-receiver` verifies, negative cases cover optional reads, writes, aliases, handlers, branches, closures and shared expression joins; the Node counterexamples pass; pipeline validation of the four expression/frame regressions is blocked by the compiler child exiting with unexpected EOF (2026-10-22, [slice measurement](#census-read-narrowing)) | `fragment-statements.mts#protocolPattern` and `fragment-statements.mts#patternStmt` move past ``gate.fail(d, "a `const` needs an initializer")`` |
| [A path of a receiver a completed read narrowed](docs/PROGRAM-TYPING.md#mapped-aliases) | closed: two slots an edge takes from one source slot are related by an alias link (`mapped-alias`), so a read link made through the plan's copy of a receiver a nullish guard narrowed reaches the receiver; an inspection (reads, `let`, allocations of operands: a method callee's evaluation) keeps every heap fact; `read-narrows-path` and `compiler-api-read-narrows-path` verify, `invalid-read-narrows-path-returning`, `-write`, `-alias-write`, `-call`, `-argument-call` and `-falsy` are refused (run under Node), a forged alias of two parameters is refused, accepted with the links check disabled (2026-10-22, [slice measurement](#census-read-narrows-path)) | `fragment-statements.mts#patternStmt`'s read `d.initializer` in `gate.span(d.initializer)` verifies |
| [Calls through a field](docs/SOURCE-MODEL.md#inferred-call-effects-elaboration-and-certification) | closed: a call through a field reads the field's contract, checked at every write, and a declared field's is its annotation, which for an ordinary arrow states no effect; so `statements`' `findIndex` callback calling `gate.abrupt` is the unrestricted one, and `abrupt`, which reads nothing of the gate, is a module function called by its binding ([source rewrite](docs/SOURCE-REWRITES.md#a-function-called-through-a-field-whose-annotation-states-no-effect)); `find-index-module-function` verifies, `invalid-field-call-effect`, `invalid-readonly-field-call-effect`, `invalid-field-call-effect-alias` and `invalid-field-call-effect-cell` are refused (run under Node) (2026-10-22, [slice measurement](#census-field-calls)) | `fragment-statements.mts#protocolPattern` and `fragment-statements.mts#patternStmt` move past `statements`' `list.findIndex((s) => gate.abrupt(s))` |
| [Pushing at the receiver's element](docs/PROGRAM-TYPING.md#judgments-and-constructor-views) | closed: a spread of a dense or readable array passes its elements at their type, and `undefined` only from a sparse one (`SpreadsInto`); a binder below and above one type, as a writable receiver's element places it, is that type, and an actual that is a literal, or a choice with a literal among its values, is built at it; `push-spread` and `push-receiver-element` verify, `invalid-push-spread-sparse`, `invalid-push-spread-wider` and `invalid-push-receiver-element` are refused (run under Node) (2026-10-22, [slice measurement](#census-push-element)) | `fragment-statements.mts#protocolPattern` and `fragment-statements.mts#patternStmt` move past `gate.hoisted.push(...statements)` and `dispatch.push(fallback ?? { … })` |
| [The search past 60 s on `shadowingLocals`](#shadowing-locals-search) | closed: the slice verifies, its search in 40 s and its check in 9 s (2026-10-20, load averages 3 to 7) | `fragment-support.mts#shadowingLocals` finishes within the census's 60 s limit |
| [Stable family members](docs/HOST-FAMILIES.md#stable-members) | closed: stable keys in the clause language, emitted by the description's rule, decoded on marked shapes, kept through every step by the stable-link rule; the controls pass, each refused one accepted with its check disabled (2026-10-20) | — |
| [A guard's false edge over a tag-set arm](docs/PROGRAM-TYPING.md#a-membership-test) | closed: the false slice drops arms the guard's set covers and reads a partly covered arm with a stable tag at the rest of its set; `compiler-api-guard-false-sets` verifies, its forged claims are refused, each accepted with coverage disabled (2026-10-20) | — |
| [A call returning `never`](docs/PROGRAM-TYPING.md#vacuous-edges) | closed: an edge out of a context with a slot of the empty type establishes any target claim, plain and branch edges alike; the producer keeps the normal edge out of an expression statement claimed at the empty type, carrying every value and local slot at the empty type with storage bindings unchanged; `never-call-narrowing` and `compiler-api-never-guard` verify, a returning call claimed at the empty type is refused (2026-10-20) | — |
| [Contextual function types](docs/SOURCE-ELABORATION.md#source-closures-and-their-annotations) | closed: a closure parameter TypeScript types by a function type is read as written where the program writes it, else through its one call signature as instantiated; `closure-contextual-callable` and `compiler-api-contextual-callable` verify, `invalid-closure-contextual-callable` is refused (run under Node) (2026-10-20) | — |
| [Assigned closure parameters](#assigned-closure-parameters) | closed: reads use a slot or cell by the flow graph's decision (2026-10-21, [slice measurement](#census-closure-parameter-slots)) | `fragment-statements.mts#protocolPattern` and `fragment-statements.mts#patternStmt` move past the `let`-union refusal |
| [Closure parameters at a union's arms](#closure-parameters-at-arms) | closed: a closure's unassigned parameter, a constructor's and a contract row's are held at their declared union's arms, as a function's; `in-test-closure` verifies, `invalid-in-open-closure` and `invalid-in-test-closure-alias` are refused (run under Node) (2026-10-22, [slice measurement](#census-closure-arms)) | `fragment-expressions.mts#expr` and the slices reaching it move past "missing field computed" |
| [Patterns binding a `for...of` over a program's iterable](docs/SOURCE-CONTRACTS.md#the-iterator-protocol) | closed: each step's value is destructured first in the closing region, by the array loop's lowering; an array's `values`, `keys` and `entries` are read at `IterableIterator` of their declared argument and stepped by the protocol (2026-10-21, [slice measurement](#census-for-of-patterns)) | `type-term.mts#readTypeTerm` and `type-term.mts#typeTerm` move past the `for...of` pattern refusal |
| [Enum reverse keys](docs/SOURCE-CONTRACTS.md#enums) | closed: an enum's object states, at each numeric value TypeScript computes, its reverse key at `string` where TypeScript's emit builds it or its runtime object is checked (`emitted-enum`); `enum-reverse-keys`, `enum-reverse-value-import` and `compiler-api-enum-reverse` verify, a key at `number` or outside the values, a string member's value and an ambient or declaration file's enum are refused (run under Node), forged claims refused at the read (2026-10-21, [slice measurement](#census-enum-reverse-keys)) | — |
| [Block-scoped type declarations](docs/SOURCE-CONTRACTS.md#block-scoped-type-declarations) | closed: a `type` or `interface` in a block runs nothing and names its block, each reference read at the declaration TypeScript binds, its equation lifted over the enclosing type parameters resolved there; `block-type-aliases` and `block-type-captures` verify, `invalid-block-type-scope` is refused (run under Node), a reference where a nearer binder hides a captured one, directly or through another block type, is refused, in a computed form, a mapped type and a default too (2026-10-21, [slice measurement](#census-block-types)) | `type-term.mts#readTypeTerm` and `type-term.mts#typeTerm` move past the type alias statement refusal |
| [A spread of an intersection beyond disjoint records](docs/SOURCE-MODEL.md#a-spread-of-an-intersection) | closed: a spread of an intersection copies the meet of one arm of each operand, a key two operands state held at the field within the other's, and each refusal names the spread's operand; `spread-intersection-meet` verifies ([slice measurement](#census-spread-intersection-meet)) | `fragment-expressions.mts`'s `{ ...part, computed: true }` with `part: ObjectPart & { name: PropertyKey }` is read at its operands' meet, and the refusal of a spread names its location |
| [Investigation of an alias of function types met with a record](#callable-alias-meet) | open: an investigation, cause unknown | `spread-intersection-callable-alias` verifies |
| [Investigation of `memberOf`'s read past a spread guard](#member-of-spread-guard) | closed: a guard's call on a `for...of` binding was an ordinary call, `readCannotThrow` not recognizing the binding; the walk stops at every binding it passes (2026-10-22, [slice measurement](#census-member-of-spread-guard)) | the cause of the producer's "missing field name" at `memberOf`'s `p.name` is established, with a reproducer |
| [Paths rooted at a slot](docs/HOST-FAMILIES.md#paths-rooted-at-a-slot) | closed: a member path may start at a `let` or assigned parameter held in a slot, its read links and entry witnesses ending at the root's next write; `slot-path` and `compiler-api-slot-path` verify, `invalid-slot-path-write`, `-loop`, `-finally`, `-pattern`, `-closure`, `-alias` and `-call` are refused (run under Node), forged entries after a write and at a loop head its back edge enters refused in search and in checking, each accepted with its check disabled (2026-10-22, [slice measurement](#census-slot-paths)) | `fragment-expressions.mts#expr` and `#binary` move past "missing field text" at `memberMayBeWritten`'s `target.argumentExpression.text` |
| [A member bound to a union of hosts](docs/PROGRAM-TYPING.md#judgments-and-constructor-views) | closed: `o.k.bind(o)` at a union of hosts each holding `k` as a member splits the host's slot and binds each host's member (`unionVar`, then `bindMember`), the producer proposing the hosts' common signature with the union of their results; the iterator protocol so binds `next` and `return` over a union of iterables; `bind-union-host` verifies, the bypasses listed in [the iterator protocol](docs/SOURCE-CONTRACTS.md#the-iterator-protocol) are refused (run under Node), a forged claim of one host's result refused in search and in checking (2026-10-22, [slice measurement](#census-union-host-bind)) | `type-term.mts#readTypeTerm` and `type-term.mts#typeTerm` move past "bind requires a single arrow and a valid argument prefix" |
| [The length of a union of arrays](docs/PROGRAM-TYPING.md#the-length-of-a-union-of-arrays) | closed: `length` of a union of array contracts is read by the same term derived at each member (`unionVar`), in a condition's term and in a statement; `compiler-api-node-list-length-test` and `array-union-length-test` verify, `invalid-array-record-length-cast` is refused (2026-10-22) | `if (xs.length !== ps.length)` with `ps = alias.typeParameters ?? []` verifies |
| [Investigation of a field re-read under a negated disjunction](#negated-disjunction-reread) | open: an investigation, cause unknown | the cause of the refusal of `if (!(k.name === "a" \|\| k.name === "b"))` is established, with a reproducer and a concrete repair obligation |
| [A chain compared with a literal](docs/SOURCE-ELABORATION.md#derived-source-forms) | closed: `x?.p ⊙ c` with `⊙` an equality and `c` a literal is the test of `x`, then `x.p ⊙ c`, `&&` or `\|\|` by what `undefined ⊙ c` gives; `optional-chain-test` verifies, `invalid-optional-chain-test-false`, `-undefined`, `-operand`, `-loose`, `-write`, `-ambient` and `-getter` are refused (run under Node) (2026-10-22, [slice measurement](#census-chain-comparison)) | `fragment-expressions.mts#expr` and `#binary` move past "missing field target" at `lambda`'s `b.target` |
| [Investigation of a conditional expression over a tested optional field](#conditional-optional-field) | open: an investigation, cause unknown | the cause of the refusal of `o.v !== undefined ? o.v : null` with `o: { v?: string \| null }` is established, with a reproducer and a concrete repair obligation |
| [Investigation of a defaulted parameter's flow](#defaulted-parameter-flow) | open: an investigation, cause unknown | the cause of `spread-defaulted-set-refused`'s edge refusal is established, with a reproducer and a concrete repair obligation |
| [Investigation of assigned parameters with defaults](#assigned-parameters-with-defaults) | open: an investigation, cause unknown | the cause of the producer's "assignment to immutable binding" refusal is established for both function declarations and closures, with a reproducer for each and a concrete repair obligation |
| [Corrected members](#corrected-members) | closed: each of the ten corrected members, read required on a8caafd, verified a function returning it at its declared type, which returns `undefined` under Node; each is refused (2026-10-19) | — |
| [Effects of dispatched calls](#effects-of-dispatched-calls) | open | a method call on a union with a primitive's shape is dispatched and `split-non-empty` verifies |
| [Remaining source forms](#remaining-source-forms) | open | the forms listed there are admitted |
| [Model limits of one form each](#model-limits-of-one-form-each) | open | each limit listed there has its model support |
| [Precision](#precision) | open | the facts listed there are derivable |
| [A semantics of the Fragment](#a-semantics-of-the-fragment) | open | extraction is proved a simulation of a Lean interpreter of the Fragment |
| [Regular expressions left](#regular-expressions-left) | open | replacement callbacks, `new RegExp`, a regex's properties and structural match iterators are admitted, and `SetIterator` and `MapIterator` loops require the native mark |
| [Computed types evaluated through helper declarations](#computed-types-evaluated-through-helper-declarations) | open: a stopgap | the helper declarations are replaced by a checker endpoint (relaxed), or TypeScript's computation is checked by a source-type elaborator in Lean (checked) |
| [The any check over external declarations](#the-any-check-over-external-declarations) | open: a stated limit, relations that `any` satisfied in an outside declaration are not re-established; 447 errors in the shadowed declarations (2026-10-18) | a check re-establishes the relations and `tests/unchecked-project/gaps.mts` is refused |
| [Node's process](#nodes-process) | open: the environment write a located gap; events known only as strings refused | a write of `process.env` through a receiver-bound host setter over shared state preserving every alias's view; signals reached through iteration proven admitted |
| [JSON records by their fields](#json-records-by-their-fields) | open | a record bounded on all its own string keys meets `JsonValue`, built or validated and kept through mutation and external calls |
| [Verification server](docs/drafts/verification-server.md) | draft pre-plan, neither accepted nor rejected (2026-10-22); decisions D1–D7 open | per-function verdicts on real files over the stage store, replacing census slicing |
| [The stage store](docs/DESIGN.md#the-stage-store) | done on macOS: every stage of the entry point (imported modules and withdrawals included) and every control runs through one invocation mechanism ([`pipeline/stages.mts`](pipeline/stages.mts)) recording each attempt; lowering, proposal, claims assembly, search, the check and explanations replay from the store (the check's replay a [trusted step](docs/DESIGN.md#trust-surface)), timeouts reused at their limit and executed again under `TSCERT_RETRY_TIMEOUTS=1` ([`tests/stage-store.mts`](tests/stage-store.mts), the replay control of `pipeline/test.mts`); a key covers the stage's execution adapter and its own code, never the replay policy, the store or presentation ([keys](docs/DESIGN.md#the-stage-store)); the census is [`dev/census.mts`](dev/census.mts) (`make census`), its slices split by `--shard i/n` over the shared store, each run a census record of outcomes, invocations and timings, `report` comparing two; the parse and TypeScript's diagnostics replay as [observed stages](docs/DESIGN.md#the-stage-store) (a [trusted step](docs/DESIGN.md#trust-surface)) on macOS, where the compiler runs confined by `sandbox-exec`, and execute without replay elsewhere ([`tests/observed-stages.mts`](tests/observed-stages.mts)); one case's parse executes, its observations incomplete (`invalid-compiler-api-guard-subpath`: a specifier the package found does not resolve); every operation of a control replays as a stage, keyed by its executable (the mutation verifier by its digest), its inputs' bytes, its environment and its exit protocol ([controls](docs/DESIGN.md#the-stage-store)); `make test` (the build, the fast checks and the controls) 113 s with a cold store and 38 s warm, its controls' 637 operations 618 executed cold and 3 warm (exits outside the protocol, which are not stored); `make suite` (the cases) 137 s cold and 14 s warm (2026-10-21, macOS, 12 cores, load 8-24, other builds running) | every stage of the entry point replays by content from one on-disk store shared by worktrees, with timeouts recorded at their limit and per-stage timing, used by the census, `run-cases.mts` and the controls of `pipeline/test.mts` |
| [The front end's own functions](#the-front-ends-own-functions) | open: of the test infrastructure (`tools/*.mts`, `dev/*.mts`, `pipeline/*.mts` and the seven drivers of `tests/`; the fixtures `tests/unchecked-project/`, `tests/unchecked-broken/`, `pipeline/examples/`, `pipeline/imports-project/` and `pipeline/library-project/` excluded), 139 of 435 functions verify in `tools/` ([ddcf13a](#census-ddcf13a)), 24 of 24 in `dev/`, 9 of 13 in `tests/` and 3 of 37 in `pipeline/` (2026-10-19, 60 s step limit) | the blockers listed there are admitted or refused by a stated restriction |

### Open work

<a id="a-connection-to-ecma-262"></a>
**A connection to ECMA-262.** Proving the host's stated types as lemmas of a
mechanized specification would turn the ECMA rows of the trust surface into
theorems; the lemmas and their cost are in
[TRUST-REDUCTION](docs/TRUST-REDUCTION.md#the-host).

<a id="native-identity-beyond-the-goal"></a>
**Native identity beyond the goal.** A program-built value is kept out of
`Promise<T>` structurally: certified code writes no `[Symbol.toStringTag]`,
which Promise's prototype record requires. A native internal slot (the
`[[PromiseState]]` that ECMA-262's `IsPromise` tests) accepts the same
programs; it becomes the cheaper path once a retained program writes its own
`[Symbol.toStringTag]`, subclasses `Promise`, or `Set`, `Map`, `Date`,
`RegExp` and `Promise` are to share one mechanism. A survey of 12.9 M lines
of library and tooling code in the local repositories' `node_modules`
(2026-10-19; no application code) ranks what lies beyond the goal: custom
thenables in 19 packages, several awaited by documented use (tinyexec,
fastify's reply, postcss's `LazyResult`), which a checked thenable protocol
at `await` and resolution would admit under either choice; about 30
hand-written tags, all in library code, one tagging a non-promise
`"Promise"` (vitest); about 7 `Promise` subclasses in 5 packages, 3 of them
one generated SDK class (`APIPromise`); and, for contrast, `extends Error`
1,150 times in 236 packages, container subclasses in about 50. The
repository's own code has none of the first three.

<a id="assigned-closure-parameters"></a>
**Assigned closure parameters.** A closure's assigned parameter is read as a
slot or cell according to the flow graph's decision, under the
[mutable-binding rules](docs/SOURCE-ELABORATION.md#mutable-bindings-and-module-constants).
The [slice measurement](#census-closure-parameter-slots) records the refusals
for `protocolPattern` and `patternStmt` in `fragment-statements.mts`.

<a id="closure-parameters-at-arms"></a>
**Closure parameters at a union's arms.** An immutable parameter declared at
a named union, of a function or a closure, is held at the union's arms, so a
failed `in` test drops the arms owning the key. The
[slice measurement](#census-closure-arms) records the refusals of `expr` and
`binary` in `fragment-expressions.mts`.

<a id="conditional-optional-field"></a>
**Investigation of a conditional expression over a tested optional field.**
Lean's search refuses both functions at the conditional's incoming edge,
"the edge from node 2 does not establish the claims at this point" (the
first: the incoming claim `null | string` of `.path:0`, the next point
requiring `unknown`; the second: the incoming claim `string`, the next
point requiring `string | ""`):

```typescript
type Opt = { v?: string | null };
export function defined(o: Opt): string | null {
  return o.v !== undefined ? o.v : null;
}
export function loose(o: Opt): string {
  return o.v != null ? o.v : "";
}
```

The same tests as an `if` with two returns verify (`optional-chain-test`'s
`defined` and `loose`).

<a id="negated-disjunction-reread"></a>
**Investigation of a field re-read under a negated disjunction.** Lean's
search refuses this function at the second `k.name`: "No rule derives this
readAt at `"b" | "c" | "d"` from k":

```typescript
export function f(k: { name: "a" | "b" | "c" | "d" }): boolean {
  if (!(k.name === "a" || k.name === "b")) return true;
  return false;
}
```

The same disjunction verifies as a branch test without `!`, and returned as a
value with or without it. In the refused check's context a path witness
(`.path:0`) holds `"b" | "c" | "d"`, the field's content past the first test,
while the term reads `k`'s field at its declared type. `type-term.mts`'s
`expandMapped` holds the form, in `keys.some(k => !(k.k === "atom" &&
(k.name === … || k.name === … || …)) && …)`.

<a id="defaulted-parameter-flow"></a>
**Investigation of a defaulted parameter's flow.** A parameter declared a
`ReadonlySet<string>` whose default is a fresh `Set<string>`, the form of
`type-term.mts#visitType`, holds either past the default, and Lean's
incoming claim at the next point is `ReadonlySet<string> | Set<string>`,
while the producer's claim there is `Set<string> | { size: never = (number) }`;
the edge does not establish it, with or without a spread of the parameter
(`spread-defaulted-set-refused`):

```typescript
export function merged(more: readonly string[], bound: ReadonlySet<string> = new Set()): number {
  return new Set([...bound, ...more]).size;
}
```

The investigation concerns the producer's row for the union of the declared
type and the default's after `DefaultValue`.

<a id="assigned-parameters-with-defaults"></a>
**Investigation of assigned parameters with defaults.** The producer refuses
assignment to a parameter with a default with "assignment to immutable
binding", for function declarations and closures alike. A concrete example
is the following function and its equivalent arrow closure:

```typescript
type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; side: number };
function f(s: Shape = { kind: "square", side: 1 }): number {
  if (s.kind === "circle") return 0;
  s = { kind: "square", side: 2 };
  return s.side;
}
```

The investigation concerns the producer's treatment of the parameter's
binding through default evaluation and subsequent assignment.

<a id="constructor-rests"></a>
**Constructor rests.** A constructor's rest parameter is refused: `new`
constructs only code without a rest (`CallArguments.construction`), so code
collecting one needs a construction that allocates the rest store from the
actuals past its parameters, and an introduction of a variadic construct
signature from such code, as `restsT_of_graphRest` is for a function.

<a id="class-offers-across-units"></a>
**Class offers across units.** A class value is offered a signature its use
expects (a variadic construct signature, a longer one) where its binding
and the use are analysed together: at the module's statements. A module
function passing a module class to a variadic construct signature leaves the
class's claim without that signature, and the call is a search failure; the
offer needs the class claim to collect the signatures every unit's uses
expect.

<a id="generic-methods-left"></a>
**Generic methods left.** A class's generic method with a bounded binder:
the member's binder row is named by its bound, which the parser does not
spell for the closure (`class-generic-method-bounded-refused`). Members of
two declarations, or of two instances of one, binding as many binders relate
up to renaming ([generic methods](docs/SOURCE-CONTRACTS.md#generic-methods)); two
binding different numbers of binders (`m<U, V>` at `m<W>`), which TypeScript
relates by instantiating the source at the target's binders, need an instance
table naming each source signature's image at the target's binders, inside
the family entry's table. A binder a member's result accumulates
(`catch`'s `Promise<T | TResult>`) grows its family by one binder per call:
each is an application of the one equation, unfolded only when read
([RECURSIVE-EQUATIONS](docs/RECURSIVE-EQUATIONS.md)), never truncated.

<a id="restoring-completeness"></a>
**Contract completeness.** Array presence, callback effects and conversion
contracts impose separate obligations. Their current designs are stated under
[arrays](docs/SOURCE-MODEL.md#arrays), [native contracts](docs/SOURCE-MODEL.md#exact-contracts-and-native-effects) and
[effect certification](docs/SOURCE-MODEL.md#inferred-call-effects-elaboration-and-certification).
A future inference improvement must preserve these distinctions: density is
stronger than readable elements; readonly aliases do not prevent callback
mutation; and a written callback annotation cannot silently acquire a stronger
effect. A program with an arbitrary callback promising readable `U[]` for every
`U` must justify that promise even when the callback shrinks the source.

Effect inference remains conservative for some rest wrappers, call forms and
nested heap operations. Expression scheduling alone does not supply the missing
effect derivation. Code that writes only locations it allocated preserves the
heap it was called with, but a body's checked footprint separates only array
stores the body allocated, through fresh results ([footprint
precision](#footprints)). A call of a value holding a fixed
signature and its variadic extension, a module constant read as a value
elsewhere, is not certified preserving: the selected call's evidence is no
qualified application at the fixed signature. Keep the source targets and their
negative controls when extending the body-effect checker.

<a id="footprints"></a>
**Footprints.** [FOOTPRINTS](docs/FOOTPRINTS.md) states the mechanism: a
construct's fact, the operations proved to keep it, stated as closed
footprints, and Lean's node-by-node check that a callback, with what it
calls, stays within one. The checked forms are inspections, typed writes of
fields holding values, and fixed calls, variadic calls and constructions at
a selected signature, `pop`, `shift` and `reverse` at a store the body
allocated ([fresh array storage](docs/FOOTPRINTS.md#fresh-array-storage)).
Left open:

- the other application forms (a variadic construction, a call of a
  callable object, a packed call) consume no footprint, so a bounded body
  refuses them;

**Footprint precision** is deferred
([FOOTPRINTS](docs/FOOTPRINTS.md#deferred-extra-precision)): separating one
array from another beyond fresh storage, so that `pop` on an array literal
the callback allocated is admitted; and a declaration's fresh result, which
only closures state.

<a id="universe-slices"></a>
**Slices of the value universe.** A tag test on a value at `unknown`
narrows nothing: `typeof v === "object" && v !== null` leaves `v` at
`unknown`. The [design](docs/SOURCE-MODEL.md#slices-of-the-value-universe-by-tag-tests-design)
slices the universe by kind; the dictionary view
`{ readonly [key: string]: unknown }` stays out of reach of those tests, so
the guards over `unknown` in `claim-text.mts`, `claim.mts`, `type-graph.mts`
and `diagnostic-view.mts` (6 slices refused at their promise, 3 more behind
them) wait on it and on their own promises.

<a id="guard-promise-field"></a>
**A guard's promise on a field.** A promise narrows an actual that is an
immutable name: `str(o.name)` (`asserts v is string`) leaves `o.name` at its
type, and a field's current-content facts hold primitive atoms only. The
promise of a call whose actual is a field read, a primitive one, would be a
current-content fact of the field through the read's link (`claim.mts`'s
`atom` and `decodeClaimType`).

<a id="guard-answer-constant"></a>
**A guard's answer held in a constant.** `const ok = isRecord(v)` keeps the
call's promise on the call's result, an implication of its slot, which no
statement entry carries: `if (ok) return v` reads `v` at its declared type,
and a narrowed claim there is refused at the edge. Carrying implications in
entry claims is a fact kind of its own.

<a id="generic-equality-condition"></a>
**Generic equality in a condition**, an investigation: a strict or loose
comparison of two values of a type parameter verifies as a returned value,
`return left !== right`, and is refused as a statement's condition, `if
(left !== right) return 1;`, with `left, right: T` (2026-10-19). The search
fails; the message it reports ("strict equality with a value of a type
parameter: neither operand is known to be a primitive or an object") is the
producer's diagnostic of the comparison (`expression_values.ml`), not a
located obligation, and which judgment fails is unknown. The Boolean-return
lowering, which turns a return into a condition, is scoped to type guards
and assertion functions until this holds: applied to every return, it
refuses `loose-equality` and `generic-unknown-arguments`, which keep their
outcomes.

<a id="negated-first-read"></a>
**A negated first read of an element**, an investigation: with `type
Declaration = { readonly kind?: string; readonly initializer?: string }`,
`const d = list[0]; if (!d.initializer) return -1; return 0;` is refused
before search at the read `d.initializer` ("read receiver must name a cell
contract", `Plans.readCell`), on f91d657 and on the branch of
[mapped aliases](#census-read-narrows-path) (2026-10-22). The same function
with `if (d.initializer) return 1;`, or with `d` read before the test
(`read-narrows-path`'s `returned`), verifies, and so does the negated test
over a compiler node (`ts.VariableDeclarationList`'s first declaration).
Which receiver type the negation's lowering hands the read is unknown.

<a id="literal-guard-json-read"></a>
**A literal guard over `JsonValue | undefined`**, an investigation:
`isDense(value: JsonValue | undefined): value is "dense"` returning `value
=== "dense"` is refused at its true return, the literal `true` at the first
code unit of `return` ("the promised argument is not within the promise at
this return"), where the diagnostic gives the argument's claim as
`JsonValue`, `undefined` removed, and not `"dense"`
(`guard-literal-json-read-refused`). The same guard over `unknown`,
`JsonValue`, `string`, `string | undefined`, `null | string` or `string |
number` verifies (2026-10-19). Which step of the comparison's narrowing
keeps the whole of `JsonValue` is unknown. The front end's literal guards
(`isArrayPresence`, `isIndexClass` in `type-graph.mts`) take `unknown`,
which verifies.

<a id="guard-overloads"></a>
**Guard overloads beyond `filter`'s.** TypeScript's `every<S>` narrows the
array to `readonly S[]` where it answers `true` at a guard, and `find<S>`
returns `S | undefined`. Neither is a contract of the native at the top
footprint a closure's promise signature is checked at
([prototype contracts](docs/SOURCE-CONTRACTS.md#prototype-contracts)): a
callback may append untested elements or replace tested ones before `every`
answers, and `find` passes `undefined` at positions a callback removed. Both
hold at a callback keeping array stores, which a promise signature can state
once a promise row's code is checked at a footprint (`effectChecked` checks
it at the top one alone). A guard read as a value meets `filter`'s guard
overload once its promise signature is adapted to the callback's longer one,
as a module function's slot meets a longer plain signature
(`filter-guard-value-refused`).

**Field facts across calls** are deferred, measured (2026-10-19): a call
step keeps no current-content fact, and keeping those a call's checked
footprint leaves true would move the evidence search of 7 functions of the
front end's census past the fact's loss at an empty-footprint call, none
more at a `value: keep` footprint, and 3 more only where every step keeps
them; search completes for 2 (`completes`, `heapAtom`), and the others stop
at a later obligation. The measurement kept facts in search's untrusted step
choice and in the producer's proposals, with the checker unchanged; no
function was verified by it.

<a id="keys-known-only-at-run-time"></a>
**Keys known only at run time.** A write at a string key known only at run
time of an object or `null` value needs the copy to replace the prototype
where the key is `__proto__`, as the setter does; a key-adding write at a key
that may be a string or a symbol, a dispatch on the key's kind. A write adding
a key to an object a reference other than its holding locals may hold (a
callee, a closure, a `let` bound to it) needs the heap to map an object's
identity to its keys, which it does not. A key added to a class instance
whose prototype holds methods is copied with the prototype, but the copy is
typed as the record `mergeResult` gives, which states no method: it needs a
merge result at the instance's row.

<a id="module-composition"></a>
**Module composition** as a Lean theorem: the step-indexed argument that
units certified against each other's signatures compose.
[Certified imports](docs/SOURCE-MODEL.md#certified-imports) check an
imported function's code in the importer's run, at its effect-qualified
signature. `checkJson_safe` keeps its statement.
Combining a certified import's conclusion with the importer's is left to
this theorem, plus the review obligation that the import binds the certified
unit's closure ([the linking obligation](docs/SOURCE-MODEL.md#certified-imports)).

<a id="decoders-dictionary-reads"></a>
**Decoders' dictionary reads.** The decoders of `calculus.mts`,
`control-flow.mts` and `diagnostic.mts` read the wire as `Json`, what
`JSON.parse` returns without a reviver
([the contract](docs/SOURCE-CONTRACTS.md#library-globals)): a parsed object
is a dictionary of parsed data, read by key as the index's value or
`undefined`, and a key it may inherit from `Object.prototype` is refused
(`invalid-json-parse-inherited`). A constructor object's one key and its
value are `Object.entries`' pair, so no read at a key known only at run
time is needed. In `calculus`, the slice of `termsOf`, holding
`decodeTerm` and `decodeCode`, takes 29 s of evidence search and 5 s of
checking (user time, 2026-10-18). Of 29.6 s, 16.5 s are image-equivalence
checks: an instance of the array prototype's scheme, its result an array of
`source & X`, against the claim's `Term[]` row, 172 checks of 24 distinct
pairs, each direction of the costliest about 0.25 s though each side is one
clause. The time is in the structural comparison of the recursive `Term`
and `Json` union arms beneath; absorbing `source & X` into `X` before the
check takes it from 16.5 s to 16.2 s, `X` being source-valued in only 56 of
the 172 checks (a probe, 2026-10-18). Candidate selection
([structure-directed comparison](docs/UNION-SHAPES.md#9-the-implementation))
takes the structural engine's demand pairs from 470,306 to 41,560; the rerun
of each comparison it leaves unestablished costs 9.8 s and establishes none.
Within `termsOf`'s search, 107,721 subtype requests ask 3,926 distinct
questions, and the repeats take 14.7 s of 24.9 s, the refused repeats 11.9 s
([where the search time goes](docs/UNION-SHAPES.md#93-where-the-search-time-goes),
2026-10-18). `dev/lowering-dump.mts`
decodes the verifier's output with `decodeUnits`, which calls `fields` and
`nat` in `map` callbacks: imported functions, whose effect no certificate
states ([module composition](#module-composition)).

<a id="optional-field-truthiness"></a>
**Optional-field truthiness over unions** uses a saved read result and its
receiver-and-field link, including where one record requires the field and
another leaves it optional ([witness edges](docs/PROGRAM-TYPING.md#witness-edges)).

<a id="exceptional-footprints"></a>
**Exceptional footprints**: a call's promise that its footprint also holds
when it throws (`onThrow`), carried through handlers and concluded by
`checkJson_safe` ([the design](docs/SOURCE-MODEL.md#exceptional-footprints)).
Left: handlers receive no current-content facts across a throw.

- a semantic extension: `SafePost` states no postcondition on a throw, so
  `checkJson_safe` needs an exceptional conclusion tied to the exact CLI
  success condition;
- composition covering evaluation before the invocation, parameter
  defaults, intermediate mutations, handlers and rethrows;
- normal-return promises and freshness stay on normal edges: neither moves
  onto an exceptional one;
- a native states `onThrow` only where its audit covers every throw, as the
  [restricted `execFileSync`](docs/SOURCE-CONTRACTS.md#library-modules)
  audit does.

<a id="iteration-left-open"></a>
**Iteration left open.** An array pattern over a host
non-array iterable needs the pattern's reads as steps of `%Iterate:K%`, or of
the protocol. A spread of a program's iterable where the statement evaluates
code before it, and a default or nested pattern in an array pattern over one,
need the protocol's steps interleaved with that code, in the expression, not
before the statement. A generator needs a state-machine lowering, as
TypeScript's downlevel emit writes one: a closure over the suspension
point's number and the live locals, whose `next` resumes at a `switch` on
it. An element read past a readonly tuple arm's length needs a rule
reading `undefined` beyond an exact length.

<a id="enum-member-case-labels"></a>
**Enum-member case labels.** A `switch` whose `case` labels are enum
members (`case K.One:`, `case ts.SyntaxKind.SourceFile:`) narrows nothing in
the producer, where the same constants narrow in an `===` test and literal
labels narrow in a `switch` (`switch-enum-case-narrowing`, a gap). The
compiler API's code switches on `node.kind` this way.

<a id="shadowing-locals-search"></a>
**The search past 60 s on `shadowingLocals`.** The slice of
`fragment-support.mts#shadowingLocals` holds that function and
`bindingScope`, which it calls. Its search spends about 44 s on
`bindingScope` and 19 s on `shadowingLocals`. On 77ca829 it spends 40 s on
`bindingScope` and stops there, refused at `block(holder.parent)`, which
the [stable-link rule](docs/HOST-FAMILIES.md#stable-members) derives; no
judgment's cost grows between the two, and the search reaches the second
function (measured 2026-10-20, the slice alone, load averages 2 to 7). The
time is in subtype comparisons that fail: at a member read or a guard's
call on a node, the receiver is compared with each pool type that has the
member, about 74 of the family's arms in this slice, and each comparison of
a union of 57 to 63 arms with one arm fails in about 70 ms. In
`bindingScope`'s own slice the pool holds 41 such arms and each comparison
takes about 7 ms: 2.5 s in all.

<a id="fragment-statements-search"></a>
**The search past 60 s on `fragment-statements.mts`.** The slice of
`protocolPattern` spends its search in lowering the functions it holds, not
in proof search. Sampled on eb3a427 (90 s alone, 2026-10-22), 78% of the
lowering is in the statement entries' witness checks (`ownWitness`): 421
subtype comparisons, twelve of them the same failing comparison of a union
of 44 node arms with one of 43, each 1.2 to 2.8 s. Two thirds of the
samples are in instantiating rows: the extraction's store answered every
read of a label's clauses by instantiating its head's template four
times, once for each row form it tested, and never kept a named type's row
between reads. With rows kept, 22% of the samples were each type
reference's linear search of the declaration document, comparing JSON
identities. With a named type's row instantiated once per graph, a row's
form read from its template, and the declarations indexed by identity,
the slice's search takes 13 s alone, with the same refusal, and its
comparisons 7 s; the twelve repeated comparisons take 0.55 s each.

<a id="fragment-statements-search-rows"></a>
**The search past 100 s on `fragment-statements.mts`.** On 526bf6e's
artifacts the slice of `protocolPattern` reaches proof search, and its search
stage takes 103 s of CPU alone (2026-10-22). Sampled, two thirds of proof
search instantiated rows of the checked equations: a test of a row's form
(`NormalGraph.plain`) instantiated the label's template three times, and a
row of an application at arguments was instantiated at every read. In
lowering, 70% of the witness checks' comparisons tested a union's labels
against another's one by one, quadratically, and each new graph of the
extraction's store instantiated the named types' rows again; each
request's search vocabulary was closed three times, by a quadratic
`eraseDups` over every known label at every round. With one form test for
both stores (`NormalGraph.ofRowMapForms`), the rows of the applications and
meets the named types' rows name kept with the checked equations
(`Equations.memo`), a union's inclusion read along its order
(`subsetIn`), the named types' rows kept in the extraction's store while
their heads are unchanged (`State.nullary`), and the vocabulary closed once
per request over its new labels, the search takes 27 s with the same
refusal. Of that, a quarter is the witness checks' comparisons, one of them
repeated twelve times at the same store, and a quarter is the per-item
check of `produceUsing`, which compares a union of 42 or 44 node arms with
`Node`'s 130 about twenty times each.

<a id="generic-instance-union-arms"></a>
**A generic method's instance at a union of arms**, an investigation:
`n.forEachChild((c: ts.Node): ts.Node => c)`, in a run whose selection
reads `Node` as several arms, is refused in evidence search at the read of
`forEachChild` ("No rule derives this readAt",
`compiler-api-node-callback-inline`), where the same callback bound to a
name, and the written callback in a run reading `Node` as one arm, verify.
Which part of the instance's proposal or of its image check fails is not
known.

<a id="corrected-members"></a>
**Corrected members.** The [corrections](docs/COMPILER-API.md#corrections)
are fields the declarations state required and the runtime leaves absent.
Read as declared (a8caafd), a function returning one at its declared type
verified and returns `undefined` under Node: `sf.parent` at `Node`,
`PropertySignatureDeclaration.initializer`, `PropertyAssignment.type`,
`ShorthandPropertyAssignment.type`, `ExportAssignment.type`,
`DefaultClause.expression`, `NoSubstitutionTemplateLiteral.rawText` and
`.templateFlags`, `TaggedTemplateExpression.questionDotToken` and
`JSDocTemplateTag.constraint`; the last two `make compiler-api-shapes`
finds. The family contract reads each optional; the ten
`invalid-compiler-api-corrected-*` cases are refused, each run under Node
by `tests/compiler-api.mts`.

<a id="effects-of-dispatched-calls"></a>
**Effects of dispatched calls.** A method call on a union receiver is
dispatched on the receiver only where no alternative has a primitive's
shape or the alternatives read different members
([PROGRAM-TYPING](docs/PROGRAM-TYPING.md)). A dispatched call is an outer
conditional whose callee is a wrapper allocation and a member lookup, and
effect selection admits only a direct call, with evaluated operands, so a
dispatched call's effect is not established (`split-non-empty`, dispatched,
leaves `{value: keep, store: keep}` unestablished). Either the dispatch
lowers into branch nodes whose callees are evaluated values, or effects are
checked compositionally for these terms.

<a id="remaining-source-forms"></a>
**Remaining source forms.** A method call on a union of primitives,
which needs one callee contract its receiver meets. An optional call of a
method on any object (`f().m?.(a)`, `optional-method-call-object-refused`):
saving the receiver once, `let r = o; let m = r.m` then
`optional(m, callWithReceiver(m, r, a))`, admits every object and needs no
analysis of whether a second read of `o` is stable; the Fragment has no
expression binding a hidden name, so the lowering needs one. A source binder used both
as a pack and as an array value (`...args: T`, `args: T`): a binder whose instances are
arrays or tuples of required positions, its pack meaning that tuple contract's lists, so an
entry collects the fresh store at it and a spread of its value gives a list in the pack. Explicit type arguments on an element call,
which reach an element only as a generic closure's quantified claim.
User guards and assertion functions: the promise is a contract a
conjunction of arrows states, `(x: A) => boolean` with
`(x: Exclude<A, T>) => false` (an assertion function's `=> never`), which the
body is checked at, as a closure at each of its signatures; a caller narrows
through a fact the call leaves tying its result slot to its argument slot,
"an argument in `Exclude<A, T>` gave `false`", which the branch on the
result turns into a slice of the argument. Such a fact is about a type's
meaning, world- and level-indexed, where current-content facts are not; it
needs its own place in the knowledge a statement entry states. A static
initializer calling a static method reading its class, or constructing it
where construction reads an earlier static field, which runs the class's code
before the class value exists (a construction reading a later one reads
`undefined`, refused on principle); private
names in inheritance, which needs the derived construction's copy of its
base part to carry the base's private slots; a prototype member keyed by a
symbol.

<a id="model-limits-of-one-form-each"></a>
**Model limits of one form each.** Module storage (`declare let`, a
module-level `let`) needs cells every call may write, read at their declared
type. Sloppy code's `this` at a receiver type that may hold a primitive,
`undefined` or `null` needs the receiver conversion (the global object, a
wrapper). A library class as a base needs a construction rule for what its
constructor allocates; `Error` has one, its message on the instance's first
link ([a class extending `Error`](docs/SOURCE-ELABORATION.md#a-class-extending-error)),
which serves while ownness, descriptors and the prototype of an instance are
refused. The Error family's general mechanism is a store of non-enumerable own
properties: reads and ownness tests see it, enumeration and copies exclude
it, the instance's prototype stays `D.prototype`, and a write or redefinition
and every subclass's construction act on it; it admits `TypeError` and the
other native errors, `hasOwnProperty("message")` and `Object.getPrototypeOf`. `keyof T` and `T[K]` over a function's own binder need a row whose
meaning fixes a key set, which a value set does not. `o.m?.()` needs the receiver saved
across the test. `key in o` at a key the built-in prototypes hold needs those
prototypes' keys in the model.

<a id="precision"></a>
**Precision.** Retaining heap facts across calls needs a proved
reachability or noninterference statement: the model's types do not bound
the locations a value names (`top` admits any object), so a location
allocated after a value cannot be shown unnamed by it, and the statement
needs every type's meaning to bound its value's locations by the world; set-valued clause covering (an
arrow against a union of arrows) needs a covering relation of another arity;
a vacuity escape for contradictory reference conjunctions
(`Ref null ∧ Ref bool ≤ Ref (null ∨ bool)`) is true and not derivable; the
producer's arrow search builds no nested `combine`. An element read keeps no
heap fact: it reads the heap only, but the value it finds is a value only
where the store's contract says so, which the frame rule would have to take
from the read's typing (a length is a number, and keeps them). An element
read the code guards is read at the element type or `undefined`; a member of
it is read past a nullish guard, which throws where JavaScript does, but the
value itself passed on keeps `undefined`
(`guarded-element-read-refused`): `xs[0] !== undefined && known.has(xs[0])`
needs a current-content fact about an element location, kept from the test
to the second read, as a field path would need one (`o.a !== undefined &&
f(o.a)` is refused the same way). An optional chain's truthy or present
result narrows the value the chain saved, not the binding it was read from
(`optional-chain-receiver-not-narrowed`: `if (o?.inner) use(o)`), which
needs the chain's test related to the receiver's slot. A `flatMap` callback returning a
primitive or an array of primitives (`flat-map-scalar-result-refused`)
needs a second signature quantifying a binder bounded by the primitives,
which the first does not use: neither the producer's instance of a member
read nor Lean's search for one assigns a binder no parameter of the
selected signature names. The design question is per-signature binders, or
bounds, in a prototype member's scheme. A closure passed to `map` over an array literal of
records with different members (`closure-contextual-literal-union`) is read
at TypeScript's contextual records, `{ a: number; b?: undefined } |
{ a?: undefined; b: number }`; the producer claims it at the literals'
records `{ a: number } | { b: number }`, which state no absence of the
other's member and so are outside the parameter's records. A closure parameter at a generic declaration's anonymous record at an
instance with an optional member at a binder
(`closure-contextual-anonymous-instance-refused`: `{ v?: T }` of
`interface Opt<T> { readonly items: readonly { v?: T }[] }`, read through
`const xs = o.items; xs.map((i) => i.v)` at `o: Opt<number>`) is refused:
the compiler's synchronous API gives the instance's members but no
instantiation of `T`, and `v`'s type carries the `undefined` optionality
adds, so `v?: number` is not told from `v?: number | undefined`. Reading it
needs the instantiation from the compiler (an API extension) or a checked
elaboration of the contextual type. A key-adding write at a symbol known only at run time
(`symbol-key-growth-refused`: `d[fresh()] = 1` with `fresh(): symbol`
returning `Symbol("k")`) is refused, as the key may be `Symbol.toStringTag`;
admitting it needs a fact that the key is no tag, such as a type of the
program's own fresh symbols, and the copy rule then refuses it too, the
object's type listing no keys.

<a id="a-semantics-of-the-fragment"></a>
**A semantics of the Fragment.** The parser's rewrites and extraction rest
on review. The Fragment moves close to source JavaScript, the rewrites move
into extraction, and the Fragment gets a direct semantics in Lean: an
executable interpreter that reads it as JavaScript does, with types erased.
Extraction is proved a simulation of it. The interpreter's faithfulness to
JavaScript is tested against node, not proved: the target is fixed, so
testing converges without a mechanized specification. A rewrite chosen by a
type (`%Iterate:K%`, `%ElementAt%`) is correct under that typing premise.
The reading of declared types and the host remain trusted; the remaining
options are in [TRUST-REDUCTION](docs/TRUST-REDUCTION.md).

<a id="computed-types-evaluated-through-helper-declarations"></a>
**Computed types evaluated through helper declarations.** A computed form
naming a declaration's parameters (a bound, a default, an annotation's
computed alias) is evaluated at an application by the pinned TypeScript,
through helper declarations added to a probe program
([written applications](docs/SOURCE-CONTRACTS.md#written-applications),
`tools/type-probe.mts`): the checker offers no operation instantiating a
declaration's syntax. This is a stopgap, to be either relaxed or checked.
Relaxed: where TypeScript's API offers a direct checker endpoint for
instantiation and `keyof` (a declaration, its arguments, a parameter's
instantiated bound or default), it replaces the helper declarations and
their resolution checks. Checked: a source-type elaborator whose reductions
Lean checks, from declaration-linked bounds and completed arguments to the
semantic types, so that the correspondence to TypeScript's computation is
proved rather than trusted. Either retires the clause of the trust surface's
TypeScript row stating that "a computed form naming a declaration's
parameters, at an application, means what the checker computes for a probe
declaration" ([trust surface](docs/DESIGN.md#trust-surface)); the checked
form retires the computation's trust altogether, the relaxed one only the
probe's correspondence to the application.

<a id="the-any-check-over-external-declarations"></a>
**The any check over external declarations.** `tools/unchecked.mts` checks
the sources over external declarations whose every value-level `any` is one
opaque type (`tools/shadow-contracts.mts`). A declaration may rely on `any`
being at once a subtype and a supertype of every type, and the opaque type
is neither: the relations that `any` satisfied in an outside declaration are
not re-established, a limit the check states. The shadowed declarations do
not check (447 errors with `skipLibCheck` off, 2026-10-18), by class:

- an override or a heritage relation the base satisfies through `any` (367:
  2416, 2430, 2417, 2420), mostly Node's event emitters, whose base
  `listener: (...args: any[]) => void` an override narrows;
- a type argument meeting a constraint through `any` (49: 2344);
- a property meeting an index signature through `any` (25: 2411);
- a rest parameter `...args: any` (3: 2370), a predicate `x is any[]` over
  a parameter typed `any` (3: 2677).

An invalid declaration changes what TypeScript decides about the sources:
`f(new D())` with overloads at `B` and `D` and `D extends B` broken selects
the other overload. The same class holds the type computations the
substitution changes: `any extends string ? string : number` becomes
`number` (written: `string | number`), a type parameter's default `any`
read as `unknown` accepts every input (`Sink<T = any>`), and `A["missing"]`
over an opaque `A` is the error type inside a member. Each is a line of
`tests/unchecked-project/gaps.mts`, accepted under the stated limit. Replacing `any` by `unknown`
at a result and `never` at a parameter keeps the relations of a parameter
and a result but not of a writable property or a type argument, whose
variance the declaration's syntax does not show; no one substitution keeps
every relation `any` satisfies.

`JSON.stringify` of a function, or of an object whose `toJSON` returns
`undefined`, is `undefined` under Node, and the check types it `string`
(`gaps.mts`). Read at the overlay's `JsonValue` (primitives, read-only
arrays and string-indexed records of them, library-globals.mts), 56 calls of
the sources stringify a value that is no `JsonValue` (2026-10-19; 84 before
`JsonValue` held arrays): a value typed `unknown` (`claim-text.mts`,
`diagnostic-view.mts`), or a record a declaration types by its fields (the
Fragment, claims and flow documents, a `tsconfig.json`'s object), which
[JSON records by their fields](#json-records-by-their-fields) would admit.

<a id="nodes-process"></a>
**Node's process.** Every global is read through reviewed entries
([Node's process](docs/SOURCE-CONTRACTS.md#nodes-process)). Two forms stay
outside:

- **The environment write.** `runRoot` writes `process.env[k] = s`, a key
  `env` may not hold, visible through every alias of the object
  (`node-process-env-write`, a gap). The model's key addition is typed only
  on a local's own fresh object, a copy no other reference sees; it cannot
  justify a key visible through existing aliases. The obligation: represent
  mutable host lookup through shared state, with read and write contracts
  preserving every exported view. The operation then designed: a
  receiver-bound host setter with `env` as its audited instance, taking a
  primitive string key and value, its footprint `{value: any, store: keep}`
  on normal return, exceptions unrestricted, promising no later read equal to
  the string written (invalid names, NUL handling and platform
  normalization unaudited); the assignment lowered as receiver, key and value
  once, in order, the setter, and the saved value as the assignment's. Its
  controls: a new key and an overwrite observed through an earlier alias,
  stale narrowings refused, array density kept, `undefined`, objects and
  symbols refused with Node's coercions run, prototype-sensitive keys, fake
  receivers, mutable-view exports and forged setter claims refused.
- **Events known only as strings.** A `for...of` over an array literal of
  signal names gives each a `string`, not proven an admitted signal, so its
  registration is refused (`collections-process`, `collections-main`, gaps,
  both verified before the review).

<a id="json-records-by-their-fields"></a>
**JSON records by their fields.** A record a declaration types by its fields
(an interface, a type literal) is no `JsonValue`: a record is open, and an own
string key it does not declare may hold a `toJSON` (`invalid-json-stringify-record`,
run under Node). Admitting one needs a bound on all of its own string keys:
each a declared field whose present value is a `JsonValue`, an ordinary data
property, over a safe prototype; established where the record is built or
validated and kept through its mutations and through external calls; and a
policy for an optional field, absent or present at `undefined`. The claim
printer's lifter (`liftType`, `liftClause` and `treeAtom` in
`claim-text.mts`) builds such records and passes them at `JsonValue`, and is
refused there. A general form of the bound: a fresh object literal
establishes it where it is built, its own keys being the literal's, and the
bound is preserved through the object's mutations and through calls.

<a id="the-front-ends-own-functions"></a>
**The front end's own functions.** Each top-level function of `tools/*.mts`,
sliced into its own file with the same-file declarations it uses, is a piece
of ordinary TypeScript the pipeline can be asked about: 337 of them. A slice
stops at its first refusal, so each blocker below hides the ones behind it.
The first blockers, by the number of slices each stops (2026-10-18; the
first three items 2026-10-19):

- a host guard answering `false`, which narrows nothing while the guard is
  read at its declared `x is T` signature
  (`compiler-api-guard-false-branch`): 18 slices of
  `fragment-statements.mts` read `elements` of a `BindingName` after
  `if (ts.isIdentifier(node)) return …`, and `knownLocal` reads `name`
  after `!ts.isSpreadAssignment(parent)` (2026-10-19, 829513e); the
  [host-guard rule](docs/COMPILER-API.md#guards) reads the call as a kind
  test refining both edges, and waits on guard recognition;
- a member read through a host node's member a test refined,
  `ts.isIdentifier(m.name) && m.name.text` (7: `staticFieldOf`,
  `staticMethodOf`, `hasInstanceClass`, `hasInstanceAlong`, `localArrow`,
  `memberOf`, and `moduleFunction` through `memberMayBeWritten`;
  2026-10-19, 829513e): a promise refines a name alone; in the
  [stable members](docs/HOST-FAMILIES.md#stable-members) design a guard
  refines the slot of its argument's read, which a later read of the same
  path is through the read link;
- a pattern binding a `for...of` over a program's iterable (17), the slices
  of `type-term.mts` past their contextual function types (2026-10-20,
  [census](#census-never-callable)), which read past it a type alias
  statement in a function body ([record](#census-for-of-patterns)), an
  iterator's `next` bound to a union of hosts ([record](#census-block-types)),
  and stop in the producer at "missing field positions", `signatures`' test
  `"positions" in contract` ([record](#census-union-host-bind)); the slices of
  `fragment-statements.mts` past `protocolPattern`'s call of `gate.fail`
  read a closure's assigned parameter after a host guard, a
  [slot](docs/SOURCE-ELABORATION.md#mutable-bindings-and-module-constants)
  of the closure's activation, read `ts.SyntaxKind[s.kind]`, a numeric
  enum's reverse lookup, at `string`, and stop in `readCannotThrow` at the
  closure `d => d.modifiers?.some(…)`, whose signature claim is outside the
  source annotation ([record](#census-enum-reverse-keys));
- a callback's parameter written without a type is read at its contextual
  type, records, indexes and aliases without parameters included; no slice
  stops there;
- library globals absent from the overlay or refused (4, 2026-10-19):
  `Reflect` ([refused](docs/SOURCE-FRAGMENT.md)) (3) and `Object.hasOwn`; the
  slices `parseInt`, `Object.fromEntries`, `Array.from`, `Math.ceil`,
  `new RegExp` and `instanceof Error` stopped now stop later, at a class
  extending a class of the file (4), `Object.hasOwn`, a `Stream` declaration,
  a type alias statement, an `in` test, and the search (2);
- members of `Type` and `Checker` outside their named views (10);
- the sync API's `API` class, whose type parameter has a default (8);
  `createRequire`, whose type names a qualified one (1); `node:path`'s
  `sep`, a constant of the object the module exports (2); a default import
  (5);
- `readDiagnostic` stops in the producer at a read of `forEach` through a
  field holding an object beside `null` or `undefined`, and `diagnosticNode` in
  search at a key read that may name an `Object.prototype` member
  (2026-10-19).

<a id="census-host-family-contract"></a>
The `tools/` census of a8caafd (main) and of 0337c3f (the family contract,
with that main merged), run back to back on one machine (2026-10-19, load
averages 20 to 40): 105 of 350 slices verify on main, 107 of 353 on the
branch. The branch adds 3 slices: `compiler-api.mts#useFamilyDescriptionForTests`
and `#hostFamily`, verified, and `host-families.mts#familyTable`, refused at
the gate on a `TransformOptions` declaration. Of the 350 common slices:

- verified on the branch only (4): `declaration-graph.mts#expressionAt`,
  `#identifierAt`, `#typeNodeAt` and `type-probe.mts#identifiers`, refused
  in search on main;
- verified on main only (3), each now refused in search, and none a
  timeout: `fragment-support.mts#jumpTarget` and `#writtenElement` write
  `parent = parent.parent` into a `let` TypeScript types `Node`, and the
  branch's `Node` reads `parent` optional, since a source file's is absent
  ([corrected members](#corrected-members)); `fragment-support.mts#bindingScope`
  reads `holder.parent` again after testing it, which no fact of the first
  read narrows ([stable members](docs/HOST-FAMILIES.md#stable-members));
- verified on main, a timeout on the branch (1):
  `declaration-graph.mts#untypedAmbientField`, the search past 60 s;
- a changed failure (3): `declaration-graph.mts#computedAt`, refused in
  search on main, the search past 60 s on the branch;
  `fragment-statements.mts#closeStatements`, the search past 60 s on main,
  the check past 60 s on the branch; `diagnostic.mts#diagnosticNode`, the
  call stack exceeded on main, on the branch a reply of
  `Checker.getTypeFromTypeNode` to the query `keyTypeOf` makes that the
  client cannot decode ("Expected fixed 3-element array (0x93), received:
  0x69"), seen once; two runs of the slice alone on 0337c3f exceeded the
  call stack, and the failing query's arguments and stack were not kept.

<a id="census-guard-recognition"></a>
The `tools/` census of ed81b46 (main) and of b7787b9 (guard recognition),
run back to back on one machine (2026-10-20, load averages 3 to 18): 127 of
365 slices verify on main, 126 of 369 on the branch, with no timeout and
no worker failure on either. The branch adds 4 slices
(`compiler-api.mts#activeGuards`, `#checkedGuards`, `#guardEntry`,
`#guardModule`), each refused at the gate on `node:path`'s `sep`. Of the
365 common slices:

- verified on the branch only (1): `declaration-graph.mts#boundedArguments`,
  `call.arguments.some(ts.isSpreadElement)`, a guard passed as a value;
- verified on main only (2), at `ts.isTypeNode`'s declared predicate,
  where its entry also accepts `ExpressionWithTypeArguments` (kind 234),
  which `TypeNode` does not declare:
  `declaration-graph.mts#typeNodeAt` returns a node `isTypeNode` accepted
  at `TypeNode`, an acceptance of a program that is not safe, refused at
  its return (`invalid-compiler-api-type-node`, run under Node, returns
  the node of kind 234); `#computedAt` passes such a node to
  `computedForm`, whose parameter is a `TypeNode`, and that argument
  obligation fails; it returns the node only where `computedForm` answers
  or `isTypeReferenceNode` holds, both `null` or `false` under Node on kind
  234, so no return outside `TypeNode` is shown, and the census reports its
  return, whose claim keeps the arm of kind 234. Each source repairs its
  refusal by excluding kind 234 first;
- a changed failure (2): `declaration-graph.mts#statementsOnPath`, refused
  in search on main, refused in the producer on the branch at
  `moduleSpecifier` after `isImportDeclaration`, which also accepts
  `JSImportDeclaration`, a node without it; `fragment-statements.mts#patternDefaults`,
  past "missing field elements" (the guard's `false` edge on a
  `BindingName`), now refused in search inside its `flatMap` callback.

<a id="census-stable-members"></a>
The `tools/` census of 77ca829 (main) and of ab51b0c (stable members: linked
reads, branch witnesses, stable links), run back to back on one machine
(2026-10-20, load averages 3 to 18): 123 of 373 slices verify on main, 134
of 373 on the branch; none verified on main fails on the branch.

- verified on the branch only (11): seven read a member path after a test of
  it (`array-prototype.mts#splitSeparators`, `fragment-support.mts#staticFieldOf`,
  `#staticMethodOf`, `#unnamedMember`, `#typeParameterMentioned`,
  `#bindingScope`, `written-applications.mts#literal`); four were refused in
  search or at an edge (`declaration-graph.mts#typesOnly`,
  `fragment-classes.mts#ownClass`, `fragment-statements.mts#patternDefaults`,
  `type-term.mts#propertyKey`);
- of the 26 slices refused at a path read on main, 6 verify (above), 17
  move past it and 3 keep it: `fragment-expressions.mts#moduleFunction` and
  `#memberMayBeWritten`, whose path's root `target` is no immutable binding,
  and `fragment-statements.mts#pattern`, whose read follows a call of
  `gate.fail` on the guard's `false` edge. Of the 17: the 8 slices reaching
  `expr`'s negated bigint, where
  `gate.span(node)` runs between the test and the read, now stop at
  "missing field computed" (10456); `refuseReceiverForm`, `confined`,
  `selfConstructs` and `assertsNothing` stop in search or at a write;
  `knownLocal`, `localArrow`, `memberOf`, `guardOf` and `namespaceMembers` at
  a later missing member;
- beyond those 26: the 21 slices of `fragment-statements.mts` stopped at
  "missing field elements" stop at "missing field text" (3593);
  `hasInstanceClass`, `hasInstanceAlong` and `callableAssign`, refused in the
  producer on main, stop in search;
- a new timeout (1): `fragment-support.mts#shadowingLocals`, refused in
  search on main, the search past 60 s on the branch;
- otherwise the same refusal at another position or a path spelling.

The census of a818552, which reads the sync API's `isUnionType` without its
declared predicate, run after b7787b9's on the same machine (2026-10-20,
load averages 10 to 18): 125 of 369 slices verify. Against b7787b9,
`declaration-graph.mts#primitivesOf`, verified there at that predicate, is
refused in the producer at `getTypes` after `isUnionType`
(`invalid-compiler-api-sync-guard`), a loss by principle: no audited
contract states the predicate. `compiler-api.mts#importsKey` replaces
`#guardModule` and is refused in search at its return.

<a id="census-never-callable"></a>
The census of the slices of `fragment-statements.mts` and `type-term.mts`
alone, on 7e17fb5 (main) and on the branch of the
[`never` call](docs/PROGRAM-TYPING.md#vacuous-edges) and the
[contextual function types](docs/SOURCE-ELABORATION.md#source-closures-and-their-annotations),
run on one machine, the branch twice (2026-10-20): 8 of 34 and 11 of 35 slices
verify on both. Of `fragment-statements.mts`, the 19 slices stopped at
"missing field text" (`protocolPattern` and its dependents) stop at a member
read of a `let` holding a union of objects after a test of it, and
`#pattern` moves from "missing field text" to search, at a numeric array key.
Of `type-term.mts`, the 17 slices stopped at the contextual
`(node: TypeNodeBase) => TypeTerm` stop at a pattern binding a `for...of`
over a program's iterable.

<a id="census-closure-parameter-slots"></a>
Two slices of `fragment-statements.mts`, `protocolPattern` and
`patternStmt`, which calls it, on a654145 (main) and on the branch reading a
closure's assigned parameters by the flow graph's slot or cell decision
(2026-10-21): neither verifies on either. On main both stop at "a read of
expression on a `let` holding a union of objects" (`hoistTarget`'s `first`
and `assignedNames`'s `targets`, `while (ts.isParenthesizedExpression(x))
x = x.expression`); on the branch both stop at "missing field 242", the
reverse lookup `ts.SyntaxKind[s.kind]` in `statements`.

<a id="census-enum-reverse-keys"></a>
The same two slices on 5191b20 (main) and on the branch stating an enum's
reverse keys (2026-10-21): neither verifies on either. On main both stop at
"missing field 242", `ts.SyntaxKind[s.kind]` in `statements`; on the branch
both read it at `string` and stop in search at "closure signature claim is
outside the source annotation", the closure
`d => d.modifiers?.some(m => m.kind === ts.SyntaxKind.DeclareKeyword)` in
`readCannotThrow`.

<a id="census-filter-guard"></a>
The same two slices on 0242a5e (main) and on the branch stating `filter`'s
guard overload (2026-10-21, load averages 4 to 17): neither verifies on
either. On main both stop in search at "closure signature claim is outside
the source annotation", the closure
`d => d.modifiers?.some(m => m.kind === ts.SyntaxKind.DeclareKeyword)` in
`readCannotThrow`. On the branch both pass it, and their evidence search
exceeds the census's 60 s step limit; run to its end (88 s and 93 s of
CPU), each stops at "a numeric array key needs a proved array-index
singleton", the read `node.elements[node.elements.length - 1]` in
`pattern`, which both reach, a refusal the lowering reports without a
location.

<a id="census-index-from-length"></a>
The same two slices on eb3a427 (main) and on the branch keeping a named
type's row per graph, reading node lists at a `number` key by
`%ElementAt%` and reading a family guard's call as a Boolean by its form
(2026-10-22, `TSCERT_STEP_LIMIT=600`): neither verifies on either. On main
both stop in search at "a numeric array key needs a proved array-index
singleton", 88 s each. On the branch both stop in search after 13 s each
at "closure signature claim is outside the source annotation", the
callback `(s) => gate.abrupt(s)` of `statements`' `list.findIndex`, whose
parameter is claimed at `Statement | undefined`. In a reduced program the
same callback calling the module function `abrupt` directly verifies, and
calling it as `gate.abrupt`, a class field holding the function, is
refused alike.

<a id="census-field-calls"></a>
The same two slices on 1e74ca1 (main) and on the branch calling `abrupt` by
its binding (2026-10-22): neither verifies on either. On main both stop in
search after 26 s each at "closure signature claim is outside the source
annotation", the callback `(s) => gate.abrupt(s)` of `statements`'
`list.findIndex`. On the branch both pass it and stop in search after 41 s
each at "closure expression claim", `gate.hoisted.push(...statements)` in
`protocolPattern`, whose spread argument is claimed at a literal array's
type where `push` requires `Stmt`'s row.

<a id="census-push-element"></a>
The same two slices on cb5e3fe (main) and on the branch inferring `push`'s
element from its receiver (2026-10-22, load averages 13 to 20): neither
verifies on either. On main both stop in search after 41 s each at
"closure expression claim", `gate.hoisted.push(...statements)`, the
spread's elements claimed at `Stmt | undefined`. On the branch both
searches exceed the census's 60 s limit; at `TSCERT_STEP_LIMIT=600` both
stop in search after 151 s each at "source expression obligation",
``gate.fail(d, "a `const` needs an initializer")`` in `patternStmt`, where
`d`, `list.declarations[0]`, is claimed at `undefined |
VariableDeclaration`.

<a id="census-read-narrowing"></a>
The same two slices on 526bf6e (main) and on the branch instantiating rows
once and narrowing a receiver past a completed read (2026-10-22,
`TSCERT_STEP_LIMIT=600`, load averages 5 to 15): neither verifies on either.
On main both stop in search after 103 s each at "source expression
obligation", ``gate.fail(d, "a `const` needs an initializer")`` in
`patternStmt`. On the branch both pass it and stop in search after 40 s
each at "source expression obligation", the read `d.initializer` in
`gate.span(d.initializer)`, which `if (!d.initializer) gate.fail(…)`
precedes.

<a id="census-read-narrows-path"></a>
The same two slices on f91d657 (main) and on the branch relating slots an
edge maps from one source and keeping heap facts through inspections
(2026-10-22): neither verifies on either. On both, both stop first in
search after 5 s each at "closure signature claim is outside the source
annotation", the callback `p => bindsName(p.name, id.text)` of
`readCannotThrow`'s `at.parameters.find`. A copy of the `patternStmt`
slice with that callback written as a loop (`TSCERT_STEP_LIMIT=600`) passes
the read `d.initializer` in `gate.span(d.initializer)` on the branch, and
stops in search after 44 s at "source expression obligation",
`gate.fail(d.initializer, UNCLOSABLE)`: the read link through the optional
member `initializer` ends at the calls `gate.iterations.get(…)` and
`d.name.elements.some(…)` before it, since an optional member is no stable
key ([stable keys](docs/HOST-FAMILIES.md#stable-keys)).

<a id="census-closure-arms"></a>
Two slices of `fragment-expressions.mts`, `expr` and `binary`, which calls
it, on eb3a427 (main) and on the branch holding a closure's parameter at
its union's arms and reading each enum's members once in the declaration
graph, each census with a fresh store (2026-10-22): neither verifies on
either. On main both stop at "missing field computed" (10456), the read
`p.computed` after `"spread" in p` in a `map` callback, each parse taking
28.3 s (the census 31 s); on the branch both stop at "missing field
refused" (24491), `inferred && "refused" in inferred`, where the passed
test keeps the open record arm `{ functionType; bagType }`, each parse
taking 9.7 s (the census 12 s).

<a id="census-answered-tag"></a>
The same two slices on 1e74ca1 (main) and on the branch tagging the gate's
answers by `ok` ([the rewrite](docs/SOURCE-REWRITES.md#a-key-tested-with-in-on-an-open-record))
(2026-10-22): neither verifies on either. On main both stop at "missing
field refused" (24491), `inferred.refused`; on the branch both stop at
"missing field properties" (24978), `initial.properties` after
`ts.isObjectLiteralExpression(initial)` with `initial = node.arguments[1]`,
an index read TScert types `Expression | undefined`
([required rewrite](docs/SOURCE-REWRITES.md#an-index-read-whose-range-a-check-elsewhere-establishes)).
Reduced programs show the guard narrowing a parameter of type `Expression`
and refusing the same read at `Expression | undefined`, and at
`args[1]` of `readonly Expression[]`; with `initial !== undefined` tested
first the read verifies.

<a id="census-callable-assign"></a>
The same two slices on 6f94a66 (main) and on the branch where
`callableAssign` returns the nodes it tests
([the rewrite](docs/SOURCE-REWRITES.md#an-index-read-whose-range-a-check-elsewhere-establishes))
(2026-10-22): neither verifies on either. On main both stop at "missing
field properties" (24978); on the branch both stop at the producer's "a
spread of an intersection of other than disjoint records is outside the
fragment", with no location ([the reading](docs/SOURCE-MODEL.md#a-spread-of-an-intersection)).

<a id="census-spread-intersection-meet"></a>
The same two slices on 8ab4e04 (main) and on the branch reading a spread of
an intersection at its operands' meet
([the reading](docs/SOURCE-MODEL.md#a-spread-of-an-intersection))
(2026-10-22): neither verifies on either. On main both stop at "a spread of
an intersection of other than disjoint records is outside the fragment";
on the branch both read `objectFields`' spread and stop in the producer at
"missing field name" at `memberOf`'s `p.name`
([the investigation](#member-of-spread-guard)).

<a id="census-rest-positions"></a>
Two slices of `type-term.mts`, `readTypeTerm` and `typeTerm`, which calls
it, on afbaa8b (main) and on the branch tagging a rest parameter's reading
by `k` ([the rewrite](docs/SOURCE-REWRITES.md#a-rest-parameters-reading-tested-with-in))
(2026-10-22): neither verifies on either. On main both stop in the
producer at "missing field positions" (`signatures`); on the branch both
stop in Lean's search at "read of a field 'length' the contract does not
name", with no location, the alias check's length comparison
([the reading](docs/PROGRAM-TYPING.md#the-length-of-a-union-of-arrays)). With that comparison
removed from the slice, the search stops at a closure of `mapped`,
`keys.some(k => !(k.k === "atom" && (k.name === …)))`: "No rule derives
this readAt" at `k.name`.

<a id="census-union-length"></a>
The same two slices on 451642b (main) and on the branch reading `length`
of a union of arrays at each member
([the reading](docs/PROGRAM-TYPING.md#the-length-of-a-union-of-arrays))
(2026-10-22): neither verifies on either. On main both stop at "read of a
field 'length' the contract does not name"; on the branch both stop at the
closure of `expandMapped` (`mapped`), "closure expression claim at
[26388,26394): evidence search failed", the second `k.name` of
`!(k.k === "atom" && (k.name === "string" || k.name === "number" || …))`
([the investigation](#negated-disjunction-reread)).

<a id="callable-alias-meet"></a>
**Investigation of an alias of function types met with a record.**
`type Calls = (() => number) & ((n: number) => number)` met with
`{ tag: string }` in a parameter's annotation is refused by Lean's reading
of the declarations: "the intersection is empty". The same three operands
written in the annotation verify (`spread-intersection-callable-grouping`).
Which step of the declaration's normalization yields no clause is not
established.

<a id="member-of-spread-guard"></a>
**Investigation of `memberOf`'s read past a spread guard.** In
`fragment-expressions.mts#memberOf`, the loop over an object literal's
`properties` handles `ts.isSpreadAssignment(p)` in an `if` whose body ends
in `continue`, then reads `p.name`. Every arm of `ObjectLiteralElementLike`
but `SpreadAssignment` states `name`. Cause: the guard's call was an
ordinary call of its signature, which narrows nothing, not the tag test of
`p` (`host-guard`). The front end writes a guard's call on a name as that
test where the name's read cannot throw (`readCannotThrow`), and that
function's scope walk recognized parameters and block declarations alone,
so a `for...of` binding fell through to `false`. Reduced:
`for (const p of ps) { if (ts.isSpreadAssignment(p)) continue; p.name }`
is refused, the same body over `const p = ps[i]` verifies. Repair: the walk
stops at every binding it passes, a loop's binding initialized in the
loop's body (and a `for` loop's test and update), a `catch` clause's in its
block, a parameter after its own declaration
([the rule](docs/HOST-FAMILIES.md#calls); `compiler-api-guard-loop-binding`
and the five `invalid-compiler-api-guard-loop-*` negatives, run under
Node).

<a id="census-member-of-spread-guard"></a>
The slices `fragment-expressions.mts#expr` and `#binary` (2026-10-22): on
a790a88 both stop at "missing field name" at `memberOf`'s `p.name`; on the
branch both move past it and stop at "missing field text" at
`memberMayBeWritten`'s `target.argumentExpression.text`, a guard on a
member path of a `let` the function assigns.

<a id="census-slot-paths"></a>
The slices `fragment-expressions.mts#expr` and `#binary` (2026-10-22): on
036caea (main) both stop at "missing field text" at `memberMayBeWritten`'s
`target.argumentExpression.text`, a path whose root `target` is a `let` held
in a slot; on the branch both move past it and stop at "missing field
target" at `lambda`'s `b.target`, read in
`b?.k === "destructure" ? [b.target, b.default_] : …` after a test of
`b?.k`, an optional chain's tag. The slice `memberMayBeWritten` verifies on
the branch.

<a id="census-chain-comparison"></a>
The slices `fragment-expressions.mts#expr` and `#binary` (2026-10-22): on
e199d42 (main) both stop at "missing field target" at `lambda`'s
`b.target`, read after `b?.k === "destructure"`; on the branch both move
past it and stop at "a write of 'bindings', a key the object's type does
not state", `gate.bindings = bindings` in the slice's binding lookup, a
key-adding write to the gate.

<a id="census-for-of-patterns"></a>
Two slices of `type-term.mts`, `readTypeTerm` and `typeTerm`, which calls it,
on 5191b20 (main) and on the branch destructuring a `for...of` pattern over a
program's iterable in the closing region (2026-10-21): neither verifies on
either. On main both stop at the gate's "a pattern binding a `for...of` over
a program's iterable", `quantified`'s `for (const [index, p] of
typeParameters.entries())`; on the branch both stop at "statement outside the
fragment (TypeAliasDeclaration)", a type alias declared in a function body.

<a id="census-block-types"></a>
The same two slices on 0242a5e (main) and on the branch reading block-scoped
type declarations (2026-10-21): neither verifies on either. On main both stop
at the gate's "statement outside the fragment (TypeAliasDeclaration)",
`members`'s `type Index`; on the branch both read it and stop in the
producer at "bind requires a single arrow and a valid argument prefix": the
slices' only bound calls are the iterators' `next` the protocol lowering
binds, in `visitType` and in `quantified`'s and `signatures`' `for (const
[index, p] of ….entries())`.

<a id="census-union-host-bind"></a>
The same two slices on 1e74ca1 (main) and on the branch binding a member to a
union of hosts (2026-10-22): neither verifies on either. On main both stop in
the producer at "bind requires a single arrow and a valid argument prefix",
`visitType`'s spread of `bound`, a `ReadonlySet<string>` defaulted to a
`Set<string>`, whose iterator is a union of two; on the branch both stop in
the producer at "missing field positions", `signatures`' `"positions" in
contract`.

<a id="census-ddcf13a"></a>
The `tools/` census of ddcf13a (main, after the stage store, the replayed
parse and the controls' move to `make test`; `make census`, 2026-10-22,
8 min 38 s cold, load averages up to about 10): 139 of 435 slices verify,
against 136 of 390 on dcc972d. Of its 1,850 stage invocations, 1,696
executed, 134 replayed, 7 timed out and 13 reported a timeout an earlier
attempt recorded at the same limit.

- verified on ddcf13a only (4): `declaration-graph.mts#untypedAmbientField`,
  past the step limit on dcc972d; three new slices of `files.mts`,
  `#ancestors`, `#privateDirectory` and `#takeQueryFailure`;
- verified on dcc972d only (1): `files.mts#io`, rewritten by the stage store,
  refused at the gate at an `instanceof` whose right operand is no class
  declared at the file's top level;
- new slices (47): the stage store's and the observed parse's functions in
  `tools/`, 3 verified, 36 refused at the gate and 8 in search;
- timeouts (20, 21 on dcc972d): the `fragment-statements.mts` chain past
  `filter`'s guard overload and `fragment-support.mts#shadowingLocals`.

<a id="census-dcc972d"></a>
The `tools/` census of dcc972d (main, after the vacuous never-call edges,
contextual callables, closure parameter slots, enum reverse keys, `for...of`
patterns, `filter`'s guard overload and block-scoped type declarations;
2026-10-21, 9 min 43 s, load averages 2.4 → 14.8): 136 of 390 slices
verify, against 134 of 385 on 6ec97aa. No slice is refused at checking:
every slice whose search wrote evidence verifies.

- verified on dcc972d only (4): `fragment-expressions.mts#refuseReceiverForm`,
  refused in search on 6ec97aa; three new slices,
  `fragment-classes.mts#identityKey` and `#registerEquation` and
  `fragment-statements.mts#typeStatement`;
- verified on 6ec97aa only (2), each now past the 60 s step limit and each
  verified when run alone with no limit:
  `declaration-graph.mts#untypedAmbientField` (57 s for the whole pipeline)
  and `fragment-support.mts#shadowingLocals` (70 s), at load averages near
  10;
- timeouts (21, none on 6ec97aa): those two and 19 slices of
  `fragment-statements.mts` (`protocolPattern`, `patternStmt`, `statements`,
  `stmt` and the statement forms reaching them), which past `filter`'s guard
  overload reach a search of about 90 s ([filter guard](#census-filter-guard));
- new slices (5): the three above, `family-activation.mts#enumObjectMatches`
  (refused at the gate) and `fragment-statements.mts#forOfPattern` (refused
  in search).

Of the 341 slices (2026-10-19, cb0d236), 82 fail in the producer and 69
in search; of the drivers' 48, 4 and 8. By the judgment that fails:

- reading a compiler node's member after a `ts.isX` guard or a `.parent`
  walk (the producer's "missing field": 55; in search, `forEachChild`,
  `.parent` and guard edges: about 25), and a `let` holding nodes read after
  a test (6): the compiler-node narrowing the host-families work covers;
- a user guard's promise not established by its body (`isObject`,
  `isRecord`: 9) and the reads it would narrow (about 16, `atom.required` in
  `claim-text.mts` among them): guard recognition; guard closures passed as
  callbacks (5) are claimed at the callback's signature, and stop at the
  guard overloads of `every` and `filter` the overlay does not state (4 of
  `shadow-contracts.mts`, where TypeScript narrows the array a guard tested)
  and at a host guard (`interfacesOf`);
- a read of a key `in` found on an open object (4, and 2 drivers): the
  [proposal](docs/PROGRAM-TYPING.md) under review;
- past their spreads of a bounded binder and of an intersection of records
  (5, 2026-10-19): `promisedBinders` returns the copy at its binder `B`,
  refused on principle, a binder narrower than its bound fixing a field the
  copy replaces (`invalid-spread-binder-result`), and `promisedMethods` calls it; the
  `hostBrands` family reads `b.bound` through the intersection
  `SourceTypeParameter<TypeTerm> & { default; span }` after `b.bound &&`,
  and maps through callbacks calling its `brand` and `fail` parameters,
  whose effects no claim states, so `map`'s results admit holes;
- `Number` both called and read through its members, a callable with
  readonly members no clause states (4), and the enum helpers past it (3);
- `reduce` without an initial value (2 drivers, `refusedByName` and
  `refusedByTypeScript`): the prototype contract states one signature per
  member, `reduce<U>(callback, initial)`; `runsCode` and `selfConstructs`,
  past their parameter's closure default, stop at `forEachChild` and a
  guarded node's `text` (2026-10-19); key-adding writes through a parameter (`gate.bindings`,
  `process.env`: 2, and 2 drivers); reads at keys an inherited member may
  name (2); singletons.

Of the 24 of `dev/`, the record tools and the lowering dump, all 24 (2026-10-18), each
sliced with the same-file declarations it uses, their imports from
`record-render`, `control-flow` and `calculus` certified. `printGraph`'s
evidence search covers `decodeTerm`, which `decodeNode` reads, and takes
48 s of wall time on a machine at load 27, near the 60 s step limit; four
slices run at once exceed it (2026-10-18). `control-flow.mts` verifies
whole.

Of the 37 functions of `pipeline/*.mts`, `keepRunDirectories`, `isJsonArray`
and `typeScriptErrors` verify; of the 13 of `tests/`, `docs.mts`'s seven and
`rule-inventory.mts`'s `withoutBlockComments` and `alternatives`
(2026-10-19, the slices of `tests/` with `pipeline/*.mts` beside them).
Their first blockers, by the number of slices each stops:

- Node's `Buffer`, through `readFileSync` and `spawnSync` without an
  encoding: `ArrayBufferLike`, an indexed access into a named type (5), and
  `Buffer<ImplicitArrayBuffer<…>>`, a conditional type over a signature's own
  binder computed only at an instance (2);
- the worker's socket, `Duplex` a member the checker synthesises (4), and
  `createHash`'s `TransformOptions` (1);
- a member read after `assert` narrowed a union (the producer's "missing
  field", 2, and `process.stdout`, outside the reviewed globals, 1);
- a key-adding write of `instantiate` in search (`checkOverloads`,
  2026-10-19, past a lowering that recursed without end on two `?.` links
  over an element read, `optional-chain-element-receiver`);
- a key-adding write to `process.env` (2);
- `import.meta`, `new Array(n)`, a mapped type over `Readonly` and a record at
  an index signature (1 each);
- the producer or the search (15), each a separate investigation, among them
  the two `must` helpers, whose `assert.ok` takes a message that is no literal
  and so narrows nothing.

`node:assert/strict`'s `equal` promises its actual is the expected value only
in its declaration: the promise is generic, and the producer encodes no
generic promise signature ("quantified callable claim encoding"), which a
program's own generic assertion function meets too (`node-assert-equal-promise`,
a gap).

`readFragmentFile` and `readClaimsFile` in `pipeline/verify-source.mts` read
back a document the run wrote, for a test to forge, and assert its type with
`as` (reason at the assertion) rather than decode it: no TypeScript decoder
of the Fragment or the claims document exists, and the tests reach about 100
fields deep in them. The two stay outside the goal by decision; what they
read is decoded again by Lean before anything is checked.

Two forms of the record tools are rewritten for a verifier limit, not
for a departure from the fragment; each rewrite is reverted when its limit
lifts: element reads the code already guards by a test of the same element
(`mathRoles`' `afterRelation` and `textWord`, `docs.mts`'s `numbered`;
`guarded-element-read-refused`);
and a `flatMap` callback returning a string (`card`;
`flat-map-scalar-result-refused`).

The goal is every function of the repository's own TypeScript verified:
`tools/`, `pipeline/`, `tests/` and `dev/`, about 21,000 lines (the sources
under `pipeline/examples/` are the cases' inputs, many refused by design).
Verification states safety, each function's annotated contract at every
call, not that the parser reads TypeScript correctly. A scan of that code
against the fragment (2026-10-16) gives the work, each item its own design:

- **The compiler API.** About 120 functions read TypeScript's syntax tree
  through `typescript/unstable/ast` and its checker through
  `typescript/unstable/sync`; [the compiler API](docs/COMPILER-API.md)
  specifies the contract they are verified under. Its implementation waits
  on [guard recognition](docs/HOST-FAMILIES.md#guard-recognition),
  [stable members](docs/HOST-FAMILIES.md#stable-members) and guard
  signatures for the sync API's type guards; a generic method called on a
  node, `forEachChild<T>`, is refused.
- **Guard signatures.** A guard's promise is part of its function type,
  proved at its definition and consumed at a call, for any promised type
  and across modules.
- **Bounds of every alias application.** An alias with a bounded parameter
  keeps the obligation that its arguments meet their bounds, whatever its
  body.
- <a id="regular-expressions-left"></a>**Regular expressions left.** A
  literal, `exec`, `test` and the string methods dispatching to a regex are
  admitted ([regular expressions](docs/SOURCE-CONTRACTS.md#regular-expressions)).
  Left: a replacement callback, whose argument list follows the shape
  (`(match, p₁ … pₙ, offset, input[, groups])`, every match collected before
  the first call, its result a string); `new RegExp(p, f)` of strings, a
  native regex of the conservative shape; a regex's properties, `lastIndex`
  (own, not enumerable, a number) and the accessors `source` and `flags`,
  read through reserved host-relative members so that no record view states
  them, with `in`, patterns and computed reads of their keys accounted for;
  a loop over a structural iterator TypeScript types `RegExpStringIterator`,
  through the iterator protocol; and the same native mark on `SetIterator`
  and `MapIterator`, whose loops are chosen by TypeScript's type alone.
- **The library globals left.** `Array.prototype.flatMap` (79 calls) and
  `flat`, `String.prototype.match`, `matchAll`, `padEnd`, `padStart` and
  `search`, `Object.fromEntries`, `hasOwn` and `assign`, `Array.from`,
  `Math` but `max` and `min`, `parseInt`, and `JSON.stringify` of an
  object, whose `toJSON` runs client code.
- **Node's modules.** `node:fs`, `path`, `child_process` (`spawnSync`,
  `execFileSync`, `fork` and its messages), `os`, `crypto`, `vm`, `net`,
  `module`, `assert/strict` (assertion functions) and `process`.
- **Classes and `this` parameters.** The parser's `Gate` class, the functions
  of `fragment-*.mts` declaring `this: Gate` (198 reads of `this`).
- **Imports between the repository's modules.** Default imports, and a
  value imported from another module certified against its signature, which [module composition](#module-composition) proves sound.
- **The code's own departures from the fragment.** Downcasting `as`
  assertions and module-level `let`: the code changes to meet the fragment.
- **Proof precision.** Of the slices past the gate, about half fail in
  proposal or search; each failure is a separate investigation.

