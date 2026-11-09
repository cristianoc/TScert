# Glossary

The project terms a commit record, a review page or a deck may use without
defining them. Each line gives a term, its meaning in one plain sentence and
the section that owns it; the owner holds the definition, and this list
holds none. A term outside this list is defined where a record first uses
it. Areas follow the pipeline's order; terms are alphabetical within each.

## Commit records

- **`⚠`**: after an Effect line's old outcome, marks that outcome unsound, an acceptance of an unsafe program ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **Before / After**: the old and the new form of a modified object ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **change block**: a heading `<Kind> <added|modified|removed> (<object>):` and its forms ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **commit record**: a commit message stating the change as a semantic diff with its reason, sections then trailers ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **Counterexample**: for a refusal, the program it excludes and what Node prints for it ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **Effect line**: one pipeline case with its kind, its outcome before and after, and the reason ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **forged:** (in `Tests:`): a control that feeds the verifier a tampered document or claim, named by what it forges ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **Gap**: what stays unsupported after the change, and what it needs ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **kind** (of a change): `Rule`, `Semantics`, `Definition`, `Typing`, `Lowering`, `Refusal`, `Trust`, `Wire`, `Docs`, `Example`, `Counterexample` or `Tooling` ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **Measured**: a number, before and after, with what produced it and when ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **object** (of a change): the stage and the concept a change block names in parentheses, such as `type reader: the members of a union` ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **Outcome**: the trailer giving the change's result, `verified`, `refused`, `gap` or `no-behaviour-change` ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **Parts**: the trailer listing the layers a change touches, such as `lean-rules`, `producer`, `parser`, `wire`, `trust` ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **record page**: a commit record rendered as a page (`make semantic-diff`, `node dev/commit-records.mts`) ([rendering](../.claude/skills/review/SKILL.md#rendering)).
- **semantic diff**: the delta on the high-level objects code implements (a rule, a lowering, a trust assumption), rendered as a page by `make semantic-diff` ([principles](../.claude/skills/review/SKILL.md#principles)).
- **Soundness**: the section saying why a change is sound, or where it is proved ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **Trust** (trailer): the new trust sentence a change adds, or `none` ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **Units**: the trailer naming the functions a change makes verify or refuse, as `file#function` ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **Why**: the opening section, the problem in concrete terms: the failing program, how it showed, why the design could not handle it ([principles](../.claude/skills/review/SKILL.md#principles)).

## The pipeline

- **calculus**: the small formal language, defined in Lean, into which a function is translated and whose execution and safety are defined ([operational language](SEMANTICS.md#operational-language)).
- **calculus graph**: the translated program, a graph of calculus code over which typing and safety are defined ([stages](DESIGN.md#stages)).
- **certificate**: a finite description of the typing and subtype derivations for a request, which search proposes and the checker validates ([stages](DESIGN.md#stages)).
- **checker** / **verifier**: the Lean program that validates a certificate against the exact translated program; its success is what acceptance means ([stages](DESIGN.md#stages), [the CLI](REQUEST-PROTOCOL.md#run-the-verifier)).
- **claim**: a type or state description the producer proposes at a program point; it becomes an obligation where extraction uses it ([claims](DESIGN.md#claims-and-the-claim-reader)).
- **claims document** / **SourceClaims**: the producer's output, every claim with its identity ([source claims](SOURCE-CLAIMS.md)).
- **code unit** / **unit**: a function, a group of functions that reach each other by name, or a module's initialization body, certified together and given one verdict ([modules and code units](DESIGN.md#modules-and-code-units), [what "verified" means](DESIGN.md#what-verified-means)).
- **declaration graph** / **declaration document**: the types and external values a source uses, as the front end collects them ([stages](DESIGN.md#stages)).
- **declaration reader**: the type reader's part that reads the declarations a type reaches ([source contracts](SOURCE-CONTRACTS.md)).
- **elaboration** / **extraction**: Lean's translation of a function, with the proposed types, into a calculus graph and its obligations ([stages](DESIGN.md#stages)).
- **environment**: the proposed types of the local bindings at a program point, with facts about their current contents ([stages](DESIGN.md#stages)).
- **equation lowering**: Lean's translation of declarations, annotations and claim labels into recursive type equations ([implementation map](DESIGN.md#implementation-map)).
- **evidence**: the certificate and the facts it cites, as the verifier receives them ([evidence](REQUEST-PROTOCOL.md#evidence)).
- **execution plans**: the statement graph and the evaluation and binding schedules Lean derives from the source before types are known ([stages](DESIGN.md#stages)).
- **execution point** / **program point**: a node of a body's statement graph, where entry claims attach ([claims](DESIGN.md#claims-and-the-claim-reader)).
- **Fragment**: the parser's output, a syntax tree of the supported source constructs ([stages](DESIGN.md#stages), [format](FRAGMENT-FORMAT.md)).
- **front end**: the TypeScript program on the compiler's API (`tools/`) that reads the source and the declarations it uses ([stages](DESIGN.md#stages)).
- **gate** (the parser's gate): the parser's admission of a source form only where it is lowered faithfully, with a located refusal elsewhere ([adding a source form](SOURCE-ELABORATION.md#adding-a-source-form)).
- **lowering**: a translation into a simpler program representation; the parser's fixes execution order, Lean's builds the typed calculus program ([architecture](DESIGN.md#architecture)).
- **obligation**: a typing or subtype judgment the extracted program must meet for acceptance ([claims](DESIGN.md#claims-and-the-claim-reader)).
- **parser**: the front end's part that emits the Fragment (`tools/fragment-parse.mts` and its parts) ([stages](DESIGN.md#stages)).
- **pipeline**: parse, plan, propose, elaborate, search, check, run by `pipeline/verify-source.mts` ([the entry point](DESIGN.md#the-pipeline-entry-point)).
- **producer**: the OCaml program that proposes the type of every expression and variable; nothing it says is trusted ([stages](DESIGN.md#stages), [the producer](../ocaml-producer/README.md)).
- **request**: the translated program with the obligations it must meet, which search and the checker read ([stages](DESIGN.md#stages)).
- **search**: Lean's untrusted procedure that looks for a certificate; its failure shows nothing about safety ([search](DESIGN.md#search)).
- **source map**: diagnostic metadata linking calculus nodes to source descriptions; it supplies no evidence ([claims](DESIGN.md#claims-and-the-claim-reader)).
- **source span**: a pair of offsets locating syntax in the source file ([claims](DESIGN.md#claims-and-the-claim-reader)).
- **type label**: a name of a type in the graph of recursive type equations; its spelling has no meaning of its own ([claims](DESIGN.md#claims-and-the-claim-reader)).
- **type reader**: the translation of annotations, declarations and library contracts into graph types ([source contracts](SOURCE-CONTRACTS.md)).
- **wire**: the JSON documents passed between stages (Fragment, claims, request, evidence), each one declared type ([languages](LANGUAGES.md)).

## Outcomes and acceptance

- **binding-annotation** (obligation): a refusal's obligation kind for a binding whose initializer must meet its annotation ([node and expression obligations](OBLIGATION-DIAGNOSTICS.md#node-and-expression-obligations)).
- **checkUnitJson_safe**: the one headline theorem, whose premise is the verifier's exact success condition and whose conclusion is safety of every accepted function ([acceptance invariant](../AGENTS.md#acceptancesoundness-invariant)).
- **error** / **tool failure**: an outcome certifying nothing: a crashed, killed or timed-out stage, or a failed file-system or compiler request ([tool failures](OBLIGATION-DIAGNOSTICS.md#tool-failures)).
- **exhausted**: a verification budget was reached before the obligation was decided ([the entry point](DESIGN.md#the-pipeline-entry-point)).
- **gap**: a case or a construct that stays unsupported for a reason open work states, not a principled refusal ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **refused**: rejected by the pipeline, at the source (unsupported) or for want of a derivation (unverified) ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **safety**: an accepted unit, given inputs meeting their types, returns a value of its type, steps or throws; it never gets stuck or returns a wrong value ([principles](DESIGN.md#principles)).
- **unsupported**: source processing or proposal refused a construct (`unsupported/source`, `unsupported/proposal`) ([the entry point](DESIGN.md#the-pipeline-entry-point)).
- **unverified**: search or checking did not establish a required derivation (`unverified/search`) ([the entry point](DESIGN.md#the-pipeline-entry-point)).
- **verified**: certificate checking accepted the extracted request ([the entry point](DESIGN.md#the-pipeline-entry-point)).

## Cases, controls and tests

- **case** / **pipeline case**: a source file with its expected outcome, run through the whole pipeline (`pipeline/cases.mts`) ([which tests to keep](../AGENTS.md#which-tests-to-keep), [test index](../tests/README.md)).
- **control**: a check on an input no case can make, such as a forged document or a mutated verifier (`pipeline/test.mts`) ([controls](STAGE-STORE.md#controls)).
- **forged claim** / **forged document**: a claim or document a control writes by hand to show the verifier refuses it ([controls](STAGE-STORE.md#controls)).
- **mutation verifier**: a test-only verifier build in which a control disables a selected check (`TSCERT_TEST_MUTATIONS`), to show that check is load-bearing ([controls](STAGE-STORE.md#controls)).
- **negative case**: a case expected to be refused ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **Node counterexample**: a negative case run under Node to show the behaviour its refusal excludes (`tests/node-runs.mts`) ([adding a source form](SOURCE-ELABORATION.md#adding-a-source-form)).
- **positive case**: a case expected to verify ([the record](../.claude/skills/review/SKILL.md#the-record)).
- **suite** (`make test-checks`, `make test-cases`; `make test` runs both): the fast checks and controls, and the pipeline cases ([the suite's shape](../AGENTS.md#the-suites-shape-and-the-rules-that-keep-it)).

## Stage store, census and measurement

- **attempt**: one execution of a stage invocation; within it, an observed stage's record is being made ([shared work](STAGE-STORE.md#shared-work)).
- **census**: every named top-level function declaration with a body in a directory (`tools/` by default), each module checked whole, unit by unit, the benchmark of front-end coverage ([function coverage](DESIGN.md#function-coverage-and-release-thresholds), [measuring coverage](../AGENTS.md#measuring-coverage-once-on-main)).
- **census record**: a census's persistent record: per file its rounds, its units' results, its omitted units and its stage invocations with their timings ([census records](STAGE-STORE.md#census-records)).
- **entry**: a stored stage result, published under its key and replayed when the key matches ([entries and timeouts](STAGE-STORE.md#entries-and-timeouts)).
- **front-end function coverage**: shallow verified census functions divided by all census functions in `tools/`, the headline and release metric ([counting and release thresholds](DESIGN.md#function-coverage-and-release-thresholds)).
- **invocation**: one call of a stage through the common mechanism, with its input description and recorded result ([the stage store](STAGE-STORE.md)).
- **key** / **stage key**: the digest of a stage, its implementation and its complete input description ([keys](STAGE-STORE.md#keys)).
- **ledger**: every answer the file system gave one compiler over its lifetime, noted in each record that uses it ([shared work](STAGE-STORE.md#shared-work)).
- **module isolation**: the conjecture that a module lowered in a parser compiler of its own is the one lowered in its importer's, byte for byte ([trust surface](DESIGN.md#trust-surface)).
- **module stage**: the observed stage, nested in a parse, that lowers one imported module alone in a parser compiler of its own ([shared work](STAGE-STORE.md#shared-work)).
- **Node-origin observation**: a file-system answer standing for a read Node's own resolver or loader made, which is always read afresh ([shared work](STAGE-STORE.md#shared-work)).
- **observations**: the file-system answers an observed stage received, each an operation, a path and an answer ([observed stages](STAGE-STORE.md#observed-stages)).
- **observed stage**: a stage keyed by what it read, because its inputs are known only after it runs: the parse and TypeScript's diagnostics ([observed stages](STAGE-STORE.md#observed-stages)).
- **pre-key**: what an observed stage's key binds before it runs ([observed stages](STAGE-STORE.md#observed-stages)).
- **process cache**: a result kept in memory for the life of one worker process, such as a Node resolution ([shared work](STAGE-STORE.md#shared-work)).
- **query omission**: the conjecture that a compiler query asked again of an unreleased snapshot answers its first text, and omitting the repeat changes no later answer ([shared work](STAGE-STORE.md#shared-work)).
- **read set**: the observations a piece of work was computed from, which decide when it is served again ([shared work](STAGE-STORE.md#shared-work)).
- **record** (of an observed stage): the observations a stage collects while it runs; a record *being made* belongs to a stage still running ([shared work](STAGE-STORE.md#shared-work)).
- **replay**: serving a stored result whose key matches instead of executing the stage ([replay and trust](STAGE-STORE.md#replay-and-trust)).
- **retained declaration session**: a worker's compiler of a named project, kept between declaration collections ([retained declaration sessions](STAGE-STORE.md#retained-declaration-sessions)).
- **shallow verified** / **deep verified**: a census function whose own unit is accepted / whose unit and every unit of its dependency closure are ([function coverage](DESIGN.md#function-coverage-and-release-thresholds)).
- **shard** (`SHARD=i/n`): one of n processes splitting a census by files ([measuring coverage](../AGENTS.md#measuring-coverage-once-on-main)).
- **shared work**: front-end work served again within a process at the lifetime its inputs fix: attempt answers, resolutions, query answers ([shared work](STAGE-STORE.md#shared-work)).
- **snapshot**: a state of a compiler's program that queries are asked of, held until the front end releases it ([retained declaration sessions](STAGE-STORE.md#retained-declaration-sessions), [shared work](STAGE-STORE.md#shared-work)).
- **stage**: one step of the pipeline (parse, propose, search, check) or one operation of a control, run through one invocation mechanism ([the stage store](DESIGN.md#the-stage-store)).
- **stage store**: the content-addressed store from which every stage replays ([the stage store](STAGE-STORE.md)).
- **statement coverage**: the percentage of executable statements inside the census functions' bodies that the census verifies ([statement coverage](DESIGN.md#statement-coverage)).
- **step limit** / **timeout**: the time after which a stage is killed, and the observation recording it at that limit ([the stage store](../AGENTS.md#the-stage-store), [entries and timeouts](STAGE-STORE.md#entries-and-timeouts)).

## Calculus and semantics

- **activation**: one run of a function body, whose environment holds its slots ([slot or cell](SOURCE-ELABORATION.md#slot-or-cell)).
- **array invariant**: every object owning an array store is a built-in array with `Array.prototype` and no own `constructor`, `then`, `toJSON` or `ArrayProto` key ([the array invariant](SEMANTICS.md#the-array-invariant)).
- **built-ins**: the objects and prototypes of the JavaScript global environment a program runs in ([arrays](SOURCE-MODEL.md#arrays)).
- **cell**: a heap location holding a binding the closures capturing it share ([slot or cell](SOURCE-ELABORATION.md#slot-or-cell)).
- **density** / **dense** / **readable** / **sparse**: an array contract's presence mode: every index present, every read typed, or holes admitted ([lasting decisions](DESIGN.md#lasting-decisions), [the fact](FOOTPRINTS.md#the-fact)).
- **graph code**: a body, function or closure, as a calculus graph with its own certificate ([graph code](SEMANTICS.md#graph-code)).
- **heap**: the map from locations to their current values ([heap and contracts](SOURCE-MODEL.md#heap-and-contracts)).
- **hole**: an index below an array's length that holds no element ([the fact](FOOTPRINTS.md#the-fact)).
- **intrinsic** (`%Name%`): a trusted value no source name spells, by which the parser lowers a host operation such as `await` or iteration ([async and iteration](SOURCE-MODEL.md#async-and-iteration)).
- **location**: an address in the heap, with a fixed storage contract in the world ([heap and contracts](SOURCE-MODEL.md#heap-and-contracts)).
- **slot**: a binding held in its activation rather than on the heap, because no closure can observe a write to it ([slot or cell](SOURCE-ELABORATION.md#slot-or-cell)).
- **storage contract**: the type every value written to a location or a mutable binding must meet ([claims](DESIGN.md#claims-and-the-claim-reader), [heap and contracts](SOURCE-MODEL.md#heap-and-contracts)).
- **store** (array store): the list of optional element locations an array holds under the reserved key `[]` ([the fact](FOOTPRINTS.md#the-fact)).
- **tag test**: the calculus's primitive runtime test of a value's kind; every guard is one ([operational language](SEMANTICS.md#operational-language), [guards](SOURCE-ELABORATION.md#guards)).
- **trusted step**: an operation assumed to return a value of its result type or throw, never a wrong value ([lasting decisions](DESIGN.md#lasting-decisions)).
- **world**: the assignment of a storage contract to each allocated location; a heap satisfies it when every value meets its contract ([heap and contracts](SOURCE-MODEL.md#heap-and-contracts)).

## Types

- **argument pack** / **pack**: the type of the argument lists a rest parameter admits; it has no value members ([argument packs](POSITIVE-TYPES.md#argument-packs)).
- **arm**: one alternative of a union type or of a claim ([types and clauses](POSITIVE-TYPES.md#types-and-clauses)).
- **binder**: a type parameter of a scheme, a parameter row reassigned at each instance ([parameter and scheme rows](POSITIVE-TYPES.md#parameter-and-scheme-rows)).
- **cell** (union shapes): what a value shows at a discriminant key, the unit structure-directed comparison selects by ([cells](UNION-SHAPES.md#12-cells)).
- **clause**: one constraint on a value's shape (`num`, `strLit s`, a record, a function); a type's body is a positive formula over clauses ([types and clauses](POSITIVE-TYPES.md#types-and-clauses)).
- **dictionary**: a record type with an index signature ([records](POSITIVE-TYPES.md#records)).
- **instance**: a scheme's signatures at chosen type arguments, checked against their bounds ([instances of a scheme row](POSITIVE-TYPES.md#instances-of-a-scheme-row)).
- **label**: a name a type graph maps to a body; a type is a finite union of labels ([types and clauses](POSITIVE-TYPES.md#types-and-clauses)).
- **meet**: the intersection of two types, one construction for every `&` ([conjunction and normalization](POSITIVE-TYPES.md#conjunction-and-normalization)).
- **open** (record): a record type describes named properties without excluding others ([objects and prototypes](SOURCE-MODEL.md#objects-and-prototypes)).
- **own-key bound**: a record type's statement of which keys an object owns, an upper list or an exclusion ([objects and prototypes](SOURCE-MODEL.md#objects-and-prototypes)).
- **packed** (parameter or binder): a rest parameter or type parameter whose values are argument lists, an argument pack ([packed binders](PROGRAM-TYPING.md#packed-binders)).
- **parameter row**: a type-graph entry standing for a generic type parameter, interpreted when the generic is instantiated ([generic bodies](DESIGN.md#generic-bodies)).
- **positive type**: a formula over clauses built with union and intersection only, never negation ([positive types](POSITIVE-TYPES.md)).
- **row**: a label of one of four kinds: clause row, parameter row, scheme row, meet row ([parameter and scheme rows](POSITIVE-TYPES.md#parameter-and-scheme-rows)).
- **scheme** / **type scheme**: a callable contract with universally quantified type parameters ([generic bodies](DESIGN.md#generic-bodies)).
- **shape** (union shapes): the outer kind of a value (null, a primitive, an array, a plain object), the first thing a union comparison splits on ([outer shapes](UNION-SHAPES.md#11-outer-shapes)).
- **subtype certificate**: the evidence that one type is included in another, checked by the certificate checker ([certificates](POSITIVE-TYPES.md#certificates)).
- **tag set**: a clause meaning exactly a finite set of numbers or strings, the type of a union of literals ([tag sets](HOST-FAMILIES.md#tag-sets)).
- **unfolding**: reading a generic application as its definition's body at its arguments, one step at a time ([meaning](RECURSIVE-EQUATIONS.md#22-meaning)).
- **view** / **readonly view**: permission to read a location without permission to write it ([heap and contracts](SOURCE-MODEL.md#heap-and-contracts)).

## Program typing

- **edge** / **true edge** / **false edge**: a transfer of a statement graph, a test's two outcomes among them, each checked against its target's claim ([point claims](PROGRAM-TYPING.md#supplied-point-claims-and-incoming-edges)).
- **frame condition**: what a step may change, stated and checked by its footprint; a fact is preserved where the step leaves the locations it reads unchanged or changes them in the direction that preserves its inequality, as a `push` preserves a length's lower bounds ([frame conditions](PROGRAM-TYPING.md#frame-conditions)).
- **guard**: a test that narrows a value's type on each edge; every guard is a tag test ([guards](SOURCE-ELABORATION.md#guards)).
- **linear fact** / **linear certificate**: an integer inequality $`c\cdot x\le d`$ or disequality over terms (values, field paths, array and typed-array lengths), and the checked list of combination steps deriving one from known facts ([linear facts](ARITHMETIC.md#linear-facts)).
- **locations a fact reads**: the field, store and typed-array-length locations a fact's terms read, which a step must preserve for the fact to hold after it ([linear facts](ARITHMETIC.md#linear-facts)).
- **loop invariant**: the facts at a loop's head, inferred by the producer and checked by Lean on every incoming edge ([reads below the length](PROGRAM-TYPING.md#reads-below-the-length)).
- **narrowing** / **refinement**: the type a tested binding has on an edge, within its type and consistent with the observed outcome ([refinement](PROGRAM-TYPING.md#refinement-under-an-observed-outcome)).
- **path**: a root binding followed by member reads, `x.f.g`, whose narrowing stable members keep ([stable members](HOST-FAMILIES.md#stable-members)).
- **point claim**: the environment claimed at an execution point, which every incoming edge must justify ([point claims](PROGRAM-TYPING.md#supplied-point-claims-and-incoming-edges)).
- **postcondition** (`ensures`): the index facts a signature states of a normal return's heap, at the result's and the call's positions ([postconditions](ARITHMETIC.md#postconditions)).
- **precondition** (`@requires`): the index facts a signature states of the call's values, assumed by the body and checked at every analyzed call ([preconditions](ARITHMETIC.md#preconditions)).
- **sealed handle**: an opaque (branded) type whose `@representation` names its underlying record, which the handle means ([type invariants](ARITHMETIC.md#type-invariants)).
- **type invariant** (`@invariant`): a clause on a type declaration, a precondition of each parameter whose type names it, and a postcondition of each such result and of each such parameter the body never reassigns ([type invariants](ARITHMETIC.md#type-invariants)).
- **typed-array length**: the length of a typed array, fixed for its life under the host's trust, the term $`\mathrm{view}(x)`$ ([typed arrays](PROGRAM-TYPING.md#typed-arrays)).
- **user-defined guard**: a function whose result is a type predicate `x is T`, read as its promise about its argument ([user-defined guards](SOURCE-ELABORATION.md#user-defined-guards)).
- **witness edge**: a read link from a slot to the slot holding a path's member, by which a path's narrowing is checked ([witness edges](PROGRAM-TYPING.md#witness-edges)).

## Effects and footprints

- **change** (`keep`, `grow`, `any`): how a location's contents may change: unchanged, an array store only growing, or anyhow ([changes and footprints](FOOTPRINTS.md#changes-and-footprints)).
- **closed footprint** / **footprint**: `{value: …, store: …}`, the change a call may make to locations holding values and to those holding array stores ([changes and footprints](FOOTPRINTS.md#changes-and-footprints)).
- **effect-qualified signature**: a call signature carrying a guarantee about its effect (a footprint, a guard's promise) ([inferred call effects](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
- **empty footprint**: `{value: keep, store: keep}`, which leaves every existing location's contents unchanged ([inferred call effects](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
- **heap-preserving callback**: a callback certified within a footprint, so that a native relying on a heap fact (`map` on density) may call it ([the checked callback contract](FOOTPRINTS.md#the-checked-callback-contract)).
- **inspection**: a node that reads, tests, computes or allocates and so preserves the heap ([the checked callback contract](FOOTPRINTS.md#the-checked-callback-contract)).
- **native footprint**: the audited footprint of a library native such as `Array.prototype.map` ([native footprints](SOURCE-CONTRACTS.md#native-footprints)).
- **onThrow**: a footprint's flag stating it holds on a throw as well as on normal return ([exceptional footprints](SOURCE-ELABORATION.md#exceptional-footprints)).
- **signature with holes** (`map`'s): the unrestricted signature of `map`, used with a callback that states no footprint, whose result may hold holes ([prototype contracts](SOURCE-CONTRACTS.md#prototype-contracts)).
- **stated effect** / **statement** / **`Within<F, T>`**: a signature's result annotation stating footprint `F` for a result of type `T`, certified from the definition's code ([stated effects](SOURCE-ELABORATION.md#stated-effects)).

## Source reading and the fragment

- **certified import**: an imported function its own module's run certifies at an effect-qualified signature ([certified imports](SOURCE-CONTRACTS.md#certified-imports)).
- **computed type**: a type TypeScript computes (`keyof`, `T[K]`, conditional, mapped), read as its checker computes it ([computed types](SOURCE-CONTRACTS.md#computed-types)).
- **derived source form**: a source form lowered as a combination of forms the calculus already has ([derived source forms](SOURCE-ELABORATION.md#derived-source-forms)).
- **fragment**: the subset of TypeScript the pipeline admits ([fragment boundary](SOURCE-FRAGMENT.md#fragment-boundary)).
- **fragment boundary** / **refusal index**: the list of every refused construct with its reason, owning section and cases ([fragment boundary](SOURCE-FRAGMENT.md#fragment-boundary)).
- **implied bound**: a bound on a type parameter that its signature implies (`Awaited<T>`) ([implied bounds](SOURCE-CONTRACTS.md#implied-bounds)).
- **model limit**: a construct refused because the calculus does not express it ([model limits](SOURCE-FRAGMENT.md#model-limits)).
- **module cell**: a module-level `let`, a cell every call may write ([module cells](SOURCE-ELABORATION.md#module-cells)).
- **overlay**: the reviewed list of library contracts, each entry pinned to the declaration text it was reviewed against ([the overlay](SOURCE-CONTRACTS.md#the-overlay)).
- **prototype contract**: the reviewed contract of a built-in prototype's natives, such as `ArrayProto` for `Array.prototype` ([prototype contracts](SOURCE-CONTRACTS.md#prototype-contracts)).
- **refused on principle**: refused because the construct could produce a wrong value or rests on an unsound TypeScript rule ([refused on principle](SOURCE-FRAGMENT.md#refused-on-principle)).
- **source rewrite**: a change to TScert's own source that makes it verify, with the property the original lacked ([source rewrites](SOURCE-REWRITES.md)).
- **written application**: a generic type applied to arguments in source, `Box<number>` ([written applications](SOURCE-CONTRACTS.md#written-applications)).

## Host families and the compiler API

- **activation** (of a family): turning a host family on by a reviewed description for the installation it names ([activation](HOST-FAMILIES.md#activation)).
- **compiler API**: TypeScript's `typescript/unstable/ast` and `unstable/sync` packages, which the front end's own code uses, verified as the first host family ([the compiler API](COMPILER-API.md)).
- **corrections**: the audited changes to a host declaration where it cannot be its own contract ([corrections](COMPILER-API.md#corrections)).
- **domain obligation**: the obligation that a family guard's argument is within what the guard admits ([undefined arguments](HOST-FAMILIES.md#undefined-arguments)).
- **family contract** / **shape table**: the record type a family member has for each tag value, with the family's marker ([the family contract](HOST-FAMILIES.md#the-family-contract)).
- **family description**: the reviewed data that states a family's tag, shapes, guard table and stable members, read by one interpreter ([the family description](HOST-FAMILIES.md#the-family-description)).
- **guard table**: the audited record of what each library guard's code tests, by which its calls narrow ([the guard table](HOST-FAMILIES.md#the-guard-table)).
- **host family** / **tagged family**: library objects whose one field, the tag, determines their shape, such as the compiler API's nodes by `kind` ([host families](HOST-FAMILIES.md)).
- **host object** / **restricted value**: an object the host package creates, which the model classifies so that no program object passes for one ([host objects](HOST-FAMILIES.md#host-objects)).
- **marker**: the reserved key `[[host]]` at a family's string, by which the model tells a family's objects apart ([the family contract](HOST-FAMILIES.md#the-family-contract)).
- **node guard** / **tag guard**: a compiler-API guard testing a node's `kind`, and one testing a `SyntaxKind` value itself ([guards](COMPILER-API.md#guards)).
- **node invariant**: the compiler API's family contract: each node meets the shape of its `kind` ([the node invariant](COMPILER-API.md#the-node-invariant)).
- **residual**: the one arm of a family union that stands for every tag a unit does not name ([residuals](HOST-FAMILIES.md#residuals)).
- **selection** (the run's): the tag values a run's candidate modules name, one set per family ([the run's selection](HOST-FAMILIES.md#the-runs-selection)).
- **stable member**: a member of a host object that reads one value for the object's life, so a narrowing of it holds across steps ([stable members](HOST-FAMILIES.md#stable-members)).
- **stand-in** (string-tagged): a small host package with string tags, the second instance that tests the family mechanism ([a string-tagged stand-in](HOST-FAMILIES.md#a-string-tagged-stand-in)).
- **tag**: the field whose value determines a family member's shape ([host families](HOST-FAMILIES.md)).
- **transparent** / **obligated** (operation): an operation that treats a restricted value as any value of its type, or one that carries an obligation on it ([operations and their obligations](HOST-FAMILIES.md#operations-and-their-obligations)).
- **unadmitted**: a guard entry's behaviour on `undefined` where the description admits none, so an argument that may be `undefined` fails the domain obligation ([the guard table](HOST-FAMILIES.md#the-guard-table)).

## Trust

- **assumed values** / **assumed of the host**: the trust surface's rows for inputs taken at their declared types, and for properties of every value a unit receives ([trust surface](DESIGN.md#trust-surface)).
- **audited** / **conjectured** / **proved** / **cited**: the strength label of a claim: checked by review against its source, believed and tested, proved in Lean, or taken from a cited work ([footprints](FOOTPRINTS.md), [union shapes](UNION-SHAPES.md)).
- **C0–C7**: the checks binding the compiler API's contract to the installed package: C0 binding, C1 enums, C2 guards (every guard-table entry run under Node), C3 shapes, C4 members, lists and operations, C5 open reads, C6 the stated type guards, C7 symbol tables and type predicates ([binding](COMPILER-API.md#binding-the-contract-to-the-implementation)).
- **caller contract**: the assumption that a value meeting a structural annotation is a plain data object whose stated fields are data properties, whose stated optional field reads, own or inherited, a value of its type where `in` finds it and `undefined` where it does not, and which neither owns nor inherits a key its type's key bounds exclude, a value at `Error` holding its `message` and `name` as strings that are not enumerable own properties; it covers parameters, imports, library and host results and arguments external code passes to callbacks ([trust surface](DESIGN.md#trust-surface)).
- **external code**: code outside the checked units, assumed to preserve the contracts of the program's values it holds ([trust surface](DESIGN.md#trust-surface)).
- **F1–F5**: a host family's trust rows: F1 supplied members (F1′ their modeled realization), F2 runtime stability, F3 guard identity (each guard-table entry describes the function Node runs), F4 transparent tag reads, F5 unwritten constants ([trust rows](HOST-FAMILIES.md#trust-rows)).
- **T1–T8**: the compiler API's trust rows: T1 node invariant, T2 guards, T3 node methods (no server request, no client code but `forEachChild`'s visitors), T4 restricted values, T5 enum objects, T6 sync API, T7 stated type guards, T8 external code ([trust](COMPILER-API.md#trust)).
- **trust row**: one assumption of the trust surface, with where it is stated ([trust surface](DESIGN.md#trust-surface)).
- **trust surface**: everything the safety theorem does not establish, each item a premise or a trusted tool ([trust surface](DESIGN.md#trust-surface)).
- **trusted tool**: a component whose correctness acceptance relies on: the parser, extraction, decoding, TypeScript's checker, Lean, the store's replay ([trust surface](DESIGN.md#trust-surface)).

## Project process

- **deep dive**: a checked-in slide deck that explains a design or a piece of work end to end ([decks](STYLE.md#decks)).
- **draft**: a design kept under `docs/drafts/` for the owner's decision; `§n` and `Dn` in a record name its sections and decisions ([documentation map](DESIGN.md#documentation-map)).
- **investigation**: a WORK row for a failure whose cause is not known ([conventions](../AGENTS.md#conventions)).
- **method-effects draft**: the design of stated effects for class methods and fields, whose decisions D1–D8 records cite ([method effects](drafts/method-effects.md)).
- **owner**: the project's maintainer, who decides the designs kept as drafts ([documentation map](DESIGN.md#documentation-map)).
- **review** (of a branch): the independent review a branch passes before it merges; a commit titled "Review repairs" fixes its findings ([measuring coverage](../AGENTS.md#measuring-coverage-once-on-main)).
- **WORK row** / **status table**: the one place progress is recorded, a row per item of work ([status](../WORK.md#status)).
