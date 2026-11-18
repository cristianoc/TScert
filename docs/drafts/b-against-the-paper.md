# B against the paper

For each definition, rule, axiom, law and example of the paper
[Tolerant frames](tolerant-frames-note/note.tex): the statement of B (the
paper's formalisation in Lean, [where B lives](implementation-and-paper-rules.md#where-b-lives))
that is it, and how far it matches. Part 2 of B's first item in
[the basis](implementation-and-paper-rules.md#the-first-item-b). The original audit was read by gpt-6-astra at commit `7a8c19f5` on
2026-11-17 without a build. This table reconciles those rows with the
additions based on fetched `single-pass` commit
`ba681dfdab8ab41c7d73f3c573f449ab90fedab7`, rebased onto the newer paper at
`fbc7078c22426e2ccc42938cce8e4a33bf903f4f`. The generated arithmetic/string/library rules,
bounded universal notation and unified lengths are compared below. The general semantic statements
and command proofs received an independent Astra source review; validation
is recorded in the implementation commits. An unchanged reference still
describes the original certificate layer, not the whole of B.

The paper is the source of truth. Where B has no statement of an item, the
row names the statement of the shared model (`Semantics/`) or of A
(`Programs/`, `Source/`) the paper's status tag cites, checked against the
paper where the row says so. **Assumed** marks a host contract the paper
states as assumed, and identifies whether B supplies an explicit contract declaration.

B is narrower than the paper. The semantic rules and the finite certificates have different coverage: a restricted checker does not narrow an imported theorem quantified over arbitrary assertions. `SemanticRules.lean` states semantic support and respect separately from the sufficient respect check. The assertion grammar and complete command/derivation rules require their own comparison. [Correspondence obligations](paper-alignment-obligations.md) states the domains and boundaries.

Notation for source references:

- All B filenames below are relative to `lean/Verification/Paper/TolerantFrames/`.
- `D` = `ParityDerivations.lean`; `E` = `ParityEvidence.lean`; `A` = `ParityAssertions.lean`.
- Outside-B filenames are relative to `lean/Verification/`.
- Paper rule/definition labels refer to the current `docs/drafts/tolerant-frames-note/note.tex`; stale original-audit line anchors are omitted.
- **Equal** compares the stated logical content, expressing an executed primitive through its semantic operation postcondition. It does not assert that acceptance applies the declaration.
- The original audit read test declarations without executing them. New
  declarations are checked by focused Lean builds and the Paper axiom check;
  compilation and axiom checks do not establish correspondence.

The original `Parity` certificate layer validates assertions with
`Atom.wellFormed` and `AssertionNode.wellFormed`. In that layer, quantified
facts concern arrays, require every quantified index present, and
admit scalar bodies only; bounds are single terms, disjunctions have invariant
guards, and separation requires two arrays.

`Assertions.lean` gives a separate general syntax interpreted in the same
shared heap/world semantics. It has recursive linear indices and bounds,
shifted and field-projected body terms, arbitrary body disjunctions, ordinary
and view elements (an in-bounds hole reads undefined), optional equalities,
finite unions of value kinds with literals, total format conversion on numeric
values, unrestricted assertion disjunction, existential source values, general
separation and region freshness. `HeapValidity` gives a world-independent logical value domain: allocated identities, source-valued ordinary slots/elements, and matching array/view spines. `RefsOk` implies heap validity at well-formed states; its fine-role converse is not assumed. `Formula.existsValue` uses its focused heap, and `TwoState.Post.forallValue` uses the current heap. Old assertions retain their entry focus. `WorldIndependence` proves equal-heap equivalences for the entire modality-free grammar, including both quantifiers. Command `ValidContext` remains world-valid; logical `HeapContext` is weaker. Scalar literals cannot contain executable
terms. Canonical `lengthPath`, `lengthElement` and body `lengthProject` choose
the shared array/view/string reader by runtime category, with empty element
suffixes allowed. The old sorted readers remain auxiliary encodings;
`PaperTermForms` checks term forms recursively through both grammars, including
free body terms, old, binders and modalities. This is separate from full
admission. `LengthBridges` preserves partial readings with explicit runtime
category evidence, not an assumed declaration-to-category theorem.
`Consequences.lean` states semantic postcondition connectives and general
value-family principles. `TwoState.Post` in `PostconditionSyntax` supplies
first-order postcondition syntax with separate program/index/value namespaces,
frozen entry interpretation and current focus. Scope and declared-region
admission are separate. `PostconditionScope`, `PostconditionAdmission` and
`PostconditionRenaming` prove logical valuation independence, odd-only value
binder lifting, and total semantic renaming through all constructors and
effects. `PostconditionProgramRenaming` proves scoped AST agreement and independence of unused program-map extensions. `PostconditionRenamingScopes`, `PostconditionScopeWeakening` and `PostconditionRenamingAdmission` prove program-only scope and declared admission transport through both phases and binders. General path/term substitution and admission for other logical-map instantiations remain separate obligations. `PostconditionExamples` structurally encodes Q_<,
Q_≠i, Push and converted View-Write, with interpretation equivalences; these
are not primitive execution proofs. `IndexInstantiation` gives a defined
frozen-value construction and a conditional obstruction to textual replacement
across old. The paper’s instantiation sentence needs clarification; this
construction is not added as a claimed Definition 23 rule.
`Renaming` covers every assertion constructor and lifts beneath binders;
`RenamingAdmission` proves declared-type pullback admission.
`PathReplacement` and `ModalReplacement` prove grammar-admissible selected
path replacement, including prefixes, binders and changed modal effects/bodies.
This is not arbitrary path-for-variable substitution into variable-only
positions. General two-state substitution remains a separate obligation. A family of present element readings is not substituted for a
body which may read no element.

`AllSupport` proves the paper’s all support for the complete modality-free
language. `Existentials` and `Derivations` give current-state witness introduction
and elimination, with only the exit valuation extended, and old monotonicity.
`Arithmetic` proves general current-state integer consequence, with recursively
mentioned index terms, literal-fixed integer models and exact goal definedness.
The corrected literal-equality directions and the separate failed-path freshness obstruction are stated below.

`Commands`, `CommandRules`, `Scopes` and `Loops` add actual command
execution and general partial-correctness rules. Runs are raw executions in
the shared calculus; triples choose admissible exit worlds and preserve valid
environments and returned/thrown values. `Admission` distinguishes the paper’s
region forms and fresh lexical bindings from the raw representation. Its
connection to complete typing and derivation admission is a separate obligation.
`Derivations` is explicitly a sound subcalculus of Definition 23, and `Transfer`
assembles Check for that subcalculus with arbitrary regional effects. No
completeness claim about certificates or search is made.

`BudgetTruncation` proves exact positive same-heap world restriction for the
complete syntactic assertion grammar, including boxes. This is not arbitrary-
world independence or a theorem for arbitrary semantic predicates. Frozen-entry
transport has an explicit exit-budget bound. Restricting a chosen admissible
exit preserves complete first-order postconditions, including implication and
transition atoms, plus source/reference validity; it is a foundation for graph
administrative steps, not Fun itself. Scope admission retains inputs and keeps
caught names local; its general preservation/avoidance theorems discharge Frame
noncapture for scoped syntax. Raw completion uses shared machine values, while
Triple's source/world guarantees are unchanged.

`OperationCode` supplies one fixed symbolic term per operation. Shared closing
substitution yields the actual closed operation with host.close ρ after at
most six pure own-read steps; terminal compiled runs invert to its exact primitive count plus those
administrative steps. `OwnFieldCode` covers arbitrary machine values, field maps,
callable objects and prototypes, with raw nonobject stuckness retained. This
uses a new internal-only pure shared hasOwnKey tag. The request decoder freezes
its original eighteen-constructor vocabulary before all enclosing codecs; old
encodings and decoding range are proved, and nested forged-tag controls pass.
Stable captured host slots remain an obligation of the command compiler.
Only those shared test/normalization/codec foundations are extended. Full
command-to-graph execution correspondence and Fun are still open.

`PureOperations` derives exact pure binding triples/effects from actual shared
reductions by deterministic terminal cancellation and chosen-world restriction.
Its computed predicate reads the entry state. `BitwiseArithmetic` proves full
Mask and Or bounds; `BitwiseRules` connects arithV to actual command triples,
empty effects and current-state syntax. Name agreement comes from existing
fresh binding scope, and integer readings from SafeInt decoding. No arbitrary
semantic predicate or stored signed-zero equality is transported. The full Shr, Shl, Mask and Or semantic statements are supplied by shared
ArithmeticRules in the rebased source; the task-specific command instances
remain auxiliary.

The next operational function foundations are proved without summary premises.
`CompilerScope` derives a finite frame bound for every command, including bind
and catch IDs, and proves exact scoped code/environment agreement. `CompilerLayout`
proves actual envMap equations, map lengths, host/payload stability, machine-value
preservation including defaults, and restored context validity from finite
source/world-valid source slots. `GraphInversion` maps every shared graph step to
an actual graph transition with the same count; `GraphSegments` separates completed
node expression steps from its heap-preserving continuation/handler transition.
`CommandMachine` makes finite control traces explicit and proves terminating
traces give existing structured Executes with exactly their primitive weight.
`CommandCompiler` now generates fixed finite graphs, and `CompilerOrigins`
generates every node/routing obligation from syntax and a derived frame bound.
`CompilerCorrectness.compiled_value`/`compiled_raise` invert actual shared Steps
to structured Executes with identical heap/exit and primitive count p≤N; terminal
named environments are retained. Host machine values are an explicit representation
premise, not a native safety assumption. `CallableEntryLayout`, `CallableEntryCode`
and `CallableEntryCorrectness` map the actual fixed-arity ABI's padded parameters,
captures and self through an appended adapter, with exact prefix count three.
Completed invocations recover body execution with p≤q<N at N=3+q, preserving
heap and exit. CallableReferences derives self reference validity from actual
object/capture roles without assuming its specification. CallableEntrySpecification
transports the body's proved Triple/Effects to actual value/throw completions,
with full syntactic postconditions, original old/mark, exact shared residual
budget, false escaping-break obligation and input-scope restoration. Separate phase-environment agreement and bounded state/framing rules are
proved. RecursiveFunctions discharges smaller-count hypotheses from a constructed
relative body proof; RecursiveCallRules supplies a real identity-aligned primitive
oracle, both effects, full caller-context validity and semantic mark independence.
Common rigid bounded effect composition is sufficient, not general Seq-Eff.
Function allocation/typing, arbitrary-actual alignment of that oracle, deriving
encoding premises, freshness rebasing, rest and full Fun remain separate.

The latest paper uses one dynamic length for arrays, typed arrays and strings,
including empty-suffix lengths of array/view elements. B's canonical
constructors express that operator in both grammars. The older sorted readings
remain auxiliary forms, distinguished recursively by PaperTerms. Inst and
Prefix's unified-length gap is closed; their rows stay narrower for the
unresolved element-free receiver interpretation. Empty additionally needs the
declared-collection-to-runtime-receiver bridge. General semantic laws over
arbitrary assertions remain unchanged. Sorted array/view/string rules retain
their mathematical statements; qualified Option-result bridges require actual
read/category evidence and do not infer it from declarations.
Existing Every already separates its receiver from its bound; elaboration of
the new bounded universal must retain the single body-element path independently
of paths mentioned in its bound/free terms. The no-element receiver case awaits
an owner decision.

There is also a static paper obstruction: for u:number[]|string, the
prescribed mixed-length union support includes u.spine, while the declared-region
grammar explicitly rejects that region because u is not a collection path.
The owner was asked to decide the correction; neither support admission nor the
paper is silently weakened. These are documented in the correspondence obligations.

**§1 — The problem**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Example 1, aliasing loop | `AliasExample.program`, `.body`, `.program_scoped`, `.Head`, `AliasExample.lean`; older `loop_safe`, `ModelLoop.lean:601` | **narrower** | The new command has the output-length test, RangeError construction and throw, private loop cell and exact head bounds. Scopes and displayed integer obligations are proved. A closed execution/graph proof connecting the primitives and all edge obligations is not supplied; the updated scope proof retains every outer binding at joins. The old six-node graph remains a different example. |
| Example 2, rewriting call | `RawDerivation.sep`, `D:639`, checked at `D:881`; `Derivation.rigidSubst`, `D:447` | **narrower** | These establish the linear length-frame ingredient for arrays and certified rigid substitution. There is no declaration of the complete `readRuns` loop and its call. |

**§2 — What exists: variables, locations, spines**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Definition 3, Commands | `Operation`, `Primitive`, `Command`, `PrimitiveRun`, `Executes`, `Commands.lean`; `Command.WellScoped`, `Admission.lean` | **narrower** | The grammar and execution constructors include sequence, choice, loops, handlers, break, return, throw, named operations and native calls. Raw completion includes shared internal machine values; source/world guarantees remain in Triple contexts/exits and typing, so malformed natives cannot disappear from the raw runs. Admission separates fresh binding steps from mutations, retains all outer names at joins and excludes caught names from outputs. Generated raw command graphs now have actual completed-run inversion for all commands. Fixed-arity callable entry now has exact actual invocation/body inversion via the three CallableEntry modules. Full admitted typing, signature/old-anchor transport and recursive Fun remain separate. Operation.nativeCall resolves a supplied callee explicitly with receiver/positional arguments; symbolic code, scope, renaming and finite compilation agree. Ordinary method lookup remains separate, since literal arrays lack push and scalar strings cannot read method fields. NativeContract/native_command_rule derives both exits and effects from actual shared safety at valid callee references; can_step rules out stuck invocation for an actual precondition instance. Concrete native contract/formula instances and full typing remain separate. |

**§3 — Model**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Definition 4, World | Shared `WorldT`, `WorldAdm`, `WExt`, `Semantics/Worlds.lean`; imported by `SemanticRules.lean` | **equal** | A finite initial segment of roles and step-indexed contracts, with contract admissibility supplied by WorldAdm. WExt appends a tail and preserves all old role/contract entries; truncation changes only the budget at which contracts are read. |
| Definition 5, Well-formed state | Shared `IndexedHeap`, `Semantics/TwoStateFormulas.lean`; `ValidContext`, `SemanticRules.lean` | **narrower** | IndexedHeap supplies heap/world/budget invariants; ValidContext adds valid source-valued environment roots and a mark within the heap. A full environment-typing judgment for a declared variable type context, and the complete embedding of the paper’s value/object domain, are not given by ValidContext alone. |
| Definition 6, Admissible transition | Shared `Admissible`, `WorldReach`, `Semantics/TwoStateFormulas.lean`; imported by `SemanticRules.lean` | **equal** | The indexed-state transition lowers the budget and extends the truncated world. The action keeps its name valuation fixed; fresh command bindings and graph renamings are accounted for separately in command scope and transfer. |
| Theorem 7, Preservation | Shared `safe_run`, `Semantics/IndexedStates.lean`; A `HasTyUsing.sound`, `Programs/ProgramTyping.lean`; `ControlFlow.state_safe`, `Programs/ControlFlow.lean` | **narrower** | The imported run theorem gives admissible endpoints and residual budget from shared calculus safety; A supplies typing-to-safety results. A preservation theorem for the complete admitted B command language and its typing assumptions is not established by the endpoint partial-correctness rules. |

**§4 — The assertion language**

The three proposition-summary rows in this report summarize their following constituent rows and are excluded from the final count.

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Remark 8, Reading | `box_eq_havoc_wlp`, `box_weakest_stable_on`, `SemanticRules.lean` | **equal** | The box is the wlp of one arbitrary action. For every rigid effect it strengthens F, is stable, and is implied by any stable strengthening G; G ranges over arbitrary assertions. |
| Proposition 9, Laws — 940 — summary | Semantic `box_elim`, `box_and`, `box_anti` in the shared model; `box_mono_on`, `box_or_on`, `box_idem_on` in `SemanticRules.lean` | **equal** | The constituent semantic laws are general; the serialized arena/checker supplies only a restricted certificate route. |
| 9(a), elimination | Shared `box_elim`, `Semantics/IndexedStates.lean`; interpreted by `Formula.meaning`, `Assertions.lean` | **equal** | Reflexive elimination quantifies over arbitrary assertions, including the general interpreter; its scope is not limited by the old arena/checker. |
| 9(b), conjunction equivalence | Shared `box_and`, `Semantics/IndexedStates.lean`; general `Derivation.boxAnd`, `.boxLeft`, `.boxRight`, `Derivations.lean` | **equal** | Both directions hold for arbitrary assertion interpretations. The general derivation constructors state the same conjunction laws. |
| 9(b), monotonicity | `box_mono_on`, `SemanticRules.lean`; shared `box_mono`, `Semantics/IndexedStates.lean` | **equal** | The premise is arbitrary semantic entailment on valid contexts. No finite context-free certificate is required by the semantic law. |
| 9(c), antitonicity in effects | Shared `box_anti`, `Semantics/IndexedStates.lean`; general `Derivation.boxAnti`, `Derivations.lean` | **equal** | Inclusion of actions gives the stated antitonicity for arbitrary assertions. InclusionEvidence is only one certificate route to that premise. |
| 9(d), invariant disjunction | `box_or_on`, `SemanticRules.lean` | **equal** | The guard is an arbitrary semantically invariant assertion on valid contexts. There is no syntactic invariant-guard restriction on disjunction or this law. |
| 9(e), idempotence | `box_idem_on`, `RigidOn`, `SemanticRules.lean` | **equal** | The premise is transitivity of the action on valid contexts, not successful rigidity evidence. |
| Proposition 10, Guards and quantified facts — 956 — summary | `guard`, `Assertions.lean`; `inst_rule`, `prefix_rule`, `empty_rule`, `QuantifiedRules.lean` | **narrower** | Guard is general. Inst and Prefix interpret canonical dynamic lengths and empty element suffixes. The element-free receiver interpretation remains unresolved. Empty additionally needs the declared-collection-to-runtime-receiver bridge because unified length includes strings. |
| (Guard) | `guard`, `equal_contradiction`, `contents_contradiction`, `Assertions.lean` | **equal** | The reading is any partial path reading, including optional final fields; disjunction requires no invariant guard. Unequal values contradict equality of the same reading. |
| (Inst) | `inst_rule`, `Body.holds_instantiate`, `QuantifiedRules.lean`; `Derivation.everyInst`, `Derivations.lean` | **narrower** | The actual instantiated goal preserves represented linear indices, offsets, projected fields and disjunctive/conjunctive bodies without density/presence premises. Canonical dynamic length and empty array/view element suffixes participate in actual instantiation; PaperTerms preservation is proved. This closes the unified-length grammar gap. The row stays narrower while the paper’s implicit receiver for an element-free body is unresolved; the encoded receiver remains independent of the bound. |
| (Prefix) | `every_prefix`, `Assertions.lean` | **narrower** | Arbitrary represented defined bounds t and t′ satisfy the general prefix argument without density or scalar-body restrictions. Canonical lengths participate in bounds and bodies, closing that grammar gap. The row remains narrower solely for the unresolved element-free receiver interpretation. |
| (Empty) | `empty_rule`, `QuantifiedRules.lean`; `Derivation.everyEmpty`, `Derivations.lean` | **narrower** | Defined kind-specific array/view length and a defined nonpositive bound give the represented quantified fact with no density premise. Current unified length also permits strings, so the paper’s explicit declared collection-path restriction must be connected to actual receiver semantics; HeapContext alone supplies no such declared classification. Canonical body/length forms are represented; that declaration-to-receiver bridge and the element-free interpretation remain separate. |

**§5 — Entering the modality**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Definition 11, Support | `Supports`, `SemanticRules.lean`; shared `SupportDomain.Supports`, `Semantics/Support.lean` | **equal** | The shared support-domain definition is instantiated at arbitrary assertions, with heap-valid logical roots and mark supplied by `HeapContext`. World-valid program contexts imply this via `ValidContext.heap`; fine-role program validity is not redefined. It includes the condition on every admissible transition, rather than just a particular run. |
| Definition 12, Respect | `Respects`, `respects_of_check`, `SemanticRules.lean` | **equal** | Semantic respect quantifies over every effect action from K. The existing Boolean pairwise test is proved sufficient, and is not used as the definition. |
| Theorem 13, Tolerant frame | `tolerant_frame`, `SemanticRules.lean` | **equal** | The premises are general semantic support under C, semantic respect under K, and C on every action. The conclusion is K ∧ F entailing the box on heap-valid logical contexts; strong program contexts supply these via `ValidContext.heap`. No finite evidence premise is substituted. |
| Definition 14, Supports of the atoms | `Formula.all_support`, `AllSupport.lean`; `reads_sound`, `equal_support`, `contents_support`, `optionalEqual_support`, `separated_support`, `PathSupports.lean`; older `SupportEvidence`, `E:811` | **narrower** | The exact all={val:keep,st:keep} supports every represented modality-free assertion, including canonical dynamic lengths/empty suffixes, projected elements, optional fields, sparse bodies, freshness and existentials. Conjunction/disjunction supports are general. Raw path reads, conditional omission at arbitrary prefixes, equality, optional equality, contents and full separation supports are proved by reuse of shared traversal. `PathTermSupports` proves numeric/string/view and keep/grow array-length path supports. `ElementSupports` proves numeric unprojected element terms with arbitrary exactly supported index expressions; `AtomSupports` proves element atoms and density with exact bound support. `EverySupports` proves the table’s restricted bodies over the unshifted numeric element and index-independent exactly supported free terms, explicitly conditioned on an ordinary array receiver (the declared-type bridge remains separate). `PolaritySupports` proves inequality support from independent semantic growth tolerance plus finite sufficient certificates, retaining nested indices and zero coefficients; maximal/canonical annotation selection is not claimed. `BelowMark` derives descriptor-region bounds from invocation-entry heap references, with world-valid origin corollaries. Complete table/admission assembly, canonical tolerance selection and remaining atom axioms are separate obligations. General path freshness at these reads is false on a failed nullable prefix: `FreshnessCounterexample.failed_path_freshness_not_supported` is a concrete valid-context B countermodel with admitted regions, not a full EnvTyping or command-execution proof. The paper freshness decision is pending. |
| Proposition 15, Axioms of the atoms — 1138 — summary | `RawDerivation.grow`, `.dense`, `.sep`, `.everyFrame`, `.init`, `.view`; `Derivation.rigidSubst` | **narrower** | The individual restrictions follow. |
| (Grow) | `grow`, `Bridges/Grow.lean:27`; `RawDerivation.grow`, `D:646`; `SupportEvidence.lengths`, `E:813` | **equal** | For the displayed lower bound over a variable or constant, B establishes preservation under arbitrary value changes and spine growth, without separation. Literal lower bounds can use the linear-support rule directly. |
| (Dense) | General `Atom.dense`, `Assertions.lean`; old `RawDerivation.dense`, `D:647` | **narrower** | The general syntax admits every defined linear bound. The old finite certificate only accepts a variable bound directly. The displayed modal density schema at variables or literals is not connected to the new interpreter by a general support proof. |
| (Sep) | `RawDerivation.sep`, `D:639`, checked at `D:881` | **narrower** | The fact must be linear over variables and the one array length, and both separated paths must read arrays. The paper allows any qualifying atom and includes the null/undefined case for the other value. |
| (Every) | `RawDerivation.everyFrame`, `D:640`; general `Every`, `Assertions.lean` | **narrower** | The general assertion no longer inserts density or unconditional element presence, and its complete body grammar is interpreted. The general Every framing schema and its support proof are not bridged to that interpretation; the old certificate has its original restrictions. |
| (Init) | `init_box`, `ModelRules.lean:82`; `init_path`, `:96`; `RawDerivation.init`, `D:641` | **narrower** | The atom is restricted to a linear fact over current terms. The paper quantifies over every atom whose heap reading is the displayed path length. |
| (Rigid) | `FormulaReplacement.rigid`, `RigidFormula.holds_iff`, `ModalReplacement.lean`; older `Derivation.rigidSubst`, `D:447` | **narrower** | General current-state selected-path replacement under modalities is proved, including binder shifting and regional effects. Unrelated paths and unchanged boxes need no rigidity. The displayed atom axiom still needs its fresh-witness derivation bridge and nonoccurrence conditions; current-state replacement alone is not that complete axiom. |
| (View) | `view_box`, `ModelRules.lean:45`; `RawDerivation.view`, `D:642`, checked at `D:930` | **narrower** | `view_box` covers linear facts over variables and view lengths; the derivation route covers assertions recognized by `invNode`. Neither states the schema for every qualifying paper atom. |

**§6 — Programs**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Break | `break_rule`, `ExitPost`, `Triple`, `Commands.lean` | **equal** | The normal postcondition is false; the unchanged state meets the enclosing loop’s obligation. Break is a distinct control exit, consumed by the enclosing loop. |
| Return | `FunctionReturn`, `return_function_rule`, `Commands.lean` | **equal** | The obligation substitutes the returned atom for the result while explicitly freezing old at the enclosing function’s entry. It is threaded unchanged through local command entries; the normal postcondition is false. |
| Throw | `throw_rule`, `Commands.lean` | **equal** | Throw has false normal postcondition and retains arbitrary R at the handler state. The thrown value’s source/reference validity is the type-system part of the triple, distinct from R. |
| Try | `try_rule`, `CommandRules.lean` | **equal** | The handler runs after the actual throw and binding of its fresh caught name. R, Q and Qe are one-state assertions; R does not mention the caught name. Caught-value validity is derived from the body’s typed exit guarantee. |
| Entry | `entry_rule`, `CommandRules.lean` | **equal** | Both exit postconditions are strengthened by arbitrary old(B) and the corresponding regional action, with B supplied at entry. Scope and marks are explicit in the triple. |
| Frame | `frame_rule`, `CommandRules.lean`; `scope_stable_of_avoids`, `Scopes.lean` | **equal** | Both normal and exceptional boxes are eliminated using their own effects. Scope transport is precisely the paper’s fresh-binding condition; it follows from dependence on names the command does not bind. No finite assertion/region certificate restriction is imposed. |
| Frame⁺ | `frame_plus_rule`, `CommandRules.lean`; `RigidOn`, `SemanticRules.lean` | **equal** | Semantic rigidity on valid contexts retains the box at the normal exit. Scope transport includes the effect under the modality and is proved from noncapture. |
| Loop | `loop_invariant`, `loop_rule`, `Loops.lean` | **equal** | Induction on actual loop execution handles normal iterations, break, return and throw. The body normal post gives I; its break obligation is I ∧ box R, as stated in the paper’s explanation. Semantic effect and rigidity plus noncapture retain the modality; no supplied prefix summary replaces the rule. |
| Call | `admitted_call_rule`, `CallAdmission.lean`; `finite_call_syntax_rule`, `CallRules.lean`; `PrimitiveRun.pullback`, `PrimitiveRenaming.lean`; `FormulaScopes.lean`; first-order program-renaming scope/admission modules | **narrower** | The displayed finite variable-actual Call transport is connected to actual shared execution, both exits and both regional effects. It fixes the callee, permits every input alias pattern, derives result-map freshness from finite names, and requires whole-caller freshness and proves the actual command WellScoped. Lexical precondition scope, normal/exceptional phase scopes, command scope and declared admission are assembled; every specification/effect component is independent of unused map images. The formal call Triple already holds uniformly at command marks, and transport retains the same mark/world/budget; it does not rebase a body-only freshness specification. Any finite formal member can be supplied, but actual rest-body/spread preparation and freshness-mark rebasing are not supplied. Fun/body realization remains a separate rule. Declared classifications are explicit pullbacks, not inferred EnvTyping facts. |
| Alloc, empty array | `alloc_step`, `ModelRules.lean:177`; `alloc_post`, `:184` | **equal** | The allocated array has a fresh spine, length zero, and is apart from every pre-existing array. Freshness at the allocation heap length implies freshness at the enclosing invocation’s earlier mark. |
| Seq-Eff | `seq_eff`, `ModelRules.lean:310`; `CommandSummary.seq_sound`, `CommandComposition.lean:163` | **narrower** | B requires the computed `rebaseAll` with `RebaseOk` and a successful `Footprint.le` check. The paper permits any rebasing satisfying its coverage relation and semantic effect inclusion. The general `Post.compose_rebases` is outside B, `Semantics/ExitComposition.lean:110`. |
| Fresh-Eff | `fresh_eff`, `ModelRules.lean:320` | **equal** | For every location below the mark, the fresh spine’s entry is removable from the effect. The theorem does not remove effects on cells that spine lists. |
| If | `if_rule`, `if_effects`, `CommandRules.lean` | **equal** | The two branches are checked under the true/false truthiness of the named test atom, with arbitrary shared postconditions and regional effects. Test facts from the operation that produced that atom remain the separate Test rule obligation. |
| Seq | `seq_rule`, `CommandRules.lean` | **equal** | The intermediate and exit assertions are one-state assertions as displayed. The first execution supplies the intermediate world and valid environment; the second starts there, with the same invocation mark. |
| Alloc, array literal | **none in B**. Cited outside B: `literalArrayAtoms_holds`, `Programs/IndexWrites.lean:175` | **none in B** | B’s empty-array theorem does not establish arbitrary literal contents and density. The paper itself marks those parts conjectural. |
| Alloc, object literal | **none in B** | **none in B** | `alloc_state` (`KindsModelRules.lean:508`) establishes allocation/state properties, not the displayed freshness-and-field-equalities postcondition. |
| Definition 16, Independence of the world | `Independent`, `Commands.lean`; `Formula.independent`, `TwoState.Post.independent`, `WorldIndependence.lean`; shared `IndependentFrom`, `Semantics/ExitWorlds.lean` | **equal** | The entry and both exit contexts are valid; the entry is fixed and exit environments agree. Truth agrees at admissible exits with equal heap and budget, regardless of their worlds. No property at invalid environments or marks is required. Every modality-free assertion, including heap-domain existentials, and every HeapOnly two-state postcondition has this property; transition atoms are excluded because they read admissibility. |
| Conj | `conj_rule`, `Commands.lean`; `SafePostExcV.conj_independent`, `SemanticRules.lean` | **equal** | The first proof’s admissible world and shared break/return obligations are retained. Only the second normal and exceptional postconditions need independence. In the shared safety encoding, retaining the first result family discharges compatibility by projection. |
| Definition 17, Rebasing | **none in B**. Shared model: `Rebases`, `Semantics/ExitComposition.lean:77` | **none in B** | `Rebases` states the coverage relation with the absorption by $`\Phi`$ at `any` explicit, and holds no evidence $`\mathit{ev}`$: the paths reading each named value in both heaps are premises of `rebase_sound` for the computed rebasing (checked). |
| Example 18, Freshness bounds effects, not facts | **none in B** | **none in B** | `fresh_eff` proves the effect ingredient. `apart_not_kept_fresh` (`ModelRules.lean:251`) refutes preservation of apartness, not this shrink-and-read example or its length fact. |
| Proposition 19, Reliance | `ActionChain.action_on`, `reliance_on`, `SemanticRules.lean` | **equal** | An arbitrary finite chain of actions bounded by a rigid effect is one action. The initial box gives F at any selected prefix endpoint. Each native step and callback must supply its action bound; an endpoint summary alone does not supply these prefixes. |
| Field-Read | `Operation.code`, `Commands.lean`; general `Atom.equal`, `.optionalEqual`, `Assertions.lean`; shared `ReadGave`, `Semantics/HeapFacts.lean` | **none in B** | Own-field command lookup explicitly bypasses prototype fallback when the own field is absent, matching optional equality. A full general primitive triple/effect proof from the required-field or optional-field typing assumptions is not supplied; code and assertion definitions alone are not that rule. |
| Field-Write | **none in B**. Cited outside B: `fieldWriteFrame`, `Programs/ExpressionEffects.lean:112`; `FieldWritten`, `:155`; `fieldWriteStep_sound`, `:229` | **none in B** | B proves preservation consequences of some writes, not the general exact field-write rule. |
| Elem-Read | `elementValue`, `Atom.element`, `Assertions.lean`; `Operation.elementRead`, `Commands.lean` | **none in B** | The general ordinary/view element assertion, including holes, and the executed ordinary read are defined. Their exact primitive triple/effect and typing/definedness bridge is not proved. |
| Arr-Length | `Operation.arrayLength`, `Commands.lean`; shared `lengthOf`, `Semantics/IndexFacts.lean` | **none in B** | The operation is interpreted through the shared calculus. The general displayed primitive triple with exact equality and empty effect is not proved. |
| Test | `Operation.binary`, `.not`, `.and`, `.or`, `Commands.lean`; `if_rule`, `CommandRules.lean` | **none in B** | Truthiness and Boolean operation execution are represented. The complete comparison/nullish/negation/conjunction/disjunction fact rules tying bindings to branch knowledge are not proved. |
| Fun | `CommandSummary.signature_holds`, `CommandBodies.lean:86`; `.signature_holds_below`, `:106`; actual command graph inversion in `CompilerCorrectness.compiled_value`/`compiled_raise`, with generated `CompilerOrigins`/`CompilerRoutes` and operational foundations | **narrower** | The old signature transport still assumes a sound body summary. The generated finite compiler and all node/routing evidence are proved internally. Every completed shared graph run yields the existing command execution, same heap and exit, restored final environment, and primitive p≤shared N. Explicit host-value representability is required; forward simulation or progress is not inferred. The three CallableEntry modules construct fixed-arity receiver/parameter/capture/self setup and the actual three-step entry adapter; completed invocations yield body execution with strict primitive p<N and exact heap/exit. CallableReferences derives self refs from object/capture roles without assuming its specification. CallableEntrySpecification transports the displayed proved body Triple/Effects to actual normal/exceptional invocations: current-only result substitution, undefined fallthrough, frozen return/old anchor, false escaping break, full syntactic exit-budget equivalence and scoped body-local removal are proved. Entry source/world validity follows from actual roles, arguments and selected source captures. BoundedCommands/BoundedFrameRules and full separate-phase environment agreement support RecursiveFunctions' actual count-induction schema. The relative body proof uses only smaller-count concrete invocation hypotheses, with FunctionEntryPre reflexively freezing entry. RecursiveCallRules connects those hypotheses to actual identity-aligned primitive call executions, both posts/effects and whole caller-context validity, under explicit input/capture/layout premises and semantic mark independence. BoundedEffects handles a common rigid footprint on both exits, not general rebased exceptional composition. Constructing the relative body proof, deriving encoding premises from typing, arbitrary actual alignment, allocation/type membership, freshness rebasing and rest prologue remain separate. Rest old-anchor semantics need an owner decision: a closed heap-valid existential can observe prologue allocation despite omitting the rest variable; the source-level obstruction is qualified in paper-call-function-bridge, not claimed as an unrestricted ordinary-body counterexample. Cited outside B: `codeObligations_sound`, `Programs/CodeConditions.lean:218`. |
| Write-In | `Derivation.writeIn`, `D:583`; `lengthsKept_of_run`, `Bridges/ParityArithmeticBridges.lean:189` | **narrower** | The conclusion concerns an array held in corresponding entry/exit slots. The paper states preservation of the length read through every path; B does not package the preservation of those path reads into this rule. |
| Write-End | `Derivation.writeEnd`, `D:589`; `boundedWrite_of_run`, `Bridges/ParityArithmeticBridges.lean:209` | **equal** | Given the bounded-write operation postcondition and the displayed end-index premises, B concludes exactly the length increase by one. The current paper does not put element equality or density extension in this rule. |
| Push | `PushPost`, `Consequences.lean`; `TwoState.pushPost`, `.pushPost_holds`, `PostconditionExamples.lean`; older `Derivation.pushPost`, `D:595` | **narrower** | The complete first-order syntax, including Q_< with index/value binders, is equivalent to the semantic length/appended-element/kept-prefix relation under receiver identity and entry/current admissibility. A command-level rule deriving it from the explicit native contract is not proved. |
| Write-Kept | `write_kept`, `Consequences.lean`; shared/A `keptCells_holds`, `Programs/HeapExpressionRules.lean:1404` | **narrower** | The general value-family preservation principle is proved. The command-level bridge identifying the read field as unchanged or written by the actual field operation is not supplied. |
| Push-Every | `push_every`, `Consequences.lean`; older A `every_appended`, `Programs/PromiseCalls.lean:2375` | **narrower** | The theorem extends arbitrary predicates of actual element readings using PushPost. It still needs the bridge for the paper’s body, its preserved free terms and whole-array premise, and the actual push command contract. |
| View-Every | `view_every`, `every_written`, `ViewWritePost`, `Consequences.lean` | **narrower** | The principle preserves and conditionally extends predicates using the converted value, without requiring conversion to be identity. EveryValue requires a reading at each index; the paper’s Every does not. The full body bridge must handle that distinction and preserved free terms rather than infer presence. |
| Add | `Derivation.arith` at `ArithmeticRules.add`, `ParityDerivations.lean`; `rules_sound` | **equal** | The paper's row is generated from the rule: safe operands and a safe mathematical sum give the exact sum. |
| Sub | `Derivation.arith` at `ArithmeticRules.sub`, `ParityDerivations.lean`; `rules_sound` | **equal** | The paper's row is generated from the rule: safe operands and a safe mathematical difference give the exact difference. |
| Scale | `Derivation.arith` at `ArithmeticRules.scale`, `ParityDerivations.lean`; `rules_sound` | **equal** | The paper's row is generated from the rule: a safe-integer constant factor and a safe mathematical product; `Derivation.commute` applies it to `c * a`. |
| Shr | `Derivation.arith` at `ArithmeticRules.shr`, `ParityDerivations.lean`; `ruleConclusion`; `rules_sound`, `Semantics/ArithmeticRules.lean` | **equal** | The paper's row is generated from the rule B applies: an operand in the signed 32-bit range, a safe-integer constant count read modulo 32 and both quotient bounds. A constant may be a literal or a value proved constant. |
| Mask | `Derivation.arith` at `ArithmeticRules.maskRange` and `maskBound`, `ParityDerivations.lean`; `rules_sound` | **equal** | The paper's two triples are generated from the two rules: the range for any number and a safe-integer mask in $`[0, 2^{31})`$, held in a variable or a literal, and the bound $`y\le b`$ by the same non-negative safe-integer mask $`b`$ of any number $`x`$, without an upper bound on $`b`$. `Derivation.commute`, `ParityDerivations.lean`, applies them to `m & x`. The separate `BitwiseRules` command theorems remain restricted corollaries; their nonnegative-input bound is not this second paper conclusion. |
| Shl | `Derivation.arith` at `ArithmeticRules.shl`, `ParityDerivations.lean`; `rules_sound` | **equal** | The paper's row is generated from the rule: a safe-integer constant count read modulo 32, and the exact product where it lies in the signed 32-bit range. |
| Or | `Derivation.arith` at `ArithmeticRules.bitOr`, `ParityDerivations.lean`; `rules_sound` | **equal** | The paper's row is generated from the rule: both operands in $`[0, 2^{31})`$ bound the result below by each and above by their sum. |
| String-length successor | `Derivation.lengthSuccessor`, `D:547`; `lengthSuccessor_sound`, `:1428` | **equal** | The result is the exact safe sum or the number $`2^{53}`$, under the stated string-length equality. |
| Str-Length | `Derivation.stringLengthRead`, `ParityDerivations.lean` | **equal** | The conclusion is the string’s UTF-16 length, represented as the result’s safe integer; B states also that the result is a safe integer, which the row's $`y=\|s\|`$ implies by the meaning of a defined term. The row is the entry `ArithmeticRules.strLength` (proved: `strLength_sound`); B's facts are its conclusion substituted, after `safeFact` (`Bridges.lengthReadFacts_entry`). |
| Str-Read | `Derivation.stringRead`, `ParityDerivations.lean`; `stringIndexFacts` | **equal** | B's premises are $`0\le i`$, $`i+1\le\|s\|`$ and $`i\le 2^{32}-2`$, the row's $`0\le i<\|s\|\wedge i<N`$ for $`N=2^{32}-1`$; the conclusion is result length one. The row is the entry `ArithmeticRules.strRead` (proved: `strRead_sound`), whose premises and conclusion substituted are B's (`Bridges.stringRead_entry`). The pass (A) has no producer of this fact. |
| Concat | `ArithmeticRules.concat`, `concat_sound`, `rules_sound`, `Semantics/ArithmeticRules.lean`; `concatFacts_entry`, `Bridges/ParityArithmeticBridges.lean` | **equal** | The shared rule has no logical precondition beyond both operands being strings; on normal execution its UTF-16 result length is the sum. The bridge identifies the instantiated conclusion. The older finite `Derivation.stringConcat` additionally derives nonnegative lengths; this certificate restriction does not narrow the general shared rule. Unified-length syntax transport is separate. |
| Library: `charCodeAt` range | `ArithmeticRules.charCodeAt`, shared `Semantics/ArithmeticRules.lean` (contract specification datum) | **assumed** | For a string receiver and safe-integer index with 0≤i<len(s), the result is safe and between 0 and 65535. The named host declaration is `String.prototype.charCodeAt`. NativeContract/native_command_rule supplies generic resolved-call safety and both-exit/effect transport. This row still needs its concrete callee, operation/mode-specific contract and paper-formula instance; the metadata proves no native implementation. |
| Library: `codePointAt` range | `ArithmeticRules.codePointAt`, shared `Semantics/ArithmeticRules.lean` (contract specification datum) | **assumed** | At a valid safe-integer index, the safe result lies between 0 and 0x10FFFF. The named host declaration is `String.prototype.codePointAt`. NativeContract/native_command_rule supplies generic resolved-call safety and both-exit/effect transport. This row still needs its concrete callee, operation/mode-specific contract and paper-formula instance; the metadata proves no native implementation. |
| Library: `codePointAt` two-unit implication | `ArithmeticRules.codePointPair`, shared `Semantics/ArithmeticRules.lean` (contract specification datum) | **assumed** | The implication 2^16≤r ⇒ i+2≤len(s) is recorded as a RuleAtom, not proved by ArithRule.Sound. The threshold is equivalent to r>0xFFFF for integer r. The named host declaration is `String.prototype.codePointAt`. NativeContract/native_command_rule supplies generic resolved-call safety and both-exit/effect transport. This row still needs its concrete callee, operation/mode-specific contract and paper-formula instance; the metadata proves no native implementation. |
| Library: string `indexOf`/`lastIndexOf` general bounds | `ArithmeticRules.indexOf`, shared `Semantics/ArithmeticRules.lean` (contract specification datum) | **assumed** | The safe result lies between -1 and the string length; the datum records the normal empty effect. The named host declaration is `String.prototype.indexOf and String.prototype.lastIndexOf`. NativeContract/native_command_rule supplies generic resolved-call safety and both-exit/effect transport. This row still needs its concrete callee, operation/mode-specific contract and paper-formula instance; the metadata proves no native implementation. |
| Library: nonempty-needle strict bound | `ArithmeticRules.indexOfNonempty`, shared `Semantics/ArithmeticRules.lean` (contract specification datum) | **assumed** | A nonempty needle gives the strict upper bound by receiver length. The named host declaration is `String.prototype.indexOf and String.prototype.lastIndexOf`. NativeContract/native_command_rule supplies generic resolved-call safety and both-exit/effect transport. This row still needs its concrete callee, operation/mode-specific contract and paper-formula instance; the metadata proves no native implementation. |
| Library: string `slice` length | `ArithmeticRules.slice`, shared `Semantics/ArithmeticRules.lean` (contract specification datum) | **assumed** | The displayed ordered safe endpoints give result length b-a. The named host declaration is `String.prototype.slice`. NativeContract/native_command_rule supplies generic resolved-call safety and both-exit/effect transport. This row still needs its concrete callee, operation/mode-specific contract and paper-formula instance; the metadata proves no native implementation. |
| Library: array `indexOf` bounds | `ArithmeticRules.arrayIndexOf`, shared `Semantics/ArithmeticRules.lean` (contract specification datum) | **assumed** | For an array receiver and arbitrary value argument, the safe result lies between -1 inclusive and array length exclusive. The named host declaration is `Array.prototype.indexOf`. NativeContract/native_command_rule supplies generic resolved-call safety and both-exit/effect transport. This row still needs its concrete callee, operation/mode-specific contract and paper-formula instance; the metadata proves no native implementation. |
| Library: typed-array construction length | `ArithmeticRules.newView`, shared `Semantics/ArithmeticRules.lean` (contract specification datum) | **assumed** | The numeric-size construction row states the result length and fresh allocation; the exceptional 2^53 outcome is separate. The named host declaration is `viewOfLength`. NativeContract/native_command_rule supplies generic resolved-call safety and both-exit/effect transport. This row still needs its concrete callee, operation/mode-specific contract and paper-formula instance; the metadata proves no native implementation. |
| Library: construction at $`2^{53}`$ throws | **none in B** | **assumed** | No B theorem states this exceptional outcome. The generic NativeContract call bridge does not instantiate this operation/mode or its paper formulas. |
| View-Length | **none in B** | **assumed** | The row is the entry `ArithmeticRules.viewLength`, assumed of `%ByteLength%`. B’s view-length invariance results concern preservation, not the primitive read. The generic NativeContract call bridge does not instantiate this operation/mode or its paper formulas. |
| View-Read | **none in B** | **assumed** | The row is the entry `ArithmeticRules.viewRead`, assumed of `%ByteAt%`; its index is a `SafeInt`, where the paper's text takes an atom holding a `Num` and reads the linear precondition as holding of an integer alone. B has a view-element assertion and support evidence, but no primitive-read rule establishing that assertion. The generic NativeContract call bridge does not instantiate this operation/mode or its paper formulas. |
| View-Write | `TwoState.viewWritePost`, `.viewWritePost_holds`, `PostconditionExamples.lean`; cited host relation `ViewWrite`, `Semantics/ElementWrites.lean:361`; `ExactWrite`, `:184` | **assumed** | The exact converted-element and universal other-index postcondition is represented and interpreted for every format. Entry/current admissibility, receiver identity, successful index reading and successful conversion are explicit interpretation premises. The operation-specific native contract/effect instance remains a parameter, not proved by the formula equivalence or concrete overlap witness; the generic NativeContract bridge is separate. The generated `ArithmeticRules.viewWrite` entry explicitly names the assumed `%ByteSet%`, `ViewWrite` and `WriteAt` contracts; its index is a SafeInt. |
| View-Write-Any | **none in B**. Related cited contract outside B: `ViewWrite`, `Semantics/ElementWrites.lean:361` | **assumed** | The row is the entry `ArithmeticRules.viewWriteAny`, assumed of `%ByteSet%` and `ViewWrite`. No B declaration states the effect for every numeric index, including out-of-bounds indices. The generic NativeContract call bridge does not instantiate this operation/mode or its paper formulas. |
| Example 20, A write through a typed array | `ViewWrite.goal` and checked derivation, `Tests/ParityDerivationTests.lean:243,245`; `viewWrite_overlap`, `KindsModelRules.lean:161` | **narrower** | The test derives the first four preserved facts, using variables for the constant prefix/index. It omits preservation of the written view’s other element; failure of one framing certificate for the other view is not a counterexample, while `viewWrite_overlap` supplies a separate concrete overlap witness. |

**§7 — Transfer along edges**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Definition 21, Checked transfer | `Check`, `Target.syntactic`, `Transfer.lean`; `Formula.holds_rename`, `Renaming.lean` | **narrower** | The assembled sequent has the paper’s five components, and target pullback equals actual capture-avoiding syntactic renaming through every assertion constructor. Full derivation admission and general two-state substitution remain separate obligations; the proof datatype is still a sound subcalculus. |
| Theorem 22, Transfer | `edge_sound_of_triple`, `transfer`, `Transfer.lean` | **narrower** | Execution-connected transfer handles arbitrary regional effects, knowledge and target interpretations, preserving valid environments and chosen exit worlds. Its Check predicate uses the sound general subcalculus, not the full derivations of Definition 23; graph-wide safety/prefix preservation is not inferred from the endpoint triple. Syntactic budget-transport foundations are auxiliary, not a completed lowering proof. |
| Definition 23, Derivations | `Derivation`, `.sound`, `Derivations.lean`; `FormulaReplacement`, `ModalReplacement.lean`; `QuantifiedRules.lean`; `Existentials.lean`, `AllSupport.lean`, `Arithmetic.lean` | **narrower** | Current-state selected path replacement is capture-avoiding and admission-checked; changed modalities transport effects and bodies under rigidity of the two selected paths only. Inst/Prefix and selected replacement include canonical dynamic lengths and empty suffixes. Canonical current-state defined-length bounds are integrated by Derivation.canonicalLengthRange. Empty retains the declared-collection bridge obligation; the element-free body receiver remains unresolved. Consequence and modal premises range over heap-valid logical contexts; command transfer supplies them from world-valid program contexts. Heap-domain existential introduction/elimination, evaluated current-value universal instantiation with definedness and a fixed witness through old, and old monotonicity, exact all framing by the sufficient respect check, current-state integer consequence with recursive term definedness, and defined-length ranges are integrated. First-order mixed-phase syntax, static admission, valuation independence and semantic renaming are supplied by the TwoState modules; full path/term substitution and admission beyond the proved program-only transport, mixed-state arithmetic, the structural support table, remaining atom schemas and complete derivation admission are not all represented. The index-at-term sentence has an explicitly unresolved frozen-value versus textual-substitution interpretation; the auxiliary frozen construction is not inserted as a rule. The owner-corrected numeric literal clause is proved and integrated by `LiteralEquality`: value→integer always, integer→value for n≠0, and the +0/−0 disjunction at zero. The old negative-zero countermodel refutes only the former unrestricted reverse rule. Failed-prefix freshness support remains a separate mathematical obstruction. |
| Example 24, Example 1 in full | `AliasExample.program`, `.program_scoped`, `.Head`, `.read_bound`, `.write_bound`, `.increment_range`, `.back_edge`, `.exit`, `AliasExample.lean` | **narrower** | The actual command contains both tests, RangeError construction/throw and the private loop cell. Head knowledge includes j≤to. Fresh scopes and the displayed arithmetic bounds/renaming consequence are proved. The dense-source typing premise and each primitive/edge connection still need a closed execution or graph proof; the older ModelLoop theorem is not used as a substitute. |

**§8 — The patterns**

These are repeated applications, rather than additional numbered definitions or primitive rules. They are listed for completeness and excluded from the main count.

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Lower bound under aliasing | `grow`, `Bridges/Grow.lean:27` | **equal** | The displayed lower-bound entailment has no separation premise. |
| Bound across a rewriting call | `RawDerivation.sep`, `D:639`; `Derivation.rigidSubst`, `:447` | **narrower** | Both arrays and the rigid substitution must meet B’s restricted representation and certificates. |
| Fresh array spine | `fresh_eff`, `ModelRules.lean:320`; `alloc_post`, `:184` | **equal** | The fresh spine contributes no change below the mark, and empty allocation establishes apartness from older arrays. |
| Write-once cache | `tolerant_frame`, `E:212`; `init_box`, `ModelRules.lean:82` | **narrower** | The atom and its support must be among B’s represented facts and accepted evidence; there is no rule for every atom tolerating initialization. |
| Reliance during callbacks | `RawDerivation.dense`, `D:647`; `reliance_at_prefix`, `CommandLoops.lean:124` | **narrower** | B supplies the density frame and a consequence of an already composed prefix bound, not the callback-chain proposition. |
| Quantified fact across a write | General `Every`, `Assertions.lean`; old `RawDerivation.everyFrame`, `D:640` | **narrower** | The general quantified assertion has no unconditional presence requirement. Its full support/Every framing schema is not bridged to the new syntax; the older certificate retains its presence and scalar restrictions. |
| Structures built in step | `Derivation.pushPost`, `D:595`; `RawDerivation.sep`, `:639` | **narrower** | The length ingredients exist, but there is no B command triple combining the actual push with preservation of the other array’s length. |
| Separation where a value exists | General `Formula.or`, `Formula.separated`, `Assertions.lean`; old `Derivation.guardCases`, `D:369` | **narrower** | The new language has unrestricted disjunction and the complete defined-nonarray separation meaning. A derivation of this guarded regional framing pattern using the full support/substitution infrastructure remains an obligation; the old certificate route retains invariant-guard restrictions. |
| Fact through a field | `grow_path`, `Bridges/Grow.lean:50`; `grow_path_typed`, `Bridges/ModelTyped.lean:150` | **narrower** | The typed bridge requires its particular stable-path and array-type evidence; the derivation route also requires certified substitution in B’s language. |
| Typed-array length | `view_box`, `ModelRules.lean:45` | **equal** | This particular linear fact over a variable and descriptor length is within the theorem’s scope. |
| Index from a shift or mask | `Derivation.arith` at `shr`, `maskRange` and `maskBound`, `ParityDerivations.lean`; `Derivation.linear` | **equal** | The pattern's facts, under its ranges $`0\le c<2^{31}`$, $`0\le d<32`$, $`0\le m<2^{31}`$, are the rules' conclusions, and $`0\le y`$ after the shift follows from them by a linear certificate. |
| Array facts across a typed-array write | General `Every`, `Assertions.lean`; `SupportEvidence.everyCells`, `E:815` | **narrower** | The new body semantics covers the paper’s facts, but the general structural support and its view-write command bridge are not proved. The cited old certificate has extra presence/scalar restrictions. |
| Fact at a handler | `frame_rule`, `try_rule`, `CommandRules.lean` | **equal** | The exceptional box gives the arbitrary framed assertion at the handler’s chosen valid state, and the handler consumes that assertion. Scope excludes the fresh caught name, as required by the paper. |

**§9 — Relation to separation logic**

This section states no additional numbered item or formal rule. It explicitly leaves the proposed correspondence unstated.

**§10 — Future work**

Its conjectures and the language extensions it lists state no claim the
paper makes, so they have no row. §11 adds no numbered definition, theorem, proposition, example or rule display.

**B declarations without a paper counterpart**

Excluding proof infrastructure, representation lemmas and bridges implementing already listed items:

- `Runs.finally`, `finally_`, `finally_sound` — `Bridges/ExitProposals.lean:187,193,198`: finalizer composition; the paper’s command grammar has no `finally`.
- `Runs.settle`, `settle_sound` — `Bridges/ExitProposals.lean:216,220`: conversion of an async body’s throw into a normal call completion.
- `handledGraph`/`handled_safe` and `escapingGraph`/`escaping_safe` — `Examples.lean:24,64,28,104`: additional concrete exception examples.
- `slotless_not_framed` — `NamedCounterexample.lean:46`: an additional concrete counterexample about named field facts under arbitrary writes.

**Count**

Each row except the three proposition summaries and the patterns of §8.
The original 89 rows are all retained (38 equal, 29 narrower, 9 absent,
13 assumed); the latest paper adds Shl (absent) and Or (equal):

| Equal | Narrower | Broader | Different | None in B | Assumed | Total |
|---:|---:|---:|---:|---:|---:|---:|
| 41 | 28 | 0 | 0 | 9 | 13 | 91 |

Imported shared statements are counted in the corresponding rows, rather than called absent merely because they live outside Paper. Equal compares that item’s semantic statement; it does not certify complete syntax admission, all of Definition 23, or implementation by A. Narrower rows state the missing premise/conclusion or unproved bridge explicitly.
