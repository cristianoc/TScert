# B against the paper

For each definition, rule, axiom, law and example of the paper
[Tolerant frames](tolerant-frames-note/note.tex): the statement of B (the
paper's formalisation in Lean, [where B lives](implementation-and-paper-rules.md#where-b-lives))
that is it, and how far it matches. Part 2 of B's first item in
[the basis](implementation-and-paper-rules.md#the-first-item-b). The original audit was read by gpt-6-astra at commit `7a8c19f5` on
2026-11-17 without a build. This table reconciles those rows with the
additions based on fetched `single-pass` commit
`ba681dfdab8ab41c7d73f3c573f449ab90fedab7`. The general semantic statements
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
- Paper line numbers refer to `docs/drafts/tolerant-frames-note/note.tex`.
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
separation and region freshness. Scalar literals cannot contain executable
terms, and suffix conditions are enforced by the term constructors.
`Consequences.lean` states semantic postcondition connectives and general
value-family principles. These do not constitute a complete postcondition
syntax, capture-avoiding substitution, or the complete derivations of
Definition 23. A family of present element readings is not substituted for a
body which may read no element.

`Commands`, `CommandRules`, `Scopes` and `Loops` add actual command
execution and general partial-correctness rules. Runs are raw executions in
the shared calculus; triples choose admissible exit worlds and preserve valid
environments and returned/thrown values. `Admission` distinguishes the paper’s
region forms and fresh lexical bindings from the raw representation. Its
connection to complete typing and derivation admission is a separate obligation.
`Derivations` is explicitly a sound subcalculus of Definition 23, and `Transfer`
assembles Check for that subcalculus with arbitrary regional effects. No
completeness claim about certificates or search is made.

**§1 — The problem**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Example 1, aliasing loop — 75 | `AliasExample.program`, `.body`, `.program_scoped`, `.Head`, `AliasExample.lean`; older `loop_safe`, `ModelLoop.lean:601` | **narrower** | The new command has the output-length test, RangeError construction and throw, private loop cell and exact head bounds. Scopes and displayed integer obligations are proved. A closed execution/graph proof connecting the primitives and all edge obligations is not supplied. The old six-node graph remains a different example. |
| Example 2, rewriting call — 82 | `RawDerivation.sep`, `D:639`, checked at `D:881`; `Derivation.rigidSubst`, `D:447` | **narrower** | These establish the linear length-frame ingredient for arrays and certified rigid substitution. There is no declaration of the complete `readRuns` loop and its call. |

**§2 — What exists: variables, locations, spines**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Definition 3, Commands — 116 | `Operation`, `Primitive`, `Command`, `PrimitiveRun`, `Executes`, `Commands.lean`; `Command.WellScoped`, `Admission.lean` | **narrower** | The grammar and execution constructors include sequence, choice, loops, handlers, break, return, throw, named operations and native calls. Admission separates fresh binding steps from mutations. Full correspondence of admitted syntax, typing, recursive calls and the raw execution representation is not established by these datatype definitions. |

**§3 — Model**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Definition 4, World — 357 | Shared `WorldT`, `WorldAdm`, `WExt`, `Semantics/Worlds.lean`; imported by `SemanticRules.lean` | **equal** | A finite initial segment of roles and step-indexed contracts, with contract admissibility supplied by WorldAdm. WExt appends a tail and preserves all old role/contract entries; truncation changes only the budget at which contracts are read. |
| Definition 5, Well-formed state — 373 | Shared `IndexedHeap`, `Semantics/TwoStateFormulas.lean`; `ValidContext`, `SemanticRules.lean` | **narrower** | IndexedHeap supplies heap/world/budget invariants; ValidContext adds valid source-valued environment roots and a mark within the heap. A full environment-typing judgment for a declared variable type context, and the complete embedding of the paper’s value/object domain, are not given by ValidContext alone. |
| Definition 6, Admissible transition — 405 | Shared `Admissible`, `WorldReach`, `Semantics/TwoStateFormulas.lean`; imported by `SemanticRules.lean` | **equal** | The indexed-state transition lowers the budget and extends the truncated world. The action keeps its name valuation fixed; fresh command bindings and graph renamings are accounted for separately in command scope and transfer. |
| Theorem 7, Preservation — 424 | Shared `safe_run`, `Semantics/IndexedStates.lean`; A `HasTyUsing.sound`, `Programs/ProgramTyping.lean`; `ControlFlow.state_safe`, `Programs/ControlFlow.lean` | **narrower** | The imported run theorem gives admissible endpoints and residual budget from shared calculus safety; A supplies typing-to-safety results. A preservation theorem for the complete admitted B command language and its typing assumptions is not established by the endpoint partial-correctness rules. |

**§4 — The assertion language**

The three proposition-summary rows in this report summarize their following constituent rows and are excluded from the final count.

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Remark 8, Reading — 930 | `box_eq_havoc_wlp`, `box_weakest_stable_on`, `SemanticRules.lean` | **equal** | The box is the wlp of one arbitrary action. For every rigid effect it strengthens F, is stable, and is implied by any stable strengthening G; G ranges over arbitrary assertions. |
| Proposition 9, Laws — 940 — summary | Semantic `box_elim`, `box_and`, `box_anti` in the shared model; `box_mono_on`, `box_or_on`, `box_idem_on` in `SemanticRules.lean` | **equal** | The constituent semantic laws are general; the serialized arena/checker supplies only a restricted certificate route. |
| 9(a), elimination — 942 | Shared `box_elim`, `Semantics/IndexedStates.lean`; interpreted by `Formula.meaning`, `Assertions.lean` | **equal** | Reflexive elimination quantifies over arbitrary assertions, including the general interpreter; its scope is not limited by the old arena/checker. |
| 9(b), conjunction equivalence — 943 | Shared `box_and`, `Semantics/IndexedStates.lean`; general `Derivation.boxAnd`, `.boxLeft`, `.boxRight`, `Derivations.lean` | **equal** | Both directions hold for arbitrary assertion interpretations. The general derivation constructors state the same conjunction laws. |
| 9(b), monotonicity — 943 | `box_mono_on`, `SemanticRules.lean`; shared `box_mono`, `Semantics/IndexedStates.lean` | **equal** | The premise is arbitrary semantic entailment on valid contexts. No finite context-free certificate is required by the semantic law. |
| 9(c), antitonicity in effects — 944 | Shared `box_anti`, `Semantics/IndexedStates.lean`; general `Derivation.boxAnti`, `Derivations.lean` | **equal** | Inclusion of actions gives the stated antitonicity for arbitrary assertions. InclusionEvidence is only one certificate route to that premise. |
| 9(d), invariant disjunction — 945 | `box_or_on`, `SemanticRules.lean` | **equal** | The guard is an arbitrary semantically invariant assertion on valid contexts. There is no syntactic invariant-guard restriction on disjunction or this law. |
| 9(e), idempotence — 946 | `box_idem_on`, `RigidOn`, `SemanticRules.lean` | **equal** | The premise is transitivity of the action on valid contexts, not successful rigidity evidence. |
| Proposition 10, Guards and quantified facts — 956 — summary | `guard`, `every_inst`, `every_prefix`, `every_empty`, `Assertions.lean` | **narrower** | General Guard and Prefix are stated exactly. Instantiation still lacks its syntactic substitution/derivation bridge, and the exact Empty corollary needs the valid-root defined-length bridge. |
| (Guard) — 960 | `guard`, `equal_contradiction`, `contents_contradiction`, `Assertions.lean` | **equal** | The reading is any partial path reading, including optional final fields; disjunction requires no invariant guard. Unequal values contradict equality of the same reading. |
| (Inst) — 961 | `every_inst`, `Assertions.lean`; older `Derivation.everyElim`, `D:463` | **narrower** | The general semantic lemma interprets the complete body at an evaluated integer index, including fields, shifts and disjunctions. Capture-avoiding syntactic body instantiation and its inclusion in the full derivation system are not supplied by it. |
| (Prefix) — 962 | `every_prefix`, `Assertions.lean` | **equal** | For arbitrary defined linear bounds t and t′, t′≤t restricts the full quantified predicate to its smaller range. No density, scalar-body or single-term restriction is imposed. |
| (Empty) — 963 | `every_empty`, `Assertions.lean`; older `Derivation.everyEmpty`, `D:456` | **narrower** | The semantic lemma handles either collection kind and any nonpositive linear bound. Its explicit collection-entry premise needs the shared-model bridge from the paper’s defined-length premise at a valid root; the exact displayed corollary is not proved. |

**§5 — Entering the modality**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Definition 11, Support — 986 | `Supports`, `SemanticRules.lean`; shared `SupportDomain.Supports`, `Semantics/Support.lean` | **equal** | The shared support-domain definition is instantiated at arbitrary assertions, with valid roots and mark supplied by `ValidContext`. It includes the condition on every admissible transition, rather than just a particular run. |
| Definition 12, Respect — 1012 | `Respects`, `respects_of_check`, `SemanticRules.lean` | **equal** | Semantic respect quantifies over every effect action from K. The existing Boolean pairwise test is proved sufficient, and is not used as the definition. |
| Theorem 13, Tolerant frame — 1034 | `tolerant_frame`, `SemanticRules.lean` | **equal** | The premises are general semantic support under C, semantic respect under K, and C on every action. The conclusion is K ∧ F entailing the box on the well-formed contexts of the paper; no finite evidence premise is substituted. |
| Definition 14, Supports of the atoms — 1049 | `SupportEvidence`, `E:811`; general `supports_and`, `supports_or`, `SemanticRules.lean` | **narrower** | Arbitrary conjunction/disjunction supports are semantic theorems. The structural definition and soundness proof for the entire atom/term support table, freshness supports, and modality-free all support are not supplied; the older certificates remain restricted. |
| Proposition 15, Axioms of the atoms — 1138 — summary | `RawDerivation.grow`, `.dense`, `.sep`, `.everyFrame`, `.init`, `.view`; `Derivation.rigidSubst` | **narrower** | The individual restrictions follow. |
| (Grow) — 1143 | `grow`, `Bridges/Grow.lean:27`; `RawDerivation.grow`, `D:646`; `SupportEvidence.lengths`, `E:813` | **equal** | For the displayed lower bound over a variable or constant, B establishes preservation under arbitrary value changes and spine growth, without separation. Literal lower bounds can use the linear-support rule directly. |
| (Dense) — 1144 | General `Atom.dense`, `Assertions.lean`; old `RawDerivation.dense`, `D:647` | **narrower** | The general syntax admits every defined linear bound. The old finite certificate only accepts a variable bound directly. The displayed modal density schema at variables or literals is not connected to the new interpreter by a general support proof. |
| (Sep) — 1145 | `RawDerivation.sep`, `D:639`, checked at `D:881` | **narrower** | The fact must be linear over variables and the one array length, and both separated paths must read arrays. The paper allows any qualifying atom and includes the null/undefined case for the other value. |
| (Every) — 1146 | `RawDerivation.everyFrame`, `D:640`; general `Every`, `Assertions.lean` | **narrower** | The general assertion no longer inserts density or unconditional element presence, and its complete body grammar is interpreted. The general Every framing schema and its support proof are not bridged to that interpretation; the old certificate has its original restrictions. |
| (Init) — 1147 | `init_box`, `ModelRules.lean:82`; `init_path`, `:96`; `RawDerivation.init`, `D:641` | **narrower** | The atom is restricted to a linear fact over current terms. The paper quantifies over every atom whose heap reading is the displayed path length. |
| (Rigid) — 1148 | `Derivation.rigidSubst`, `D:447` | **narrower** | Capture avoidance and absence of the fresh witness from the effect are represented, but both the atom and its modal derivation must belong to B’s restricted assertion and derivation languages. |
| (View) — 1149 | `view_box`, `ModelRules.lean:45`; `RawDerivation.view`, `D:642`, checked at `D:930` | **narrower** | `view_box` covers linear facts over variables and view lengths; the derivation route covers assertions recognized by `invNode`. Neither states the schema for every qualifying paper atom. |

**§6 — Programs**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Break — 1209 | `break_rule`, `ExitPost`, `Triple`, `Commands.lean` | **equal** | The normal postcondition is false; the unchanged state meets the enclosing loop’s obligation. Break is a distinct control exit, consumed by the enclosing loop. |
| Return — 1210 | `FunctionReturn`, `return_function_rule`, `Commands.lean` | **equal** | The obligation substitutes the returned atom for the result while explicitly freezing old at the enclosing function’s entry. It is threaded unchanged through local command entries; the normal postcondition is false. |
| Throw — 1211 | `throw_rule`, `Commands.lean` | **equal** | Throw has false normal postcondition and retains arbitrary R at the handler state. The thrown value’s source/reference validity is the type-system part of the triple, distinct from R. |
| Try — 1212 | `try_rule`, `CommandRules.lean` | **equal** | The handler runs after the actual throw and binding of its fresh caught name. R, Q and Qe are one-state assertions; R does not mention the caught name. Caught-value validity is derived from the body’s typed exit guarantee. |
| Entry — 1249 | `entry_rule`, `CommandRules.lean` | **equal** | Both exit postconditions are strengthened by arbitrary old(B) and the corresponding regional action, with B supplied at entry. Scope and marks are explicit in the triple. |
| Frame — 1251 | `frame_rule`, `CommandRules.lean`; `scope_stable_of_avoids`, `Scopes.lean` | **equal** | Both normal and exceptional boxes are eliminated using their own effects. Scope transport is precisely the paper’s fresh-binding condition; it follows from dependence on names the command does not bind. No finite assertion/region certificate restriction is imposed. |
| Frame⁺ — 1253 | `frame_plus_rule`, `CommandRules.lean`; `RigidOn`, `SemanticRules.lean` | **equal** | Semantic rigidity on valid contexts retains the box at the normal exit. Scope transport includes the effect under the modality and is proved from noncapture. |
| Loop — 1255 | `loop_invariant`, `loop_rule`, `Loops.lean` | **equal** | Induction on actual loop execution handles normal iterations, break, return and throw. The body normal post gives I; its break obligation is I ∧ box R, as stated in the paper’s explanation. Semantic effect and rigidity plus noncapture retain the modality; no supplied prefix summary replaces the rule. |
| Call — 1257 | `call_rule`, `ModelRules.lean:154` | **narrower** | B’s theorem is for a checked graph, its normal completion, slot renaming and a list of named caller facts. The two-exit signature theorem cited by the paper, `call_exits_exact`, is **outside B**, `Semantics/CallEffects.lean:541`. |
| Alloc, empty array — 1259 | `alloc_step`, `ModelRules.lean:177`; `alloc_post`, `:184` | **equal** | The allocated array has a fresh spine, length zero, and is apart from every pre-existing array. Freshness at the allocation heap length implies freshness at the enclosing invocation’s earlier mark. |
| Seq-Eff — 1261 | `seq_eff`, `ModelRules.lean:310`; `CommandSummary.seq_sound`, `CommandComposition.lean:163` | **narrower** | B requires the computed `rebaseAll` with `RebaseOk` and a successful `Footprint.le` check. The paper permits any rebasing satisfying its coverage relation and semantic effect inclusion. The general `Post.compose_rebases` is outside B, `Semantics/ExitComposition.lean:110`. |
| Fresh-Eff — 1263 | `fresh_eff`, `ModelRules.lean:320` | **equal** | For every location below the mark, the fresh spine’s entry is removable from the effect. The theorem does not remove effects on cells that spine lists. |
| If — 1308 | `if_rule`, `if_effects`, `CommandRules.lean` | **equal** | The two branches are checked under the true/false truthiness of the named test atom, with arbitrary shared postconditions and regional effects. Test facts from the operation that produced that atom remain the separate Test rule obligation. |
| Seq — 1313 | `seq_rule`, `CommandRules.lean` | **equal** | The intermediate and exit assertions are one-state assertions as displayed. The first execution supplies the intermediate world and valid environment; the second starts there, with the same invocation mark. |
| Alloc, array literal — 1349 | **none in B**. Cited outside B: `literalArrayAtoms_holds`, `Programs/IndexWrites.lean:175` | **none in B** | B’s empty-array theorem does not establish arbitrary literal contents and density. The paper itself marks those parts conjectural. |
| Alloc, object literal — 1350 | **none in B** | **none in B** | `alloc_state` (`KindsModelRules.lean:508`) establishes allocation/state properties, not the displayed freshness-and-field-equalities postcondition. |
| Definition 16, Independence of the world — 1379 | `Independent`, `Commands.lean`; shared `IndependentFrom`, `Semantics/ExitWorlds.lean` | **equal** | The entry and both exit contexts are valid; the entry is fixed and exit environments agree. Truth agrees at admissible exits with equal heap and budget, regardless of their worlds. No property at invalid environments or marks is required. |
| Conj — 1397 | `conj_rule`, `Commands.lean`; `SafePostExcV.conj_independent`, `SemanticRules.lean` | **equal** | The first proof’s admissible world and shared break/return obligations are retained. Only the second normal and exceptional postconditions need independence. In the shared safety encoding, retaining the first result family discharges compatibility by projection. |
| Definition 17, Rebasing — 1412 | **none in B**. Shared model: `Rebases`, `Semantics/ExitComposition.lean:77` | **none in B** | `Rebases` states the coverage relation with the absorption by $`\Phi`$ at `any` explicit, and holds no evidence $`\mathit{ev}`$: the paths reading each named value in both heaps are premises of `rebase_sound` for the computed rebasing (checked). |
| Example 18, Freshness bounds effects, not facts — 1447 | **none in B** | **none in B** | `fresh_eff` proves the effect ingredient. `apart_not_kept_fresh` (`ModelRules.lean:251`) refutes preservation of apartness, not this shrink-and-read example or its length fact. |
| Proposition 19, Reliance — 1459 | `ActionChain.action_on`, `reliance_on`, `SemanticRules.lean` | **equal** | An arbitrary finite chain of actions bounded by a rigid effect is one action. The initial box gives F at any selected prefix endpoint. Each native step and callback must supply its action bound; an endpoint summary alone does not supply these prefixes. |
| Field-Read — 1478 | `Operation.code`, `Commands.lean`; general `Atom.equal`, `.optionalEqual`, `Assertions.lean`; shared `ReadGave`, `Semantics/HeapFacts.lean` | **none in B** | Own-field command lookup explicitly bypasses prototype fallback when the own field is absent, matching optional equality. A full general primitive triple/effect proof from the required-field or optional-field typing assumptions is not supplied; code and assertion definitions alone are not that rule. |
| Field-Write — 1479 | **none in B**. Cited outside B: `fieldWriteFrame`, `Programs/ExpressionEffects.lean:112`; `FieldWritten`, `:155`; `fieldWriteStep_sound`, `:229` | **none in B** | B proves preservation consequences of some writes, not the general exact field-write rule. |
| Elem-Read — 1480 | `elementValue`, `Atom.element`, `Assertions.lean`; `Operation.elementRead`, `Commands.lean` | **none in B** | The general ordinary/view element assertion, including holes, and the executed ordinary read are defined. Their exact primitive triple/effect and typing/definedness bridge is not proved. |
| Arr-Length — 1481 | `Operation.arrayLength`, `Commands.lean`; shared `lengthOf`, `Semantics/IndexFacts.lean` | **none in B** | The operation is interpreted through the shared calculus. The general displayed primitive triple with exact equality and empty effect is not proved. |
| Test — 1482 | `Operation.binary`, `.not`, `.and`, `.or`, `Commands.lean`; `if_rule`, `CommandRules.lean` | **none in B** | Truthiness and Boolean operation execution are represented. The complete comparison/nullish/negation/conjunction/disjunction fact rules tying bindings to branch knowledge are not proved. |
| Fun — 1547 | `CommandSummary.signature_holds`, `CommandBodies.lean:86`; `.signature_holds_below`, `:106` | **narrower** | B transports a supplied sound body summary to a supplied signature at call positions. It does not establish the recursive function rule, default `undefined` return, and return obligations from the displayed body premises. Cited outside B: `codeObligations_sound`, `Programs/CodeConditions.lean:218`. |
| Write-In — 1572 | `Derivation.writeIn`, `D:583`; `lengthsKept_of_run`, `Bridges/ParityArithmeticBridges.lean:189` | **narrower** | The conclusion concerns an array held in corresponding entry/exit slots. The paper states preservation of the length read through every path; B does not package the preservation of those path reads into this rule. |
| Write-End — 1573 | `Derivation.writeEnd`, `D:589`; `boundedWrite_of_run`, `Bridges/ParityArithmeticBridges.lean:209` | **equal** | Given the bounded-write operation postcondition and the displayed end-index premises, B concludes exactly the length increase by one. The current paper does not put element equality or density extension in this rule. |
| Push — 1574 | `PushPost`, `Consequences.lean`; older `Derivation.pushPost`, `D:595` | **narrower** | The full length, appended-element and universal kept-prefix postcondition is stated semantically. A command-level rule deriving it from the explicit native contract and connecting it to the full assertion language is not proved. |
| Write-Kept — 1606 | `write_kept`, `Consequences.lean`; shared/A `keptCells_holds`, `Programs/HeapExpressionRules.lean:1404` | **narrower** | The general value-family preservation principle is proved. The command-level bridge identifying the read field as unchanged or written by the actual field operation is not supplied. |
| Push-Every — 1607 | `push_every`, `Consequences.lean`; older A `every_appended`, `Programs/PromiseCalls.lean:2375` | **narrower** | The theorem extends arbitrary predicates of actual element readings using PushPost. It still needs the bridge for the paper’s body, its preserved free terms and whole-array premise, and the actual push command contract. |
| View-Every — 1608 | `view_every`, `every_written`, `ViewWritePost`, `Consequences.lean` | **narrower** | The principle preserves and conditionally extends predicates using the converted value, without requiring conversion to be identity. EveryValue requires a reading at each index; the paper’s Every does not. The full body bridge must handle that distinction and preserved free terms rather than infer presence. |
| Add — 1648 | `Derivation.integerOperation`, `D:536`; `integerOperation_sound`, `:1363` | **equal** | Safe operands and a safe mathematical sum give the exact sum. |
| Sub — 1648 | `Derivation.integerOperation`, `D:536`; `integerOperation_sound`, `:1363` | **equal** | Safe operands and a safe mathematical difference give the exact difference. |
| Scale — 1648 | `Derivation.integerOperation`, `D:536`; `resultForm`, `:205` | **equal** | Multiplication requires a constant factor and a safe mathematical result. |
| Shr — 1649 | `Derivation.shiftRight`, `D:522`; `shrFacts`, `:193`; `shiftRight_sound`, `:1299` | **equal** | The operand and shift ranges, nonnegative result, and both quotient bounds agree. A constant may be a literal or a value proved constant. |
| Mask — 1650 | `Derivation.mask`, `D:529`; `maskFacts`, `:199`; `mask_sound`, `:1327` | **equal** | Both upper bounds—by the mask and by the operand—and the stated ranges agree. |
| String-length successor — 1655 | `Derivation.lengthSuccessor`, `D:547`; `lengthSuccessor_sound`, `:1428` | **equal** | The result is the exact safe sum or the number $`2^{53}`$, under the stated string-length equality. |
| Str-Length — 1668 | `Derivation.stringLengthRead`, `D:567` | **equal** | The conclusion is the string’s UTF-16 length, represented as the result’s safe integer; B states also that the result is a safe integer, which the row's $`y=\|s\|`$ implies by the meaning of a defined term. The row is the entry `ArithmeticRules.strLength` (proved: `strLength_sound`); B's facts are its conclusion substituted, after `safeFact` (`Bridges.lengthReadFacts_entry`). |
| Str-Read — 1669 | `Derivation.stringRead`, `D:573`; `stringIndexFacts`, `:258` | **equal** | B's premises are $`0\le i`$, $`i+1\le\|s\|`$ and $`i\le 2^{32}-2`$, the row's $`0\le i<\|s\|\wedge i<N`$ for $`N=2^{32}-1`$; the conclusion is result length one. The row is the entry `ArithmeticRules.strRead` (proved: `strRead_sound`), whose premises and conclusion substituted are B's (`Bridges.stringRead_entry`). The pass (A) has no producer of this fact. |
| Concat — 1670 | `Derivation.stringConcat`, `D:578`; `concatFacts`, `:242` | **narrower** | For a normal string concatenation, the result length is the sum of the operand lengths. B takes the premises $`0\le\|s\|`$ and $`0\le\|s'\|`$, where the row's precondition is $`\mathsf{true}`$; a string's length is non-negative by the term's meaning. The row is the entry `ArithmeticRules.concat` (proved: `concat_sound`); B's conclusion is its conclusion substituted (`Bridges.concatFacts_entry`). |
| Library: `charCodeAt` range — 1685 | **none in B**. Cited outside B: `unit_bound`, `Semantics/StringPostconditions.lean:10`; `code_unit_safe`, `:23` | **assumed** | B has no corresponding host-call contract rule. The cited lemmas concern model code units. The row is the entry `ArithmeticRules.charCodeAt`, assumed of A's overlay signature `String.prototype.charCodeAt`, which states it alike: $`\mathrm{int}(i)`$, $`0\le i<\|s\|`$ give $`\mathrm{int}(r)`$, $`0\le r\le 65535`$. |
| Library: `codePointAt` range — 1686 | **none in B** | **assumed** | The paper states an assumed host contract; no B declaration states it. The row is the entry `ArithmeticRules.codePointAt`, assumed of A's overlay signature `String.prototype.codePointAt`, whose one bounded signature states this row's facts and the next row's. |
| Library: `codePointAt` two-unit implication — 1687 | **none in B** | **assumed** | No B declaration gives the displayed implication from the returned code point to the remaining string length. The row is the entry `ArithmeticRules.codePointPair`. A's signature states in its place the linear fact $`r\le\mathtt{0xFFFF}+2^{20}(\|s\|-i-1)`$, which under $`0\le r\le\mathtt{0x10FFFF}`$ and $`i<\|s\|`$ holds exactly where the implication does. |
| Library: string `indexOf`/`lastIndexOf` general bounds — 1688 | **none in B**. Cited outside B: `search_bounds`, `Semantics/StringPostconditions.lean:40` | **assumed** | B has no corresponding host-call contract. The row is the entry `ArithmeticRules.indexOf`, assumed of A's overlay signatures `String.prototype.indexOf` and `lastIndexOf`, which state it alike and take an optional position beside $`u`$. |
| Library: nonempty-needle strict bound — 1689 | **none in B**. Cited outside B: `search_bounds`, `Semantics/StringPostconditions.lean:40` | **assumed** | No B rule derives the strict upper bound from the needle-length premise. The row is the entry `ArithmeticRules.indexOfNonempty`; A's signature at $`1\le\|u\|`$ states also $`-1\le r`$, the first row's lower bound. |
| Library: string `slice` length — 1690 | **none in B**. Cited outside B: `slice_length`, `Semantics/StringPostconditions.lean:32` | **assumed** | B has no host-call rule producing this exact length. The row is the entry `ArithmeticRules.slice`, assumed of A's overlay signature `String.prototype.slice`, which states it alike. |
| Library: array `indexOf` bounds — 1691 | **none in B** | **assumed** | No B declaration states the displayed contract. The row is the entry `ArithmeticRules.arrayIndexOf`, assumed of A's overlay signature `Array.prototype.indexOf`, which states it alike. |
| Library: typed-array construction length — 1692 | **none in B** | **assumed** | No B declaration states the general constructor contract. The row is the entry `ArithmeticRules.newView`, its $`n`$ a `Num`. A's form `viewOfLength` takes the wider precondition $`(\mathrm{int}(n)\land 0\le n)\lor\mathrm{past}(n)`$, which admits the double $`2^{53}`$, at which the construction throws (the next row), and states the result's length $`\mathrm{view}(r)=n`$. |
| Library: construction at $`2^{53}`$ throws — 1696 | **none in B** | **assumed** | No B theorem states this exceptional outcome. |
| View-Length — 1720 | **none in B** | **assumed** | The row is the entry `ArithmeticRules.viewLength`, assumed of `%ByteLength%`. B’s view-length invariance results concern preservation, not the primitive read. |
| View-Read — 1721 | **none in B** | **assumed** | The row is the entry `ArithmeticRules.viewRead`, assumed of `%ByteAt%`; its index is a `SafeInt`, where the paper's text takes an atom holding a `Num` and reads the linear precondition as holding of an integer alone. B has a view-element assertion and support evidence, but no primitive-read rule establishing that assertion. |
| View-Write — 1722 | **none in B** as a general rule. Cited outside B: `ViewWrite`, `Semantics/ElementWrites.lean:361`; `ExactWrite`, `:184` | **assumed** | The row is the entry `ArithmeticRules.viewWrite`, assumed of `%ByteSet%`, `ViewWrite` and `WriteAt`; its index is a `SafeInt`, as View-Read's. B supplies concrete witnesses such as `viewWrite_overlap` (`KindsModelRules.lean:161`), not the rule for every format, value and in-bounds index. |
| View-Write-Any — 1723 | **none in B**. Related cited contract outside B: `ViewWrite`, `Semantics/ElementWrites.lean:361` | **assumed** | The row is the entry `ArithmeticRules.viewWriteAny`, assumed of `%ByteSet%` and `ViewWrite`. No B declaration states the effect for every numeric index, including out-of-bounds indices. |
| Example 20, A write through a typed array — 1748 | `ViewWrite.goal` and checked derivation, `Tests/ParityDerivationTests.lean:243,245`; `viewWrite_overlap`, `KindsModelRules.lean:161` | **narrower** | The test derives the first four preserved facts, using variables for the constant prefix/index. It omits preservation of the written view’s other element; failure of one framing certificate for the other view is not a counterexample, while `viewWrite_overlap` supplies a separate concrete overlap witness. |

**§7 — Transfer along edges**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Definition 21, Checked transfer — 1793 | `Check`, `Edge`, `Target`, `Transfer.lean`; `Derivation`, `Derivations.lean` | **narrower** | Check assembles exactly old knowledge, the regional transition, node postcondition, branch condition and renamed target. Its proof datatype is explicitly a sound subcalculus; full Definition 23 and syntactic substitution/admission are separate obligations. |
| Theorem 22, Transfer — 1804 | `edge_sound_of_triple`, `transfer`, `Transfer.lean` | **narrower** | Execution-connected transfer handles arbitrary regional effects, knowledge and target interpretations, preserving valid environments and chosen exit worlds. Its Check predicate uses the sound general subcalculus, not the full derivations of Definition 23; graph-wide safety/prefix preservation is not inferred from the endpoint triple. |
| Definition 23, Derivations — 1812 | `Derivation`, `.sound`, `Derivations.lean`; older `Derivation`, `RawDerivation`, `D:342,605` | **narrower** | The new finite proof datatype has general logical connectives, implication/index/value instantiation and modal laws, with soundness. Complete atom/term substitution, contradictions as rule constructors, structural/all-support framing, arithmetic and remaining paper schemas are not all represented. The serialized checker remains a separate restricted certificate layer. |
| Example 24, Example 1 in full — 1903 | `AliasExample.program`, `.program_scoped`, `.Head`, `.read_bound`, `.write_bound`, `.increment_range`, `.back_edge`, `.exit`, `AliasExample.lean` | **narrower** | The actual command contains both tests, RangeError construction/throw and the private loop cell. Head knowledge includes j≤to. Fresh scopes and the displayed arithmetic bounds/renaming consequence are proved. The dense-source typing premise and each primitive/edge connection still need a closed execution or graph proof; the older ModelLoop theorem is not used as a substitute. |

**§8 — The patterns**

These are repeated applications, rather than additional numbered definitions or primitive rules. They are listed for completeness and excluded from the main count.

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Lower bound under aliasing — 1948 | `grow`, `Bridges/Grow.lean:27` | **equal** | The displayed lower-bound entailment has no separation premise. |
| Bound across a rewriting call — 1949 | `RawDerivation.sep`, `D:639`; `Derivation.rigidSubst`, `:447` | **narrower** | Both arrays and the rigid substitution must meet B’s restricted representation and certificates. |
| Fresh array spine — 1950 | `fresh_eff`, `ModelRules.lean:320`; `alloc_post`, `:184` | **equal** | The fresh spine contributes no change below the mark, and empty allocation establishes apartness from older arrays. |
| Write-once cache — 1951 | `tolerant_frame`, `E:212`; `init_box`, `ModelRules.lean:82` | **narrower** | The atom and its support must be among B’s represented facts and accepted evidence; there is no rule for every atom tolerating initialization. |
| Reliance during callbacks — 1952 | `RawDerivation.dense`, `D:647`; `reliance_at_prefix`, `CommandLoops.lean:124` | **narrower** | B supplies the density frame and a consequence of an already composed prefix bound, not the callback-chain proposition. |
| Quantified fact across a write — 1953 | General `Every`, `Assertions.lean`; old `RawDerivation.everyFrame`, `D:640` | **narrower** | The general quantified assertion has no unconditional presence requirement. Its full support/Every framing schema is not bridged to the new syntax; the older certificate retains its presence and scalar restrictions. |
| Structures built in step — 1954 | `Derivation.pushPost`, `D:595`; `RawDerivation.sep`, `:639` | **narrower** | The length ingredients exist, but there is no B command triple combining the actual push with preservation of the other array’s length. |
| Separation where a value exists — 1955 | General `Formula.or`, `Formula.separated`, `Assertions.lean`; old `Derivation.guardCases`, `D:369` | **narrower** | The new language has unrestricted disjunction and the complete defined-nonarray separation meaning. A derivation of this guarded regional framing pattern using the full support/substitution infrastructure remains an obligation; the old certificate route retains invariant-guard restrictions. |
| Fact through a field — 1956 | `grow_path`, `Bridges/Grow.lean:50`; `grow_path_typed`, `Bridges/ModelTyped.lean:150` | **narrower** | The typed bridge requires its particular stable-path and array-type evidence; the derivation route also requires certified substitution in B’s language. |
| Typed-array length — 1957 | `view_box`, `ModelRules.lean:45` | **equal** | This particular linear fact over a variable and descriptor length is within the theorem’s scope. |
| Index from a shift or mask — 1958 | `Derivation.shiftRight`, `D:522`; `.mask`, `:529` | **equal** | Their conclusions include the displayed bounds under the stated ranges. |
| Array facts across a typed-array write — 1959 | General `Every`, `Assertions.lean`; `SupportEvidence.everyCells`, `E:815` | **narrower** | The new body semantics covers the paper’s facts, but the general structural support and its view-write command bridge are not proved. The cited old certificate has extra presence/scalar restrictions. |
| Fact at a handler — 1960 | `frame_rule`, `try_rule`, `CommandRules.lean` | **equal** | The exceptional box gives the arbitrary framed assertion at the handler’s chosen valid state, and the handler consumes that assertion. Scope excludes the fresh caught name, as required by the paper. |

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

Each row except the three proposition summaries and the patterns of §8:

| Equal | Narrower | Broader | Different | None in B | Assumed | Total |
|---:|---:|---:|---:|---:|---:|---:|
| 40 | 27 | 0 | 0 | 9 | 13 | 89 |

Imported shared statements are counted in the corresponding rows, rather than called absent merely because they live outside Paper. Equal compares that item’s semantic statement; it does not certify complete syntax admission, all of Definition 23, or implementation by A. Narrower rows state the missing premise/conclusion or unproved bridge explicitly.
