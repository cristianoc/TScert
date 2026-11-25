# B against the paper

For each definition, rule, axiom, law and example of the paper
[Tolerant frames](tolerant-frames-note/note.tex): the statement of B (the
paper's formalisation in Lean, [where B lives](implementation-and-paper-rules.md#where-b-lives))
that is it, and how far it matches. Part 2 of B's first item in
[the basis](implementation-and-paper-rules.md#the-first-item-b). Read by
gpt-6-astra from the sources at commit `7a8c19f5` on 2026-11-17, with no
build or test run; four of its claims (Example 1, Push, Fresh-Eff and the
quantified atom's presence condition) were checked against the source. The rows Add, Sub, Scale, Shr, Mask, Shl, Or and the index from a shift
or a mask state the sources with `Derivation.arith`, after that commit.

The paper is the source of truth. Where B has no statement of an item, the
row names the statement of the shared model (`Semantics/`) or of A
(`Programs/`, `Source/`) the paper's status tag cites, checked against the
paper where the row says so. **Assumed** marks a host contract the paper
states as assumed, which B does not state either.

B is narrower than the paper. Several general statements cited by the paper live entirely outside B. Within B, the main restrictions are the assertion grammar, the available support and rigidity certificates, and command summaries that do not state the complete displayed command rule.

Notation for source references:

- All B filenames below are relative to `lean/Verification/Paper/TolerantFrames/`.
- `D` = `ParityDerivations.lean`; `E` = `ParityEvidence.lean`; `A` = `ParityAssertions.lean`.
- Outside-B filenames are relative to `lean/Verification/`.
- Paper line numbers refer to `docs/drafts/tolerant-frames-note/note.tex`.
- **Equal** compares the stated logical content, expressing an executed primitive through its semantic operation postcondition. It does not assert that acceptance applies the declaration.
- Test declarations and `#guard` commands were read, not executed.

A restriction recurring below is worth stating once. B validates assertions with `Atom.wellFormed` (`A:258`) and `AssertionNode.wellFormed` (`A:439`). Its quantified facts concern arrays, require every quantified index present, and admit scalar bodies only. Bounds and element indices are individual terms. Its disjunctions require a syntactically recognized invariant guard. The underlying definitions are **outside B**, in `Semantics/TwoStateFormulas.lean:196`, `:210`, `:251`, and `:270`. In particular, its separation requires two arrays; the paper’s separation also holds when either defined value is not an array.

**§1 — The problem**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Example 1, aliasing loop — 75 | `loop_safe`, `ModelLoop.lean:601`; `loopGraph`, `:444` | **different** | B’s graph has no `j > out.length` test or throw. Its element write permits writes beyond the current length; the paper’s example explicitly checks that the write is inside or at the end. |
| Example 2, rewriting call — 82 | `RawDerivation.sep`, `D:639`, checked at `D:881`; `Derivation.rigidSubst`, `D:447` | **narrower** | These establish the linear length-frame ingredient for arrays and certified rigid substitution. There is no declaration of the complete `readRuns` loop and its call. |

**§2 — What exists: variables, locations, spines**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Definition 3, Commands — 116 | **none in B** | **none in B** | `Runs` (`CommandSummaries.lean:41`) is an arbitrary relation on two completion kinds, not the paper’s inductive command language with steps, sequence, choice, loop, handler, return, throw and break. The definition has no Lean status citation. |

**§3 — Model**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Definition 4, World — 357 | **none in B**. Outside B: `WorldT`, `Semantics/Worlds.lean:198`; `WExt`, `:257` | **none in B** | B imports worlds. The paper gives no status citation on this definition. |
| Definition 5, Well-formed state — 373 | **none in B**. Shared model: `IndexedHeap`, `Semantics/TwoStateFormulas.lean:78` | **none in B** | The shared model's state is a budget, a world, a heap, its positivity, `WorldAdm` and `HeapOk`; it holds no environment, so the environment's part of (W3) and (W4) is stated apart where it is used (`RootsOk`). Whether `HeapOk` is exactly (W1)–(W4) for the heap is not checked here. |
| Definition 6, Admissible transition — 405 | **none in B**. Shared model: `Admissible`, `WorldReach`, `Semantics/TwoStateFormulas.lean:88,104` | **none in B** | The shared model states it equally: `WorldReach W W'` is a budget $`k' \le k`$ with $`W`$ truncated to $`k'`$ extended by $`W'`$ (checked). |
| Theorem 7, Preservation — 424 | **none in B**. Shared model: `safe_run`, `run`, `Semantics/IndexedStates.lean:131–150`; A: `HasTyUsing.sound`, `Programs/ProgramTyping.lean:712`; `ControlFlow.state_safe`, `Programs/ControlFlow.lean:1322` | **none in B** | The shared model states it from a safety premise (`Safe`) in place of acceptance by the type system: a run of $`j < k`$ steps reaches an admissible state with budget $`k - j`$ (checked). The step from typing to that premise, and (W1)–(W3), are A's. |

**§4 — The assertion language**

The three proposition-summary rows in this report summarize their following constituent rows and are excluded from the final count.

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Remark 8, Reading — 930 | **none in B** | **none in B** | No declaration identifies the modality with weakest liberal precondition or proves the stated weakest stable strengthening characterization. |
| Proposition 9, Laws — 940 — summary | `Derivation.boxElim` through `boxIdem`, `D:399–432` | **narrower** | The rules concern B’s represented assertions and, where applicable, checked inclusion, invariance and rigidity evidence. |
| 9(a), elimination — 942 | `Derivation.boxElim`, `D:399` | **narrower** | The conclusion is the same for represented assertions; the quantification over every assertion of the paper is absent. Cited general theorem outside B: `box_elim`, `Semantics/IndexedStates.lean:183`. |
| 9(b), conjunction equivalence — 943 | `Derivation.boxAndIntro`, `D:402`; `boxAndLeft`, `:407`; `boxAndRight`, `:411` | **narrower** | Both directions exist for represented assertions only. Cited general theorem outside B: `box_and`, `Semantics/IndexedStates.lean:186`. |
| 9(b), monotonicity — 943 | `Derivation.boxMono`, `D:415` | **narrower** | B requires a context-free derivation of the premise entailment in its own system; arbitrary semantic entailment is insufficient. Cited outside B: `box_mono`, `Semantics/IndexedStates.lean:191`. |
| 9(c), antitonicity in effects — 944 | `Derivation.boxAnti`, `D:420` | **narrower** | Semantic inclusion of actions is replaced by a successful `InclusionEvidence` certificate under an established assertion. Cited outside B: `box_anti`, `Semantics/IndexedStates.lean:195`. |
| 9(d), invariant disjunction — 945 | `Derivation.boxGuard`, `D:424` | **narrower** | The guard must pass `invNode`; B does not accept an arbitrary proof that the guard is invariant. Cited outside B: `box_or`, `Semantics/IndexedStates.lean:211`. |
| 9(e), idempotence — 946 | `Derivation.boxIdem`, `D:430`; `RigidityEvidence`, `E:563` | **narrower** | Rigidity evidence is either a closed effect or regions stable along certified rigid paths, with a recognized invariant domain. Transitivity of an arbitrary effect is not an accepted premise. Cited outside B: `box_idem`, `Semantics/IndexedStates.lean:219`. |
| Proposition 10, Guards and quantified facts — 956 — summary | `guardCases`, `D:369`; `everyElim`, `:463`; `everyEmpty`, `:456` | **narrower** | B has restricted instances; it has no general Prefix rule. |
| (Guard) — 960 | `Derivation.guardCases`, `D:369`; `atomClash`, `:516` | **narrower** | B admits invariant-guard disjunctions and the displayed equality-versus-contents contradiction. It lacks the general optional-field guard and a constructor expressing every unequal-value contradiction in the paper. Cited outside B: `unguardIndices_holds`, `Semantics/HeapKnowledge.lean:3242`; `releaseEither_holds`, `:3855`. |
| (Inst) — 961 | `Derivation.everyElim`, `D:463`; `everyInstances`, `:332` | **narrower** | B elaborates only atomic clauses whose terms are the index and free parameters. It skips disjunctive clauses and clauses containing the element, its string length, its fields or shifted elements. Cited outside B: `instantiateEvery_holds`, `Semantics/HeapKnowledge.lean:3760`; `elementInstances_holds`, `:3829`. |
| (Prefix) — 962 | **none in B**. Shared model: `everySubinterval_sound`, `Semantics/HeapKnowledge.lean:2403` | **none in B** | The cited theorem is the soundness of a check over the pass's index facts (`everySubinterval`), with that language's conditions; it is not the rule over the paper's assertions (checked). |
| (Empty) — 963 | `Derivation.everyEmpty`, `D:456` | **narrower** | B additionally requires a density assertion establishing an array, uses a single-term bound, and admits scalar bodies only. The paper requires a defined array or view length and a nonpositive bound. |

**§5 — Entering the modality**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Definition 11, Support — 986 | `Supports`, `E:199` | **narrower** | The semantic support condition is instantiated at an arena assertion. Assertions of the paper outside that representation are excluded. |
| Definition 12, Respect — 1012 | **none in B**. Shared model: `Supported`, `Semantics/Footprints.lean:735`; `respects`, `respect_sound`, `Semantics/Support.lean:160,165` | **none in B** | No definition carries the paper's notion: it is expressible as `Supported S` of every action of $`\Phi`$ from a state of $`K`$. The declaration documented as "Respect (the note's Definition)", `respects`, is the sufficient pairwise check (each change of $`\Phi`$ within the support's change, or the regions disjoint by a query), which `respect_sound` proves sufficient (checked). |
| Theorem 13, Tolerant frame — 1034 | `tolerant_frame`, `E:212`; `Derivation.tolerantFrame`, `D:437` | **narrower** | Besides the assertion restriction, B requires the pairwise sufficient respect check and a sound separation query, rather than arbitrary semantic respect. The derivation constructor further restricts support and context evidence. |
| Definition 14, Supports of the atoms — 1049 | `SupportEvidence`, `E:811`; `.check`, `:822`; `.sound`, `:958` | **narrower** | There is no structural definition covering the whole displayed table. The certificates cover invariant assertions, linear facts, restricted density and scalar quantification, one-field literal equalities, initialization and literal view-element facts; they do not cover arbitrary contents predicates, optional equalities, arbitrary freshness regions, conjunction/disjunction supports, or the general modality-free support `all`. |
| Proposition 15, Axioms of the atoms — 1138 — summary | `RawDerivation.grow`, `.dense`, `.sep`, `.everyFrame`, `.init`, `.view`; `Derivation.rigidSubst` | **narrower** | The individual restrictions follow. |
| (Grow) — 1143 | `grow`, `Bridges/Grow.lean:27`; `RawDerivation.grow`, `D:646`; `SupportEvidence.lengths`, `E:813` | **equal** | For the displayed lower bound over a variable or constant, B establishes preservation under arbitrary value changes and spine growth, without separation. Literal lower bounds can use the linear-support rule directly. |
| (Dense) — 1144 | `RawDerivation.dense`, `D:647`, checked at `D:976` | **narrower** | The direct schema requires the bound to be a variable term. The paper also admits a literal bound directly; B’s density syntax has no literal-bound constructor. The cited fixed-number `dense_support` is outside B, `Semantics/FootprintProvenance.lean:88`. |
| (Sep) — 1145 | `RawDerivation.sep`, `D:639`, checked at `D:881` | **narrower** | The fact must be linear over variables and the one array length, and both separated paths must read arrays. The paper allows any qualifying atom and includes the null/undefined case for the other value. |
| (Every) — 1146 | `RawDerivation.everyFrame`, `D:640`, checked at `D:897` | **narrower** | B’s quantified premise additionally requires every index below the bound present, even when the body does not read an element. Its admitted scalar terms are the index, numeric element, element string length and scalar parameters. |
| (Init) — 1147 | `init_box`, `ModelRules.lean:82`; `init_path`, `:96`; `RawDerivation.init`, `D:641` | **narrower** | The atom is restricted to a linear fact over current terms. The paper quantifies over every atom whose heap reading is the displayed path length. |
| (Rigid) — 1148 | `Derivation.rigidSubst`, `D:447` | **narrower** | Capture avoidance and absence of the fresh witness from the effect are represented, but both the atom and its modal derivation must belong to B’s restricted assertion and derivation languages. |
| (View) — 1149 | `view_box`, `ModelRules.lean:45`; `RawDerivation.view`, `D:642`, checked at `D:930` | **narrower** | `view_box` covers linear facts over variables and view lengths; the derivation route covers assertions recognized by `invNode`. Neither states the schema for every qualifying paper atom. |

**§6 — Programs**

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Break — 1209 | **none in B** | **none in B** | B has no general break rule requiring the enclosing loop’s postcondition. |
| Return — 1210 | **none in B** | **none in B** | B has no displayed return rule substituting the returned atom into an arbitrary two-state function postcondition. |
| Throw — 1211 | **none in B** | **none in B** | `throw_nul_safe` (`Examples.lean:53`) treats one thrown value and a safety judgment, not this general triple. |
| Try — 1212 | `CommandSummary.handle_sound`, `CommandComposition.lean:193` | **narrower** | B composes encoded exit specifications through rebasing, inclusion and consequence evidence. The paper’s rule is over arbitrary one-state assertions and does not require those certificates. |
| Entry — 1249 | `CommandSummary.Sound`, `CommandSummaries.lean:54`; `ExitSpec.facts`, `:61`; `holds_iff_facts`, `:64` | **narrower** | These definitions provide the exit transition and encoded postconditions; no B theorem states the full strengthening by arbitrary entry assertion and its `old` form. The cited acceptance theorem `entry_sound` is outside B, `Semantics/StepRelations.lean:409`. |
| Frame — 1251 | `Derivation.frame`, `D:470` | **narrower** | B states modal elimination at a two-state with certified name transport. It does not state the complete two-exit command triple, and its framed assertion is restricted to the arena language. |
| Frame⁺ — 1253 | `Derivation.framePlus`, `D:487`; `box_of_rigid`, `CommandLoops.lean:89` | **narrower** | The derivation constructor requires recognized rigidity evidence and represented assertions. The semantic lemma gives the modal consequence of an action, not the complete command-triple rule. |
| Loop — 1255 | `LoopEvidence.prefix_sound`, `CommandLoops.lean:60`; `.loop_sound`, `:74`; `.frame_at_head`, `:97`; `frame_at_exit`, `:110` | **narrower** | B requires a separately supplied prefix summary, checked composition evidence and summaries of departures. It does not derive the displayed command rule from just the body triple, its effect and rigidity; break and return are not constructors of its runs. |
| Call — 1257 | `call_rule`, `ModelRules.lean:154` | **narrower** | B’s theorem is for a checked graph, its normal completion, slot renaming and a list of named caller facts. The two-exit signature theorem cited by the paper, `call_exits_exact`, is **outside B**, `Semantics/CallEffects.lean:541`. |
| Alloc, empty array — 1259 | `alloc_step`, `ModelRules.lean:177`; `alloc_post`, `:184` | **equal** | The allocated array has a fresh spine, length zero, and is apart from every pre-existing array. Freshness at the allocation heap length implies freshness at the enclosing invocation’s earlier mark. |
| Seq-Eff — 1261 | `seq_eff`, `ModelRules.lean:310`; `CommandSummary.seq_sound`, `CommandComposition.lean:163` | **narrower** | B requires the computed `rebaseAll` with `RebaseOk` and a successful `Footprint.le` check. The paper permits any rebasing satisfying its coverage relation and semantic effect inclusion. The general `Post.compose_rebases` is outside B, `Semantics/ExitComposition.lean:110`. |
| Fresh-Eff — 1263 | `fresh_eff`, `ModelRules.lean:320` | **equal** | For every location below the mark, the fresh spine’s entry is removable from the effect. The theorem does not remove effects on cells that spine lists. |
| If — 1308 | `CommandSummary.choice_sound`, `CommandComposition.lean:246`; `.join_sound`, `:262` | **narrower** | B combines arbitrary run relations and encoded summaries; the guarded branches must already be supplied as those relations. There is no rule deriving the branch conditions from the paper’s command syntax. |
| Seq — 1313 | `CommandSummary.seq_sound`, `CommandComposition.lean:163` | **narrower** | Composition requires encoded summaries and `ThenEvidence`, including rebasing and checked effect inclusion. It is not the general one-state triple rule as displayed. |
| Alloc, array literal — 1349 | **none in B**. Cited outside B: `literalArrayAtoms_holds`, `Programs/IndexWrites.lean:175` | **none in B** | B’s empty-array theorem does not establish arbitrary literal contents and density. The paper itself marks those parts conjectural. |
| Alloc, object literal — 1350 | **none in B** | **none in B** | `alloc_state` (`KindsModelRules.lean:508`) establishes allocation/state properties, not the displayed freshness-and-field-equalities postcondition. |
| Definition 16, Independence of the world — 1379 | **none in B**. Shared model: `IndependentFrom`, `Semantics/ExitWorlds.lean:179` | **none in B** | The shared model states it equally: equal truth at any two exit states admissible from the entry with the same heap and budget (checked). |
| Conj — 1397 | **none in B**. Shared model: `SafePostExcV.cross_independent`, `Semantics/ExitWorlds.lean:188`; `PromiseWith.conj`, `Semantics/CallEffects.lean:403` | **none in B** | `cross_independent` states it with a premise the rule lacks, `CrossCompatUpTo` of the two derivations' result families; `PromiseWith.conj` is its instance for native contracts whose second exit reads only the heap (checked). |
| Definition 17, Rebasing — 1412 | **none in B**. Shared model: `Rebases`, `Semantics/ExitComposition.lean:77` | **none in B** | `Rebases` states the coverage relation with the absorption by $`\Phi`$ at `any` explicit, and holds no evidence $`\mathit{ev}`$: the paths reading each named value in both heaps are premises of `rebase_sound` for the computed rebasing (checked). |
| Example 18, Freshness bounds effects, not facts — 1447 | **none in B** | **none in B** | `fresh_eff` proves the effect ingredient. `apart_not_kept_fresh` (`ModelRules.lean:251`) refutes preservation of apartness, not this shrink-and-read example or its length fact. |
| Proposition 19, Reliance — 1459 | **none in B**. Shared model: `rely_chain`, `Semantics/FootprintNatives.lean:473` | **none in B** | `rely_chain` states it for the facts of `FactKind`, under a stability check of each step's effect for the fact's support in place of a rigid bound with $`\Box_\Phi F`$ at the start (checked); the paper's status tag records this scope. |
| Field-Read — 1478 | **none in B**. Shared model: `ReadGave`, `Semantics/HeapFacts.lean:13` | **none in B** | `ReadGave` defines a read's result (the field's location, or `undefined` for an absent key with no prototype); no statement gives the rule's postcondition $`x.f \doteq y`$ and its empty effect (checked). |
| Field-Write — 1479 | **none in B**. Cited outside B: `fieldWriteFrame`, `Programs/ExpressionEffects.lean:112`; `FieldWritten`, `:155`; `fieldWriteStep_sound`, `:229` | **none in B** | B proves preservation consequences of some writes, not the general exact field-write rule. |
| Elem-Read — 1480 | **none in B** | **none in B** | B’s element atom denotes a typed-array element, not an array element or hole. The paper marks the ordinary element-read contract assumed. |
| Arr-Length — 1481 | **none in B** | **none in B** | No B constructor states this primitive read’s equality and empty effect. The paragraph supplies no named Lean citation for it. |
| Test — 1482 | **none in B** | **none in B** | `guard_safe` (`ModelLoop.lean:351`) treats the example’s numeric comparison. It does not state all the paper’s comparison, nullish, negation, conjunction and disjunction cases. |
| Fun — 1547 | `CommandSummary.signature_holds`, `CommandBodies.lean:86`; `.signature_holds_below`, `:106` | **narrower** | B transports a supplied sound body summary to a supplied signature at call positions. It does not establish the recursive function rule, default `undefined` return, and return obligations from the displayed body premises. Cited outside B: `codeObligations_sound`, `Programs/CodeConditions.lean:218`. |
| Write-In — 1572 | `Derivation.writeIn`, `D:583`; `lengthsKept_of_run`, `Bridges/ParityArithmeticBridges.lean:189` | **narrower** | The conclusion concerns an array held in corresponding entry/exit slots. The paper states preservation of the length read through every path; B does not package the preservation of those path reads into this rule. |
| Write-End — 1573 | `Derivation.writeEnd`, `D:589`; `boundedWrite_of_run`, `Bridges/ParityArithmeticBridges.lean:209` | **equal** | Given the bounded-write operation postcondition and the displayed end-index premises, B concludes exactly the length increase by one. The current paper does not put element equality or density extension in this rule. |
| Push — 1574 | `Derivation.pushPost`, `D:595` | **narrower** | B concludes the length increase, generalized to several arguments. It does not conclude the appended-element atom or preservation of every earlier element, both present in the current paper’s Push rule. |
| Write-Kept — 1606 | **none in B**. Cited outside B: `keptCells_holds`, `Programs/HeapExpressionRules.lean:1404` | **none in B** | No B rule preserves arbitrary membership of the possibly aliased field using membership of the written value. |
| Push-Every — 1607 | **none in B**. Cited outside B: `every_appended`, `Programs/PromiseCalls.lean:2375`; `appendKept_holds`, `:2485` | **none in B** | B has framing of quantified facts, not their extension by a pushed value. |
| View-Every — 1608 | **none in B**. Cited outside B: `every_written`, `Programs/PromiseCalls.lean:2707`; `every_written_prefix`, `:2780`; `writeKept_holds`, `:2853` | **none in B** | B’s quantified assertion is over arrays. No B rule preserves or extends a typed-array prefix using the converted written value. |
| Add — 1648 | `Derivation.arith` at `ArithmeticRules.add`, `D:551`; `rules_sound` | **equal** | The paper's row is generated from the rule: safe operands and a safe mathematical sum give the exact sum. |
| Sub — 1648 | `Derivation.arith` at `ArithmeticRules.sub`, `D:551`; `rules_sound` | **equal** | The paper's row is generated from the rule: safe operands and a safe mathematical difference give the exact difference. |
| Scale — 1648 | `Derivation.arith` at `ArithmeticRules.scale`, `D:551`; `rules_sound` | **equal** | The paper's row is generated from the rule: a constant factor and a safe mathematical product; `Derivation.commute` applies it to `c * a`. |
| Shr — 1652 | `Derivation.arith` at `ArithmeticRules.shr`, `D:551`; `ruleConclusion`, `:218`; `rules_sound`, `Semantics/ArithmeticRules.lean` | **equal** | The paper's row is generated from the rule B applies: an operand in the signed 32-bit range, the count read modulo 32 and both quotient bounds. A constant may be a literal or a value proved constant. |
| Mask — 1653 | `Derivation.arith` at `ArithmeticRules.maskRange` and `maskBound`, `D:551`; `rules_sound` | **equal** | The paper's two triples are generated from the two rules: the range for any number and a mask in $`[0, 2^{31})`$, held in a variable or a literal, and the bound $`y\le b`$ by the same non-negative mask $`b`$ of any number $`x`$. `Derivation.commute`, `D:545`, applies them to `m & x`. |
| Shl — 1654 | `Derivation.arith` at `ArithmeticRules.shl`, `D:551`; `rules_sound` | **equal** | The paper's row is generated from the rule: the exact product where it lies in the signed 32-bit range. |
| Or — 1655 | `Derivation.arith` at `ArithmeticRules.bitOr`, `D:551`; `rules_sound` | **equal** | The paper's row is generated from the rule: both operands in $`[0, 2^{31})`$ bound the result below by each and above by their sum. |
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
| Definition 21, Checked transfer — 1793 | `checkScoped`, `D:2049` | **narrower** | B checks supplied premises and a supplied goal in its restricted language. It has no definition assembling exactly the node’s entry knowledge, exit transition, postcondition, branch condition and renamed target assertion into the paper’s `Check`. |
| Theorem 22, Transfer — 1804 | `checkScoped_sound`, `D:2064`; `transfer`, `Bridges/Transfer.lean:37` | **narrower** | The first proves semantic consequence once all premises hold. The second treats class effects and transported `IndexFact` lists, with target obligations supplied separately; it does not connect arbitrary regional exit effects and arbitrary paper knowledge to the stated run conclusion. Cited `sat_subst` and `graph_safe` are outside B, `Semantics/AssertionScopes.lean:627` and `Programs/SinglePass/GraphSafety.lean:329`. |
| Definition 23, Derivations — 1812 | `Derivation`, `D:342`; `RawDerivation`, `:605`; `Derivation.sound`, `:1679` | **narrower** | Besides the assertion restrictions, B lacks general quantified-postcondition instantiation and implication elimination, general element substitution, the complete contradiction schemas and the general Prefix rule. Its arithmetic rule requires a checked certificate, and its modal introduction uses the finite evidence forms described above. |
| Example 24, Example 1 in full — 1903 | `loopGraph`, `ModelLoop.lean:444`; `HeadAt`, `:454`; `loop_safe`, `:601` | **different** | B omits the output-length check and throw, does not put $`j\le\mathit{to}`$ in its head assertion, and permits sparse source arrays. It proves safety of that different graph, not the displayed annotation and all eight obligations. |

**§8 — The patterns**

These are repeated applications, rather than additional numbered definitions or primitive rules. They are listed for completeness and excluded from the main count.

| Paper item | B’s statement | Relation | Difference |
|---|---|---|---|
| Lower bound under aliasing — 1948 | `grow`, `Bridges/Grow.lean:27` | **equal** | The displayed lower-bound entailment has no separation premise. |
| Bound across a rewriting call — 1949 | `RawDerivation.sep`, `D:639`; `Derivation.rigidSubst`, `:447` | **narrower** | Both arrays and the rigid substitution must meet B’s restricted representation and certificates. |
| Fresh array spine — 1950 | `fresh_eff`, `ModelRules.lean:320`; `alloc_post`, `:184` | **equal** | The fresh spine contributes no change below the mark, and empty allocation establishes apartness from older arrays. |
| Write-once cache — 1951 | `tolerant_frame`, `E:212`; `init_box`, `ModelRules.lean:82` | **narrower** | The atom and its support must be among B’s represented facts and accepted evidence; there is no rule for every atom tolerating initialization. |
| Reliance during callbacks — 1952 | `RawDerivation.dense`, `D:647`; `reliance_at_prefix`, `CommandLoops.lean:124` | **narrower** | B supplies the density frame and a consequence of an already composed prefix bound, not the callback-chain proposition. |
| Quantified fact across a write — 1953 | `RawDerivation.everyFrame`, `D:640` | **narrower** | B additionally requires presence at every quantified index, including when the body itself would not require it. |
| Structures built in step — 1954 | `Derivation.pushPost`, `D:595`; `RawDerivation.sep`, `:639` | **narrower** | The length ingredients exist, but there is no B command triple combining the actual push with preservation of the other array’s length. |
| Separation where a value exists — 1955 | `Derivation.guardCases`, `D:369`; `RawDerivation.sep`, `:639` | **narrower** | The path guard must be recognized invariant, and separation is only between arrays. The displayed general guarded path case is not represented as stated. |
| Fact through a field — 1956 | `grow_path`, `Bridges/Grow.lean:50`; `grow_path_typed`, `Bridges/ModelTyped.lean:150` | **narrower** | The typed bridge requires its particular stable-path and array-type evidence; the derivation route also requires certified substitution in B’s language. |
| Typed-array length — 1957 | `view_box`, `ModelRules.lean:45` | **equal** | This particular linear fact over a variable and descriptor length is within the theorem’s scope. |
| Index from a shift or mask — 1971 | `Derivation.arith` at `shr`, `maskRange` and `maskBound`, `D:551`; `Derivation.linear` | **equal** | The pattern's facts, under its ranges $`0\le c<2^{31}`$, $`0\le d<32`$, $`0\le m<2^{31}`$, are the rules' conclusions, and $`0\le y`$ after the shift follows from them by a linear certificate. |
| Array facts across a typed-array write — 1959 | `SupportEvidence.everyCells`, `E:815`; `Derivation.tolerantFrame`, `D:437` | **narrower** | The quantified fact has B’s additional presence requirement and restricted scalar-body interpretation. |
| Fact at a handler — 1960 | `Derivation.frame`, `D:470`; `CommandSummary.handle_sound`, `CommandComposition.lean:193` | **narrower** | The modal consequence exists for encoded facts; no general command rule connects every exceptional exit to its handler with arbitrary paper assertions. |

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
| 14 | 36 | 0 | 2 | 26 | 13 | 91 |

Of the rows with no statement in B, the shared model states Definitions 6 and 16 equally, and Theorem 7 from a safety premise; the others are recorded in their rows.
