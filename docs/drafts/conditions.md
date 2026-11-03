# Draft: conditions as short-circuit dispatch

A condition in a test position is lowered by one translation, the standard
short-circuit translation of a Boolean condition into branches
([Aho et al. 2006](../REFERENCES.md#aho-lam-sethi-and-ullman-2006)).

## The existing mechanism this extends

An expression's evaluation is an execution plan (`ExpressionPlan.lean`,
[logical operators](../SOURCE-ELABORATION.md#logical-operators)): a tree of
atoms, sequences and `choose` nodes. A `choose` saves an operand's value and
dispatches on a test of it (`truthy`, `nullish`, `defined`); each arm is a
plan, and the plan's consumer is compiled once per path
(`LoweringExecution.executePlanTail`). A `choose` on a value whose test
refines a predicate is *correlated*: each arm is reached by the predicate's
own dispatch (`LoweringAtoms.compileConditionAtom`), in the context the
answer leaves (`conditionContext`), and rebinds the outcome to `true` or
`false`. A tested value whose type answers the test one way takes that arm
alone (`Answers`).

A condition is lowered by `buildCondition`, then `compileCondition` tests the
plan's value ([conditions read for truthiness](../SOURCE-ELABORATION.md#conditions-read-for-truthiness),
[negated operands](../SOURCE-ELABORATION.md#negated-operands)). Today
`buildCondition` (`truthOf`) evaluates a condition built of tests (`testForm`)
as a value and re-dispatches its predicate, and dispatches on truth only
where a left operand is no test, after regrouping `(a op b) op c`
(`dispatchedTest`, `residual`) and with a negated non-test operand decided by
a literal the producer claims at the `!` (`negationMark`).

This draft replaces that case analysis by the translation below, in the same
plan language, with one added plan operation: the outcome literal.

## The translation

Write $`\mathcal{C}[\![e]\!](t, f)`$ for the plan of $`e`$ in a test position
that continues with $`t`$ where $`e`$ is truthy and with $`f`$ where it is
falsy, and $`\mathsf{T}`$, $`\mathsf{F}`$ for the outcome literals `true` and
`false`:

```math
\begin{aligned}
\mathcal{C}[\![a\mathbin{\&\&}b]\!](t,f) &= \mathcal{C}[\![a]\!](\mathcal{C}[\![b]\!](t,f),\ f)\\
\mathcal{C}[\![a\mathbin{\Vert}b]\!](t,f) &= \mathcal{C}[\![a]\!](t,\ \mathcal{C}[\![b]\!](t,f))\\
\mathcal{C}[\![!a]\!](t,f) &= \mathcal{C}[\![a]\!](f,\ t)\\
\mathcal{C}[\![c\ ?\ a : b]\!](t,f) &= \mathcal{C}[\![c]\!](\mathcal{C}[\![a]\!](t,f),\ \mathcal{C}[\![b]\!](t,f))\\
\mathcal{C}[\![(x,\ a)]\!](t,f) &= x;\ \mathcal{C}[\![a]\!](t,f)\\
\mathcal{C}[\![e]\!](t,f) &= \mathsf{let}\ v=e\ \mathsf{in}\ \mathsf{if}\ \mathsf{truthy}(v)\ \mathsf{then}\ t\ \mathsf{else}\ f
\quad\text{(any other } e\text{)}
\end{aligned}
```

and a statement's condition $`e`$ is
$`\mathcal{C}[\![e]\!](\mathsf{T},\mathsf{F})`$; a conditional expression
$`c\ ?\ a : b`$ in a value position is $`\mathcal{C}[\![c]\!](a, b)`$, so an
arm's first reads are checked by the edge of the leaf dispatch that reaches
it.
Parentheses are the parser's grouping and add no case. In the last line,
$`e`$'s plan is its value plan (`build`), observed at its span as today, and
the dispatch is a `choose` on truthiness with the role `truth`: correlated
where its predicate refines, a plain truthiness split otherwise. Its value is
never read but by the dispatch, whose arms are $`t`$ and $`f`$.

The test positions are the conditions of `if`, `while`, `do`, `for` and `?:`
(as a statement's condition and as a value's), and every operand the
translation reaches: the operands of `&&` and `||`, the operand of `!`, a
nested `?:`'s three operands and a comma's right operand. An operator in a
value position keeps its value plan (`logical`): $`a\mathbin{\&\&}b`$ there
yields the selected operand, and `!a` the negation of $`a`$'s value.

$`\mathsf{T}`$ and $`\mathsf{F}`$ are a plan operation of their own,
`outcome`, at the empty span where the condition starts, which no source
expression and no claim has. Its type is `[true]` or `[false]`, its node the
literal's term, its effect none; the plan's JSON carries it as the kind
`outcome` with its Boolean, which the producer reads as the Boolean result it
already handles (`execution.ml`, `execution_analysis.ml`'s `outcomes`).
Where an outcome is a dispatch's arm, a statement's condition sends the
dispatch's edge to that outcome's destination itself (`executePlanTail`'s
`exit`), so the destination's entry claims are checked against what the
leaf's answer establishes (a field's truthiness refining its object's arms,
a key test, a path witness), as the predicate's dispatch does today.

**Size.** The plan is a tree. Its construction and its JSON are linear in
the condition but where a continuation occurs under two exits:
$`\mathcal{C}[\![(a\mathbin{\Vert}b)\mathbin{\&\&}c]\!]`$ holds
$`\mathcal{C}[\![c]\!]`$ under both exits of $`a\mathbin{\Vert}b`$, so $`k`$
nested disjunctions in conjunctions' left operands give $`2^k`$ copies. The
graph is compiled per path, as `executePlanTail` compiles a `choose`'s
continuation once per path of its evaluated operand today; its size is the
number of paths through the condition, which the value plan of the same
condition already reaches. A scaling case measures a chain of such
conjunctions.

**A known Boolean.** A leaf whose value plan is a read of an immutable
binding (a `const` or a parameter never written, storage `value`, resolved
through the scope by the name the parser gives it) takes one arm where the
binding's slot type in the leaf's context answers the test one way, as a
tested value whose claim answers it does. The slot type is the node's
context, which the graph checker establishes on every incoming edge; the
read's own claim is still observed at its span. In
`(c && x) || (!c && y)`, where `x` failed with `c` true, the leaf `c` of `!c`
holds `[true]`, so only the arm where `!c` is false is built. A mutable
binding, a cell or a slot, is never pruned on.

**Claims the translation does not consume.** A condition in a test position
evaluates no value of an operator it decomposes: `&&`, `||`, `!`, `?:` and a
comma there yield no value any program reads. Their expressions' claims stay
admissible sites (`Claims.Sites`) and are not obligations: the lowering
reads none, so the graph checks none. Every operand the translation reaches
as a leaf keeps its own observation, and an operator in a value position
keeps its own.

## What it replaces

- `truthOf`'s case analysis (`logicalTruth`, the test-form and negation
  special cases) and its regrouping: $`\mathcal{C}`$ needs no grouping,
  since $`\mathcal{C}[\![(a\ op\ b)\ op\ c]\!]`$ and
  $`\mathcal{C}[\![a\ op\ (b\ op\ c)]\!]`$ are the same plan.
- `dispatchedTest`, `leftTestForm`, `testForm` and `residual`
  (`ExpressionPlan`), the literal at the `!` (`negationMark`) with its
  claim site (`Claims.Sites`) and the producer's claim of it
  (`expression_values.ml`).
- The pending patch's `testLeft` and `knownCondition`: the first is the
  $`!`$ and $`\Vert`$ cases, the second the known-Boolean rule above, stated
  on the tested value's context type rather than on a variable's syntax.
- In `compileCondition`, the re-dispatch of the condition's predicate
  (`compileConditionAtom` on the whole condition): every outcome is a
  dispatch's arm, sent to its destination. `compileConditionAtom` stays the leaf dispatch, with `readGuard`,
  `equalitySplit`, the witness handling and `conditionContext`; its `.logical`
  and `.not` cases stay for predicates `executionPredicate` rebuilds from a
  value-position plan (a correlated `choose` of `a && b` as a value, a value
  `!a`) and for a guard's Boolean return.

## Why it is sound

The lowering is unproved; this is the review argument that it preserves
JavaScript's evaluation ([ECMA-262](../REFERENCES.md#ecma-262), the
runtime semantics of `LogicalANDExpression`, `LogicalORExpression`,
`UnaryExpression : ! UnaryExpression`, `ConditionalExpression`,
`Expression : Expression , AssignmentExpression`, and `if`/loop statements,
each of which calls `ToBoolean` on the condition's value).

Claim, by induction on $`e`$: running $`\mathcal{C}[\![e]\!](t,f)`$
evaluates the same operands, in the same order, once each, as JavaScript
evaluates $`e`$, then runs $`t`$ exactly where $`\mathsf{ToBoolean}(e)`$ is
true and $`f`$ where it is false.

- $`a\mathbin{\&\&}b`$: JavaScript evaluates $`a`$; where it is falsy the
  value is $`a`$'s, falsy, and $`b`$ is not evaluated; otherwise the value is
  $`b`$'s. The plan runs $`a`$, then $`f`$ where $`a`$ is falsy, and
  $`\mathcal{C}[\![b]\!](t,f)`$ where it is truthy.
- $`a\mathbin{\Vert}b`$: symmetric.
- $`!a`$: its value is `true` exactly where $`a`$ is falsy.
- $`c\ ?\ a : b`$: $`c`$, then exactly one of $`a`$, $`b`$ by $`c`$'s truth.
- $`(x,\ a)`$: $`x`$ for its effects, then $`a`$'s value.
- Any other $`e`$: evaluated once by its value plan, its truth tested.

An exception raised by an operand leaves the plan where it leaves
JavaScript's evaluation, through the operand's own atom. The outcome
literals carry no source obligation: the condition's value is read by
nothing but its test, so no value the program reads is replaced.

A dropped arm is one no run takes: the tested value's checked type (its
claim, or an immutable binding's context type, which every incoming edge
establishes) admits only the other answer.

## What changes in the proofs

Nothing. The plan, its lowering and the outcome literal's node are inside
the source extraction, which no theorem covers ([trust surface](../DESIGN.md#trust-surface)); the graph each produces is
checked as any graph is, the literal by the literal rule. The design changes
the trusted extraction's row in DESIGN.md: the regrouping and the negation
mark go, the short-circuit translation comes in.

## Cases and controls

Positive, each with a negative twin unsafe under Node: the shapes of the
three patches (a test then a non-test, a negated non-test, a negated test
in a disjunction, `blocker-compiler-api-optional-path-join`), nested
negations, mixed `&&`/`||`, `?:` in a condition, a guard call under `!` on
either side, an optional-chain length test, and a known Boolean re-tested
(`(c && x) || (!c && y)`); evaluation order and single evaluation with
writes, a throwing call and a comma's effect, a loop's condition retested
after `continue`, a value-position selected operand, and leaf equality and
property narrowing. Controls in `pipeline/test.mts`, each through evidence
production and checking: a statement entry claim forged to state what only
a pruned edge would carry, contradicting a reachable incoming edge, is
refused; and a known Boolean's entry claim forged to a literal its edges do
not establish, which would prune a reachable arm, is refused at that edge.
The existing controls forging a negation's claim inside a condition are
reconciled with the claim policy above: a forged claim of the synthetic `!`
literal has no site, and a negation's own claim is forged where the
negation is a value.
