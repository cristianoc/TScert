# The cost of a walk: one comparison, one name per value, live facts only

A walk of the single pass holds, at each node, the facts of its state; the
cost of a unit is the sum over its nodes. On `tools/type-term.mts`
(`typeTerm`), that sum reaches 4.75 GiB, above the census's 4 GiB stage
limit, and the four files importing it lose their module interfaces. This
draft states, for one small program, where the facts come from, and five
changes, each a cause on its own: the lowering of a comparison, the names a
walk keeps, the one form a fact over a read field takes, the facts a store
keeps, and how stores are held. Each change has its test and its
measurement.

## The example

```ts
export enum Kind { K0, K1, K2 }
export type Tree = { kind: Kind; text: string; children: Tree[] };
export function sameTrees(x: Tree, y: Tree): boolean {
  const same = (a: Tree, b: Tree): boolean => {
    if (a.kind !== b.kind) return false;
    …
  };
  return same(x, y);
}
```

`TSCERT_DUMP=1` ([the request protocol](../REQUEST-PROTOCOL.md)) prints the
closure's walk. Its first nodes, in execution order (`n1` is `a`, `n2` is
`b`, `tK` the temporary holding the name `nK`):

```
78  t12 = a.kind
77  t13 = b.kind
76  t14 = (t12 === t13)
75  t15 = (t14 ? false : true)      a.kind !== b.kind
74  t16 = a.kind                    read again
73  t17 = b.kind                    read again
72  t18 = (t16 === t17)             compared again, the Boolean dropped
71  t19 = b.kind                    read a third time
70  test t19 == 0      yes → a.kind == 0 ?     no → 69
69  t20 = b.kind
68  test t20 == 1      …   then == 2 and == -0
```

The facts the nodes add (the dump's `+` lines):

```
75  [if n15] n1.kind − n2.kind ≠ 0   [if n15] n12 − n13 ≠ 0   [if n15] n1.kind − n13 ≠ 0
    [unless n15] n1.kind − n2.kind ≤ 0   [unless n15] −n1.kind + n2.kind ≤ 0   … (12)
73  [if n15] n1.kind − n17 ≠ 0   [if n15] n12 − n17 ≠ 0   [if n15] n16 − n17 ≠ 0   … (12)
70  n19 − n19 ≤ 0   −n2.kind + n2.kind ≤ 0   int(n19)
69  n20 ≠ 0   [if n15] n12 − n20 ≠ 0   [unless n15] ±(n12 − n20) ≤ 0   … (10)
```

## Measurement

The measurement runs the example at 8 to 128 members through the file worker: wall time, peak resident
memory, and the facts the closure's walk holds, summed over its nodes (each
node's state after its step). Beside it: `typeTerm` alone on the v0.94
corpus (time and peak memory at an 8 GiB stage limit), the touched case
patterns, and the census of the v0.94 corpus.

Baseline (single-pass at `7494763`, 2026-11-24, this machine):

| Members | Time | Peak memory | Nodes | Facts held |
| --- | --- | --- | --- | --- |
| 8 | 0.19 s | 35 MB | 104 | 5,063 |
| 16 | 0.35 s | 37 MB | 136 | 9,511 |
| 32 | 0.96 s | 47 MB | 200 | 23,795 |
| 64 | 3.54 s | 90 MB | 328 | 73,873 |
| 128 | 17.10 s | 322 MB | 584 | 255,889 |

`typeTerm`: 476 s, 4.75 GiB peak. Census: 526 of 686 functions shallow
verified, 28 min.

## 1. A comparison of two values is one comparison

A branch on `l === r` evaluates each operand once, in source order, and
branches on the comparison's own answer. The comparison is a membership
test whose tags come from the other operand's type: each edge narrows the
operands by the membership test's yields, and states on the cells the
operands were read from what that answer leaves of their contents. Claims
below are labelled **proved** (with the proof's location), **cited** (with
its source and scope) or **conjectured**.

### The existing mechanism this extends

In the pass, an edge changes a slot's type only through the node's yields,
and a cell's contents only through the edge's observation. A yield
`{conditional, onFalse, target, type, evidence}` (`PromiseCalls.Yield`,
`Programs/PromiseCalls.lean:33`) states that, where the node's result is
`true` (`conditional`) or `false` (`onFalse`), the value of slot `target` is
in `type` (`YieldsOk`, line 47). Read from the code:

```
nodeYields (CertificateProducer.lean:1589)       -- untrusted: proposes
  term = var i                       → the implications testing i
  term = ite (test t (var i)) tru fls → tagSlice of slot i, fieldSlice of the
                                        objects a read link names, and memberYields [t] i [false]
  term = memberOn ts (var i)         → memberYields ts i [true, false]
  otherwise                          → []

checkedYields (SinglePass.lean:887)              -- trusted: filters
  keep y  iff  yieldFollows G images Γ xs links t y

yieldFollows (PromiseCalls.lean:705)
  memberFollows t y                               -- t = memberOn ts (var i): memberYield
  || match t with
     | var i                         → y.conditional ∧ some implication on i states y
     | ite (test t (var i)) tru fls  → y.conditional ∧ (y.target = i ∧ observed i t true
                                                         ∨ fieldYield G images Γ links y i t true)
     | ite (test t (var i)) fls tru  → the same at false
     | _                             → false
  observed i t q = checkObservedSubUsing G images Γ[i] y.type (.tag t q) p   -- ObservedSub:
      tagSlice, tagMember (familyMember, BranchRefinement.lean:1335), meetSlice, setSlice, …

memberYield G Γ links y ts i (line 677)
  y.conditional = ¬y.onFalse
  ∧ ( y.target = i            ∧ memberSlotSlice G Γ[i] ts (¬y.onFalse) ⊑ y.type
    ∨ some link {cell := y.target, field := f, value := i}
                              ∧ memberFieldSlice G Γ[y.target] f ts (¬y.onFalse) ⊑ y.type )

refinedContext (SinglePass.lean:2809)
  branchBind, true arm  → the context refined by the conditional yields
  branchBind, false arm → refined by the onFalse yields
  bind                  → unconditional yields; conditional ones become
                          implications on the pushed result (edgeImplications, PromiseCalls.lean:311)

edgeKnowledge (CertificateProducer.lean:1575), checked at ControlFlow.lean:448
  tagBind t   → observeTyped … 0 (.tag t q)    -- observeTag: the slot's value set met with
                                                -- ofTag t q, copied to the cells its read
                                                -- links name (linkFacts, HeapKnowledge.lean:3310)
  branchBind  → observeTyped … 0 (.boolean q)   -- the result alone
```

`memberSlotSlice` is the slice of the membership test
([PROGRAM-TYPING.md, "A membership test"](../PROGRAM-TYPING.md#a-membership-test)):

```math
\mathsf{slice}_{\mathsf{true}}(A, S) = \bigcup_{t\in S}\sigma(A, t, \mathsf{true})
\qquad
\mathsf{slice}_{\mathsf{false}}(A, S) = \rho_S\big(\sigma(\dots\sigma(A, t_1, \mathsf{false})\dots, t_n, \mathsf{false})\big)
```

with $`\sigma`$ = `BranchRefinement.tagSlice` (`BranchRefinement.lean:56`),
a filter of $`A`$'s labels by `tagClause` (`TypingBasics.lean:1389`). Its
soundness is `memberYield_sound` (`PromiseCalls.lean:848`), whose only
premise about the run is

```math
(u = \mathsf{true}\land \exists t\in S.\ \mathsf{tagHoldsIn}_h(t, \rho_i)) \lor
(u = \mathsf{false}\land \forall t\in S.\ \neg\mathsf{tagHoldsIn}_h(t, \rho_i))
```

**proved** there; `member_run` (line 791) discharges it for a term
`memberOn ts (var i)`.

Three things this mechanism does not do. A strict comparison
`arith .eq (var i) (var j)` matches no arm of `yieldFollows`, so the
checker keeps none of its yields; for safe-integer operands the step adds
only `equalAtoms` (`IndexWrites.lean:799`), linear facts that narrow no
type. The true side of `memberYield` is weaker than the single-tag rule: it
checks plain subtyping of $`\mathsf{slice}_{\mathsf{true}}`$, and
$`\sigma`$ keeps a family (`str`, `num`) or `top` whole, where `observed`
narrows `string` under `strEq "a"` to `"a"` through `familyMember`. And a
`branchBind` edge observes only its Boolean, so a membership answer states
nothing on the cells its operand was read from.

The narrowing of `x === y` comes from the lowering instead. Before it, the
front end (`comparisonsExpr`, `Lowering/Types.lean:632`) turns an equality
with a singleton operand into `singletonTest`, a tag test of the other
operand. Then:

```
compileConditionAtom (Source/Lowering/Atoms.lean:1214), cond = l === r:
  equalitySplit (Control.lean:315): l or r is a name or a field of a name
      whose type's members are each a singleton (singletonTag, Lowering/Types.lean:613)
    → evaluate l === r, drop its Boolean               (its obligations)
      dispatch (Atoms.lean:1255): for each singleton tag k of the split operand s:
        re-read s; test s == k  -- tagBind: yields, observeTag on the read's cell
          yes: re-read the other operand o; test o == k  (yes → yes, no → no)
          no:  next k
      after the last k → no
  savedSplit (Control.lean:342): l a name, r an expression with effects
      whose type's members are singletons
    → evaluate r once into a slot; dispatch on it as above
  otherwise → simple: evaluate l === r, then branch on its Boolean (emitBranch)
```

A correlated `choose` (`Execution.lean:1069`), the statement condition
`if (p)` whose predicate `p` is a Boolean read without effect, evaluates `p`
first and then dispatches `p` again through `compileConditionAtom`, whose
contract reads that evaluation (`Atoms.lean:1205`).

### The example as it is

`if (a.kind !== b.kind) return false`, with `Kind` = `K0 | K1 | K2` = 0, 1,
2. TScert's literal type `0` is both zeros (`literalLabels`,
`Source/Equations/Interning.lean:471`), so `Kind` has four number labels,
0, 1, 2 and −0. The closure's walk (`dump-before.txt`, 84 nodes) lowers the
condition to nodes 78 to 56, in execution order:

```
78  t12 = a.kind                       choose: evaluate
77  t13 = b.kind
76  t14 = (t12 === t13)
75  t15 = (t14 ? false : true)          !==
74  t16 = a.kind                       compileConditionAtom → .not → .arith .eq:
73  t17 = b.kind                         equalitySplit: split b.kind, other a.kind
72  t18 = (t16 === t17)  dropped         the comparison's obligations
71  t19 = b.kind         70  test t19 == 0   yes → 57   no → 69
69  t20 = b.kind         68  test t20 == 1   yes → 59   no → 67
67  …                    66  test     == 2   yes → 61   no → 65
65  …                    64  test     == −0  yes → 63   no → return false
57  a.kind  56  test == 0   yes → after the if    no → return false
59, 58 / 61, 60 / 63, 62: the same for 1, 2 and −0
```

Twenty-three nodes; per member, two reads and two tests. Each read is a
fresh name related by `equalAtoms` and links to every earlier name of the
other value under both values of the pending `t15`. At 64 members the walk
holds 73,873 facts in 3.54 s; with the split turned off
(`dump-nosplit.txt`: nodes 63 to 56, the evaluation, the comparison again
and a branch on its Boolean) it holds 6,954 in 0.20 s (**cited**: the
implementer's measurement on the enum repro, single-pass at `7494763`).
With the split off, `equality-several-singletons`, `literal-equality` and
`module-value-equality` fail: nothing narrows.

### The change

**The tags of a type.** Each clause $`c`$ determines tags $`\tau(c)`$, one
of which holds of every value strictly equal to a value of $`c`$. It is a
`match` over the 25 constructors of `Clause`
(`Types/PositiveNormalization.lean`), with no wildcard, so Lean checks it
exhaustive:

```lean
def equalityTagsOf : Clause α → Option (List Tag)
  | .nul => some [.isNul]
  | .undef => some [.isUndef]
  | .bool => some [.isBool]
  | .boolLit b => some [.boolEq b]
  | .num => some [.isNum]
  | .int => some [.isNum]
  | .numLit k => some [.numEq k]
  | .numIn S => some (S.map .numEq)
  | .str => some [.isStr]
  | .strLit s => some [.strEq s]
  | .strIn S => some (S.map .strEq)
  | .bigint => some [.isBigint]
  | .bigintLit i => some [.bigintEq i]
  | .symbol => some [.isSymbol]
  | .symbolLit _ => some [.isSymbol]
  -- Strict equality compares two objects by identity alone: the other
  -- operand is some object, of either call code.
  | .refs .. => some [.isRef, .isFun]
  | .dict .. => some [.isRef, .isFun]
  | .arrs .. => some [.isRef, .isFun]
  | .callable .. => some [.isRef, .isFun]
  | .ctors .. => some [.isRef, .isFun]
  | .view .. => some [.isRef, .isFun]
  -- No value is strictly equal to a spine (`strictEquals` answers `false`
  -- or nothing).
  | .list .. => some []
  | .pack .. => some []
  -- Every value: no tag set bounds what equals one.
  | .top => none
  | .source => none

def equalityTags (G : NormalGraph ι) (B : Ty ι) : Option (List Tag) :=
  if G.plainTy B then
    ((expand G B).mapM equalityTagsOf).map fun tss => dedupNumberEqual tss.flatten
  else none
```

`isRef` or `isFun` holds of every object, one per call code (`tagHolds`,
`Calculus.lean:1551`; `CallCode`'s four constructors, line 321).
`dedupNumberEqual` keeps one `numEq` per class of `numberEqual`:
`numEq(+0)` and `numEq(−0)` have the same holders, since `numberEqual`
ignores the sign of zero (`Calculus.lean:759`), so `Kind`'s tags are three.

`equalityTags` is `none` unless every label of $`B`$ is a clause row
(`plainTy`). `expand` returns `[]` for a type with a parameter or scheme
row (`PositiveRules.lean:58`); read as tags, `[]` would make the true slice
empty and the true edge unreachable, which is unsound: in
`function f<T>(x: "a" | "b", y: T)`, `x === y` holds at `f("a", "a")`.

**The rule.** A node whose term is $`x_i \equiv x_j`$
(`arith .eq (var i) (var j)`), with $`B = \Gamma(j)`$, is a membership test
of $`x_i`$ against $`\mathsf{tags}(B)`$ where it answers `true`, and,
where $`B`$ is one value up to strict equality (`singletonTag G B = some
t`), a membership test of $`x_i`$ against $`[t]`$ where it answers
`false`. The same holds with $`i`$ and $`j`$ exchanged. Its yields are
`memberYield`'s for those tag sets:

```
yieldFollows … t y :=
  memberFollows t y || match t with
  | arith .eq (var i) (var j) => eqYield i j || eqYield j i      -- new arm
  | …
where eqYield a b := match Γ[b]? with
  | some B => (if y.onFalse then (singletonTag G B).map ([·]) else equalityTags G B)
                .any (memberYield G images Γ links y · a)
  | none => false
```

and `nodeYields` proposes `memberYields (equalityTags G Γ[j]) i [true]`,
plus `[false]` where `singletonTag G Γ[j]` is a tag, for each operand.

**`memberYield`'s true side as strong as one tag's.** The true side of
`memberYield` accepts a yield where its type holds what the single-tag
rule accepts for every tag of $`S`$:

```math
\forall t\in S.\ \big(y.\mathit{target} = i \land \mathsf{ObservedSub}(\Gamma(i),\ y.\mathit{type},\ \mathsf{tag}\ t\ \mathsf{true})\big)
\ \lor\ \mathsf{fieldYield}(y, i, t, \mathsf{true})
```

beside the slice check it has. Sound by the same premise: where some
$`t\in S`$ holds of $`\rho_i`$, that $`t`$'s rule gives $`y`$'s type
(`checkObservedSub_sound`, `fieldYield_sound`, **proved** for one tag).
`string` against `"a" | "b"` then narrows to `"a" | "b"`, through
`familyMember`. `familyMember` refuses `numEq` of a zero
(`BranchRefinement.lean:1347`), so `number` against `0` stays `number`,
which is right, since `−0 === 0`. With this, the single-tag test is the
instance $`S = [t]`$ of `memberYield`, on both edges.

**The membership answer observed on the cells.** A `branchBind` edge out of
a membership test (`memberOn S (var i)`, or a comparison, with the tag sets
above) observes, besides its Boolean, on the tested slot: "some tag of
$`S`$ holds" on the true edge, "no tag of $`S`$ holds" on the false edge.
This is `observeTag` with a set:

```math
R_{\mathsf{true}} = V \sqcap \bigsqcup_{t\in S}\mathsf{ofTag}(t, \mathsf{true})
\qquad
R_{\mathsf{false}} = V \sqcap \textstyle\sqcap_{t\in S}\,\mathsf{ofTag}(t, \mathsf{false})
```

with $`V`$ the slot's value set (`valueBy`). It is stated of the slot and,
through `linkFacts`, of every cell a live read link says the slot was read
from, as `observeTag` does for one tag (`HeapKnowledge.lean:3368`). The
observation is a new `Observation` constructor,
`member (tags : List Tag) (answer : Bool)`, applied where `.tag` is:
`edgeKnowledge` and the edge check (`ControlFlow.lean:448`, its soundness
at line 1111). Its lemma is the analogue of `observeTag_holds`
(`HeapKnowledge.lean:3375`):

```math
\textbf{(O)}\quad \mathsf{Holds}\ k\ \rho\ h \;\land\;
(q \Rightarrow \exists t\in S.\ \mathsf{tagHolds}\ t\ \rho_i) \;\land\;
(\neg q \Rightarrow \forall t\in S.\ \neg\mathsf{tagHolds}\ t\ \rho_i)
\;\Rightarrow\; \mathsf{Holds}\ (\mathsf{observeMember}\ k\ i\ S\ q)\ \rho\ h
```

by `ofTag_holds` (`ValueSets.lean:433`), `mem_join` and `mem_meet`, and
`linkFacts_holds`. Its premise comes from `member_run` for `memberOn`, and
from (E1) and (E2) below for a comparison. The cells keep the fact after the
target's mapping drops the operand temporaries (`Atoms.lean:1217`), so a
re-read of `o1.a` after `if (o1.a === o2.b)` reads a cell whose contents
are `1 | 2`, as a re-read after a tag test does today.

**±0 and NaN.** A `numLit` label's meaning is its exact bits
($`v = \mathsf{num}\ b`$, `PositiveNormalization.lean:212`), so `+0` and
`−0` are different labels, and the label meet keeps two `numLit` labels
only when their bits are equal (line 449). `strictEquals`
(`Calculus.lean:885`) compares numbers by `numberEqual`: NaN equals
nothing, and the zeros equal each other. With $`x = -0`$ and
$`y : \mathsf{numLit}(+0)`$ (an internal type such as `positionRead`'s
index literal, `Control.lean:286`, holds `+0` alone), the label meet is
empty, which would make the true arm unreachable while Node takes it. The
tag slice keeps `−0`: $`\mathsf{tags}(y) = [\mathsf{numEq}(+0)]`$ and
`tagClause (numEq k) (numLit v)` is `numberEqual v k`. A NaN literal's tag
`numEq NaN` answers `false` of every `numLit`, so its true slice drops
every number literal, which is right: the true edge is not taken.

The false edge narrows only by `singletonTag`, whose number case requires
every literal of $`B`$ to be `numberEqual` to the first
(`Lowering/Types.lean:616`): `0` (both zeros) is the tag `numEq(+0)`. A
value $`u`$ with $`u \not\equiv v`$ for $`v`$ of $`B`$ is then no zero, so
`numEq(+0)` fails of it and the false slice drops both zeros, which is sound
because `−0 === +0`. No object type is a singleton for `singletonTag`, and no
tag tests one identity, so the false edge never narrows an object;
`symbolLit` is a one-value type without an equality tag and narrows nothing
on the false edge either.

**The soundness lemmas.** These are about values: `meaning`
(`PositiveRules.lean:147`), `strictEquals`, `sameValue`, `numberEqual` and
`tagHolds`. None reads the heap, so objects compared by identity need no
heap invariant. **Conjectured** (statements fixed, proofs by cases not
written):

```math
\textbf{(E1)}\quad \mathsf{equalityTags}\ G\ B = \mathsf{some}\ S \;\land\; v\in[\![B]\!]_{n,W} \;\land\; \mathsf{strictEquals}\ u\ v = \mathsf{some\ true}
\;\Rightarrow\; \exists t\in S.\ \mathsf{tagHolds}\ t\ u
```

```math
\textbf{(E2)}\quad \mathsf{singletonTag}\ G\ B = \mathsf{some}\ t \;\land\; v\in[\![B]\!]_{n,W} \;\land\; \mathsf{strictEquals}\ u\ v = \mathsf{some\ false}
\;\Rightarrow\; \neg\,\mathsf{tagHolds}\ t\ u
```

```math
\textbf{(E3)}\quad \mathsf{strictEquals}\ u\ v = \mathsf{strictEquals}\ v\ u
```

```math
\textbf{(E4)}\quad \mathsf{Steps}\ m\ h\ (\mathsf{arith\ eq}\ v\ w)\ h'\ u \;\land\; \mathsf{isVal}\ u
\;\Rightarrow\; h' = h \land \exists q.\ \mathsf{strictEquals}\ v\ w = \mathsf{some}\ q \land u = \mathsf{boolVal}\ q
```

(E1) is by cases over the clause holding $`v`$ (`plainTy` gives one, by
`expand_sem`) and `strictEquals`'s arms; `dedupNumberEqual` keeps a tag
with the same holders. (E2) uses that the holders of an equality tag are
pairwise strictly equal ($`\mathsf{numberEqual}`$ is transitive off NaN,
and `numEq NaN` holds of nothing) and that every clause of $`B`$ answers
$`t`$ `true` (`tagClause_sound`). (E3) is the symmetry of `numberEqual` and
of the identity comparison. (E4) is the `Steps`-level form of `binop`'s
`.eq` arm, as `member_run` and `test_ite_run` are for theirs; `arith_run`
(`IndexWrites.lean:52`) states it on `SafePost` and does not serve here.
None of $`\tau`$'s tags is `hasKey`, so
$`\mathsf{tagHoldsIn}_h = \mathsf{tagHolds}`$ (`Calculus.lean:1704`).

The new case of `yieldFollows_sound` (`PromiseCalls.lean:923`) reads
`y.conditional = !y.onFalse` from `memberYield`, takes $`u = \mathsf{true}`$
from `hcond` or $`u = \mathsf{false}`$ from `hneg`, and only then builds
`hrun`: with (E4) and (E1) (with (E3) for the operand $`j`$) on the true
side, (E2) on the false side. Then `memberYield_sound` applies as it is.

A type is not closed under strict equality. `numLit(+0)` holds `+0` and not
`−0`, and an object type holds a term while another term may carry the same
identity. So the lemma is the weaker statement that suffices: a value
strictly equal to a value of $`B`$ passes one of $`B`$'s tags.
**Conjectured**: with an invariant that an identity determines its object
term, the true edge could narrow an object operand to the other's object
clauses. The model states no such invariant, and this rule does not need
one.

**The lowering.** A branch on `l === r` (`compileConditionAtom`,
`.arith p .eq l r`) lowers as a membership test's branch does
(`memberNodes`, `Atoms.lean:481`): `l` into a slot, then `r` into a slot,
each once, in source order, then one node `arith .eq (var 1) (var 0)` whose
continuation is `.branchBind yes no`. `!==` is `.not`, which exchanges the
targets. Its yields and observations follow the rule. What replaces each
part of the split:

- `equalitySplit` and `dispatch` are deleted. Their narrowing is the
  rule's two edges, and their field facts are the membership observation.
  The arm-by-arm correlation they stated ($`x`$ is $`k`$ exactly when
  $`y`$ is) is the slice's union over $`k`$. The chain's redirection of an
  impossible arm (`possible`) becomes an empty slice, which the pass reads
  as an unreachable edge.
- `savedSplit` is deleted: every operand, a call included, is evaluated
  once into a slot.
- The comparison that is evaluated and then dropped (node 72) is deleted:
  the branching node is the comparison, and it carries the comparison's
  obligations.
- The correlated `choose` keeps its own evaluation in this step.
  Dropping it is a separate, later step: `compileConditionAtom`'s contract
  (`Atoms.lean:1205`) and `executionPredicate` read that evaluation, and
  it costs a constant four nodes.

The comparison node with `.bind` (a value, not a branch) keeps its true
yields as implications on its result (`edgeImplications`), so
`const c = (x === y); if (c) …` narrows on `c`'s true edge.

### The example through the change

```
78  t12 = a.kind     choose: evaluate (kept)
77  t13 = b.kind
76  t14 = (t12 === t13)
75  t15 = (t14 ? false : true)
    t16 = a.kind     link {cell a, field kind, value t16}
    t17 = b.kind     link {cell b, field kind, value t17}
    t16 === t17      branchBind: true → after the if    false → return false
```

1. Reads: slots `t16` and `t17` at `Kind`, with links to `a.kind` and
   `b.kind`.
2. The comparison node's step adds `equalAtoms` as before: on `true`,
   $`t_{16} - t_{17} \le 0`$ and $`-t_{16} + t_{17} \le 0`$; on `false`,
   $`t_{16} - t_{17} \ne 0`$. Each is one fact, conditional on the result.
3. True edge: $`\mathsf{tags}(\mathsf{Kind}) = [\mathsf{numEq}\ 0, \mathsf{numEq}\ 1, \mathsf{numEq}\ 2]`$.
   The slice of `Kind` by them is `Kind`'s four labels, the whole type, and
   the field slice of `Tree` (one record) at `kind` is `Tree`, so no yield
   narrows anything. The observation meets each cell's value set with
   $`\{0, -0, 1, 2\}`$: one fact per cell.
4. False edge: `Kind` has no single equality tag, so there is no yield and
   no observation beyond the Boolean.

Seven nodes for the condition (four after the later step), for any number
of members. The closure's walk goes from 84 nodes to 68 (computed from the
dumps, not run).

### What this duplicates

| Modelled here | Where the verifier models it | Relation |
| --- | --- | --- |
| The slice of an operand by a set of tags | `memberSlotSlice`, `memberFieldSlice`, `memberYield` | read: the comparison is a membership test whose tags come from the other operand's type |
| One tag's narrowing of a family | `observed`, `ObservedSub`, `familyMember` (`PromiseCalls.lean:712-723`, `BranchRefinement.lean:1335`) | read by `memberYield`'s true side, for each tag |
| What an answer states of the cells | `observeTag`, `linkFacts` | generalized from one tag to a set (`observeMember`), which `memberOn` and the comparison share |
| A singleton's tag | `singletonTag` (lowering) | read: moved into the checker with (E2), and the lowering calls it there |
| A comparison with a singleton | `singletonTest` (`comparisonsExpr`, `Lowering/Types.lean:632-645`), lowered as a tag test of the other operand | duplicated by the rule at $`S = [t]`$, which is as strong once `memberYield`'s true side reads `ObservedSub` and the edge observes the answer. It stays in this step. It is retired in its own commit once its cases (`literal-equality`, `literal-equality-reads`, `module-value-equality`) verify through the comparison. **Conjectured**: `literal-equality-reads` needs $`i = k`$ from `equalAtoms` with a constant's slot, where `numEqIndices` states it for the tag test today |
| The run of a strict comparison | `binop`'s `.eq` arm, `arith_run` | read, through (E4) |
| Linear facts of a comparison | `equalAtoms` | kept, unchanged |
| The narrowing in the claims | `Synthesis.lean:3281` (each operand the union of its slices at the other's singletons) | the same rule, so the claims ask for what the pass proves: the synthesis computes $`\mathsf{slice}_q(\Gamma(x), \mathsf{tags}(\Gamma(y)))`$ by the same definitions |

The prose about the split moves to the documents that own it.
[PROGRAM-TYPING.md](../PROGRAM-TYPING.md#a-membership-test) gains "A strict
comparison" after "A membership test", stating the tags, the rule, the
observation and (E1) to (E4). Its membership slice reads `ObservedSub` on
the true side. The paragraphs of SOURCE-ELABORATION.md ("`x === y` with `x`
claimed at a union of singletons …") and SINGLE-PASS-FRONT.md ("equality
with an operand holding one of several singletons …, `equalitySplit`")
state the rule instead.

### Tests

- `equality-several-singletons`, `literal-equality` and
  `module-value-equality` verify, re-reads after the branch included
  (`const a: 1 | 2 = o1.a` in `fieldAgainstField`, `const f: 0 | 1 =
  obj.field` in `fieldAgainstName`). Their negative cases
  (`invalid-equality-several-singletons`, `invalid-literal-equality`,
  `invalid-module-value-equality`) are refused.
- A family: `function f(s: string, k: "a" | "b"): "a" | "b" { if (s === k)
  return s; return k }` verifies, and the same with `x: number` against
  `1 | 2`. Negative: `x: number` against `0 | 1` returning `x` at `1`
  is refused.
- A type parameter (negative):
  `function f<T>(x: "a" | "b", y: T, xs: number[]): number { if (x === y) return xs[0]!; return 0 }`
  is refused. Under Node, `f("a", "a", [])` returns `undefined` at
  `number`. If the true edge were read as unreachable, it would be accepted.
- ±0: no source program is unsafe for it, since TScert's `0` is both zeros
  and a literal type holding one zero alone is internal. A control of
  `tests/single-pass-controls.mts` forges a fragment with `x : −0` and
  `y : +0` (one label each) and a true arm reading a field of `null`. It is
  refused, because the arm is reachable, as it is under Node; with the
  label meet it would be accepted. A second forged control, `x : +0 | 1`
  and `y : −0` with the false arm returning `x` at `1`, is accepted.
- An object operand: a case comparing `a: string | Cat` with `b: Cat` reads
  `a.meow` on the true edge; its negative reads `a.length`.
- The lowering: `make lowering` on the example shows `a.kind` and `b.kind`
  read once each by the dispatch, in source order, and one comparison node
  branching.
- Size: the example's node count is the same at 8 and 128 members, and its
  time and facts are measured as the baseline was.

### Size

Measured from the code at `7494763`: lines removed are counted, lines added
are estimated (not measured).

| File | Definitions | Change |
| --- | --- | --- |
| `Source/Lowering/Control.lean` | `SplitOperand`, `equalitySplit`, `savedSplit` (lines 305–357) | −53 |
| `Source/Lowering/Atoms.lean` | `dispatch`, the `.arith .eq` arm (lines 1248–1321) | −74, +20 |
| `Source/Lowering/Types.lean` | `singletonTag` moves to the checker | −10 |
| `Programs/PromiseCalls.lean` | `equalityTagsOf`, `equalityTags`, `singletonTag`, (E1)–(E3), the `yieldFollows` arm and its case of `yieldFollows_sound` | +150 to +250 |
| `Programs/PromiseCalls.lean` | `memberYield`'s true side by `ObservedSub` and `fieldYield` per tag, and `memberYield_sound`'s case | +40 to +60 |
| `Semantics/Calculus.lean` or `Programs/IndexWrites.lean` | (E4), the `Steps` lemma of `.eq` | +30 |
| `Semantics/HeapKnowledge.lean` | `observeMember`, (O) | +40 to +60 |
| `Programs/BranchRefinement.lean`, `Programs/ControlFlow.lean`, `Programs/CertificateProducer.lean` | the `member` observation, its `holds`, the edge check (lines 448, 1111) and `edgeKnowledge` | +40 |
| `Programs/CertificateProducer.lean` | `nodeYields`' arm | +10 |
| `Programs/Parametricity.lean` | `yieldFollows_reassign` (line 330) over the new arm | +10 |
| `Source/Synthesis.lean` | the equality narrowing (line 3281) | ~±20 |
| Docs | PROGRAM-TYPING.md, SOURCE-ELABORATION.md, SINGLE-PASS-FRONT.md | +50, −10 |

The later step, the correlated `choose` without its own evaluation
(`Execution.lean`), is not counted here.

Open risks:

- **Slice cost.** The checker's slice costs $`|A|\cdot|\mathsf{tags}(B)|`$
  clause answers per yield (about 4,000 at 64 members), plus one
  `ObservedSub` per tag on the true side. Neither is measured. If it shows,
  the true slice is computed in one pass over $`A`$: each label is kept
  where some clause of $`B`$ is not contradicted, by a hash set of
  $`B`$'s literals.
- **Retiring `singletonTest`.** It depends on the linear facts of
  `literal-equality-reads`.

## 2. One name per value, and only the names a later node reads

### The existing mechanism this extends

A walk's names (`State.names`) are the values its slots hold. A read
(`readAt`) gives a fresh name and a read link from the object's name
(`link {cell := 1, value := 16, field := kind}`); a second read of the same
field, with no write between, gives another fresh name, linked to the first
as an alias (`link {cell := 16, value := 12, alias := true}`). A name leaves
the store when no slot of the target holds it (`edgeTransfer`, `droppedBy`,
then `Store.drop`, which restates the name's facts through links and
eliminates it from the linear facts). The lowering's jumps keep every slot
of the scope, temporaries included.

On the example, `a.kind` has the names `n1.kind`, `n12` and `n16`, and
`b.kind` the names `n2.kind`, `n13`, `n17`, `n19` and `n20`; each new name
is related to every name of the other value, under both values of the
pending `n15`. `n12` and `n13` are never read after node 72 and stay to the
end of the chain.

### The change

- **A read returns the name its read link states.** Where the store holds
  `link {cell := o, value := v, field := f}` and no write between reaches
  `o.f`, `o.f` is `v`: the step's result is `v`, not a fresh name. The read
  link is already a fact of the store; this uses it.
- **A name leaves at the first edge after its last read.** The slots a
  node's successors read (liveness over the walk's graph) are computed once
  per walk; at each edge, a name no live slot of the target holds is in
  `gone`, as a name of a slot the mapping drops is. `Store.drop` is the
  existing step.

On the example, `a.kind` and `b.kind` have one name each, and the
temporaries of the comparison leave after the branch.

### What this duplicates

The read link is the store's own fact; `Store.drop` is the step every edge
already applies. Liveness is new, a function of the graph alone.

### Tests

- A case reading a field twice across no write verifies with one name, and
  a negative case reading it across a write that reaches it keeps two.
- The dump of the example shows no fact naming a temporary after the node
  that last reads it.
- Every case pattern of the pass's reads, links and drops passes.

## 3. A path and the name its read link gives are one term

### The existing mechanism this extends

A read link `o.f ↦ v` (`HeapLinks.Link`, held by `HeapLinks.Holds`) states
that the field `f` of the object named `o` holds the value named `v` in the
current heap; `bridgeReads_term` (`HeapKnowledge.lean`) proves that a term
rooted at `o` with `f` first denotes what the term rooted at `v` with the
rest of the path does. The code moves facts between the two forms at five
places, read from it:

```
applyDelta (SinglePass.lean)           -- after each step
  add each output fact not among the step's inputs (Store.add)
  for each added linear fact x, each name v of x a read link o.f ↦ v gives:
    add x restated over o.f            (restateReads reads (· == v) [x])
readFrame, writeOutput (HeapExpressionRules.lean)   -- a read's or a write's rule
  withReadAtoms: each linear fact over the path o.f..., restated over v (readAtoms)
                 each linear fact over a read's value v, restated over o.f (liftedEvery)
expandLinks (KnowledgeExpand.lean)     -- every step's and check's knowledge
  each value fact v ∈ S behind a link, as the cell fact o.f ∈ S (linkFacts)
  each linear fact over a path, restated over the link's value (lowerAtoms)
Store.drop (SinglePass.lean)           -- a name leaving
  each linear fact over a dropped v, restated over o.f where every dropped
  name of the fact has a read (restateReads, liftDropped), then eliminated
bridgeOf (HeapKnowledge.lean)          -- an entailment check
  both sides' terms lifted toward the paths (liftTerm)
```

`Store.add` inserts a fact as it is given. So a fact a rule states over the
read's value is stored over the value and, by `applyDelta`, over each of
its paths; a cell fact a rule's input derives (`linkFacts`) is stored beside
the value fact it came from.

### The example as it is

Node 59 of the closure's walk (`kind3`, single-pass at `da5e4522e`) is
`t14 = (t12 === t13)`, the correlated `choose`'s evaluation of
`a.kind === b.kind`; its entry holds the links `n1.kind ↦ n12` and
`n2.kind ↦ n13`. Its step adds 15 facts and holds 17:

```
[if n14]     ±(n12 − n13) ≤ 0   ±(n1.kind − n13) ≤ 0   ±(n12 − n2.kind) ≤ 0
[unless n14] n12 − n13 ≠ 0      n1.kind − n13 ≠ 0      n12 − n2.kind ≠ 0
cell n1.kind ∈ K   cell n2.kind ∈ K   n12 ∈ K   n13 ∈ K   int(n12)   int(n13)
```

with $`K = \{0, 1, 2, -0\}`$. The comparison's rule states the first column;
`applyDelta` restates each fact through each read (the next two columns);
the ternary at node 58 restates those again, giving the fourth form
`n1.kind − n2.kind`. The cells come from `expandLinks`' `linkFacts` of the
value facts its context gives, which the step's output carries. Over the
closure's 67 nodes, 369 of the 1,535 facts held are linear facts over a
path a live link names, and 127 are value facts a cell fact restates
through a link (counted on the `TSCERT_DUMP` output).

### The change

**The store's form of a fact** (`Store.lowerAtom`, applied by `Store.add`):
where the store holds a read link `o.f ↦ v`,

- a linear fact's term rooted at `o` with path `f :: p` is the term rooted
  at `v` with path `p`, as far as the links reach (`Store.lowerTerm`);
- a cell fact `o.f ∈ S` is the value fact `v ∈ S`.

Proved: `lowerTerm_eq` (from `bridgeReads_term`), `value_of_cell`,
`lowerAtom_holds`; `add_ok` and `add_below` read them.

**Each step reads both forms.** `applyDelta` no longer restates; the step's
knowledge (`expandLinks`) restates each linear fact over a read's value
toward the path it was read from (`restateReads`, proved by
`restateReads_holds`) beside `lowerAtoms` and `linkFacts`, so a rule that
keeps a fact over a path across a call or a write that drops the link
(`linked-path-fact`, `map-insert-keeps-paths`) finds it.

**A name leaving restates through its link.** `Store.drop` restates a
dropped name's value fact as the cell fact of the field a read link from a
kept name says it was read from (`Store.cellsOfDropped`, proved by
`cellsOfDropped_ok`, from `cell_of_value`), and restates a linear fact's
terms as far as the reads reach, leaving a term whose root no read gives
for the elimination (`liftDropped`): from `t − n_old ≤ 1` and
`−n_old ≤ 0`, where the write `c.i = t` gave the link `c.i ↦ t` and
removed `c.i ↦ n_old`, dropping both names gives `−c.i ≤ −1`
(`cursor-invariant-after-writing-call`, `local-callback-cursor`).

A fact over a path the store held before its link was added keeps the
path's form. Merges compare facts by form: after `a && b` reading
`p.widths` in both arms and `p.segmentFlags` in one, restating the
invariant `|p.segmentFlags| = |p.widths|` at each link gives
`|p.segmentFlags| = |n_w|` in one predecessor and `|n_s| = |n_w|` in the
other, and the meet loses it (`lazy-cache-keeps-facts`).

### The example through the change

Node 59's step adds 7 facts and holds 9:

```
[if n14]     ±(n12 − n13) ≤ 0
[unless n14] n12 − n13 ≠ 0
n12 ∈ K   n13 ∈ K   int(n12)   int(n13)
```

The rule's output carries the cell facts `linkFacts` derived; `Store.add`
stores each as `n12 ∈ K`, already held. The branching comparison, node 55,
holds 12 facts (29 before).

### What this duplicates

| Modelled here | Where the verifier models it | Relation |
| --- | --- | --- |
| A path and a link's value as one term | `lowerAtoms`, `liftTerm`, `bridgeReads_term` | read: `Store.lowerTerm` is `lowerByLinks` over the store's links, one read at a time |
| A cell behind a link as the value | `valueBy`, `cellBy`, `linkFacts` | read: `value_of_cell` is `valueBy_mem`'s link case, `cell_of_value` `linkFacts_holds`'s |
| Restating a dropped name | `restateReads` in `Store.drop`, `materialize` and `project` | the same function, its lift total |

### Measurement

`TSCERT_DUMP`, the closure's walk: 1,036 facts over 67 nodes at 3, 8 and 32
members (1,535 before). Removed: the 369 linear facts over a linked path,
and 127 value facts and the cell facts beside them. Two duplicates are
other instances, left: `int(n)` beside a value set of safe integers, which
implies it (118 facts: a value set implying an index fact, no read link),
and a length atom's linear expansion beside `length(x) = n` (120 facts,
`Store.add`'s `atomLinear`, kept for the call layers that keep or drop the
linear form).

### Tests

- `field-and-link-value`: a precondition over `box.at` bounds `xs[i]` at the
  read's name `i`, and a test over `i` meets a callee's precondition over
  `box.at`; `invalid-field-and-link-value`, the field written between the
  test and the call, is refused and reads past the array under Node.

## 4. A store holds no fact that says nothing, and no impossible state

### The existing mechanism this extends

`Store.add` and `Store.addRaw` insert any atom once (`Atom.canon`).
`ControlFlow.unsatisfiable` finds a node unreachable from its claim's
types, and an exit of such a node is vacuous (`vacuousOf`, `vacuous_false`):
its types, its target's assertion and a loop head's checks are skipped.

On the example the store holds `0 ≤ 0` and `0 ≤ 4294967295`, left by the
elimination of a dropped name bounded on both sides, each at 31 of the
closure's 67 nodes.

### The change

- A linear fact over no term is a constant (`Atom.trivial`): a true one is
  not added. A form whose terms cancel (`n19 − n19 ≤ 0`) is no constant: it
  states its terms defined.
- An unconditional fact whose form normalizes to no term with a false
  bound (`Atom.contradiction`) is stored as `0 ≤ -1` (`Atom.bot`); a store
  holding it is impossible (`Store.impossible`). Its soundness is a theorem:
  such a store holds at no valuation (`storeOk_impossible`).
- An exit whose edge store is impossible is vacuous, as an exit whose
  context is empty: it checks nothing. The node's step is still checked,
  and the false fact stays in the stores after it.

Skipping the step of a node whose entry store is impossible, and carrying
no facts past it, needs the step's checks (`checkedStep` and the lemmas
reading its result) to state their conclusion under the entry's facts,
with a case for a step not run.

### Tests

- The dump of the example shows no trivial fact: the closure's walk holds
  1,535 facts over its 67 nodes (1,597 before), and every walk of the unit
  65 fewer.
- `facts-impossible-branch` verifies with its branch's edge into a loop
  head unchecked; `invalid-facts-possible-branch`, where the facts do not
  exclude the branch, is refused, and returns `NaN` under Node.

## 5. Stores share what their nodes share

### The existing mechanism this extends

`Store` is a `Std.HashSet` of atoms and a `Std.HashMap` from names to atoms.
A walk keeps each node's entry and after states, its step's store and each
incoming edge's state (`LabelWalk`, `Walk.incoming`); consecutive nodes'
stores are separate copies.

### The change

`Store` is a persistent map (`Lean.PersistentHashMap`), so a node's store
shares every fact it did not change with its predecessor's.

### Tests

The pass's results are equal before and after on every case pattern;
memory is measured.

## Order and measurement

The changes land in the order 1, 2, 4, 3, 5, each measured as the baseline
was. Each is a separate commit series and states its measurement in its
commit records.
