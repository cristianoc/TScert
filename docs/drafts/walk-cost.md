# The cost of a walk: one comparison, one name per value, live facts only

A walk of the single pass holds, at each node, the facts of its state; the
cost of a unit is the sum over its nodes. On `tools/type-term.mts`
(`typeTerm`), that sum reaches 4.75 GiB, above the census's 4 GiB stage
limit, and the four files importing it lose their module interfaces. This
draft states, for one small program, where the facts come from, and four
changes, each a cause on its own: the lowering of a comparison, the names a
walk keeps, the facts a store keeps, and how stores are held. Each change
has its test and its measurement.

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

### The existing mechanism this extends

`equalitySplit` and `dispatch` (`Source/Lowering/Control.lean`,
`Source/Lowering/Atoms.lean`), for a branch on `l === r` where one operand
is read without effect and claimed at a union of singletons:

```
lower (if (l === r) yes else no):
  evaluate l === r, drop its Boolean            -- its obligations
  for each singleton k of the split operand s:  -- chain
    re-read s; test s == k
      yes: re-read the other operand o; test o == k   (yes → yes, no → no)
      no:  next k
  after the last k → no
```

It was added for `equality-several-singletons`, `literal-equality` and
`module-value-equality` (c04f4ec57): on the true edge, `x === y` narrows `x`
to `y`'s singletons, and each singleton's arm narrows both operands to it.
On the example, `a.kind !== b.kind` evaluates the comparison twice (nodes
76, 72), reads `b.kind` four times and `a.kind` four times, and tests four
constants (0, 1, 2 and −0) for three members: about four nodes per member.

### The change

A branch on `l === r` lowers to the comparison and one branch on its
Boolean. The true edge narrows each operand to the meet of the two operands'
types, and states their equality as a link of the two names (one name, §2);
the false edge narrows an operand only where the other is a singleton (the
rule of a test against a constant, `BranchRefinement.tagSlice`). The
singletons' correlation the chain stated arm by arm (`x` is `k` exactly when
`y` is) is the equality itself.

On the example: nodes 78–75 stay; 74–56 go. The walk has a constant number
of nodes for any number of members.

### What this duplicates

The narrowing of the true edge is the narrowing of `x === k` for a
singleton `k`, applied to a meet; the equality is the link a read already
states. Nothing new is modelled.

### Tests

- The three cases of c04f4ec57 verify; a negative case where the narrowed
  operand is used at a member the other excludes is refused.
- The lowering's tests for evaluation order: each operand is read once,
  in source order (`make lowering` on the example).
- The example's node count at 8 and 128 members is the same.

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

## 3. A store holds no fact that says nothing, and no impossible state

### The existing mechanism this extends

`Store.add` and `Store.addRaw` insert any atom once (`Atom.canon`).
`ControlFlow.unsatisfiable` finds a node unreachable from its claim's types.

On the example the store holds `n19 − n19 ≤ 0`, `−n2.kind + n2.kind ≤ 0`
and `0 ≤ 0`, and, after the chain has excluded every member,
`b.kind ≤ −1`, `−b.kind ≤ −3` and `0 ≤ −4`.

### The change

- A linear fact whose form is empty after normalization is true or false
  as a constant: a true one is not added; a false one makes the state
  unsatisfiable.
- An unsatisfiable state is the state of an unreachable node, as an empty
  claim type already is: the walk carries no facts on it and checks
  nothing there. Its soundness is a theorem: a store holding `0 ≤ d` with
  `d < 0` holds at no environment.

### Tests

- The dump of the example shows no trivial fact.
- A case whose branch is impossible by its facts (and not its types)
  verifies with the branch unvisited; a negative case where the facts do
  not exclude it is refused.

## 4. Stores share what their nodes share

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

The changes land in the order 1, 2, 3, 4, each measured as the baseline
was. Each is a separate commit series and states its measurement in its
commit records.
