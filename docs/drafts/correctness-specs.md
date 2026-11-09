# Draft: correctness specifications

A design for stating correctness properties of TypeScript functions in
TypeScript and proving them over the calculus graph the function lowers to,
approved by the owner (2026-10-28) with every decision as recommended; its
status is in [WORK](../../WORK.md#status). Base: TScert main at b59096f. Claims are labelled **proved** (with the Lean
name), **cited** (with the document and its scope), **observed** (with what
ran) or **conjectured**; every theorem this draft names without a Lean
location is a proposal. Out of scope: proving the lowering, concurrency and
async interleavings, termination, and exceptional postconditions. Stated
limits of this design, each refused where it is written: postconditions
over the entry heap's contents (old values), frames of nested objects,
contracts of generic and of overloaded signatures (§2).

## The existing mechanism this extends

The [effect-qualified call contract](../SEMANTICS.md#effect-qualified-call-contracts)
of a signature, written as a [stated effect](../SOURCE-ELABORATION.md#stated-effects)
and proved from the callee's code by the declaration-effect check
([inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)),
over the [checked control-flow graph](../PROGRAM-TYPING.md#checked-control-flow-graphs)
a unit lowers to, with its promise in the language of
[stored knowledge](../PROGRAM-TYPING.md#stored-knowledge-and-how-it-is-read)
(cited). A guard's and an assertion's promise are such contracts; a source
contract (§1) is the same contract with a precondition, a postcondition
and a frame written by the program, the frame a closed footprint
([footprints](../FOOTPRINTS.md#changes-and-footprints)). What the design
adds to these mechanisms is the knowledge contract a unit exports (§3), the
atoms its promises state beyond the existing ones (§4), and the proof routes
and the acceptance conjunct that certify a contract (§5).

## 1. The contract

A unit $`f`$ lowers to a graph $`P`$ with input context $`\Gamma`$, entry
label $`s`$ and goal $`R`$
([checked control-flow graphs](../PROGRAM-TYPING.md#checked-control-flow-graphs)).
Its entry environment $`\rho`$ holds the receiver, the parameters and the
captures in the order [graph code](../SEMANTICS.md#graph-code) fixes; write
$`r_0`$ for the receiver and $`\vec a`$ for the actuals. A **source
contract** of one signature of $`f`$ is a precondition $`p`$, a
postcondition $`q`$ and a frame $`\Phi`$. $`p`$ and $`q`$ are closures,
graph code with captures of their own, invoked with $`f`$'s receiver as
their receiver; $`q`$ takes the result before the actuals:

```math
p(\vec a)\Downarrow^{j}_h b\iff\exists h'.\ h,\mathsf{invoke}(p,r_0,\vec a)\to^{j}h',b
\qquad(b\ \text{a value})
```

The steps are deterministic (proved: `Step_det`). The source contract is a
property of runs. For inputs meeting $`\Gamma`$ and a heap meeting its
contracts:

```math
\models\{p\}\,f\,\{q\}[\Phi]\iff
p(\vec a)\Downarrow_h\mathsf{true}\ \land\ h,\mathsf{goto}(s,\rho)\to^{*}h',v\
\Longrightarrow\ \neg\bigl(q(v,\vec a)\Downarrow_{h'}\mathsf{false}\bigr)\land\mathrm{Post}(⟦\Phi⟧_{\vec a,h},h,h')
```

The precondition is **established truth** ($`p`$ returns `true`); the
postcondition is **weak** ($`q`$ does not return `false`, which a throwing
or diverging $`q`$ meets); the statement is partial correctness of normal
returns. Omitted clauses are `true`, `true` and the unrestricted frame. A
signature has at most one contract; a second is refused.

**Frames.** $`⟦\Phi⟧_{\vec a,h}`$ is a `Footprints.Footprint` read at the
entry heap (proved definition: `Footprints.Post` keeps every entry-heap
location outside the regions and leaves fresh locations unconstrained).
`modifies` has one accepted form, an arrow whose body is an array literal
of region terms, each

```text
region ::= field(x, "k")   x a parameter, "k" a string literal naming a field of x's declared type
         | elements(x)     x a parameter of an array type
```

read as $`(\mathsf{field}(x,\texttt{k}),\mathsf{any})`$, and as
$`(\mathsf{field}(x,\texttt{[]}),\mathsf{any})`$ with
$`(\mathsf{elems}(x),\mathsf{any})`$ (`[]` is `arrayStoreKey`: the array's
store location and its element cells). Any other body is refused; the
`modifies` closure is never run, and lowers as ordinary code.

## 2. The source form

A contract is a statement in the module declaring $`f`$:

```ts
export type Region = { readonly kind: "region" };
export function spec<F>(f: F, contract: {
  requires?: (...args: never[]) => boolean;
  ensures?: (result: never, ...args: never[]) => boolean;
  modifies?: (...args: never[]) => readonly Region[];
}): Modifies<{}, void> {}
export function invariant(holds: () => boolean): Modifies<{}, void> {}
export function lemma(name: string, holds: (...args: never[]) => boolean): Modifies<{}, void> {}
export function forAll(from: number, to: number,
    p: (i: number) => Modifies<{}, boolean>): Modifies<{}, boolean> {
  for (let i = from; i < to; i++) if (!p(i)) return false;
  return true;
}
export function field<T extends object, K extends keyof T & string>(o: T, k: K): Region { return { kind: "region" }; }
export function elements(a: readonly unknown[]): Region { return { kind: "region" }; }
```

```ts
spec(clamp, {
  requires: (x: number, lo: number, hi: number) => lo <= hi && x === x,
  ensures: (r: number, x: number, lo: number, hi: number) => lo <= r && r <= hi,
});
```

Footprints are written in place, the only form `statementOf`
(`tools/type-term.mts`) admits; an alias of one is refused there.

**Selecting the signature.** Each predicate writes its parameter types,
and a receiver as `this:` in a function expression. The reader matches the
written list against $`f`$'s signature and refuses a contract matching
none. TypeScript checks the bodies against the written types; the reader
checks the match, as it checks a closure's annotation. The contract is the
[effect-qualified call contract](../SEMANTICS.md#effect-qualified-call-contracts)
of that signature with a knowledge promise (§3); the guard and assertion
promises are two instances (conjectured: an embedding theorem relating
`CallEffects.Effect`'s `guards p` and `asserts p` to it). A generic
signature and an overloaded declaration are refused: the stated-effect
rules refuse a statement on a generic closure, whose code is checked at its
binders' bounds, and on any signature of an overloaded declaration, whose
unit is certified at one (cited:
[stated effects](../SOURCE-ELABORATION.md#stated-effects)). Lifting them is
front-end and checker work: certifying a predicate at every admissible
assignment of the contract's binders, as a generic body is
([generic bodies](../DESIGN.md#generic-bodies); cited), and checking an
overloaded declaration's body once per contracted overload.

**Effects over the written domain.** The registration functions' empty
bodies certify nothing about their arguments, and their parameter types
state no effect. The obligation comes from the contract plan: the reader
claims each predicate closure at the signature its written parameters give,
result `boolean`, with the empty closed footprint, and the closure's code
is checked at that claim by the declaration-effect check, its captures'
reads and its callees included
([function declarations](../SOURCE-ELABORATION.md#function-declarations);
cited). `forAll`'s callback parameter states the footprint as a function
type, an admitted written signature; a closure passed for it is claimed at
that qualified signature and certified before the call consumes it (cited:
[inferred call effects](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)).
The registration call is an ordinary call: its arguments are evaluated
(closure allocations) and it lowers with no rewrite.

**Loop invariants** are a statement `invariant(() => …)` first in a loop
body; the closure reads the loop's locals by lexical scope. **Lemmas** are
`lemma(name, (…) => …)` statements (§5).

The criterion is that the front end reads the form and TypeScript checks
it:

| Form | Read by the front end | Checked by TypeScript |
| --- | --- | --- |
| `spec`/`invariant`/`lemma` statements | as calls, bound by declaration | yes |
| JSDoc tags (`@requires lo <= hi`), the style of JML | as comment text, by a second expression parser | no |
| A sidecar `.spec.ts` module importing $`f`$ | yes | yes; it cannot name a loop's locals |
| A sidecar in another language (Lean, JSON) | by a reader of its own | no |

The statement form meets both. It is the design of embedded contract
languages (.NET Code Contracts: contracts as calls in the host language,
checked by its compiler); the clause names are Dafny's.

## 3. The knowledge contract

What a unit **exports** to its callers is a **knowledge contract**
$`\models_K\{K_p\}\,f\,\{K_q\}[\Phi]`$: stored knowledge $`K_p`$ over
$`r_0,\vec a`$ and $`K_q`$ over the result, $`r_0`$ and $`\vec a`$, in the
language of [stored knowledge](../PROGRAM-TYPING.md#stored-knowledge-and-how-it-is-read)
with the atoms of §4. It states, for every budget $`n`$, world $`W`$, heap
$`h`$ and environment $`\rho`$ with $`\mathrm{EnvOk}(\Gamma,\rho,n,W)`$,
$`\mathrm{WorldAdm}(W)`$, $`\mathrm{HeapOk}(n,W,h)`$ and
$`\mathrm{Holds}(K_p,\rho,h)`$:

```math
\mathrm{SafePostExc}_P\bigl(⟦R⟧,\ \lambda h'\,v.\ \mathrm{Holds}(K_q,[v,r_0,\vec a],h')\land\mathrm{Post}(⟦\Phi⟧_{\vec a,h},h,h'),\ n,W,h,\mathsf{goto}(s,\rho)\bigr)
```

the heap-aware graph judgment `DocumentSafe` already states for a unit's
claimed footprint (proved:
[Json.lean](../../lean/Verification/Source/Claims/Json.lean), the second
safety conjunct of `DocumentSafe`, from `GraphCode.goto_bounded`).
Knowledge holds of an environment and a heap and names no budget or world
(proved definition: `HeapKnowledge.Holds`), so the postcondition is
budget-independent. Every route that establishes a contract establishes
this one: the automatic route, a manual request-level proof (§5), a
recursive call, a certified import. Callers consume it alone: a call
establishes $`K_p`$ of its actuals and its result then holds $`K_q`$, as a
call at a promise signature consumes the promise the callee holds
(`if-guard`; proved: `promiseCall_sound` in
[PromiseCalls.lean](../../lean/Verification/Programs/PromiseCalls.lean)).
The source contract of §1 is a proved consequence and is never consumed: a
precondition `false` or a throwing postcondition gives a caller nothing.
An imported contract is consumed only through a
[certified import](../SOURCE-CONTRACTS.md#certified-imports), whose own run
establishes the knowledge contract; an uncertified import's contract is
not consumed. A recursive call, or a cycle of contracted functions, uses the
knowledge contract one budget level lower, the argument recursive
closures' types rest on (conjectured to extend).

**The automatic route** checks $`P`$ from entry knowledge $`K_p`$ (proved:
`accepted_entry_safe` in
[ControlFlow.lean](../../lean/Verification/Programs/ControlFlow.lean) takes
claimed environment and heap facts at a checked point) at a new goal
`Goal.ensures R K_q`, whose return check maps $`K_q`$ into the return node:
the result to the returned value's slot, the receiver and each actual to a
slot still holding it, tracked by the edges as a promise goal's argument
slots are (`Goal.argument`); the frame by the declaration-effect check at
$`⟦\Phi⟧`$. `ensures_safe` (new) gives the judgment above, as
`goto_bounded` gives it for a footprint, and needs `goto_bounded` extended
from closed to region footprints.

**From the knowledge contract to the source contract.** The producer
proposes $`K_p`$ and $`K_q`$; neither is trusted. Two more checks bridge
them to $`p`$ and $`q`$:

```math
\frac{\vdash p:\mathsf{true}\Rightarrow K_p\qquad
      \models_K\{K_p\}\,f\,\{K_q\}[\Phi]\qquad
      K_q\vdash q:\mathsf{true}}
     {\models\{p\}\,f\,\{q\}[\Phi]}\ \textsf{contract}
```

1. $`\vdash p:\mathsf{true}\Rightarrow K_p`$ checks $`p`$'s code at a
   promise goal, each return of `true` holding $`K_p`$ of its receiver and
   parameters: `guard-def`
   ([user-defined guards](../SOURCE-ELABORATION.md#user-defined-guards);
   cited) with a knowledge in place of one parameter's type.
2. $`K_q\vdash q:\mathsf{true}`$ checks $`q`$'s graph at the result type
   `true` from entry knowledge $`K_q`$, its captures at their claimed types.

`contract_sound` (new) proves the rule by budgets chosen from the run.
Given a run of $`p`$ returning `true` in $`j`$ steps from $`h`$, a run of
$`f`$ reaching $`v,h'`$ in $`k`$ steps and a run of $`q`$ from $`h'`$ in
$`m`$ steps, take $`n>j+k+m`$; the entry premises hold at every budget.
Premise 1 at budget $`n`$ gives $`K_p`$ at $`p`$'s final heap $`h_p`$;
$`p`$ runs within the empty footprint, so $`h_p`$ extends $`h`$ and agrees
with it on $`h`$'s locations, and `back_holds` (new) carries $`K_p`$ back
to $`h`$: value facts and separation name no heap, cell facts and links
read locations of $`h`$, and helper atoms move by their supports (§4).
The knowledge contract at budget $`n`$ leaves a residual budget above
$`m`$ at $`v,h'`$, with $`K_q`$, a world $`W'`$ extending $`W`$ and
$`\mathrm{HeapOk}`$ there; premise 2 at that budget makes $`q`$'s run of
$`m`$ steps end in `true`. So no run of $`q`$ from $`h'`$ returns `false`.
A check of $`q`$ at one finite residual budget alone would state nothing
past it ([`SafePost`](../../lean/Verification/Semantics/HeapObservations.lean)
states nothing at budget zero); choosing the budget from the run is what
gives the unbounded statement.

A postcondition conditional on the result (`r === -1 ? A : B`) has
$`K_q`$ facts under an observation of the result slot, the form the
conditional yields of [a membership test](../PROGRAM-TYPING.md#a-membership-test)
take (cited).

| Theorem | Status |
| --- | --- |
| `accepted_entry_safe`, `GraphCode.goto_bounded`, `Post.compose` | proved; the second extends to `Goal.ensures` and region footprints |
| `HeapKnowledge.check_sound`, `checkIn_sound`, `expand_holds`, `checkStep_sound` | proved; each extends to the atoms of §4 |
| `yieldFollows_sound`, `promiseCall_sound` | proved; generalized to a knowledge promise |
| `ensures_safe`, `back_holds`, `contract_sound`, the guard and assertion embeddings | new |
| the atom lemmas of §4 (holds, shift, check, expansion, refinement, `support_sound`) | new |

## 4. The atoms

Today's value facts are, per kind, finite or cofinite sets of number bit
patterns, strings and bigints (proved definition: `ValueSet` in
[ValueSets.lean](../../lean/Verification/Semantics/ValueSets.lean)).
Contracts need four more atoms:

- **Order** $`x\lhd y`$, $`\lhd\in\{<,\le\}`$, between slots or a slot and a
  constant: both are numbers in IEEE order, neither NaN. It names only the
  environment, so it joins $`\Pi`$ and survives writes and calls, the
  argument the separation facts use (cited:
  [separation facts](../PROGRAM-TYPING.md#separation-facts)).
- **Integer** $`\mathsf{int}(x)`$: a safe integer, $`|x|\le 2^{53}-1`$. With
  it, a link $`r=x\oplus y`$ for $`\oplus\in\{+,-\}`$ gives exact difference
  bounds where the exact result is a safe integer, and $`r=x\ggg 1`$ gives
  $`2r\le x\le 2r+1`$ where $`0\le x<2^{32}`$ (outside that range the shift
  reduces modulo $`2^{32}`$: `2 ** 32 >>> 1` is `0`).
- **Element link** $`a[i]\mapsto y`$: reading `a` at index $`i`$ gives
  $`y`$, in $`\Sigma`$ beside the field read links.
- **Helper atom** $`g(\vec x)`$, established truth: the pure helper $`g`$
  returns `true` on the slots' values at the current heap; a value $`g`$
  captures is one of the atom's arguments, a slot holding it. The atom is
  introduced where a call of $`g`$ returned `true` (the call's true edge)
  or by a lemma instance (§5), and eliminated only through reification
  (§6) or a lemma's premise. A range atom $`\forall i\in[a,b).\ g(i,\vec x)`$
  is `forAll(a, b, …)` returning `true`, for safe-integer bounds.

**Support.** A helper atom survives a write or a call only by a **support
certificate**: a footprint $`S_g`$ over $`g`$'s arguments covering every
location of the entry heap that $`g`$'s run reads, its callees' reads
included, checked from its graph. `sorted(xs)` reads `xs`'s store location
(its length and element list) and its element cells, so
$`S=\{\mathsf{field}(xs,\texttt{[]}),\mathsf{elems}(xs)\}`$. A run may also
allocate (the empty footprint constrains only the entry heap's locations)
and read what it allocated; those reads need no certificate. `support_sound`
(new) preserves Boolean truth: if $`h_1`$ and $`h_2`$ agree on $`S_g`$ read
at $`h_1`$ and $`g`$ returns `true` from $`h_1`$, it returns `true` from
$`h_2`$. Its proof relates the two runs by the bijection of their fresh
locations (allocation appends at the heap's end in both), so reads of
fresh locations correspond, and compares only the Boolean result, which
holds no location. `Footprints.Supported` with `keep` entries (proved
definition) states the agreement, so a write or a call whose footprint
keeps $`S_g`$ keeps the atom.

**Rules.** A comparison is typed at `true` or `false` where order atoms
decide it (beside `arith`, whose result is never a singleton; cited:
[operators](../PROGRAM-TYPING.md#operators)); a comparison's branch edges add
its outcome, the false edge $`\neg(x<y)`$, which gives $`y\le x`$ only with
both non-NaN, as [refinement under an observed outcome](../PROGRAM-TYPING.md#refinement-under-an-observed-outcome)
adds a tag's outcome; ranges of one helper join
($`[a,c)\cup[c',b)\supseteq[a,b)`$ where $`c'\le c`$).

**Numbers.** The calculus computes number comparison (`doubleOrder`) and
`+`, `-`, `*`, `/` (`arithBits`) with Lean's `Float`. In the pinned
toolchain (Lean 4.33.1) `Float` is a structure over `Float.Model`, a
subtype of `UInt64`, and `Float.add`, `sub`, `mul`, `div`, `lt`, `le`,
`beq`, `ofBits` and `toBits` are defined through the model, each compiled
to its C operation (cited: `Init/Data/Float/Float.lean` and
`Init/Data/Float/Model/Float.lean` of that toolchain). The order and
arithmetic laws the atoms need are therefore theorems to prove about the
model: totality and transitivity of the order on non-NaN values, the
exactness of `+` and `-` on safe integers with a safe result, and the
negation laws of the comparisons under NaN. Two correspondences need an
audit beside the proofs. The model's `ofBits` canonicalizes every NaN, so
`toBits ∘ ofBits` is the identity on non-NaN bits only; a rule reading a
result's bits states its NaN case. The checker runs compiled: an executable
check computing an operation runs the C operation, which the logic equates
to the model by the `extern` attribute, a trusted step of every compiled
check. Test vectors against Node observe that correspondence; they prove
nothing.

## 5. Proof routes and acceptance

**The automatic route.** The producer proposes $`K_p`$, $`K_q`$, each node's
knowledge and each loop head's assertion; the search and the checker work
as today. An `invariant` closure is a **hint**: the producer reads it as
the assertion of the loop's cut, which every incoming edge proves (cited:
[supplied point claims](../PROGRAM-TYPING.md#supplied-point-claims-and-incoming-edges)).
It has no part in §1 or §3, so a wrong or misplaced invariant fails
verification. Decided automatically: nullness and shapes, equalities,
orders and integer bounds, and helper atoms carried by their supports or
joined by ranges.

**Lemmas.** A lemma `lemma(name, h)` claims that its predicate returns
`true` on every argument meeting its parameters' types: established truth,
so its instances introduce helper atoms. A lemma is written as an
implication, `!(premises) || conclusion`; an instance adds the
conclusion's atom where the knowledge holds the premises' atoms
(`instance_sound`, new). Its meaning is a reified formula (§6),

```math
\mathrm{Valid}(\varphi)\iff\forall\vec c\in\vec C,\ \vec v\in\vec A,\ h.\ \exists k.\ \exists h'.\ \mathrm{eval}_k(\varphi,h,\vec c,\vec v)=(\mathsf{ret}\ \mathsf{true},h')
```

over heaps meeting their contracts, with $`\vec A`$ the parameters' types
and $`\vec C`$ the claimed types of the predicate's captured values, which
are variables of $`\varphi`$ bound symbolically: an instance binds them to
the capture values of the closure the check runs, which meet those types.
The proof is a Lean theorem in a proofs library linked into the verifier,
entered in one registry constant the checker reads:

```lean
structure LemmaProof where
  name : String
  key : LemmaKey     -- the comparison key below
  valid : key.formula.Valid
```

The **comparison key** is the formula with the reified bodies of every
helper it calls, transitively; the parameter and capture types it
assumes; and the identity of every native value contract its reification
uses. At check time the verifier reifies the source's lemma again and
accepts the entry with an equal key (`DecidableEq`), so an edit of a
helper, a type or a native contract reports the proof stale by name, and an
edit of a program using the lemma leaves it valid. A lemma's proof is a
closed Lean theorem and cannot rest on the registry or on a contract.

**Request-level proofs.** Where knowledge cannot carry the reasoning, a
registered Lean proof of the knowledge contract of §3 for one request,
keyed `file#function:signature`, is accepted where the lowered request
equals the registered one; every edit of the function makes it stale. This
is the CFML style: characteristic formulae proved by hand over the
program.

**Acceptance.** A contract adds a plan constructor, `CertifiedPlan.spec`,
holding the unit's request at `Goal.ensures`, $`p`$'s and $`q`$'s requests,
the frame and the registry entries used, and leaves the unit's ordinary
`CertifiedPlan.graph` in place, so a document with a contract certifies
both the unit's unconditional safety and its contract
([acceptance/soundness invariant](../../AGENTS.md#acceptancesoundness-invariant)).
`FunctionPlan.certify` converts it exhaustively, and `DocumentSafe` gains
one conjunct stating both the knowledge contract and, by
`contract_sound`, the source contract.

Two integration obligations come with it:

- **Inventory.** `DocumentSafe` quantifies over the extracted plans, so
  exhaustive conversion cannot show a contract missing from them. A
  registration statement is an ordinary call, which stays in the Fragment
  as part of the lowered program; extraction inventories every call whose
  callee is the binding of `spec`, `invariant` or `lemma` and requires
  exactly one plan or a located refusal for each. Which declaration a name
  binds to stays the parser's trusted name resolution.
- **Axioms.** The registry's proofs are covered by
  [AxiomCheck.lean](../../lean/Verification/Tests/AxiomCheck.lean), which
  checks the axioms `checkUnitJson_safe` depends on, only once the checker's
  soundness proof uses each entry's `valid` field, so that the registry
  constant is in that dependency closure. A control adds an entry resting
  on a project axiom and requires the build to fail.

Controls (`pipeline/test.mts`): forged $`K_p`$ and $`K_q`$, refused at the
edge and the return; a contract attached to another function or signature,
refused by the match; a registration call without a plan, refused by the
inventory; a stale lemma after a helper edit; a registry entry with a
different key; the axiom control above.

## 6. Pure helpers and reification

A helper is a function whose signature states the empty footprint in
place; by `Step_det` its run is a function of its receiver, actuals and
heap. **Reification** reads a helper's checked graph into a functional
language $`\mathsf{PExpr}`$: constants, parameters, `let`, conditionals,
the operators, field and element reads, lambdas with their free variables
(closure conversion of a callback such as `forAll`'s), calls of reified
helpers in mutually recursive groups, and natives with a value-level
contract. Its evaluator threads the heap, so a native's fresh result is a
location of the returned heap and later reads see it:

```math
\mathrm{eval}_k(e,h,\vec c,\vec v)\in\{\mathsf{ret}\ w,\ \mathsf{throw}\ w,\ \mathsf{out}\}\times\mathrm{Heap}
```

with the exact correspondence

```math
\mathrm{reify}(G)=\mathsf{some}\ e\ \Longrightarrow\
\bigl(G(\vec v)\Downarrow_h w\ \text{ending in}\ h'\iff\exists k.\ \mathrm{eval}_k(e,h,\vec c,\vec v)=(\mathsf{ret}\ w,h')\bigr)
\qquad(\texttt{reify\_sound},\ \text{new})
```

and likewise for throws. Native value contracts state a result and the
heap it returns (`Object.keys` a fresh array of the own string keys,
`Number.isInteger` a Boolean and the heap unchanged); each is a reviewed
host row (§8). A graph allocating anything but a closure or a native's
fresh result, or running a loop other than `forAll`'s, is not reified.
`forAll` is reified as the bounded quantifier over the integers of
$`[\mathit{from},\mathit{to})`$ for safe-integer bounds, proved once from
its graph: `i++` stays exact below $`2^{53}`$, so the loop visits each
integer once and stops. The pipeline prints each reified helper as a Lean
definition with a lemma unfolding $`\mathrm{eval}`$ to it. This is
Aeneas's functional translation (Rust to pure Lean) with the translation
proved once and run at each check.

## 7. Examples

### Pure: `clamp`

```ts
export function clamp(x: number, lo: number, hi: number): number {
  if (x < lo) return lo;
  if (x > hi) return hi;
  return x;
}
```

with the contract of §2. $`K_p=\{lo\le hi,\ x\le x\}`$, the second atom
stating that $`x`$ is not NaN. At `return lo` the result aliases $`lo`$ and
$`lo\le hi`$ holds; at `return hi` likewise; at `return x` the false edges
of `x < lo` and `x > hi` give $`lo\le x\le hi`$, no operand being NaN.
$`K_q=\{lo\le r,\ r\le hi\}`$ types both comparisons of `ensures` at
`true`. The route is automatic, infinities included. Without `x === x` the
contract is false: `clamp(NaN, 0, 1)` returns `NaN`, for which `ensures` is
`false` (observed under Node 25.2.1, 2026-10-28, and Node 26.13.0,
2026-11-05); no order atom holds of
$`x`$ at the third return. A positive and a negative case show both.

### Loop: binary search

```ts
export function search(xs: readonly number[], x: number): number {
  let lo = 0;
  let hi = xs.length;
  while (lo < hi) {
    invariant(() => 0 <= lo && lo <= hi && hi <= xs.length &&
      forAll(0, lo, (i) => xs[i] !== x) && forAll(hi, xs.length, (i) => xs[i] !== x));
    const mid = lo + ((hi - lo) >>> 1);
    const y = xs[mid];
    if (y === x) return mid;
    if (y < x) lo = mid + 1;
    else hi = mid;
  }
  return -1;
}
spec(search, {
  requires: (xs: readonly number[], x: number) => sorted(xs),
  ensures: (r: number, xs: readonly number[], x: number) =>
    r === -1 ? forAll(0, xs.length, (i) => xs[i] !== x) : 0 <= r && r < xs.length && xs[r] === x,
});
```

`sorted(xs)` is `forAll(0, xs.length - 1, (i) => xs[i] <= xs[i + 1])`. For
an array of two or more elements it excludes holes and NaN, each of which
makes a comparison false; for one element it holds whatever the element.
The invariant states `!==`: with `x` NaN every comparison is false, and
`!==` is what the loop keeps. The lemmas, over a safe integer `m`:

```ts
lemma("sorted-below", (xs: readonly number[], m: number, x: number) =>
  !(sorted(xs) && Number.isInteger(m) && 0 <= m && m < xs.length && xs[m] < x) ||
  forAll(0, m + 1, (i) => xs[i] !== x));
lemma("sorted-above", (xs: readonly number[], m: number, x: number) =>
  !(sorted(xs) && Number.isInteger(m) && 0 <= m && m < xs.length && xs[m] !== x && !(xs[m] < x)) ||
  forAll(m, xs.length, (i) => xs[i] !== x));
```

`sorted-below`: `xs[m] < x` makes both numbers and not NaN, and every
`xs[i]` with $`i\le m`$ is at most `xs[m]` by sortedness, so below `x`.
`sorted-above`, by cases: `x` NaN, where every `!==` holds; one element,
where the range is $`\{m\}`$ and `xs[m] !== x` is a premise; otherwise
`xs[m]` is a number, not NaN, not below `x` and not `x`, so above it, and
every later element is at least `xs[m]`. Their reification needs the value
contract of `Number.isInteger`.

| Obligation | Discharged by |
| --- | --- |
| invariant on entry | automatic: `lo = 0`, `hi = xs.length`, empty ranges |
| `lo ≤ mid < hi` | automatic: integer atoms; `xs.length` is an integer below $`2^{32}`$ (cited: ECMA-262's array length bound; the array contract must state it), so `0 ≤ hi - lo < 2^32` and the `>>>` rule applies |
| `return mid` meets the `r !== -1` arm | automatic: the element link $`xs[mid]\mapsto y`$ and the true edge of `y === x` |
| preserved by `lo = mid + 1` | the instance of `sorted-below` at `m = mid` |
| preserved by `hi = mid` | the instance of `sorted-above` at `m = mid` |
| `return -1` meets the `r === -1` arm | automatic: the false edge of `lo < hi` gives `hi ≤ lo`, and the ranges join |
| `sorted(xs)` at every node | its support, `xs`'s store and elements, kept: the body writes nothing and calls only functions stating the empty footprint |

A Lean proof of `sorted-below`, as pseudocode over the reified helpers and
the model's order (`DLt`, `DLe`):

```lean
theorem sorted_below : (lemma% "sorted-below").Valid := by
  intro xs m x ⟨hs, hint, hm0, hm, hlt⟩ i hi
  have hle : DLe (xs.get i) (xs.get m) := hs.le_of_le (Nat.lt_succ_iff.mp hi) hm
  exact (DLe.lt_of_le_of_lt hle hlt).ne
```

### Round trip: a wire decoder of TScert

`isCallEffect` in [`tools/type-graph.mts`](../../tools/type-graph.mts) is
the type guard decoding a call effect from a parsed JSON value; the front
end writes the value with `JSON.stringify`. The round trip is a contract of
a two-line function:

```ts
export function callEffectRoundTrip(e: JsonValue): Json {
  return JSON.parse(JSON.stringify(e));
}
spec(callEffectRoundTrip, {
  requires: (e: JsonValue) => isCallEffect(e),
  ensures: (back: Json, e: JsonValue) => isCallEffect(back) && jsonEqual(back, e),
});
```

The parameter is a `JsonValue` because `JSON.stringify` is read at
`JsonValue` alone (cited: [`JSON` and `Error`](../SOURCE-CONTRACTS.md#json-and-error)).
`jsonEqual(a, b)` holds where both are primitives equal by `===`, both
arrays of one length with elements pairwise `jsonEqual`, or both
non-array objects with one set of own string keys and values pairwise
`jsonEqual`. The proof:

1. **Host contract** (trusted, a new row): on a normal return,
   `JSON.parse(JSON.stringify(v))` for a `JsonValue` $`v`$ whose numbers
   are finite is `jsonEqual` to $`v`$, and an object or array result is
   fresh (cited: [ECMA-262](../REFERENCES.md#ecma-262), `JSON.stringify`
   and `JSON.parse`; to be tested under Node). A cyclic `JsonValue`, which
   the existing contract admits, makes `JSON.stringify` throw, which the
   contract's normal-return reading excludes.
2. **Finiteness**: under `isCallEffect(e)` the only number is the promise's
   `param`, an integer.
3. **Congruence** (a lemma): `isCallEffect` returns one answer on
   `jsonEqual` arguments. Its reified form needs value contracts for
   `Object.keys` and `Number.isInteger`, beside `typeof`, `in`, `===` and
   `>=`, and the proof goes through each read: own-key counts agree because
   the key sets do, and `-0` and `0` give the same answers.

Two weaker statements are false (observed under Node 25.2.1,
2026-10-28, and Node 26.13.0, 2026-11-05): equality by `Object.is` fails at `param: -0`, which comes
back `0`; and without the precondition, a `CallEffect` holding an own
`asserts: undefined`, which its type admits, comes back without the key.

## 8. Trust

A proved contract states §1 and §3 of the lowered graph and the lowered
predicates. Its trust differs from a type claim's in three ways.

- **Value faithfulness becomes load-bearing.** The function and its
  predicates pass through the same trusted front end and extraction, so
  an error both share (a misread operator, an assignment to the wrong
  slot) can make a false source property proved. A type claim is
  sensitive to errors that change types, a contract to every error that
  changes values. The part most needing its own proof is extraction's data
  flow for the forms contracts use (`let` and assignment, loops, `if`,
  `return`, the operators, element reads):
  [option (3)](../TRUST-REDUCTION.md#options-cheapest-first) of trust
  reduction, the open row
  [a semantics of the Fragment](../../WORK.md#a-semantics-of-the-fragment).
- **Attachment and completeness are new obligations.** That a `spec`
  statement belongs to the unit and signature it names rests on the
  declaration TypeScript binds `f` to, then on the checked signature match
  and the predicates' closure environments; that every registration
  statement reaches a plan rests on the inventory of §5 over the
  Fragment's calls, with the binding of `spec` from the parser's trusted
  name resolution. Which program point a claim attaches to stays unproved
  ([trust surface](../DESIGN.md#trust-surface)) and adds nothing here: the
  knowledge contract attaches at the request's entry and return
  continuations, which Lean builds, and invariants are hints.
- **Host value contracts are new rows**: a native's value-level behaviour
  (the JSON round trip, `Object.keys`, `Number.isInteger`), each with its
  Node test, beside today's type-level rows; and the `extern`
  correspondence of compiled `Float` operations to the model (§4).

## Decisions for the owner

1. **Where contracts live.** `spec(f, {...})` in $`f`$'s module, or a
   sibling `.spec.ts` module. Recommendation: $`f`$'s module, so a certified
   import brings its contract and one parse reads both.
2. **Signature selection by written parameters**, receivers as `this:`;
   generic and overloaded signatures refused until the work of §2.
   Recommendation: yes; `Parameters<F>` loses overloads and generic
   relations (cited: TypeScript's utility types documentation).
3. **Predicate effects from the contract plan**: the reader claims each
   predicate at its written signature with the empty footprint.
   Recommendation: yes.
4. **Callers consume the knowledge contract**, never the source contract;
   contracts of imports only through certified imports. Recommendation:
   yes.
5. **Weak postconditions, strong preconditions and lemmas.**
   Recommendation: yes.
6. **Number laws from `Float.Model`**, with the NaN and compiled-operation
   audit. Recommendation: yes, the order laws first.
7. **Verdicts.** A contract is a plan beside the unit's ordinary plan; the
   document is verified only when every plan is. Recommendation: yes.
8. **Manual proofs.** Lemmas over reified helpers in one registry constant
   linked into the verifier (an external project builds its verifier from
   TScert's library and its proofs); request-level proofs of the knowledge
   contract as the fallback. Recommendation: lemmas first.
9. **Invariants are hints.** Recommendation: yes.
10. **Host value contracts** for natives a case needs, each a reviewed row
    with a Node test. Recommendation: yes, `Number.isInteger`, `JSON` and
    `Object.keys` first.
11. **Stated limits:** old values, nested frames, generic and overloaded
    signatures. Old values need a two-state predicate over the entry and
    final heaps with a snapshot's allocation and aliasing defined.
    Recommendation: keep them refused until a case needs one.

## Order of work

1. Predicate foundations: the signature match, the predicates' claims at
   the empty footprint, support certificates and `support_sound`, region
   frames.
2. The knowledge contract and acceptance: `Goal.ensures`, `ensures_safe`,
   `back_holds`, `contract_sound`, `CertifiedPlan.spec`, the `DocumentSafe`
   conjunct, the inventory and the controls of §5.
3. The `Float.Model` order laws, order atoms with their rules, and the
   `clamp` cases, positive and negative, with the Node run.
4. Calls of contracted signatures through the knowledge contract, and the
   guard and assertion embeddings.
5. Integer atoms, element links, helper and range atoms; the value contract
   of `Number.isInteger`; reification, `reify_sound`, the lemma registry and
   its axiom control; the binary search cases.
6. Host value contracts for `JSON` and `Object.keys`; the round-trip case.
7. Extraction's data flow proved (the Fragment semantics row), starting
   with the forms the cases use.
