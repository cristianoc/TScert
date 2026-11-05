# Recursive generic types as equations

Generic declarations such as TypeScript's `Promise` define infinite families
of types that no finite type graph can present. Here each declaration is a
parameterized type definition, a type is a finite term that may apply a
definition to arguments, and a check unfolds an application one step when
it reads it. Types mean what the step-indexed semantics of
[SEMANTICS](SEMANTICS.md) and [POSITIVE-TYPES](POSITIVE-TYPES.md) says.
Members of a family are related by substitution, for instantiation, and by
parametric assumptions, for subtyping.

The Lean mechanization (section 8) covers sections 2, 3 and 4.1, and 4.2
with instance hypotheses discharged by table pairs, subsets and hypotheses.
The checker validates equation well-formedness and subtype derivations.
The interpretation of source declarations in section 5 is trusted.

## 1. The problem

A finite type graph presents a *regular* type: finitely many distinct
types, recursion by reference back to a node. Many generic types are
regular at each instance: `List<number>` mentions only `List<number>` and
`number`. Others are not:

```ts
interface Promise<T> {
  then<R>(f: (x: T) => R): Promise<R>;
  catch<R>(f: (e: unknown) => R): Promise<T | R>;
}
```

Unfolding `Promise<number>` reaches `Promise<number | R>` through `catch`,
whose own `catch` reaches `Promise<number | R | R′>`, and so on. Every member
mentions a larger one, so the unfolding has infinitely many distinct
subtrees. Such definitions are *non-regular*
([Solomon 1978](REFERENCES.md#solomon-1978)). A presentation that enumerates
instances must stop somewhere. Past a budget it can only refuse the
declaration, since reading the tail as `unknown` would be unsound.

The semantics admits infinitely many nodes: a type's meaning is a guarded
fixed point. What must be finite is what a check inspects. So each member is named by a
finite term, its structure is computed on demand, and members are related
by rules that inspect finitely many unfoldings.

## 2. Type definitions

### 2.1 Syntax

Types are the positive types of [POSITIVE-TYPES](POSITIVE-TYPES.md), with
type variables $`\alpha,\beta`$, applications of definitions, and
intersections:

```math
\tau \;::=\; \alpha \;\mid\; D\langle\tau_1,\ldots,\tau_n\rangle \;\mid\; c(\tau_1,\ldots,\tau_k) \;\mid\; \tau\lor\tau \;\mid\; \tau\land\tau \;\mid\; \bot
```

Here $`c`$ ranges over the constructors of the positive language: records,
arrays, functions with their signatures, primitives. A signature may be
quantified, $`\forall\vec\beta\le\vec\rho.\,\sigma`$, which binds
$`\vec\beta`$ in $`\sigma`$.

A **program of definitions** is a finite set of equations

```math
D\langle\alpha_1,\ldots,\alpha_n\rangle \;=\; \tau_D ,
```

one for each name $`D`$, where $`\mathrm{fv}(\tau_D)\subseteq\{\vec\alpha\}`$
and $`\tau_D`$ is *contractive*: a constructor $`c(\ldots)`$, a union of
constructors, or a quantified signature.
Definitions may refer to each other and to themselves, at any arguments.
`Promise` is

```math
\mathit{Promise}\langle\alpha\rangle=\{\ \mathit{then}:\forall\beta.\,(\alpha\to\beta)\to\mathit{Promise}\langle\beta\rangle,\ \ \mathit{catch}:\forall\beta.\,(\top\to\beta)\to\mathit{Promise}\langle\alpha\lor\beta\rangle\ \}.
```

### 2.2 Meaning

An application unfolds to its definition's body at its arguments:

```math
⟦D\langle\vec\tau\rangle⟧^\eta \;=\; ⟦\tau_D[\vec\tau/\vec\alpha]⟧^\eta ,
```

with capture-avoiding substitution, and $`\eta`$ assigning meanings to free
variables. Contractiveness makes this a guarded definition: an application
in the body sits under a constructor, whose operands are read at a lower
step. So the step-indexed fixed point exists, and it is the verifier's
semantics. One unfolding substitutes into a finite body
and leaves the applications in it unexpanded, so a check pays only for the
unfoldings it performs. The family `Promise` has infinitely many members,
but every member a check reaches is a finite term.

An intersection means exactly the intersection of its operands,
$`⟦\tau\land\sigma⟧^\eta=⟦\tau⟧^\eta\cap⟦\sigma⟧^\eta`$. It must: once
$`\alpha\land\rho`$ appears in a body, substitution can put any type for
$`\alpha`$. The lemmas of section 3 require meaning to commute with
substitution, which fixes the intersection of the operands as the only
admissible reading.

## 3. Metatheory

Three lemmas let a check work on finite terms while the meaning is a fixed
point over infinitely many unfoldings. Each holds for values and argument
lists alike.

**Lemma 1 (support).** If $`\eta`$ and $`\theta`$ agree on
$`\mathrm{fv}(\tau)`$, then $`⟦\tau⟧^\eta=⟦\tau⟧^\theta`$.

**Lemma 2 (congruence).** If $`⟦\tau_i⟧^\eta=⟦\sigma_i⟧^\theta`$ for every
$`i`$, then $`⟦D\langle\vec\tau\rangle⟧^\eta=⟦D\langle\vec\sigma\rangle⟧^\theta`$.

*Proof sketch.* By induction on the step index $`n`$. Constructors read
their operands below $`n`$, and the operands are the body's subterms at the
two argument lists, equal by the induction hypothesis. Quantified signatures
compare their instances pairwise; argument lists at $`n`$ use the values
just established at $`n`$. The two environments may differ, which is what
lets the lemma relate two applications that bind their quantifiers
separately. $`\square`$

**Lemma 3 (substitution).** $`⟦\tau⟧^{\eta[\vec\alpha\mapsto⟦\vec\sigma⟧^\eta]}=⟦\tau[\vec\sigma/\vec\alpha]⟧^\eta`$
for simultaneous, capture-avoiding substitution at matching kinds.

*Proof sketch.* By structural induction on the finite term $`\tau`$: an
application is handled by Lemma 2, and intersection distributes over the
unions substituted into it. Substitution traverses only the finite term.
$`\square`$

Lemma 3 makes instantiation checkable: a call instantiates a generic
signature by substituting into its finite syntax, and the checker recomputes
that substitution, or checks a proof that a named image is equal to it. The
checker and its soundness proofs, expression typing
and control flow included, are stated over an interface: an image check with
a proof that it computes correct images. Substitution is one instance of it,
and the closure check of a finite table another. The interface also carries
inclusions already proved in the graph, each with its proof at every
parameter assignment; a comparison of one of them is established without
comparing (`InstanceImageCheck.known`, `compareUsing_sound`). The check of a
document holds none; the producer's own checks hold those its search
established.

## 4. Subtyping

Subtyping between recursive types is checked coinductively. A certificate
supplies a finite set of assumed pairs. The checker verifies that each
pair's structure is covered, reading the pairs themselves for the operands,
one step lower
([Amadio and Cardelli 1993](REFERENCES.md#amadio-and-cardelli-1993),
[Brandt and Henglein 1998](REFERENCES.md#brandt-and-henglein-1998),
[POSITIVE-TYPES](POSITIVE-TYPES.md#covered-pairs)). For a non-regular family
the needed set is infinite, since
`Promise<number> ≤ Promise<number | string>` needs
`Promise<number | β> ≤ Promise<number | string | β>` for `catch`, then a
pair with one more bound variable, without end. The pairs differ only in
their arguments, so the assumptions are made parametric.

**Soundness, not completeness.** The rules below are sound for the semantic
inclusion, and no sound checker can be complete for it: inclusion is
undecidable, and not recursively enumerable, already for definitions with
readonly fields whose arguments grow. On readonly records, inclusion is
simulation of the unfoldings, which encodes inclusion of simple languages
([Friedman 1976](REFERENCES.md#friedman-1976)); non-inclusion is
semi-decidable, level by level. The argument is on paper, not mechanized.

**A decidable fragment.** On readonly records, inclusion is decidable when
one side is regular, its unfolding reaching finitely many types. Every
subtyping question in the examples either has this form or relates two
applications of one definition, decided by $`\textsf{Var}`$. The argument
abstracts each argument of the other side by the set of the regular side's
types it is below, which leaves finitely many states for a greatest
fixpoint; it rests on inclusion being simulation. It is on paper, and its
extension to functions and writable fields is open.
We conjecture the fragment is EXPTIME-complete in the size of the program
and of the regular side's unfolding: that procedure is exponential in it,
and simulation between pushdown and finite-state processes
([Kučera and Mayr 2010](REFERENCES.md#kučera-and-mayr-2010)) reduces to it.
The checker therefore decides these questions by $`\textsf{Var}`$ and the
coinductive fallback, which close every question the examples pose.
We further conjecture that on the examples this work is linear per question
in the size of the types compared. On the pipeline cases the ratio of
$`\textsf{Inst}`$ steps to size is at most 8.2 over the 169 questions the
check step asks (measured October 2026),
which is consistent with a linear bound but does not establish one. The
steps are not one per argument: five questions of size 5 to 8 take 19 to 48
steps, all by $`\textsf{Var}`$, while variances of components of 8 to 36
members are computed. The measurement covers the checker's questions and
the fallback searches, not the producer's proof search.

The source-value universe $`J`$ also supports the checked intersection rule:

```math
A\subseteq J\quad\Longrightarrow\quad P\cap A\subseteq P\cap J.
```

Clause shapes establish $`A\subseteq J`$ (`sourceClause_sound`); the
intersection rule is proved by `meetBelow_sound`. A quantified callable is
also contained in $`J`$, since its semantics requires an invocable object
(`OpaqueUniverse`, `pair_values_sound`). Internal parameter families remain
unrestricted until a bound or intersection supplies this premise.

The same premise gives $`A\subseteq A\cap J`$. The checked source-membership
test recognizes clause restrictions and quantified callables
(`sourceTy_sound`); `meet_target_value` proves intersection introduction.

### 4.1 Quantified signatures

Two quantified signatures are compared up to renaming of bound variables,
with the target's quantifiers rigid and bounds compared contravariantly:

```math
\frac{\vec{\rho}'\le\vec\rho\qquad \sigma\le\sigma'[\vec\alpha/\vec\beta]\qquad \vec\alpha\notin\mathrm{fv}(\forall\vec\beta.\,\sigma')}
{\forall\vec\alpha\le\vec\rho.\,\sigma\ \le\ \forall\vec\beta\le\vec{\rho}'.\,\sigma'}
```

This is the kernel rule of F<: restricted to one fixed pairing of
quantifiers, which is decidable
([Pierce 1994](REFERENCES.md#pierce-1994)). Soundness is Lemma 3: an instance
of the source at $`\vec X`$ within $`\vec{\rho}'`$ is an instance of the
target at the same $`\vec X`$.

### 4.2 Parametric assumptions

An **assumption** $`a`$ is a constrained judgment with a finite table
$`T_a`$ of pairs over its variables:

```math
a\;=\;\forall\vec\alpha\vec\beta.\ \Pi_a\Rightarrow D\langle\vec\alpha\rangle\le D'\langle\vec\beta\rangle ,
```

where $`\Pi_a`$ is a finite set of hypotheses $`\gamma\le\delta`$ between
its variables. A plain pair is an assumption without variables. Fix a set
$`\mathcal A`$ of assumptions. Types are taken as unions of atoms
(variables, applications, constructors, intersections); $`l`$ ranges over
atoms and $`A,B`$ over unions.

**Premises.** An operand comparison is read by the judgment
$`\Pi;T\vdash A\sqsubseteq B`$:

```math
\frac{(A,B)\in T}{\Pi;T\vdash A\sqsubseteq B}\ \textsf{Tab}
\qquad
\frac{\forall l\in A.\ \ \Pi;T\vdash l\sqsubseteq B}{\Pi;T\vdash A\sqsubseteq B}\ \textsf{Union}
\qquad
\frac{l\in B}{\Pi;T\vdash l\sqsubseteq B}\ \textsf{Mem}
```

```math
\frac{(A',B')\in T\qquad (A,B)=(A',B')\rho\ \ \text{for a renaming}\ \rho\ \text{of bound variables}}{\Pi;T\vdash A\sqsubseteq B}\ \textsf{TabRen}
```

```math
\frac{(\gamma\le\delta)\in\Pi\qquad \delta\in B}{\Pi;T\vdash\gamma\sqsubseteq B}\ \textsf{Hyp}
\qquad
\frac{(\gamma\le\delta)\in\Pi\qquad \delta\land\rho\in B}{\Pi;T\vdash\gamma\land\rho\sqsubseteq B}\ \textsf{MeetHyp}
```

```math
\frac{\forall\vec\alpha\vec\beta.\ \Pi_a\Rightarrow D\langle\vec\alpha\rangle\le D'\langle\vec\beta\rangle\ \in\mathcal A\qquad D'\langle\vec\sigma\rangle\in B\qquad \forall(\gamma\le\delta)\in\Pi_a.\ \ \Pi;T\vdash\gamma\theta\sqsubseteq\delta\theta}
{\Pi;T\vdash D\langle\vec\tau\rangle\sqsubseteq B}\ \textsf{Inst}
```

where $`\theta=[\vec\tau/\vec\alpha,\vec\sigma/\vec\beta]`$. The premises of $`\textsf{Inst}`$
compare $`\vec\tau`$ and $`\vec\sigma`$, strict subterms of its conclusion,
so derivations are finite and the judgment is decidable. $`\textsf{TabRen}`$
reuses a pair at renamed bound variables: hypotheses mention no bound
variable, and Lemma 3 makes the renamed pair an instance.

**Covering.** A pair is covered, $`\Pi;T\vdash A\le B`$, when every clause
of $`A`$'s one-step unfolding is covered by a clause of $`B`$'s, under the
[clause coverage rules](POSITIVE-TYPES.md#clause-coverage) with their
operand premises read by $`\sqsubseteq`$, and every variable of $`A`$ is in
$`B`$ or below a member of $`B`$ by a hypothesis. Quantified signatures are
compared by 4.1.

**Validity.**

```math
\frac{\forall(A,B)\in T_a\cup\{(D\langle\vec\alpha\rangle,D'\langle\vec\beta\rangle)\}.\ \ \Pi_a;T_a\vdash A\le B}
{\vdash a\ \mathsf{valid}}\ \textsf{Valid}
```

**Theorem 1.** Let every assumption of $`\mathcal A`$ be valid. Write
$`\eta\models_n\Pi`$ when every hypothesis of $`\Pi`$ holds at $`\eta`$ at
every step up to $`n`$. For every $`a\in\mathcal A`$, every $`n`$ and every
$`\eta\models_n\Pi_a`$, the conclusion of $`a`$ and every pair of $`T_a`$
hold at $`\eta`$ at step $`n`$.

*Proof sketch.* By strong induction on $`n`$, values before argument lists,
with an inner induction on the derivation of each premise.
- A premise is read below $`n`$. $`\textsf{Tab}`$ holds there by the outer
  induction, $`\textsf{TabRen}`$ by it and Lemma 3, $`\textsf{Mem}`$ and
  $`\textsf{Union}`$ outright, and $`\textsf{Hyp}`$ and $`\textsf{MeetHyp}`$
  by $`\eta\models_n\Pi`$.
- $`\textsf{Inst}`$ is the conclusion of its assumption at
  $`\eta'=\eta[\vec\alpha\mapsto⟦\vec\tau⟧^\eta,\vec\beta\mapsto⟦\vec\sigma⟧^\eta]`$.
  Its hypotheses hold there because their instances are premises, which
  hold by the inner induction. So the outer induction applies at
  $`\eta'`$, and Lemma 3 turns the conclusion into
  $`D\langle\vec\tau\rangle\le D'\langle\vec\sigma\rangle`$ at $`\eta`$.
  Substitution is simultaneous, so an assumption may be used at its own
  variables, as `catch` does.
- Quantified signatures reassign bound variables only, and hypotheses
  mention none.
- Argument lists read element contracts at step $`n`$ itself. An instance
  there has its hypotheses only for values at $`n`$, so the theorem is
  proved together with a variant whose hypotheses hold below $`n`$ and, at
  $`n`$, for values.

$`\square`$ With no variables this is the existing theorem for finite
tables.

### 4.3 Variance

A **variance assignment** $`V`$ gives each parameter $`i`$ of each
definition $`D`$ a variance $`V_D(i)`$ in the lattice

```math
\mathsf{none}\ <\ \mathsf{co},\ \mathsf{contra}\ <\ \mathsf{inv} ,
```

where lower is the stronger claim. It stands for the assumptions, with
empty tables,

```math
a_{D}^{V}\;=\;\forall\vec\alpha\vec\beta.\ \Pi_D^V\Rightarrow D\langle\vec\alpha\rangle\le D\langle\vec\beta\rangle,
\qquad
\Pi_D^V=\{\alpha_i\le\beta_i\mid V_D(i)\in\{\mathsf{co},\mathsf{inv}\}\}\cup\{\beta_i\le\alpha_i\mid V_D(i)\in\{\mathsf{contra},\mathsf{inv}\}\}.
```

An invariant position has two variables related both ways. With
$`\mathcal A_V=\{a_D^V\}_D`$:

```math
\frac{\forall D.\ \ \mathcal A_V\vdash a_D^V\ \mathsf{valid}}{V\ \mathsf{valid}}\ \textsf{VarValid}
\qquad
\frac{V\ \mathsf{valid}\qquad \forall i.\ \ \tau_i\le\sigma_i\ \ (V_D(i)\in\{\mathsf{co},\mathsf{inv}\})\qquad \sigma_i\le\tau_i\ \ (V_D(i)\in\{\mathsf{contra},\mathsf{inv}\})}
{D\langle\vec\tau\rangle\le D\langle\vec\sigma\rangle}\ \textsf{Var}
```

$`\textsf{Var}`$ is sound by Theorem 1 and Lemma 3: its conclusion is an
instance of $`a_D^V`$.

**Computation.** The checker computes $`V`$ for the definitions a check
compares, once per definition:
1. Order the definitions by the strongly connected components of the
   reference graph ($`D\to E`$ when $`E`$ occurs in $`\tau_D`$), dependencies
   first.
2. For a component, set each member's candidate to the least fixpoint of
   the polarity equations
   $`V_D(i)=\bigsqcup\{\mathrm{pol}(o)\mid o\ \text{an occurrence of}\ \alpha_i\ \text{in}\ \tau_D\}`$,
   with $`\mathsf{none}`$ for no occurrence. $`\mathrm{pol}(o)`$ is
   $`\mathsf{co}`$ under results and readonly positions, $`\mathsf{contra}`$
   under parameters, and $`\mathsf{inv}`$ under writable fields, cells,
   mutable elements and bounds. Under an application
   $`E\langle\ldots\rangle`$ it composes with $`V_E`$ at that argument.
3. Check each member by $`\textsf{Valid}`$ against $`\mathcal A_V`$, which
   includes the component's own candidates and the variances of the
   components before it. The assumption is guarded, because every
   reference sits under a constructor.
4. Set a member that fails to $`\mathsf{inv}`$ at every parameter, drop one
   that fails at $`\mathsf{inv}`$ at every parameter (it has no variance,
   and $`\textsf{Var}`$ does not apply to it), and repeat from 3, for at most
   $`2k+1`$ rounds over the component's $`k`$ generic members, keeping none
   when they run out.
5. Check the members left together, with the variable condition; a
   component that fails this check keeps no variance.

Lean computes $`V`$ so (`Equations.settle`, `Equations.componentVariances`),
and each variance it keeps is valid (proved: `CheckedVariances.sound`,
`Variances.sound`).

**Lemma 4 (conjectured).** For any definition, $`\mathsf{inv}`$ at every
parameter is valid.

*Proof sketch.* Each comparison in the body relates a variable to its
counterpart, and both directions are hypotheses. $`\square`$

Where Lemma 4 holds of a component's members, step 4 drops none, and the
loop ends after at most one step per member. A definition on no cycle takes
one traversal of its body.

**Other pairs.** A pair $`D\langle\vec\tau\rangle\le E\langle\vec\sigma\rangle`$
that $`\textsf{Var}`$ does not derive is covered by unfolding, with the pair
added to the table and reused by $`\textsf{TabRen}`$. A pair of definitions
that recurs, other than by a renaming, is refused at its third occurrence
when its arguments are larger than at both earlier ones. `Promise<number> ≤ PromiseLike<number>` closes
with two pairs: itself, and $`\mathit{Promise}\langle\rho\rangle\le\mathit{PromiseLike}\langle\rho\rangle`$
for the bound $`\rho`$ of `then`, which recurs renamed.

### 4.4 Instantiation

The judgment has one more rule, standard in F<:
([Pierce 1994](REFERENCES.md#pierce-1994)): a quantified signature is below
each instance of it within its bounds,

```math
\frac{\vec\tau\le\vec\rho[\vec\tau/\vec\alpha]\qquad \sigma[\vec\tau/\vec\alpha]\le\sigma'}
{\forall\vec\alpha\le\vec\rho.\,\sigma\ \le\ \sigma'}\ \textsf{Inst}_\forall
```

where $`\sigma[\vec\tau/\vec\alpha]\le\sigma'`$ is signature subsumption: receiver
and arguments contravariant, result covariant, effect subsuming
([POSITIVE-TYPES](POSITIVE-TYPES.md#instances-of-a-scheme-row)). The instance's
images are the substitution itself. Each bound
premise is decided by the judgment itself. A table's coverage may use such an
instance as a known row: a prototype's quantified member, at the object as
receiver, covering a target's method. Soundness is Lemma 3 with the bound
premises ([POSITIVE-TYPES](POSITIVE-TYPES.md#instances-of-a-scheme-row)).

[Instance elimination and effect subsumption](POSITIVE-TYPES.md#instances-of-a-scheme-row)
compose with intersection introduction. A target intersection requires inclusion in each of
its components, so instantiating its arrow component also requires inclusion
in every opaque component. This is the usual intersection introduction rule:

```math
\frac{S\le A\qquad S\le P_1\qquad\cdots\qquad S\le P_k}
     {S\le A\cap P_1\cap\cdots\cap P_k}
```

The executable comparison operation discharges bound premises with the same
rules as its enclosing comparison, including quantified instantiation. The
structural kernel uses the equation representation's validated variance entries
and binder renaming. `instanceTarget_value` proves intersection introduction
for an instantiated arrow and its opaque parts. `compareInstArrsState_sound`
proves the instance rule from sound bound comparisons; `compareUsingCore_sound` proves those comparisons at
every parameter assignment. Instantiated prototype members are validated before
structural coverage uses them. A bound query repeated on the current instance
path may use a checked structural derivation; it cannot assume its unfinished
instance. Its structural recurrence requires the guarded family rule.

Instance inference supplies alternatives from unification, unification of the
arguments without the results, and structural matching. A binder matching does not
determine is proposed at the empty union where no target operand mentions it
(`filter`'s `S` at a plain predicate), and stands for itself where one does;
the substitution, bound and image checks decide either proposal. Its constructor receives the
substitution operation and constructs choices. `compareInstancesState` validates
those choices in order, selecting a successful one and retaining exhaustion when no
alternative succeeds; each alternative is computed when it is reached
(`Proposals`), so structural matching runs only once unification's instance is
refuted, and reads no row where a target signature has no scheme signature of
its effect and arity. This selection serves ordinary subtype comparisons and
explicit method type arguments through `selectInstancesUsing`.
`compareInstancesState_sound` reduces acceptance to a checked instance at every
parameter assignment.

Within a comparison, successful bound and component judgments are shared
between sibling premises and alternative instance candidates. A
`CheckedComparison` contains the selected choices and a proof of the exact
inclusion at every parameter assignment. The cache uses exact source and target
equation labels within one fixed equation environment and image checker. Labels
identify their lexical binders; hypotheses require the guarded structural rule.
Only completed successful checks publish entries. An unsuccessful enclosing
alternative retains successful child entries. Each operation starts with an
empty cache, including comparisons over a growing equation store. Semantic
equality checks inclusion in each direction, each with its own comparison state.

Dependency and arrow-evidence discovery read quantified rows directly and
through their opaque intersection components. Dependency discovery has an
execution budget measured in frontier rounds.
Each frontier can contain arbitrarily many comparisons. The same budget bounds
descent through instance-bound comparisons. At the descent boundary, a
structural derivation can establish the premise; otherwise the unsearched
instance alternatives report exhaustion. The kernel distinguishes
established inclusion, an inclusion its search does not establish, and resource
exhaustion. Instance validation retains the outcomes of bound comparisons and
image equality; equality requires sequential inclusion in both directions.
Conjunction returns its first unsuccessful premise. Alternative rules return an
established inclusion when any rule succeeds; if none succeeds, an exhausted
attempt remains exhausted. Member instances are validated once, and their
outcomes serve both guarded coverage and the enclosing comparison's outcome.
Its acceptance theorem covers only established inclusion. The
command-line protocol for resource outcomes is tracked in
[WORK](../WORK.md#status).

### 4.5 Example

The polarity equations give `Promise` the candidate $`\mathsf{co}`$: its
parameter occurs in `then`'s callback parameter, a parameter of a parameter,
and in `catch`'s result. Its assumption
$`\forall\alpha\beta.\ \alpha\le\beta\Rightarrow\mathit{Promise}\langle\alpha\rangle\le\mathit{Promise}\langle\beta\rangle`$
is valid, member by member:
- **`then`:** after renaming the quantifiers, the callback
  $`\beta\to\gamma`$ must be within $`\alpha\to\gamma`$, which is the
  hypothesis. Both results are $`\mathit{Promise}\langle\gamma\rangle`$.
- **`catch`:** the results $`\mathit{Promise}\langle\alpha\lor\gamma\rangle`$
  and $`\mathit{Promise}\langle\beta\lor\gamma\rangle`$ are related by
  $`\textsf{Inst}`$ of the assumption itself. Its hypothesis
  $`\alpha\lor\gamma\sqsubseteq\beta\lor\gamma`$ follows by
  $`\textsf{Union}`$, from $`\textsf{Hyp}`$ and $`\textsf{Mem}`$.

`Promise<number> ≤ Promise<number | string>` is then `Var` with the premise
`number ≤ number | string`. The converse fails at its premise, and so does
the definition's unfolding, at `then`'s callback. For
`interface Cell<T> { v: T }` the writable field gives $`\mathsf{inv}`$, and
`Cell<A> ≤ Cell<B>` requires `A` and `B` equivalent.

## 5. From source

Lowering turns the parser's declarations into definitions:
- **Declarations:** an interface, a class instance type or an object alias
  becomes a definition over its type parameters. Its bases are met into
  its body.
- **Generic members:** a generic method becomes a quantified signature in
  that body. A binder's declared default is no part of the signature: it
  names the instance a producer proposes where nothing constrains the
  binder, and a claim states every instance, which the checker checks
  against the bounds.
- **Units:** a generic function, closure, class or imported generic value
  is typed by a quantified signature of its own.
- **Literals:** each occurrence of an object, function, tuple or array type
  inside a definition becomes a definition of its own, over the variables
  it mentions: $`L\langle\vec\gamma\rangle=\text{the literal}`$ with
  $`\vec\gamma`$ its free variables. This is λ-lifting of type literals.
- **Packed binders:** a binder used both as a value and as a rest's argument
  lists is one variable $`\alpha`$ of the packed sort, read in both
  components; its argument lists $`\alpha^{*}`$, spelled `T#pack`, are the
  same variable. A unit's or a closure's literal is lifted over it once. A
  generic value's literal is lifted over $`\alpha`$ and $`\alpha^{*}`$ apart,
  which its instance gives as $`X`$ and $`\mathsf{Pack}(\tau)`$, $`\tau`$ the
  tuple contract of the array or tuple type $`X`$. A declaration's packed
  parameter's argument is the union of the two. Its domain, the laws
  relating $`\alpha`$ and $`\alpha^{*}`$, and the instantiation check are in
  [PROGRAM-TYPING](PROGRAM-TYPING.md#packed-binders).

A written type application must satisfy each declaration's bound at its
completed arguments, read from the written syntax whatever term a reader
states for it ([written applications](SOURCE-CONTRACTS.md#written-applications)).
These subtype obligations are checked over the compacted
equations with the same execution budget as later comparisons. Their
[diagnostics](OBLIGATION-DIAGNOSTICS.md#direct-obligations) retain the compared
types and distinguish exhausted work from an unsuccessful completed search.

Every other declaration is an alias, inlined at its uses. Inlining
terminates when every cycle through aliases passes through a definition:
lifted literals are keyed by their occurrence. An alias
such as `type T<X> = X | T<[X]>` recurs under no constructor, so it is
refused as unguarded.

Definitions are created per source construct, so their
number is bounded by the size of the source, whatever families it defines.
`Pair<T>`'s `push<U>(): Pair<[T, U]>` has the result type
$`\mathit{Pair}\langle\mathit{Array}\langle L\langle T,U\rangle\rangle\rangle`$
with $`L\langle\gamma,\delta\rangle=[\gamma,\delta]`$. The family grows by
application, over a fixed set of definitions.

TypeScript reads a record met with a function as one callable object, which
the model's exact intersection would make empty. Lowering applies that
reading only to ground intersections, producing a literal definition, out
of reach of substitution.

## 6. Trust and acceptance

Untrusted code proposes and a small checker decides, as everywhere in the
verifier.

- **Proposed:** the definitions, and every certificate with its
  assumptions between different definitions, tables and instances. An
  instance is found by matching the scheme's signatures against the
  target's terms, two applications of different heads through one step of
  each unfolding; its images are the substitution.
- **Checked:** the definitions' well-formedness (scoping, arity,
  contractiveness), every instantiation by substitution, each image being
  the substitution, each target signature covered by an image's, and every
  assumption by the conditions of Theorem 1.
- **Computed by the checker:** variances (4.3).

Every semantic premise of a rule is discharged by Lemmas 1–3 and Theorem 1
from the definitions themselves.

The acceptance theorem's premise is the exact success condition of the
command-line checker. Its conclusion, safety of every accepted unit, is
stated over the unit's definitions. A finite type graph is the case where
no definition has parameters. The trusted boundary is the parser and the
reading of declared types.

## 7. Related work

The families are the parameterized type definitions of
[Solomon 1978](REFERENCES.md#solomon-1978), whose equivalence he related to
that of deterministic pushdown automata. Here a checker validates
certificates and computes variances.

Coinductive subtyping over assumed pairs
([Amadio and Cardelli 1993](REFERENCES.md#amadio-and-cardelli-1993),
[Brandt and Henglein 1998](REFERENCES.md#brandt-and-henglein-1998)) handles
regular types. Parametric assumptions extend it with variables and
hypotheses, so that one assumption covers a non-regular family. [Kennedy
and Pierce 2007](REFERENCES.md#kennedy-and-pierce-2007) prove nominal
subtyping with variance undecidable under expansive inheritance;
the definitions here are structural, and section 4 relates an expanding
definition to itself only through per-position variance.

An application is a closure, a definition with its arguments, like a
suspended substitution in calculi of explicit substitutions
([Abadi et al. 1991](REFERENCES.md#abadi-cardelli-curien-and-lévy-1991)).
What it delays is the unfolding of a definition; substitution is carried
out in full. The type level has no β-redexes, so only the substitution
lemma carries over.

## 8. Mechanization

Intersection trees flatten nested intersections, sort their operands and remove
repeated operands; row construction also removes repeated clause lists from
differently named operands. The intersection wrapper remains for a single operand,
since an intersection contains values only and its operand may also denote
argument lists. `Equations.meetOf_denote` in
[EquationMeets.lean](../lean/Verification/Types/EquationMeets.lean) proves that this
normalization preserves the intersection's value meaning; `meet_noArguments`
proves its exclusion of argument lists.

The Lean development represents a bound variable by the application that
introduces it. The `β` of the `then` of `Promise⟨number⟩` is a distinct term
from the `β` of the `then` of `Promise⟨string⟩`, so capture-avoidance holds
by construction, and comparing quantifiers from two applications is an
explicit renaming (section 4.1). Definitions are numbered, and bodies refer
to parameters and quantified variables by position.

| Concept | Lean |
| --- | --- |
| Definitions, types and unfolding (2) | [Types/EquationGraphs.lean](../lean/Verification/Types/EquationGraphs.lean) |
| A meet label means the intersection of its parts (2, 3.3) | [Types/EquationMeets.lean](../lean/Verification/Types/EquationMeets.lean) |
| Lemma 1, support | [Types/EquationSupport.lean](../lean/Verification/Types/EquationSupport.lean) |
| Lemma 2, congruence of applications | [Types/EquationCongruence.lean](../lean/Verification/Types/EquationCongruence.lean) |
| Lemma 3, substitution | [Types/EquationSubstitution.lean](../lean/Verification/Types/EquationSubstitution.lean) |
| Instantiation by substitution in the subtyping checker | [Types/EquationCertificates.lean](../lean/Verification/Types/EquationCertificates.lean) |
| Quantified signatures (4.1), assumptions and Theorem 1 (4.2) | `Types/PositiveRules.lean`, `Types/SchemeInstances.lean`, `Types/PairFamilies.lean`, `Types/PositiveCertificates.lean` |
| Comparison and instance bounds over the equations (4.2–4.4) | `Types/PositiveCertificates.lean` (`compareUsingCore_sound`, `compareInstArrsState_sound`, `compareStructural_sound`) |
| Soundness of the computed variances and of `Var` (4.3) | [Types/EquationFamilies.lean](../lean/Verification/Types/EquationFamilies.lean) |
| A graph with qualified rows keeps an ordinary template's meaning (`DomainRegion.denote`) | [Types/QualifiedTemplateEmbedding.lean](../lean/Verification/Types/QualifiedTemplateEmbedding.lean) |
| The dependency region of a definition, closed and ordinary, keeps its meaning under a descriptor domain (`checkOrdinaryRegion`, `OrdinaryRegion.domainRegion`) | [Types/EquationDomains.lean](../lean/Verification/Types/EquationDomains.lean) |
| Well-formedness of equations | [Types/EquationValidator.lean](../lean/Verification/Types/EquationValidator.lean) |
| Term spelling of trees | [Types/EquationJson.lean](../lean/Verification/Types/EquationJson.lean) |
| Lowering source declarations (5) | [Source/Equations/Lowering.lean](../lean/Verification/Source/Equations/Lowering.lean) |

The pipeline cases `non-regular-alias` and `invalid-non-regular-alias` lower an
alias applied to a longer tuple at each level to one invariant head.
`pipeline/test.mts` refuses by name, in forged declarations the parser
does not write, a binder used both as an argument pack and as a value and an
unguarded alias, where a nested method's own binder of the same name is
accepted.

The wire spellings are in [SOURCE-CLAIMS](SOURCE-CLAIMS.md#encoding) and
[REQUEST-PROTOCOL](REQUEST-PROTOCOL.md). Progress is recorded in
[WORK](../WORK.md#status).
