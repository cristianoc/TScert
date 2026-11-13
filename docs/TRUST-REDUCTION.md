# Reducing trust

The bridges between a TypeScript program and the proved theorem that rest on
review rather than proof, the ways each could be narrowed or proved, and how
they compose. [A semantics of the Fragment](../WORK.md#a-semantics-of-the-fragment)
is the open work taking options (2) and (3), with the Fragment semantics
read as JavaScript directly and tested against node.

## The bridges

[`mode8Accepted_sound`](DESIGN.md#what-verified-means) proves the extracted
calculus program safe. Between the source a user writes and that program,
four bridges rest on review; the [trust surface](DESIGN.md#trust-surface)
lists them with the rest of what the theorem assumes:

| Bridge | Where | What is trusted |
| --- | --- | --- |
| **Parser rewrites** | `tools/fragment-parse.mts` with its parts `fragment-classes.mts`, `fragment-expressions.mts`, `fragment-statements.mts`, `fragment-support.mts` and `fragment-guards.mts` (TypeScript) | Its lowerings (`switch`, `for`, templates, enums, optional chains, patterns, `super`, the iterator protocol, shadowing renames, …) preserve JavaScript's execution; TypeScript's binder names each reference's declaration; for [certified imports](SOURCE-CONTRACTS.md#certified-imports), each imported module's document lowers the bytes its digest names, no code of it left unlowered writes the binding of one of its function declarations, and each import resolves to its unit's terminal declaration. |
| **Extraction** | `Source/SourceExtraction.lean`, `Source/Fragment.lean` (Lean) | The calculus program it builds from the Fragment AST means what the Fragment means: control flow, lexical binding, evaluation order, and the program point each claim attaches to; for certified imports, a unit's run, its initialisation included, is its module's. |
| **Declared types** | `tools/declaration-graph.mts`, `type-term.mts`, `computed-types.mts`, `written-applications.mts`; `Source/Equations/Lowering.lean` | A declaration or annotation is read as the type TypeScript means, and its written applications are supplied with their scopes, each one ([written applications](SOURCE-CONTRACTS.md#written-applications)); the standard library's declarations are reviewed, the applications inside them included; for certified imports, a module's declarations are read in its own document. |
| **Host** | intrinsics, library overlay, environment premises | Native code meets its stated types ([the host](#the-host)); for certified imports, the module loader binds an eligible import to its unit's closure, evaluated once ([the linking obligation](SOURCE-CONTRACTS.md#certified-imports)). |

Extraction runs inside Lean, so what is checked is exactly what it produced;
but no theorem states that it preserves the source's meaning, because the
Fragment AST has no semantics in Lean. Its faithfulness is a reviewed
definition, as the parser's is.

## Options, cheapest first

1. **Structural theorems about extraction.** Provable in Lean over the AST it
   already has, with no JavaScript semantics: every edge targets a node; slots
   are fresh; every variable reference resolves to the declaration it names;
   every claim sits at its source span; every early exit passes the finalizers
   it leaves. These rule out the binding and control-flow errors extraction can
   make without ruling out every semantic one.
2. **Rewrites move from the parser into Lean.** The parser emits an AST close
   to the source (statement-level `switch`, `for`, templates, `super`,
   patterns, the iterator protocol) and extraction performs the rewrites.
   Trusted TypeScript shrinks to reading syntax and TypeScript's name and type
   resolution; the rewrites become subject to (1) and (3). Where a rewrite is
   chosen by a TypeScript type (`%Iterate:K%`, `%ElementAt%`), stating its
   correctness exposes the premise it needs ("the value is a host `Set`"),
   which is how a forged host value is caught.
3. **A Fragment semantics and a preservation theorem.** Give the Fragment AST
   an operational semantics in Lean, written as JavaScript's statement-level
   rules, and prove extraction a simulation: every run of the extracted program
   corresponds to a run of the Fragment with related states, throws included.
   Faithfulness then rests on the Fragment semantics, which reads like the
   specification and is reviewable against it. With (2), it covers the
   rewrites too; without (2), bugs before the Fragment escape it.
4. **A meaning for declared types.** Reading a declaration is a separate
   bridge: a meaning for TypeScript's type syntax (the forms the reader admits)
   and a theorem that the reader's graph rows denote it. Neither (2) nor (3)
   covers it.
5. **The host**, by [host lemmas](#the-host): each intrinsic and overlay
   entry proved of the specification's built-in.

## How they compose

Faithfulness of the extracted program to JavaScript splits in two with (3):
the Fragment semantics against JavaScript, stated at the level of
JavaScript's statements, and extraction against the Fragment semantics,
which is (3). The first half is read and tested against node; proving it
would take a mechanized specification M, which (5) needs as well.

| Option | Retires | Needs |
| --- | --- | --- |
| (1) structural theorems | binding, control-flow and claim-placement errors in extraction | nothing new |
| (2) rewrites in Lean | trust in the parser's rewrites | (1) or (3) to prove them |
| (3) Fragment semantics | extraction's faithfulness, relative to the Fragment semantics | a Fragment semantics |
| (4) declared-type meaning | the declaration reader's faithfulness | a meaning of type syntax |
| (5) host lemmas | the ECMA rows of the trust surface | M |

## Evidence

Errors of the kinds these options address have been found in each bridge
by review or tests, none by the proofs, which hold of the program the
bridges deliver: in extraction, a binding resolved by name and source keys
spelling the model's reserved keys ((1) or (3)); in the parser's rewrites,
a program-built object passing for a host `Set` ((2) with (3)); in the
declaration reader, generic contracts erased ((4)); in the host, an
unbounded `%Await%` ((5)).

## The host

Promises, `await`, the library built-ins and the intrinsics have no step
rules. They enter as values in the environment with a declared type
(`EnvOk`), and the theorem assumes the native code behaves as typed.

Proving that needs **M**, a mechanized [ECMA-262](REFERENCES.md#ecma-262)
semantics: an abstract machine over the specification's values, records,
realms and job queue, with the built-ins' algorithms. ESMeta (formerly JISET,
[Park et al. 2020](REFERENCES.md#jiset-and-esmeta)) extracts such a semantics
from the specification's own algorithm text and covers promises and async;
using it from Lean means importing or re-stating its fragment in Lean. JSCert
([Bodin et al. 2014](REFERENCES.md#bodin-et-al-2014-jscert)) is a hand-written
Coq alternative, for ECMAScript 5, before promises. M is related to calculus
states by a relation R on values (primitives, including `numberToString`'s
spelling of property keys), objects (own keys, `[[Prototype]]`, data
properties), the calculus's reserved keys (the array store `[]`,
`[[proto]]`, the class brand) and built-in objects (`Array.prototype`,
`Promise`, …).

**Host lemmas.** For every intrinsic and overlay entry $`x : \tau`$ in the
[trust surface](DESIGN.md#trust-surface), the corresponding M built-in
$`b_x`$ is in the M-level meaning of $`\tau`$: $`b_x \in ⟦\tau⟧_M`$. The
meaning $`⟦\cdot⟧_M`$ is the calculus's type meaning transported along R,
with one extension: a `Promise<X>` is a built-in promise whose fulfillment value
is in $`⟦X⟧_M`$. Every row of the trust surface that names ECMA behaviour,
such as `%Await%`, `%Iterate%`, `%ForIn%`, `Array.prototype`'s members,
`JSON`, `BigInt` and `Set`/`Map`/`Date`, becomes a proof obligation.

**End to end.** Composing [`mode8Accepted_sound`](DESIGN.md#what-verified-means)
with faithfulness and the host lemmas gives: for a source unit that
`verify-source.mts` verifies, run in M from any state whose environment values are in
the M-meanings of the unit's declared inputs, every value observed at a
claimed program point is in the M-meaning of its claim, and every run
returns, throws, or continues. Its remaining premises are about code outside
ECMA: imported modules and ambient declarations meet their declared types;
TypeScript's resolution and the parser are correct.

| Piece | Scale |
| --- | --- |
| M in Lean, for the fragment's operations and built-ins | Large: importing or re-stating ESMeta's semantics for objects, operators, promises and the job queue |
| Host lemmas | Medium per built-in; many built-ins |
| End to end | Small once faithfulness and the host lemmas exist |

A cheaper step catches much of the same class of error without M: a
differential harness that runs node against each trust-surface entry on
generated values, with thenables, extra own keys, `NaN`/`-0`, holes and
nested promises as adversarial inputs. It proves nothing.

### Illustration: nested promises

A trust-surface row
$`\mathtt{\%Await\%} : \forall T.\ \mathsf{Promise}\langle T\rangle \Rightarrow T`$
with $`T`$ unbounded is false. A trusted generic declaration such as
`declare function wrap<T>(x: T): Promise<T>` can be instantiated at
`T = Promise<number>`; the model then expects `await wrap(p)` to be a
promise, and at run time it is a `number`. Every proof goes through, because
the false statement is an assumption.

The host lemma
$`b_{\mathtt{Await}} \in ⟦\forall T.\ \mathsf{Promise}\langle T\rangle \Rightarrow T⟧_M`$
is false at any thenable $`T`$, and the specification gives the
counterexample directly:

- a promise's resolve function, called with a value that has a callable
  `then`, does not fulfill with it; it schedules `NewPromiseResolveThenableJob`
  and adopts it (ECMA-262, *Promise Resolve Functions*);
- so no built-in promise is ever fulfilled with a thenable;
- `Await` of a built-in promise yields its fulfillment value
  (*Await*, *PromiseResolve*).

Hence
$`⟦\mathsf{Promise}\langle \mathsf{Promise}\langle \mathsf{number}\rangle\rangle⟧_M = \emptyset`$
among built-in promises, and the lemma cannot be proved.

The end-to-end statement shows the same error differently. The declaration
`wrap<T>` enters it as a premise: `wrap` is in
$`⟦\forall T.\ T \Rightarrow \mathsf{Promise}\langle T\rangle⟧_M`$. At
$`T = \mathsf{Promise}\langle\mathsf{number}\rangle`$ the result type is
empty, so no implementation meets the premise, and the conclusion is vacuous
for every program that uses `wrap` there. The statement needs no premise to
be satisfiable, so this surfaces only if someone asks for it: a reason for it
to include a satisfiability check of its external premises at their
instantiations.

The pipeline states:

- `%Await%` at $`\forall X:\mathsf{Awaitable}.\ (X) \Rightarrow X.\mathsf{Observed}`$, whose observation-qualified $`X`$ ranges over the inputs observed as stable, a native promise of any payload or a union of those ([implied bounds](SOURCE-CONTRACTS.md#implied-bounds));
- the host assumption that a value of type `Promise<T>` is a built-in promise,
  with the source refused from building an object that has a `then` member;
- a trusted generic signature's type parameters that occur under
  `Promise<…>` bounded by the non-thenable types
  $`N = P \mid \{\mathtt{readonly\ then?}: P\} \mid \mathsf{readonly\ unknown[]}`$.

Under M, the qualified `%Await%` lemma is provable from the specification;
"`Promise<T>` values are built-in promises" becomes a lemma for every promise
the program or the built-ins create; and the non-thenable bound is exactly
the condition under which a trusted generic promise signature is
satisfiable, so the external premises are not vacuous. The assumption left
is that third-party code keeps its declared promise types, which no
specification can state. The same fact is discussed for ReScript
([#5709](REFERENCES.md#rescript-5709), [#6433](REFERENCES.md#rescript-6433),
[#2345](REFERENCES.md#rescript-2345)) and TypeScript
([#27711](REFERENCES.md#typescript-27711), [#49946](REFERENCES.md#typescript-49946),
[#35419](REFERENCES.md#typescript-35419), [#55408](REFERENCES.md#typescript-55408)).

The same shape recurs in any **flattening** constructor, one whose runtime
representation satisfies $`c\langle c\langle t\rangle\rangle = c\langle t\rangle`$,
such as nullable values and promises. A generic signature is truthful at
$`c\langle T\rangle`$ only for $`T`$ outside $`c`$'s image, and generic
instantiation can always produce the nested type
([TypeScript #59111](REFERENCES.md#typescript-59111); two such constructors
composed, [ReScript #5211](REFERENCES.md#rescript-5211)). So soundness cannot
rest on banning nested types: it has to come from the meaning of the
constructor, or from a bound at every trusted instantiation
([ReScript #5707](REFERENCES.md#rescript-5707)).
