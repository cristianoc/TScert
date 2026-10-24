# Draft: class methods' effects

The design of class methods' effects; its status and the owner's decisions
on it are in [WORK](../../WORK.md#class-methods-effects). Base: TScert main at d99275a.
Claims are labelled **proved** (with the Lean name), **cited** (with the
document and its scope) or **conjectured**. Observed on 0e48e9f: async
definitions' effects are unrestricted, and three probes that break an effect
through a rejected promise are refused (each leaves a hole under Node).

## 1. The problem, at the level of the judgment

A call `e.m(v⃗)` consumes the contract of the location the callee is read
from ([calls through a location](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification);
cited): a member found along `e`'s prototype chain (`bindMember`,
`MethodMembers.memberT`) or a field (`field-call`). The effect of the call is
the effect that contract states. A class member's contract is its
declaration's signature, which states no effect, so

```math
\frac{\Gamma\vdash e:C\qquad \mathrm{member}_G(C,m)=(\vec A\to B\;!\;\top)}
     {\Gamma\vdash e.m(\vec v):B\;!\;\top}
```

and a callback containing that call is outside every closed footprint but
`top`. `map` then takes its signature with holes and `find`/`findIndex`
their unrestricted one ([natives](../FOOTPRINTS.md#natives); cited).

The judgment that fails is the call's effect, and it fails correctly: `C`
is TypeScript's structural type, a look-alike object or a subclass instance
is a value of it, and either may hold an `m` that pops the mapped array
(`invalid-map-method-call-effect`, run under Node; cited from
[SOURCE-REWRITES](../SOURCE-REWRITES.md#a-map-callback-calling-a-method-of-a-structurally-typed-object)).
A receiver of TScert's own code is almost always a parameter annotated
`Gate` (`this: Gate`, `gate: Gate`: 143 occurrences in `tools/`), so the
effect a call may use is the effect the **type** `Gate` promises, not the
effect of code the checker can see at the call.

## 2. Decision D1: where a member's effect lives

The effect a receiver's type promises is part of that type's meaning, and
the meaning of a written annotation must be the same in every run: a
unit's theorem assumes its inputs at their annotations (`EnvOk` in the
premise of `checkJson_safe`), and a producer-chosen effect in an input
type would make "verified at its annotation" depend on a proposal. Three
ways to fix it:

- **(a) Stated effects (recommended).** A signature's result annotation may
  state the signature's effect with a verifier declaration (§3). The
  statement is part of the annotation: every run reads it alike, through
  the trusted front end, and every value introduced at the type is checked
  to meet it. Inference proposes statements and the claims inside bodies;
  Lean certifies every statement from the body it describes.
- **(b) Certified in every run that reads it.** The run reading `C` at
  member effects certifies `C`'s members from their code, as a
  [certified import](../SOURCE-CONTRACTS.md#certified-imports) is
  certified (cited). No new trust within a run. For `Gate` the members'
  code is the whole lowering (`fragment-{parse,expressions,statements,classes,support}.mts`,
  `type-term.mts`, about 9,000 lines) and its modules import each other,
  which the acyclic qualified-dependency graph refuses (cited). Two runs
  may also certify `C` at different effects, so linking two runs needs
  them equal, which no run checks.
- **(c) Exact instances.** Read a program class's name nominally (its
  prototype a stable key holding the class's one prototype object, its
  readonly method fields stable at the functions they are initialised
  with) and certify the reached closures in the run. This needs the
  program to introduce stable keys, which it never does today
  ([stable keys](../HOST-FAMILIES.md#stable-keys); cited), a nominal
  reading of class names that refuses look-alikes and subclass instances,
  and (b)'s per-run cost for every closure reached.

The rest of this document is design (a). It needs no program-wide
analysis (no "no subclass overrides `m`", no "no code writes the field"):
each condition the owner listed is an instance of one rule already in the
model, *a location's contract is checked at every write and every
introduction*, applied to a contract that now states an effect.

## 3. The statement

**Declaration.** A verifier file beside `tools/resolvable.d.ts`, recognized
by the declaration TypeScript binds the name to, never by its spelling:

```ts
// tools/effects.d.ts
type Footprint = { value: "keep" | "any"; store: "keep" | "grow" | "any"; onThrow?: true };
type Within<F extends Footprint, T> = T;
```

TypeScript reads `Within<F, T>` as `T`. TScert reads it in one position:

```math
\frac{⟦\vec A⟧=\vec P\qquad ⟦T⟧=B\qquad F=\{\mathsf{value}{:}\,v,\ \mathsf{store}{:}\,s[,\ \mathsf{onThrow}]\}}
     {⟦(\vec x:\vec A)\Rightarrow\mathtt{Within}\langle F,T\rangle⟧=\mathcal F_{\epsilon(F)}(R,\vec P,B)}\ \textsf{stated-effect}
```

with $`\epsilon(F)`$ the effect of footprint $`\{v,s\}`$, `onThrow` as
written, no promise, no fresh result, no receiver-store exception. The
position is the result annotation of any written signature: a function
declaration, a class or static method, an object-literal method, an arrow
or function expression, an arrow or function type, an interface's or a
type literal's method or call signature. `typeof f` reads
`f`'s declaration, so it reads the statement too
([calls through a location](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)
already says `typeof f` names `f`'s declared signature; cited).

**Refusals** (each located, each a negative case in §9):

- `Within` anywhere else (a parameter, an element type, a type argument
  other than a signature's result, nested inside another `Within`);
- `Within` on any signature of an overloaded declaration, the
  implementation's included. Source overloads have no per-overload
  certification today (`functionDecl` lowers one signature with its body,
  `FunctionAst` carries one, and a declaration's claim one footprint), so
  a statement there could not be certified; stating effects on overloads
  is later work with its own extraction obligation (each callable
  overload associated with the implementation and checked at its own
  domain);
- a statement whose footprint is `{value: any, store: any}`: it states
  nothing the ordinary effect does not, and `effectResult`
  (`Source/SourceRequests.lean`) admits an effect check only below `top`;
- `Within` on an async definition (§6, the completion boundary);
- `Within` on a declaration whose type parameters carry a resolution
  qualification (`T extends Resolvable` or `Awaitable`): such a unit is
  refused a footprint claim today (`effectResult` requires
  `qualification.isNone`);
- a statement in the **effective type** of a value declared outside the
  program's modules (a dependency's `.d.ts`, an ambient declaration),
  however it is reached: written there, or reached through `typeof`, an
  alias, an indexed access or a re-export of a program declaration
  (`export const evil: typeof good`). The parser decides this on the term
  it builds for the external binding, which `typeQuery`
  (`tools/computed-types.mts`) already follows to its declaration. An
  external implementation's effect is an audited overlay entry or nothing
  ([elaboration](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification);
  cited). The one exception is a statement inside a program class's
  instance type (an external function returning a `Gate`): the instance is
  the program's value, whose conformance §8's row assumes;
- `Within` on a guard's or an assertion function's result (its promise
  signature states a footprint beside the promise already, `moduleArrow`);
- `Within` on an accessor, a constructor or a construct signature;
  accessors are outside the fragment, a construct signature's effect is
  the constructor's and stays as today (`ctorGraph`).

**Wire.** Two documents carry a statement, each already shaped for it:

- the **declaration document**'s function and constructor terms carry
  `effect: CallEffect` (`tools/declaration-types.mts`), decoded by Lean for
  natives. The parser writes the stated effect there for every signature a
  declaration, an interface, a type literal or a function type states; an
  unstated signature keeps `Effect.ordinary` (footprint `top`);
- the **Fragment**'s callable definitions (function declarations,
  function expressions, arrows, object-literal methods, class
  methods and static methods) carry their written signatures, the result
  annotation among them (`lambda`'s `result`, today a `TypeTerm | null` read
  by `gate.typeOf`). Each written signature gains its stated effect beside
  its result: the **stated-signature obligation** of §4.1. The producer's
  claimed signatures are a separate document and never supply it.

## 4. Certification: where every statement is proved

Every value the program introduces at a type stating an effect meets it,
and Lean checks each introduction.

1. **Every callable definition (the stated-signature obligation).** For a
   definition whose written signature $`\sigma`$ states $`\epsilon`$ (a
   function declaration without overloads, a function expression, an
   arrow, an object-literal method, a class method, a static method), Lean
   requires, from the Fragment's stated signature and never from a claim,
   that the definition's code is certified at $`\sigma`$ with an effect
   within $`\epsilon`$, located at the definition, whether or not any code
   calls it. "Within" is `Effect.covers` from the certified effect to
   $`\epsilon`$ (`onThrow` where $`\epsilon`$ states it). The certification
   is the existing one for the definition's kind: `declaration-effect` for
   a declaration's unit (`checkRequests_footprint_at`, proved), a code
   entry for a closure (`codeChecked_sound`, proved); both run the
   parameter defaults as nodes of the graph, so a default that pops is
   within the check. Each definition has one written signature, overloads
   being refused a statement (§3). The claim may be
   stronger than the statement; other units of the run read the claim, as
   today, and other runs read the statement.
2. **Class construction.** `new C(…)` returns, at `C`'s instance type, the
   allocation $`\varphi_0`$ of [classes](../SOURCE-CONTRACTS.md#classes)
   (cited): own fields at their contracts and `[[proto]]` holding
   `C.[[prototype]]`, which the class statement allocated once holding
   each method's closure. Two obligations, both on code that exists:
   (i) the prototype's allocation stores each closure at a location whose
   contract is the closure's certified type, by 1; (ii) the constructor's
   result meets the instance type: for each member $`m`$, `memberT` finds
   $`m`$ on the prototype (`along … 1`) at a contract implying $`m`$'s
   signatures, effect included, on the host. For a derived class `D`, the
   instance type is `D`'s members met with its base's (cited, ibid.), so
   (ii) checks an override against the base's statement. Static methods
   are bindings (`static C.m`, cited) and are definitions under 1.
3. **A method field** `f: typeof g = g` (the `Gate` convention). The
   field's contract is its annotation, which reads `g`'s statement; the
   initialiser `g` is read at its declaration's signature and meets it by
   reflexivity. A later write `o.f = h` is checked at that contract
   (`field-call`; cited), so `h` must be certified at the statement.
   Copies follow the existing paths unchanged: a spread or
   `Object.assign` into a fresh literal allocates new locations, whose
   contracts are the copy's type and may forget the effect without
   weakening the original's; `Object.assign` onto an existing object is
   admitted only where the target is an owned local object, lowered as a
   copy rebound to every holder (`growSites`; `Lowering/Flow.lean`,
   `Lowering/Execution.lean`), so the original location is never written
   and its holders hold the copy at the copy's type; an aliased target
   (a parameter, a field) is refused by that ownership rule before any
   contract applies.
4. **Any other value at the type**: an object literal or another class's
   instance passed where `C` is expected meets `C` by subtyping, whose
   member and field coverage compares effects (`Effect.covers` in
   `PositiveRules`/`PositiveCertificates`, `Effect.covers_sound`; proved),
   and whose writable fields require contract agreement both ways. A
   look-alike whose method is not certified within the statement is
   refused there. A union host binds a member only where every arm's
   member covers the claimed signature (`bind-union-host`; cited).
5. **Inputs.** A unit's inputs at an effect-stating type meet it by
   `EnvOk`: the theorem assumes of an input what its annotation says.
6. **Imports.** An import is read at its declaration, statement included
   (`import` rule; cited). That the imported value meets it is the import
   assumption (§8), conditional as §6 states.

A call then uses the existing rules unchanged: `bindMember` covers the
claimed signature by the member's, effects included
([PROGRAM-TYPING](../PROGRAM-TYPING.md#judgments-and-constructor-views);
cited), and `field-call` gives $`B\;!\;\epsilon`$ for the field's contract.
A callback whose calls are all within $`\Phi`$ is within $`\Phi`$
(`selectedWithinAt`, `ExpressionEffects.selected_sound`; proved), and the
natives' per-footprint signatures follow: `map` dense for $`\Phi`$ in the
stable set (`map_rely`, `stableDenseClosed_sound`; proved),
`find`/`findIndex` at `T` for the empty footprint.

**Which receivers qualify.** Every receiver whose type states the
member's effect, by any of 1–6; no receiver whose type does not. The
listed candidates reduce to this rule:

| Candidate condition | What the rule does instead |
| --- | --- |
| no subclass overrides `m` | an override is checked against the base's statement at its class (2) |
| a final class | not needed: subclassing is checked at the subclass |
| a `readonly` method field initialised once | not needed: every write is checked at the field's contract (3); `readonly` stays a view |
| a field reassigned after construction | the write is checked (3); a writable alias `{f: F}` without the statement is no supertype, since an invariant field's contract must agree with the alias's (`SlotContract`, $`c_j\equiv T_j`$; cited [POSITIVE-TYPES](../POSITIVE-TYPES.md)) |
| a method read off an interface | the interface's member states its effect or none; values meeting the interface are checked at introduction (4, 5) |
| a borrowed method `o.m.call(r, …)` | refused today (`refuseReceiverForm`; cited): `.call`, `.apply` and `.bind` are admitted on known local functions only |

**Relation to "Calls through a location".** The section's rule is
unchanged; its sentence "an ordinary arrow annotation states no effect"
becomes "an annotation states the effect its `Within` states, and none
without one". `invalid-field-call-effect` and
`invalid-readonly-field-call-effect` stay refused: their fields state no
effect.

## 5. What a statement may say

A statement is a closed footprint and `onThrow`
([changes and footprints](../FOOTPRINTS.md#changes-and-footprints);
cited): six footprints, ordered entrywise (`closed_order_exact`; proved).
It is type-blind: it bounds how every previously allocated location of
each class may change, wherever it is reached from. The node rules that
bound a body:

| Body operation | Footprint (existing rule) |
| --- | --- |
| write of a `this` field or any field holding a source value | `{value: any, store: keep}` (`writeWithin`, `write_within`; proved) |
| `push`/`unshift` on any array, a `this` field's included | `{value: any, store: grow}` (audited native row) |
| `Map`/`Set` mutators | at most `{value: any, store: keep}` (audited) |
| `pop`/`shift`/`reverse` on a store the call did not allocate | `top` (receiver-store exception; cited) |
| allocation, reads, tests | empty (`inspect_safe`; proved) |
| a call | its callee's signature's effect (`selected_sound`; proved) |

So `Gate`'s members that only read, write fields, set maps and push stay
within `{value: any, store: grow}`, in the stable set for density.

**Reachability is a separate step.** Showing that a call whose footprint
lets stores change beyond `grow` cannot reach a given local array is the
[deferred precision](../FOOTPRINTS.md#deferred-extra-precision)
(regions rooted at operands, transport, framing). It stays out of this
design:

- the operations outside `grow` in `Gate`'s members are `shift` on its two
  scope stacks (`enterTypeParams`/`leaveTypeParams`,
  `tools/fragment-parse.mts` 457–465) and the protocol sites'
  `entries.shift()`/`spans.shift()` (`fragment-statements.mts` 946–947), by
  a search of `tools/fragment-*.mts` for `shift`, `pop`, `splice`,
  `reverse`, `sort`, `fill`, `copyWithin`, `length =` and `delete`
  (`rest.splice` at `fragment-parse.mts` 2039 and the `sort`s at
  `fragment-classes.mts` 111 and `intrinsics.mts` 288 act on fresh arrays,
  conjectured from the code); each becomes a field write of the remaining
  list (`{value: any, store: keep}`), a source rewrite;
- the deferred design is a Lean development of its own whose trigger is
  "a retained program refused for this reason" (cited), which these
  rewrites remove;
- a regional effect would be one more form of the same statement,
  certified by the same rule, so nothing here changes when it lands.

A host node list's store is never changed by client code (T4,
[COMPILER-API](../COMPILER-API.md#node-lists-in-the-model); cited).
`map` over a node list could take the dense result whatever its callback
does, but only through an explicit family-sensitive native signature:
today a node list is read as an ordinary dense readonly array, whose store
a footprint `top` may change. That is a host-family item, independent of
method effects; §10 counts what it would cover.

## 6. Recursion, exceptions, async, accessors, `this`

**Recursion.** A body is checked against its own statement with every
callee read at its statement or, within the run, its claim. Mutual
recursion among methods, among module functions, and between the two
needs no fixpoint in Lean: each body consumes types, never bodies. Within
a run the producer's greatest fixpoint
([function declarations](../SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification);
cited) proposes claims for unstated declarations as today and reads stated
ones at their statements; class methods' self-reference through `this` is
the step-indexed self-reference `funGraphSelf` discharges (proved for
recursive constants; L3 for prototype closures).

**Scope across modules: conditional.** A run's acceptance certifies its
own definitions' statements (§4.1) and is relative to its imports meeting
theirs: if `b.ts` states `keep` on `g` and pops, `a.ts`, calling `g` in a
`map` callback, verifies under the import assumption while `b.ts`'s run is
refused. That the linked program meets every statement needs every
module's run to pass and the [module composition](../../WORK.md#module-composition)
theorem, which is open (WORK.md); until it is proved, the statement's
cross-module use is the import assumption, a review obligation listed in
§8, exactly as a declared type's is today. Nothing here makes the
exporting run's success a premise of the importer's acceptance.

**Exceptions.** A statement without `onThrow` holds on normal return only
(`SafePost`; cited). Nothing moves onto an exceptional edge: a handler
covering a call at a signature without `onThrow`, and a `finally` reached
from it, is refused in bounded certification (`GraphCode.NodeWithin`'s
`thr`; cited). A method that pops and then throws meets every
normal-return footprint, and a caller that catches it gains nothing
(`invalid-method-effect-throw-caught`). A statement with `onThrow` is
certified with `SafePostExc` (cited), so a pop before a throw refutes it.

**A node without a normal return.** A node whose term is typed, by its
checked ordinary typing, at a result family that admits no value never
returns normally, so its normal-return run is within every footprint
(conjectured; obligation L5). The rule is a node rule of bounded
certification beside the existing ones, not a coverage rule and not
specific to calls: the member is bound and the callee selected at their
own signatures (`bindMember`, `CoveredCallUsing` unchanged), and

```math
\frac{\Gamma_l\vdash t_l:B\ \text{(the node's checked ordinary typing)}\qquad ⟦B⟧=\varnothing}
     {\text{node } l \text{ within } \Phi\ \text{on normal return } (\mathsf{thr}=\mathsf{false})}\ \textsf{no-return}
```

for every closed footprint $`\Phi`$. $`B`$ is the type the node's own
safety derivation gives its term, at the selected instance, after union
normalization and instantiation, and its emptiness is Lean's existing
decision that makes a slot of a type no value meets an unreachable entry
(`GraphCode.unreachableEntry`; cited): empty for `never`, for a union of
empty arms, for `die<never>()`; not for `Promise<never>`, an inhabited
promise. A guard call's term is typed at `boolean`, its promise being
about an argument, so `x is never` gives no empty $`B`$. Restriction:

- **normal return only** (`thr = false`): the node gains no exceptional
  bound, so a handler or `finally` around it is refused as today. Whether
  the node bounds its throw is decided apart, by `throwsWithin` and the
  callee's own `onThrow`, whatever its result.

**Producer.** `footprint_expr` receives callees' `call_effect` lists,
which hold neither results nor instantiations, and `proposal.ml` keeps
generic and packed-rest callees out of effect summaries. The no-return
case reads instead the producer's own typing of the call expression at
its instance (the node-typing claim it proposes for that node): where
that type is `never`, the node's normal footprint is empty, and its
exceptional summary (`throws_expr`) is left as the callee's signatures
give it. A wrong proposal fails at Lean's emptiness decision. Positive
cases cover a member call (`gate.fail`), a generic instance
(`die<never>()`), and a call of a declaration with a rest parameter.

`gate.fail` (`fail(…): never`) is called in 12 of the 125 callbacks of
§10 and is the only program member called in 4; under this rule those
calls need no statement. The rule is independent of methods and can land
first.

**Async definitions: the completion boundary.** An async function's body
runs synchronously up to its first `await`, and a throw out of it,
a failing parameter default included, does not leave the call: JavaScript
turns it into a rejected promise, which the call returns normally. The
model reads the body's throw as a throw (cited:
[async functions](../SOURCE-CONTRACTS.md#async-functions-and-await),
"a throw in an async body leaves it as a throw"). So an async call's
normal return covers the body's exceptional exits, and a normal-return
footprint certified for the body, which says nothing of its throws, is
not a footprint of the call. Two routes reach the gap once effects below
`top` exist for async code: a body ending in a call at
`(xs: number[]) => Within<Keep, never>` (met by any never-returning
function, one that pops and throws included), and `no-return` applied
inside an async body. Under Node, a `map` callback calling such an async
function leaves a hole (`async-probe/p1`–`p3` in the scratchpad).

Rule: **an async definition's effect is certified with its throws
bounded.** Its body is checked as a body claiming `onThrow` at the
statement's footprint (`GraphCode.BoundState`'s `exc`, `SafePostExc` with
$`R`$ the footprint; cited), so every node bounds the heap it raises in,
`no-return` contributes nothing there (it gives normal returns only), and
the call's signature then states the footprint on normal return. The
same rule binds inferred effects: Lean applies it to every async code
entry and async declaration unit whose claim states a footprint below
`top`, whatever the producer proposed. Today every async body's
completion calls `%AsyncReturn%` or `%AsyncComplete%`, whose signatures
are ordinary (`fn` with `ordinaryEffect`, `tools/intrinsics.mts`), so an
async definition is `top` wherever a completion is reachable; the rule
also closes the bodies with no reachable completion. Until the async
intrinsics state footprints of their own, the simplest form of the rule
is a refusal: `Within` on an async definition is refused (§3), and Lean
refuses a footprint below `top` for async code (L6).

**Main today** (0e48e9f, probed without changing the repository): the
three programs above, written without `Within` and with an unannotated
never-returning callee, are refused (`unverified`, in search, at the
return contract of `xs.map(…)`: the async function's inferred footprint
is `top`), and each leaves a hole under Node. The refusal rests on two
facts of main: a mutation before a throw is always a node of some
certified body, checked within its footprint whether or not a throw
follows; and the async completion intrinsics are ordinary. That no value
on main has a normal-return-only footprint below `top` hiding a mutation
on its throw is conjectured (by induction over certified bodies, its base
the audited native rows, each of which writes within its footprint before
any throw; not audited for that property); `Within` on a never-returning function type and
`no-return` would be the first such sources, hence the rule.

**Accessors** are outside the fragment; `Within` on one is refused with
it.

**`this` escaping.** A closure capturing `this` is a value with its own
type; storing it is a write the method's statement must bound (a `push`
onto a registry is `grow`); a later call of it is a call at its type. The
constructor reads no `this` and ends in the allocation (the parser's class
lowering; cited from the trust surface), so no instance exists before its
fields hold their initialisers.

## 7. Lean obligations

- **L1 (decoding).** Declaration-document terms and the Fragment's
  written signatures decode a statement exactly: a footprint and
  `onThrow`; anything else (a promise, `fresh`, `receiverStore`) in a
  statement is refused.
- **L2 (stated-signature obligation).** Acceptance requires, for every
  callable definition of the checked documents whose written signature
  states $`\epsilon`$, a certification of its code at that signature with
  an effect covered by $`\epsilon`$ (§4.1), read from the Fragment. For a declaration unit, `checkRequests_footprint_at` and
  `Closed.Holds.mono` (proved) give the stated footprint; for a closure,
  `codeChecked_sound` and `Effect.covers_sound` (proved). A definition
  stating an effect and lacking that certificate is a located refusal,
  never a dropped plan, so the exhaustive `FunctionPlan` → `CertifiedPlan`
  conversion is unchanged.
- **L3 (class construction).** The class statement's prototype allocation
  stores each method closure at a location whose contract implies the
  closure's certified type (L2), and the constructor's result meets the
  instance type: for an instance $`v`$ allocated with `[[proto]]` holding
  that prototype, `memberT Ξ m k W v` for every member $`m`$. The proof
  path is the existing prototype coverage (`CoversByProto`, `FoundOn`,
  `CoversArrows`), whose arrow coverage compares effects; the closure's
  `this` at the instance type refers back to $`m`$ at a lower level, the
  step-indexed argument those lemmas already make for declared
  signatures. To confirm in the code: whether today's class
  lowering already certifies a prototype closure at a qualified member
  signature (then L3 is the existing proof path at non-`top` effects) or
  only at the declared one (then L3 is new code on proved lemmas).
- **L4 (coverage).** Member and field coverage compare effects
  (`Effect.covers`, proved sound). No new theorem.
- **L5 (`no-return`).** For a node whose ordinary safety derivation types
  its term at a family empty at every level, the node's run is within any
  closed footprint on normal return (`NodeWithin` with `thr = false`):
  `SafePost`'s normal disjunct needs a value of that family. New lemma
  beside `ExpressionEffects.selected_sound`, from the node's ordinary
  safety alone, with the emptiness decision as its checked premise.

- **L6 (async completion), with trusted provenance.** The Fragment
  states, for every callable definition (function declaration, function
  expression, arrow, object-literal method, class and static method), its
  **completion kind**, `sync` or `async`, written by the parser from the
  definition's own `async` modifier (`completion`), since a throw-only
  async body lowers like a synchronous one (`asyncCompletion` adds no
  intrinsic to a body that ends in a throw) and nothing in its graph
  distinguishes them. Lean
  binds every certified unit and code entry to its definition's kind and,
  for `async`, refuses a footprint below `top` before any certification
  alternative is tried, the pure-body rule included, located at the
  definition. The kind comes from the Fragment, never from a claim, so a
  forged claim cannot drop it; it covers async methods, arrows, function
  expressions, their parameter defaults, and certified imports (the
  imported module's Fragment states its definitions' kinds). L5 lands
  with L6 or after it, never before: `no-return` inside an async body is
  the route L6 closes.

**`checkJson_safe`.** The premise stays the exact CLI success condition;
it now includes L2's check. The first conclusion (safety of every accepted
function) is unchanged. The second conclusion gives each unit claiming a
footprint other than `top` that footprint, so each stated unit its stated
one by L2; a stated closure's statement is a property of its code entry
(`CodesSound`). The inputs' `EnvOk` is at the annotations, which now state
effects where the source states them. The acceptance invariant of
AGENTS.md holds as before: the plan type and the CLI path are unchanged.

## 8. Trust

One row of the [trust surface](../DESIGN.md#trust-surface) changes
and one is added.

| Assumption | Where it is stated |
| --- | --- |
| *(changed, assumed values)* An imported value meets its declaration, a guard's declared promise **and a stated effect (`Within`) included**; … (rest unchanged). A statement occurs only in program modules' declarations; whether the exporting module's run certifies it is not a premise of the importer's acceptance (§6), and that the linked program meets every statement rests on module composition, an open theorem. | `IMPORT` in SOURCE-CONTRACTS; `Within` in `tools/effects.d.ts` |
| *(added, assumed of the host)* External code preserves every effect-bearing contract of the program's values it holds or returns: it writes no function field of a program value with a function outside the field's statement, creates no own member on a program class's instance that shadows a prototype member, deletes no such member, writes no member of a program class's prototype or static method binding, replaces no instance's prototype, and passes to verified code no instance of a subclass whose override exceeds the base's statement. Conforming to a program type means TScert's contract, statements included, not TypeScript's assignability, which erases `Within`. | `EnvOk` over the input types; the caller contract row; the class lowering in `tools/fragment-classes.mts` |

The trusted front end gains the reading of `Within` (§3) and each callable
definition's completion kind (L6), part of the parser row's "represents the
source faithfully". Inference gains no
trust: a forged statement claim fails at the first node outside it.

A separate prerequisite with its own row change: §10's first callbacks
call `node.getStart`, which the
[compiler API](../COMPILER-API.md#node-methods-and-callbacks) reads at
its declaration, with no effect. T3 states the node methods make no server
request, run no client code **but `forEachChild`'s visitors**, and change
no stable member; T4 that their hidden effects are observed by no
transparent operation (cited). The extension states
`{value: keep, store: keep}` with `onThrow` for the callback-free node
methods only: `getText`, `getStart`, `getEnd`, `getFullStart`,
`getWidth`, `getFullText`, `getSourceFile` and
`getLineAndCharacterOfPosition`. `forEachChild` keeps its declared
signature, its effect the visitor's by the ordinary rule for a function
value passed to a callee, unrestricted unless that rule is given a
callback-dependent footprint signature of its own.

## 9. Bypass attempts, as future cases

Each negative case runs under Node where a run can show the hole or the
`undefined`; each forged claim is refused in search and in checking.

| Case | Attempt | Refused at |
| --- | --- | --- |
| `invalid-method-effect-override` | `class D extends C` overrides `C.m: Within<keep>` with a body that pops the mapped array; a `D` passed as `C` | `D`'s construction: the override is checked against the met member (§4.2) |
| `invalid-method-field-effect-write` | `gate.f = (n) => { xs.pop(); … }` after construction | the write: the field's contract states the effect |
| `invalid-method-field-effect-alias` | `const h: { f: (this: Gate, n: N) => R } = gate; h.f = popper;` | the subsumption `Gate ≤ {f: …}` (invariant field contract) |
| `invalid-method-effect-borrowed` | `xs.map((x) => gate.span.call(other, x))` | the parser (`refuseReceiverForm`) |
| `invalid-method-effect-interface` | `i: I` with `I.m` unstated; a callback calls `i.m` | the callback is unrestricted: `map` with holes, refused at the return contract |
| `invalid-method-effect-lookalike` | an object literal with a popping `m` passed where `C` (stating `keep`) is expected | the subsumption: effect coverage |
| `invalid-method-effect-this-alias` | `C` holds `xs` in `this.xs`; `c.xs.map((x) => c.bump(x))` with `bump` popping `this.xs` and stated `keep` | `bump`'s statement (L2); stated honestly (`top`), `map` with holes |
| `invalid-method-effect-unused` | `export const bad = (xs: number[]): Within<Keep, number> => { xs.pop(); return 0; }`, never called in its module | the arrow's stated-signature obligation (L2) |
| `invalid-method-effect-default` | `function bad(xs: number[], x = xs.pop()): Within<Keep, number>` | the declaration's statement (L2): the default is a node of its graph |
| `invalid-method-effect-overload` | overloads `(xs, flag: true): Within<Keep, number>` and `(xs, flag: false): number` | the parser (§3): no statement on an overload |
| `invalid-method-effect-top` | `Within<{ value: "any"; store: "any"; onThrow: true }, never>` | the parser (§3): a `top` statement states nothing |
| `invalid-method-effect-qualified` | `identity<T extends Resolvable>(x: T): Within<Keep, T>` | the parser (§3): a qualified declaration states no footprint |
| `invalid-method-effect-static` | a static method stated `keep` that pops | its statement (L2) |
| `invalid-method-effect-throw-caught` | `bump` pops then throws (`keep` on normal return); the callback catches it | the callback's handler: no `onThrow` on `bump` |
| `invalid-method-effect-onthrow` | `bump` pops then throws, stated `onThrow` | `bump`'s statement (`SafePostExc`) |
| `invalid-method-effect-escaped-this` | a method pushes `() => this.xs.pop()` into a registry; the callback calls `registry[0]()` | the callback: the closure's type is `top` |
| `invalid-method-effect-external` | a dependency's `.d.ts` states `Within` on a function | the parser (§3) |
| `invalid-method-effect-misplaced` | `Within` on a parameter, an element type, a getter, a guard's result | the parser (§3) |
| `invalid-method-effect-async` | an async method stated `keep` | the parser (§3): no statement on an async definition |
| `invalid-async-rejection-effect` | `async run(xs, stop: (xs: number[]) => never) { return stop(xs); }`, a `map` callback calling `run` (and the variants with a default `n = fail(xs)` and a never-returning module function) | `run`'s footprint is `top` (L6); a hole under Node |
| `invalid-async-rejection-forged` | the same with `run`'s claim forged at `keep` | L6, in search and in checking |
| `invalid-async-throw-only-forged` | `async function run(xs, stop) { stop(xs); throw 0; }` (no reachable completion intrinsic), claimed `keep`; the same as an async arrow, an async method, and with the throw in a parameter default | L6 from the Fragment's completion kind, in search and in checking; a control drops the kind from the claims and is still refused |
| `invalid-method-effect-prototype` | `C.prototype.m = popper`, `Object.setPrototypeOf(c, evil)`, `c.__proto__ = evil` | the parser and the overlay: none is in the fragment |
| `invalid-method-effect-import` | module A states `keep` on `f` whose body pops; module B maps with a callback calling `f` | A's run (located); B verifies relative to the import assumption: the control shows A refused and records B's acceptance as conditional |
| `invalid-no-return-onthrow` | `die(xs): never` (unstated) pops then throws; a `map` callback catches it and claims `keep` | the handler: `no-return` gives a normal-return bound only |
| `invalid-no-return-guard` | `isNever(xs, x): x is never` pops and returns `false`; a `map` callback calls it | `no-return`: the call's term is typed at `boolean` |
| `invalid-node-visitor-effect` | `node.forEachChild(() => { xs.pop(); })` in a `map` callback | `forEachChild` is not among the stated node methods |
| `invalid-method-effect-implementation` | overload `bad(xs): number` with implementation signature `bad(xs): Within<Keep, number>` that pops | the parser (§3): no statement on an overloaded declaration |
| `invalid-method-effect-external-typeof` | a dependency declares `export const evil: typeof good` with `good` stated `keep`; its JavaScript pops | the parser (§3): a statement in an external value's effective type |
| `invalid-method-effect-assign` | `Object.assign(o, { f: popper })` with `o` a parameter whose type states `f`'s effect | the ownership rule of `Object.assign` (aliased target) |
| `invalid-no-return-promise` | an async function returning `Promise<never>` that pops, called in a `map` callback | `no-return`: `Promise<never>` is inhabited |
| forged claims (`pipeline/test.mts`) | a method's code entry claimed `keep` while its body pops; a declaration claimed within its statement while its loop leaves it; a stated definition's claim withheld; a `no-return` node at a non-empty result | search and checking; accepted only with the L2 check disabled |

The external-code bypasses (an own `m` created on an instance by external
code, an external subclass, an external write of a `Gate` method field)
are not program inputs TScert can refuse: they are what the added row of
§8 excludes, each run under Node as a counterexample to the assumption.

Positive cases: `method-effect-map` (a class method stated `keep`, a `map`
callback calling it, dense result), `method-effect-field` (a method field
`f: typeof g = g`, `g` stated), `method-effect-recursive` (two methods
calling each other, stated), `method-effect-subclass` (an override within
the base's statement), `method-effect-arrow` (a stated arrow in a fresh
literal's field), `method-effect-import`, `no-return-callee-map`.

## 10. Measurement

**Scan.** An AST scan of `tools/*.mts` at d99275a with TypeScript 5.8's
checker (`scratchpad/scan/ast-scan3.cjs`, rows in `ast-rows3.json`), rerun
at 0e48e9f; an independent scan under TypeScript 6.0.3 reproduced the
count.
Counted: a call `r.m(cb, …)` with `m` among `map`, `find`, `findIndex`,
`some`, `every`, `filter`, `forEach`, `flatMap`, `findLast`,
`findLastIndex`, `r` typed by the checker as an array, a tuple, a readonly
array or a `NodeArray` (every arm of a union), and `cb` an arrow or
function expression whose own body, excluding every nested function body
(arrows, function expressions and declarations, methods, accessors,
constructors) and every nested class, calls
a member the checker resolves to a declaration of the program. A nested
callback is its own row; a call inside it is attributed to it alone.
These are syntactic hits, not verdicts: what blocks each enclosing
function first is the census's to show. **125 callbacks**:

| Group | Callees | Callbacks | Enclosing functions |
| --- | --- | --- | --- |
| A | `Gate` members that read: `span`, `local`, `fail`, `hasTypeParam`, `typeParamName` | 49 (46 `map`) | 9: `classBody`, `enumMembers`, `expr`, `lambda`, `lowerFile`, `neverAssigned`, `protocolPattern`, and the methods `Gate.declaredReference`, `Gate.termScope` |
| B | A plus `typeOf`, `optionalTypeOf`, `closureParamType`, `restType`, `moduleRestType` | 3 (all `map`) | 3: `expr`, `lambda`, `functionDecl` |
| C | a `Gate` method field (`expr`, `pattern`, `inert`, …) or `spreadOperand` | 41 (26 `map`) | 19 |
| S | members of type literals and interfaces (function-valued fields of records such as a scope's `fail`, `libraryFile`) | 32 (10 `map`, 9 `filter`, 7 `flatMap`) | 12, outside the `fragment-*` modules |

Of C's 26 `map` callbacks, 15 map a value the checker types
`NodeArray<…>` and 2 a union with one.

**Census.** The census of e9dfc1a (436 slices: 140 verified, 106
unverified, 190 unsupported) names a method effect as the first blocker
of none; `enumMembers` and `enumOpen` stop at "no derivation of its
return-contract claim" at a span conjectured to be the
`info.members.map` whose callback calls only `gate.fail` (to confirm by
the slice). The class recurs as other blockers clear: `protocolPattern`
and `patternStmt` met it twice (`gate.abrupt`, `named.map` with
`gate.local`), each removed by a rewrite. Gains are conjectured until the
slices below show them.

**Steps, each measured on its hub slice and one dependent (`make census
FILES=… FUNCTIONS=…`, before and after):**

1. `no-return` (L5), with L6 in the same change: the 4 callbacks calling only `fail`
   (`enumMembers`, `classBody`, `expr`, `protocolPattern`). Slices:
   `fragment-classes.mts#enumMembers`, `#enumOpen`. Cost: the node lemma
   and its premise (the existing emptiness decision), the producer case
   reading its own node typing, and cases: a member call, a generic
   instance at `never`, a rest declaration's call, `Promise<never>`
   refused, a caught throw refused, a guard refused, a forged no-return
   node at a non-empty type refused.
2. The T3 extension (§8): prerequisite of `span`, `local` and `fail`'s
   bodies. Cost: family entries, the audit, its controls.
3. `Within` (§3, L1–L4) and statements on `Gate`'s group-A members, then
   B's where `typeTerm` (`type-term.mts`) certifies within a stated
   footprint (unknown until measured). Slices:
   `fragment-classes.mts#classBody` and `fragment-statements.mts#neverAssigned`
   (`lowerFile` is unsupported at an earlier blocker). Cost: the parser's
   reading and refusals, the Fragment's stated signatures, the producer
   reading statements and bounding claims by them, Lean L1–L3, about 25
   cases.
4. Group C, by either route: (i) statements on the method-field
   functions, which needs the producer to propose footprints for field
   writes (`Write _ -> None` in `footprint_expr` today) and for `try …
   finally` (`None` today; `lambda` and `functionDecl` restore state in
   `finally`, which needs `onThrow` on every call inside), and the `shift`
   rewrites of §5; or (ii) for the 15 node-list callbacks, the
   family-sensitive `map` of §5, with no method effect. (ii) is smaller;
   (i) covers the rest.
5. Group S takes statements on its record types' function fields by the
   same rule; no further mechanism.
6. After 3, the two rewrites made for this class
   ([SOURCE-REWRITES](../SOURCE-REWRITES.md)) may be reverted where the
   original form then verifies; a measurement of the design, not a
   requirement.

## 11. Decisions for the owner

- **D1** where a member's effect lives across runs: (a) stated
  (recommended), (b) certified in every run, (c) exact instances (§2).
- **D2** the statement's spelling: `Within<{ value; store; onThrow? }, T>`
  at a result, read by declaration identity (recommended), or a smaller
  set of named aliases (`Keeps<T>`, `Grows<T>`).
- **D3** `no-return` (§6) as an independent first step (recommended).
- **D4** T3's extension to the callback-free node methods' footprints, `forEachChild` excluded (recommended, its
  own change and trust row).
- **D5** reachability stays deferred; `Gate`'s `shift` stacks are
  rewritten instead (recommended); the node-list stable store is
  investigated as its own host-family item.
- **D6** an override whose effect exceeds its base's statement is refused
  at the subclass even when no instance is upcast (follows from the
  existing meet; recommended), a restriction relative to TypeScript.
