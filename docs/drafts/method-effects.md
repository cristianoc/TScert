# Draft: class methods' effects

The design of class methods' effects; its status and the owner's decisions
on it are in [WORK](../../WORK.md#class-methods-effects). Base: TScert main at ffd7b87.
Claims are labelled **proved** (with the Lean name), **cited** (with the
document and its scope) or **conjectured**.

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

**Declaration.** The verifier's declaration file `tools/resolvable.d.ts`,
which already declares `Resolvable` and `Awaitable`, declares

```ts
type Footprint = { value: "keep" | "any"; store: "keep" | "grow" | "any"; onThrow?: true };
type Within<F extends Footprint, T> = T;
```

A reference is a statement when TypeScript binds its name to that `Within`,
never by its spelling: the declaration reader asks the checker for the
reference's declaration; the gate reads a file's references as the
declaration reader reports them, unshadowed by a type parameter or a
block's type, as it reads `Resolvable`. `tools/tsconfig.json` lists the
file, so TScert's own modules may write statements.

TypeScript reads `Within<F, T>` as `T`. TScert reads it in one position,
the result annotation of a written signature, with $`F`$ a type literal
written in place whose members are `value` and `store`, each at a string
literal type, and optionally `onThrow?: true`:

```math
\frac{⟦\vec A⟧=\vec P\qquad ⟦T⟧=B\qquad F=\{\mathsf{value}{:}\,v,\ \mathsf{store}{:}\,s[,\ \mathsf{onThrow}]\}\qquad \{v,s\}\neq\{\mathsf{any},\mathsf{any}\}}
     {⟦(\vec x:\vec A)\Rightarrow\mathtt{Within}\langle F,T\rangle⟧=\mathcal F_{\epsilon(F)}(R,\vec P,B)}\ \textsf{stated-effect}
```

with $`\epsilon(F)`$ the effect of the closed footprint $`\{v,s\}`$,
`onThrow` as written, no promise, no fresh result, no receiver-store
exception. The written signatures are those of a function declaration, a
class's instance or static method, an object literal's method, an arrow, a
function expression, a function type, and an interface's or a type
literal's method or call signature. `typeof f` reads `f`'s declaration, so
it reads the statement too, and every reader of a signature (the
declaration reader for a declaration a type reaches, the gate for a
definition it lowers) reads it through the one function that reads a
signature's result (`signatures` in `tools/type-term.mts`).

**Refusals**, each located:

- `Within` anywhere else: a parameter, an element, a type argument, a field,
  a guard's promised type, inside another `Within`. The declaration reader
  refuses a reference resolving to `Within` or `Footprint` wherever it
  resolves one, so no reader can read `Within` as the alias it is;
- $`F`$ other than a type literal of that shape (an alias of one included);
- a statement whose footprint is `{value: any, store: any}`, with or
  without `onThrow`: it states nothing the ordinary effect does not, a
  throw's heap being unconstrained by that footprint too;
- a statement on any signature of an overloaded declaration, the
  implementation's included: a declaration's unit is certified at one
  signature;
- a statement on an async definition: its throw is its promise's rejection
  (§6);
- a statement on a declaration with a resolution-qualified type parameter
  (`T extends Resolvable` or `Awaitable`): such a unit claims no footprint
  (`effectResult`);
- a statement on a guard's or an assertion function's result, an accessor,
  a constructor or a construct signature;
- a statement read from a declaration outside the program's sources (a
  declaration file, a package, an ambient `declare` declaration), and any
  statement reached from the type of a value declared there, through
  `typeof`, an alias, an interface or an indexed access, other than a
  member of a class the program declares (§8). The declaration reader
  records the definitions whose equations read a statement, and walks each
  such value's type and the definitions it references, a program class
  excepted, refusing the value where it meets one.

**Wire.** Two documents carry a statement:

- the **declaration document**'s function and constructor terms carry
  `effect: CallEffect` (`tools/declaration-types.mts`). A signature's
  statement is that term's effect; an unstated signature keeps the ordinary
  effect;
- the **Fragment**'s callable definitions, `FunctionAst` and `lambda`
  (function declarations, function expressions, arrows, object-literal
  methods, class and static methods), carry `stated: { footprint:
  ClosedFootprint; onThrow: boolean } | null` beside their result
  annotation, the statement of their written signature, or `null`. The
  claims never supply it.

## 4. Certification: where every statement is proved

Every value the program introduces at a type stating an effect meets it,
and Lean checks each introduction.

1. **Every callable definition (the stated-signature obligation, L2).** For
   a definition whose Fragment states $`\epsilon`$, Lean requires its
   certified effect to be within $`\epsilon`$, located at the definition,
   whether or not any code calls it:
   - a function declaration's unit: its claim's footprint $`\Phi`$ and
     on-throw flag satisfy $`\Phi\le\epsilon.\mathsf{footprint}`$ and
     $`\epsilon.\mathsf{onThrow}\Rightarrow`$ the claim's; the unit is then
     certified at $`\Phi`$ (`declaration-effect`,
     `checkRequests_footprint_at`, proved), so at $`\epsilon`$
     (`Closed.post_mono`, proved). The unit's inputs are its annotated
     parameters and receiver (`moduleArrow`, the unit's own frame), so the
     certification covers the written signature's whole domain;
   - a lambda (a closure, a class or static method): a claim may offer a
     closure at signatures narrower than its annotation
     (`ClosureSetup`'s `requireWithin` checks only that each offered row is
     within it), so the statement is proved as a written promise is,
     whatever the claim offers: **some** row the code is checked at
     admits the annotation's whole domain (its receiver contains the
     annotated receiver, each of its arguments the annotated one, a
     defaulted one with `undefined`, at the annotation's arity), returns
     within the annotated result, and has an effect covering $`\epsilon`$
     (`Effect.covers`). The code is certified at that row
     (`codeChecked_sound`, proved), so at $`\epsilon`$ over the written
     signature (`Effect.covers_sound`, proved). A lambda with no such row,
     one claimed at no call signature included, is a located refusal. A
     closure collecting a rest array is checked at the row its annotation
     states (`ClosureSetup`'s own row), whose effect is the annotation's:
     the statement where there is one, the ordinary effect otherwise. A
     generic closure's rows are its scheme's, compared at its binders.
   Both run parameter defaults as nodes of the checked graph. The claim may
   be stronger than the statement; other units of the run read the claim,
   as today, and other runs read the statement.
2. **Class construction (L3).** A class method's statement is part of the
   instance type's member, so the constructor's result, checked at the
   instance type, finds each member on the prototype (`memberT … along 1`)
   at a contract whose coverage compares effects; the prototype holds each
   method's closure at its claimed type, which L2 makes within the
   statement. A static method's binding is checked at its annotation, the
   statement included. For a derived class the instance type meets its
   base's members, so an override is checked against the base's statement
   (D6). This is the existing path; a control drops a method's `stated`
   from the Fragment and is still refused, at the construction.
3. **A method field** `f: typeof g = g` (the `Gate` convention). The
   field's contract is its annotation, which reads `g`'s statement; the
   initialiser `g` is read at its claim or its declaration and meets it by
   L2 or reflexivity. A later write `o.f = h` is checked at that contract
   (`field-call`; cited), so `h` must meet the statement. A copy into a
   fresh literal allocates new locations at the copy's type; `Object.assign`
   onto an existing object is admitted only where the target is an owned
   local object (`growSites`), so the original location is never written.
4. **Any other value at the type**: an object literal or another class's
   instance passed where `C` is expected meets `C` by subtyping, whose
   member and field coverage compares effects (`Effect.covers` in
   `PositiveRules`/`PositiveCertificates`, `Effect.covers_sound`; proved),
   and whose writable fields require contract agreement both ways. A union
   host binds a member only where every arm's member covers the claimed
   signature (`bind-union-host`; cited).
5. **Inputs.** A unit's inputs at an effect-stating type meet it by
   `EnvOk`: the theorem assumes of an input what its annotation says.
6. **Imports.** An import is read at its declaration, statement included
   (`import` rule; cited). That the imported value meets it is the import
   assumption (§8), conditional as §6 states. A certified import's unit is
   certified in the importer's run, L2 included.

A call then uses the existing rules unchanged: `bindMember` covers the
claimed signature by the member's, effects included, and `field-call`
gives $`B\;!\;\epsilon`$ for the field's contract. A callback whose calls
are all within $`\Phi`$ is within $`\Phi`$ (`selected_sound`; proved), and
the natives' per-footprint signatures follow: `map` dense for $`\Phi`$ in
the stable set (`map_rely`, `stableDenseClosed_sound`; proved),
`find`/`findIndex` at `T` for the empty footprint.

**Which receivers qualify.** Every receiver whose type states the
member's effect, by any of 1–6; no receiver whose type does not.

| Candidate condition | What the rule does instead |
| --- | --- |
| no subclass overrides `m` | an override is checked against the base's statement at its class (2) |
| a final class | not needed: subclassing is checked at the subclass |
| a `readonly` method field initialised once | not needed: every write is checked at the field's contract (3); `readonly` stays a view |
| a field reassigned after construction | the write is checked (3); a writable alias `{f: F}` without the statement is no supertype, since an invariant field's contract must agree with the alias's (`SlotContract`; cited [POSITIVE-TYPES](../POSITIVE-TYPES.md)) |
| a method read off an interface | the interface's member states its effect or none; values meeting the interface are checked at introduction (4, 5) |
| a borrowed method `o.m.call(r, …)` | refused (`refuseReceiverForm`; cited): `.call`, `.apply` and `.bind` are admitted on known local functions only |

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
| write of a variable's cell, or of a field holding a source value | `{value: any, store: keep}` (`write_within`; proved) |
| `push`/`unshift` on any array | `{value: any, store: grow}` (audited native row) |
| `Map`/`Set` mutators | at most `{value: any, store: keep}` (audited) |
| `pop`/`shift`/`reverse` on a store the call did not allocate | `top` (receiver-store exception; cited) |
| allocation, reads, tests | empty (`inspect_safe`; proved) |
| a call | its callee's signature's effect (`selected_sound`; proved), empty on normal return at a callee result no value meets (`no-return`; proved) |

So `Gate`'s members that only read, write fields and cells, set maps and
push stay within `{value: any, store: grow}`, in the stable set for
density.

**Reachability stays deferred (D5).** Showing that a call whose footprint
lets stores change beyond `grow` cannot reach a given local array is the
[deferred precision](../FOOTPRINTS.md#deferred-extra-precision). The
operations outside `grow` among `Gate`'s lowering code are, by a search of
`tools/fragment-*.mts` for `shift`, `pop`, `splice`, `reverse`, `sort`,
`fill`, `copyWithin`, `length =`, `clear` and `delete`: the `shift`s of its
two scope stacks (`enterTypeParams`/`leaveTypeParams`,
`tools/fragment-parse.mts` 464–472), and the closing region's
`entries.shift()`/`spans.shift()` of `protocolForOf`
(`fragment-statements.mts` 946–947). The
others act on arrays the code allocated (`work.shift()` in `parseModules`,
`rest.splice` in `fragment-parse.mts`, the `sort`s of `fragment-classes.mts`
and `intrinsics.mts`), or are not reached from a `Gate` method
(`opened.clear()` in `close`); conjectured from the code. The rewrite, an
exception to the no-rewrite rule approved for the statements that need it
([SOURCE-REWRITES](../SOURCE-REWRITES.md); it lands with them, §10):

- `this.typeParamScopes.shift()` and `this.resolutionScopes.shift()` become
  `this.typeParamScopes = this.typeParamScopes.slice(1)` and the same for
  `resolutionScopes`, whose fields lose `readonly`: a field write of the
  remaining list, `{value: any, store: keep}`. Every reader reads the stacks
  through `this` (`hasTypeParam`, `typeParamName`, the resolution scope),
  and no reader keeps either outer array (the resolution scope keeps inner
  entries, which `slice(1)` preserves), so replacing the array is
  unobservable. `leaveTypeParams` keeps its order (the resolution stack
  first) and its refusal of an empty type-parameter stack;
- `entries.shift()` and `spans.shift()` become reads at an index each list's
  own counter advances, `entries[e++]` and `spans[s++]`, each keeping its
  exhaustion check (`?? gate.fail(…)`): a cell write and an element read.

A regional effect would be one more form of the same statement, certified
by the same rule, so nothing here changes when it lands.

## 6. Recursion, exceptions, async, accessors, `this`

**Recursion.** A body is checked against its own statement with every
callee read at its statement or, within the run, its claim. Mutual
recursion needs no fixpoint in Lean: each body consumes types, never
bodies. Within a run the producer's greatest fixpoint proposes claims for
unstated declarations as today; for a stated one it proposes its inferred
footprint where that is within the statement, and the statement otherwise,
which Lean then checks node by node.

**Scope across modules: conditional.** A run's acceptance certifies its
own definitions' statements (§4.1) and is relative to its imports meeting
theirs: if `b.ts` states `keep` on `g` and pops, `a.ts`, calling `g` in a
`map` callback, verifies under the import assumption while `b.ts`'s run is
refused. That the linked program meets every statement needs every
module's run to pass and the [module composition](../../WORK.md#module-composition)
theorem, which is open; until then a statement's cross-module use is the
import assumption, a review obligation of §8, as a declared type's is.
A census slice's own definitions are a copy of its module's, so a verified
slice certifies their statements relative to the statements of what the
slice imports, the module's other functions included.

**Exceptions.** A statement without `onThrow` holds on normal return only
(`SafePost`). A handler covering a call at a signature without `onThrow`,
and a `finally` reached from it, is refused in bounded certification
(`GraphCode.NodeWithin`'s `thr`), so a caller that catches a stated
method's throw gains nothing (`invalid-method-effect-throw-caught`). A
statement with `onThrow` is certified with `SafePostExc`, so a pop before
a throw refutes it. A call typed `never` is within every footprint on
normal return (`no-return`; [footprints](../FOOTPRINTS.md); proved), so
`gate.fail` needs no statement.

**Async definitions.** An async call returns its promise where its body
throws, so Lean certifies async code at `top` (`asyncEffects`, from the
Fragment's `completion`), and the parser refuses a statement on an async
definition. Lean refuses one too, by the definition's `completion`, before
any other check: a stated async definition is a located refusal, whatever
its claim.

**Accessors** are outside the fragment; `Within` on one is refused with
it.

**`this` escaping.** A closure capturing `this` is a value with its own
type; storing it is a write the method's statement must bound (a `push`
onto a registry is `grow`); a later call of it is a call at its type. The
constructor reads no `this` and ends in the allocation (the parser's class
lowering; cited from the trust surface), so no instance exists before its
fields hold their initialisers.

## 7. Lean obligations

- **L1 (decoding).** The Fragment's `stated` decodes to a closed footprint
  and a flag, exactly; the declaration document's effect decodes as for
  natives. The parser never writes a promise, `fresh` or `receiverStore`
  into a statement, and `stated` has no field for them.
- **L2 (stated-signature obligation).** For a unit, `checkRequestsResult`
  requires the coverage of §4.1 (and, for an async unit, no statement)
  before any certification alternative is tried; a failure is a located
  refusal, never a dropped plan, so the exhaustive `FunctionPlan` →
  `CertifiedPlan` conversion is unchanged. A lemma beside
  `checkRequests_footprint_at` states that an accepted stated unit's run
  meets its statement (`Closed.post_mono`). For a lambda, the lowering
  (`ClosureSetup`, beside the guard obligation) requires the full-domain
  row of §4.1 among the rows it records as code requests, each of which the
  code table checks; the stated closure's value is then at a type with that
  row, so every reader of its declaration's statement reads a signature its
  checked code meets.
- **L3 (class construction).** The existing prototype coverage
  (`CoversByProto`, `FoundOn`, `CoversArrows`), whose arrow coverage
  compares effects; no new theorem. A control shows it independent of L2.
- **L4 (coverage).** Member and field coverage compare effects
  (`Effect.covers`, proved sound). No new theorem.

**`checkJson_safe`.** The premise stays the exact CLI success condition;
it now includes L2's check. The conclusions are unchanged: the second
gives each unit claiming a footprint other than `top` that footprint, so
each stated unit its statement by L2's lemma. The inputs' `EnvOk` is at the
annotations, which state effects where the source states them. The plan
type and the CLI path are unchanged.

## 8. Trust

One row of the [trust surface](../DESIGN.md#trust-surface) changes, one is
added, and four extend existing rows.

| Assumption | Where it is stated |
| --- | --- |
| *(changed, assumed values)* An imported value meets its declaration, a guard's declared promise **and a stated effect (`Within`) included**; … (rest unchanged). A statement occurs only in program modules' declarations; whether the exporting module's run certifies it is not a premise of the importer's acceptance (§6), and that the linked program meets every statement rests on module composition, an open theorem. | `IMPORT` in SOURCE-CONTRACTS; `Within` in `tools/resolvable.d.ts` |
| *(added, assumed of the host)* External code preserves every effect-bearing contract of the program's values it holds or returns: it writes no function field of a program value with a function outside the field's statement, creates no own member on a program class's instance that shadows a prototype member, deletes no such member, writes no member of a program class's prototype or static method binding, replaces no instance's prototype, and passes to verified code no instance of a subclass whose override exceeds the base's statement. Conforming to a program type means TScert's contract, statements included, not TypeScript's assignability, which erases `Within`. | `EnvOk` over the input types; the caller contract row; the class lowering in `tools/fragment-classes.mts` |
| *(extended, the parser row)* The parser reads `Within` (§3) and refuses it where §3 does. | `tools/type-term.mts` (`signatures`), `tools/declaration-graph.mts`, `tools/fragment-expressions.mts` (`lambda`), `fragment-statements.mts` (`functionDecl`) |
| *(extended, T3 of the compiler API, D4)* The callback-free node methods `getText`, `getStart`, `getEnd`, `getFullStart`, `getWidth`, `getFullWidth`, `getLeadingTriviaWidth`, `getFullText`, `getSourceFile` and `SourceFile.getLineAndCharacterOfPosition` change no location of the model on normal return or throw (T3: no server request, no client code, no stable member changed; T4: their hidden effects are observed by no transparent operation). The family description states each, with its reviewed declaration text, at `{value: keep, store: keep}` with `onThrow`; `forEachChild` is the next row's. | the family description in `tools/compiler-api.mts`; [COMPILER-API](../COMPILER-API.md#node-methods-and-callbacks) |
| *(extended, T3 of the compiler API, D7)* `forEachChild` runs no code of the program but its visitors, so a call of it whose visitors are within a closed footprint $`\varepsilon`$ is within $`\varepsilon`$; it is read with one signature per closed footprint (§12). | `tools/compiler-api.mts`; [COMPILER-API](../COMPILER-API.md#node-methods-and-callbacks) |
| *(extended, T6 of the compiler API, D8 (a))* A sync API request runs no code of the program but its instance's `fs` callbacks and the `toJSON` methods and getters of the program's objects among its arguments. A request whose arguments are primitives and host objects is read at `{value: any, store: grow}`, and the six that may receive an object of the program at their declared signatures (§12). | `hostViews` and `serializingRequests` in `tools/compiler-api.mts`; [COMPILER-API](../COMPILER-API.md#the-sync-api) |

Inference gains no trust: a forged statement claim fails at the first
node outside it.

## 9. Cases

Each negative case runs under Node where a run can show the hole. The
controls on a forged stated declaration and on a stated closure claimed at a
weaker effect are refused in search and in checking, and certified with the
check removed (the `stated` mutation); those on a narrowed domain, a dropped
statement and a statement written into a generic closure's Fragment are
refused in search.

Positive:

- `method-effect-map`: a class method stated `{value: any, store: grow}`
  that pushes onto a field, a `map` callback calling it, dense result;
- `method-effect-field`: a method field `f: typeof g = g`, `g` a stated
  module function, called in a `map` callback;
- `method-effect-recursive`: two stated methods calling each other;
- `method-effect-subclass`: an override within the base's statement;
- `method-effect-interface`: an interface member stated `keep`, met by an
  object literal's method, called in a `find` callback, result at `T`;
- `method-effect-arrow`: a stated arrow in a fresh literal's field;
- `method-effect-static`: a stated static method;
- `generic-stated-declaration-refused` (a gap): a stated generic
  declaration, certified at its statement, whose instances callers read at
  its declared signature without a footprint;
- `method-effect-onthrow`: a statement with `onThrow` whose caller catches.

Negative:

| Case | Attempt | Refused at |
| --- | --- | --- |
| `invalid-map-method-call-effect` | (existing) an unstated method of a structurally typed object | the callback is unrestricted |
| `invalid-method-effect-unused` | a stated arrow that pops, never called | L2 at the arrow |
| `invalid-method-effect-declaration` | a function declaration stated `keep` that pops | L2 at the declaration |
| `invalid-method-effect-default` | a default `x = xs.pop()` beside a `keep` statement | L2: the default is a node |
| `invalid-method-effect-method` | a class method stated `keep` that pops, called in a `map` callback | L2 at the method |
| `invalid-method-effect-override` | an override popping, beyond the base's `keep` | the derived class's construction (D6) |
| `invalid-method-effect-lookalike` | an object literal with a popping `m` passed where an interface stating `keep` is expected | the subsumption: effect coverage |
| `invalid-method-field-effect-write` | `o.f = popper` for a field stating `keep` | the write |
| `invalid-method-effect-unstated-dependency` | a stated `run(this: G)` calling `this.helper()`, `helper` a method field stating no effect; a `G` whose `helper` pops, run under Node | L2 at `run`: the call is unrestricted |
| `invalid-method-effect-static` | a static method stated `keep` that pops | L2 |
| `invalid-method-effect-throw-caught` | (existing, now with a statement) `bump` pops then throws, stated `keep`; the callback catches | the handler: no `onThrow` |
| `invalid-method-effect-onthrow` | `bump` pops then throws, stated with `onThrow` | L2 (`SafePostExc`) |
| `invalid-method-effect-overload` | a statement on an overload | the parser |
| `invalid-method-effect-top` | `{ value: "any"; store: "any" }` | the parser |
| `invalid-method-effect-async` | an async method stated `keep` | the parser |
| `invalid-method-effect-misplaced` | `Within` on a parameter, an element, a guard's result, a getter | the parser |
| `invalid-method-effect-alias` | $`F`$ written through an alias | the parser |
| `invalid-method-effect-external` | a package's declaration stating `Within`, and one typed `typeof` a stated program function | the parser |
| `invalid-node-visitor-effect` | `node.forEachChild(() => { xs.pop(); })` in a `map` callback | `forEachChild` states no footprint |

Positive besides: `method-effect-rest`, a stated closure collecting a rest
array; and the negative `invalid-method-effect-rest-default`, a stated
closure with a rest whose default pops.

Controls (`pipeline/test.mts`): a stated definition's claim forged above
its statement (a unit and a code entry), refused in search and in checking;
a stated arrow's and a stated generic or static method's claim forged at a
narrowed domain (a parameter at `never`, a receiver narrower than the
annotation) at a covering effect, refused (the full-domain row); the
Fragment's `stated` of a method dropped while its class's instance type
states it, refused at the construction (L3 independent of L2); an importer
of a module whose stated function pops, verified relative to the import
assumption while the module's own run is refused.

## 10. Measurement

In the census of ffd7b87 (the draft's base, whose functions state no effect), slices at 300 s: `fragment-statements.mts#pattern`,
`#forOfPattern`, `#protocolPattern`, `#patternStmt`, `#abrupt` unverified
(each "no derivation of its binding-annotation claim" at a `map`'s result);
`#patternDefaults`, `#steppedPattern`,
`fragment-expressions.mts#moduleFunction` verified;
`fragment-classes.mts#classBody` unsupported at an earlier blocker.

**A statement holds over its whole declared domain.** A statement on
`m(this: C, …)` promises its effect for every receiver of type `C`, so every
call in `m`'s body must be at a contract stating an effect within it: a
stated program declaration or member, a native or host entry stating a
footprint, a callee typed `never`, or a function the body itself defines.
A call of an unstated member of `C`, or of a callback parameter whose type
states no effect, defeats the statement, since a value of `C` may hold any
function there. Lean checks this wherever it certifies the definition (each
call at its selected signature); a statement on a definition no run
certifies is written only where this **contract closure** is closed, which
the record of the commit writing it shows by listing its body's callees.

**A statement is an annotation, and its certification is measured as an
annotation's is.** A statement on a program function is certified where a
run checks that function's code: its module's run, or a census slice
holding it. A slice that verifies while calling a stated function its own
run does not check is verified relative to that statement, as it is
relative to every imported declaration (§6): conditional evidence, which
the measurement reports with every statement a slice relies on and whether
that statement's definition is certified by a verified slice.

**The statements.** Three groups:

- the class methods of `Gate` that array callbacks reaching no `expr` call
  (in `classBody`, `neverAssigned` and `moduleFunction`):
  `span`, `local` and `hasTypeParam`, each reading the node's position
  (`getStart`, D4), a `Map` (`get`, `has`) or an array (`some`), at
  `{value: keep, store: keep}`, and `typeParamName`, iterating an array, at
  `{value: any, store: keep}`; `fail` is typed `never` and needs none;
- the method fields' module functions `patternDefaults` and `inert`
  (`{value: keep, store: keep}`: reads, guards, `flatMap`/`every` callbacks
  calling themselves) and `steppedPattern` (`{value: any, store: keep}`:
  its `forEach` callback writes a captured cell);
- `expr`'s contract closure (§12): every function `expr` and the gate's
  `TermScope` object reach, at `{value: any, store: grow}` unless a smaller
  footprint holds, with D5's rewrite of the `shift`s in that closure
  (`enterTypeParams`, `leaveTypeParams`, `protocolForOf`). The closure
  crosses two host boundaries, `forEachChild` (D7) and the checker's
  requests the declaration reader's scopes make (D8 (a)), each closed by
  an extension of a trust row (§8). [The inventory](method-effects-inventory.md)
  gives each function of the closure its statement and its basis.

**A dispatched call.** A method call on an object of several labels with
plain actuals, as `node.getStart(this.file)` on `node: Node` in `span`, is
lowered as one node that reads the member and invokes it
(`dispatchCallTerm`): its callee is no value, which the bounded check's
selected-call rule requires, so the producer proposes the unbounded
footprint for it (`Type_queries.dispatches_call`) and a body holding one is
certified only at `top`. A node rule composing the head's inspection, which
keeps the heap a prefix, with the call at its selected signature would
certify such bodies; the statements on `Gate`'s members are uncertified
whichever run lowers `Gate`.

**Slices measured** before and after a change of the statements (`make
census FILES=… FUNCTIONS=…`): the five functions whose callbacks call
`gate.expr` (`pattern`, `forOfPattern`, `protocolPattern`, `patternStmt`,
`abrupt`); `patternDefaults`, `steppedPattern` and `inert`, whose slices
verify at their statements; the functions enclosing the array callbacks
of the first group (`fragment-classes.mts#classBody`,
`fragment-statements.mts#neverAssigned`,
`fragment-expressions.mts#moduleFunction`); and the functions of the
inventory. Their outcomes, each with its commit, are
[WORK](../../WORK.md#class-methods-effects)'s.

## 11. Decisions

The owner's decisions are recorded in
[WORK](../../WORK.md#class-methods-effects): D1 (a), D2 the `Within<…>`
spelling, D3 `no-return` first, D4 the node methods' footprints, D5 the
`shift` rewrites, D6 an override refused at the subclass, and (2026-10-24)
D7, `forEachChild` given one signature per callback effect, and D8 (a), the
checker's requests stated as an audited host contract. §12 designs them.

## 12. `expr`'s contract closure

**D7: `forEachChild` at each callback effect.** `forEachChild<T>(visitNode,
visitList?)` is read as the conjunction, over the six closed footprints
$`\varepsilon`$, of its declared signature with both visitors' function types
at $`\varepsilon`$ and the call at $`\varepsilon`$, the mechanism the array
members' overlay uses (`atEachFootprint`), stated in the family description
(`footprints`, with the member's reviewed text and the kind `callbacks`). The
native-contract audit, under T3 and T4 (cited, [COMPILER-API](../COMPILER-API.md#trust)):

- *callbacks:* `visitNode` and, when given, `visitList`, the client's own
  functions, are the only client code the call runs, synchronously, during
  the call; no conversion, iteration protocol or thenable runs (the visitors'
  results are tested for truthiness, which on a value runs nothing);
- *arguments:* each child node, and each child list as a node list, of the
  receiver, in the package's child order; the traversal reads only the
  buffer, so the children passed are fixed whatever a visitor does;
- *aliases:* a visitor may write the client's storage, never a host object
  (stable members are readonly views, T1); a node list's store never changes
  (T4), so no visitor changes what a later visit is passed;
- *result:* the first truthy result, else `undefined`, at the declared
  `T | undefined`;
- *exceptions:* a visitor's throw propagates and nothing else throws but the
  host's request-free reads; the call states no `onThrow`.

So with both visitors within $`\varepsilon`$ the call is within
$`\varepsilon`$ on normal return: its own steps change no location of the
model (T3, T4), and its client code is the visitors'.

**D8 (a): the checker's requests, an audited host contract (T6 extended).**
The requests are the methods of the named views
([COMPILER-API](../COMPILER-API.md#the-sync-api)): `API.updateSnapshot`,
`API.close`, `Snapshot`'s two, `Program`'s six, `Checker`'s 25,
`NodeHandle.resolve`, `Type`'s four and `Signature`'s three (`hostViews` in
`tools/compiler-api.mts`, each with its reviewed text). T6 states that a
request may call its instance's retained `fs` callbacks synchronously and
returns a value of its declared type or throws; with T4, the host's own
state is observed by no transparent operation. So a request changes no
location the program holds but through its instance's callbacks, and the
contract bounds those:

- *The statement.* Each request whose arguments are primitives and host
  objects is read at `{value: any, store: grow}`; the six that may receive
  an object of the program (`API.updateSnapshot`,
  `Snapshot.getDefaultProjectForFile`, `Program.getSourceFile`,
  `Program.getSemanticDiagnostics`, `Program.getSyntacticDiagnostics` and
  `Checker.resolveName`, `serializingRequests`) are read at their declared
  signatures, since serializing their payload runs the object's `toJSON`
  and getters ([COMPILER-API](../COMPILER-API.md#the-sync-api)). The
  statement is read without `onThrow` (a caller catching a request's failure has no bound on
  the heap the failure leaves), stated in the view lists beside each
  member's reviewed text and read where the views are read.
- *The instances it holds of, enforced where they are made.* A verified
  program makes no instance: `new API(…)` is outside the admitted language
  (the gate refuses the constructor's declaration, and no view lists it;
  were it admitted, its `fs` callbacks would be read at the statement and
  checked at the call). TScert's own instances are made by
  `openCompiler` (`tools/compiler-channel.mts`), the one place that
  constructs one, which `tests/observed-stages.mts --reads` keeps the front
  end's only compiler channel; its callers pass `compilerFileSystem`'s five
  callbacks (`tools/files.mts`) and `tools/unchecked.mts`'s, fixed code
  audited below. An instance a verified program receives from outside is an
  input, and that it was opened with callbacks within the statement is an
  external-input assumption, a row of the trust surface.
- *The audit.* `compilerFileSystem`'s callbacks read the file system and
  note each answer in the open recordings' maps (`noteIn`, `set`), mark a
  recording incomplete or the process inconsistent (field and module-cell
  writes), and `kept` writes the module cell `queryFailure`;
  `openCompiler`'s wrappers write its document maps; `unchecked.mts`'s read
  library files. None pops, shifts, splices, truncates, sorts or reverses a
  store it did not allocate: within `{value: any, store: grow}`.

**Fixed and substitutable callees.** The contract-closure rule (§10)
distinguishes two kinds of call. A *substitutable* callee is read off a
value a caller supplies: a member or field of a parameter's, a field's or an
element's type, or a callback parameter; any value of the type may hold any
function there, so its type must state the effect. A *fixed* callee is code
the call always runs: a module function declaration no code reassigns, or a
constant closure the body captures; its effect is its body's, transitively:
an audit of its code, and of every substitutable callee its code calls,
establishes it for an uncertified statement, and its claim does in a
certified run. A closure's identity bounds nothing it captures: an audit
following a supplied closure states its provenance, every call site
supplying it, and recurses through its dependencies.

**`TermScope`'s statements and every value of it.** `TermScope`'s function
members, and the `read` callbacks `named` and `computed` take, state
`{value: any, store: grow}`. Its values are object literals:

- the gate's `termScope` (`fragment-parse.mts`): closures reading the gate's
  maps and arrays, calling `fail` (typed `never`) and `declaredReference`;
- the inner scopes of `type-term.mts` (`{ ...scope, named, … }`): closures
  calling the outer scope's members, which are stated, and `typeTerm`;
- the declaration reader's (`valueScope`, `scopeOf` in `collect`, the
  sweep's `sweepScope`, the mapped templates' and the probes'): closures over
  the reader's own code, the D8 requests, and four supplied callbacks, each
  with its provenance: `collect`'s `context` (its one caller, `collectFrom`,
  passing the reader's closures), `valueScope`'s `captured` (its callers'
  closures building a binder term), `sweepScope`'s `binder` (the sweep's
  closures naming a binder), and `collectDeclarations`' `options.seen`, which
  `clean` calls with each TypeScript error it meets (from `lookup`,
  `declarationOf` and `computedContext.annotation`) and whose every supplier
  is a closure pushing onto a list its caller allocated (`(d) => seen.push(d)`
  in `pipeline/parse-stage.mts` and `fragment-parse.mts`'s command line;
  every other caller passes none), within `{value: any, store: grow}` on
  normal return and on a throw; the audit recurses through them into
  `computed-types.mts`, `type-probe.mts` and `written-applications.mts`;
- the scopes of `array-prototype.mts` and `library-globals.mts`' overlays:
  closures reading the reviewed entries.

By a search of these modules, every store-shrinking operation (`pop`,
`shift`, `splice`, `sort`, `reverse`, `fill`, `copyWithin`, a `length` write)
acts on an array the code allocated (`[...list].sort`, `pending.pop()` of a
local worklist, `work.pop()` of `externalStatements`' local), and the
collections' mutators (`Map.set`, `clear`) are within `{value: any, store:
keep}`. By the [caller contract](../DESIGN.md#trust-surface), a value
meeting a structural type is a plain data object: every field it owns,
stated or not, is a data property, so a spread, a field read or
`Object.entries` of it runs no getter. A data field may hold a function,
and `JSON.stringify` calls the one at `toJSON`, so every `JSON.stringify`
of these modules serializes a JSON value the code built: a string, a span,
an identity key's array of strings and a span (`identityKey`), a property
key's text (`propertyKeyText`, which reads the key's stated fields), or
`type-probe.mts`' arrays of positions; `sameIndex` compares two type terms
field by field, without serializing (`sameData`). So every value of
`TermScope` meets the statement.

**Catches.** A `never`-typed call contributes no normal-return obligation
only where its exception escapes. The closure's catches (`parseModules`,
the declaration reader's refusal handlers turning a failure into a refusal,
`aliasOf`, which returns `null` where `lookup` throws, so after `clean` and
its `seen` callback, and `kept`'s rethrow) resume after code whose every operation, failing
or not, is within `{value: any, store: grow}`, by the search above: a throw
leaves the heap within the statement of the entry heap, so resuming keeps it.

**The statements, a reviewable inventory.** Every function `expr` reaches
through `Gate`'s fields and members and by direct call states
`{value: any, store: grow}` unless a smaller footprint holds; the inventory,
generated by the scan of §10 and listed in
[the inventory](method-effects-inventory.md), gives each callee its basis: a stated contract (a `Gate` member
or field, a `TermScope` member, the claim-site record `{ entry(): number;
span(): Span }` of `sites`, `closeStatements` and `Gate.hoist`,
`enterTypeParams`' `rename`), a certified claim (its slice verifies), an
audited fixed implementation, or a host contract (the node methods (D4),
`forEachChild` (D7), the host guards, the reviewed overlays of natives and
library globals). With D5's rewrite (§5) the closure holds no store-shrinking
operation on a store it did not allocate. A generic definition in the
closure states nothing (§3).

**Certifying the bodies.** Each stated function is certified where a slice
holding it verifies (L2); a caller verifying relative to a statement does
not certify it (§10), and the measurement reports which statements are
certified. A body holding a statement's method call dispatched on an object
of several labels needs the node rule of §10. Its premises: the head is an
inspection term (the member's read and binding, typed by union elimination
of the object's slot), the receiver and the actuals are values already, and
every dispatch alternative's callable contract states an effect within the
bound; its run is the head's inspection, which keeps the heap a prefix and
carries typing through heap and world extension, then the call at the
covering effect, the footprint relative to the node's entry heap, on normal
return only (no exceptional bound follows from the inspection). It lands if
a measured slice refuses at such a node. The producer's typing of a `map`
callback's node parameter as `Node residual | SourceFile` where a
`SourceFile` binding is in scope is repaired if it blocks a measured slice.

**Cases.** D7: visitors in both positions; an omitted list visitor; the two
visitors at different effects (the call at their join); a destructive
visitor in a `map` callback (refused, run under Node); a forged claim of a
`forEachChild` call within the empty footprint with a popping visitor
(refused in search and in checking). D8: a retained `fs` callback popping a
captured array, run under Node (a later request shrinks the array), refused
at its construction.

**Measured** before and after: the slices of `pattern`, `forOfPattern`,
`protocolPattern`, `patternStmt`, `abrupt`, `neverAssigned`, `expr` and
`moduleFunction`, and every slice verified on main that holds a function
this step states, so a statement a body does not meet shows as a lost
slice.
