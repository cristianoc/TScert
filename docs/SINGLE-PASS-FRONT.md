# The single pass's walk rules

The rules by which the [single pass](SINGLE-PASS.md)'s front computes what
it proposes: the store and signatures it lowers, each expression's and
statement entry's type, each function's footprint, and how imports, cells,
classes and narrowing read. The walk is `Synthesis.retypeUnit` over a
unit's flow graphs; its declarations' footprints are the pass's own steps'
(`PassProposals.proposals`).
Every result is a proposal: the pass checks each at its node
([steps and obligations](SINGLE-PASS.md#5-steps-and-obligations)), so no
rule here is trusted, and a rule that proposes too little costs coverage
only. A force named beside a rule (`TSCERT_FORCE=…`) states the rule's
proposal falsely, and the [controls](SINGLE-PASS-CONTROLS.md#forced-proposals)
require its unit refused. The proposals at loop heads are
[loop heads' proposals](SINGLE-PASS.md#loop-heads-proposals).

## Store and signatures

The store is the fragment's declarations and
annotations, lowered with a type table of the primitives alone
(`fragmentClaims`). Each function's parameters and result are its
annotations' types; its footprint is the one its declaration writes
(`Modifies<…>`, with its `@requires` and `@ensures`), else the ordinary
effect. Another function, and an import, is read at that signature; an
import at its declared type, at the footprint its module establishes
where one does ("Imports" below). A function literal whose body the walk sees
change nothing states the footprint keeping values and stores.

## Types

Every expression's and statement entry's type and every
`let`'s storage contract is the walk's (`Synthesis.retypeUnit`), at each
execution point of the unit's flow graphs (`SourceFlow.pointId`), each
point holding its node's sites' expressions and its statement's bindings.
A module constant is read at its initializer's type in the
initialization's walk with its annotation, a module cell at that walk's
storage contract (`Front.withInitTypes`). A call of a generic module value,
a generic class's construction and a `for...of`'s iteration intrinsic are
instantiated at the binders' types the walk gives them
(`instancesFromWalk`); a loop's element is its intrinsic's one binder,
else (a union's iteration) the `value` its stepper yields. An async
literal with an expression body is at the promise its `%AsyncReturn%`
call gives. A binder a resolution qualifies (`%Await%`,
`%AsyncReturn%`, `%PromiseResolve%`, an `Awaited<T>`-resolved one) is
instantiated at its input's type with the certificate that type's form
gives (`Scheme.resolutionCertificate`: a binder of the unit's own scheme
or its observation that binder's, a native promise its payload's where
the binder is resolvable, else observed whatever its payload, a union each
label's, any other label stable), its observation and result the ones the
checked certificate establishes (`Scheme.resolutionInstance`); written
type arguments name its binders but the observations and results. A
binder's type is read off an actual by matching its parameter's type one
level at a time (`Synthesis.matchBinder`), at what the receiver gives
it, else at the join of what the actuals give it; a bound `U extends T` propagates U's lower candidates
to T until the finite sets settle. A binder the signature reads only at its callbacks'
parameters at the candidate within every other,
a primitive's members read off its prototype: the binder itself; in a
union, the one member naming it at the actual less what the other members
admit and less the labels another binder of the call reads off one of
them (a union iteration's parts, each kind's binders apart), else each
label of the actual, a single one included, at the first member it
matches, the bare binder last (`TResult1 | PromiseLike<TResult1>` at
`string` is `string`, else the
bare binder); one type
constructor's arguments at the actual's of the same constructor; an
array's elements (a tuple's positions separately), a record's fields and
methods' results, a constructor's first signature's result and parameters,
a callable's result at the actual's, then its parameters
where the result supplies no candidate, of a callable stating several
signatures (a guard's plain row beside its promise row) the first naming
the binder (a written guard's promised type). A binder no actual gives is at what
the type expected of the call's value gives it, whether or not that
instance admits the actuals (the call's step decides), else at a
scheme's declared default read at the binders so far (`then`'s `TResult2
= never`), a proposal the
call's instance check decides, else at its bound
read at the binders so far, else at `unknown`. Fresh array literals at generic
tuple positions keep those positions recursively, each value widened.
An actual that is a call, at a parameter placing the call's unbounded
binders at tuple positions (through at most four arrays; of a
construction's signatures, the first placing them so), is walked at that
parameter with those binders as holes: a type naming a hole guides an
array literal (a tuple of the positions it states, a position holding a
hole at its element's own type) and a call, whose instance is read off its
actuals and whose callback is walked at its parameter read at the binders
the call's result gives there, where that names holes in its result alone
(`new
Map(xs.map((x) => [x.k, x]))` is a `Map` of the pairs' types).
A source function's unbounded binder inferred directly from its actuals
widens primitive literal candidates when its result does not return that
binder bare, within the other actuals' and expected result's constraints. Written bounds, explicit seeds and callback-only
candidates retain their types. The instance precedes result allocation;
each existing argument keeps its store contract.
An ordinary generic constructor supplies its construct signatures at fresh
binders; its actuals supply their instance as for a function call.
A packed generic class's construction reads written callback parameters
before choosing its tuple instance; the tuple parameter's actual supplies
that instance, whose argument lists the existing lowering derives.
A generic method's binder its annotations read as packed (a class
binder at its declaration's packed parameter) is packed in the method's
scheme, its argument lists its own row. A callee of one signature whose rest is a packed
binder's argument lists takes one last spread of a value of that binder
at its own type; the lowering's
`callPacked` checks the operand.
A finite record gives a dictionary parameter no index candidate; an
otherwise unconstrained, unbounded binder there defaults to `unknown`.
Its named fields do not constrain other
own values. Explicit method type arguments seed the instance. An expected union's
unique application of the result's declaration supplies its contextual
type arguments. Of a call's signatures the first each walked actual is
within at the binders so read, satisfying their bounds, is selected, else
the first the actuals' count admits; a call may omit each trailing parameter whose
contract admits `undefined` (`T | undefined` included), a variadic
signature's fixed ones too, passing no rest.
Of one signature, a fresh literal at a parameter that is a bounded binder
is made at the bound where the bound names a dictionary (an object
literal) or a tuple (an array literal), and the binder read off it; a fresh array literal at
a parameter whose binders are bounded by literal types is made at the
parameter read at those bounds, where that leaves it no binder (`pick<K extends 0 | 1>(e: Array<[K,
number]>)` at `[[0, 1]]`). Of several signatures, an object or array
literal at a parameter they state differently is made at the first one's
parameter it fits. A rest that is a binder's
argument lists (`...args: T`) binds it at the actuals past the fixed ones,
widened: an argument pack where only the rest uses the binder, else the
tuple of them, whose argument lists the rest's are; an occurrence solely
as a constructor or callback's argument pack supplies no value type. A spread actual of a tuple of required positions
stands for those positions; a spread of any other array for one actual of
its elements, which only a variadic signature taking no more fixed
parameters than the actuals before it admits; into an ordinary call of no
variadic signature, no actual after the first spread runs code. Constructors
admit later actuals that run code, with tuple spreads saved by their
execution plan. A slice rest of an array pattern is the call of its
`%RestFrom:k%` at the value, its binder the union of the value's elements
from position `k` on, an optional one's with `undefined`, any other rest the
tuple of the positions after it. An object pattern's rest is a fresh
object of the value's one record's fields but the named keys, at their
types; of any other value, the copies it gives as a spread's operand but
the named keys. An assignment pattern's rest is a pattern's. A nested pattern's value is stated at its span (a parameter's
pattern is a destructuring of the parameter), and a defaulted part that
is a name is read at the field's type at its span. A declaration of a statement declaring several holds the
bindings before it.

## Function literals

A body has no type; an expression body the parser
writes as statements (a guard's Boolean return, `booleanReturn`) shares
its expression's span, which keeps the expression's type. A function literal
passed as an actual takes its unwritten parameters' types from its
parameter's signature taking the most parameters; any other literal is at
its written parameters and receiver (a method's `this`). Its body reads each binding
it captures that a slot holds (`cellLocals`: the unit's or an enclosing
literal's) at its type where the literal is made, one a cell holds at its
declared type; `TSCERT_FORCE=captures` reads a
cell's at its type there too, the adversarial proposal. A literal of no
rest that is not a guard is stated at its own parameters' row and, beside
it, at each signature the expected callable states binding more
parameters whose leading ones are within its own (variadic: at least as
many), each at its own result and effect, each offered row at the offered signature's
result where the body's is within it (`{s with call_effect}`), a use's
offer at the literal's own leading parameters (`discarded_signature`);
where the expected signature's leading
parameters differ from its own in representation, at that signature alone. A constant holding
a literal of no type parameters and no rest, unannotated or annotated at
one signature, read where one fixed signature binding more parameters
whose leading ones are within the literal's is expected (an argument, an
annotated binding, a return), offers the literal that signature
(`closure_offer`). A module constant, unannotated, holding a literal of
no type parameters, rest, defaults or guard whose result is written, is
also at its signature extended by a rest of `unknown`, its code
discarding the further actuals, as a module function's slot is. Where a unit's walk finds such an offer, the unit is
walked once more with each offered row stated at its literal, the walk's
one retry, at most one walk beyond the first.
`TSCERT_FORCE=offers` offers every longer signature whatever its leading
parameters, the adversarial proposal. A defaulted parameter is offered
with `undefined`, bound in the body at its type less `undefined` joined
with its default's (a parameter of `unknown` at `unknown`), its default
made at that type at the literal's entry, before the body, its effect the literal's
(`TSCERT_FORCE=defaults` leaves it out, the adversarial proposal). A
literal with an array rest is stated at its rest arrow, the pack of the
rest's element, at its written effect else the ordinary one
(`ClosureSetup`'s own signature of an array rest); a rest of a tuple of
required positions is one fixed parameter per position. Its effect is the one
it writes (`Modifies<…>`); else the footprint keeping values and stores
where the walk sees no write, assignment or call changing the heap, else
the closed footprint of the classes of contents its writes and calls
change (an assignment of a binding it does not declare or a field write
the values, `x ??= v` of such a binding whose `v` changes nothing its
initialization, `init`; an element write the values and a store's growth;
a `for...of` what each step of its stepper's first signature does, the
values and its store's change where the step changes its receiver's own
locations (a native iterator's position), else the step's footprint
(`TSCERT_FORCE=steps` leaves the steps out, the adversarial proposal); an array's
`length`, and a call changing a receiver's store or elements, both,
but a call changing the store of a constant holding a store the run
allocated (one initialized by a call whose instance states a fresh
result, or by such a constant); a call changing its receiver's own
locations the values and its store's change; any other call its
instance's footprint); it bounds a throw (`onThrow`) where none of its
calls states a throw left unbounded; and an expression body that is a
call whose instance states a fresh result states one. `TSCERT_FORCE=fresh` takes every named receiver as
such a constant, the adversarial proposal. A
generic function literal (one writing type parameters, a class's generic
method included) is claimed at the scheme its annotations state, before
its unit's walk: its binders its own, each bound its written one; its
receiver its written `this`, an arrow's every value; its parameters and
result as written, a defaulted parameter with `undefined`, an array rest
its element; its effect its written one, else, for an expression body
that with its defaults calls nothing (`Synthesis.mayCall`), keeping values
and stores and bounding its throws, else the ordinary effect. Its scheme row and binder
rows are `Scheme.closureRows`', so its annotations, and its body's walk,
read each binder as a rigid row; the walk states it at that scheme where
its body's effect is within the scheme's, and states a call of a local
holding a scheme with its callee at the call's instance (`closureRows`'
instances): a binder's row that is a meet (a bounded binder, `T extends
U` reading `T ⊓ U`) at the one clause row holding the meet of its
binders' types' clauses with the row's own (`SchemeInstances.meetOk`), and
elsewhere a meet naming several binders at the type every other's labels
include; a scheme's rest is stated at the argument pack of its positions
read at the binders, a binder's meet row there at the binder's type
itself, the labels a spread's store must hold (`SpreadsInto`). An unwritten result whose parameters contain no nested scheme is
proposed by a preliminary body walk
, then checked at the scheme’s rigid
rows with the body. A result that this walk cannot determine supplies no
scheme. Any generic literal a walk meets before the scheme rows are made (a
declaration's footprint, the initialization's walk), is walked at its own
parameters as any other literal. A
callback is stated at that effect on every row it offers, never at its
parameter's (without `onThrow` where the parameter states none). Of a call's several
signatures, each callback is walked first at the first one's parameter
under the binders its receiver and other actuals give, and the signature
chosen is the first whose parameters admit the walked actuals and whose
callback parameter each callback's type is within (the checker's
subtyping of arrows, which bounds the callback's effect by the
parameter's), in the store after those walks, with every binder it
mentions bound; where none admits a
callback, the first stating each callback's promise, else the first
admitting the other actuals, the callback at its own effect, which the
pass then refuses. A binder the chosen signature does not mention is at
the empty type. `TSCERT_FORCE=callbacks` chooses the first signature and
states each callback at its parameter's effect, the adversarial
proposal. A callback whose parameter is a binder another actual's
parameter takes at a position of one of its methods is walked at the
callable the actual's method of that key takes there: of its signatures
of that arity taking a callable there, the last whose effect covers the
parameter's method's, else the first (a string's `replace` dispatching to
a native regex's `[Symbol.replace]`); the
binder is then read off the walked callback. The binders a
callback's result would give are first read off the type expected of the
call's value, where that instance admits the actuals. An empty array
literal in a callback's body is made at no expected array naming a binder
of the call that no actual has given a type yet: it keeps its own type,
an array of no element, and the binder is read
off the callback's other returns. A written type
guard or assertion is stated with its promise, its result the guarded
type, and also at its own parameters. A constant holding a function
literal that reads it is walked with the constant at its written type,
else at its written signature keeping values and stores and bounding its
throws, raised to the type the walk gives the literal until the two
agree, at most four rounds. Its self reads offer the literal longer signatures as any read
of a constant holding a literal does; where the walk
states offered rows at the literal, the constant is read at the type the
walk gives the literal, those rows included, written or not. Its own check decides it ([a footprint](SINGLE-PASS.md#a-footprint)).
A field of an object literal at a key the expected record states as a
method is walked at the callable a read of that method bound to the
record is, its signatures the method's: a literal there is stated at each of them
binding more parameters, an iterator's `next` at `(value) => …` beside
its own row. A generic function literal at a key the expected record
states as a scheme is allocated at that scheme, the store's contract the
annotation's; the allocation's typing checks the
literal's own scheme within it.
A constant holding such a literal, read where one variadic signature of
an element rest binding at least as many fixed parameters is expected,
offers the literal that signature at its own leading parameters
(`closure_offer`). A literal walked with no
expected type (a field of an argument's object literal) is stated,
beside its own row, at the rows the parameter's callable offers it once
the call's instance is chosen (`fit`, `contextRows`).
A constant holding a class value whose constructor's body returns an
allocation last, read where a constructor type is expected (a
dictionary's field at its index's value, less the `undefined` of an
absent read), is offered: each method of its
prototype chain a constant of a literal holds, the signature the
expected instance's member states binding more parameters, at the
class's instance as receiver; and the class value, the construct
signature giving that instance, at that signature's parameters where it
binds more than the constructor, else at the constructor's; a variadic
construct signature of an element rest as it is. A class value is held at its
own construct signatures, the offered ones among them, as a callable is;
the constructor's code is checked at each (`ClosureSetup`).
A member stating its signatures at several receivers (an array's methods
at a dense and at a sparse array) is called at those whose receiver
admits the walked receiver, each callback walked first at the first of
them, and its type at the call states those rows.
A call whose instance's result is the empty type, under no handler and
in no async body, changes nothing on a normal return, for a literal's
effect and for a declaration's footprint; its throw is its signature's. Under a handler or
in an async body its throw is caught and the heap it leaves is a normal
return's: the call changes what its instance's footprint states.
`TSCERT_FORCE=no-return` reads it as changing nothing there too, the
adversarial proposal.
A synchronous throw operand outside a handler or finalizer contributes
only its exceptional effect, since it has no normal exit. A finalizer’s body and handler retain those effects:
the finalizer may replace a throw with a normal return.

## Declarations

Each function a wanted unit reaches, callees first, is proposed what its
own checked steps establish (`PassProposals.proposals`,
[proposals by the pass](drafts/proposals-by-the-pass.md)). Its member is
planned with every function proposed before it at its proposal and every
other at its written effect, else at the ordinary effect, and run by the
single pass with its footprint open, its loop heads' facts settled as its
check settles them (`inferredSettle`). Each visited step $`n`$ has a local
effect $`\ell_r(n)`$ on each of the two routes $`r`$ the pass checks a
footprint by. On the direct route it is the least closed footprint
`SinglePass.footprintCheck` accepts at the step. On the regional route it is
the least of the step's alternatives (the closed check, a call's frame, an
element write's frame: `ArgumentRegionGraph.checkClosedNode`, `callStep`,
`writeStep`), each frame rebased to the entry through the regional facts
(`Footprints.rebaseAll`) and read in the closed language. A route's
footprint is the join of its steps' local effects, and the proposal is the
regional route's where that is strictly below the direct route's:

```math
\frac{\ell_r(n)=\min\{\Phi \mid \mathsf{check}_r(n,\Phi)\}\qquad
      \Phi_r=\bigsqcup_{n\in\mathrm{visited}(f)}\ell_r(n)\qquad r\in\{\mathsf{direct},\mathsf{regional}\}}
     {\mathrm{propose}(f)=\begin{cases}\Phi_{\mathsf{regional}} & \Phi_{\mathsf{regional}}\sqsubset\Phi_{\mathsf{direct}}\\
       \Phi_{\mathsf{direct}} & \text{otherwise}\end{cases}}\ \textsf{steps-footprint}
```

The regional route is run where the direct route's footprint is more than
keep/keep, the least footprint. The proposal bounds the throws where the
join of the steps' effects with their throws checked is within the
footprint and the footprint is less than the ordinary effect. A step in the
region from which no normal return is possible (`GraphCode.deadIterate`)
contributes its throw alone. A function is proposed nothing where its
footprint is the ordinary effect or one of its runs stops. The same rule
covers a generic function and one with a rest parameter.

A self-recursive function's own reads start at keep/keep bounding its
throws and are joined with what its steps establish until they establish no
more, $`I_0=\bot,\ I_{n+1}=I_n\sqcup T_f(I_n)`$, at most one run per step of
the lattice's height. A member of a cycle of two or more functions reads
the members not yet proposed at their written effect, else at the ordinary
effect. A function whose
result annotation can state a returned function's footprint
(`resultWithFootprint`: one function type of fixed signatures stating no
effect, throw bound or promise) is proposed, beside its footprint, the join
of the footprints of the signatures of the checked type of the value each
of its returns returns, as the footprint of the function it returns; its
callers read it, its returns establish it
(`resultWithFootprint`); `TSCERT_FORCE=results` proposes it keeping values
and stores, the adversarial proposal (the controls
`returned-closure-footprint` `countLetters`, accepted unforced, and
`invalid-returned-closure-footprint` `lastRead`). Where the initialization
calls a function so proposed, the proposals are computed once more, the
initialization's walk typing the module values at the first proposals. A guard or an
assertion function is proposed like any other, its promise kept. A function
with a written effect keeps its footprint and throw bound, its steps
proposing its returned function's footprint; an async function keeps the
ordinary effect, by the language. The front states each proposal at the function's claim and
slot (`Front.withStandIns`): its callers read it and its own unit
establishes it.

## Imports that never return

An import of one fixed signature whose
declared result is the empty type, stating no promise, is read at the
footprint keeping values and stores (`Front.withNeverImports`): it has no
normal return, so its normal return meets every footprint; its throws
stay unbounded. The reading rests on the declared result, as every read
of the import does. An intrinsic (`%…%`) keeps its reviewed contract.
Pretext's `x ?? missing()` is the case: with it the functions calling
`missing` are proposed their own footprints.

## Imports

An import is read at the footprint its module establishes
where the fragment alone resolves it to a function of a module the fragment
lists (`Claims/Imports.lean`, `resolveRead`;
[certified imports](SOURCE-CONTRACTS.md#certified-imports)): its
declaration identity names that module, the function is the module's of the
declaration's name whose name lies within the declaration's span (a default
import's declaration names the function, a re-export's the module declaring
it; a function the parser leaves out, `absent`, is none), its binding is
stable (no code of its module writes it), and no other import binds its
local name; the entry's rows and the importer's reading of the import
correspond by the store-map checks (`FilePlans.refuseRows`). Only the reads the code the selected units reach mentions
are resolved, a module's top-level code counted where its functions read a
name it binds (`reachMentions`); a module's own imports are resolved the
same way, recursively. The modules are planned callees first, each from
its own fragment (`fragmentPlansWithModules`): its imports at what the
modules planned before establish, a module on a cycle with its reads of
the modules not yet planned at the ordinary effect; each function read
proposed the footprint its steps establish (`PassProposals.proposals`) or
the one it writes. Of the importer's functions reached, an async one, read
at the ordinary effect by the language, adds no names: its body is neither
run nor checked for the selected units. Before the modules are planned,
the reads are resolved from the importer down, a round at a time, each
module's front built once and kept for its plans (`Front.withQualified`):
a function read whose walk with every import at the least footprint
(keeping values and stores, bounding its throws) proposes the ordinary
effect is at the ordinary effect, and its module is planned for it no
further, nor are the modules only its code reads (first its own walk with
every module value at that footprint, then the walks of what it reaches, each function
returned at the least footprint too); nothing is so decided in a module
whose initialization calls a function returning one, whose values hold
the returned functions at the ordinary effect there. That its walk
at any established footprints proposes the ordinary effect too rests on
the walk's grades being monotone in its callees' footprints, conjectured;
where it fails, the read is at the ordinary effect, which needs no check.
The groups of the functions proposed more than the ordinary effect, and
every group they reach, are checked by the pass (in the interface stage,
[module interfaces](STAGE-STORE.md#single-pass-module-interfaces), or in
the importer's invocation), each verdict on its own line as the unit
`module:<location>#<unit>`, its loop heads' facts inferred (input slots,
implications, regional tables, `computedGiven`) and its region separations
proposed (`withFreshApart`) as for the file's own units. A read is at its proposal where
the function's group and every group it depends on, of its module and of
the modules it reads, was accepted there; the importer's units that
mention the read list that group in `depends`. Every other import, one
of no module fragment (a declaration file, a package), one the fragment
does not resolve, one of a module whose plans fail, and one whose
proposal is the ordinary effect or is not established, is at its declared
type with the ordinary effect (but the reading of an import that never
returns). The declared type is what the importer reads in every case;
only the effect rests on the module's check. `TSCERT_FORCE=imports` proposes
every function read keeping values and stores and bounding its throws,
the adversarial proposal: the controls `certified-value-import`
`tallies` (accepted unforced) and `invalid-certified-write-value-import`
`zeros` are refused under it, each at its module's refusal of `tally`
and `drop`, which change the heap.

## Cells

A binding the unit assigns and holds in no slot (a module
binding, one a closure shares, every `let` of a module's initialization)
is narrowed by its own assignment and by tests, as a slot is, until a
statement changes a value location other than by assigning that binding:
from the next statement on it is at its declared type, whether or not the
walk has met an assignment of it. What a cell currently holds is a current-content fact,
which no step keeps across a write without a separation
([no general frame rule](PROGRAM-TYPING.md#no-general-frame-rule)).
A handler's entry
and a finalizer's entry on a throw's route state each cell at its
declared type, and so does a return's route through a finalizer where
evaluating the returned value changes a value location: a throw keeps no
current-content fact (`ControlFlow.handlerFacts`). `TSCERT_FORCE=cells` keeps the narrowing,
the controls
`module-cache-keeps-lengths` `count` and
`module-cache-before-initialization` `rhs` (its initialization's `let`
across the call of a function that writes it), `fresh-separation`
`handlerCell` (a shared `let` at a handler's entry) and
`module-cells-written-in-turn` `aside` (two module cells at a finalizer's
entry, on the throw's route and the return's).

## Early bindings

Each early binding of a statement list (the flow
graph's `.early` node) is bound from the list's entry on at its written
contract: its annotation, else its function literal's written receiver,
parameters (a defaulted one admitting `undefined`) and result at its
written effect, else the ordinary one; that is its storage contract. It
stays at that contract after its declaration, which writes its cell, every
later read checking the cell's contents against it; `TSCERT_FORCE=early` holds it at
its initializer's type, the control `early-bindings` `count`. A
`return`'s value holds the statement's bindings at its own position,
where a finalizer holds the return.

## Finalizers

The flow graph copies a `finally` block per route that
leaves the `try` (`SourceFlow.sequence`). The copies of the normal
completion, the throw and each `break` or `continue` share one entry per
statement: the join of the statement's normal completion, the bindings a
throw of its body or handler leaves (each binding they assign at its
declared type) and each such jump's. A return's copy is walked from the
return's bindings, its statements' entries read by that copy's points
(a point whose scope holds `%return@p%`). A loop's close (the
iterator's `return` that a `for...of` over a program's iterable calls
when a `return` leaves it) is such a finalizer: each return's copy is
walked from the return's bindings, and the return's held value holds that
copy's completion. After the finalizer, its
bindings hold at the statement's start (the rethrow), at each return's
held value (that return's copy's), and for each jump; where a copy never
completes, these are at the empty type.

## Regions

A function whose statement states store regions is
proposed at `top`; the regional check of its own regions certifies the
statement.

## Classes

A class value is the construct signature of its
constructor's written parameters and instance (its written result), with
its static fields, each at the class binding's annotation's type where it
states one. A fresh constructor (a class binding `C.[[class]]`) has first
the signature giving the instance its body allocates, its tail
allocations stating their own keys exactly; a class value whose code is
a constructor an earlier class value of its declaration was walked at
has that one's signatures. An allocation holding a prototype link states
its own keys exactly, the link at its walked type and each other key at
the expected record's field. A copy (`{ ...o }`) whose sources each state
their own keys exactly, with no optional field, states its own keys
exactly. Where a type is expected, each copy an object literal with spreads gives
is made at the first member of it whose field at each named key the part
is within, its named fields at that member's, where the copy is within
the member (`TSCERT_FORCE=objects` states the expected type itself).
A copy (`{ ...o }`, `Object.assign`) is the union of the
copies its parts give: a named field set in each, a spread merged into
each once per label of its operand (a record's fields but its prototype
link and a key it also states as a method, a key two operands of an
intersection state at the field within the other's; a class value's
static fields; nothing from a primitive; no stated key from a string or a
function of no fields; a function's fields, open; a dictionary's string
fields, its string index the type of every other own string key and its
symbol index every symbol key's, two indexes of one key class, an
intersection's, not handled), a key the source surely has at its type,
one it may have at the union of both, or at a side's index, one either
may hold at an unknown type dropped; where a side states an index and
each says what it gives under every key of its class, the copy states
the index at the union of both sides' and that class's fields', and
each such field at it.
The initialization's generic closures, a generic class's methods among
them (each quantifying the class's binders, `C."m"#classI`), are claimed
at the schemes their annotations state, as scheme rows, before its walk
types the values holding them. A read off a generic class's name (a
static field) reads the class at an instance, each binder at its bound
(`unknown` where it states none), recorded as the read's type arguments;
a bound reading another binder is not handled there.
A fresh call bound to an unannotated constant and followed by an alias
or a mutating member use selects a matching overload whose result has no
required array positions, where one exists. The call creates that store contract;
later uses retain it. Other uses retain their existing result proposal.
A member `o.m` of a union of objects each stating it at the same signatures
(a host family's node kinds, each its own receiver) is that member with
every member's receivers and schemes; each stating it at one signature of
no promise, binders or rest, all taking the same parameters at the same
effect, it is that signature returning the union of their results. Any other member of a union is read arm by arm,
each arm's member at that arm's receiver (its own or its prototype's) or
its field, the union of them: a union of callables.
A call of a union of callables, each arm of one fixed signature and no
binders, is each arm's call: every arm's count admits the actuals, each
actual is made at the parameter every arm states at its position, else at
its own type, and the value is the union
of the arms' results; for a declaration's footprint it is a call of no one
instance, changing anything and leaving a throw unbounded. `TSCERT_FORCE=arms` states the first arm's signature alone,
the adversarial proposal. A bounded binder's value is called at its bound.
An array arm's `length` is a number beside the other arms' reads.
A keyed read `o[k]` is an array's or a string's element, an object's
field at each name the key may spell (its string literals, its numbers
that are array indices: an enum's reverse map, a record at a
literal-union key), else its index (a dictionary's, with `undefined`).
A member of a receiver typed by a bounded binder is read through the
bound (`Plans.boundOf`). A function's `toString` is `Function.prototype`'s. A member read the
read rule refuses at the walked receiver's type (a member no contract of
it states, a key no index constrains, a primitive's prototype stating
none: `readCell`) is the unit's refusal at that read, a call of one
callable none of whose signatures admits the actuals' count (the
lowering's `selectSignature`; a construction of a class of no binders, a
value of no call signature such as `Function`, and a variadic signature
whose argument lists are the empty type admitting none) the unit's
refusal at that call, and so is a call of a union of callables an arm of
which does not admit the count, a call of a union an arm of which states
no call signature (the lowering's split names an arrow at every arm), a
spread of an intersection of two operands with index signatures the
unit's refusal at that spread, and
an expression a part of which is; any other type the walk does not
determine is a construct the pass does not handle.
Each expression's type is read at its own statement's point,
where two statements' expressions share a span (a construction's parts).

## Function forms

`Object.assign(f, { … })` at its two annotations is
the callable object of the record annotation's fields at the function
annotation's signatures (its variadic ones where `f` has a rest
parameter), `f` walked at the function annotation and the literal at the
record's. `f.bind(o, a…)` of a target other than a member of `o` is, of
the target's fixed signatures (else its one variadic one), the first
stating no promise, keeping what binding keeps (`Effect.keeps`) and
taking the prefix within its first parameters: at any receiver, the
parameters left, its result and its effect past the prefix
(`Effect.drop`), with each further signature of the same parameters
promising about a parameter past the prefix. `o.m.bind(o)` (a
`for...of` over a program's iterable binds its iterator's `next` so) is
the member at any receiver at the effect binding keeps, of several
signatures its first of no promise binding keeps (`next(...[value]: [] |
[TNext])` at its zero-argument row) with each further one of its
parameters promising; of a union of hosts whose
members differ (`%iterator.next.bind(%iterator)` over a union of
iterables), the member read arm by arm, and bound, of each arm's member
its first signature of no promise binding keeps, where all take the same
parameters at the same effect, at any receiver taking them at the effect
binding keeps, returning the union of their results (the lowering splits the host's slot, `unionVar`, and binds
each arm's member, `bindMember`); `TSCERT_FORCE=binds`
states it keeping values and stores, the adversarial proposal.
`f.apply(o, list)` and
`Reflect.apply(f, o, list)` are the target's one signature's result, the
call at its effect, for a list that is null, undefined or a tuple of
required positions, or, for a target taking only a rest, an array of any
length. A method at a computed key of one string literal is that member; at an
index key of an array, the array's element there, called at the array.

## Collected values

A spread of a program's iterable and an array
pattern over one collect the values its protocol's steps yield
(`collect`, `protocolPattern`, tools/fragment-statements.mts): the
collected array (`%items`, `%rest`, an unannotated `[]` the steps push
onto) is made at the array of the values a step not done yields, an
element binding (`let %vI = undefined`) at `undefined` or those values;
the step's type is the protocol's bound `next` of the statement's other
bindings, or of the next statement, walked ahead.
A `for...of`'s iteration intrinsic of no binders (a string's,
`%Iterate:string%`) is called at the iterable as a generic one is, its
stepper held at the loop's head and its `value` the element.

## Expected types

A store's contract is fixed where the store is made;
a read is a copy, an upcast of an immutable value, or an upcast of a store
to a readonly view of it. An annotated declaration holds an object it is
initialized with at the members of its declared type the object is
within (a primitive, nullish or callable value as an assignment narrows
it; an early binding at its written contract), never at the exact type of
the store it was made from; an object literal assigned to a binding a
slot holds likewise. So a value is made at the type its position
expects: a return's, an annotated declaration's, an assignment's (also
`??=`, `||=`, `&&=`), a field write's field, an element write's contents,
a cast's target, a function literal's result; and from there a
conditional's arms, the right operand of `&&`, `||`, `??` and `,`, an
object literal's fields (the union of the fields the expected members
state at the key) and an array literal's positions. By form: an object
literal states its own keys exactly (`HasTyUsing.alloc`'s bound), where
nothing is expected each field a literal's widened type, a name's, a
read's or a const assertion's (`true as const`) as it is; at a
dictionary with a writable index it is allocated at that dictionary with
each of its keys a field (at the dictionary's named field, else its
index), the optional fields it leaves out absent; at a record, it is that
record's form with each key a field the allocation writes (a stable key
the record states as a view stays a view), at the expected field, else at
the value's own type, as written where that is within the expected
record, else stating its own keys exactly. An array literal is made at the
one array member whose positions admit its elements, each element made at
its position; at an iterable other than an array, at the readonly array
of what it yields (its `[Symbol.iterator]`'s `next` results' `value`),
presence `readable`; where nothing is expected, at an array of its
elements' widened union, presence `readable`. `[…] as const` and `{…} as
const` make the operand at the const type. A function literal writing no
parameter's type is walked at the expected signature taking the most
parameters. A call's binders are read off the receiver and the actuals
first, those still unbound off the expected type; where the instance so
read has a result the expected type does not admit, the expected type's
instance where it binds every binder and admits the actuals. A call whose
signature states a fresh result is made at the first expected array whose
elements admit the result's.
An uncontextualized object literal nested directly in a fresh field is
made at its own open record, unless its own keys are required exact or
it carries a prototype.
A spread nested inside a fresh call actual receives the expected record
fields recursively; each spread operand that is a literal receives the
optional fields of that context, and each resulting copy is checked
within an expected arm.

## Narrowing

A tag test narrows a binding or path by the tag slice;
`unknown` (a `source` label) becomes the kinds of value the test does not
contradict where it contradicts some (`BranchRefinement.sourceSlice`); a
type parameter's value (its meet with its bound), where a test naming one
primitive family holds, becomes that family, as `unknown` does, and stays
where it fails; under any other test, a meet row becomes the meets of its
parts with each clause of it the test does not contradict, none where it
contradicts every one (`T ⊓ (number | null)` less `null` and `undefined`
is `T ⊓ number`, the lowering's `observedSlice`). Where a constant holding
a condition's value (a guard's call, a test, a conjunction of them,
`implicationForm`) is tested `true`, each constant and each parameter no
cell holds is at what the condition narrows where it holds
(`constantImplications`). A test that cannot give an answer (its value's slice for
it is empty, `!e` where `e` cannot give the other, `a || b` not `false`
where either operand is never falsy, not `true` where neither is ever
truthy, `a && b` dually) leaves the arm of that answer unreached, walked
for its entries; a loop whose test cannot answer `false` is left by its
breaks alone; a statement whose value has no type (a call of a function
returning `never`) does not complete, what follows it walked for its
entries, unreached, each binding at the empty type; an unreached expression whose type the walk does not determine is at
the empty type. `typeof x` is a `string`. A
call of a type guard, on its true arm, and a statement calling an
assertion function, after it, narrow the binding the promise names to
its members within the guarded type, else to that type; a method's
promise is read at the member's type. A family guard testing its
operand's field (`ts.isIdentifier(n)`) narrows the binding to the arms
whose field can answer so, `undefined` answering no `true` and, where
the guard throws on it, no `false` (`PromiseCalls.memberFieldSlice`). A
member read of a receiver that may be `null` or `undefined` reads the
others (it throws on those, `nullishSplit`), and past it the receiver,
where a slot of the unit holds it, is without them (`readNarrowing`);
an assignment, a join and a loop head end that as any narrowing. A destructuring
default is added where the part may be `undefined`, made at the part's
type less `undefined` (a parameter's default at its annotation's); a
function the default makes within a callable part's type is held at that
type (a parameter's type is what the body reads), an object literal
default at that type's members it is within. Strict equality with
a literal holding narrows the operand, where it may hold the literal
(`unknown` included), to the literal (but `0`, which `-0` equals too);
a comma expression tested is its last operand's test, where the test
assigns no binding; equality with an operand holding one of
several singletons (each member of its type one, `equalitySplit`)
narrows each operand to the union of its slices at the
singletons the other may hold. `k in x` holding states a record's optional
`k` present (a field where the record states one, else a view) and a
dictionary not naming `k` with `k` a view of its index. `Array.isArray`
holding keeps the labels the edge's observation keeps
(`arrayRefine`, `BranchRefinement.arraySlice`). A discriminant test no
member of a binding can answer so leaves the binding no value; an arm a
test leaves a binding or path no value is walked for its entries, and
where it completes or returns is unreached.
A member read whose receiver supplies no cell contract is a located
refusal, as `Plans.readCell`, including a binder meet
whose bound supplies no readable row. A primitive member whose prototype
is absent from the unit is likewise a located read refusal
(`Plans.primitiveArms`).

## Field contents

A statement entry states the member paths a test
narrowed (its `current` contents, an execution point's `entryCurrent`),
each a member of an object other than `length`: a test of the path, a
guard or a family guard whose actual it is (a guard's only where its call
changes no value of the heap), and a discriminant test of a member of it
(`o.key.kind` narrows `o.key` to the arms whose `kind` can answer so),
where some read of the unit's walk reads the path, or a longer path of its
root, at its narrowed type. A
path's narrowing ends at a write of its field, at an assignment of its
root (a destructuring assignment's from its first target on), after a
call whose instance may change a value of the heap (or whose callee is
unknown) but where each member of the path is a key every arm of its
receiver states stable, and, but such
stable paths, after the left operand of `&&` or `||` whose right operand's
walk ends a path; a guard's call narrows its actual's path only where its
own call ends none. A method call reads its member path at its narrowed type before walking
its actuals, as any other read; the
receiver remains the object holding the member. A path's prefix is read at its narrowed type; a
write of an element at a key naming no one field or number, and
`Object.assign`, end every path; after `o.f ??= v` (and `||=`, `&&=`)
the path `o.f` holds the assignment's value, and after `o.f = v`, of an
immutable binding's object every record arm of which states `f`, its
contract less the nullish values `v` does not admit; a handler states none. An array literal assigned to an array pattern of as many names or
members (`[o.f] = …`, at the field's type), none defaulted, is made at
the tuple of their declared types. A path narrowed
before a loop is stated at its head, at each statement entry of its body
and past its exit where nothing in its test, body and update ends it (a
write of a field the path reads, an assignment of its root, a call that
may change a value of the heap) and its root is no binding the loop
declares; over a `for...of`, also only where the iterable is an array,
the root holds no allocation (an object or array literal) and each member
of the path is a required field every record arm of its receiver states,
none a `length` (the locations an
iterator's step keeps).
Over a `for` or `while` loop, a path whose root the loop neither
declares nor assigns is held from its head on, through the test and the
body, where nothing in the loop calls or writes (an increment or an
assignment of a binding aside) or each member of the path is stable.
After such a call, each binding a function literal walked so far assigns
(one it captures, held in a cell) is at its declared type again.

## Named guard offers

A longer signature collected for a named guard
retains the guard's written promise and proposed body effect when the
requested promise matches.
Its leading parameters supply that row's interior; the body's result
remains Boolean. The code check establishes the promise separately at
every advertised row, including the original signature.

## Constructor result offers

When an offered constructor's result
widens one of the class's method signatures, a fixed argument pack offers
that result at the constructor's own parameters. An element-rest offer
keeps the variadic rule. The constructor body and every method row establish the
proposed result; fixed storage contracts remain unchanged.

## Async literal results

A generic module value retains which binders
have no written bound, through equation lowering and preparation. Direct
primitive candidates of those binders are widened
before resolution and fresh allocation; explicit arguments and declared
bounds retain their constraints. A literal's contextual result guides
async return calls before allocation.
A widened candidate's observation and resolution result are instantiated
by its resolution certificate before comparison with the expected result;
a failed resolution retains the original candidate. Thus the expected
resolution result bounds widening.
An async block's result is the union of its walked return calls, as for
an expression body. The resolution instance and each code
body's return are checked; no existing promise store changes contract.

## Implemented overload interiors

A literal with no binders, rest or
defaults, expected at several fixed signatures of its own arity, proposes
that callable and walks its body once at each signature's parameters and
result. Each row supplies its expression,
entry and local storage proposals through the existing closure overlay.
Captured cells keep their declared contracts. The front places each
overlay at the body's execution points; `ClosureSetup` checks its
row count, and the file plans check every code body.

## Annotated recursive constants

A non-early constant’s annotation supplies
its recursive signature; the self-effect starts at keep/keep with a bound
on throws. The four-round
self proposal checks agreement with the walked body;
the annotation supplies contextual parameter types. Each code body must
establish its proposed signature and footprint.

## Annotated module callables

An immutable annotated callable retains a
separately inferred keep/keep effect on the same receiver, parameters and
result, including its bound on throws. The default
receiver admits source values; the literal’s internal `top` receiver
also admits them. The declaration keeps its signature and every other
component. The initialization’s code body and each use check this proposal.

## Write footprints

A compound write at a numeric literal index proposes
value `any`, store `grow`. A logical
write to a required writable field of source values proposes value `any`,
store `keep`; the receiver
is a binding or a path with known contents. `ExpressionEffects.sourceField`
checks the principal invariant operand. Each proposal is checked against
the body by the pass's footprint check ([a footprint](SINGLE-PASS.md#a-footprint)).

## Growth and assignment

A write of a key a constant's records may lack
is at the contract it adds the key at (the optional field's, else the
value's type, a literal's widened), the constant's records owning it
after. `Object.assign`'s value is the target's fields and then each
source's, a later key replacing an earlier one.

## Loop head types

At the head of a `while` or `for` loop, a binding
the loop assigns is at its declared type, but a source binding a slot
holds (no cell) that enters narrower than its declared type, with no
literal that widens within the declared type (`let i = 0` at `number`
widens at the head, as TypeScript widens a mutable binding's literals):
that one is at the join of
its entry type and its types on the edges back to the head, the loop's
test, body and update walked again from that join until the edges add
nothing, at most three walks, the walk's state restored after each; kept
where the join settles strictly within the declared type, else at the
declared type. The head's
types are its point claims, so the pass checks every edge into the head
against them, the entry and each back edge ([steps and obligations](SINGLE-PASS.md#5-steps-and-obligations)).
`TSCERT_FORCE=head-entry` states such a binding at its entry type,
unwalked, the adversarial proposal: `loop-head-contents` `continued`,
accepted unforced, is refused at an edge into its loop's head.

## First use through a module function

A use of an unannotated
constant's fresh array as an actual of a module function reads the
function at its one written signature, its slot's extension by a rest of
`unknown` aside: `joined([...a, ...xs])`
of `joined(terms: Term[])` builds `xs = forms.map(…)` at `Term[]`. The
pass checks the allocation at that contract and every use against it.

## Expected instance with a receiver

Where the instance the actuals give
has a result the expected type does not admit, the expected type's
instance binds the receiver's binders from the receiver first, an input as
the actuals are: `calls.map(name)` expected at
`(string | undefined)[]` is the call at `U` of `string | undefined`. The
instance must still admit every actual; the pass checks the call at it.

## Rethrowing handlers

A `try` with no finalizer whose handler has no
normal exit (it completes only by a throw) contributes its body's changes
alone to a normal return's footprint, the body's calls graded as outside
any handler; the handler's changes leave a throw unbounded where they
exceed the body's. The function's own unit checks
the proposal (the footprint check, a dead handler region bounding
throws alone).

## Captured cells' contents

No member path whose root a cell holds (a
`let` a closure shares, a captured binding of a function literal) is
narrowed: a field's contents are stated of an immutable binding's
object alone. A test that changes a value location
ends a cell's narrowed contents in both its arms, at the step
; and a cell whose contract names a type
parameter keeps its contract under a test, as `observed_contents` keeps a
contract that is no union of atoms. A member of a
union of objects is read at every object clause of each arm, a bounded
binder's meet row at its bound's clauses (`Synthesis.memberFor`).

## Dispatched callbacks

For a declaration's footprint, a callback walked
at the callable an actual's method takes (a string's `replace` at a
regex's `[Symbol.replace]`) changes what that method's signature and the
callback's own signatures state, the call's member read at its claimed
row; any other function passed to a
generic module function's call changes everything. The function's own unit
checks the proposal; `TSCERT_FORCE=callbacks` still refuses
`invalid-map-fresh-alias` `drained`.

## Casts through `unknown`

`x as unknown` is at `x`'s type
, so the outer cast of `x as unknown as H`
is the obligation that `x` meets `H` (a sealed handle's representation and
invariant); the cast's own claim is checked against its annotation
(`Atoms.lean`'s `cast-annotation`).
