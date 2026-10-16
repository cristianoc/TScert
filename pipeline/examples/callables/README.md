# Callables

Source examples for callable contracts, each a pipeline case run through the
parser, the OCaml producer and the Lean checker.

Add coverage for a distinct semantic obligation or an interaction that could
fail even when its components pass separately. Minor syntax variations alone
do not warrant another example. If a standalone Lean test takes too long to
develop or check, defer it until the case is expressible through the pipeline.

## The callable surface

Supported. Function declarations, function expressions and arrows are callable
values.
Parameter lists of any length are checked, with the callee evaluated before the
actuals and the actuals left to right. A call may omit a trailing position
whose contract admits `undefined`, which is the value the machine binds there;
`x?: T` is carried as `T | undefined`. A parameter may instead carry a default,
`y: B = e`: its position admits `undefined` for the same reason, and `e`
replaces that value before the body runs, so the body reads `B`; a default may
read initialized earlier parameters. A rest parameter whose contract is a tuple
of required positions, `...rest: [B, C]`, is those positions in the signature
and one fresh array in the body, allocated where the parameter is bound. A
spread writes the elements of such a tuple in place of the last arguments, read
after every earlier argument has been evaluated. A rest parameter whose
contract is a mutable array, `...rest: T[]`, makes the closure variadic: it
takes any number of actuals past its fixed parameters, each at `T`, and the
call collects them into a fresh array. Spreads into it may stand anywhere among
those actuals, any number of them, each read where it is written: a spread
followed by an actual that runs code is copied there. An optional fixed
parameter before the rest may be omitted. A function type promises which actual
lists a caller may write, not which code the callee has, so a variadic closure
meets a fixed signature whose positions it admits, one value may carry fixed and
variadic signatures, and a callable object may be variadic. A current or later raw argument slot is
not a readable binding. Literal closures may capture later parameters through
acyclic closure conversion: their allocation waits until their captures are
initialized, and no executing initializer may read or expose a pending closure.
Effectful defaults retain source order. Quantified defaults, including inputs
of type `T | undefined`, have universal initialization certificates.
Callables pass as
arguments, return as results, escape as closures and appear as thunks; they form
unions with null and with each other, are selected by
`typeof x === "function"` guards, and are held in cells, including recursive
invocation through one. A fresh arrow takes one initialized `value` field through
explicitly typed `Object.assign`. `.call` applies to local arrows and their
immutable aliases, with the receiver evaluated and then discarded. `.bind` saves
an argument prefix on the same arrows. One closure may advertise several signatures — an intersection of arrows —
and is then checked once per signature, each a separate obligation on the same
body; the producer states what that body claims under each. TypeScript rejects
the implementations this accepts. Generic declarations, their bounds and
quantified local closures are checked at every instance.

Not supported, with the refusal each one meets:

| Form | Where it stops |
| --- | --- |
| `arguments` | the producer refuses it as an unbound name; a binding named `arguments` is refused in sloppy code |
| A spread into fixed parameters of an array that is not a tuple of required positions | the producer: a spread argument needs a tuple of required positions |
| A spread of an array that may have holes into a rest whose element type lacks `undefined` | the write leaving the hole is refused; TypeScript accepts the call ([witness](../spread-holes.ts)) |
| `.call` on a method read off an object | a source refusal: `.call` requires a known local function ([call-objects.ts](call-objects.ts)) |
| One quantified method instantiated at two receiver contracts | evidence search fails ([generic-receivers.ts](generic-receivers.ts)) |
| Accessors | a source refusal: the heap model has data properties only |
| Generators | a source refusal: no term of the calculus suspends at `yield` |
| A function expression referring to its own name | a source refusal: a recursive binding |
| A callable object type with an index signature or a readonly field | refused at the annotation: it needs a combined clause |
| A call of an intersection of a function type and a record or array type | the producer: an annotation's meet does not form it |
| A closure capturing a `for` loop's `let` | a source refusal: JavaScript copies the binding per iteration |
| Sloppy code reading `this` at a receiver type that may hold a non-object | a source refusal: the receiver conversion has no step in the model |

Refusal reasons are defined in
[obligation diagnostics](../../../docs/OBLIGATION-DIAGNOSTICS.md); the encoding and its
restrictions belong to the
[protocol](../../../docs/FRAGMENT-FORMAT.md#expression-closures-and-calls).

The hole-spread witness writes past the end of a Boolean array, leaving a
hole. Spreading it would materialize `undefined` in a `boolean[]`. TypeScript
accepts this contract violation; the pipeline refuses the write.

### Defaults

A default is an entry node of the code's graph: a tag dispatch on
`undefined` at the parameter's slot, the default's evaluation on one arm. The
slot's type is `T ∪ {undefined}` and the initialized binding's `T`; in a
generic closure the code is checked at its scheme row, so initialization must
establish `T` for every assignment of the binders, and observed calls cannot
justify it. It never obtains `T` by deleting `undefined` from the input: `T` can
itself contain `undefined`.

Forward capture uses closure conversion in the trusted Lean extractor. A literal closure allocation can wait until its
captures are initialized because no pending closure is exposed and parameters
are immutable in this fragment. It is allocated once, preserving sharing, and
captures outer mutable cells by identity. All potentially effectful defaults
retain source order. `Fragment.parameterOrder` fixes the entry nodes' order,
and its dependency traversal is exhaustive.

Cyclic captures and exposing a pending closure during initialization
are refused, even where a supplied actual could avoid the default.
Supporting them needs an explicit initialization frame with
initializedness separate from fixed world types; it must not expose raw actuals
or retype locations. Early invocation of a pending closure and a Boolean
initializer claimed at arbitrary `T` are refused at their own obligations. The
closure-conversion argument is part of the trusted
source adapter, as other JavaScript-to-calculus correspondence is; Lean proves
safety of the resulting term, not equivalence to a formal JavaScript semantics.

### Rests and spreads

Fixed and variadic signatures share the
[common function equation](../../../docs/SEMANTICS.md#one-meaning-for-callable-contracts).
Code collecting a rest allocates the store of the
further actuals before its run (`graphEntry`), and `restsT_of_graphRest` lifts
the code's check at each variadic signature to the variadic contract; over a
binder, at every assignment of it. Both declarations and closures are
consumed by `SourceClaimJson.checkJson_safe` as graph requests.

[`generic-rest.ts`](../generic-rest.ts) checks a returned `T[]`, independent Boolean and numeric uses of one closure,
a fixed prefix with empty rest and tuple spread, a universal default,
a possibly sparse spread, and a variadic callback inside a generic body.
The negative controls reject a captured Boolean array as arbitrary `T[]` and a
Boolean actual sent to a rest callback at arbitrary `T`. Both CLI entry points
reject altered rest contracts, substitutions, source binding flags and operand
claims. These are universal certificates plus ground consequences, never
observed-call monomorphization. Required tuple snapshots retain their dense
contract; potentially sparse arrays need an element contract admitting
`undefined`.

Restrictions on generic body forms and nested quantification are stated in
[SOURCE-CLAIMS](../../../docs/SOURCE-CLAIMS.md#quantified-callables-and-their-eliminations).

### Receivers

Every signature states a receiver beside its parameters and result, and every
call passes one: `undefined` for a plain call, the object for a method call,
the first argument for `.call` and `.apply`. An arrow's `this` is a capture of
the enclosing ordinary function's receiver. `.bind` allocates a forwarding
descriptor whose receiver a later `.bind` or `.call` cannot replace; `.apply`
reads its list's `length` and each index in order before invoking.
[SOURCE-MODEL](../../../docs/SOURCE-MODEL.md#receivers) owns the receiver rules,
[FRAGMENT](../../../docs/FRAGMENT-FORMAT.md#receivers) their encoding, and the call order
follows ECMA-262's EvaluateCall and OrdinaryCallBindThis
([ECMA-262](../../../docs/REFERENCES.md#ecma-262)).

## Examples

| Example in [unions.ts](unions.ts) | What it establishes                                                                                                                                                                                                            |
| --------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `guardedCallableUnion`            | A null guard permits calling either remaining signature and preserves both possible results.                                                                                                                                   |
| `andGuardedCallable`              | `&&` calls only the non-null function; its true result does not erase the skipped false result.                                                                                                                                |
| `orGuardedCallable`               | `\|\|` skips the call for null, preserving true alongside the callable's false result.                                                                                                                                         |
| `coalescedCallable`               | Null and undefined select a fallback function before invocation; either callable can supply the result.                                                                                                                        |
| `capturedGuardedCallable`         | A returned closure retains the immutable capture's non-null refinement and both callable alternatives after the branch ends.                                                                                                   |
| `aliasedCallableSelection`        | A selected local alias retains both callable alternatives through a nested closure; its callability does not transfer to the original nullable input.                                                                          |
| `sharedCallableDomain`            | A call must fit the shared argument domain of Boolean-accepting and true-only alternatives, while retaining both possible results.                                                                                             |
| `branchLocalCallableDomains`      | Branch-refined Boolean arguments satisfy different callable domains; neither branch facts nor singleton results can be transferred to the other branch.                                                                        |
| `callableArgumentWrite`           | An assignment used as a call argument checks both storage and parameter contracts; its false RHS admits an explicitly refined false-only callable view.                                                                        |
| `selectedCallableAfterMutation`   | A selected callable remains fixed while a shared-cell write changes its live capture. A same-typed callee substitution needs fresh evidence.               |
| `callbackProbeDoesNotNarrow`      | A Boolean-returning probe has no type-predicate contract: its true result cannot narrow the captured callback in the caller, whose own null guard remains required.                                                            |
| `ambiguousCaptureGuard`           | A successful disjunction may be justified by a separate Boolean flag; the returned closure must retain the nullable capture and guard it itself.                               |
| `compoundAbsenceCapture`          | A returning null-or-undefined guard must exclude both tags before closure creation.                                                                        |
| `twoAbsenceCapture`               | Eliminating undefined must retain null in a returned closure capture; its inner null guard is still needed.                       |
| `laterGuardedCallback`            | A guard after closure creation cannot refine its earlier capture; the closure needs its own guard. |
| `escapedLocalCallback`            | A returned closure captures a guarded nullable const whose declaration is wider than its initializer.                    |
| `distinctNullableCallbacks`       | Same-typed local callbacks require independent null guards.                                                     |
| `nullableFactoryResult`           | A factory result can mix a callable with null; both alternatives survive the factory contract and invocation, and the caller must guard the returned value before calling it.                                                  |
| `returnedCallableDomain`          | Factory branches with Boolean and true-only callable domains both implement a true-only result contract; neither the nested result claim nor a later call can widen that shared domain.                                        |
| `branchReturnedCapture`           | A factory returns different closures from a null-test branch; the escaping closure retains its own factory argument's refinement, which cannot transfer to the nullable caller capture.                                        |
| `nestedCallableArgumentWrite`     | A write inside a closure's call argument preserves the captured receiver and named RHS through temporary bindings; a same-typed capture cannot replace the parameter in the evidence.                                          |

Each file in this directory is a pipeline case
([`cases.mts`](../../cases.mts)).

[factories.ts](factories.ts) contrasts factories allocating a private cell per
invocation with a control sharing a cell outside the factory.
[arguments.ts](arguments.ts) covers a stateful callback passed to an invoker and
`escapedCallbackArgument`, where that callback enters a wrapper factory, escapes
as a captured parameter, and returns through another invoker; an intervening
cell write distinguishes execution-time reads from creation-time snapshots. Its
`exchangeMultiArgument` transports a two-argument function through a mutable
cell and narrows its first domain on return.
[cells.ts](cells.ts) covers mutable callback storage: `replacedCallback`
distinguishes a saved function value from a later cell read after replacement,
and `recursiveCallback` installs a callback that reads and invokes itself
through the cell, then reaches a base case.
[thunks.ts](thunks.ts) covers zero-argument creation and invocation: a
returned thunk reads a cell after a write, and a saved thunk remains distinct
from its replacement.
[arity.ts](arity.ts) requires callee evaluation first, actuals left to right,
then the body; it also checks a returned closure capturing its second
parameter and a multi-argument union callee.
[guards.ts](guards.ts) selects callable signatures with strict
`typeof ... === "function"` and `!==` guards.

Overloaded closures are
[`overloads.ts`](../overloads.ts), with
`invalid-overload.ts` claiming a signature its body does not implement. The
claims carry one interior set per signature, the same mechanism compiled scheme
eliminations use, and a block body is checked at each signature's own result
rather than at its one enclosing annotation.

[rest-arguments.ts](rest-arguments.ts) collects a tuple rest, reads it by
index, and spreads one in place of the last arguments, with and without fixed
arguments before it. A spread relies on the array's positions being what it
yields, which holds because this fragment cannot install an iterator of its
own. [variadic-arguments.ts](variadic-arguments.ts) collects an array rest in a
declaration and in closures, calls them with any number of actuals and with
several spreads among them, spreads a tuple into an array rest, passes a
variadic closure to a function that calls it, calls one through a fixed
signature, omits an optional parameter before the rest, gives one value fixed
and variadic signatures, and makes a variadic callable object with a field.

[optional-arguments.ts](optional-arguments.ts) omits an optional trailing
argument, writes it, and writes `undefined` for it; the three agree at run
time. [default-arguments.ts](default-arguments.ts) gives a parameter a
default, writes the argument anyway, and reads an earlier parameter in a
default. The lowering binds the parameter's own slot anonymously and binds its
name to the value that replaces an omitted argument, so no name is invented
and nothing shadows.

[methods.ts](methods.ts) passes a method's object as its receiver and keeps a
copied method's plain call apart; [apply.ts](apply.ts) reads an `.apply`
list's length and indices after its receiver, in order. Two receiver examples
are gap cases: [call-objects.ts](call-objects.ts) uses `.call` with a
different object as receiver of a method read off an object, which is refused
(`.call` requires a known local function), and
[generic-receivers.ts](generic-receivers.ts) instantiates one quantified
method at two receiver contracts, where evidence search fails.

[function-field.ts](function-field.ts) initializes one mutable field on a fresh
arrow, writes through the original reference and reads/calls through an alias;
explicit `Object.assign` type arguments are required.
[receiver-call.ts](receiver-call.ts) brings `.call` on local arrows into the
pipeline, including an alias of a function with a field and a captured nullary
arrow. The receiver expression is evaluated before actuals even though its
value is ignored.

`make cases P=callables/` runs these examples. The
[test index](../../../tests/README.md) describes suite ownership, and the
[protocol](../../../docs/FRAGMENT-FORMAT.md#expression-closures-and-calls) owns callable
signature restrictions.
