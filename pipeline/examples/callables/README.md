# Callables

Source examples for callable contracts, each a pipeline case run through the
parser, the OCaml producer and the Lean checker.

Add coverage for a distinct semantic obligation or an interaction that could
fail even when its components pass separately. Minor syntax variations alone
do not warrant another example. If a standalone Lean test takes too long to
develop or check, defer it until the case is expressible through the pipeline.

## The callable surface

What a callable is and what its type promises is
[CALLABLES](../../../docs/CALLABLES.md); argument lists, rests and spreads are
[calls](../../../docs/SOURCE-MODEL.md#calls), receivers
[receivers](../../../docs/SOURCE-MODEL.md#receivers), parameter defaults and
their order
[parameter initialization order](../../../docs/SOURCE-ELABORATION.md#parameter-initialization-order),
and every refused form, with the reason and its cases,
[functions, calls and methods](../../../docs/SOURCE-FRAGMENT.md#fragment-boundary)
in the refusal index. The encoding is the
[Fragment's](../../../docs/FRAGMENT-FORMAT.md#expression-closures-and-calls).

[`generic-rest.ts`](../generic-rest.ts) checks a returned `T[]`, independent
Boolean and numeric uses of one closure, a fixed prefix with empty rest and
tuple spread, a universal default, a possibly sparse spread, and a variadic
callback inside a generic body. Its negative controls reject a captured
Boolean array as arbitrary `T[]` and a Boolean actual sent to a rest callback
at arbitrary `T`. [`spread-holes.ts`](../spread-holes.ts) writes past the end
of a Boolean array, leaving a hole a spread would pass as `undefined` in a
`boolean[]`; TypeScript accepts the write, and the pipeline refuses it.

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
list's length and indices after its receiver, in order.

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
