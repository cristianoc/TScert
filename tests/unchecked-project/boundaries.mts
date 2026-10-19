/* Functions at a unit's boundary, each of which must state its types, and
 * functions inside a unit, which need not. */
declare const flag: boolean;

export function inferred(x: number) { // expected: unannotated
  return x;
}
export const arrow = (x: number) => x; // expected: unannotated
export const chosen = flag ? (x: number) => x : (x: number): number => x + 1; // expected: unannotated
export const listed = [(x: number) => x]; // expected: unannotated
export const sequenced = (Math.random(), (x: number) => x); // expected: unannotated
export let assignedLater: (x: number) => number = (x: number): number => x;
// The type of `assignedLater`, which its annotation states, gives the
// assigned function its context.
export const reassigned = (assignedLater = (x) => x);
export const object = {
  method(x: number) { // expected: unannotated
    return x;
  },
  property: (x: number) => x, // expected: unannotated
  get value() { // expected: unannotated
    return 1;
  },
};
export class Counter {
  count = 0;
  step = flag ? (by: number) => by : (by: number): number => -by; // expected: unannotated
  constructor(start: number, extra = 0) { // expected: unannotated
    this.count = start + extra;
  }
  next() { // expected: unannotated
    return this.count + 1;
  }
}
export default () => 1; // expected: unannotated
// A module `let` or `var` is read and written by the module's units: its
// type is written, as a `const`'s need not be.
export let counter = 0; // expected: unannotated
export var total = 0; // expected: unannotated
export let counted: number = 0;
// A `var` in a block or a loop of the module is the module's binding, which
// a function reads; a block's `let` and a function's `var` are not.
{
  var hidden = 0; // expected: unannotated
  let local = 0;
  hidden += local;
}
for (var step = 0; step < 1; step++) {} // expected: unannotated
export function read(): number {
  var inner = hidden + step;
  return inner;
}
export const fixed = 0;

// A written type gives these their types: the binding's, the parameter's,
// the context of an argument.
export const typed: (x: number) => number = (x) => x;
export const shaped: { m(x: number): number } = {
  m(x) {
    return x;
  },
};
export function local(xs: number[]): number[] {
  const twice = (x: number) => x * 2;
  return xs.map((x) => twice(x));
}
export const asserted = 1 as number; // expected: as
