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
export let assignedLater = (x: number): number => x;
// The type of `assignedLater`, which its annotated initializer states, gives
// the assigned function its context.
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
