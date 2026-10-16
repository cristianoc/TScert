// Ambient declarations: values the module states the types of and nothing
// here defines. Each is an assumption at its declared type, as an import is:
// a function, an annotated constant, a class constructed with `new`, and a
// generic function at the instance its call names. A value may share its
// name with an interface, the name's other meaning, as `Point` does here.
declare function double(x: number): number;
declare const limit: number;
declare const origin: { readonly x: number };
declare class Counter {
  count: number;
  constructor(start: number);
  bump(): number;
}
declare function identity<T>(x: T): T;
interface Point {
  readonly x: number;
}
declare const Point: { readonly origin: Point };
export function next(): number {
  const c = new Counter(double(limit));
  return c.bump() + origin.x + identity(limit) + Point.origin.x;
}
