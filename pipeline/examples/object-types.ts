// `object` is every object: an ordinary one, an array, a function or a class
// value. `{}` is every value but `null` and `undefined`, primitives included;
// it is not an empty record.
class Point {
  x: number = 0;
}
function fromRecord(r: { a: number }): object {
  return r;
}
function fromArray(xs: number[]): object {
  return xs;
}
function fromFunction(f: (n: number) => number): object {
  return f;
}
function fromClass(): object {
  return Point;
}
function fromInstance(p: Point): object {
  return p;
}
function anyObject(o: object): {} {
  return o;
}
function fromNumber(n: number): {} {
  return n;
}
function fromString(): {} {
  return "s";
}
function fromBoolean(b: boolean): {} {
  return b;
}
function fromLiteral(): {} {
  return { a: 1 };
}
// A mapped type over no key has no member: it is `{}`.
function noKeys(): Record<never, number> {
  return 1;
}
export function use(): {} {
  const o: object = fromRecord({ a: 1 });
  return [
    fromArray([1]),
    fromFunction((n: number): number => n),
    fromClass(),
    fromInstance(new Point()),
    anyObject(o),
    fromNumber(1),
    fromString(),
    fromBoolean(true),
    fromLiteral(),
  ];
}
