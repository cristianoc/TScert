// A literal inferred for an unbounded binder that the result does not return
// bare widens, as TypeScript widens it: `wrap(42)` is `{ v: number }` and
// `new Box(42)` a `Box<number>`, while `id(42)` stays `42`.
class Box<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}

function wrap<T>(x: T): { v: T } {
  return { v: x };
}

function id<T>(x: T): T {
  return x;
}

export function use(): number {
  const w: { v: number } = wrap(42);
  const b: Box<number> = new Box(42);
  const inferred = new Box(7);
  const n: 42 = id(42);
  return w.v + b.value + inferred.value + n;
}
