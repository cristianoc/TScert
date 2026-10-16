// A binder bounded by another is the meet of the two parameter rows, within
// the other's bound when it has one: below the other binder, and below its
// bound.
class DependentBox<T, U extends T> {
  first: T;
  second: U;
  constructor(first: T, second: U) {
    this.first = first;
    this.second = second;
  }
}

function widen<T extends string | number, U extends T>(x: U): T {
  const y: T = x;
  return y;
}

function throughBound<T extends { size: number }, U extends T>(x: U): number {
  return x.size;
}

export function use(n: number): number {
  const box = new DependentBox(n, n);
  return box.second + widen<number, number>(n) + throughBound({ size: n });
}
