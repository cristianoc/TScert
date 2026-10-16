// An `Iterable<number>` may be any object with a `[Symbol.iterator]`: the
// loop runs its iterator by the protocol, typed by the standard library's
// `Iterable`, `Iterator` and `IteratorResult`. Left early by `return`, it
// calls the iterator's `return` where it has one, after the returned value
// is read.
export function first(values: Iterable<number>): number {
  for (const v of values) return v;
  return 0;
}

// A guard on the loop's element holds for the element it tested.
export function firstPositive(values: Iterable<number | null>): number {
  for (const v of values) {
    if (v !== null && v > 0) return v;
  }
  return 0;
}
