// A `ReadonlySet`'s `has` called in a `findIndex` callback. The interface
// states no `[Symbol.toStringTag]`, so a program's object with a `has` of
// its own is a `ReadonlySet`, and its `has` may shrink the list: the member
// keeps its declared effect, and the element is `number | undefined`.
export function first(
  names: ReadonlySet<number>,
  list: readonly number[],
): number {
  return list.findIndex((n: number) => names.has(n));
}
