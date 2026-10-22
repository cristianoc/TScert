// A `ReadonlySet`'s iterator, which TypeScript types `SetIterator`, stepped
// in a `findIndex` callback. A program's object meets `ReadonlySet`, so its
// iterator is any `Iterator`, whose `next` may shrink the list: it is no
// native collection iterator, which the host's iteration requires, and the
// loop is refused.
export function first(
  names: ReadonlySet<number>,
  list: readonly number[],
): number {
  const it = names[Symbol.iterator]();
  let seen = 0;
  list.findIndex((n: number): boolean => {
    seen = n;
    for (const x of it) seen = seen + x;
    return false;
  });
  return seen;
}
