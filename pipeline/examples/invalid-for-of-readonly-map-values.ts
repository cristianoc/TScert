// A `ReadonlyMap`'s `values()` stepped in a `findIndex` callback: a
// program's object meets the view, so its iterator's `next` is any
// function, which may shrink the list; the callback states no footprint
// `findIndex` admits, and `findIndex` hands it `undefined` (run under Node).
export function first(
  names: ReadonlyMap<string, number>,
  list: readonly number[],
): number {
  let seen = 0;
  list.findIndex((n: number): boolean => {
    seen = n;
    for (const x of names.values()) seen = seen + x;
    return false;
  });
  return seen;
}
