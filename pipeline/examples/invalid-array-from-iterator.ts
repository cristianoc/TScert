// A length record may hold an iterator of its own, which `Array.from` steps:
// client code, which may change the array a `map` reads (run under Node:
// the result has a hole). A callback calling it is not preserving.
export function grow(
  xs: number[],
  items: { readonly length: number },
): number[][] {
  return xs.map(() => Array.from(items, (_, i) => i));
}
