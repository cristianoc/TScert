// The loop's `g` is a caller's function, not the local arrow of the same
// name: it may own a `call` property returning a string.
function probe(fs: (() => number)[]): number {
  const g = (): number => 1;
  for (const g of fs) return g.call(undefined);
  return g.call(undefined);
}
