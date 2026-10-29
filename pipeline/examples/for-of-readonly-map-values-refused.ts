// A `for...of` over a `ReadonlyMap`'s `values()`: the overlay reads the
// result as an `Iterator`, which a program's object meeting the interface
// may return without `[Symbol.iterator]`, so the loop has no iteration
// intrinsic. `exportsOf` in `declaration-graph.mts#collectDeclarations`
// iterates the map itself instead (SOURCE-REWRITES.md, "A `for...of` over a
// `ReadonlyMap`'s values").
export function total(m: ReadonlyMap<string, number>): number {
  let sum = 0;
  for (const v of m.values()) sum += v;
  return sum;
}
