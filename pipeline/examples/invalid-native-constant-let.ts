// A `let` annotated `ReadonlyMap` and initialized by a `Map` is read at its
// annotation, which a later assignment may meet with another object: its
// `get` may change any store, so the bound on `xs` is lost past the call.
// Under Node the other map's `get` empties the array, and `xs[0]!` reads
// `undefined`.
export function first(xs: number[], other: ReadonlyMap<string, number>): number {
  let table: ReadonlyMap<string, number> = new Map()
  if (xs.length > 5) table = other
  if (xs.length === 0) return 0
  table.get('a')
  return xs[0]!
}
