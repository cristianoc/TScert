// What is known of a field's contents (here: not null) survives a write
// that may alias it where every value the write may leave meets it
// (`weak-update`, `HeapExpressionRules.keptCells`): a field write of a
// number into a record that may be the same, an element write at a
// literal index, and a push, which replaces a store by a store.
export type Box = { v: number | null };

export function fieldWrite(a: Box, b: Box): number {
  if (a.v === null) return 0;
  b.v = 3;
  return a.v;
}

export function elementWrite(a: Box, xs: number[]): number {
  if (a.v === null) return 0;
  xs[0] = 1;
  return a.v;
}

export function pushWrite(a: Box, xs: number[]): number {
  if (a.v === null) return 0;
  xs.push(1);
  return a.v;
}
