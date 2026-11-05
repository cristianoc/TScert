// A dictionary may lack the key a pattern reads: TypeScript types the
// read at the dictionary's values, and `total({})` returns `undefined` for
// its number result.
export function total(counts: Record<string, number>): number {
  let n = 0;
  ({ total: n } = counts);
  return n;
}
