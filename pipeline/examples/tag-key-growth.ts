// A key-adding write at a string key known only at run time verifies; the
// forged control (`pipeline/test.mts`) claims its key at `symbol`, which may
// be `Symbol.toStringTag`, and is refused at the write.
export function grown(k: string): { [k: string]: number } {
  const d: { [k: string]: number } = {};
  d[k] = 1;
  return d;
}
