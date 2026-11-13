// A write that may alias a field narrowed not null, of a value that may be
// null: the narrowing is not kept (`weak-update` needs every value the
// write may leave to meet it). Under Node `fieldWrite(o, o)` returns null
// where its type says number.
export type Box = { v: number | null };

export function fieldWrite(a: Box, b: Box, w: number | null): number {
  if (a.v === null) return 0;
  b.v = w;
  return a.v;
}
