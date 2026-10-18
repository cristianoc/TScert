// A write that may alias the tested field discards the test's fact: `u` may
// be `t`, so after the write `t.mapping` may hold the number written.
type Box = { mapping: number[] | number };
export function wrong(t: Box, u: Box): number[] {
  if (!Array.isArray(t.mapping)) return [];
  u.mapping = 5;
  return t.mapping;
}
