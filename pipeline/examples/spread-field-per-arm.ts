// TypeScript types the written `k` per arm of the expected union: `boolean`
// where the copy has `a`, `true` where it has `b`. The copy is allocated per
// pair of the merge's operand clauses, each field at the type of the arm that
// pair gives, so each arm holds its own writable `k`.
type AB = { a: number } | { b: string };
type Tagged = { a: number; k: boolean } | { b: string; k: true };

export function tag(x: AB): Tagged {
  return { ...x, k: true };
}
