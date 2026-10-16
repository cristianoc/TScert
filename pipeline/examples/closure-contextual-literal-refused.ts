// TypeScript types `o` from its context as an object type written nowhere
// by name: no annotation states it.
export function firsts(pairs: { a: number }[]): number[] {
  return pairs.map((o) => o.a);
}
