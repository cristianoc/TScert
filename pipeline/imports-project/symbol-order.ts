// A module whose interface type reaches `Map`'s, keyed by well-known
// symbols: its document lists `Symbol.toStringTag` and the collections'
// iterator mark third and fourth, after the array built-ins' two.
export function count(m: Map<string, number>, k: string): number {
  return m.get(k) ?? 0;
}
