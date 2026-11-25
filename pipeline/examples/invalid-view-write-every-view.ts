// A write through a `Uint8Array` can alias another `Uint8Array` (e.g. a
// subarray view), so a quantified upper bound over a `Uint8Array`'s elements
// must NOT survive an unseparated `Uint8Array` write.
/**
 * @requires 0 < xs.length && 0 < other.length && 0 < table.length
 * @requires forall i in xs: safeInteger(xs[i]) && 0 <= xs[i] && xs[i] < table.length
 */
export function writeViewAliased(xs: Uint8Array, other: Uint8Array, table: number[]): number {
  other[0] = 99;
  return table[xs[0]!]!;
}
