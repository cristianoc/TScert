// Bounds pattern P8, the supported neighbours of
// `bounds-pattern-write-at-length-refused`: a read below the old length after
// a write at the length, a write below the length, and measureAnalysis's
// first read of `starts`.
// Pretext: prepare.ts measureAnalysis.
/** @requires safeInteger(k) && 1 <= k && k <= xs.length && k <= 1000000 */
export function readBefore(xs: number[], k: number): number {
  xs[k] = 1;
  return xs[k - 1]!;
}

/** @requires safeInteger(k) && 1 <= k && k < xs.length */
export function readBelow(xs: number[], k: number): number {
  xs[k] = 1;
  return xs[k - 1]!;
}

/** @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= starts.length && (from === 0 || from < to) */
export function first(starts: number[], from: number, to: number): number {
  return from === 0 ? 0 : starts[from]!;
}
