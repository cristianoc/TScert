// A counter guard, an inner loop, then `break`: the guarded body is never
// reached (the loop breaks on its first pass, so `i` stays 0). The
// producer's facts settle (pretext's measurement.ts#getFontKanaKerning has
// this shape); the edge into the unreachable inner loop is refused, which
// the gap records.
export function settleMin(n: number): number {
  for (let i = 0; i < n; i++) {
    if (i > 0) {
      for (let j = 0; j < 5; j++) {}
    }
    break
  }
  return 0
}
