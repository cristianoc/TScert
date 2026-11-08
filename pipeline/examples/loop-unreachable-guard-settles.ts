// A counter guard and inner loop in a loop that breaks on its first pass.
// The guarded body is unreachable: i stays 0. Pretext's
// measurement.ts#getFontKanaKerning has this shape.
export function settleMin(n: number): number {
  for (let i = 0; i < n; i++) {
    if (i > 0) {
      for (let j = 0; j < 5; j++) {}
    }
    break
  }
  return 0
}
