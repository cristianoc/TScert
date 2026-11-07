// A conditional clamp one past the count, `end < count ? end : count + 1`:
// the joined arms state `segmentEnd ≤ count + 1` only, and the read
// `xs[i]!` at `i = count` is refused. The loop reads past the array's end
// (run under Node: `clampedSum([1, 2], 5)` reads `undefined` at `number` at
// `i = 2`, a sum `NaN`).

/** @requires safeInteger(end) && 0 <= end */
export function clampedSum(xs: number[], end: number): number {
  const count = xs.length;
  const segmentEnd = end < count ? end : count + 1;
  let s = 0;
  for (let i = 0; i < segmentEnd; i++) s = s + xs[i]!;
  return s;
}
