// pretext's `buildRangeText` clamps a range's end to the segment count with a
// conditional, `const segmentEnd = end < count ? end : count`, then reads
// below it. Each arm states what its answer of the test states and the
// declared binding equal to the arm's value; the two are joined, so
// `segmentEnd ≤ count` and `segmentEnd ≤ end` hold after the declaration and
// the loop's reads `xs[i]!` below `segmentEnd` are bounded (PROGRAM-TYPING.md,
// "Reads below the length").

/** @requires safeInteger(end) && 0 <= end */
export function clampedSum(xs: number[], end: number): number {
  const count = xs.length;
  const segmentEnd = end < count ? end : count;
  let s = 0;
  for (let i = 0; i < segmentEnd; i++) s = s + xs[i]!;
  return s;
}
