// Bounds pattern P19: a running sum of element lengths.
// Fact: at + (the lengths of segments[i..]) = total < offsets.length at the
// loop head.
// Pretext: rich-inline.ts findSegmentSources (2 sites).
// Gap: no term sums over elements, so `at` has no bound.
// (The document's program reads a parameter `offsets` no clause relates to
// `segments`, which is unsafe; here the view is allocated at the sum, and
// the lengths are bounded so that the sum is a safe integer.)
/** @requires segments.length <= 1000 && forall i in segments: segments[i].length <= 1000 */
export function sources(segments: string[]): number {
  let total = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(total) && 0 <= total && total <= 1000 * i */
  for (let i = 0; i < segments.length; i++) total += segments[i]!.length;
  const offsets = new Int32Array(total + 1);
  let s = 0;
  for (let i = 0, at = 0; i < segments.length; at += segments[i++]!.length) {
    s += offsets[at]!;
  }
  return s;
}
