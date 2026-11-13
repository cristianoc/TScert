// Bounds pattern P19, the supported neighbour of
// `bounds-pattern-running-sum-refused`: the view allocated at the sum, read
// at the sum itself.
// Pretext: rich-inline.ts findSegmentSources.
/** @requires segments.length <= 1000 && forall i in segments: segments[i].length <= 1000 */
export function atTotal(segments: string[]): number {
  let total = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(total) && 0 <= total && total <= 1000 * i */
  for (let i = 0; i < segments.length; i++) total += segments[i]!.length;
  const offsets = new Int32Array(total + 1);
  return offsets[total]!;
}
