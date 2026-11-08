// Pretext rich-inline.ts's builder loop: itemSegments remains bounded
// while an unrelated, freshly allocated array grows and receives element
// writes.
/** @requires forall i in itemSegments: safeInteger(itemSegments[i]) && 0 <= itemSegments[i] && itemSegments[i] < widths.length */
export function build(widths: number[], itemSegments: number[]): number {
  const scratch: number[] = [0];
  let sum = 0;
  /** @invariant forall i in itemSegments: safeInteger(itemSegments[i]) && 0 <= itemSegments[i] && itemSegments[i] < widths.length */
  for (let k = 0; k < itemSegments.length; k++) {
    scratch.push(sum);
    if (k < scratch.length) scratch[k] = -1;
    sum += widths[itemSegments[k]!]!;
  }
  return sum;
}
