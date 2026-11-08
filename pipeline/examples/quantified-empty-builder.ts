// pretext rich-inline.ts: itemSegments built from an empty array, then consumed.
export function buildSegments(
  widths: number[],
  items: number,
): number {
  const itemSegments: number[] = [];
  /** @invariant forall i in itemSegments: safeInteger(itemSegments[i]) && 0 <= itemSegments[i] && itemSegments[i] <= widths.length */
  while (itemSegments.length <= items) itemSegments.push(widths.length);
  let total = 0;
  for (let index = 0; index + 1 < itemSegments.length; index++) {
    for (let i = itemSegments[index]!; i < itemSegments[index + 1]!; i++)
      total += widths[i]!;
  }
  return total;
}

