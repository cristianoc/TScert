// A quantified fact extended across `push` (ARITHMETIC.md, "Quantified
// clauses"): a normal return of `push` keeps the receiver's elements at their
// indices and appends its actual at the old length, so `forall i in xs: B`
// over the whole receiver holds after `xs.push(a)` where `B` holds of `a` at
// index `xs.length`. pretext's builder (rich-inline.ts) pushes the current
// count of widths for each item, `itemSegments.push(widths.length)`, and its
// consumer, `narrowsLine`, reads `widths` between consecutive entries.

/** @requires forall i in itemSegments: safeInteger(itemSegments[i]) && 0 <= itemSegments[i] && itemSegments[i] <= widths.length */
export function extendSegments(
  widths: number[],
  itemSegments: number[],
  items: number,
): number {
  /** @invariant forall i in itemSegments: safeInteger(itemSegments[i]) && 0 <= itemSegments[i] && itemSegments[i] <= widths.length */
  while (itemSegments.length <= items) itemSegments.push(widths.length);
  let total = 0;
  for (let index = 0; index + 1 < itemSegments.length; index++) {
    for (let i = itemSegments[index]!; i < itemSegments[index + 1]!; i++)
      total += widths[i]!;
  }
  return total;
}

/**
 * @requires 1 <= widths.length
 * @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length
 */
export function sumAfterPush(widths: number[], ends: number[]): number {
  ends.push(widths.length - 1);
  let total = 0;
  /** @invariant forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
  for (let i = 0; i < ends.length; i++) total += widths[ends[i]!]!;
  return total;
}
