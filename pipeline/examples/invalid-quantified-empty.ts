// Non-empty arrays do not satisfy an arbitrary quantified body.
export function invalidEmpty(widths: number[]): number {
  const ends: number[] = [7];
  let total = 0;
  /** @invariant forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
  for (let i = 0; i < ends.length; i++) total += widths[ends[i]!]!;
  return total;
}
