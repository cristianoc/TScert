// A push of a value its quantified fact excludes: `ends.push(widths.length)`
// appends the length, which `ends[i] < widths.length` excludes, so the fact
// holds of no longer prefix than the old one and the loop's head refuses its
// entry (run under Node: `sumAfterPush([5], [])` pushes `1`, then reads
// `widths[1]`, `undefined` at `number`).

/** @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
export function sumAfterPush(widths: number[], ends: number[]): number {
  ends.push(widths.length);
  let total = 0;
  /** @invariant forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
  for (let i = 0; i < ends.length; i++) total += widths[ends[i]!]!;
  return total;
}
