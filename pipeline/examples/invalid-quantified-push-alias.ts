// A push into an array that may be the quantified one: no separation fact
// keeps `other`'s store apart from `ends`'s, so the push may lengthen `ends`
// by a value its fact excludes, and the loop's head refuses its entry (run
// under Node: `sumAfterPush([5], a, a)` with `a = []` pushes `1` into `ends`
// through `other`, then reads `widths[1]`, `undefined` at `number`).

/** @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
export function sumAfterPush(
  widths: number[],
  ends: number[],
  other: number[],
): number {
  other.push(widths.length);
  let total = 0;
  /** @invariant forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
  for (let i = 0; i < ends.length; i++) total += widths[ends[i]!]!;
  return total;
}
