// The quantified array keeps its elements, but the free body term
// box.widths.length changes. Under Node this returns undefined at number.
/** @requires safeInteger(k) && 0 <= k && k < ends.length
 * @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < box.widths.length */
export function afterFreeTerm(ends: number[], box: {widths: number[]}, k: number): number {
  box.widths = [];
  return box.widths[ends[k]!]!;
}
