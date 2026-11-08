// Pretext rich-inline.ts's itemSegments/widths builder: a fact on an
// existing array across a bounded write to separately allocated storage.
/** @requires safeInteger(k) && 0 <= k && k < ends.length
 * @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
export function afterFreshWrite(widths: number[], ends: number[], k: number): number {
  const scratch: number[] = [0];
  if (k < scratch.length) scratch[k] = -1;
  return widths[ends[k]!]!;
}
