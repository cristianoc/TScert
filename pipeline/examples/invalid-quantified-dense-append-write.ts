// Dense-append element write placing an empty array into `extras` violates the
// parallel length invariant `advances[j].length <= extras[j].length`.
// Unsafe (run under Node: `copyLockstepShorterExtra([[5, 6]])` returns `NaN`).
/**
 * @requires forall i in srcAdvances: srcAdvances[i] === null || 1 <= srcAdvances[i].length
 */
export function copyLockstepShorterExtra(
  srcAdvances: (number[] | null)[],
): number {
  const advances: (number[] | null)[] = [];
  const extras: (number[] | null)[] = [];
  /**
   * @invariant safeInteger(i) && 0 <= i && i <= srcAdvances.length && advances.length === i && extras.length === i
   * @invariant forall j in advances: advances[j] === null || 1 <= advances[j].length
   * @invariant forall j in advances: advances[j] === null || extras[j] === null || advances[j].length <= extras[j].length
   */
  for (let i = 0; i < srcAdvances.length; i++) {
    const adv = srcAdvances[i] ?? null;
    const ex: number[] = [];
    if ((i & 0x7fffffff) !== i || i > advances.length)
      throw new RangeError("index");
    advances[i] = adv;
    if ((i & 0x7fffffff) !== i || i > extras.length)
      throw new RangeError("index");
    extras[i] = ex;
  }
  let sum = 0;
  for (let i = 0; i < advances.length; i++) {
    const row = advances[i];
    if (row === undefined || row === null) continue;
    const ex = extras[i] ?? null;
    sum += row[0]! + (ex === null ? 0 : ex[0]!);
  }
  return sum;
}
