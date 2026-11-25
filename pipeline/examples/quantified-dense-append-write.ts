// Building two parallel arrays in lockstep via dense-append element writes
// (`if (i > a.length) throw; a[i] = v`) extends both the single-array
// guarded length invariant and the parallel-array length invariant.
// Safe (run under Node).
/**
 * @requires srcAdvances.length === srcExtras.length
 * @requires forall i in srcAdvances: srcAdvances[i] === null || 1 <= srcAdvances[i].length
 * @requires forall i in srcAdvances: srcAdvances[i] === null || srcExtras[i] === null || srcAdvances[i].length <= srcExtras[i].length
 */
export function copyLockstep(
  srcAdvances: (number[] | null)[],
  srcExtras: (number[] | null)[],
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
    const ex = srcExtras[i] ?? null;
    if ((i & 0x7fffffff) !== i || i > advances.length) throw new RangeError("index");
    advances[i] = adv;
    if ((i & 0x7fffffff) !== i || i > extras.length) throw new RangeError("index");
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

/**
 * @requires forall i in src: 1 <= src[i].length
 */
export function copyNonEmpty(src: number[][]): number {
  const dst: number[][] = [];
  /**
   * @invariant safeInteger(i) && 0 <= i && dst.length === i
   * @invariant forall j in dst: 1 <= dst[j].length
   */
  for (let i = 0; i < src.length; i++) {
    const row = src[i]!;
    if ((i & 0x7fffffff) !== i || i > dst.length) throw new RangeError("index");
    dst[i] = row;
  }
  let sum = 0;
  for (let i = 0; i < dst.length; i++) {
    sum += dst[i]![0]!;
  }
  return sum;
}
