// Negative control for shifted parallel indexing (#397): `appendSubRange` of
// quantified-offset-parallel.ts with every loop invariant kept and one change:
// the last loop writes `subExtras[s]` into `extras[base + s - 1]` instead of
// `extras[base + s]`. The copy pairs `subExtras[s]` with `advances[base + s - 1]`,
// which the shifted invariant does not bound, and under Node a prefix row
// longer than the appended one is overwritten by it (`extras[0][2]` is
// `undefined` where `advances[0][2]` is `3`).
/**
 * @invariant this.advances.length <= this.extras.length
 * @invariant forall i in this.advances: this.advances[i] === null || this.extras[i] === null || this.advances[i].length <= this.extras[i].length
 */
export type ConcatParallel = {
  advances: (number[] | null)[];
  extras: (number[] | null)[];
};

export function appendSubRangeWrongShift(
  prefix: ConcatParallel,
  subWidths: number[],
): ConcatParallel {
  const advances: (number[] | null)[] = prefix.advances.slice();
  const base = advances.length;
  const subExtras: (number[] | null)[] = [];
  /**
   * @invariant safeInteger(base) && safeInteger(s) && 0 <= base && base <= prefix.extras.length && 0 <= s
   * @invariant subExtras.length === s
   * @invariant advances.length === base + s
   * @invariant forall i < base of advances: advances[i] === null || prefix.extras[i] === null || advances[i].length <= prefix.extras[i].length
   * @invariant forall k in subExtras: advances[base + k] === null || subExtras[k] === null || advances[base + k].length <= subExtras[k].length
   */
  for (let s = 0; s < subWidths.length; s++) {
    const w = subWidths[s]!;
    advances.push([w]);
    subExtras.push([w, 0]);
  }
  const extras: (number[] | null)[] = new Array<number[] | null>(
    advances.length,
  ).fill(null);
  /**
   * @invariant safeInteger(base) && safeInteger(i) && 0 <= i && i <= base && base <= prefix.extras.length
   * @invariant forall j < base of advances: advances[j] === null || prefix.extras[j] === null || advances[j].length <= prefix.extras[j].length
   * @invariant forall k in subExtras: advances[base + k] === null || subExtras[k] === null || advances[base + k].length <= subExtras[k].length
   * @invariant forall j in advances: advances[j] === null || extras[j] === null || advances[j].length <= extras[j].length
   */
  for (let i = 0; i < base; i++) {
    if ((i & 0x7fffffff) !== i || i >= extras.length)
      throw new RangeError("index");
    extras[i] = prefix.extras[i] ?? null;
  }
  /**
   * @invariant safeInteger(base) && safeInteger(s) && 0 <= base && 0 <= s && s <= subExtras.length
   * @invariant forall k in subExtras: advances[base + k] === null || subExtras[k] === null || advances[base + k].length <= subExtras[k].length
   * @invariant forall j in advances: advances[j] === null || extras[j] === null || advances[j].length <= extras[j].length
   */
  for (let s = 0; s < subExtras.length; s++) {
    const at = base + s - 1;
    if ((at & 0x7fffffff) !== at || at >= extras.length)
      throw new RangeError("index");
    extras[at] = subExtras[s] ?? null;
  }
  return { advances, extras };
}
