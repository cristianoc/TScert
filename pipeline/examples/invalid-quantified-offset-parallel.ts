// Negative control for shifted parallel indexing (#397): `appendSubRange` of
// quantified-offset-parallel.ts with every loop invariant kept and one change:
// each appended `subExtras` row is shorter than the `advances` row appended
// with it. The first loop's shifted invariant
// `advances[base + k].length <= subExtras[k].length` does not survive the two
// pushes, and under Node the result breaks `ConcatParallel`'s invariant
// (`extras[1][1]` is `undefined` where `advances[1][1]` is `0`).
/**
 * @invariant this.advances.length <= this.extras.length
 * @invariant forall i in this.advances: this.advances[i] === null || this.extras[i] === null || this.advances[i].length <= this.extras[i].length
 */
export type ConcatParallel = {
  advances: (number[] | null)[];
  extras: (number[] | null)[];
};

export function appendSubRangeShortRow(
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
    advances.push([w, 0]);
    subExtras.push([w]);
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
    const at = base + s;
    if ((at & 0x7fffffff) !== at || at >= extras.length)
      throw new RangeError("index");
    extras[at] = subExtras[s] ?? null;
  }
  return { advances, extras };
}
