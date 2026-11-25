// Negative control for shifted parallel indexing (#397): copying `subExtras[s]`
// into `extras[base + s]` when `subExtras` holds shorter rows than `advances`
// (or off-by-one shift `base + s + 1`) violates `ConcatParallel`'s invariant
// (`advances[i].length <= extras[i].length`), so indexing `extras[i][j]` reads
// `undefined` / `NaN` at runtime (verified under Node).
/**
 * @invariant this.advances.length <= this.extras.length
 * @invariant forall i in this.advances: this.advances[i] === null || this.extras[i] === null || this.advances[i].length <= this.extras[i].length
 */
export type ConcatParallel = {
  advances: (number[] | null)[];
  extras: (number[] | null)[];
};

export function appendSubRangeOffByOne(
  prefix: ConcatParallel,
  subWidths: number[],
): ConcatParallel {
  const advances: (number[] | null)[] = prefix.advances.slice();
  const base = advances.length;
  const subExtras: (number[] | null)[] = [];
  for (let s = 0; s < subWidths.length; s++) {
    const w = subWidths[s]!;
    advances.push([w, 0]);
    subExtras.push([w]);
  }
  const extras: (number[] | null)[] = new Array<number[] | null>(
    advances.length,
  ).fill(null);
  for (let i = 0; i < base; i++) {
    if ((i & 0x7fffffff) !== i || i >= extras.length)
      throw new RangeError("index");
    extras[i] = prefix.extras[i] ?? null;
  }
  for (let s = 0; s < subExtras.length; s++) {
    const at = base + s;
    if ((at & 0x7fffffff) !== at || at >= extras.length)
      throw new RangeError("index");
    extras[at] = subExtras[s] ?? null;
  }
  return { advances, extras };
}
