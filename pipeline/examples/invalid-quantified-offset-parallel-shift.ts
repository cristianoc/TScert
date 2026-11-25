// Negative control for shifted parallel indexing (#397): writing `subExtras[s]`
// into `extras[base + s - 1]` (off-by-one shift) overwrites `extras[0]` with a
// shorter row than `advances[0]`, violating `ConcatParallel`'s invariant so
// reading `extras[0][1]` yields `undefined` / `NaN` at runtime (verified under Node).
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
  for (let s = 0; s < subWidths.length; s++) {
    const w = subWidths[s]!;
    advances.push([w]);
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
    const at = base + s - 1;
    if ((at & 0x7fffffff) !== at || at >= extras.length)
      throw new RangeError("index");
    extras[at] = subExtras[s] ?? null;
  }
  return { advances, extras };
}
