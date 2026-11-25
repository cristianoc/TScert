// Shifted parallel indexing (`rich-inline.ts:496-578`): a sub-range builder
// appends `subWidths.length` entries onto `advances` starting at `base` while
// building a 0-indexed `subExtras` whose element `subExtras[s]` matches
// `advances[base + s]`. Copying `subExtras[s]` into `extras[base + s]` keeps
// `advances[i].length <= extras[i].length`, relying on a shifted parallel
// invariant (`advances[base + s]` vs `subExtras[s]`) that `Bound.parallel`
// cannot currently express. Safe (run under Node).
/**
 * @invariant this.advances.length <= this.extras.length
 * @invariant forall i in this.advances: this.advances[i] === null || this.extras[i] === null || this.advances[i].length <= this.extras[i].length
 */
export type ConcatParallel = {
  advances: (number[] | null)[];
  extras: (number[] | null)[];
};

export function appendSubRange(prefix: ConcatParallel, subWidths: number[]): ConcatParallel {
  const advances: (number[] | null)[] = prefix.advances.slice();
  const base = advances.length;
  const subExtras: (number[] | null)[] = [];
  for (let s = 0; s < subWidths.length; s++) {
    const w = subWidths[s]!;
    advances.push([w]);
    subExtras.push([w, 0]);
  }
  const extras: (number[] | null)[] = new Array<number[] | null>(advances.length).fill(null);
  for (let i = 0; i < base; i++) {
    if ((i & 0x7fffffff) !== i || i >= extras.length) throw new RangeError("index");
    extras[i] = prefix.extras[i] ?? null;
  }
  for (let s = 0; s < subExtras.length; s++) {
    const at = base + s;
    if ((at & 0x7fffffff) !== at || at >= extras.length) throw new RangeError("index");
    extras[at] = subExtras[s] ?? null;
  }
  return { advances, extras };
}
