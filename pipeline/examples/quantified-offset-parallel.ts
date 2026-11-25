// Shifted parallel indexing (`rich-inline.ts:496-578`, issue #397): a sub-range
// builder appends `subWidths.length` entries onto `advances` starting at `base`
// while building a 0-indexed `subExtras` whose element `subExtras[s]` matches
// `advances[base + s]`. Copying `prefix.extras[i]` into `extras[i]` and
// `subExtras[s]` into `extras[base + s]` keeps `advances[j].length <= extras[j].length`.
/**
 * @invariant this.advances.length <= this.extras.length
 * @invariant forall i in this.advances: this.advances[i] === null || this.extras[i] === null || this.advances[i].length <= this.extras[i].length
 */
export type ConcatParallel = {
  advances: (number[] | null)[];
  extras: (number[] | null)[];
};

export function appendSubRange(
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
    const at = base + s;
    if ((at & 0x7fffffff) !== at || at >= extras.length)
      throw new RangeError("index");
    extras[at] = subExtras[s] ?? null;
  }
  return { advances, extras };
}

/**
 * Shallow-copying `prefix.advances` via 0-arg `slice()` preserves its
 * quantified parallel-length invariant against `prefix.extras`.
 */
export function cloneAdvances(prefix: ConcatParallel): ConcatParallel {
  const advances = prefix.advances.slice();
  return { advances, extras: prefix.extras };
}

/**
 * Reading a shifted parallel element at `base + s - from` establishes the
 * paired inner-array length bound.
 *
 * @requires safeInteger(base) && safeInteger(from) && safeInteger(s)
 * @requires 0 <= s && s < subExtras.length
 * @requires 0 <= base + s - from && base + s - from < advances.length
 * @requires forall k in subExtras: advances[base + k - from] === null || subExtras[k] === null || advances[base + k - from].length <= subExtras[k].length
 */
export function sumShiftedPair(
  advances: (number[] | null)[],
  subExtras: (number[] | null)[],
  base: number,
  from: number,
  s: number,
): number {
  const at = base + s - from;
  const adv = advances[at];
  const ext = subExtras[s];
  if (adv === null || adv === undefined || ext === null || ext === undefined)
    return 0;
  let total = 0;
  for (let i = 0; i < adv.length; i++) {
    total += adv[i]! + ext[i]!;
  }
  return total;
}
