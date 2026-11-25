// Lazy allocation of a parallel array mid-loop (`prepare.ts:559-564, 633`) and
// general interval quantified clauses (`forall lo <= j < hi of P: ...`,
// `forall lo <= j in P: ...`) with standalone element-tag bodies (`xs[j] === null`).
// Safe (run under Node).
/**
 * @invariant this.extras === null || this.advances.length <= this.extras.length
 * @invariant forall i in this.advances: this.advances[i] === null || 1 <= this.advances[i].length
 * @invariant this.extras === null || forall i in this.advances: this.advances[i] === null || this.extras[i] === null || this.advances[i].length <= this.extras[i].length
 */
export type LazyParallel = {
  advances: (number[] | null)[];
  extras: (number[] | null)[] | null;
};

/**
 * @requires srcAdvances.length === srcExtras.length
 * @requires forall i in srcAdvances: srcAdvances[i] === null || 1 <= srcAdvances[i].length
 * @requires forall i in srcAdvances: srcAdvances[i] === null || srcExtras[i] === null || srcAdvances[i].length <= srcExtras[i].length
 */
export function buildLazyExtras(
  srcAdvances: (number[] | null)[],
  srcExtras: (number[] | null)[],
): LazyParallel {
  const n = srcAdvances.length;
  const advances: (number[] | null)[] = [];
  let extras: (number[] | null)[] | null = null;
  /**
   * @invariant safeInteger(i) && safeInteger(n) && 0 <= i && i <= n && advances.length === i
   * @invariant extras === null || extras.length === n
   * @invariant forall j in advances: advances[j] === null || 1 <= advances[j].length
   * @invariant extras === null || forall j in advances: advances[j] === null || extras[j] === null || advances[j].length <= extras[j].length
   * @invariant extras === null || forall i <= j < n of extras: extras[j] === null
   */
  for (let i = 0; i < n; i++) {
    const adv = srcAdvances[i] ?? null;
    const ex = srcExtras[i] ?? null;
    if (adv !== null && ex !== null) {
      extras ??= new Array<number[] | null>(n).fill(null);
      const store = extras;
      if ((i & 0x7fffffff) !== i || i >= store.length) throw new RangeError("index");
      store[i] = ex;
    }
    if ((i & 0x7fffffff) !== i || i > advances.length) throw new RangeError("index");
    advances[i] = adv;
  }
  return { advances, extras };
}

/**
 * @requires safeInteger(lo) && safeInteger(hi) && safeInteger(k)
 * @requires 0 <= lo && lo <= k && k < hi && hi <= xs.length
 * @requires forall lo <= j < hi of xs: safeInteger(xs[j]) && 0 <= xs[j] && xs[j] < table.length
 */
export function readInInterval(
  xs: number[],
  table: number[],
  lo: number,
  hi: number,
  k: number,
): number {
  const idx = xs[k]!;
  return table[idx]!;
}

/**
 * @requires safeInteger(lo) && safeInteger(hi) && 0 <= lo && lo + 2 <= hi && hi <= xs.length
 * @requires forall lo <= j < hi of xs: safeInteger(xs[j]) && 0 <= xs[j] && xs[j] < table.length
 * @ensures forall lo + 1 <= j < hi - 1 of xs: safeInteger(xs[j]) && 0 <= xs[j] && xs[j] < table.length
 */
export function shrinkInterval(
  xs: number[],
  table: number[],
  lo: number,
  hi: number,
): number {
  return table[xs[lo + 1]!]!;
}

/**
 * @requires safeInteger(lo) && safeInteger(k) && 0 <= lo && lo <= k && k < xs.length
 * @requires forall lo <= j in xs: safeInteger(xs[j]) && 0 <= xs[j] && xs[j] < table.length
 */
export function readLowerBounded(
  xs: number[],
  table: number[],
  lo: number,
  k: number,
): number {
  return table[xs[k]!]!;
}

/**
 * @requires safeInteger(i) && 0 <= i && i < xs.length
 * @requires forall j in xs: xs[j] === null
 * @ensures forall 0 <= j < i of xs: xs[j] === null
 * @ensures forall i + 1 <= j < xs.length of xs: xs[j] === null
 */
export function overwriteSplitsNulls(
  xs: (number[] | null)[],
  i: number,
  val: number[],
): void {
  if ((i & 0x7fffffff) !== i || i >= xs.length) throw new RangeError("index");
  xs[i] = val;
}

/**
 * @requires safeInteger(i) && 0 <= i && i <= xs.length
 * @ensures forall i <= j < i of xs: xs[j] === null
 */
export function emptyIntervalVacuous(
  xs: (number[] | null)[],
  i: number,
): (number[] | null)[] {
  return xs;
}

/**
 * @requires safeInteger(lo) && safeInteger(hi) && 0 <= lo && lo <= hi && hi <= flags.length
 * @requires forall lo <= j < hi of flags: flags[j] === false
 * @ensures forall lo <= j < hi of flags: flags[j] === false || 1 <= values[j].length
 */
export function standaloneBoolTag(
  flags: boolean[],
  values: number[][],
  lo: number,
  hi: number,
): boolean[] {
  return flags;
}
