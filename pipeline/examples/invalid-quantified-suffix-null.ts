// Negative control for issue #396: allocating `extras` filled with `[]`
// instead of `null` leaves unwritten suffix entries non-null and empty,
// violating `LazyParallel`'s paired length bound (`advances[i].length <= extras[i].length`).
// Unsafe under Node: `buildLazyExtrasWrongFill([[1, 2], [3, 4]], [[10, 20], null])`
// produces `advances[1].length === 2 > extras[1].length === 0`.
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
export function buildLazyExtrasWrongFill(
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
      extras ??= new Array<number[] | null>(n).fill([]);
      const store = extras;
      if ((i & 0x7fffffff) !== i || i >= store.length) throw new RangeError("index");
      store[i] = ex;
    }
    if ((i & 0x7fffffff) !== i || i > advances.length) throw new RangeError("index");
    advances[i] = adv;
  }
  return { advances, extras };
}
