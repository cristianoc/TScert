// Lazy allocation of a parallel array mid-loop (`prepare.ts:559-564, 633`):
// `extras` is allocated on demand as `new Array(n).fill(null)` and written at
// index `i` only when `ex !== null`. On later iterations where `ex === null`,
// proving `advances[i].length <= extras[i].length` (vacuously, because
// `extras[i] === null`) requires knowing `extras[j] === null` on the unwritten
// suffix `i <= j < n`, which `forall j < stop` cannot express.
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
