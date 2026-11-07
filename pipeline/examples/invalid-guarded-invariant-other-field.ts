// A guarded invariant freed by the null test of another field: the
// invariant `this.contexts === null || this.hyphens.length ===
// this.widths.length` states `hyphens` parallel to `widths` only where there
// are contexts, and `lastHyphen` tests `extra`, another nullable field,
// before reading `hyphens[i]!`: the test eliminates no guard, and the read is
// refused (run under Node: `lastHyphen({ widths: [1], contexts: null,
// hyphens: [], extra: [] }, 0)` reads `undefined` at `number`).

/** @invariant this.contexts === null || this.hyphens.length === this.widths.length */
export type Data = {
  widths: number[];
  contexts: number[] | null;
  hyphens: number[];
  extra: number[] | null;
};

/** @requires safeInteger(i) && 0 <= i && i < prepared.widths.length */
export function firstHyphen(prepared: Data, i: number): number {
  if (prepared.contexts !== null) return prepared.hyphens[i]!;
  return 0;
}

/** @requires safeInteger(i) && 0 <= i && i < prepared.widths.length */
export function lastHyphen(prepared: Data, i: number): number {
  if (prepared.extra !== null) return prepared.hyphens[i]!;
  return 0;
}
