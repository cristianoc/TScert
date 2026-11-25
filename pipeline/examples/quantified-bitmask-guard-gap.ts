// Bitmask-guarded parallel invariant (`rich-inline.ts:461-468`):
// `PRESERVED_SPACE` segments never carry `extras` (`(flags[i] & 0x7) === 2`
// implies `extras[i] === null`), so overwriting `advances[patchAt]` with a
// fresh non-empty array when `(flags[patchAt] & 0x7) === 2` preserves
// `advances[i].length <= extras[i].length`. `BodyClause.guarded` currently
// supports only nullability tags (`=== null` / `=== undefined`), not bitmask
// comparisons over a parallel `Uint8Array`. Safe (run under Node).
const KIND_BITS = 0x7;
const TEXT = 1;
const PRESERVED_SPACE = 2;

/**
 * @invariant this.flags.length === this.advances.length
 * @invariant this.advances.length === this.extras.length
 * @invariant forall i in this.advances: this.advances[i] === null || 1 <= this.advances[i].length
 * @invariant forall i in this.advances: this.advances[i] === null || this.extras[i] === null || this.advances[i].length <= this.extras[i].length
 */
export type TaggedChunks = {
  flags: Uint8Array;
  advances: (number[] | null)[];
  extras: (number[] | null)[];
};

/** @requires safeInteger(patchAt) && 0 <= patchAt && patchAt < kinds.length */
export function buildAndPatchPreservedSpace(kinds: Uint8Array, patchAt: number): TaggedChunks {
  const n = kinds.length;
  const flags = new Uint8Array(n);
  const advances: (number[] | null)[] = [];
  const extras: (number[] | null)[] = [];
  for (let i = 0; i < n; i++) {
    const k = kinds[i]! & KIND_BITS;
    flags[i] = k;
    if (k === TEXT) {
      advances.push([10, 20]);
      extras.push([1, 2]);
    } else {
      advances.push(null);
      extras.push(null);
    }
  }
  if ((flags[patchAt]! & KIND_BITS) === PRESERVED_SPACE) {
    if ((patchAt & 0x7fffffff) !== patchAt || patchAt >= advances.length) {
      throw new RangeError("index");
    }
    advances[patchAt] = [5, 5, 5];
  }
  return { flags, advances, extras };
}
