// Bitmask-guarded parallel invariant (`rich-inline.ts:461-468`):
// `PRESERVED_SPACE` segments never carry `extras` (`(flags[i] & 0x7) === 2`
// implies `extras[i] === null`), so overwriting `advances[patchAt]` with a
// fresh non-empty array when `(flags[patchAt] & 0x7) === 2` preserves
// `advances[i].length <= extras[i].length`. Safe (run under Node).
const KIND_BITS = 0x7;
const TEXT = 1;
const PRESERVED_SPACE = 2;
const EXTRA_FLAG = 0x8;

/**
 * @invariant this.flags.length === this.advances.length
 * @invariant this.advances.length === this.extras.length
 * @invariant forall i in this.advances: this.advances[i] === null || 1 <= this.advances[i].length
 * @invariant forall i in this.advances: this.advances[i] === null || this.extras[i] === null || this.advances[i].length <= this.extras[i].length
 * @invariant forall i in this.extras: (this.flags[i] & 0x7) !== 2 || this.extras[i] === null
 */
export type TaggedChunks = {
  flags: Uint8Array;
  advances: (number[] | null)[];
  extras: (number[] | null)[];
};

/** @requires safeInteger(patchAt) && 0 <= patchAt && patchAt < kinds.length */
export function buildAndPatchPreservedSpace(
  kinds: Uint8Array,
  patchAt: number,
): TaggedChunks {
  const n = kinds.length;
  const flags = new Uint8Array(n);
  const advances: (number[] | null)[] = [];
  const extras: (number[] | null)[] = [];
  /**
   * @invariant safeInteger(i) && 0 <= i && i <= flags.length && advances.length === i && extras.length === i
   * @invariant forall j in advances: advances[j] === null || 1 <= advances[j].length
   * @invariant forall j in advances: advances[j] === null || extras[j] === null || advances[j].length <= extras[j].length
   * @invariant forall j in extras: (flags[j] & 7) !== 2 || extras[j] === null
   */
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

/**
 * Setting a disjoint flag bit (`0x8`, disjoint from `0x7`) on a `TaggedChunks`
 * instance preserves `(chunks.flags[i] & 0x7) !== 2 || chunks.extras[i] === null`.
 * @requires safeInteger(patchAt) && 0 <= patchAt && patchAt < chunks.flags.length
 */
export function setExtraFlag(
  chunks: TaggedChunks,
  patchAt: number,
): TaggedChunks {
  const cur = chunks.flags[patchAt]!;
  chunks.flags[patchAt] = cur | EXTRA_FLAG;
  return chunks;
}

/**
 * Setting a disjoint flag bit (`0x8`, disjoint from `0x7`) preserves the
 * bitmask-guarded invariant across the view write so patching `advances[patchAt]`
 * when `(flags[patchAt] & 0x7) === 2` still verifies.
 * @requires safeInteger(patchAt) && 0 <= patchAt && patchAt < kinds.length
 */
export function buildSetExtraFlagAndPatch(
  kinds: Uint8Array,
  patchAt: number,
): TaggedChunks {
  const n = kinds.length;
  const flags = new Uint8Array(n);
  const advances: (number[] | null)[] = [];
  const extras: (number[] | null)[] = [];
  /**
   * @invariant safeInteger(i) && 0 <= i && i <= flags.length && advances.length === i && extras.length === i
   * @invariant forall j in advances: advances[j] === null || 1 <= advances[j].length
   * @invariant forall j in advances: advances[j] === null || extras[j] === null || advances[j].length <= extras[j].length
   * @invariant forall j in extras: (flags[j] & 7) !== 2 || extras[j] === null
   */
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
  const cur = flags[patchAt]!;
  flags[patchAt] = cur | EXTRA_FLAG;
  if ((flags[patchAt]! & KIND_BITS) === PRESERVED_SPACE) {
    if ((patchAt & 0x7fffffff) !== patchAt || patchAt >= advances.length) {
      throw new RangeError("index");
    }
    advances[patchAt] = [5, 5, 5];
  }
  return { flags, advances, extras };
}
