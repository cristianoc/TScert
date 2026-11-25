// Negative controls for bitmask-guarded quantified clauses: each function
// breaks `TaggedChunks`'s invariant and produces `undefined`/`NaN` under Node.
const KIND_BITS = 0x7;
const TEXT = 1;
const PRESERVED_SPACE = 2;

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

/**
 * Patching on `TEXT` (1) instead of `PRESERVED_SPACE` (2) overwrites
 * `advances[patchAt]` with length 3 while `extras[patchAt]` has length 2.
 * @requires safeInteger(patchAt) && 0 <= patchAt && patchAt < kinds.length
 */
export function patchOnTextTag(
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
  if ((flags[patchAt]! & KIND_BITS) === TEXT) {
    if ((patchAt & 0x7fffffff) !== patchAt || patchAt >= advances.length) {
      throw new RangeError("index");
    }
    advances[patchAt] = [5, 5, 5];
  }
  return { flags, advances, extras };
}

/**
 * Guarding with a narrower mask (`0x3` instead of `0x7`) matches tag `6`,
 * which carries a 2-element `extras` entry, breaking `advances[i].length <= extras[i].length`.
 * @requires safeInteger(patchAt) && 0 <= patchAt && patchAt < kinds.length
 */
export function patchWithWrongMask(
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
    if (k === 6) {
      advances.push([10, 20]);
      extras.push([1, 2]);
    } else {
      advances.push(null);
      extras.push(null);
    }
  }
  if ((flags[patchAt]! & 0x3) === PRESERVED_SPACE) {
    if ((patchAt & 0x7fffffff) !== patchAt || patchAt >= advances.length) {
      throw new RangeError("index");
    }
    advances[patchAt] = [5, 5, 5];
  }
  return { flags, advances, extras };
}

/**
 * Setting a bit overlapping `KIND_BITS` (`0x2` overlaps `0x7`) flips a tag-0
 * entry with non-null `extras` to `PRESERVED_SPACE` (2), breaking the invariant.
 * @requires safeInteger(patchAt) && 0 <= patchAt && patchAt < chunks.flags.length
 */
export function setOverlappingBit(
  chunks: TaggedChunks,
  patchAt: number,
): TaggedChunks {
  const cur = chunks.flags[patchAt]!;
  chunks.flags[patchAt] = cur | 0x2;
  return chunks;
}
