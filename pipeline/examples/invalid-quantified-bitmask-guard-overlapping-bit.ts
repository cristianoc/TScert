// A negative control for bitmask-guarded quantified clauses: the function
// breaks `TaggedChunks`'s invariant, as a run under Node shows.

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
