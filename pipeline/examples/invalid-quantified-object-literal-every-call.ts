// A call passing `{ chunks: other }` where ChunkBox is required: `other` does
// not satisfy ChunkBox's quantified invariant, so the call's precondition does
// not hold, and lastInChunk reads index -1 of the empty row (`undefined` at
// `number` under Node).
/** @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length */
export type ChunkBox = {
  chunks: (number[] | null)[];
};

/** @requires safeInteger(i) && 0 <= i && i < box.chunks.length */
export function lastInChunk(box: ChunkBox, i: number): number {
  const c = box.chunks[i];
  if (c === undefined || c === null) return 0;
  return c[c.length - 1]!;
}

/** @requires forall i in chunks: chunks[i] === null || 1 <= chunks[i].length
 *  @requires safeInteger(k) && 0 <= k && k < other.length */
export function lastOfOther(chunks: (number[] | null)[], other: (number[] | null)[], k: number): number {
  return lastInChunk({ chunks: other }, k);
}
