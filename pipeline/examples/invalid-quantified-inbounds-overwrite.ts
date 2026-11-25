// Overwriting an in-bounds element with an empty array `[]` violates the
// quantified element-length invariant `1 <= this.chunks[i].length` at `k`.
// Unsafe (run under Node: `replaceEmpty({ chunks: [[1]] }, 0).chunks[0][0]` is `undefined`).
/**
 * @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length
 */
export type ChunkList = {
  chunks: (number[] | null)[];
};

/** @requires safeInteger(k) && 0 <= k && k < list.chunks.length */
export function replaceEmpty(list: ChunkList, k: number): ChunkList {
  const empty: number[] = [];
  const chunks = list.chunks;
  if ((k & 0x7fffffff) !== k || k >= chunks.length)
    throw new RangeError("index");
  chunks[k] = empty;
  return list;
}
