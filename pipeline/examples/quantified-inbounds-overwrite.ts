// Overwriting an in-bounds element of an ordinary array (`chunks[k] = next`,
// `chunks[k] = null`, or a guarded nullable array) keeps the quantified
// invariant on all other indices (`i !== k`), because an ordinary JS array's
// element cells are distinct (`listT`), and checks the body clause at `k`.
// Safe (run under Node).
/**
 * @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length
 */
export type ChunkList = {
  chunks: (number[] | null)[];
};

/** @requires safeInteger(k) && 0 <= k && k < list.chunks.length */
export function replaceChunk(list: ChunkList, k: number): ChunkList {
  const next: number[] = [42];
  const chunks = list.chunks;
  if ((k & 0x7fffffff) !== k || k >= chunks.length)
    throw new RangeError("index");
  chunks[k] = next;
  return list;
}

/** @requires safeInteger(k) && 0 <= k && k < list.chunks.length */
export function clearChunk(list: ChunkList, k: number): ChunkList {
  const chunks = list.chunks;
  if ((k & 0x7fffffff) !== k || k >= chunks.length)
    throw new RangeError("index");
  chunks[k] = null;
  return list;
}

/**
 * @requires safeInteger(k) && 0 <= k && k < list.chunks.length
 * @requires next === null || 1 <= next.length
 */
export function replaceChunkNullable(
  list: ChunkList,
  k: number,
  next: number[] | null,
): ChunkList {
  const chunks = list.chunks;
  if ((k & 0x7fffffff) !== k || k >= chunks.length)
    throw new RangeError("index");
  chunks[k] = next;
  return list;
}
