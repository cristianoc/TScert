// Overwriting an in-bounds element of an ordinary array (`chunks[k] = next`)
// with a value satisfying the quantified invariant (`1 <= next.length`) keeps
// the quantified invariant on all other indices (`i !== k`), because an
// ordinary JS array's element cells are distinct. Safe (run under Node).
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
  if ((k & 0x7fffffff) !== k || k >= chunks.length) throw new RangeError("index");
  chunks[k] = next;
  return list;
}
