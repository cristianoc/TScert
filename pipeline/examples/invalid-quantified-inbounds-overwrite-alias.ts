// Overwriting an in-bounds element through an unseparated parameter array that
// may alias `list.chunks` invalidates `list`'s quantified element-length invariant.
// Unsafe (run under Node: `const c = [[1]]; overwriteAliased({ chunks: c }, c, 0).chunks[0][0]` is `undefined`).
/**
 * @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length
 */
export type ChunkList = {
  chunks: (number[] | null)[];
};

/** @requires safeInteger(k) && 0 <= k && k < alias.length */
export function overwriteAliased(
  list: ChunkList,
  alias: (number[] | null)[],
  k: number,
): ChunkList {
  const empty: number[] = [];
  if ((k & 0x7fffffff) !== k || k >= alias.length)
    throw new RangeError("index");
  alias[k] = empty;
  return list;
}
