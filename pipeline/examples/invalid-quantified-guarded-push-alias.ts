// Pushing an empty `number[]` onto an unseparated `(number[] | null)[]`
// parameter that may alias `bag.chunks` violates `ChunkBag`'s invariant: the
// two arrays share the same element type so type-disjoint spine apartness does
// not separate them. Unsafe (run under Node: passing `other === bag.chunks`
// appends `[]`, so `out.chunks[1][0]` is `undefined` at `number`).

/**
 * @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length
 */
export type ChunkBag = {
  chunks: (number[] | null)[];
};

export function pushAliasedChunks(
  bag: ChunkBag,
  other: (number[] | null)[],
): ChunkBag {
  other.push([]);
  return bag;
}
