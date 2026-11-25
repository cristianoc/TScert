// Returning `{ chunks }` when `chunks` does not satisfy `ChunkBox`'s
// quantified invariant is refused: wrapping `[[]]` produces a `ChunkBox` whose
// `lastInChunk` reads index `-1` (`undefined` at `number`, run under Node).
/**
 * @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length
 */
export type ChunkBox = {
  chunks: (number[] | null)[];
};

export function wrapUnchecked(chunks: (number[] | null)[]): ChunkBox {
  return { chunks };
}

/** @requires safeInteger(i) && 0 <= i && i < box.chunks.length */
export function lastInChunk(box: ChunkBox, i: number): number {
  const c = box.chunks[i]!;
  if (c === null) return 0;
  return c[c.length - 1]!;
}
