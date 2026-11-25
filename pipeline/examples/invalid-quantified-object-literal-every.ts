// An array that does not satisfy ChunkBox's quantified invariant gives a
// literal that does not either: wrapOther returns `{ chunks: other }`, whose
// empty row makes lastInChunk read index -1 (`undefined` at `number` under
// Node).
/** @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length */
export type ChunkBox = {
  chunks: (number[] | null)[];
};

/** @requires forall i in chunks: chunks[i] === null || 1 <= chunks[i].length */
export function wrapOther(chunks: (number[] | null)[], other: (number[] | null)[]): ChunkBox {
  return { chunks: other };
}

/** @requires safeInteger(i) && 0 <= i && i < box.chunks.length */
export function lastInChunk(box: ChunkBox, i: number): number {
  const c = box.chunks[i];
  if (c === undefined || c === null) return 0;
  return c[c.length - 1]!;
}
