/** @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length */
export type ChunkBox = {
  chunks: (number[] | null)[];
};

/** @requires forall i in chunks: chunks[i] === null || 1 <= chunks[i].length */
export function wrapOther(chunks: (number[] | null)[], other: (number[] | null)[]): ChunkBox {
  return { chunks: other };
}
