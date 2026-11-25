// Returning a fresh object literal `{ chunks }` (or `{ chunks, extras }`, or
// a nested literal `{ inner: { chunks } }`) when the wrapped arrays already
// satisfy quantified invariants discharges the field-rooted postconditions
// (including guarded and parallel `every` clauses) by lowering goal `every`
// roots, stop terms, parallel targets, and body clauses through `HeapLinks`.
// Safe (run under Node).
/**
 * @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length
 */
export type ChunkBox = {
  chunks: (number[] | null)[];
};

/** @requires forall i in chunks: chunks[i] === null || 1 <= chunks[i].length */
export function wrapChunks(chunks: (number[] | null)[]): ChunkBox {
  return { chunks };
}

/**
 * @invariant this.extras === null || this.extras.length === this.chunks.length
 * @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length
 * @invariant this.extras === null || forall i in this.chunks: this.chunks[i] === null || this.extras[i] === null || this.chunks[i].length <= this.extras[i].length
 */
export type ParallelChunkBox = {
  chunks: (number[] | null)[];
  extras: (number[] | null)[] | null;
};

/**
 * @requires extras === null || extras.length === chunks.length
 * @requires forall i in chunks: chunks[i] === null || 1 <= chunks[i].length
 * @requires extras === null || forall i in chunks: chunks[i] === null || extras[i] === null || chunks[i].length <= extras[i].length
 */
export function wrapParallelBox(
  chunks: (number[] | null)[],
  extras: (number[] | null)[] | null,
): ParallelChunkBox {
  return { chunks, extras };
}

/**
 * @invariant forall i in this.inner.chunks: this.inner.chunks[i] === null || 1 <= this.inner.chunks[i].length
 */
export type NestedChunkBox = {
  inner: ChunkBox;
};

/** @requires forall i in chunks: chunks[i] === null || 1 <= chunks[i].length */
export function wrapNested(chunks: (number[] | null)[]): NestedChunkBox {
  const inner = { chunks };
  return { inner };
}
