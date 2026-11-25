// A quantified fact about an array establishes the same fact about the field
// of an object literal initialized with that array: the literal's required
// field read gives the array from the field and from the slot it was read
// into, also along a chain of literals, at a return and at a call.
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

/** @invariant this.chunks.length === this.extras.length
 *  @invariant forall i in this.chunks: this.chunks[i] === null || this.extras[i] === null || this.chunks[i].length <= this.extras[i].length */
export type PairedChunks = {
  chunks: (number[] | null)[];
  extras: (number[] | null)[];
};

/** @requires chunks.length === extras.length
 *  @requires forall i in chunks: chunks[i] === null || extras[i] === null || chunks[i].length <= extras[i].length */
export function wrapPaired(chunks: (number[] | null)[], extras: (number[] | null)[]): PairedChunks {
  return { chunks, extras };
}

/** @invariant this.extras === null || forall i in this.chunks: this.chunks[i] === null || this.extras[i] === null || this.chunks[i].length <= this.extras[i].length */
export type OptionalPairedChunks = {
  chunks: (number[] | null)[];
  extras: (number[] | null)[] | null;
};

/** @requires extras === null || forall i in chunks: chunks[i] === null || extras[i] === null || chunks[i].length <= extras[i].length */
export function wrapOptionalPaired(
  chunks: (number[] | null)[],
  extras: (number[] | null)[] | null,
): OptionalPairedChunks {
  return { chunks, extras };
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

/** @requires safeInteger(i) && 0 <= i && i < box.chunks.length */
export function lastInChunk(box: ChunkBox, i: number): number {
  const c = box.chunks[i];
  if (c === undefined || c === null) return 0;
  return c[c.length - 1]!;
}

/** @requires forall i in chunks: chunks[i] === null || 1 <= chunks[i].length
 *  @requires safeInteger(k) && 0 <= k && k < chunks.length */
export function lastOfChunks(chunks: (number[] | null)[], k: number): number {
  return lastInChunk({ chunks }, k);
}
