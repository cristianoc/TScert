// A quantified fact on chunks establishes the matching invariant on the
// field of an object literal initialized with chunks.
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
