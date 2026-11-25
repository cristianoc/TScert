// Returning a fresh object literal `{ chunks }` when `chunks` already satisfies
// a quantified invariant (`forall i in chunks: ...`) fails to discharge the
// field-rooted postcondition `forall i in result.chunks: ...` because goal
// checking does not lower `result.chunks` through the literal's `readLink`
// (`result.chunks === chunks`). Safe (run under Node).
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
