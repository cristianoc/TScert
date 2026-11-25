// Pushing `null` or a non-empty `number[]` onto `(number[] | null)[]`
// preserves `forall i in chunks: chunks[i] === null || 1 <= chunks[i].length`;
// The inner `number[]` and outer `(number[] | null)[]` have incompatible
// writable spine contracts even when empty. A push on a row already in the
// outer array preserves its lower length bound at every occurrence.
/**
 * @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length
 */
export type ChunkBag = {
  chunks: (number[] | null)[];
};

/** @ensures forall i in result: result[i] === null || 1 <= result[i].length */
export function buildChunks(widths: number[]): (number[] | null)[] {
  const chunks: (number[] | null)[] = [];
  /** @invariant forall i in chunks: chunks[i] === null || 1 <= chunks[i].length */
  for (let i = 0; i < widths.length; i++) {
    const w = widths[i]!;
    if (w <= 0) {
      chunks.push(null);
    } else {
      const row: number[] = [];
      row.push(w);
      chunks.push(row);
    }
  }
  return chunks;
}

export function appendNonEmpty(bag: ChunkBag, row: number[], w: number): ChunkBag {
  row.push(w);
  bag.chunks.push(row);
  return bag;
}
