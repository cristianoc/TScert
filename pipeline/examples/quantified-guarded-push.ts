// Pushing `null` or a non-empty `number[]` onto `(number[] | null)[]`
// preserves `forall i in chunks: chunks[i] === null || 1 <= chunks[i].length`;
// pushing onto an inner `number[]` cannot alias the outer `(number[] | null)[]`
// spine because their element types are disjoint. Safe (run under Node).
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

export function appendNonEmpty(
  bag: ChunkBag,
  row: number[],
  w: number,
): ChunkBag {
  row.push(w);
  bag.chunks.push(row);
  return bag;
}
