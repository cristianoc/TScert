// `rows` may hold `bag.chunks` itself. Appending a null row can grow the
// spine matched to `widths` without adding a width. Under Node the last
// width read is undefined when `rows` and `bag.chunks` share a spine.
/** @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length */
export type ChunkBag = { chunks: (number[] | null)[] };

/** @requires bag.chunks.length === widths.length && 1 <= widths.length */
export function readLastWidth(bag: ChunkBag, rows: (number[] | null)[], widths: number[]): number {
  rows.push(null);
  return widths[bag.chunks.length - 1]!;
}
