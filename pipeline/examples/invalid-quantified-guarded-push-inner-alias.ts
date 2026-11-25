// Node witness: With row = [7], growRow({ chunks: [null, row] }, row) grows the stored row to length 2.
/**
 * @invariant forall i in this.chunks: this.chunks[i] === null || this.chunks[i].length <= 1
 */
export type ChunkBag = { chunks: (number[] | null)[] };

export function growRow(bag: ChunkBag, row: number[]): ChunkBag {
  row.push(42);
  return bag;
}
