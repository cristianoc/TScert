/** @ensures result.length === chunks.length
 *  @ensures forall i in chunks: result[i] === null || chunks[i] === null || chunks[i].length <= result[i].length */
export function attachNullExtras(chunks: (number[] | null)[]): (number[] | null)[] {
  return new Array<number[] | null>(chunks.length).fill(null);
}

/** @requires forall i in chunks: chunks[i] === null || 0 <= chunks[i].length
 *  @ensures result.length === chunks.length
 *  @ensures forall i in chunks: chunks[i] === null || result[i] === null || chunks[i].length <= result[i].length */
export function attachNullExtrasAfterChunkGuard(chunks: (number[] | null)[]): (number[] | null)[] {
  return new Array<number[] | null>(chunks.length).fill(null);
}
