/** @ensures result.length === chunks.length
 *  @ensures forall i in chunks: result[i] === null || chunks[i] === null || chunks[i].length <= result[i].length */
export function attachEmptyRows(chunks: (number[] | null)[]): (number[] | null)[] {
  return new Array<number[] | null>(chunks.length).fill([]);
}
