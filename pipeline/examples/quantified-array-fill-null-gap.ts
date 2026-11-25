// `new Array<number[] | null>(n).fill(null)` creates an array of length `n`
// whose every element is `null`, which vacuously establishes a guarded
// parallel-array invariant against any array of length `n`. Safe (run under Node).
/**
 * @ensures result.length === chunks.length
 * @ensures forall i in chunks: chunks[i] === null || result[i] === null || chunks[i].length <= result[i].length
 */
export function attachEmptyExtras(chunks: (number[] | null)[]): (number[] | null)[] {
  return new Array<number[] | null>(chunks.length).fill(null);
}
