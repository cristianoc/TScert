// `new Array<number[] | null>(n).fill(null)` creates an array of length `n`
// whose every element is `null`, vacuously discharging guarded single-array,
// parallel-array, and object-literal-wrapped quantified invariants. Safe (run
// under Node).
/**
 * @ensures result.length === chunks.length
 * @ensures forall i in chunks: chunks[i] === null || result[i] === null || chunks[i].length <= result[i].length
 */
export function attachEmptyExtras(chunks: (number[] | null)[]): (number[] | null)[] {
  return new Array<number[] | null>(chunks.length).fill(null);
}

/**
 * @requires safeInteger(n) && 0 <= n
 * @ensures result.length === n
 * @ensures forall i in result: result[i] === null || 1 <= result[i].length
 */
export function makeEmptySlots(n: number): (number[] | null)[] {
  return new Array<number[] | null>(n).fill(null);
}

/**
 * @invariant this.extras.length === this.chunks.length
 * @invariant forall i in this.chunks: this.chunks[i] === null || this.extras[i] === null || this.chunks[i].length <= this.extras[i].length
 */
export type ChunkExtras = {
  chunks: (number[] | null)[];
  extras: (number[] | null)[];
};

export function attachEmptyExtrasBox(chunks: (number[] | null)[]): ChunkExtras {
  const extras = new Array<number[] | null>(chunks.length).fill(null);
  return { chunks, extras };
}
