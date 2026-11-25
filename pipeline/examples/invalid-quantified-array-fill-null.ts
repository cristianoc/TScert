// `new Array<number[] | null>(chunks.length).fill([])` fills every element with
// an empty array rather than `null`, so the guarded parallel-array postcondition
// is refused: reading `extras[0][1]` for `chunks = [[1, 2]]` yields `undefined`
// at `number` (run under Node).
/**
 * @ensures result.length === chunks.length
 * @ensures forall i in chunks: chunks[i] === null || result[i] === null || chunks[i].length <= result[i].length
 */
export function attachWrongFill(
  chunks: (number[] | null)[],
): (number[] | null)[] {
  return new Array<number[] | null>(chunks.length).fill([]);
}

/**
 * @requires safeInteger(i) && 0 <= i && i < chunks.length
 * @requires extras.length === chunks.length
 * @requires forall j in chunks: chunks[j] === null || extras[j] === null || chunks[j].length <= extras[j].length
 */
export function readLastExtra(
  chunks: (number[] | null)[],
  extras: (number[] | null)[],
  i: number,
): number {
  const c = chunks[i]!;
  const e = extras[i]!;
  if (c === null || e === null || c.length === 0) return 0;
  return e[c.length - 1]!;
}
