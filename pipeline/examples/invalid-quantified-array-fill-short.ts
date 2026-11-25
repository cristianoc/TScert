// A null fill one element shorter than `chunks` leaves the last index of the
// guarded domain outside the filled array: `result[i]` is `undefined` there,
// so the clause compares `chunks[i].length` with `undefined.length`. Under
// Node, `readLastExtra([[1, 2]], attachShortExtras([[1, 2]]), 0)` throws a
// TypeError.
/**
 * @requires 1 <= chunks.length
 * @ensures forall i in chunks: chunks[i] === null || result[i] === null || chunks[i].length <= result[i].length
 */
export function attachShortExtras(
  chunks: (number[] | null)[],
): (number[] | null)[] {
  return new Array<number[] | null>(chunks.length - 1).fill(null);
}

/**
 * @requires safeInteger(i) && 0 <= i && i < chunks.length
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
