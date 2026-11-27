/** @requires safeInteger(start) && safeInteger(end) && 0 <= start && start <= end && xs.length === end - start */
export function badWrongDisequality(
  start: number,
  end: number,
  xs: Dense<number[]>,
): number {
  let state = 1;
  let count = 0;
  /** @invariant safeInteger(start) && safeInteger(end) && safeInteger(i) && safeInteger(count) && safeInteger(state) && 0 <= start && start <= i && i <= end && 0 <= count && count <= i - start
   *  @invariant i <= start || count < i - start
   *  @invariant state === 1 || count < i - start */
  for (let i = start; i < end; i++) {
    if (i > start) {
      count++;
    }
    state = 2;
  }
  if (state !== 2) {
    return xs[count]! + 1;
  }
  return 0;
}
