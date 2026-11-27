const START_STATE = 1;
const CLUSTER_END = 0x80;

/** @requires safeInteger(start) && safeInteger(end) && 0 <= start && start <= end
 *  @ensures safeInteger(result) && 0 <= result && result <= end - start */
export function countClustersLiteral(
  start: number,
  end: number,
  flags: readonly number[],
): number {
  let state = 1;
  let count = 0;
  /** @invariant safeInteger(start) && safeInteger(end) && safeInteger(i) && safeInteger(count) && safeInteger(state) && 0 <= start && start <= i && i <= end && 0 <= count && count <= i - start
   *  @invariant i <= start || count < i - start
   *  @invariant state === 1 || count < i - start */
  for (let i = start; i < end; i++) {
    const f = i < flags.length ? flags[i] : 2;
    if (f !== undefined) {
      if (i > start && (f & CLUSTER_END) !== 0) {
        count++;
      }
      state = f & ~CLUSTER_END;
    }
  }
  if (state !== 1) {
    count++;
  }
  return count;
}

/** @requires safeInteger(start) && safeInteger(end) && 0 <= start && start <= end
 *  @ensures safeInteger(result) && 0 <= result && result <= end - start */
export function countClustersConst(start: number, end: number): number {
  let state = START_STATE;
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
  if (state !== START_STATE) {
    count++;
  }
  return count;
}

/** @requires safeInteger(start) && safeInteger(end) && 0 <= start && start <= end
 *  @ensures safeInteger(result) && 0 <= result && result <= end - start */
export function countClustersConstCross(start: number, end: number): number {
  let state = START_STATE;
  let count = 0;
  /** @invariant safeInteger(start) && safeInteger(end) && safeInteger(i) && safeInteger(count) && safeInteger(state) && 0 <= start && start <= i && i <= end && 0 <= count && count <= i - start
   *  @invariant i <= start || count < i - start
   *  @invariant state === START_STATE || count < i - start */
  for (let i = start; i < end; i++) {
    if (i > start) {
      count++;
    }
    state = 2;
  }
  if (state !== 1) {
    count++;
  }
  return count;
}

/** @requires safeInteger(x) && 0 <= x && x < xs.length */
function readChecked(xs: Dense<number[]>, x: number): number {
  return xs[x]!;
}

/** @requires safeInteger(x) && 0 <= x && (state === 1 || x < xs.length) */
export function readNonContiguousUnion(
  state: 0 | 2,
  xs: Dense<number[]>,
  x: number,
): number {
  return readChecked(xs, x);
}

/** @requires safeInteger(x) && 0 <= x && (state <= 1 || x < xs.length) */
export function readNarrowedLiteralUnion(
  state: 1 | 2,
  xs: Dense<number[]>,
  x: number,
): number {
  if (state !== 1) {
    return readChecked(xs, x);
  }
  return 0;
}
