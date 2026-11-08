// The inclusive bound does not establish a strict invariant on the loop cell.
/** @requires safeInteger(start) && 0 <= start && start <= xs.length */
export function scan(xs: number[], start: number): number {
  let i = start;
  /** @invariant safeInteger(i) && 0 <= i && i < xs.length */
  while (true) {
    const value = xs[i]!;
    if (++i >= xs.length) return value + 1;
  }
}
