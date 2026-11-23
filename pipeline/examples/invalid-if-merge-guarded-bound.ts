// Negative control for #367: the second `if` (`pending > 0`) does not
// exclude the changing branch (`pending >= 0`) when `pending === 0`.
// With `start = 1`, `n = 2`, `unbroken = true`, `flags = [10, 1, 20]`,
// `end` becomes `0 < start`, and `flags[end - start]` reads `flags[-1]`
// (`undefined` at `number`, returning `NaN` under Node).

/** @requires safeInteger(start) && safeInteger(n) && 0 <= start && start < n && n < flags.length */
export function lineEndMismatch(
  start: number,
  n: number,
  unbroken: boolean,
  flags: number[],
): number {
  let end = start;
  let pending = 0;
  /** @invariant safeInteger(i) && safeInteger(n) && safeInteger(start) && start <= i && i <= n && 0 <= start && n < flags.length
   *  @invariant safeInteger(end) && start <= end && end <= n
   *  @invariant safeInteger(pending) && pending <= n */
  for (let i = start; i < n; i++) {
    if (flags[i] === 0) {
      pending = i;
      continue;
    }
    if (unbroken && pending >= 0) end = pending;
    if (!unbroken || pending > 0) return 0;
    if (flags[i] === 2) end = i + 1;
  }
  return flags[end - start]! + 1;
}
