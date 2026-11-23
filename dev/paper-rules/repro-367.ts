// Issue #367.
// A branch that sets `end` from `pending` is followed by an exit that every
// run of that branch takes, so past the exit `end` is as it was. The pass
// merges the two arms of the first `if` and keeps a bound over `end` only
// where both arms entail it from their linear facts; `start <= pending`
// holds only where `pending >= 0`, so the merge drops `start <= end`.

// Refused (unprovable): the loop head lacks `start <= end`.
/** @requires safeInteger(start) && safeInteger(n) && 0 <= start && start < n
 *  @ensures safeInteger(result) && 0 <= result */
export function lineEnd(start: number, n: number, unbroken: boolean, flags: number[]): number {
  let end = start;
  let pending = -1;
  /** @invariant safeInteger(i) && safeInteger(n) && safeInteger(start) && start <= i && i <= n && 0 <= start
   *  @invariant safeInteger(end) && start <= end
   *  @invariant safeInteger(pending) && pending <= n */
  for (let i = start; i < n; i++) {
    if (flags[i] === 0) { pending = i; continue; }
    if (unbroken && pending >= 0) end = pending;
    if (!unbroken || pending >= 0) return 0;
    if (flags[i] === 2) end = i + 1;
  }
  return end;
}

// `paperAssume(fact, "#N");` is the prototype's unsafe assume: the prototype
// checks it as `if (!(fact)) throw "#N";`, so past it the pass knows `fact`
// as on the branch where it holds, and names the issue in its verdict; the
// ordinary verifier reads it as a call that changes nothing.
function paperAssume(fact: boolean, issue: string): Modifies<{}, void> {}

// Accepted by the prototype, naming #367; refused by the ordinary verifier.
/** @requires safeInteger(start) && safeInteger(n) && 0 <= start && start < n
 *  @ensures safeInteger(result) && 0 <= result */
export function lineEndAssumed(start: number, n: number, unbroken: boolean, flags: number[]): number {
  let end = start;
  let pending = -1;
  /** @invariant safeInteger(i) && safeInteger(n) && safeInteger(start) && start <= i && i <= n && 0 <= start
   *  @invariant safeInteger(end) && start <= end
   *  @invariant safeInteger(pending) && pending <= n */
  for (let i = start; i < n; i++) {
    if (flags[i] === 0) { pending = i; continue; }
    if (unbroken && pending >= 0) end = pending;
    if (!unbroken || pending >= 0) return 0;
    paperAssume(start <= end, "#367"); // unsafe assume until #367
    if (flags[i] === 2) end = i + 1;
  }
  return end;
}

// Refused (unprovable): `0 <= end` does not give the invariant `start <= end`.
/** @requires safeInteger(start) && safeInteger(n) && 0 <= start && start < n
 *  @ensures safeInteger(result) && 0 <= result */
export function lineEndWeak(start: number, n: number, unbroken: boolean, flags: number[]): number {
  let end = start;
  let pending = -1;
  /** @invariant safeInteger(i) && safeInteger(n) && safeInteger(start) && start <= i && i <= n && 0 <= start
   *  @invariant safeInteger(end) && start <= end
   *  @invariant safeInteger(pending) && pending <= n */
  for (let i = start; i < n; i++) {
    if (flags[i] === 0) { pending = i; continue; }
    if (unbroken && pending >= 0) end = pending;
    if (!unbroken || pending >= 0) return 0;
    paperAssume(0 <= end, "#367"); // unsafe assume until #367
    if (flags[i] === 2) end = i + 1;
  }
  return end;
}
