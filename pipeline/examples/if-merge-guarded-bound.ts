// Issue #367: a bound over a local changed on one branch of an `if` is
// retained at the merge as a disjunction with the linear path condition of
// the changing branch (`0 <= pending || start <= end`), and released past
// an exit whose condition contradicts that branch (`SINGLE-PASS.md`,
// "Loop heads").

/** @requires safeInteger(start) && safeInteger(n) && 0 <= start && start < n
 *  @ensures safeInteger(result) && 0 <= result */
export function lineEnd(
  start: number,
  n: number,
  unbroken: boolean,
  flags: number[],
): number {
  let end = start;
  let pending = -1;
  /** @invariant safeInteger(i) && safeInteger(n) && safeInteger(start) && start <= i && i <= n && 0 <= start
   *  @invariant safeInteger(end) && start <= end
   *  @invariant safeInteger(pending) && pending <= n */
  for (let i = start; i < n; i++) {
    if (flags[i] === 0) {
      pending = i;
      continue;
    }
    if (unbroken && pending >= 0) end = pending;
    if (!unbroken || pending >= 0) return 0;
    if (flags[i] === 2) end = i + 1;
  }
  return end;
}

/** @requires safeInteger(start) && safeInteger(n) && 0 <= start && start < n
 *  @ensures safeInteger(result) && 0 <= result */
export function pureLinearGuard(
  start: number,
  n: number,
  flags: number[],
): number {
  let end = start;
  let pending = -1;
  /** @invariant safeInteger(i) && safeInteger(n) && safeInteger(start) && start <= i && i <= n && 0 <= start
   *  @invariant safeInteger(end) && start <= end
   *  @invariant safeInteger(pending) && pending <= n */
  for (let i = start; i < n; i++) {
    if (flags[i] === 0) {
      pending = i;
      continue;
    }
    if (pending >= 0) end = pending;
    if (pending >= 0) return 0;
    if (flags[i] === 2) end = i + 1;
  }
  return end;
}

/** @requires safeInteger(start) && safeInteger(n) && safeInteger(limit) && 0 <= start && start < n
 *  @ensures safeInteger(result) && 0 <= result */
export function twoVarGuard(
  start: number,
  n: number,
  limit: number,
  flags: number[],
): number {
  let end = start;
  let pending = limit;
  /** @invariant safeInteger(i) && safeInteger(n) && safeInteger(start) && safeInteger(limit) && start <= i && i <= n && 0 <= start
   *  @invariant safeInteger(end) && start <= end
   *  @invariant safeInteger(pending) */
  for (let i = start; i < n; i++) {
    if (flags[i] === 0) {
      pending = i;
      continue;
    }
    if (pending < limit) end = pending;
    if (pending < limit) return 0;
    if (flags[i] === 2) end = i + 1;
  }
  return end;
}

/** @requires safeInteger(start) && safeInteger(n) && 0 <= start && start < n
 *  @ensures safeInteger(result) && 0 <= result */
export function sameConjunctionGuard(
  start: number,
  n: number,
  unbroken: boolean,
  flags: number[],
): number {
  let end = start;
  let pending = -1;
  /** @invariant safeInteger(i) && safeInteger(n) && safeInteger(start) && start <= i && i <= n && 0 <= start
   *  @invariant safeInteger(end) && start <= end
   *  @invariant safeInteger(pending) && pending <= n */
  for (let i = start; i < n; i++) {
    if (flags[i] === 0) {
      pending = i;
      continue;
    }
    if (unbroken && pending >= 0) end = pending;
    if (unbroken && pending >= 0) return 0;
    if (flags[i] === 2) end = i + 1;
  }
  return end;
}

/** @requires safeInteger(start) && safeInteger(n) && safeInteger(limit) && 0 <= start && start < n
 *  @ensures safeInteger(result) && 0 <= result */
export function linearConjunctionGuard(
  start: number,
  n: number,
  limit: number,
  flags: number[],
): number {
  let end = start;
  let pending = -1;
  /** @invariant safeInteger(i) && safeInteger(n) && safeInteger(start) && safeInteger(limit) && start <= i && i <= n && 0 <= start
   *  @invariant safeInteger(end) && start <= end
   *  @invariant safeInteger(pending) && pending <= n */
  for (let i = start; i < n; i++) {
    if (flags[i] === 0) {
      pending = i;
      continue;
    }
    if (pending >= 0 && pending < limit) end = pending;
    if (pending >= 0 && pending < limit) return 0;
    if (flags[i] === 2) end = i + 1;
  }
  return end;
}
