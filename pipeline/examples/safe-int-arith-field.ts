// A sum known to be a safe integer stored at a field typed `SafeInt`: under
// `c.count < 100` the facts state `c.count + 1` a safe integer, so the write
// reads it at `SafeInt` (docs/drafts/integer-types.md, "The bridge": a step
// is checked at its context refined by its facts' safe integers).

type Counter = { count: SafeInt };

/** @requires 0 <= c.count && c.count < 100 */
export function bump(c: Counter): void {
  c.count = c.count + 1;
}

/** @requires 0 <= n && n < 100 */
export function next(n: SafeInt): SafeInt {
  const m = n + 1;
  return m;
}
