// Importers gain both the stated regional frame and the `@ensures`
// postcondition of an imported function whose module certifies them.
import {
  appendAndReset,
  normalizeStart,
  type Cursor,
} from "@fixture/stated-region-ensures";

/** @requires safeInteger(c.i) && 0 <= c.i */
function use(c: Cursor): Modifies<{}, number> {
  return c.i;
}

export function stepNext(xs: number[]): number {
  const c = { i: 0 };
  if (!normalizeStart(xs, c)) return 0;
  return xs[c.i]! + use(c);
}

export function growAndUse(xs: number[]): number {
  const c = { i: 0 };
  appendAndReset(c, xs);
  return use(c);
}
