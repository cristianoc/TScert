// Functions with stated argument regions and `@ensures` postconditions,
// certified by their module's interface for importers to consume.
export type Cursor = { i: number };

/** @requires safeInteger(c.i) && 0 <= c.i
 *  @ensures safeInteger(c.i) && 0 <= c.i
 *  @ensures result === false || c.i < xs.length */
export function normalizeStart(
  xs: number[],
  c: Cursor,
): Modifies<{ "c.*": "scalar" }, boolean> {
  if (c.i >= xs.length) return false;
  c.i = 0;
  return true;
}

/** @requires safeInteger(c.i) && 0 <= c.i
 *  @ensures safeInteger(c.i) && 0 <= c.i */
export function appendAndReset(
  c: Cursor,
  xs: number[],
): Modifies<{ values: "any"; "xs[*]": "any" }, number> {
  c.i = 0;
  xs.push(1);
  return c.i;
}
