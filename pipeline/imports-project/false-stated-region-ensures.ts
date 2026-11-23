// Functions whose stated regional frame or `@ensures` postcondition does not
// hold: their module publishes no entry for them, and a generic import with a
// body carries no uncertified postcondition.
export type Cursor = { i: number };

/** @requires safeInteger(c.i) && 0 <= c.i
 *  @ensures safeInteger(c.i) && 0 <= c.i
 *  @ensures result === false || c.i < xs.length */
export function lyingNormalize(
  xs: number[],
  c: Cursor,
): Modifies<{ "c.*": "scalar" }, boolean> {
  c.i = xs.length;
  return true;
}

/** @requires safeInteger(c.i) && 0 <= c.i
 *  @ensures safeInteger(c.i) && 0 <= c.i */
export function escapingNormalize(
  xs: number[],
  c: Cursor,
): Modifies<{ "c.*": "scalar" }, boolean> {
  xs.pop();
  c.i = 0;
  return true;
}

/** @requires safeInteger(c.i) && 0 <= c.i && c.i < xs.length
 *  @ensures safeInteger(c.i) && 0 <= c.i && c.i < xs.length */
export function lyingGeneric<E>(
  xs: number[],
  c: Cursor,
  e: E | undefined,
): number | null {
  c.i = xs.length;
  if (e === undefined) return null;
  return c.i;
}
