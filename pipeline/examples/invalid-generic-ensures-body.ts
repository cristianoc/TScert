// A generic module function whose body does not establish its `@ensures`
// postcondition is refused at its return. Under Node `read([1])` returns
// `undefined`.
type Cursor = { i: number };

/** @requires safeInteger(c.i) && 0 <= c.i && c.i < xs.length
 *  @ensures safeInteger(c.i) && 0 <= c.i && c.i < xs.length */
function badGeneric<E>(
  xs: number[],
  c: Cursor,
  e: E | undefined,
): number | null {
  c.i = xs.length;
  if (e === undefined) return null;
  return c.i;
}

export function read(xs: number[]): number {
  if (xs.length === 0) return 0;
  const c = { i: 0 };
  badGeneric(xs, c, undefined);
  return xs[c.i]!;
}
