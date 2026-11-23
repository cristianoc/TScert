// A generic module function keeps its `@requires`, `@ensures`, stated
// regional frame and proposed footprint across instantiation at each call.
type Cursor = { i: number };

/** @requires safeInteger(c.i) && 0 <= c.i */
function use(c: Cursor): Modifies<{}, number> {
  return c.i;
}

/** @requires safeInteger(c.i) && 0 <= c.i
 *  @ensures safeInteger(c.i) && 0 <= c.i */
function generic<E>(c: Cursor, e: E | undefined): number | null {
  c.i = 0;
  if (e === undefined) return null;
  return c.i;
}

/** @requires safeInteger(c.i) && 0 <= c.i
 *  @ensures safeInteger(c.i) && 0 <= c.i */
function genericScalar<E>(
  c: Cursor,
  e: E | undefined,
): Modifies<{ "c.*": "scalar" }, number | null> {
  c.i = 0;
  if (e === undefined) return null;
  return c.i;
}

/** @requires safeInteger(c.i) && 0 <= c.i
 *  @ensures safeInteger(c.i) && 0 <= c.i */
function nullableResult(c: Cursor, single: boolean): number | null {
  c.i = 0;
  if (single) return null;
  return c.i;
}

export function callGeneric(): number {
  const c = { i: 0 };
  generic(c, undefined);
  return use(c);
}

export function callGenericScalar(xs: number[]): number {
  if (xs.length === 0) return 0;
  const c = { i: 0 };
  genericScalar(c, undefined);
  return use(c) + xs[0]!;
}

export function callNullable(): number {
  const c = { i: 0 };
  nullableResult(c, true);
  return use(c);
}
