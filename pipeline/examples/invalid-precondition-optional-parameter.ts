// A call outside an optional parameter's precondition: `atOptional(xs, c)`
// with `c.i` at the array's length reads past the end, so `last([1, 2])`
// returns `undefined` as a `number` (run under Node).
export type Cursor = { i: number };

/** @requires c === undefined || (safeInteger(c.i) && 0 <= c.i && c.i < xs.length) */
export function atOptional(xs: number[], c?: Cursor): number {
  if (c === undefined) return 0;
  return xs[c.i]!;
}

export function last(xs: number[]): number {
  const c: Cursor = { i: xs.length };
  return atOptional(xs, c);
}
