// A precondition naming an optional or a defaulted parameter: the clause
// reads the argument as the call passes it, `undefined` where the call
// passes none, so it states the cursor's bounds past `c === undefined`. The
// body is checked assuming the clause at its entry, before the default
// replaces an undefined argument, and each call passing the argument
// establishes it (ARITHMETIC.md, "Preconditions").
export type Cursor = { i: number };

/** @requires c === undefined || (safeInteger(c.i) && 0 <= c.i && c.i < xs.length) */
export function atOptional(xs: number[], c?: Cursor): number {
  if (c === undefined) return 0;
  return xs[c.i]!;
}

/** @requires c === undefined || (safeInteger(c.i) && 0 <= c.i) */
export function atDefault(xs: number[], c: Cursor = { i: 0 }): number {
  return c.i < xs.length ? xs[c.i]! : 0;
}

export function sum(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    const c: Cursor = { i };
    s = s + atOptional(xs, c) + atDefault(xs, c);
  }
  return s;
}
