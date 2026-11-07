// A write through another parameter that may be the same object: a fact of
// `b.i` does not survive `a.i = …`, a number written where a number was. Under
// Node, `aliased(c, c, [5])` with `c = { i: 0 }` reads `xs[1]`, `undefined` at
// `number`.

type Cursor = { i: number };

/** @requires safeInteger(b.i) && 0 <= b.i && b.i < xs.length */
export function aliased(a: Cursor, b: Cursor, xs: number[]): number {
  a.i = xs.length;
  return xs[b.i]!;
}
