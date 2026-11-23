// A caller of a generic module function must establish its `@requires`
// precondition. Under Node `badCall([1])` returns `undefined`.
type Cursor = { i: number };

/** @requires safeInteger(c.i) && 0 <= c.i && c.i < xs.length */
function readAt<E>(xs: number[], c: Cursor, _e: E): number {
  return xs[c.i]!;
}

export function badCall(xs: number[]): number {
  const c = { i: -1 };
  return readAt(xs, c, true);
}
