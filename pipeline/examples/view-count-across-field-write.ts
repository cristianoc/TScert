// A typed array's element count across a write of a number field: the count
// is the number the location of the view's `[[viewLength]]` holds, and no
// heap invariant sets that location apart from a program object's number
// field, so the write keeps no fact naming the count and the read after it
// is refused. Safe under Node: the view's length never changes.

type Cursor = { at: number };

/** @requires safeInteger(n) && n <= flags.length */
export function marked(flags: Uint8Array, n: number, c: Cursor): number {
  let s = 0;
  for (let i = 0; i < n; i++) {
    const f = flags[i]!;
    if (f === 1) c.at = i;
    s = s + f;
  }
  return s;
}
