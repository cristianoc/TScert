// A typed array's element count across a write of a number field: the count
// is the number the location of the view's `[[viewLength]]` holds, a stable
// key of the view's type, a location of one value, so every step keeps a
// fact naming the count, the write of `c.at` among them, and the read below
// it after the write is accepted.

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
