// A read of `b` below the length of another view, `a`, across a write
// of a number field: the write keeps `i < a.length`, which bounds no read of
// `b`, and `b[i]!` past `b`'s end is `undefined` at `number`, bound to `f`
// (run under Node: `other(new Uint8Array(3), new Uint8Array(1), { at: 0 })`
// reads `undefined` at `i = 1` and returns `NaN`).

type Cursor = { at: number };

export function other(a: Uint8Array, b: Uint8Array, c: Cursor): number {
  let s = 0;
  for (let i = 0; i < a.length; i++) {
    c.at = i;
    const f = b[i]!;
    s = s + f;
  }
  return s;
}
