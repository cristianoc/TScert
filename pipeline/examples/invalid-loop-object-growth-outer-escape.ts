// A key-adding write in an inner loop, which lets the object escape nowhere,
// whose outer loop binds the object to a view at another type of the key
// after it: the next outer iteration's write adds the key the view reads, and
// the write is refused (run under Node: with the rows ["y"] and ["x"], the
// view reads the number 1 at `x`).
export function aliased(rows: readonly (readonly string[])[]): string {
  const o = {};
  let view: { x?: string } = {};
  for (const row of rows) {
    for (const k of row) {
      const w: { [key: string]: number } = o;
      w[k] = 1;
    }
    view = o;
  }
  const v = view.x;
  return v === undefined ? "" : v.toUpperCase();
}
