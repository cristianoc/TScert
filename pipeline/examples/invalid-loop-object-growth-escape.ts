// A key-adding write in a loop whose later statement binds the object to a
// view at another type of the key: the next iteration's write adds the key
// the view reads, and the write is refused (run under Node: with the keys
// "y" and "x", the view reads the number 1 at `x`).
export function aliased(keys: readonly string[]): string {
  const o = {};
  let view: { x?: string } = {};
  for (const k of keys) {
    const w: { [key: string]: number } = o;
    w[k] = 1;
    view = o;
  }
  const v = view.x;
  return v === undefined ? "" : v.toUpperCase();
}
