// A constant bound to the object holds it too: a write through it adds the
// key to the object both hold, so the local holds the copy with the key and
// is no view lacking it at another type.
export function grow(): string {
  const o = {};
  const w: { x?: number } = o;
  w.x = 1;
  const view: { x?: string } = o;
  const v = view.x;
  return v === undefined ? "" : v.toUpperCase();
}
