// A write at a key known only at run time adds the key to the object every
// holder holds: the constant bound to it holds the copy with the key too, and
// is no view lacking it at another type.
export function grow(key: "x" | "y"): string {
  const o = {};
  const w = o;
  o[key] = 1;
  const view: { x?: string } = w;
  const v = view.x;
  return v === undefined ? "" : v.toUpperCase();
}
