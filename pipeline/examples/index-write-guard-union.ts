// A guarded write at a key typed as a union of numeric literals, or of
// `number` with one: every value the key holds is a number, so the guard's
// mask and comparison bound it exactly as a `number` key's, and the write
// lands on an element or appends (PROGRAM-TYPING.md, "Writes at a checked
// index"). The union is the `number` key's meaning, not a different rule.
export function set(xs: number[], k: 0 | 1, v: number): void {
  if ((k & 0x7fffffff) !== k || k > xs.length) throw new RangeError("index");
  xs[k] = v;
}

// A union of `number` with a literal: the same classification, the same
// guard.
export function setWide(xs: string[], k: number | 0, v: string): void {
  if ((k & 0x7fffffff) !== k || k > xs.length) throw new RangeError("index");
  xs[k] = v;
}
