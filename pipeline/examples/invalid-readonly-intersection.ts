// A readonly view grants no write: the object's location may be under a
// narrower contract, `readonly a: 1`, which a write of `2` through a writable
// alias would break. TypeScript accepts it, as readonly does not affect
// assignability.
export function writable(v: { readonly a: number } & { readonly b: number }): {
  a: number;
  b: number;
} {
  return v;
}
