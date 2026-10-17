// `&` of two bigints is a bigint in JavaScript, which TypeScript accepts; the
// model states `&`, `|`, `<<`, `>>` and `>>>` on numbers alone, so the
// operation is refused.
export function mask(a: bigint, b: bigint): bigint {
  return a & b;
}
