// `!==` of two typed arrays, refused at the clause (ARITHMETIC.md, "Store
// separation"): two views are distinct objects that may share one buffer, so
// distinct views are no evidence of distinct storage.
/** @requires a !== b */
export function first(a: Uint8Array, b: Uint8Array): number {
  return a.length + b.length;
}
