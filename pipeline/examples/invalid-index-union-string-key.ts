// A read at `k.toString()` of a key that may be a string is no read at a
// number: `"toString".toString()` names the member every object inherits
// from `Object.prototype` (run under Node: `lookup({}, "toString")` returns
// a function).
export function lookup(
  cache: { [id: string]: number },
  k: string | number,
): number | undefined {
  return cache[k.toString()];
}
