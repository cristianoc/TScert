// A literal owning the key the model keeps an array's store under would be
// an array to the model's `Array.isArray` (and `in`), though JavaScript's
// says no: with a claim dropping that arm on the failed test, `h` would
// return the object as a number. The key is refused wherever a source
// spells it.
export function h(flag: boolean): number {
  const x = flag ? { "[]": "s" } : 0;
  if (Array.isArray(x)) {
    return 1;
  }
  return x;
}
