// `new Array<T>(n).fill(v)` modelled as code, at its contracts (ECMA-262,
// sec-array-len and sec-array.prototype.fill; tools/intrinsics.mts):
//   %ArrayLength%: (n: number) => number, ensures safeInteger(result),
//     0 <= result <= 2^32 - 1, result === n; a RangeError where n is no array length
//   %ArrayFilled%: <T>(n: number, v: T) => T[] (dense),
//     footprintEffect(emptyFootprint, { fresh: true, ensures: result.length === n })
// The construct checks the length (a RangeError where ToUint32(n) is not n),
// then defines each index below it as `v` on an array no code reached before.
/** @ensures safeInteger(n) && result.length === n */
export function filled<T>(n: number, v: T): Modifies<{}, Fresh<T[]>> {
  if (!Number.isSafeInteger(n) || n < 0 || n > 4294967295) throw new RangeError("Invalid array length");
  const out: T[] = [];
  /** @invariant safeInteger(k) && 0 <= k && k <= n && n <= 4294967295 && safeInteger(n) && out.length === k */
  for (let k = 0; k < n; k++) out[k] = v;
  return out;
}
