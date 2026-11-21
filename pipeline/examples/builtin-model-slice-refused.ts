// `slice()` of a dense receiver modelled as code, at its contract (ECMA-262,
// sec-array.prototype.slice; tools/array-prototype.mts):
//   { name: "slice", from: "ReadonlyArray", signature: "slice(start?: number, end?: number): T[];",
//     stated: { receiver: readonly T[] (dense), params: [], result: T[] (dense),
//       effect: footprintEffect(emptyFootprint, { fresh: true,
//         ensures: result.length === receiver.length }) } }
// It reads the length once, then defines each element at its index of a
// fresh array (ArraySpeciesCreate at the standard species). Of a dense
// receiver every index below the length is present.
/** @ensures result.length === this.length */
export function slice<T>(this: readonly T[]): Modifies<{}, Fresh<T[]>> {
  const len = this.length;
  const out: T[] = [];
  /** @invariant safeInteger(k) && 0 <= k && k <= len && safeInteger(len) && len === this.length && out.length === k */
  for (let k = 0; k < len; k++) out[k] = this[k];
  return out;
}
