// An exact element write of -0 into a view of each element type
// (SOURCE-CONTRACTS.md, "Stated library types"): the element holds the
// element type's conversion of -0, +0 of a Uint8Array, a Uint16Array and an
// Int32Array and -0 of a Float64Array (run under Node: `Object.is(t[0], -0)`
// is false of the three and true of the fourth). Both denote the integer 0,
// so a quantified fact whose body admits 0 holds after the write, and the
// element read back indexes `widths`; `Object.is` tells the two zeros apart
// at run time, and the verdict reads neither.

/** @requires safeInteger(k) && 0 <= k && k < items.length && widths.length > 0
 * @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function uint8(widths: number[], items: Uint8Array, k: number): number {
  const z = -0;
  items[k] = z;
  return widths[items[k]!]! + (Object.is(items[k], -0) ? 1 : 0);
}

/** @requires safeInteger(k) && 0 <= k && k < items.length && widths.length > 0
 * @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function uint16(widths: number[], items: Uint16Array, k: number): number {
  const z = -0;
  items[k] = z;
  return widths[items[k]!]! + (Object.is(items[k], -0) ? 1 : 0);
}

/** @requires safeInteger(k) && 0 <= k && k < items.length && widths.length > 0
 * @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function int32(widths: number[], items: Int32Array, k: number): number {
  const z = -0;
  items[k] = z;
  return widths[items[k]!]! + (Object.is(items[k], -0) ? 1 : 0);
}

/** @requires safeInteger(k) && 0 <= k && k < items.length && widths.length > 0
 * @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function float64(widths: number[], items: Float64Array, k: number): number {
  const z = -0;
  items[k] = z;
  return widths[items[k]!]! + (Object.is(items[k], -0) ? 1 : 0);
}
