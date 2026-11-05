// The standard library's `Float64Array` as pretext uses it
// (chenglou/pretext at 0d102a5c, src/measurement.ts): a record field that
// is a table or `null` or not computed yet, `new Float64Array(n).fill(NaN)`,
// an element read at a number, a table entry not asked yet being `NaN`, and
// an element write. A view's elements are any doubles, `NaN` included.
export type Measurement = {
  kanaKerning: Float64Array | null | undefined;
  size: number;
};

export function getKerning(
  measurement: Measurement,
  count: number,
): Float64Array | null {
  if (measurement.kanaKerning === undefined) {
    measurement.kanaKerning = null;
    if (count > 0)
      measurement.kanaKerning = new Float64Array(count * count).fill(NaN);
  }
  return measurement.kanaKerning;
}

export function kerningAt(
  kernings: Float64Array,
  index: number,
  measured: number,
): number {
  const kerning = kernings[index] ?? 0;
  return Number.isNaN(kerning) ? (kernings[index] = measured) : kerning;
}

export function total(kernings: Float64Array): number {
  let sum = 0;
  for (let i = 0; i < kernings.length; i++) sum += kernings[i] ?? 0;
  return sum + new Float64Array([0.5, 0.25]).subarray(1).length;
}
