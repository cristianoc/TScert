// pretext measurement.ts: zeros and its bounded consumer.
/** @requires safeInteger(count) && 0 <= count && count <= 4294967295
 * @ensures result.length === count
 */
export function zeros(count: number): number[] {
  const out: number[] = [];
  for (let i = 0; i < count; i++) out.push(0);
  if (out.length !== count) throw new Error("length mismatch");
  return out;
}
/** @requires safeInteger(count) && 0 < count && count <= 4294967295 */
export function lastZero(count: number): number {
  const out = zeros(count);
  return out[count - 1]!;
}

/** @requires source.length < 4294967295
 * @ensures result.length === source.length + 1 */
export function flags(source: string): Uint8Array {
  const out = new Uint8Array(source.length + 1);
  return out;
}
/** @ensures result.values.length === source.length */
export function wrapped(source: string): { values: Uint8Array } {
  const values = new Uint8Array(source.length);
  return { values };
}

/** @ensures result.length === source.length */
export function defaults(source: string, ignored: boolean = false): Uint8Array {
  const out = new Uint8Array(source.length);
  return out;
}

/** @requires safeInteger(count) && 0 <= count
 * @requires ends === null || count <= ends.length
 * @ensures safeInteger(result) && 0 <= result
 * @ensures ends === null || result <= ends.length */
export function countEnds(ends: Int32Array | null, count: number): number {
  return count;
}
/** @requires forall i in xs: safeInteger(xs[i]) && 0 <= xs[i]
 * @ensures forall i in result: safeInteger(result[i]) && 0 <= result[i] */
export function nonnegative(xs: number[]): number[] {
  return xs;
}
