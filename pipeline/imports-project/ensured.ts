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
