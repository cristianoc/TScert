// pretext measurement.ts: zeros. Exact push-loop length is a proof gap.
/** @requires safeInteger(count) && 0 <= count && count <= 4294967295
 * @ensures result.length === count */
export function zeros(count: number): number[] {
  const out: number[] = [];
  for (let i = 0; i < count; i++) out.push(0);
  return out;
}
