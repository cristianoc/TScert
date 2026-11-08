import { zeros } from "../imports-project/ensured.js";
/** @requires safeInteger(count) && 0 < count && count <= 4294967295 */
export function read(count: number): number {
  const out = zeros(count);
  return out[count - 1]!;
}
