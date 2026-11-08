import { zeros, defaults } from "../imports-project/ensured.js";
/** @requires safeInteger(count) && 0 < count && count <= 4294967295 */
export function read(count: number): number {
  const out = zeros(count);
  return out[count - 1]!;
}

/** @ensures result.length === source.length */
export function forwarded(source: string): Uint8Array {
  const out = defaults(source);
  return out;
}
