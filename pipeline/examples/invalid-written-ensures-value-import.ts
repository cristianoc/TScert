import { short } from "../imports-project/false-ensures.js";
/** @requires safeInteger(count) && 0 < count */
export function read(count: number): number {
  const out = short(count);
  return out[count - 1]! + 1;
}
