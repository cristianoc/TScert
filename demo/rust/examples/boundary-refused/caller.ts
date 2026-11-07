import { scale } from "./lib.js";

// Refused: `scale` takes an i64, a bigint in JavaScript, and `x` is a number.
export function doubled(x: number): bigint {
  return scale(x, 2n);
}
