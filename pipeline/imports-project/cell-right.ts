// The other module of the cycle, its cell read by `left`'s initialization.
import { readLeft } from "@fixture/cell-left";
let right: number = 2;
export function readRight(): number {
  return right;
}
export function both(): number {
  return readLeft() + right;
}
