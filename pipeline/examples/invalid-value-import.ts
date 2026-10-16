// An imported function's result is its declared type, not another.
import { double } from "@fixture/lib";
export function wrong(x: number): boolean {
  return double(x);
}
