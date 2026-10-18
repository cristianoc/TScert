// An imported function of a `.mts` module is a certified import as one of a
// `.ts` module is: `scaled` preserves the heap, so the `map` callback calling
// it is preserving and the result is dense.
import { scaled } from "@fixture/scaled";
export function doubled(xs: number[]): number[] {
  return xs.map((x) => scaled(x));
}
