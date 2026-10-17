// An imported function is assumed at the type its declaration states, which
// states no heap effect: its body is not this unit's to certify. A `map`
// callback calling it is not preserving, `map` takes its unrestricted
// overload, and the result is sparse.
import { double } from "@fixture/lib";
export function doubled(xs: number[]): number[] {
  return xs.map((x) => double(x));
}
