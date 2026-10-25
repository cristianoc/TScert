// An imported function of a module whose top-level code calls a function the
// gate refuses: the module is refused as a whole, and `kept` is read at the
// type its declaration states, which states no heap effect. The `map`
// callback calling it is not preserving and the result is sparse.
import { kept } from "@fixture/partial-init";
export function incremented(xs: number[]): number[] {
  return xs.map((x) => kept(x));
}
