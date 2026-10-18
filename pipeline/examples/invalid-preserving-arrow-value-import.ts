// An imported constant arrow is read at its annotations, which state no heap
// effect: `shrink` pops the array `map` visits. The callback calling it is
// not preserving, `map` takes its unrestricted overload, and the result is
// sparse (run under Node: a hole).
import { shrink } from "@fixture/lib";

export function shrunk(xs: number[]): number[] {
  return xs.map((x) => shrink(xs) + x);
}
