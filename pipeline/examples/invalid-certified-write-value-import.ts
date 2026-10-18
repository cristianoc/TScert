// An imported function popping the array it is given is certified with a
// footprint that lets the heap change: the `map` callback calling it on the
// array being mapped is not preserving, `map` takes its unrestricted
// overload, and the result is sparse.
import { drop } from "@fixture/certified";
export function zeros(xs: number[]): number[] {
  return xs.map((x: number) => drop(xs) + x);
}
