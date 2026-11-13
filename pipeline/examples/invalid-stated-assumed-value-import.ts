// An imported function whose statement its own module's run refuses (it
// pops the array it is handed): no interface entry establishes the
// statement, so the importer reads it at the ordinary effect, and the
// `map` callback calling it is within no footprint: the result may be
// sparse. Under Node `drained([1, 2, 3])` has no element at 2.
import { drain } from "@fixture/stated";

export function drained(xs: number[]): number[] {
  const r: number[] = xs.map((x) => drain(xs, x));
  return r;
}
