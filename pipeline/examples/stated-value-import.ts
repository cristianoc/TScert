// An imported function stating the empty footprint, whose module's run
// certifies it: a `map` callback calling it is within its statement, so the
// result is dense.
import { keep } from "@fixture/stated";

export function kept(xs: number[]): number[] {
  const r: number[] = xs.map((x) => keep(x));
  return r;
}
