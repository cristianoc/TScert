// An imported function stating `spines: "extend"`, which its module's run
// certifies: the statement crosses the declaration document as the closed
// footprint `{value: any, spine: extend}`, and `i < xs.length`, established
// before the call, holds after it.
import { append } from "@fixture/extended";

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function get(xs: number[], i: number): number {
  append(xs, 2);
  return xs[i]!;
}
