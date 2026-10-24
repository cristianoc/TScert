// An imported function with one overload whose implementation states an
// effect: callers read the overload, and no run checks the statement, so it
// is refused where the declaration is read.
import { only } from "@fixture/stated-overload";

export function used(xs: number[]): number {
  return only(xs);
}
