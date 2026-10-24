// An imported overloaded function whose overload states an effect: a
// declaration's unit is certified at one signature, so the statement is
// refused where the declaration is read.
import { pick } from "@fixture/stated-overload";

export function picked(xs: number[]): number {
  return pick(xs, true);
}
