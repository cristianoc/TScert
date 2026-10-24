// A constant a declaration file declares at a program alias of `typeof` a
// function stating an effect: the value is the environment's, whose code no
// run checks, so the statement its type reaches is refused.
import { copied } from "@fixture/stated-ambient";

export function used(xs: number[]): number[] {
  return xs.map((x) => copied(x));
}
