// A function a declaration file declares, stating an effect: its code is
// the environment's, which no run checks, so the statement is refused.
import { ext } from "@fixture/stated-ambient";

export function used(xs: number[]): number[] {
  return xs.map((x) => ext(x));
}
