import * as helper from "@fixture/stated";

export function f(xs: number[], n: number): Modifies<{}, number> {
  return helper.drain(xs, n);
}
