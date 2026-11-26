import * as helper from "../imports-project/namespace-effect.js";

export function f(n: number): Modifies<{}, number> {
  return helper.id(n);
}
