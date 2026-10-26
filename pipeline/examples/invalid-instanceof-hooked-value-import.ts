// `instanceof` of an imported class whose module replaces its prototype by
// an object holding a `[Symbol.hasInstance]` method: the method answers the
// test, `true` of a string, and the read after it is `undefined` (run under
// Node).
import { Hooked } from "@fixture/failures-hooked";

export function f(x: Hooked | string): number {
  return x instanceof Hooked ? x.n : 0;
}
