// `instanceof` of an imported class whose module defines its
// `[Symbol.hasInstance]` (see the fixture's header): the method answers
// the test, `true` of a string, and the read after it is `undefined` (run
// under Node).
import { BaseHooked } from "@fixture/failures-heritage-hook";

export function f(x: BaseHooked | string): number {
  return x instanceof BaseHooked ? x.n : 0;
}
