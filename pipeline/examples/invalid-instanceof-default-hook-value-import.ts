// `instanceof` of an imported class whose module defines its
// `[Symbol.hasInstance]` (see the fixture's header): the method answers
// the test, `true` of a string, and the read after it is `undefined` (run
// under Node).
import { DefaultHooked } from "@fixture/failures-default-hook";

export function f(x: DefaultHooked | string): number {
  return x instanceof DefaultHooked ? x.n : 0;
}
