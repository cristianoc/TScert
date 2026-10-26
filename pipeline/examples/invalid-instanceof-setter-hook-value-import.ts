// `instanceof` of an imported class whose module defines its
// `[Symbol.hasInstance]` (see the fixture's header): the method answers
// the test, `true` of a string, and the read after it is `undefined` (run
// under Node).
import { SetterHooked } from "@fixture/failures-setter-hook";

export function f(x: SetterHooked | string): number {
  return x instanceof SetterHooked ? x.n : 0;
}
