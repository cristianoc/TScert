// `instanceof` of an imported class whose base an ambient module declares:
// the base's constructor, whose code no module checks, may own a static
// `[Symbol.hasInstance]` its declaration does not state, which answers the
// test in place of the prototype walk.
import { OnDeclared } from "@fixture/failures-ambient-base";

export function on(x: OnDeclared | string): number {
  if (x instanceof OnDeclared) {
    return x.on;
  }
  return 0;
}
