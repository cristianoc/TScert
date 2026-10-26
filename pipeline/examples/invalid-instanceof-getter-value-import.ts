// `instanceof` of an imported class whose module defines, through an alias,
// a getter for its `[Symbol.hasInstance]`: the lookup runs the getter, which
// shrinks the array `map` visits, and the result has a hole (run under
// Node).
import { Getter, saved } from "@fixture/failures-getter";

export function marked(): number[] {
  return saved.map((n) => ("x" instanceof Getter ? 0 : n));
}
