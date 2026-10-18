// A done step's value is `undefined`, which a `string` does not admit.
import { keysOf } from "@fixture/lib";

export function first(m: Map<string, number>): string {
  // @ts-expect-error: a done step's value is undefined
  return keysOf(m).next().value;
}
