// A built-in iterator that is done returns `undefined`
// (`BuiltinIteratorReturn`, as `strict` reads it): a step's value is the
// element or `undefined`.
import { keysOf } from "@fixture/lib";

export function firstLength(m: Map<string, number>): number {
  const v: string | undefined = keysOf(m).next().value;
  return v === undefined ? 0 : v.length;
}
