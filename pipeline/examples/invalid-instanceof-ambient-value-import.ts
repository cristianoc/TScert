// `instanceof` of a class an ambient module declares: no body is checked,
// and the name may hold any constructor at run time.
import { Declared } from "@fixture/failures-ambient";

export function declared(x: unknown): boolean {
  return x instanceof Declared;
}
