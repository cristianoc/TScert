// A library interface's generic method with a bounded binder, called at an
// instance within the bound.
import { flags } from "@fixture/lib";
export function pick(flag: boolean): boolean {
  return flags.either(flag, !flag);
}
