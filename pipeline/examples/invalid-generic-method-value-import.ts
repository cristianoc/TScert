// A generic method's instance returns what the instance names: picking between
// Booleans gives a Boolean, not a number.
import { chooser } from "@fixture/lib";
export function wrong(flag: boolean): number {
  return chooser.pick(flag, flag);
}
