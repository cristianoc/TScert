// A library interface's generic methods, called at the instances their calls
// name: the method's type is a scheme, and each call is below one instance.
import { chooser, type Cell } from "@fixture/lib";
export function choose(flag: boolean): boolean {
  return chooser.pick(flag, !flag);
}
export function relabel(c: Cell<number>, s: string): string {
  return c.with(s).value;
}
