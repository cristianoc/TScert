// An imported guard narrows at its call by the promise its module's check
// establishes: `isName`'s entry states its plain and promise signatures,
// both realized by its one request at the promise's goal.
import { isName } from "@fixture/guards";

export function size(x: string | number): number {
  return isName(x) ? x.length : 0;
}

export function name(x: string | number): string {
  if (!isName(x)) throw Error("not a name");
  return x;
}
