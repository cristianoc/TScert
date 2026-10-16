// An imported class is a value: reading it runs nothing, and only `new` runs
// its construct-only code.
import { Counter } from "@fixture/lib";
export function leak(): null {
  const make = Counter;
  return null;
}
