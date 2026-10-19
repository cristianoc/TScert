// Read by pipeline/test.mts on the stand-in string-tagged family:
// `isNameLoosely`'s answer depends on its option argument, so its table
// has no entry, and it narrows nothing: `n.name` is read off a unit.
import { isNameLoosely, type Unit } from "@fixture/strings";

export function name(n: Unit): string {
  return isNameLoosely(n) ? n.name : "";
}
