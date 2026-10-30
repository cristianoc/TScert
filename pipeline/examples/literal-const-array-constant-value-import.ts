// An imported constant initialized by an array literal `as const` has the
// readonly tuple of its literals' types, which the declaration reader does
// not read: refused where it is imported.
import { pinned } from "@fixture/lib";

export function second(): 2 {
  return pinned[1];
}
