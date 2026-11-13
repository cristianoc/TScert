// An importer reading the two-state postcondition of `measure` at its
// established entry: after `measure(lists, 10)` the list is 10 longer than
// just before the call, so its last element is present.
import { measure, type Lists } from "../imports-project/two-state.js";

/** @requires 0 <= lists.widths.length && lists.widths.length <= 1000 */
export function last(lists: Lists): number {
  measure(lists, 10);
  return lists.widths[lists.widths.length - 1]!;
}
