// Importing `right` first evaluates `left` before `right`'s body (run under
// Node: `left`'s call of `readRight` reads `right`'s cell uninitialized and
// throws a ReferenceError). Each unit reads its cells through checked
// accesses, so the model states the throw: every unit verifies.
import { both } from "@fixture/cell-right";

export function total(): number {
  return both();
}
