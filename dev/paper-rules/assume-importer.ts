// An importer of a module holding an unsafe assume: the prototype reads the
// assumes of the checked file alone, so the imported module is as its
// interface was established, and the importer keeps its ordinary verdict.
import { size } from "./assume-lib.js";

// Accepted.
export function twice(xs: number[]): number {
  return 2 * size(xs);
}
