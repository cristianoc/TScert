// An import of a function whose loop body declares a constant holding a
// recursive arrow: its module's document binds every name the arrow reads,
// its own constant included, so the importer's read of it is not refused.
import { depth } from "@fixture/recursive-local";

export function twice(ns: readonly number[]): number {
  return depth(ns) + depth(ns);
}
