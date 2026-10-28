// A host value's family states its keys: an `in` test on a node finds the
// package's internal `view`, which no member states, and the read stays
// refused, though at `unknown` it would expose the package's mutable heap.
import type { Node } from "typescript/unstable/ast";
export function internal(node: Node): unknown {
  return "view" in node ? node.view : undefined;
}
