// A host node refined by a predicate to a binder bounded by Node calls a method
// of the bound's one clause, bound to the node.
// Census functions:
// type-probe.mts#nodeAt.
import type { Node } from "typescript/unstable/ast";
export function use<N extends Node>(
  node: Node,
  test: (n: Node) => n is N,
): number {
  return test(node) ? node.getStart() : 0;
}
