// A generic host node refined by a predicate needs its Node bound available
// for a method read.
// Census functions:
// type-probe.mts#nodeAt.
import type { Node } from "typescript/unstable/ast";
export function use<N extends Node>(
  node: Node,
  test: (n: Node) => n is N,
): number {
  return test(node) ? node.getStart() : 0;
}
