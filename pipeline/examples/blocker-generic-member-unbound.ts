// A method read off a host node refined to a binder bounded by Node, then
// called without its object: the member's contract holds only of a call on
// the node it is read from, so the call is refused.
import type { Node } from "typescript/unstable/ast";
export function use<N extends Node>(
  node: Node,
  test: (n: Node) => n is N,
): number {
  if (!test(node)) return 0;
  const get = node.getStart;
  return get();
}
