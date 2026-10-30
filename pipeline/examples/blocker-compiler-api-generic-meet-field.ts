// A host node refined by a predicate to a binder bounded by Node, in a run
// whose reading of Node has several arms, needs a field its arms state read
// through the meet of the binder and those arms.
// Census functions:
// type-probe.mts#nodeAt.
import type { Node, SourceFile } from "typescript/unstable/ast";
export function use<N extends Node>(
  file: SourceFile,
  node: Node,
  test: (n: Node) => n is N,
): number {
  return test(node) && node.getStart(file) === 0 ? node.end : 0;
}
