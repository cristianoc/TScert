// initializer read after an in test on a compiler node's parent.
// Census functions:
// written-applications.mts#writtenApplications
import type { Node } from "typescript/unstable/ast";
export function initializer(node: Node): boolean {
  return (
    !!node.parent &&
    "initializer" in node.parent &&
    node.parent.initializer === node
  );
}
