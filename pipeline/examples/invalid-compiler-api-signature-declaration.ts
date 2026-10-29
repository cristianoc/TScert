// A resolved signature's `declaration` is a `NodeHandle` or absent: the
// signature TypeScript resolves at a binary expression has none, which `!`
// does not rule out (run under Node).
import type { Node } from "typescript/unstable/ast";
import type { Checker, NodeHandle } from "typescript/unstable/sync";

export function wrong(
  checker: Checker,
  node: Node,
  otherwise: NodeHandle,
): NodeHandle {
  const signature = checker.getResolvedSignature(node);
  return signature === undefined ? otherwise : signature.declaration!;
}
