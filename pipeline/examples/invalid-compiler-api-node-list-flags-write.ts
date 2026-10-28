// A node list's `transformFlags` is read as a readonly member at `number`,
// though declared writable: a write to it is refused (R1; run under Node:
// the own data property takes the write, and the list reads it back).
import type * as ts from "typescript/unstable/ast";

export function mark(node: ts.FunctionDeclaration): number {
  node.parameters.transformFlags = 1;
  return node.parameters.transformFlags;
}
