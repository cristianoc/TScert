// `isTypeNode` also accepts `ExpressionWithTypeArguments` (kind 234), which
// `TypeNode` does not declare: read from its entry, its `true` edge's node
// is no `TypeNode`, refused at the return. Under Node, on the heritage
// clause of `class A extends B<C> {}`, it returns the node of kind 234.
import * as ts from "typescript/unstable/ast";

export function asTypeNode(node: ts.Node): ts.TypeNode | null {
  return ts.isTypeNode(node) ? node : null;
}
