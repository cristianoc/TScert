// `ts.isTypeNode` accepts ExpressionWithTypeArguments (kind 234), whose
// declaration extends MemberExpressionBase and no TypeNodeBase: its true edge
// holds a node outside TypeNode, so returning it at TypeNode is refused.
// Census functions:
// declaration-graph.mts#computedAt, declaration-graph.mts#typeNodeAt.
import * as ts from "typescript/unstable/ast";
export function use(node: ts.Node): ts.TypeNode | null {
  return ts.isTypeNode(node) ? node : null;
}
