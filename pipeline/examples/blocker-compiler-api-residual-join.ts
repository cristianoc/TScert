// Host tag refinements need compatible recursive claims when guard branches
// rejoin.
// Census functions:
// fragment-expressions.mts#letWrites, fragment-expressions.mts#localValues,
// fragment-support.mts#writtenElement.
import * as ts from "typescript/unstable/ast";
export function use(node: ts.Node): boolean {
  const parent = node.parent;
  if (
    (ts.isPrefixUnaryExpression(parent) ||
      ts.isPostfixUnaryExpression(parent)) &&
    (parent.operator === ts.SyntaxKind.PlusPlusToken ||
      parent.operator === ts.SyntaxKind.MinusMinusToken)
  )
    return true;
  return ts.isDeleteExpression(parent);
}
