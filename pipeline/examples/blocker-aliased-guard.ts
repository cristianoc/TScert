// A Boolean binding holding a host guard result needs to carry its narrowing
// to the conditional branch.
// Census functions:
// fragment-statements.mts#assignedSteps.
import * as ts from "typescript/unstable/ast";
export function use(node: ts.Expression): ts.Expression {
  const assigned =
    ts.isBinaryExpression(node) &&
    node.operatorToken.kind === ts.SyntaxKind.EqualsToken;
  return assigned ? node.left : node;
}
