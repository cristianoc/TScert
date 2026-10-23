// A guard of the compiler API after failed tests of `kind`: the tests leave
// a fact of the node's `kind` at the next statement, the guard reads `kind`
// through that fact and tests it, and its true edge narrows the node to the
// guarded shape through the read's link, present since `Node` states `kind`
// (the form of `written-applications.mts#literal`).
import * as ts from "typescript/unstable/ast";

export function literal(node: ts.Node): boolean {
  if (
    node.kind === ts.SyntaxKind.TrueKeyword ||
    node.kind === ts.SyntaxKind.FalseKeyword
  )
    return true;
  if (ts.isParenthesizedExpression(node)) return literal(node.expression);
  return false;
}
