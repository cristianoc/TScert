// Census functions:
// fragment-expressions.mts#expr
// fragment-expressions.mts#objectFields
// fragment-expressions.mts#optionalChain
// fragment-expressions.mts#optionalMethodCall
// fragment-expressions.mts#wrappedMethodCall
// fragment-expressions.mts#chainLink
// fragment-expressions.mts#update
// fragment-expressions.mts#template
// fragment-expressions.mts#binary
// fragment-expressions.mts#lambda
import * as ts from "typescript/unstable/ast";
export function receiver(
  node: ts.CallExpression,
  expr: (e: ts.Expression) => number,
): number {
  return expr(node.arguments[0]);
}
