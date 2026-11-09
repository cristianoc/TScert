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
  expr: (
    e: ts.Expression,
  ) => Modifies<{ values: "any"; stores: "grow" }, number>,
  span: (n: ts.Node) => Modifies<{}, number>,
  knownLocal: (
    e: ts.Expression,
  ) => Modifies<{ values: "any"; stores: "grow" }, boolean>,
): number {
  if (!ts.isPropertyAccessExpression(node.expression))
    throw Error("expected a method call");
  if (
    node.questionDotToken ||
    node.expression.questionDotToken ||
    node.typeArguments?.length ||
    node.arguments.length === 0 ||
    node.arguments.some((arg) => ts.isSpreadElement(arg)) ||
    !knownLocal(node.expression.expression)
  )
    throw Error(
      "expected a known local function, an explicit receiver and ordinary arguments",
    );
  const receiver = node.arguments[0];
  if (receiver === undefined) throw Error("expected an explicit receiver");
  span(node);
  expr(node.expression.expression);
  return expr(receiver);
}
