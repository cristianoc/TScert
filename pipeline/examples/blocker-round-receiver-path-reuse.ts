// Census functions: fragment-expressions.mts#expr,#objectFields,#optionalChain,
// #optionalMethodCall,#wrappedMethodCall,#chainLink,#update,#template,#binary,#lambda.
import * as ts from "typescript/unstable/ast";
import type { Gate } from "../../tools/fragment-parse.mts";
export function receiver(
  this: Gate,
  node: ts.Expression,
): Modifies<{ values: "any"; stores: "grow" }, number> {
  const gate: Gate = this;
  if (ts.isCallExpression(node)) {
    if (
      ts.isPropertyAccessExpression(node.expression) &&
      node.expression.name.text === "apply" &&
      gate.libraryName(node.expression.name)
    ) {
      return 0;
    }
    if (
      ts.isPropertyAccessExpression(node.expression) &&
      ["call", "bind"].includes(node.expression.name.text) &&
      gate.libraryName(node.expression.name)
    ) {
      if (
        node.questionDotToken ||
        node.expression.questionDotToken ||
        node.typeArguments?.length ||
        node.arguments.length === 0 ||
        node.arguments.some((arg) => ts.isSpreadElement(arg)) ||
        !gate.knownLocal(node.expression.expression)
      )
        gate.refuseReceiverForm(node, "receiver");
      return node.arguments.length;
    }
  }
  return 0;
}
