import * as ts from "typescript/unstable/ast";

type Parent =
  | ts.NewExpression
  | ts.CallExpression
  | ts.ExpressionWithTypeArguments
  | ts.Identifier;

export function guarded(parent: Parent, child: ts.Node): boolean {
  return (ts.isNewExpression(parent) && parent.expression === child) ||
    (ts.isCallExpression(parent) && parent.expression === child) ||
    (ts.isExpressionWithTypeArguments(parent) && parent.expression === child)
    ? true
    : false;
}

export function narrowed(
  parent: Parent,
  child: ts.Node,
): ts.Expression | undefined {
  if (
    (ts.isNewExpression(parent) && parent.expression === child) ||
    (ts.isCallExpression(parent) && parent.expression === child) ||
    (ts.isExpressionWithTypeArguments(parent) && parent.expression === child)
  ) {
    return parent.expression;
  }
  return undefined;
}
