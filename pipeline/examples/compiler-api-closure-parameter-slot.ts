// A closure's assigned parameter holding a compiler node, a slot of the
// closure's activation: a host guard narrows it until the next write, as it
// narrows a function's (the front end's `assignedNames` and `hoistTarget`).
import * as ts from "typescript/unstable/ast";

export function names(n: ts.Node): string[] {
  const found: string[] = [];
  const targets = (e: ts.Node): void => {
    while (ts.isParenthesizedExpression(e)) e = e.expression;
    if (ts.isIdentifier(e)) found.push(e.text);
    else if (ts.isSpreadElement(e)) targets(e.expression);
    else if (
      ts.isBinaryExpression(e) &&
      e.operatorToken.kind === ts.SyntaxKind.EqualsToken
    )
      targets(e.left);
  };
  targets(n);
  return found;
}

export function head(n: ts.Node): ts.Node | null {
  const first = (x: ts.Node): ts.Node | null => {
    while (ts.isParenthesizedExpression(x)) x = x.expression;
    if (ts.isPropertyAccessExpression(x) && !x.questionDotToken)
      return first(x.expression) ?? x.expression;
    return null;
  };
  return first(n);
}
