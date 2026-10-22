// A member path of a compiler node whose root is a `let` held in a slot
// (HOST-FAMILIES.md, "Paths rooted at a slot"), as the front end's
// `memberMayBeWritten` reads an assignment's target after unwrapping its
// parentheses: a guard of the path refines the read it made until the
// root's next write, past a call where every member is stable.
import * as ts from "typescript/unstable/ast";

export function namesOther(n: ts.Expression, member: string): boolean {
  let target: ts.Expression = n;
  while (ts.isParenthesizedExpression(target)) target = target.expression;
  return (
    ts.isElementAccessExpression(target) &&
    !(
      ts.isStringLiteral(target.argumentExpression) &&
      target.argumentExpression.text !== member
    )
  );
}

export function keyAfterCall(n: ts.Expression, log: () => void): string {
  let target: ts.Expression = n;
  while (ts.isParenthesizedExpression(target)) target = target.expression;
  if (
    !ts.isElementAccessExpression(target) ||
    !ts.isStringLiteral(target.argumentExpression)
  )
    return "";
  log();
  return target.argumentExpression.text;
}
