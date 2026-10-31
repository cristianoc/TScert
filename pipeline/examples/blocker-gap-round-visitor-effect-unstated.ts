// A forward-captured visitor helper states its store-preserving effect.
// Census functions:
// fragment-expressions.mts#knownLocal
// fragment-expressions.mts#localArrow
// fragment-expressions.mts#memberOf
// fragment-expressions.mts#localValues
// fragment-expressions.mts#letWrites
import * as ts from "typescript/unstable/ast";
import type { Node, Expression } from "typescript/unstable/ast";
export function letWrites(
  block: Node,
): Within<{ value: "any"; store: "grow" }, Expression[]> {
  const values: Expression[] = [];
  const visit = (n: Node): void => {
    if (ts.isBinaryExpression(n) && outermostIs(n.left, n))
      values.push(n.right);
    n.forEachChild(visit);
  };
  const outermostIs: (
    top: Node,
    n: Node,
  ) => Within<{ value: "any"; store: "keep" }, boolean> = (top, n) => {
    let at: Node = top;
    while (ts.isParenthesizedExpression(at)) at = at.expression;
    return at === n;
  };
  visit(block);
  return values;
}
