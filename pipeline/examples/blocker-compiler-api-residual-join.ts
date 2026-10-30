// Guard branches rejoining after `parent.operator` failed `++` and `--`:
// the facts the two tests leave of the readonly `operator` exclude the
// postfix update's arm, whose operator is one of the two, so `parent`
// enters the return without it (PROGRAM-TYPING.md, field contents).
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
