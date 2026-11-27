// A disjunction of plain guard calls on one value reaches its last test
// along one path: each test is lowered in place and its narrowing reaches
// the branch.
// Census functions:
// fragment-support.mts#bindingScope, fragment-support.mts#runsCode,
// fragment-expressions.mts#testPosition.
import * as ts from "typescript/unstable/ast";
export function opaque(n: ts.Node): boolean {
  if (ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isFunctionDeclaration(n)) return false;
  return true;
}
