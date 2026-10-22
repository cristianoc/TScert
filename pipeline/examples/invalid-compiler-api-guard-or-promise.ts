// Under `||`, the guard answers `true` where the family guard's test
// answered `false`: the promise does not hold there (run under Node).
import * as ts from "typescript/unstable/ast";

export function isDeclaration(
  node: ts.Node,
  any: boolean,
): node is ts.FunctionDeclaration {
  return ts.isFunctionDeclaration(node) || any;
}
