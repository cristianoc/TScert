// `isLeftHandSideExpression` reads beyond the tag, so the guard table does
// not list it, and it is read at its parameters and result without its
// declared predicate (HOST-FAMILIES.md, "Guard recognition"): `n` stays a
// node where it answers `true`, which is no `LeftHandSideExpression`.
import * as ts from "typescript/unstable/ast";

export function unary(n: ts.Node): ts.LeftHandSideExpression | undefined {
  return ts.isLeftHandSideExpression(n) ? n : undefined;
}
