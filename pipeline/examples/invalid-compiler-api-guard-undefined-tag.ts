// The compiler API's description admits no tag guard's behaviour on
// `undefined` (HOST-FAMILIES.md, "Undefined arguments"), so a tag guard's
// argument that may be `undefined` is refused at the domain obligation,
// which TypeScript refuses too. Under Node, `additive(undefined)` returns
// `false`.
import * as ts from "typescript/unstable/ast";

export function additive(op: ts.SyntaxKind | undefined): boolean {
  return ts.isAdditiveOperator(op);
}
