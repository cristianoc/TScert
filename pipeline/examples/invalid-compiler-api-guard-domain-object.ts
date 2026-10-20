// The domain obligation (HOST-FAMILIES.md, "Calls"): a listed guard's
// argument is within its declared parameter type. A program object holding
// an identifier's kind is no node: refused at the call, which TypeScript
// refuses too: under Node `isIdentifier` answers `true` of it.
import * as ts from "typescript/unstable/ast";

export function identifier(): boolean {
  const o = { kind: ts.SyntaxKind.Identifier };
  return ts.isIdentifier(o);
}
