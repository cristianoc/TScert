// The JSDoc `@import`'s kind, which no declaration states, has its audited
// shape (COMPILER-API.md, "Audited shapes"), which states `moduleSpecifier`.
import * as ts from "typescript/unstable/ast";

export function specifierOf(n: ts.Node): ts.Node | undefined {
  return n.kind === ts.SyntaxKind.JSImportDeclaration
    ? n.moduleSpecifier
    : undefined;
}
