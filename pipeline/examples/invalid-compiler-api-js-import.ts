// A tag value no declaration states and no audited shape describes, the
// JSDoc `@import`'s, has the base declaration's shape (the table's `base`
// rule), which states no `moduleSpecifier`.
import * as ts from "typescript/unstable/ast";

export function specifierOf(n: ts.Node): ts.Node | undefined {
  return n.kind === ts.SyntaxKind.JSImportDeclaration
    ? n.moduleSpecifier
    : undefined;
}
