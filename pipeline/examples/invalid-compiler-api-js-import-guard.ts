// `isImportDeclaration` declares `node is ImportDeclaration`, and also
// accepts a JSDoc `@import`, whose kind is 346 (HOST-FAMILIES.md, "Guard
// recognition"). Read from its entry, its `true` edge leaves `n` at both
// kinds, so `n.kind` is no `SyntaxKind.ImportDeclaration`: refused. Under
// Node, on an `@import` tag's node, it returns 346.
import * as ts from "typescript/unstable/ast";

export function importKind(
  n: ts.Node,
): ts.SyntaxKind.ImportDeclaration | undefined {
  return ts.isImportDeclaration(n) ? n.kind : undefined;
}
