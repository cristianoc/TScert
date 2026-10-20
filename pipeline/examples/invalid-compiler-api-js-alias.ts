// `isTypeAliasDeclaration` declares `node is TypeAliasDeclaration`, and
// also accepts a JSDoc `@typedef`, whose kind is 345 (HOST-FAMILIES.md,
// "Guard recognition"). Read from its entry, its `true` edge leaves `n` at
// both kinds, so `n.kind` is no `SyntaxKind.TypeAliasDeclaration`: refused.
// Under Node, on a `@typedef`, it returns 345.
import * as ts from "typescript/unstable/ast";

export function aliasKind(n: ts.Node): ts.SyntaxKind.TypeAliasDeclaration | undefined {
  return ts.isTypeAliasDeclaration(n) ? n.kind : undefined;
}
