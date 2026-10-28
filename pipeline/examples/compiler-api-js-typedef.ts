// The JavaScript typedef's kind, which no declaration states, has its
// audited shape (COMPILER-API.md, "Audited shapes"), which states `name`.
import * as ts from "typescript/unstable/ast";

export function nameOf(n: ts.Node): ts.Node | undefined {
  return n.kind === ts.SyntaxKind.JSTypeAliasDeclaration ? n.name : undefined;
}
