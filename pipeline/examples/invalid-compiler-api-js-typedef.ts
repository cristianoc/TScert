// A tag value no declaration states, the JavaScript typedef's, has the base
// declaration's shape (the table's `base` rule), which states no `name`.
import * as ts from "typescript/unstable/ast";

export function nameOf(n: ts.Node): ts.Node | undefined {
  return n.kind === ts.SyntaxKind.JSTypeAliasDeclaration ? n.name : undefined;
}
