// A unit naming `Identifier` keeps its shape and leaves `SourceFile` to the
// residual of `Node`, whose `parent` is optional since a source file's
// `parent` is absent (HOST-FAMILIES.md, "Residuals"): `n.parent` is no `Node`.
// Under Node, on a source file, `up` returns `undefined`.
import * as ts from "typescript/unstable/ast";

export function up(n: ts.Node): ts.Node {
  if (n.kind === ts.SyntaxKind.Identifier) return n;
  return n.parent;
}
