// Read by pipeline/test.mts under a description correcting `getText` to
// absent on a source file: the method is then an optional member of the
// residual holding the source file's shape, and the call refused; under the
// compiler API's own description it verifies.
import * as ts from "typescript/unstable/ast";

export function anyText(n: ts.Node): string {
  return n.kind === ts.SyntaxKind.Identifier ? n.text : n.getText();
}
