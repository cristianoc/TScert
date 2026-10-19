// Read by pipeline/test.mts under a description correcting `getText` to
// absent at the question token's kind: the run's `Node` selects that kind's
// arm, `Token`'s application, whose method is then optional, and the call
// refused; under the compiler API's own description it verifies.
import * as ts from "typescript/unstable/ast";

export function armText(n: ts.Node): string {
  return n.kind === ts.SyntaxKind.QuestionToken ? n.getText() : "";
}
