// Read by pipeline/test.mts under a description correcting `getText` to
// absent at the question token's kind: `QuestionToken` is `Token`'s
// application, whose method is then optional, and the call refused; under
// the compiler API's own description it verifies.
import * as ts from "typescript/unstable/ast";

export function tokenText(t: ts.QuestionToken): string {
  return t.getText();
}
