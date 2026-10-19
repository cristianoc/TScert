// Read by pipeline/test.mts under a description correcting `getText` to
// absent on a source file: the method is then an optional member of the
// source file's shape, and the call refused; under the compiler API's own
// description it verifies.
import * as ts from "typescript/unstable/ast";

export function fileText(f: ts.SourceFile): string {
  return f.getText();
}
