// A module the compiler-API units example imports a function from: it names
// `Identifier`, its importer `NumericLiteral`. One run lowers both against one
// tag selection (HOST-FAMILIES.md, "Residuals").
import * as ts from "typescript/unstable/ast";

export function nameOf(n: ts.Node): string {
  return n.kind === ts.SyntaxKind.Identifier ? n.text : "";
}
