// A listed guard's call passes its one argument, written as one
// (HOST-FAMILIES.md, "Calls"): a second argument is refused by the gate,
// which TypeScript refuses too.
import * as ts from "typescript/unstable/ast";

export function name(n: ts.Node): string {
  return ts.isIdentifier(n, n) ? n.text : "";
}
