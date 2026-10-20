// A listed guard's call passes its one argument, written as one
// (HOST-FAMILIES.md, "Calls"): a spread argument is refused by the gate.
import * as ts from "typescript/unstable/ast";

export function name(nodes: [ts.Node]): string {
  return ts.isIdentifier(...nodes) ? "identifier" : "";
}
