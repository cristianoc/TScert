// A mixed path, `w.node.name`, whose first member is a program record's:
// a call between the test and the read may replace `w.node`, so the read
// past it is of the declared type (HOST-FAMILIES.md, "Stable links").
import * as ts from "typescript/unstable/ast";

type Holder = { readonly node: ts.PropertyAssignment };

export function nameText(w: Holder, log: () => void): string {
  return ts.isIdentifier(w.node.name) ? (log(), w.node.name.text) : "";
}
