// A path of three members whose middle member is a program record's field:
// the call between the test and the read may replace `h.box.node`, which no
// stable link keeps, so the read past it is of the declared type
// (HOST-FAMILIES.md, "Entries").
import * as ts from "typescript/unstable/ast";

type Box = { node: ts.PropertyAssignment };
type Holder = { readonly box: Box };

export function nameText(h: Holder, log: () => void): string {
  if (!ts.isIdentifier(h.box.node.name)) return "";
  log();
  return h.box.node.name.text;
}
