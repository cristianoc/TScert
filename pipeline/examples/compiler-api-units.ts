// Two modules naming different kinds, one importing a function from the
// other: one run lowers both against one tag selection, the union of the
// kinds each names (HOST-FAMILIES.md, "Residuals"), so both read `Node` alike.
import * as ts from "typescript/unstable/ast";
import { nameOf } from "@fixture/node-names";

export function describe(n: ts.Node): string {
  return n.kind === ts.SyntaxKind.NumericLiteral ? n.text : nameOf(n);
}
