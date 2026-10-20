// The domain obligation (HOST-FAMILIES.md, "Calls"): a listed guard called
// on a name whose type holds `null` beside the family is refused at the
// call, which TypeScript refuses too. Under Node the guard throws on `null`.
import * as ts from "typescript/unstable/ast";

export function name(n: ts.Node | null): string {
  return ts.isIdentifier(n) ? n.text : "";
}
