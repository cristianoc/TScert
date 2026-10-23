// F5 (HOST-FAMILIES.md, "Trust rows"): `Object.assign` onto `ts.SyntaxKind`
// copies to the enum object, writing it: refused.
import * as ts from "typescript/unstable/ast";

export function rewrite(): void {
  Object.assign(ts.SyntaxKind, { Identifier: 345 });
}
