// F5 (HOST-FAMILIES.md, "Trust rows"): `Object.assign` onto `ts.SyntaxKind`
// copies onto the enum object, a write to it: refused.
import * as ts from "typescript/unstable/ast";

export function rewrite(): void {
  Object.assign(ts.SyntaxKind, { Identifier: 345 });
}
