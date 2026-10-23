// F5 (HOST-FAMILIES.md, "Trust rows"): a write to `ts.SyntaxKind` through a
// record type naming one of its members is refused at the write.
import * as ts from "typescript/unstable/ast";

export function rewrite(): void {
  const kinds: { Identifier: number } = ts.SyntaxKind;
  kinds.Identifier = 345;
}
