// F5 (HOST-FAMILIES.md, "Trust"): the package's enum objects are never
// written. A write to `ts.SyntaxKind` through a record view of it is
// refused at the write; under Node it would make `isIdentifier` answer
// `false` of every identifier.
import * as ts from "typescript/unstable/ast";

export function rewrite(): void {
  const kinds: Record<string, unknown> = ts.SyntaxKind;
  kinds["Identifier"] = 345;
}
