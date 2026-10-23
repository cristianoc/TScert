// F5 (HOST-FAMILIES.md, "Trust rows"): the package's enum objects are
// unwritten. A write to `ts.SyntaxKind` through a record view of it is
// refused at the write; under Node it would make `isIdentifier` answer
// `false` of each identifier.
import * as ts from "typescript/unstable/ast";

export function rewrite(): void {
  const kinds: Record<string, unknown> = ts.SyntaxKind;
  kinds["Identifier"] = 345;
}
