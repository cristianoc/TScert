// A `let` root a callback replaces between the test and the read: the read
// of the root is a cell's, whose link the call ends, so the path read past it
// is of the declared type (HOST-FAMILIES.md, "Stable links").
import * as ts from "typescript/unstable/ast";

export function nameText(
  first: ts.PropertyAssignment,
  other: ts.PropertyAssignment,
): string {
  let m = first.name;
  const replace = (): void => {
    m = other.name;
  };
  return m.kind === ts.SyntaxKind.Identifier ? (replace(), m.text) : "";
}
