// A `let` root a callback replaces between the test and the read: the
// producer refuses the read of `text` on a `let` holding a union of objects.
// The forged claims and evidence of pipeline/test.mts isolate the root's
// read link, which the call ends (HOST-FAMILIES.md, "Stable links").
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
