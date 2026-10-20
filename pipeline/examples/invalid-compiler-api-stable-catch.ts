// A refinement read in a `catch` whose `try` block called code: the
// exceptional edge keeps no stable link (HOST-FAMILIES.md, "Stable links"),
// so the read in the handler is of the declared type.
import * as ts from "typescript/unstable/ast";

export function nameText(m: ts.PropertyAssignment, log: () => void): string {
  if (!ts.isIdentifier(m.name)) return "";
  try {
    log();
  } catch {
    return m.name.text;
  }
  return "";
}
