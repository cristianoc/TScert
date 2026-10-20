// A path through a member one arm states stable and another does not: the
// program record's `name` may change through another reference, so the read
// link ends at the call, and the read past it is of the declared type
// (HOST-FAMILIES.md, "Stable links").
import * as ts from "typescript/unstable/ast";

type Named = { readonly name: ts.PropertyName };

export function nameText(m: ts.PropertyAssignment | Named, log: () => void): string {
  if (!ts.isIdentifier(m.name)) return "";
  log();
  return m.name.text;
}
