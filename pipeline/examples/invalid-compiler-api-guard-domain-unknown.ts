// The domain obligation (HOST-FAMILIES.md, "Calls"): a listed guard called
// on an `unknown` is refused at the call, which TypeScript refuses too.
import * as ts from "typescript/unstable/ast";

export function identifier(v: unknown): boolean {
  return ts.isIdentifier(v);
}
