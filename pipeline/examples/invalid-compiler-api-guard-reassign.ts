// F5 (HOST-FAMILIES.md, "Trust rows"): a guard's binding is never written.
// The namespace `ts` passed to `Object.assign`, to write `isIdentifier`, is
// refused at that mention: a namespace import is used only through member
// reads and qualified type names.
import * as ts from "typescript/unstable/ast";

export function rewrite(): void {
  Object.assign(ts, { isIdentifier: (_n: ts.Node): boolean => true });
}
