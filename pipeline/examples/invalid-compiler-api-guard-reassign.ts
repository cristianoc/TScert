// F5 (HOST-FAMILIES.md, "Trust rows"): a guard's binding is never written. A
// write of the namespace member `ts.isIdentifier` is refused at the write.
import * as ts from "typescript/unstable/ast";

export function rewrite(): void {
  Object.assign(ts, { isIdentifier: (_n: ts.Node): boolean => true });
}
