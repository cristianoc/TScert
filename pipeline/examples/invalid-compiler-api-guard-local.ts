// A local function named `isIdentifier` is that function, never the host
// guard (HOST-FAMILIES.md, "Calls"): its promise is checked by its body,
// which answers `true` of every node: refused at its return.
import * as ts from "typescript/unstable/ast";

function isIdentifier(n: ts.Node): n is ts.Identifier {
  return n.pos >= 0 || n.pos < 0;
}

export function local(n: ts.Node): number {
  return isIdentifier(n) ? n.text.length : 0;
}
