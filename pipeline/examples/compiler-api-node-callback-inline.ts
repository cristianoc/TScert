// A callback of `forEachChild` written in place and returning the node it
// received, in a run whose selection reads `Node` as several arms (the
// guard below selects `Identifier`): the binder's instance at that union has
// no derivation in evidence search, where the same callback bound to a name
// (`compiler-api-node-callback`) verifies (WORK.md, a generic method's
// instance at a union of arms).
import * as ts from "typescript/unstable/ast";

export function firstNode(n: ts.Node): ts.Node | undefined {
  return n.forEachChild((c: ts.Node): ts.Node => c);
}

export function name(n: ts.Node): string {
  return ts.isIdentifier(n) ? n.text : "";
}
