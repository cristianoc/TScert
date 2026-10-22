// A callback of `forEachChild` written in place and returning the node it
// received, in a run whose selection reads `Node` as several arms (the
// guard below selects `Identifier`): creating the callback runs code, so the
// member of each arm is bound to the node before it, at the call's instance.
import * as ts from "typescript/unstable/ast";

export function firstNode(n: ts.Node): ts.Node | undefined {
  return n.forEachChild((c: ts.Node): ts.Node => c);
}

export function name(n: ts.Node): string {
  return ts.isIdentifier(n) ? n.text : "";
}
