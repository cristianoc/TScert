// A recursive visitor whose node the flow reads at several arms of its
// family where it calls the node's `forEachChild` in an expression, passing
// itself: the call is dispatched on the union in one node, and the visitor
// verifies at the footprint its body shows.
import * as ts from "typescript/unstable/ast";
import type { Node } from "typescript/unstable/ast";

export function first(file: Node, names: Set<string>): Node | undefined {
  const refers = (n: Node): Node | undefined =>
    ts.isIdentifier(n) && names.has(n.text) ? n : n.forEachChild(refers);
  return refers(file);
}
