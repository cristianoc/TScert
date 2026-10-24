// A node method called with plain actuals on a `Node`, as `erased`
// (tools/written-applications.mts) calls `getSourceFile` and the `inside`
// closure of `untypedAmbientField` (tools/declaration-graph.mts) calls
// `getStart`: the module's `isTypeNode` guard declares `Node` as the union
// of the type nodes and the others, and the lowering reads and invokes the
// member in one node dispatched on that union, which no bounded node rule
// admits. A function's body and an arrow's expression body calling it are
// proposed the unbounded footprint, which their bodies establish.
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile } from "typescript/unstable/ast";

export function typed(n: Node): boolean {
  return ts.isTypeNode(n);
}

export function elsewhere(n: Node, c: SourceFile): boolean {
  return n.getSourceFile() !== c;
}

export function covers(
  nodes: Node[],
  file: SourceFile,
  p: number,
  q: number,
): boolean {
  return nodes.some((n: Node) => n.getStart(file) <= p && q <= n.end);
}
