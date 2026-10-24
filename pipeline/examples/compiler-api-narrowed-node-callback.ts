// A node the flow reads at several arms of its family after a guard: a
// `map` callback testing it with a guard keeps every array store, and a
// recursive visitor testing its node, then passing itself to the node's
// `forEachChild` as a statement, is within the footprint of its own writes
// (COMPILER-API.md, "Node methods and callbacks"), so each result is dense.
import * as ts from "typescript/unstable/ast";
import type { Node } from "typescript/unstable/ast";

export function identifiers(nodes: Node[]): number[] {
  const r: number[] = nodes.map((n) => (ts.isIdentifier(n) ? 1 : 0));
  return r;
}

export function names(files: Node[]): number[] {
  const r: number[] = files.map((file) => {
    const seen = new Set<string>();
    const visit = (n: Node): void => {
      if (ts.isIdentifier(n)) seen.add(n.text);
      n.forEachChild(visit);
    };
    visit(file);
    return seen.size;
  });
  return r;
}
