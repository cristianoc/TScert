import * as ts from "typescript/unstable/ast";
import type { Node, Identifier } from "typescript/unstable/ast";

export function walk(nodes: readonly Identifier[]): string[] {
  const topStatement = (n: Node): string =>
    n.parent && !ts.isSourceFile(n.parent) ? topStatement(n.parent) : n;
  return nodes.map(topStatement);
}
